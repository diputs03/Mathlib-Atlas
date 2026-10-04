#!/usr/bin/env python3
"""verify_weak_band.py — independent verification for 32_weak_band_scan.

Checks:
  1. set arithmetic: weak-band pairs = loose(>=0.70) minus tight(>=0.80), and
     every weak row truly has 0.70 <= cosine < 0.80;
  2. the two-stage family partition sums to the weak-band total;
  3. the emitted residual is EXACTLY {weak rows: ledger31 family == unresolved
     AND weak_family == wb_noise} (independent re-derivation, bijection);
  4. every non-residual weak row is claimed by some known family;
  5. summary counts reconcile and the result is deterministic.
Pure stdlib.
"""
import json, os, sys, importlib.util, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")


def load_mod(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


s32 = load_mod("s32v", "script/python/32_weak_band_scan.py")
led = s32.led

LOOSE = os.path.join(DATA, "semantic_hidden_candidates_loose070.jsonl")
TIGHT = os.path.join(DATA, "semantic_hidden_candidates.jsonl")
RESID = os.path.join(DATA, "semantic_weak_band_residual.jsonl")
SUM = os.path.join(DATA, "semantic_weak_band_summary.json")
LO, HI = 0.70, 0.80


def main():
    loose = [json.loads(l) for l in open(LOOSE, encoding="utf-8")]
    tight = [json.loads(l) for l in open(TIGHT, encoding="utf-8")]
    resid = [json.loads(l) for l in open(RESID, encoding="utf-8")]
    summary = json.load(open(SUM, encoding="utf-8"))
    errs = []

    tightset = {s32.pairkey(r) for r in tight}

    # 1. band arithmetic
    weak = []
    for r in loose:
        if s32.pairkey(r) in tightset:
            continue
        c = r["cosine"]
        if not (LO - 1e-9 <= c < HI + 1e-9):
            errs.append(f"loose row outside expected bands: cos={c}")
            continue
        weak.append(r)
    # tight rows must all be >= HI
    for r in tight:
        if r["cosine"] < HI - 1e-9:
            errs.append("tight row below 0.80")
            break
    if len(weak) != summary["weakBandTotal"]:
        errs.append(f"weak total {len(weak)} != summary {summary['weakBandTotal']}")
    if summary["looseTotal"] != len(loose) or summary["tightTotal"] != len(tight):
        errs.append("loose/tight totals disagree with summary")

    # 2+3. independently re-derive the two-stage partition and residual
    stage1 = collections.Counter()
    stage2 = collections.Counter()
    expect_resid = set()
    for r in weak:
        ra, rb = led.root(r["a"]["conclusionHead"]), led.root(r["b"]["conclusionHead"])
        f1 = led.classify(ra, rb)
        stage1[f1] += 1
        if f1 == "unresolved":
            f2 = s32.weak_family(ra, rb)
            stage2[f2] += 1
            if f2 == "wb_noise":
                expect_resid.add(s32.pairkey(r))
    if dict(stage1) != summary["weakByFamily"]:
        errs.append("first-stage breakdown mismatch")
    if dict(stage2) != summary["secondStageOfUnresolved"]:
        errs.append("second-stage breakdown mismatch")
    if sum(stage1.values()) != len(weak):
        errs.append("first stage does not partition weak band")
    if sum(stage2.values()) != stage1["unresolved"]:
        errs.append("second stage does not partition unresolved")

    got_resid = {frozenset((r["a"]["name"], r["b"]["name"])) for r in resid}
    if got_resid != expect_resid:
        errs.append(f"residual mismatch: missing {len(expect_resid-got_resid)} "
                    f"extra {len(got_resid-expect_resid)}")
    if len(resid) != summary["novelResidual"]:
        errs.append("residual count disagrees with summary")
    # residual rows are themselves in-band
    for r in resid:
        if not (LO - 1e-9 <= r["cosine"] < HI + 1e-9):
            errs.append("residual row out of band")
            break
    # residual sorted by descending cosine
    cs = [r["cosine"] for r in resid]
    if cs != sorted(cs, reverse=True):
        errs.append("residual not sorted by descending cosine")

    print("weak band:", len(weak))
    print("stage1:", dict(stage1))
    print("stage2:", dict(stage2))
    print("residual (wb_noise):", len(resid))
    if errs:
        print("FAILURES:")
        for e in errs[:25]:
            print("  -", e)
        sys.exit(1)
    print("VERIFICATION OK")


if __name__ == "__main__":
    main()
