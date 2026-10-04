#!/usr/bin/env python3
"""verify_class_fact_derivations.py — independent rebuild of script 43."""
import json, os, sys, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
MIN_SPEC, MIN_CARRIERS, STRATEGY_SHARE = 4, 3, 0.6


def generic(node):
    while isinstance(node, dict) and "binderInfo" in node:
        bt = node.get("binderType")
        if isinstance(bt, dict) and bt.get("tag") == "sort":
            return True
        node = node["body"]
    return False


def main():
    chead = set()
    for line in open(os.path.join(DATA, "atlas_classes.jsonl"), encoding="utf-8"):
        chead.add(json.loads(line)["name"].split(".")[-1])
    skel = {}
    for line in open(os.path.join(DATA, "atlas_type_skeletons.jsonl"), encoding="utf-8"):
        s = json.loads(line)
        if s.get("kind") == "theorem":
            skel[s["name"]] = (s.get("conclusionHead"),
                               tuple(sorted(c["class"] for c in s.get("constraints", []))),
                               s.get("nDefault", 0))
    feat = {}
    for line in open(os.path.join(DATA, "atlas_features.jsonl"), encoding="utf-8"):
        f = json.loads(line)
        feat[f["name"]] = (f.get("valueHead"), f.get("namespace", ""),
                           f.get("module", ""))
    gen = set()
    for line in open(os.path.join(DATA, "atlas_corpus.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        if r.get("kind") == "theorem" and isinstance(r.get("typeAst"), dict) \
                and generic(r["typeAst"]):
            gen.add(r["name"])

    groups = {}
    ncf = 0
    for name, (vh, ns, mod) in feat.items():
        sk = skel.get(name)
        if sk is None:
            continue
        head, ckey, ndef = sk
        if not head or head.split(".")[-1] not in chead or not mod.startswith("Mathlib"):
            continue
        ncf += 1
        g = groups.setdefault((head, ckey, ndef),
                              {"gen": 0, "spec": 0, "car": set(),
                               "strat": collections.Counter()})
        if name in gen:
            g["gen"] += 1
        else:
            g["spec"] += 1
            g["car"].add((ns or "").split(".")[0])
            if vh:
                g["strat"][vh] += 1

    rebuilt = {}
    n_spec_only = 0
    for (head, ckey, ndef), g in groups.items():
        if g["gen"] > 0 or g["spec"] < MIN_SPEC:
            continue
        n_spec_only += 1
        car = {c for c in g["car"] if c and c != "[anonymous]"
               and c != "definition" and not c.startswith("inst")}
        if len(car) < MIN_CARRIERS or not g["strat"]:
            continue
        st, sn = sorted(g["strat"].items(), key=lambda kv: (-kv[1], kv[0]))[0]
        if sn / g["spec"] < STRATEGY_SHARE:
            continue
        cf_tail = head.split(".")[-1]
        st_tail = st.split(".")[-1]
        own = (st_tail in ("mk", "mk'") or st.endswith("." + cf_tail + ".mk")
               or st.endswith("." + cf_tail + ".mk'"))
        rebuilt[(head, tuple(ckey), ndef)] = (g["spec"], len(car), st,
                                              round(sn / g["spec"], 3),
                                              "ownConstructor" if own else "reusesGeneric")

    written = [json.loads(l) for l in open(
        os.path.join(DATA, "class_fact_derivation_candidates.jsonl"), encoding="utf-8")]
    summ = json.load(open(os.path.join(DATA, "class_fact_summary.json"), encoding="utf-8"))
    errs = []
    if ncf != summ["classFactTheorems"]:
        errs.append(f"classFactTheorems {ncf} != {summ['classFactTheorems']}")
    if n_spec_only != summ["specializedOnlyGroups"]:
        errs.append("specializedOnlyGroups mismatch")
    if len(written) != summ["sharedStrategyCandidates"] or len(written) != len(rebuilt):
        errs.append(f"candidate count {len(written)} vs {len(rebuilt)} / summary "
                    f"{summ['sharedStrategyCandidates']}")
    for w in written:
        key = (w["classFact"], tuple(w["constraints"]), w["nDefault"])
        b = rebuilt.get(key)
        if b is None:
            errs.append(f"missing rebuilt {key[0]}")
            continue
        if (w["nSpecialized"], w["nCarriers"], w["sharedStrategy"],
                w["strategyShare"], w["disposition"]) != b:
            errs.append(f"mismatch {key[0]}: {w['nSpecialized']},{w['nCarriers']},"
                        f"{w['sharedStrategy']},{w['strategyShare']},{w['disposition']} vs {b}")
    disp = collections.Counter(v[4] for v in rebuilt.values())
    if dict(disp) != summ["disposition"]:
        errs.append(f"disposition {dict(disp)} != {summ['disposition']}")
    if summ["genuineGaps"] != 0:
        errs.append("genuineGaps should be 0")
    keys = [(c["classFact"], c["nCarriers"], c["nSpecialized"]) for c in written]
    if keys != sorted(keys, key=lambda x: (-x[1], -x[2], x[0])):
        errs.append("not deterministically sorted")

    print(f"classFact theorems {ncf}; spec-only groups {n_spec_only}; "
          f"candidates {len(rebuilt)}; disposition {dict(disp)}")
    if errs:
        print("VERIFICATION FAILED")
        for e in errs[:30]:
            print("  FAIL:", e)
        sys.exit(1)
    print("counts, bijection, disposition, sort order all match")
    print("VERIFICATION OK")


if __name__ == "__main__":
    main()
