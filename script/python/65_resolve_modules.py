#!/usr/bin/env python3
"""65_resolve_modules.py — one-off helper: resolve declaration modules and
basic feature fields for a hard-coded adjudication name list (script 64).
Usage: python script/python/65_resolve_modules.py
"""
import json, os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")

WANT = {
    "Sym2.map", "Stream'.Seq.map", "Cycle.map", "Multiset.map",
    "Ultrafilter.map", "Filter.Germ.map", "Trunc.map", "Computation.map",
    "CompactCoherentification.map", "SummationFilter.map",
    "Stream'.WSeq.zipWith", "Stream'.corecState", "Set.image", "Filter.map",
    "Part.bind", "Trunc.bind", "Ultrafilter.bind", "Erased.map",
    "WithOne.map", "WithZero.map", "WithBot.map", "WithTop.map",
    "OnePoint.map", "Set.image2", "Filter.map₂", "WithZero.map₂",
    "WithBot.map₂", "WithTop.map₂", "WithOne.map₂", "Stream'.WSeq.map",
    "Stream'.Seq1.map", "Stream'.Seq.bind", "Cycle.bind", "Sym2.bind",
    "Filter.Germ.bind", "Stream'.WSeq.zipWith?",
}


def main():
    found = {}
    with open(os.path.join(DATA, "atlas_features.jsonl"), "rb") as f:
        for line in f:
            r = json.loads(line)
            n = r.get("name")
            if n in WANT:
                found[n] = r
    for n in sorted(WANT):
        r = found.get(n)
        if r is None:
            print(f"{n:45s} NOT FOUND")
        else:
            print(f"{n:45s} {r['kind']:10s} pi={r['nPi']:2d} "
                  f"tn={r['typeNodes']:2d} td={r['typeDepth']:2d} "
                  f"nc={r['typeConsts']:2d} vh={r.get('valueHead')}  "
                  f"<= {r['module']}")


if __name__ == "__main__":
    main()
