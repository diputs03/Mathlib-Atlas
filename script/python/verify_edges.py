#!/usr/bin/env python3
"""Verification for the 08 labelled dependency-edge graph (JSONL).

Checks, streaming:
  * required fields / types on every edge;
  * internal consistency: inType <=> typeCount>0, inValue <=> valueCount>0,
    isSelf <=> source == target, targetKind in the known set;
  * uniqueness of ordered (source, target);
  * every edge has at least one layer, counts are non-negative ints;
  * optional --corpus: every edge source is a Mathlib declaration present in
    the 07 corpus, and reports how many corpus nodes have outgoing edges.
Prints degree / layer / targetKind distributions.
"""

import argparse
import collections
import json
import sys

KINDS = {"axiom", "definition", "opaque", "theorem", "quotient",
         "inductive", "constructor", "recursor", "unknown"}
REQUIRED = {"source", "target", "inType", "inValue", "typeCount",
            "valueCount", "targetKind", "isSelf"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("edges")
    ap.add_argument("--corpus", help="07 main-corpus JSONL for source cross-ref")
    args = ap.parse_args()

    n = 0
    seen = set()
    dup = 0
    bad = 0
    self_edges = 0
    out_deg = collections.Counter()
    layers = collections.Counter()
    tk = collections.Counter()
    sources = set()

    with open(args.edges, "rb") as fh:
        for raw in fh:
            r = json.loads(raw)
            n += 1
            if REQUIRED - r.keys():
                bad += 1
                continue
            s, t = r["source"], r["target"]
            key = (s, t)
            if key in seen:
                dup += 1
            seen.add(key)
            sources.add(s)
            out_deg[s] += 1
            if r["targetKind"] not in KINDS:
                bad += 1
            if not (isinstance(r["typeCount"], int) and r["typeCount"] >= 0
                    and isinstance(r["valueCount"], int) and r["valueCount"] >= 0):
                bad += 1
            if r["inType"] != (r["typeCount"] > 0):
                bad += 1
            if r["inValue"] != (r["valueCount"] > 0):
                bad += 1
            if not (r["inType"] or r["inValue"]):
                bad += 1
            if r["isSelf"] != (s == t):
                bad += 1
            if r["isSelf"]:
                self_edges += 1
            layers[(r["inType"], r["inValue"])] += 1
            tk[r["targetKind"]] += 1

    print(f"edges                 : {n}")
    print(f"unique (source,target): {len(seen)}  (duplicates {dup})")
    print(f"distinct sources      : {len(sources)}")
    print(f"self-edges            : {self_edges}")
    print(f"inconsistent records  : {bad}")
    print(f"layer (type,value)    : {dict(layers)}")
    print(f"targetKind            : {dict(tk)}")
    if out_deg:
        degs = sorted(out_deg.values())
        q = lambda p: degs[min(len(degs) - 1, int(p * len(degs)))]
        print(f"out-degree: p50={q(.5)} p90={q(.9)} p99={q(.99)} max={degs[-1]} "
              f"mean={sum(degs)/len(degs):.1f}")

    ok = dup == 0 and bad == 0

    if args.corpus:
        corpus_names = set()
        with open(args.corpus, "rb") as fh:
            for raw in fh:
                # name is the first field; parse fully for correctness
                corpus_names.add(json.loads(raw)["name"])
        missing = [s for s in sources if s not in corpus_names]
        no_out = len(corpus_names - sources)
        print(f"corpus nodes          : {len(corpus_names)}")
        print(f"edge sources not in corpus: {len(missing)}")
        print(f"corpus nodes with no outgoing edge: {no_out}")
        ok = ok and not missing

    print("\nVERIFICATION", "OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
