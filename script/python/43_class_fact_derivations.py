#!/usr/bin/env python3
"""43_class_fact_derivations.py — missing GENERIC class-fact derivations.

Script 42 showed half of frontier repetition is per-carrier class/prop-fact
derivation (theorems whose conclusion head is itself a class/prop, proved again
for each concrete carrier). Script 35 only checked missing cross-rung
*instances* synthesizable by projection; here we ask a different question:

  when the SAME class fact is derived for many carriers by the SAME proof
  strategy (common value head), and no polymorphic theorem/instance exists,
  a single generic lemma "derive class C via strategy S" may be missing.

A group is keyed (conclusionHead=class/prop, constraint tuple, nDefault); we
keep only specialized-only groups (no sort-binder generic member), require
>= MIN_CARRIERS carriers and a DOMINANT shared valueHead (>= STRATEGY_SHARE of
members use the same proof-strategy head). Output is a shortlist to kernel-check.

Inputs : atlas_corpus.jsonl (generic test from typeAst),
         atlas_type_skeletons.jsonl (head/constraints/nDefault),
         atlas_features.jsonl (valueHead, namespace),
         atlas_classes.jsonl (class heads), area_maturity_profile.jsonl
Outputs: data/class_fact_derivation_candidates.jsonl,
         data/class_fact_summary.json
Pure stdlib, streaming, deterministic.
"""
import json, os, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
MIN_SPEC, MIN_CARRIERS = 4, 3
STRATEGY_SHARE = 0.6


def is_generic(node):
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
    bucket = {}
    for line in open(os.path.join(DATA, "area_maturity_profile.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        bucket[r["area"]] = r["bucket"]

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

    # pass 1: which theorem names are generic
    generic = set()
    for line in open(os.path.join(DATA, "atlas_corpus.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        if r.get("kind") != "theorem":
            continue
        ta = r.get("typeAst")
        if isinstance(ta, dict) and is_generic(ta):
            generic.add(r["name"])

    # pass 2: group class/prop-fact theorems
    groups = {}
    n_class_fact_thm = 0
    for name, (vh, ns, mod) in feat.items():
        sk = skel.get(name)
        if sk is None:
            continue
        head, ckey, ndef = sk
        if not head or head.split(".")[-1] not in chead:
            continue
        if not mod.startswith("Mathlib"):
            continue
        n_class_fact_thm += 1
        key = (head, ckey, ndef)
        g = groups.setdefault(key, {"gen": 0, "spec": 0, "carriers": set(),
                                    "areas": collections.Counter(),
                                    "strat": collections.Counter(), "ex": []})
        area = mod.split(".")[1] if mod.count(".") >= 1 else ""
        if name in generic:
            g["gen"] += 1
        else:
            g["spec"] += 1
            g["carriers"].add((ns or "").split(".")[0])
            g["areas"][area] += 1
            if vh:
                g["strat"][vh] += 1
            if len(g["ex"]) < 12:
                g["ex"].append(name)

    candidates = []
    n_spec_only = n_shared_strat = 0
    for (head, ckey, ndef), g in groups.items():
        if g["gen"] > 0 or g["spec"] < MIN_SPEC:
            continue
        n_spec_only += 1
        carriers = {c for c in g["carriers"] if c and c != "[anonymous]"
                    and c != "definition" and not c.startswith("inst")}
        if len(carriers) < MIN_CARRIERS:
            continue
        if not g["strat"]:
            continue
        top_strat, top_n = sorted(g["strat"].items(), key=lambda kv: (-kv[1], kv[0]))[0]
        share = top_n / g["spec"]
        if share < STRATEGY_SHARE:
            continue
        n_shared_strat += 1
        dom_area = max(sorted(g["areas"]), key=lambda a: g["areas"][a])
        cf_tail = head.split(".")[-1]
        st_tail = top_strat.split(".")[-1]
        own_ctor = (st_tail in ("mk", "mk'")
                    or top_strat.endswith("." + cf_tail + ".mk")
                    or top_strat.endswith("." + cf_tail + ".mk'"))
        candidates.append({
            "classFact": head, "constraints": list(ckey), "nDefault": ndef,
            "nSpecialized": g["spec"], "nCarriers": len(carriers),
            "carriers": sorted(carriers),
            "sharedStrategy": top_strat, "strategyShare": round(share, 3),
            "disposition": "ownConstructor" if own_ctor else "reusesGeneric",
            "dominantArea": dom_area, "dominantBucket": bucket.get(dom_area, "other"),
            "areas": [{"area": a, "n": c}
                      for a, c in sorted(g["areas"].items(),
                                         key=lambda kv: (-kv[1], kv[0]))],
            "examples": g["ex"]})
    candidates.sort(key=lambda x: (-x["nCarriers"], -x["nSpecialized"],
                                   x["classFact"]))
    with open(os.path.join(DATA, "class_fact_derivation_candidates.jsonl"),
              "wb") as o:
        for c in candidates:
            o.write((json.dumps(c, ensure_ascii=False) + "\n").encode("utf-8"))

    bcount = collections.Counter(c["dominantBucket"] for c in candidates)
    dcount = collections.Counter(c["disposition"] for c in candidates)
    summary = {
        "classFactTheorems": n_class_fact_thm,
        "specializedOnlyGroups": n_spec_only,
        "sharedStrategyCandidates": n_shared_strat,
        "disposition": dict(dcount),
        "genuineGaps": sum(1 for c in candidates
                          if c["disposition"] not in ("ownConstructor", "reusesGeneric")),
        "params": {"minSpec": MIN_SPEC, "minCarriers": MIN_CARRIERS,
                   "strategyShare": STRATEGY_SHARE},
        "candidatesByBucket": dict(bcount),
        "topCandidates": candidates[:30],
    }
    with open(os.path.join(DATA, "class_fact_summary.json"), "w",
              encoding="utf-8") as o:
        json.dump(summary, o, ensure_ascii=False, indent=2)

    print(f"class/prop-fact theorems {n_class_fact_thm}; specialized-only groups "
          f"{n_spec_only}; shared-strategy candidates {n_shared_strat}")
    print("by bucket:", dict(bcount), "| disposition:", dict(dcount),
          "| genuine gaps:", summary["genuineGaps"])
    for c in candidates[:25]:
        print(f"  {c['classFact']:<22} via {c['sharedStrategy']:<22} "
              f"carriers={c['nCarriers']} spec={c['nSpecialized']} "
              f"share={c['strategyShare']} {c['dominantArea']}/{c['dominantBucket']}")


if __name__ == "__main__":
    main()
