#!/usr/bin/env python3
"""34_typeclass_structure.py — typeclass hierarchy + peer-relative instance gaps.

Inputs (already extracted, read-only):
  data/atlas_classes.jsonl    : class defs with `parents` [{name, projFn, subobject}]
  data/atlas_instances.jsonl  : instances {className, targetHead, ...}

Two analyses:

(A) HIERARCHY TOPOLOGY. Build the `extends` DAG. `subobject = true` marks the
    principal parent (main line); `subobject = false` marks a cross-rung (e.g.
    CommGroup's main parent Group, cross parent CommMonoid). Report depth,
    multiple inheritance / diamonds, descendant and instance fan-out.

(B) PEER-RELATIVE INSTANCE GAPS (the discovery signal). A concrete carrier T has
    a *concrete* instance of class C when an instance with targetHead == T and
    className == C exists. For a direct CROSS parent P of C (subobject=false —
    main-line parents are auto-projected and are therefore not expected to be
    redeclared), compare carriers that reach C:
      providers   = carriers with concrete C AND concrete P
      nonproviders= carriers with concrete C but no concrete P
    If most peers concretely provide P while a few do not, the few are candidate
    omissions (relative to Mathlib's own convention). This is deliberately
    conservative: it never claims a true Lean synthesis failure (which needs the
    kernel), only a deviation from peer practice worth a `#synth` check.

Pure stdlib, deterministic. Mathlib declarations only.
"""
import json, os, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
CLS = os.path.join(DATA, "atlas_classes.jsonl")
INS = os.path.join(DATA, "atlas_instances.jsonl")
OUT_GAP = os.path.join(DATA, "typeclass_gap_candidates.jsonl")
OUT_SUM = os.path.join(DATA, "typeclass_structure_summary.json")

PEER_MIN = 3          # need >= this many providers to call omission unusual
PEER_RATIO = 0.66     # providers/(providers+nonproviders) >= this majority


def load(f):
    return [json.loads(l) for l in open(f, encoding="utf-8")]


def main():
    classes = [c for c in load(CLS) if c["mathlib"]]
    instances = [i for i in load(INS) if i["mathlib"]]
    by = {c["name"]: c for c in classes}

    # ---- (A) hierarchy DAG --------------------------------------------------
    parents = {c["name"]: [(p["name"], p["subobject"]) for p in c.get("parents", [])]
               for c in classes}
    # children reverse map
    children = collections.defaultdict(list)
    for c, ps in parents.items():
        for (p, _) in ps:
            children[p].append(c)

    def ancestors(name):
        seen, stack = set(), list(parents.get(name, []))
        while stack:
            p, _ = stack.pop()
            if p in seen:
                continue
            seen.add(p)
            stack.extend(parents.get(p, []))
        return seen

    # main-line depth = longest chain following subobject==True
    def main_depth(name, memo={}):
        if name in memo:
            return memo[name]
        mains = [p for (p, sub) in parents.get(name, []) if sub]
        memo[name] = 1 + max((main_depth(p) for p in mains), default=-1)
        return memo[name]

    # diamond: class with >=2 distinct parents that share a common ancestor
    def is_diamond(c):
        ps = [p for (p, _) in parents.get(c, []) if p in by]
        if len(ps) < 2:
            return False
        anc = [ancestors(p) | {p} for p in ps]
        for x in range(len(anc)):
            for y in range(x + 1, len(anc)):
                if anc[x] & anc[y]:
                    return True
        return False

    n_with_parent = sum(1 for c in classes if parents[c["name"]])
    n_multi = sum(1 for c in classes if len(parents[c["name"]]) >= 2)
    n_diamond = sum(1 for c in classes if is_diamond(c["name"]))
    depth_hist = collections.Counter(main_depth(c["name"]) for c in classes)
    desc_count = {n: len(_desc(children, n)) for n in parents}
    top_descendants = sorted(((desc_count[n], n) for n in parents),
                             reverse=True)[:15]

    # ---- concrete carrier -> class set -------------------------------------
    carrier_classes = collections.defaultdict(set)
    class_carriers = collections.defaultdict(set)
    n_concrete = 0
    for i in instances:
        t = i.get("targetHead")
        c = i["className"]
        if not t or c not in by:
            continue
        if c not in carrier_classes[t]:
            n_concrete += 1
        carrier_classes[t].add(c)
        class_carriers[c].add(t)

    # ---- (B) peer-relative cross-parent gaps -------------------------------
    gaps = []
    rule_stats = collections.Counter()
    for c in classes:
        cname = c["name"]
        cross_parents = [p for (p, sub) in parents[cname] if not sub and p in by]
        if not cross_parents:
            continue
        carriers = class_carriers.get(cname, set())
        if len(carriers) < PEER_MIN:
            continue
        for P in cross_parents:
            providers, nonproviders = [], []
            for T in carriers:
                if P in carrier_classes[T]:
                    providers.append(T)
                else:
                    nonproviders.append(T)
            tot = len(providers) + len(nonproviders)
            if len(providers) < PEER_MIN or tot == 0:
                continue
            ratio = len(providers) / tot
            rule_stats["rulesExamined"] += 1
            if ratio >= PEER_RATIO and nonproviders:
                rule_stats["rulesWithGaps"] += 1
                for T in sorted(nonproviders):
                    gaps.append({
                        "carrier": T, "strongClass": cname, "missingParent": P,
                        "providers": len(providers),
                        "nonproviders": len(nonproviders),
                        "providerRatio": round(ratio, 3),
                        "carrierClasses": sorted(carrier_classes[T])})

    gaps.sort(key=lambda g: (-g["providerRatio"], -g["providers"],
                             g["strongClass"], g["carrier"]))
    with open(OUT_GAP, "wb") as o:
        for g in gaps:
            o.write((json.dumps(g, ensure_ascii=False) + "\n").encode("utf-8"))

    # carriers that concretely instantiate the most classes (densest bundles)
    densest = sorted(((len(s), t) for t, s in carrier_classes.items()),
                     reverse=True)[:15]
    summary = {
        "mathlibClasses": len(classes),
        "mathlibInstances": len(instances),
        "concreteInstancePairs": n_concrete,
        "concreteCarriers": len(carrier_classes),
        "hierarchy": {
            "classesWithParent": n_with_parent,
            "multipleInheritance": n_multi,
            "diamonds": n_diamond,
            "mainLineDepthHist": dict(sorted(depth_hist.items())),
            "topByDescendants": [{"class": n, "descendants": d}
                                 for d, n in top_descendants],
            "topByInstances": [
                {"class": n, "instances": k} for k, n in sorted(
                    ((c["nInstances"], c["name"]) for c in classes),
                    reverse=True)[:15]],
        },
        "densestCarriers": [{"carrier": t, "nClasses": n} for n, t in densest],
        "gapRules": dict(rule_stats),
        "gapCandidates": len(gaps),
        "gapByStrongClass": collections.Counter(g["strongClass"] for g in gaps).most_common(20),
    }
    with open(OUT_SUM, "w", encoding="utf-8") as o:
        json.dump(summary, o, ensure_ascii=False, indent=2)

    print("mathlib classes", len(classes), "instances", len(instances),
          "concrete pairs", n_concrete, "carriers", len(carrier_classes))
    print("withParent", n_with_parent, "multipleInh", n_multi, "diamonds", n_diamond)
    print("main-line depth hist", dict(sorted(depth_hist.items())))
    print("gap rules:", dict(rule_stats), "candidate gaps:", len(gaps))
    print("top descendants:", [(n, d) for d, n in top_descendants[:8]])
    print("\nfirst 25 gap candidates:")
    for g in gaps[:25]:
        print(f"  {g['carrier']:<28} has {g['strongClass']:<22} "
              f"missing {g['missingParent']:<20} "
              f"peers {g['providers']}/{g['providers']+g['nonproviders']}")


def _desc(children, root):
    seen, stack = set(), [root]
    while stack:
        n = stack.pop()
        for ch in children.get(n, ()):
            if ch not in seen:
                seen.add(ch); stack.append(ch)
    return seen


if __name__ == "__main__":
    main()
