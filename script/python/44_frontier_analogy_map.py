#!/usr/bin/env python3
"""44_frontier_analogy_map.py — frontier-restricted analogy re-cut.

Scripts 17/28 already computed ALL structural/semantic cross-area pairs; the
global triages (21/26/27, 31) were not area-stratified. Here we reuse those pair
artifacts (no re-embedding) and ask the discovery question 40/42 motivate:

  which FRONTIER declarations have a near-identical-shape counterpart in a
  mature CORE area under a DIFFERENT conclusion head? That is the signature of
  an abstraction solved in the core that the frontier may be re-deriving — the
  same shape as the one positive (Set<->Filter PointwiseLift).

Outputs per frontier area: donor core areas, and a dedup shortlist of
different-head frontier<->core analog groups ranked by member count / cosine.

Inputs : embedding_cross_area_analogies.jsonl (structural),
         semantic_hidden_candidates.jsonl (semantic),
         atlas_type_skeletons.jsonl (head lookup), area_maturity_profile.jsonl
Outputs: data/frontier_analogy_shortlist.jsonl,
         data/frontier_donor_map.jsonl, data/frontier_analogy_summary.json
Pure stdlib, deterministic.
"""
import json, os, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
STRUCT_CUT, SEM_CUT = 0.90, 0.85
WRAPPER = {"eq", "iff", "exists", "mono", "epi", "iso", "injective",
           "surjective", "bijective", "le", "lt", "ne", "and", "or"}
# spelling/qualifier tokens that vary while the mathematical concept stays fixed
TOK_STOP = {"at", "on", "within", "strict", "left", "right", "of", "the",
            "le", "lt", "eq", "set", "is", "category", "has", "inst", "a",
            "an", "to", "within at", "m"}


def camel_tokens(h):
    """lower-camel / snake head -> content concept tokens (qualifiers removed,
    leading manifold 'm' folded: mFDeriv->fderiv, mDiff->diff)."""
    tail = h.split(".")[-1].replace("_", " ")
    out = []
    cur = ""
    for ch in tail + " ":
        if ch.isupper() or ch == " ":
            if cur:
                t = cur.lower()
                out.append(t)
            cur = ch.lower() if ch.isupper() else ""
        else:
            cur += ch
    res = []
    for t in out:
        t = t.rstrip("0123456789")
        if not t:
            continue
        if t in TOK_STOP:
            continue
        if len(t) >= 2 and t[0] == "m" and t[1:] not in TOK_STOP and len(t[1:]) >= 3:
            t = t[1:]  # manifold prefix
        res.append(t)
    return set(res)


def triage(fh, ch, source, shared):
    ft, ct = fh.split(".")[-1].lower(), ch.split(".")[-1].lower()
    if ft in WRAPPER and ct in WRAPPER:
        return "wrapperVariant"
    shared_classes = [t for t in (shared or []) if t.startswith("C:")]
    tf, tc = camel_tokens(fh), camel_tokens(ch)
    overlap = tf & tc
    # a shared mathematical noun (len>=3) means one concept family / generic
    if any(len(t) >= 3 for t in overlap):
        if ft == ct:
            return "sameConcept"
        return "sharedHeadFamily"
    if source == "structural" and shared_classes:
        return "sharedGenericClass"
    return "unresolved"




def head_of(name, skel):
    s = skel.get(name)
    return s if s else None


def main():
    bucket = {}
    for line in open(os.path.join(DATA, "area_maturity_profile.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        bucket[r["area"]] = r["bucket"]
    skel = {}
    for line in open(os.path.join(DATA, "atlas_type_skeletons.jsonl"), encoding="utf-8"):
        s = json.loads(line)
        skel[s["name"]] = s.get("conclusionHead")

    # group key: (frontierHead, coreHead, source) -> aggregated analog group
    groups = {}
    pair_kind = collections.Counter()
    seen_pairs = set()

    def ingest(aa, bb, cos, source, shared):
        A, B = aa["area"], bb["area"]
        bA, bB = bucket.get(A), bucket.get(B)
        if bA == "frontier" and bB in ("core", "other", "frontier", "infra"):
            f, c, fside, cside = A, B, aa, bb
        elif bB == "frontier" and bA in ("core", "other", "frontier", "infra"):
            f, c, fside, cside = B, A, bb, aa
        else:
            return
        kind = ("frontier-" + (bB if bA == "frontier" else bA))
        pair_kind[kind] += 1
        if not (bucket.get(f) == "frontier" and bucket.get(c) == "core"):
            return  # shortlist keeps only frontier<->core
        fh = fside.get("conclusionHead") or head_of(fside["name"], skel)
        ch = cside.get("conclusionHead") or head_of(cside["name"], skel)
        if not fh or not ch or fh == ch:
            return  # different-head analogies only
        pkey = tuple(sorted((fside["name"], cside["name"])))
        if pkey in seen_pairs:
            return
        seen_pairs.add(pkey)
        gkey = (f, c, fh, ch, source)
        g = groups.setdefault(gkey, {"n": 0, "maxCos": 0.0, "ex": [],
                                    "shared": collections.Counter()})
        g["n"] += 1
        g["maxCos"] = max(g["maxCos"], cos)
        if len(g["ex"]) < 6:
            g["ex"].append({"frontier": fside["name"], "core": cside["name"],
                            "cosine": round(cos, 4)})
        for tok in shared or []:
            g["shared"][tok] += 1

    for line in open(os.path.join(DATA, "embedding_cross_area_analogies.jsonl"),
                     encoding="utf-8"):
        p = json.loads(line)
        if p["cosine"] < STRUCT_CUT:
            continue
        ingest(p["a"], p["b"], p["cosine"], "structural", p.get("sharedStrong"))
    for line in open(os.path.join(DATA, "semantic_hidden_candidates.jsonl"),
                     encoding="utf-8"):
        p = json.loads(line)
        if p["cosine"] < SEM_CUT:
            continue
        ingest(p["a"], p["b"], p["cosine"], "semantic",
               p.get("sharedRoleTokens"))

    rows = []
    for (f, c, fh, ch, src), g in groups.items():
        shared_sig = [t for t, _ in g["shared"].most_common(6)]
        rows.append({"frontierArea": f, "donorArea": c, "source": src,
                     "frontierHead": fh, "coreHead": ch, "nPairs": g["n"],
                     "maxCosine": round(g["maxCos"], 4),
                     "triage": triage(fh, ch, src, shared_sig),
                     "sharedSignature": shared_sig,
                     "examples": g["ex"]})
    rows.sort(key=lambda r: (r["frontierArea"], -r["nPairs"], -r["maxCosine"],
                             r["frontierHead"]))
    with open(os.path.join(DATA, "frontier_analogy_shortlist.jsonl"),
              "wb") as o:
        for r in rows:
            o.write((json.dumps(r, ensure_ascii=False) + "\n").encode("utf-8"))

    # donor map: per frontier area, which core areas donate analogies
    donor = collections.defaultdict(collections.Counter)
    donor_groups = collections.defaultdict(set)
    for r in rows:
        donor[r["frontierArea"]][r["donorArea"]] += r["nPairs"]
        donor_groups[r["frontierArea"]].add((r["donorArea"], r["frontierHead"],
                                             r["coreHead"]))
    drows = []
    for f in sorted(donor):
        tot = sum(donor[f].values())
        drows.append({"frontierArea": f, "analogPairs": tot,
                      "distinctAnalogGroups": len(donor_groups[f]),
                      "donorAreas": [{"area": a, "pairs": n}
                                     for a, n in donor[f].most_common()]})
    drows.sort(key=lambda r: -r["analogPairs"])
    with open(os.path.join(DATA, "frontier_donor_map.jsonl"), "wb") as o:
        for r in drows:
            o.write((json.dumps(r, ensure_ascii=False) + "\n").encode("utf-8"))

    by_src = collections.Counter(r["source"] for r in rows)
    by_triage = collections.Counter(r["triage"] for r in rows)
    unresolved = [r for r in rows if r["triage"] == "unresolved"]
    by_f = collections.Counter()
    for r in rows:
        by_f[r["frontierArea"]] += r["nPairs"]
    summary = {
        "cuts": {"structuralCosine": STRUCT_CUT, "semanticCosine": SEM_CUT},
        "pairKindCounts": dict(pair_kind),
        "frontierCoreDifferentHeadGroups": len(rows),
        "bySource": dict(by_src),
        "byTriage": dict(by_triage),
        "unresolvedCount": len(unresolved),
        "unresolved": unresolved,
        "pairsByFrontierArea": dict(by_f.most_common()),
        "donorMap": drows,
        "topGroups": sorted(rows, key=lambda r: (-r["nPairs"], -r["maxCosine"]))[:30],
    }
    with open(os.path.join(DATA, "frontier_analogy_summary.json"), "w",
              encoding="utf-8") as o:
        json.dump(summary, o, ensure_ascii=False, indent=2)

    print("pair-kind counts (all frontier-involved):", dict(pair_kind))
    print(f"frontier<->core different-head analog groups: {len(rows)} "
          f"by source {dict(by_src)}")
    print("triage:", dict(by_triage), "| unresolved:", len(unresolved))
    for r in unresolved:
        print(f"  UNRESOLVED {r['frontierArea']} {r['frontierHead']} ~ "
              f"{r['donorArea']}.{r['coreHead']} cos={r['maxCosine']} {r['source']}")
    print("pairs per frontier area:", dict(by_f.most_common()))
    print("donor map (top):")
    for r in drows[:12]:
        top = ", ".join(f"{a}:{n}" for a, n in
                        [(d['area'], d['pairs']) for d in r['donorAreas'][:4]])
        print(f"  {r['frontierArea']:<20} groups={r['distinctAnalogGroups']:<4} {top}")


if __name__ == "__main__":
    main()
