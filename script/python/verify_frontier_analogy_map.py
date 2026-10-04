#!/usr/bin/env python3
"""verify_frontier_analogy_map.py — independent rebuild of script 44."""
import json, os, sys, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
STRUCT_CUT, SEM_CUT = 0.90, 0.85
WRAPPER = {"eq", "iff", "exists", "mono", "epi", "iso", "injective",
           "surjective", "bijective", "le", "lt", "ne", "and", "or"}
TOK_STOP = {"at", "on", "within", "strict", "left", "right", "of", "the",
            "le", "lt", "eq", "set", "is", "category", "has", "inst", "a",
            "an", "to", "m"}


def camel_tokens(h):
    tail = h.split(".")[-1].replace("_", " ")
    out, cur = [], ""
    for ch in tail + " ":
        if ch.isupper() or ch == " ":
            if cur:
                out.append(cur.lower())
            cur = ch.lower() if ch.isupper() else ""
        else:
            cur += ch
    res = []
    for t in out:
        t = t.rstrip("0123456789")
        if not t or t in TOK_STOP:
            continue
        if len(t) >= 2 and t[0] == "m" and len(t[1:]) >= 3:
            t = t[1:]
        res.append(t)
    return set(res)


def triage(fh, ch, source, shared):
    ft, ct = fh.split(".")[-1].lower(), ch.split(".")[-1].lower()
    if ft in WRAPPER and ct in WRAPPER:
        return "wrapperVariant"
    sc = [t for t in (shared or []) if t.startswith("C:")]
    ov = camel_tokens(fh) & camel_tokens(ch)
    if any(len(t) >= 3 for t in ov):
        return "sameConcept" if ft == ct else "sharedHeadFamily"
    if source == "structural" and sc:
        return "sharedGenericClass"
    return "unresolved"


def main():
    bucket = {}
    for line in open(os.path.join(DATA, "area_maturity_profile.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        bucket[r["area"]] = r["bucket"]
    skel = {}
    for line in open(os.path.join(DATA, "atlas_type_skeletons.jsonl"), encoding="utf-8"):
        s = json.loads(line)
        skel[s["name"]] = s.get("conclusionHead")

    groups = {}
    pk = collections.Counter()
    seen = set()

    def ingest(aa, bb, cos, source, shared):
        A, B = aa["area"], bb["area"]
        bA, bB = bucket.get(A), bucket.get(B)
        if bA == "frontier":
            f, c, fs, cs_, bC = A, B, aa, bb, bB
        elif bB == "frontier":
            f, c, fs, cs_, bC = B, A, bb, aa, bA
        else:
            return
        pk["frontier-" + bC] += 1
        if not (bucket.get(f) == "frontier" and bucket.get(c) == "core"):
            return
        fh = fs.get("conclusionHead") or skel.get(fs["name"])
        ch = cs_.get("conclusionHead") or skel.get(cs_["name"])
        if not fh or not ch or fh == ch:
            return
        p = tuple(sorted((fs["name"], cs_["name"])))
        if p in seen:
            return
        seen.add(p)
        key = (f, c, fh, ch, source)
        g = groups.setdefault(key, {"n": 0, "max": 0.0, "sh": collections.Counter()})
        g["n"] += 1
        g["max"] = max(g["max"], cos)
        for t in shared or []:
            g["sh"][t] += 1

    for line in open(os.path.join(DATA, "embedding_cross_area_analogies.jsonl"),
                     encoding="utf-8"):
        p = json.loads(line)
        if p["cosine"] >= STRUCT_CUT:
            ingest(p["a"], p["b"], p["cosine"], "structural", p.get("sharedStrong"))
    for line in open(os.path.join(DATA, "semantic_hidden_candidates.jsonl"),
                     encoding="utf-8"):
        p = json.loads(line)
        if p["cosine"] >= SEM_CUT:
            ingest(p["a"], p["b"], p["cosine"], "semantic", p.get("sharedRoleTokens"))

    rebuilt = {}
    tri = collections.Counter()
    for (f, c, fh, ch, src), g in groups.items():
        sig = [t for t, _ in g["sh"].most_common(6)]
        tg = triage(fh, ch, src, sig)
        tri[tg] += 1
        rebuilt[(f, c, fh, ch, src)] = (g["n"], round(g["max"], 4), tg)

    written = [json.loads(l) for l in open(
        os.path.join(DATA, "frontier_analogy_shortlist.jsonl"), encoding="utf-8")]
    drows = [json.loads(l) for l in open(
        os.path.join(DATA, "frontier_donor_map.jsonl"), encoding="utf-8")]
    summ = json.load(open(os.path.join(DATA, "frontier_analogy_summary.json"),
                          encoding="utf-8"))
    errs = []
    if dict(pk) != summ["pairKindCounts"]:
        errs.append(f"pairKind {dict(pk)} != {summ['pairKindCounts']}")
    if len(written) != len(rebuilt) or \
            len(written) != summ["frontierCoreDifferentHeadGroups"]:
        errs.append("group count mismatch")
    for w in written:
        key = (w["frontierArea"], w["donorArea"], w["frontierHead"],
               w["coreHead"], w["source"])
        b = rebuilt.get(key)
        if b is None:
            errs.append(f"missing {key}")
        elif (w["nPairs"], w["maxCosine"], w["triage"]) != b:
            errs.append(f"mismatch {key}: {w['nPairs']},{w['maxCosine']},{w['triage']} vs {b}")
    if dict(tri) != summ["byTriage"]:
        errs.append(f"triage {dict(tri)} != {summ['byTriage']}")
    if summ["unresolvedCount"] != 0 or tri.get("unresolved", 0) != 0:
        errs.append("unresolved must be 0")
    # donor map reconstruction
    don = collections.defaultdict(int)
    for (f, c, fh, ch, src), g in groups.items():
        don[f] += g["n"]
    dmap = {d["frontierArea"]: d["analogPairs"] for d in drows}
    if dict(don) != {k: v for k, v in
                     sorted(dmap.items(), key=lambda kv: -kv[1])} and \
            sum(don.values()) != sum(dmap.values()):
        errs.append("donor map pair totals mismatch")
    keys = [(r["frontierArea"], -r["nPairs"], -r["maxCosine"], r["frontierHead"])
            for r in written]
    if keys != sorted(keys):
        errs.append("shortlist not sorted")

    print(f"groups {len(rebuilt)}; triage {dict(tri)}; pairKind {dict(pk)}")
    if errs:
        print("VERIFICATION FAILED")
        for e in errs[:30]:
            print("  FAIL:", e)
        sys.exit(1)
    print("pair-kind, group bijection, triage, donor totals, sort all match")
    print("VERIFICATION OK")


if __name__ == "__main__":
    main()
