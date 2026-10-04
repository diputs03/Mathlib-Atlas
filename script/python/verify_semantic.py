#!/usr/bin/env python3
"""verify_semantic.py — independent verification for 28_semantic_analogy.py.

It does NOT import script 28. It re-derives, from the same raw inputs, the
population, the role/concept tokenization, the TF-IDF cosine, the blocking and
the structural-divergence filters, then asserts:

  1. population/exclusion counts reconcile to semantic_summary.json;
  2. every emitted candidate row is cross-area, theorem/theorem, has a real
     conclusion, a DIFFERENT conclusion head and value head, meets the shared
     result-vocabulary gate, shares a role block, and has cosine >= threshold;
  3. the independently regenerated candidate pair SET equals the emitted set
     (per-block cap and global cap respected);
  4. docsWithHiddenNeighbor / roleShortlistEntries reconcile;
  5. deterministic: the regenerated set is stable under a second pass that
     iterates blocks in sorted-key order (must be order-independent).

Pure stdlib. Usage: python script/python/verify_semantic.py
"""
import json, math, array, collections, os, re, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
FEAT = os.path.join(DATA, "atlas_features.jsonl")
SKEL = os.path.join(DATA, "atlas_type_skeletons.jsonl")
CLS = os.path.join(DATA, "atlas_classes.jsonl")
OUT_CAND = os.path.join(DATA, "semantic_hidden_candidates.jsonl")
OUT_ROLE = os.path.join(DATA, "semantic_role_shortlist.json")
OUT_SUM = os.path.join(DATA, "semantic_summary.json")

# --- independently restated parameters (must agree with script 28) ----------
INCLUDE_KINDS = {"theorem", "definition", "opaque"}
NONMATH = {"Tactic", "Lean", "(root)"}
GEN_SUFFIX = ("hcongr",)
TF_CAP = 4
SEM_THRESH = 0.80
MIN_SHARED = 2
MIN_HEADW = 1
MAX_BLOCK = 1500
PER_BLOCK_CAP = 12
CAND_CAP = 40000
TOPK = 8

_HUMP = re.compile(r"[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+|[A-Z]+|\d+")
STOP = {"is", "of", "the", "a", "to", "le", "ge", "lt", "gt", "eq", "ne", "mk",
        "class", "inst", "self", "this", "h", "x", "y", "f", "g", "on", "for",
        "and", "or", "not", "iff", "def", "thm", "aux", "proof"}
ORDER = {"LE", "LT", "GE", "GT", "Min", "Max", "Subset", "SubsetEq", "SSubset",
         "SSubsetEq", "IsLeast", "IsGreatest", "IsLUB", "IsGLB", "Directed",
         "CovBy", "WCovBy"}
LOGIC = {"Eq": "equality", "Iff": "iff", "Not": "negation", "And": "and",
         "Or": "or", "Exists": "exists", "False": "false", "True": "true",
         "Membership.mem": "membership"}


def log(m):
    print(f"[verify {time.strftime('%H:%M:%S')}] {m}", flush=True)


def bk(x):
    return 0 if x <= 0 else min(7, (x - 1).bit_length())


def area(mod):
    p = mod.split(".")
    return p[1] if len(p) >= 2 and p[0] == "Mathlib" else "(root)"


def prole(ch, cnames):
    root = ch.split(".")[-1] if ch else ""
    if not root:
        return "no-conclusion"
    if root in LOGIC:
        return "P:" + LOGIC[root]
    if root in ORDER:
        return "P:order-comp"
    if ch in cnames:
        return "P:instance-goal"
    return "P:other-pred"


def vrole(vh, hv, trunc):
    if not hv:
        return "V:none"
    if not vh or trunc:
        return "V:opaque"
    root = vh.split(".")[-1]
    if root in ("rfl", "Eq.refl"):
        return "V:rfl"
    if root == "mk" or root.endswith(".mk"):
        return "V:constructor"
    if root in ("casesOn",) or root.endswith("casesOn"):
        return "V:cases"
    if root.endswith("recOn") or root.endswith("brecOn") or root in ("rec",):
        return "V:recursor"
    if root in ("Eq.mpr", "Eq.mp", "Iff.mpr", "Iff.mp", "Eq.ndrec", "Eq.rec",
                "id", "Eq.symm"):
        return "V:rewrite"
    return "V:named-lemma"


def words(name):
    out = []
    for seg in (name or "").split("."):
        for w in _HUMP.findall(seg):
            wl = w.lower()
            if len(wl) >= 3 and wl not in STOP:
                out.append(wl)
    return out


def build():
    carea_of, cnames = {}, set()
    with open(CLS, "rb") as f:
        for line in f:
            r = json.loads(line)
            cnames.add(r["name"]); carea_of[r["name"]] = area(r["module"])
    skel = {}
    with open(SKEL, "rb") as f:
        for line in f:
            r = json.loads(line)
            skel[r["name"]] = [c["class"] for c in r.get("constraints", [])]

    tid, tstr, df = {}, [], array.array("i")
    def T(t):
        j = tid.get(t)
        if j is None:
            j = len(tstr); tid[t] = j; tstr.append(t); df.append(0)
        return j

    docs, raw, blocks = [], [], collections.defaultdict(list)
    role_members = collections.defaultdict(list)
    nscan = 0
    with open(FEAT, "rb") as f:
        for line in f:
            r = json.loads(line); nscan += 1
            if r["isGenerated"] or r["kind"] not in INCLUDE_KINDS:
                continue
            if r.get("isInstance") or r.get("isClass"):
                continue
            name, mod = r["name"], r["module"]
            ar = area(mod)
            if ar in NONMATH or name.startswith("_private") or ".Meta." in mod:
                continue
            tail = name.rsplit(".", 1)[-1]
            if tail.startswith(GEN_SUFFIX):
                continue
            if (tail.endswith("casesOn") or tail.endswith("recOn") or
                    tail.endswith("brecOn") or tail in ("rec", "noConfusion",
                    "noConfusionType") or tail.endswith("inductionOn")):
                continue
            cons = skel.get(name, [])
            ch = r.get("conclusionHead") or ""
            vh = r.get("valueHead") or ""
            pr, vr = prole(ch, cnames), vrole(vh, r.get("hasValue"),
                                              r.get("valueTruncated"))
            cc = collections.Counter(
                x for c in cons if (x := carea_of.get(c)))
            toks = []
            def add(t, tf=1): toks.append((T(t), tf))
            add(("k", r["kind"])); add(("P", pr)); add(("V", vr))
            for a, n in cc.items():
                add(("R", a), n)
            for w in words(ch):
                add(("w", w))
            if vh and r.get("hasValue") and not r.get("valueTruncated"):
                for w in words(vh):
                    add(("vw", w))
            for key, val in (("pi", r["nPi"]), ("inst", r["nInstImplicit"]),
                             ("imp", r["nImplicit"]),
                             ("strict", r["nStrictImplicit"]),
                             ("default", r["nDefault"]), ("nc", len(cons)),
                             ("nca", len(cc)), ("tn", r["typeNodes"]),
                             ("td", r["typeDepth"]),
                             ("tdist", r["typeDistinct"]),
                             ("vn", r["valueNodes"]),
                             ("vd", r["valueDepth"]),
                             ("vdist", r["valueDistinct"]),
                             ("vapps", r["valueApps"]),
                             ("vforall", r["valueForalls"])):
                add(("s", key, bk(val)))
            if r.get("valueIsRfl"): add(("S", "rfl"))
            if (r.get("caseRefs") or 0) > 0: add(("S", "uses-cases"))
            if (r.get("recRefs") or 0) > 0: add(("S", "uses-rec"))
            if (r.get("valueLams") or 0) > 0: add(("S", "uses-lam"))
            if (r.get("valueLets") or 0) > 0: add(("S", "uses-let"))
            agg = {}
            for j, tf in toks:
                agg[j] = min(TF_CAP, agg.get(j, 0) + tf)
            raw.append(agg)
            for j in agg:
                df[j] += 1
            role_sig = (r["kind"], pr, vr, bk(r["nPi"]), bk(r["typeDepth"]),
                        bk(r["valueNodes"]))
            d = len(docs)
            docs.append({"name": name, "area": ar, "kind": r["kind"],
                         "ch": ch, "vh": vh, "pr": pr, "vr": vr})
            role_members[role_sig].append(d)
            hw = set(words(ch))
            if hw:
                for w in hw:
                    blocks[role_sig + (("w", w),)].append(d)
    N = len(docs)
    idf = [math.log((N + 1.0) / (df[j] + 1.0)) + 1.0 for j in range(len(tstr))]
    vec = []
    for agg in raw:
        w_, s = {}, 0.0
        for j, tf in agg.items():
            v = (1.0 + math.log(tf)) * idf[j]; w_[j] = v; s += v * v
        n = math.sqrt(s)
        vec.append({j: v / n for j, v in w_.items()} if n else {})
    return docs, vec, tstr, blocks, nscan, N


def regenerate(docs, vec, tstr, blocks, sorted_blocks=False):
    def cos(a, b):
        wa, wb = vec[a], vec[b]
        if len(wa) > len(wb):
            wa, wb = wb, wa
        return sum(v * wb[j] for j, v in wa.items() if j in wb)

    cands = []
    nbp = skipped = 0
    seen = {}
    keys = sorted(blocks.keys()) if sorted_blocks else blocks.keys()
    for bkey in keys:
        mem = blocks[bkey]
        bc = []
        if len(mem) > MAX_BLOCK:
            skipped += 1; continue
        M = len(mem)
        for a in range(M):
            i = mem[a]
            for b in range(a + 1, M):
                k = mem[b]; nbp += 1
                di, dk = docs[i], docs[k]
                if di["area"] == dk["area"]:
                    continue
                if di["kind"] != "theorem" or dk["kind"] != "theorem":
                    continue
                if not di["ch"] or not dk["ch"]:
                    continue
                if di["ch"] == dk["ch"] and di["ch"]:
                    continue
                if di["vh"] and dk["vh"] and di["vh"] == dk["vh"]:
                    continue
                sw = sum(1 for j in vec[i]
                         if j in vec[k] and tstr[j][0] == "w")
                svw = sum(1 for j in vec[i]
                          if j in vec[k] and tstr[j][0] == "vw")
                if sw < MIN_HEADW or sw + svw < MIN_SHARED:
                    continue
                c = cos(i, k)
                if c >= SEM_THRESH:
                    bc.append((c, i, k, sw + svw))
        bc.sort(key=lambda z: -z[0])
        for c, i, k, nc in bc[:PER_BLOCK_CAP]:
            pk = (i, k)
            if pk not in seen or c > seen[pk][0]:
                seen[pk] = (c, nc)
    cands = [(c, i, k, nc) for (i, k), (c, nc) in seen.items()]
    cands.sort(key=lambda z: -z[0])
    cands = cands[:CAND_CAP]
    pairset = {frozenset((docs[i]["name"], docs[k]["name"])): round(c, 6)
               for c, i, k, _ in cands}
    best = set()
    for c, i, k, _ in cands:
        best.add(i); best.add(k)
    return pairset, nbp, skipped, len(cands), len(best)


def main():
    summary = json.load(open(OUT_SUM, encoding="utf-8"))
    emitted = [json.loads(l) for l in open(OUT_CAND, encoding="utf-8")]
    shortlist = json.load(open(OUT_ROLE, encoding="utf-8"))
    log("rebuilding population + vectors independently ...")
    docs, vec, tstr, blocks, nscan, N = build()
    byname = {d["name"]: d for d in docs}
    errs = []

    # 1. counts
    if nscan != summary["scanned"]:
        errs.append(f"scanned {nscan} != {summary['scanned']}")
    if N != summary["embedded"]:
        errs.append(f"embedded {N} != {summary['embedded']}")
    if len(tstr) != summary["vocab"]:
        errs.append(f"vocab {len(tstr)} != {summary['vocab']}")
    if len(blocks) != summary["roleBlocks"]:
        errs.append(f"blocks {len(blocks)} != {summary['roleBlocks']}")
    log(f"population ok: scanned={nscan} embedded={N} vocab={len(tstr)} "
        f"blocks={len(blocks)}")

    # 2. per-row invariants
    if len(emitted) != summary["hiddenCandidates"]:
        errs.append(f"emitted rows {len(emitted)} != summary "
                    f"{summary['hiddenCandidates']}")
    for r in emitted:
        a, b = byname.get(r["a"]["name"]), byname.get(r["b"]["name"])
        if a is None or b is None:
            errs.append(f"row decl not in population: {r['a']['name']}"); continue
        if a["kind"] != "theorem" or b["kind"] != "theorem":
            errs.append(f"non-theorem pair {a['name']}/{b['name']}")
        if a["area"] == b["area"]:
            errs.append(f"same-area pair {a['name']}/{b['name']}")
        if not a["ch"] or not b["ch"] or a["ch"] == b["ch"]:
            errs.append(f"conclusion head not divergent {a['name']}/{b['name']}")
        if a["vh"] and b["vh"] and a["vh"] == b["vh"]:
            errs.append(f"value head equal {a['name']}/{b['name']}")
        if r["cosine"] + 1e-9 < SEM_THRESH:
            errs.append(f"below threshold {a['name']}/{b['name']}")
        if r["sharedConcepts"] < MIN_SHARED:
            errs.append(f"shared-concept gate {a['name']}/{b['name']}")
    log(f"per-row invariants checked on {len(emitted)} rows")

    # 3. regenerate pair set and compare
    log("regenerating candidate set (insertion order) ...")
    pset, nbp, skipped, ncand, nbest = regenerate(docs, vec, tstr, blocks, False)
    if nbp != summary["blockPairs"]:
        errs.append(f"blockPairs {nbp} != {summary['blockPairs']}")
    if skipped != summary["skippedOversizedBlocks"]:
        errs.append(f"skipped {skipped} != "
                    f"{summary['skippedOversizedBlocks']}")
    if ncand != summary["hiddenCandidates"]:
        errs.append(f"regenerated count {ncand} != {summary['hiddenCandidates']}")
    if nbest != summary["docsWithHiddenNeighbor"]:
        errs.append(f"docsWithHiddenNeighbor {nbest} != "
                    f"{summary['docsWithHiddenNeighbor']}")
    emset = {frozenset((r["a"]["name"], r["b"]["name"])): r["cosine"]
             for r in emitted}
    missing = set(pset) - set(emset)
    extra = set(emset) - set(pset)
    if missing:
        errs.append(f"{len(missing)} regenerated pairs missing from file")
    if extra:
        errs.append(f"{len(extra)} file pairs not regenerated")
    # cosine agreement
    for key, c in pset.items():
        if key in emset and abs(c - emset[key]) > 1e-5:
            errs.append(f"cosine mismatch {set(key)}: {c} vs {emset[key]}"); break
    log(f"pair-set equality: regenerated={len(pset)} emitted={len(emset)} "
        f"missing={len(missing)} extra={len(extra)}")

    # 4. shortlist count
    if len(shortlist) != summary["roleShortlistEntries"]:
        errs.append(f"shortlist {len(shortlist)} != "
                    f"{summary['roleShortlistEntries']}")
    for r in shortlist:
        if r["nAreas"] < 3 or r["members"] < 6:
            errs.append("shortlist entry below admission line"); break

    # 5. determinism under sorted-block iteration
    log("determinism pass (sorted block keys) ...")
    pset2, *_ = regenerate(docs, vec, tstr, blocks, True)
    if set(pset2) != set(pset):
        errs.append("candidate set depends on block iteration order")
    log(f"determinism: {'stable' if set(pset2) == set(pset) else 'UNSTABLE'}")

    if errs:
        log("FAILURES:")
        for e in errs[:25]:
            log("  - " + e)
        sys.exit(1)
    log("VERIFICATION OK")


if __name__ == "__main__":
    main()
