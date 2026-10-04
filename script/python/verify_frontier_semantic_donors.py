#!/usr/bin/env python3
"""verify_frontier_semantic_donors.py — independent verification for script 52.

Checks, without importing the production script:
  A. file/count consistency (targets, pairs, coverage, gap pairs, TOPK cap,
     famous-seed coverage recomputed from the targets file);
  B. invariants on every emitted pair (donor in a CORE area, target in a
     FRONTIER area, distinct areas, >=2 shared meaning words, threshold floors,
     sim = 0.65*meaning + 0.35*role, no boilerplate, global sort order);
  C. independent RECOMPUTATION of the meaning cosine for a deterministic sample
     of pairs: rebuild document-frequency with a fresh full corpus pass using an
     independently reimplemented tokenizer, reload each pair's raw feature row,
     and recompute TF-IDF cosine directly from name + conclusion head + value
     head, comparing to the reported meaningCos.
"""
import json, math, collections, os, re

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
FEAT = os.path.join(DATA, "atlas_features.jsonl")
MAT = os.path.join(DATA, "area_maturity_profile.jsonl")
PAIRS = os.path.join(DATA, "frontier_semantic_donors.jsonl")
TARGETS = os.path.join(DATA, "frontier_semantic_targets.jsonl")
SUM = os.path.join(DATA, "frontier_semantic_summary.json")

INCLUDE_KINDS = {"theorem", "definition", "opaque"}
TF_CAP = 4
MEANING_W, ROLE_W = 0.65, 0.35
MIN_SHARED = 2
MFLOOR, SFLOOR, TOPK = 0.30, 0.42, 8
GEN_SUFFIX = ("hcongr",)
BOIL = ("term_", "«term", "ctoridx", "ctor_idx", ".quot", "notation",
        "match_", "_match", "anonymous", "raw_", "delab", "parser_",
        "_parser", "macro_", ".macro")
_HUMP = re.compile(r"[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+|[A-Z]+|\d+")
STOP = {"is", "of", "the", "a", "to", "le", "ge", "lt", "gt", "eq", "ne", "mk",
        "class", "inst", "self", "this", "h", "x", "y", "f", "g", "on", "for",
        "and", "or", "not", "iff", "def", "thm", "aux", "proof"}
fail = []


def check(cond, msg):
    if not cond:
        fail.append(msg)


def words(name):
    out = []
    for seg in (name or "").split("."):
        for w in _HUMP.findall(seg):
            wl = w.lower()
            if len(wl) >= 3 and wl not in STOP:
                out.append(wl)
    return out


def area_of(module):
    p = module.split(".")
    return p[1] if len(p) >= 2 and p[0] == "Mathlib" else "(root)"


def gen_tail(tail):
    return (tail.endswith("casesOn") or tail.endswith("recOn") or
            tail.endswith("brecOn") or tail in ("rec", "noConfusion",
            "noConfusionType") or tail.endswith("inductionOn"))


def eligible(r):
    if r["isGenerated"] or r["kind"] not in INCLUDE_KINDS:
        return False
    if r.get("isInstance") or r.get("isClass"):
        return False
    name, module = r["name"], r["module"]
    if name.startswith("_private") or ".Meta." in module:
        return False
    tail = name.rsplit(".", 1)[-1]
    if tail.startswith(GEN_SUFFIX) or gen_tail(tail):
        return False
    low = name.lower()
    return not any(b in low for b in BOIL)


def meaning_counter(r):
    c = collections.Counter()
    for w in words(r["name"]):
        c[w] += 1
    for w in words(r.get("conclusionHead") or ""):
        c[w] += 1
    vh = r.get("valueHead") or ""
    if vh and r.get("hasValue") and not r.get("valueTruncated"):
        for w in words(vh):
            c[w] += 1
    return {w: min(TF_CAP, n) for w, n in c.items()}


# ---- load --------------------------------------------------------------
bucket_of, core, frontier = {}, set(), set()
for line in open(MAT, "rb"):
    r = json.loads(line)
    bucket_of[r["area"]] = r["bucket"]
    if r["bucket"] == "core":
        core.add(r["area"])
    elif r["bucket"] == "frontier":
        frontier.add(r["area"])
pairs = [json.loads(l) for l in open(PAIRS, encoding="utf-8")]
trows = [json.loads(l) for l in open(TARGETS, encoding="utf-8")]
summ = json.loads(open(SUM, encoding="utf-8").read())

# ---- A. counts -----------------------------------------------------------
check(len(trows) == summ["targets"], "targets file count != summary")
check(len(pairs) == summ["donorPairs"], "pairs file count != summary")
covered = sum(1 for t in trows if t["nDonors"] > 0)
check(covered == summ["targetsWithDonor"], "coverage mismatch")
check(sum(1 for p in pairs if p["structuralGap"]) ==
      summ["structuralGapPairs"], "structuralGap count mismatch")
per = collections.Counter(p["target"]["name"] for p in pairs)
check(all(c <= TOPK for c in per.values()), "TOPK cap violated")
seed_t, seed_c = collections.Counter(), collections.Counter()
for t in trows:
    if t["seed"]:
        seed_t[t["seed"]] += 1
        if t["nDonors"]:
            seed_c[t["seed"]] += 1
for s, v in summ["famousSeedCoverage"].items():
    check(v["namedTargets"] == seed_t.get(s, 0), f"seed targets {s}")
    check(v["withMatureDonor"] == seed_c.get(s, 0), f"seed covered {s}")

# ---- B. per-pair invariants ---------------------------------------------
prev = None
for p in pairs:
    ta, da = p["target"]["area"], p["donor"]["area"]
    check(da in core, f"donor not core: {da}")
    check(ta in frontier, f"target not frontier: {ta}")
    check(da != ta, "same-area pair present")
    check(len(p["sharedMeaning"]) >= MIN_SHARED, "shared-meaning gate violated")
    check(p["meaningCos"] >= MFLOOR - 1e-9, "meaning floor violated")
    check(p["sim"] >= SFLOOR - 1e-9, "sim floor violated")
    calc = MEANING_W * p["meaningCos"] + ROLE_W * p["roleCos"]
    check(abs(calc - p["sim"]) < 1e-6, f"sim blend wrong: {p['sim']} vs {calc}")
    low = (p["target"]["name"] + p["donor"]["name"]).lower()
    check(not any(b in low for b in BOIL), "boilerplate leaked into pair")
    if prev is not None:
        check(p["sim"] <= prev + 1e-9, "pairs not sorted by sim desc")
    prev = p["sim"]

# ---- C. independent meaning-cosine recomputation ------------------------
# deterministic sample: overall top 12 + up to 4 per nonempty seed
sample = pairs[:12]
by_seed = collections.defaultdict(list)
for p in pairs:
    if p["target"]["seed"] and len(by_seed[p["target"]["seed"]]) < 4:
        by_seed[p["target"]["seed"]].append(p)
for v in by_seed.values():
    sample.extend(v)
seen, sample = set(), []
for p in pairs[:12] + [q for v in by_seed.values() for q in v]:
    k = (p["target"]["name"], p["donor"]["name"])
    if k not in seen:
        seen.add(k); sample.append(p)
want = {p["target"]["name"] for p in sample} | {p["donor"]["name"] for p in sample}

N = 0
df = collections.Counter()
rows = {}
with open(FEAT, "rb") as f:
    for line in f:
        r = json.loads(line)
        if not eligible(r):
            continue
        N += 1
        a = area_of(r["module"])
        if a in core or a in frontier:
            mc = meaning_counter(r)
            for w in mc:
                df[w] += 1
            if r["name"] in want:
                rows[r["name"]] = mc


def norm(counter):
    v, s = {}, 0.0
    for w, tf in counter.items():
        x = (1.0 + math.log(tf)) * (math.log((N + 1.0) / (df[w] + 1.0)) + 1.0)
        v[w] = x
        s += x * x
    n = math.sqrt(s)
    return {w: x / n for w, x in v.items()} if n else {}


def cos(a, b):
    if len(a) > len(b):
        a, b = b, a
    return sum(x * b.get(w, 0.0) for w, x in a.items())


checked = 0
for p in sample:
    tn, dn = p["target"]["name"], p["donor"]["name"]
    check(tn in rows and dn in rows, f"raw row missing for {tn} / {dn}")
    if tn in rows and dn in rows:
        rec = cos(norm(rows[tn]), norm(rows[dn]))
        checked += 1
        if abs(rec - p["meaningCos"]) > 5e-3:
            fail.append(f"meaningCos mismatch {tn} ~ {dn}: "
                        f"recomputed {rec:.4f} reported {p['meaningCos']:.4f}")

print(f"pairs={len(pairs)} targets={len(trows)} covered={covered} "
      f"gapPairs={summ['structuralGapPairs']} sameFamilyDropped="
      f"{summ['sameConceptFamilyDropped']}")
print(f"famous-seed (named/with-donor): " +
      json.dumps({s: (v['namedTargets'], v['withMatureDonor'])
                  for s, v in summ['famousSeedCoverage'].items()}))
print(f"independently recomputed meaning cosine for {checked} sampled pairs")
if fail:
    print("FAILURES:")
    for m in fail:
        print("  - " + m)
    raise SystemExit(1)
print("VERIFICATION OK")
