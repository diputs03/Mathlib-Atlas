#!/usr/bin/env python3
"""verify_precise_ladders.py — independent checks for scripts 68/69 outputs."""
import json, os, re, sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
fails = []
def check(cond, msg):
    print(("PASS  " if cond else "FAIL  ") + msg)
    if not cond:
        fails.append(msg)

terms_p = os.path.join(DATA, "atlas_conclusion_terms.jsonl")
members_p = os.path.join(DATA, "precise_ladder_members.jsonl")
pairs_p = os.path.join(DATA, "precise_ladder_pairs.jsonl")
summary_p = os.path.join(DATA, "precise_ladder_summary.json")
for p in (terms_p, members_p, pairs_p, summary_p):
    check(os.path.exists(p) and os.path.getsize(p) > 0, f"exists & nonempty: {os.path.basename(p)}")

# ---- rebuild hierarchy independently ----
direct = defaultdict(set)
for line in open(os.path.join(DATA, "atlas_classes.jsonl"), encoding="utf-8"):
    r = json.loads(line)
    short = r["name"].split(".")[-1]
    for p in r.get("parents", []):
        pn = p["name"]
        if pn.startswith("Lean.Grind."):
            pn = pn[len("Lean.Grind."):]
        direct[short].add(pn.split(".")[-1])
anc = {}
def anc_of(c, stack):
    if c in anc:
        return anc[c]
    if c in stack:
        return set()
    stack.add(c)
    out = set()
    for p in direct.get(c, ()):
        out.add(p); out |= anc_of(p, stack)
    stack.discard(c)
    anc[c] = out
    return out
for c in list(direct):
    anc_of(c, set())

def covers(strong, avail):
    pool = list(avail)
    for c in strong:
        i = next((i for i, w in enumerate(pool)
                  if w == c or c in anc.get(w, set())), None)
        if i is None:
            return False
        del pool[i]
    return True

# ---- independently recompute canonical groups (theorem-only) ----
groups = defaultdict(list)
nterms = ntrunc = 0
for line in open(terms_p, encoding="utf-8"):
    r = json.loads(line)
    nterms += 1
    if r.get("truncated"):
        ntrunc += 1
        continue
    if r.get("kind") != "theorem" or "(c " not in r.get("conclusion", ""):
        continue
    parts = []
    cons = []
    for e in r.get("prefix", []):
        tag, tm = e.split(":", 1)
        if tag == "c":
            parts.append("c:?")
            m = re.search(r"\(c ([^() ]+)\)", tm)
            if m:
                cons.append(m.group(1).split(".")[-1])
        else:
            parts.append(e)
    groups["|".join(parts) + "::" + r["conclusion"]].append(
        (r["name"], cons))
multi = {k: v for k, v in groups.items() if len(v) >= 2}

members_rows = [json.loads(l) for l in open(members_p, encoding="utf-8")]
pairs_rows = [json.loads(l) for l in open(pairs_p, encoding="utf-8")]
summary = json.load(open(summary_p, encoding="utf-8"))

check(nterms == summary["termRows"], f"term rows {nterms} == summary {summary['termRows']}")
check(ntrunc == summary["truncatedSkipped"],
      f"truncated {ntrunc} == summary {summary['truncatedSkipped']}")
check(len(groups) == summary["canonicalGroups"],
      f"canonical groups {len(groups)} == summary {summary['canonicalGroups']}")
check(len(multi) == summary["multiGroups"],
      f"multi groups {len(multi)} == summary {summary['multiGroups']}")
check(len(members_rows) == summary["ladders"],
      f"ladders {len(members_rows)} == summary {summary['ladders']}")
check(len(pairs_rows) == summary["pairs"],
      f"pairs {len(pairs_rows)} == summary {summary['pairs']}")

# ---- every reported chain: distinct members, strict weakening along chain ----
name_to_cons = {}
for k, v in groups.items():
    for n, c in v:
        name_to_cons[n] = c
chain_ok = pair_covered = True
reported_pairs = set()
for r in members_rows:
    ch = r["chain"]
    if len(ch) != len(set(ch)) or len(ch) < 2:
        chain_ok = False
    for a, b in zip(ch, ch[1:]):
        ca, cb = name_to_cons.get(a), name_to_cons.get(b)
        if ca is None or cb is None or not covers(ca, cb):
            chain_ok = False
        reported_pairs.add((a, b))
check(chain_ok, "every chain has distinct members with strict weakening edges")

for p in pairs_rows:
    if (p["strong"], p["weak"]) not in reported_pairs:
        pair_covered = False
check(pair_covered, "every emitted pair is an edge of a reported chain")

# ---- strongest/weakest consistency ----
end_ok = True
for r in members_rows:
    if r["chain"][0] != r["strongest"] or r["chain"][-1] != r["weakest"]:
        end_ok = False
check(end_ok, "strongest/weakest match chain endpoints")

print()
if fails:
    print(f"{len(fails)} CHECK(S) FAILED")
    sys.exit(1)
print("ALL CHECKS PASSED")
