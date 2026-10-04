#!/usr/bin/env python3
"""69_precise_generalization_ladders.py — term-precise vertical ladders.

Replaces script 67's coarse shape heuristic with exact conclusion-term
evidence (data/atlas_conclusion_terms.jsonl from Lean script 68):

* Canonical statement key: the full type with every instance-implicit binder's
  TYPE replaced by a fixed hole (binder positions and de Bruijn indices kept),
  plus the conclusion. Two theorems with the same key are the SAME statement
  with the only difference being the exact typeclass constraints.
* Constraint multiset per theorem = class heads of the instance binders.
* Direction via Mathlib's real class hierarchy (atlas_classes parents): the
  member whose constraints are all synthesized from another's is the stronger
  one. Each canonical group with >=2 strength levels is a ladder.

Outputs:
  data/precise_ladder_members.jsonl   one row per canonical statement group
  data/precise_ladder_pairs.jsonl     stronger->weaker pairs within groups
  data/precise_ladder_summary.json    funnel + strongest ladders
Pure stdlib, deterministic.
"""
import json, os, re, time
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
TERMS = os.path.join(DATA, "atlas_conclusion_terms.jsonl")
CLASSES = os.path.join(DATA, "atlas_classes.jsonl")
TOPN = 30

def log(msg):
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)

def area_of(module):
    p = module.split(".")
    return p[1] if len(p) > 1 and p[0] == "Mathlib" else ""

# ---------------------------------------------------------------- hierarchy
log("loading class hierarchy ...")
direct = defaultdict(set)
for line in open(CLASSES, encoding="utf-8"):
    r = json.loads(line)
    short = r["name"].split(".")[-1]
    for p in r.get("parents", []):
        pn = p["name"]
        if pn.startswith("Lean.Grind."):
            pn = pn[len("Lean.Grind."):]
        direct[short].add(pn.split(".")[-1])
anc = {}
def ancestors(c, stack):
    if c in anc:
        return anc[c]
    if c in stack:
        return set()
    stack.add(c)
    out = set()
    for p in direct.get(c, ()):
        out.add(p); out |= ancestors(p, stack)
    stack.discard(c)
    anc[c] = out
    return out
for c in list(direct):
    ancestors(c, set())
log(f"hierarchy entries: {len(anc)}")

_CONST_RE = re.compile(r"\(c ([^() ]+)\)")
def class_head(term):
    """Head class of an instance-binder term: the leftmost/app-head constant.
    Terms look like (a (a (c Group) (c Nat)) ..) -> the head const is the one
    reached by following the app spine, which the encoding prints first."""
    t = term.strip()
    # follow spine: (a fn arg) -> fn
    while t.startswith("(a "):
        depth = 0
        i = 3
        # split top-level fn/arg
        started = i
        parts = []
        d = 0
        for k in range(i, len(t) - 1):
            ch = t[k]
            if ch == '(':
                d += 1
            elif ch == ')':
                if d == 0:
                    parts.append(t[started:k])
                    break
                d -= 1
            elif ch == ' ' and d == 0:
                parts.append(t[started:k])
                started = k + 1
        if parts:
            t = parts[0].strip()
        else:
            break
    m = _CONST_RE.fullmatch(t)
    if m:
        return m.group(1).split(".")[-1]
    m = _CONST_RE.search(t)
    return m.group(1).split(".")[-1] if m else ""

def covers(strong, avail):
    """Match every strong class occurrence to an available occurrence that is
    equal or a transitive descendant (avail class extended by strong)."""
    pool = list(avail)
    n = 0
    for c in strong:
        hit = next((i for i, w in enumerate(pool)
                    if w == c or c in anc.get(w, set())), None)
        if hit is None:
            return n, False
        del pool[hit]; n += 1
    return n, True

# ---------------------------------------------------------------- load terms
log("loading conclusion terms ...")
groups = defaultdict(list)
nrows = ntrunc = skipped_kind = 0
for line in open(TERMS, encoding="utf-8"):
    r = json.loads(line)
    nrows += 1
    if r.get("truncated"):
        ntrunc += 1
        continue
    if r.get("kind") != "theorem":
        skipped_kind += 1
        continue
    # the conclusion must carry an asserted relation (a constant), else the
    # statement identity is only the declaration name itself
    if "(c " not in r.get("conclusion", ""):
        skipped_kind += 1
        continue
    pfx = r.get("prefix", [])
    # canonical key: hole out instance-binder types, keep everything else
    canon_parts = []
    constraints = []
    for entry in pfx:
        tag, tm = entry.split(":", 1)
        if tag == "c":
            canon_parts.append("c:?")
            h = class_head(tm)
            if h:
                constraints.append(h)
        else:
            canon_parts.append(entry)
    key = "|".join(canon_parts) + "::" + r.get("conclusion", "")
    groups[key].append(dict(
        name=r["name"], kind=r["kind"], module=r.get("module", ""),
        area=area_of(r.get("module", "")), constraints=constraints))
log(f"term rows {nrows} (truncated skipped {ntrunc}, kind skipped {skipped_kind})")
log(f"canonical statement groups: {len(groups)}")

# --------------------------------------------------------- ladders & pairs
multi = {k: v for k, v in groups.items() if len(v) >= 2}
log(f"groups with >=2 members: {len(multi)}")

ladder_rows = []
pairs_out = []
n_ladder = n_crossarea = 0
strength_cache = {}
for key, members in multi.items():
    # dedupe identical constraint multisets into levels; order by strength
    def is_stronger(ca, cb):
        _, ok = covers(ca, cb)
        return ok
    # strength = number of members this one's constraints cover derivability of
    def strength(i):
        if (key, i) in strength_cache:
            return strength_cache[(key, i)]
        s = 0
        for j, b in enumerate(members):
            if j != i and is_stronger(members[i]["constraints"], b["constraints"]):
                s += 1
        strength_cache[(key, i)] = s
        return s
    order = sorted(range(len(members)), key=lambda i: -strength(i))
    levels = []
    for i in order:
        if not levels or members[levels[-1]]["constraints"] != members[i]["constraints"]:
            levels.append(i)
    # a ladder needs a strict weakening chain among distinct levels
    chain = [levels[0]]
    for li in levels[1:]:
        tip = members[chain[-1]]
        cur = members[li]
        down = is_stronger(tip["constraints"], cur["constraints"])
        up = is_stronger(cur["constraints"], tip["constraints"])
        if down and not up:
            chain.append(li)
    if len(chain) < 2:
        continue
    n_ladder += 1
    areas = sorted({members[i]["area"] for i in chain})
    ns = sorted({members[i]["name"].split(".")[0] for i in chain})
    cross_area = len(areas) > 1
    if cross_area:
        n_crossarea += 1
    ordered_members = [members[i] for i in order]
    ladder_rows.append(dict(
        key=key, size=len(members), chainLength=len(chain), areas=areas,
        namespaces=ns, crossArea=cross_area, crossNs=len(ns) > 1,
        strongest=ordered_members[0]["name"],
        weakest=members[chain[-1]]["name"],
        strongestCons=ordered_members[0]["constraints"],
        weakestCons=members[chain[-1]]["constraints"],
        chain=[members[i]["name"] for i in chain],
        members=[{"name": m["name"], "area": m["area"],
                  "module": m["module"], "constraints": m["constraints"]}
                 for m in ordered_members]))
    # pairs along the chain (adjacent levels)
    for a_i, b_i in zip(chain, chain[1:]):
        pairs_out.append(dict(strong=members[a_i]["name"],
                              weak=members[b_i]["name"],
                              strongCons=members[a_i]["constraints"],
                              weakCons=members[b_i]["constraints"],
                              areas=areas, crossArea=cross_area))

ladder_rows.sort(key=lambda l: (-l["chainLength"], -l["size"],
                                -int(l["crossArea"])))
log(f"term-precise ladders: {n_ladder} (cross-area {n_crossarea})")

with open(os.path.join(DATA, "precise_ladder_members.jsonl"), "w",
          encoding="utf-8") as f:
    for row in ladder_rows:
        f.write(json.dumps(row, ensure_ascii=False) + "\n")
with open(os.path.join(DATA, "precise_ladder_pairs.jsonl"), "w",
          encoding="utf-8") as f:
    for p in pairs_out:
        f.write(json.dumps(p, ensure_ascii=False) + "\n")

summary = dict(termRows=nrows, truncatedSkipped=ntrunc,
               canonicalGroups=len(groups), multiGroups=len(multi),
               ladders=n_ladder, crossAreaLadders=n_crossarea,
               pairs=len(pairs_out),
               topLadders=[{k: v for k, v in row.items() if k in
                            ("chainLength","size","areas","namespaces",
                             "crossArea","strongest","weakest",
                             "strongestCons","weakestCons","chain")}
                           for row in ladder_rows[:TOPN]])
with open(os.path.join(DATA, "precise_ladder_summary.json"), "w",
          encoding="utf-8") as f:
    json.dump(summary, f, ensure_ascii=False, indent=2)

for row in ladder_rows[:15]:
    log(f"  len={row['chainLength']} size={row['size']} areas={row['areas']} "
        f"cross={row['crossArea']}  {row['strongest']} ==> {row['weakest']}")
log(f"ladders={n_ladder} pairs={len(pairs_out)}")
