#!/usr/bin/env python3
"""67_generalization_ladders.py — vertical weakening/generalization ladders.

Different phenomenon from script 64 (parallel cross-area analogies) and 66
(class integration): find theorems with the SAME conclusion/shape where one
carries strictly stronger typeclass constraints than another. The weaker one
generalizes the stronger one; chains of >=3 form a "generalization ladder"
pointing at the most general statement that should exist.

Weakening is tested against Mathlib's real class hierarchy (parents/extends in
atlas_classes.jsonl): constraint multiset A is derivable from B if every class
occurrence in A is matched to an occurrence in B that is the same class or a
transitive ancestor of it (B's class is extended by A's).

Blocks: (conclusionHead, explicit-pi count, nImplicit, nDefault, typeDepth,
typeNodes bucket). Instance binders are excluded from the shape key (they are
exactly what varies under weakening). Diffuse blocks are skipped.

Outputs (data/):
  generalization_ladder_pairs.jsonl   scored stronger->weaker pairs
  generalization_ladders.jsonl        chains/components, longest weakening
  generalization_ladder_summary.json  funnel + top ladders
Pure stdlib, deterministic.
"""
import json, os, re, sys, time
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
SKELETONS = os.path.join(DATA, "atlas_type_skeletons.jsonl")
FEATURES = os.path.join(DATA, "atlas_features.jsonl")
CLASSES = os.path.join(DATA, "atlas_classes.jsonl")

# ---- tunables ----
BLOCK_NODE_DELTA = 8        # |typeNodes diff| allowed within a block
BLOCK_CAP = 400             # blocks larger than this are diffuse, skipped
MAX_NODE_PER_INST = 14      # typeNodes diff per removed instance binder allowed
MATCH_FLOOR = 1.0           # every stronger occurrence must be covered
SHAPE_FLOOR = 0.80          # overall shape similarity floor for emitted pairs
MIN_LADDER = 3              # members in a reported ladder
TOPN = 25
LIMIT = int(os.environ.get("ATLAS_LIMIT", "0"))

def log(msg):
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)

def area_of(module):
    parts = module.split(".")
    return parts[1] if len(parts) > 1 and parts[0] == "Mathlib" else ""

CORE_AREAS = {"Algebra","Analysis","Data","FieldTheory","GroupTheory",
              "LinearAlgebra","Logic","Order","RingTheory","Topology"}

# ---------------------------------------------------------------- hierarchy
def load_hierarchy():
    """short class name -> set(short ancestor names), transitive closure."""
    direct = defaultdict(set)
    full = {}
    for line in open(CLASSES, encoding="utf-8"):
        r = json.loads(line)
        short = r["name"].split(".")[-1]
        full[r["name"]] = True
        for p in r.get("parents", []):
            pn = p["name"]
            if pn.startswith("Lean.Grind."):
                pn = pn[len("Lean.Grind."):]
            direct[short].add(pn.split(".")[-1])
    # transitive closure
    anc = {}
    def ancestors(c, stack):
        if c in anc:
            return anc[c]
        if c in stack:
            return set()
        stack.add(c)
        out = set()
        for p in direct.get(c, ()):  # direct parents
            out.add(p)
            out |= ancestors(p, stack)
        stack.discard(c)
        anc[c] = out
        return out
    for c in list(direct):
        ancestors(c, set())
    return anc

def covers(strong_classes, weak_multiset, anc):
    """Can every occurrence in strong_classes (multiset list) be synthesized
    from weak_multiset (list)? Returns matched count via greedy assignment."""
    avail = list(weak_multiset)
    matched = 0
    for c in strong_classes:
        hit = None
        for i, w in enumerate(avail):
            if w == c or c in anc.get(w, set()):
                hit = i
                break
        if hit is None:
            return matched, False
        del avail[hit]
        matched += 1
    return matched, True

GENERIC_TOKENS = {"the","lemma","proof","left","right","iff","eq","ne","le",
    "lt","ge","gt","zero","one","add","sub","mul","div","neg","inv","map",
    "bind","pure","id","comp","sup","inf","bot","top","mem","not","and","or",
    "forall","exists","to","of","coe","apply","mk","get","set","has","self",
    "inst","def","aux","rec","cases","int","nat","bool","type","prop","val",
    "spec","defn","thm","self","iff","ne","pos","neg","comm","assoc"}
_camel = re.compile(r"[A-Za-z]+")
def name_tokens(name):
    out = set()
    for part in name.split("."):
        for token in _camel.findall(part):
            token = token.lower()
            if len(token) >= 3 and token not in GENERIC_TOKENS:
                out.add(token)
    return out

# ---------------------------------------------------------------- load
log("loading class hierarchy ...")
anc = load_hierarchy()
log(f"hierarchy entries: {len(anc)}")

log("loading features (shape numbers) ...")
shape = {}
for line in open(FEATURES, encoding="utf-8"):
    r = json.loads(line)
    shape[r["name"]] = (r.get("typeNodes", 0), r.get("typeDepth", 0),
                        r.get("typeConsts", 0))
log(f"features: {len(shape)}")

log("loading skeletons ...")
nodes = {}
skipped_noncore = skipped_kind = skipped_head = 0
for line in open(SKELETONS, encoding="utf-8"):
    r = json.loads(line)
    name = r["name"]
    # generated instance-proof obligations and private simp lemmas are not
    # user-facing theorems: inst*.eq_N / ._proof_N / ._simp_N / _private
    if name.startswith("_private") or re.search(
            r"(\._proof_|\._simp_|\.eq_\d|_aux_|mkEq|ofEq)", name):
        skipped_head += 1
        continue
    module = r.get("module", "")
    a = area_of(module)
    if a not in CORE_AREAS:
        skipped_noncore += 1
        continue
    if r.get("kind") != "theorem":
        skipped_kind += 1
        continue
    ch = r.get("conclusionHead", "")
    if not ch or ch in {"Forall","Functor"}:
        skipped_head += 1
        continue
    cons = [c["class"] for c in r.get("constraints", []) for _ in range(c.get("count", 1))]
    npi = r.get("nPi", 0)
    ninst = r.get("nInstImplicit", 0)
    nexpl = npi - ninst
    tn, td, tc = shape.get(name, (0, 0, 0))
    if tn == 0:
        continue
    nsroot = name.split(".")[0]
    nodes[name] = dict(name=name, module=module, area=a, nsroot=nsroot,
                       head=ch, cons=cons, nexpl=nexpl, tokens=name_tokens(name),
                       nimp=r.get("nImplicit",0), ndef=r.get("nDefault",0),
                       ninst=ninst, tn=tn, td=td, tc=tc)
log(f"eligible theorem nodes: {len(nodes)} (noncore {skipped_noncore}, "
    f"kind {skipped_kind}, head {skipped_head})")

# ---------------------------------------------------------------- block
blocks = defaultdict(list)
for r in nodes.values():
    key = (r["head"], r["nexpl"], r["nimp"], r["ndef"], r["td"],
           r["tn"] // (BLOCK_NODE_DELTA + 1))
    blocks[key].append(r["name"])
log(f"blocks: {len(blocks)}")

# ---------------------------------------------------------------- pairs
pairs = []
blocks_used = blocks_diffuse = 0
for key, members in blocks.items():
    if len(members) < 2:
        continue
    if len(members) > BLOCK_CAP:
        blocks_diffuse += 1
        continue
    blocks_used += 1
    ms = [nodes[n] for n in members]
    for i in range(len(ms)):
        for j in range(i + 1, len(ms)):
            x, y = ms[i], ms[j]
            if abs(x["tn"] - y["tn"]) > BLOCK_NODE_DELTA:
                continue
            # per-instance-binder shape budget
            inst_delta = abs(x["ninst"] - y["ninst"])
            if abs(x["tn"] - y["tn"]) > MAX_NODE_PER_INST * max(1, inst_delta):
                continue
            if abs(x["tc"] - y["tc"]) > max(2, inst_delta + 1):
                continue
            # same-construction evidence: shared namespace AND a shared rare
            # name token (vertical ladders live within a construction family)
            if x["nsroot"] != y["nsroot"]:
                continue
            if not (x["tokens"] & y["tokens"]):
                continue
            # decide direction from constraints
            mx, fully_x = covers(x["cons"], y["cons"], anc)
            my, fully_y = covers(y["cons"], x["cons"], anc)
            if fully_x and fully_y:
                continue  # equi-strength (or same classes) -> script 64 territory
            strong, weak, matched, total = None, None, 0, 0
            if fully_x and not fully_y:
                strong, weak, matched, total = x, y, mx, len(x["cons"])
            elif fully_y and not fully_x:
                strong, weak, matched, total = y, x, my, len(y["cons"])
            else:
                continue  # incomparable hypotheses
            coverage = matched / max(1, total)
            if coverage < MATCH_FLOOR:
                continue
            # shape similarity (type nodes/consts agreement)
            tn_sim = 1 - abs(x["tn"] - y["tn"]) / max(x["tn"], y["tn"], 1)
            tc_sim = 1 - abs(x["tc"] - y["tc"]) / max(x["tc"], y["tc"], 1)
            shape_score = 0.7 * tn_sim + 0.3 * tc_sim
            if shape_score < SHAPE_FLOOR:
                continue
            gained = len(strong["cons"]) - matched
            pairs.append(dict(
                strong=strong["name"], weak=weak["name"],
                strongArea=strong["area"], weakArea=weak["area"],
                strongNs=strong["nsroot"], weakNs=weak["nsroot"],
                strongCons=strong["cons"], weakCons=weak["cons"],
                coverage=round(coverage, 4),
                shapeScore=round(shape_score, 4),
                redundant=strong["ninst"] - weak["ninst"],
                crossArea=strong["area"] != weak["area"],
                crossNs=strong["nsroot"] != weak["nsroot"]))
log(f"blocks used {blocks_used}; diffuse skipped {blocks_diffuse}")
log(f"weakening pairs: {len(pairs)}")

# ---------------------------------------------------------------- ladders
# Components over pairs; rank members by constraint strength (number of
# synthesizable descendants within the component), longest weakening chain.
parent = {}
def find(x):
    parent.setdefault(x, x)
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x
def union(a, b):
    ra, rb = find(a), find(b)
    if ra != rb:
        parent[ra] = rb

for p in pairs:
    union(p["strong"], p["weak"])

comp = defaultdict(list)
for n in parent:
    comp[find(n)].append(n)

ladders = []
for root, members in comp.items():
    if len(members) < MIN_LADDER:
        continue
    # strength index: how many component members' constraints this one covers
    idx = {m: nodes[m] for m in members if m in nodes}
    strength = {}
    for m, r in idx.items():
        s = 0
        for m2, r2 in idx.items():
            if m == m2:
                continue
            _, ok = covers(r["cons"], r2["cons"], anc)
            if ok:
                s += 1
        strength[m] = s
    ordered = sorted(idx, key=lambda m: -strength[m])
    chain = [ordered[0]]
    for m in ordered[1:]:
        last = idx[chain[-1]]
        _, down = covers(idx[m]["cons"], last["cons"], anc)
        _, up = covers(last["cons"], idx[m]["cons"], anc)
        if up and not down:  # m strictly weaker than chain tip
            chain.append(m)
    areas = sorted({idx[m]["area"] for m in chain if m in idx})
    ns = sorted({idx[m]["nsroot"] for m in chain if m in idx})
    strongest = chain[0] if chain else ordered[0]
    weakest = chain[-1] if chain else ordered[-1]
    ladders.append(dict(
        members=ordered, chain=chain,
        length=len(chain), size=len(members),
        areas=areas, namespaces=ns,
        crossArea=len(areas) > 1, crossNs=len(ns) > 1,
        strongest=strongest, weakest=weakest,
        strongestCons=idx[strongest]["cons"] if strongest in idx else [],
        weakestCons=idx[weakest]["cons"] if weakest in idx else []))
ladders.sort(key=lambda l: (-l["length"], -l["size"], -int(l["crossArea"])))
log(f"ladders (>= {MIN_LADDER}): {len(ladders)}")

# ---------------------------------------------------------------- emit
with open(os.path.join(DATA, "generalization_ladder_pairs.jsonl"), "w",
          encoding="utf-8") as f:
    for p in sorted(pairs, key=lambda q: (-q["shapeScore"], q["strong"])):
        f.write(json.dumps(p, ensure_ascii=False) + "\n")
with open(os.path.join(DATA, "generalization_ladders.jsonl"), "w",
          encoding="utf-8") as f:
    for l in ladders:
        f.write(json.dumps(l, ensure_ascii=False) + "\n")

cross = sum(1 for p in pairs if p["crossArea"])
summary = dict(
    eligibleNodes=len(nodes), blocks=len(blocks), blocksUsed=blocks_used,
    blocksDiffuse=blocks_diffuse, pairs=len(pairs), crossAreaPairs=cross,
    ladders=len(ladders), crossAreaLadders=sum(1 for l in ladders if l["crossArea"]),
    topLadders=[{k: v for k, v in ld.items() if k in
                 ("length","size","areas","namespaces","crossArea","strongest",
                  "weakest","strongestCons","weakestCons","chain")}
                for ld in ladders[:TOPN]],
    topPairs=sorted([{k: v for k, v in pr.items()} for pr in pairs],
                    key=lambda q: (-q["shapeScore"], -q["redundant"]))[:TOPN])
with open(os.path.join(DATA, "generalization_ladder_summary.json"), "w",
          encoding="utf-8") as f:
    json.dump(summary, f, ensure_ascii=False, indent=2)

log("top ladders:")
for ld in ladders[:12]:
    log(f"  len={ld['length']} size={ld['size']} areas={ld['areas']} "
        f"cross={ld['crossArea']}  {ld['strongest']}  ==>  {ld['weakest']}")
log(f"pairs={len(pairs)} (cross-area {cross}); ladders={len(ladders)}")
