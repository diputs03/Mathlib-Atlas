#!/usr/bin/env python3
"""88_approximate_matcher.py — v2: simhash-cosine blocking.

v1 rare-stem blocking failed the positive-control gate (Fin 13%, Dual 3%,
Twin 0.1%): same-strategy proofs share common structure, not rare lemmas.
A direct probe showed stemmed **token-multiset cosine is 0.91-1.0 across
the Fin family while fragment Jaccard splits (0.05-0.2 across variants)**,
so v2 blocks with Charikar simhash over the stemmed token multiset T.

Fixed design (before looking at unknown results):
  fingerprints over strategy-only `core` trees for ALL real theorems:
    T : token multiset, K tokens operation-stemmed (add/mul, zero/one,
        neg/inv, sub/div) by exact segment replacement
    H : structure-head multiset (A/L/Q/E/J)
    F : fragment set (subtrees size 3..6, cap 300; proofs >4000 nodes: F empty)
  blocking: 64-bit simhash of T, 8 bands x 8 bits -> candidate pairs
  gates  : cos(T) >= 0.80 AND cos(H) >= 0.55
  score  : s = .70*cos(T) + .30*cos(H); fragment J recorded when present
Outputs:
  data/proof_matches.jsonl, data/proof_match_summary.json,
  data/control_gate.json
"""
import json, os, re, math, struct
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
SIZE_CAP = 4000
FRAG_CAP = 300
NBITS, NBAND = 64, 8

def parse(sexp):
    toks = sexp.split(); pos = 0
    def rd():
        nonlocal pos
        t = toks[pos]; pos += 1
        if t.startswith("("):
            ch = []
            while toks[pos] != ")":
                ch.append(rd())
            pos += 1
            return [t] + ch
        return t
    return rd()

def walk(t):
    yield t
    if isinstance(t, list):
        for c in t[1:]:
            yield from walk(c)

SEG = re.compile(r"[A-Z]+(?=[A-Z][a-z]|\b)|[A-Z]?[a-z]+|[0-9]+")
OP = {"add": "#o", "mul": "#o", "zero": "#u", "one": "#u",
      "neg": "#i", "inv": "#i", "sub": "#d", "div": "#d"}
def stem_k(name):
    out = [OP.get(s.lower(), s) for s in SEG.findall(name)]
    return "K" + ".".join(out)

def render(t):
    if isinstance(t, str):
        return t
    return " ".join([t[0]] + [render(c) for c in t[1:]] + [")"])

# ---------------- fingerprints (all real theorems) ----------------
records = {}
n_large = 0
for l in open(os.path.join(DATA, "proof_norm_core.jsonl"), encoding="utf-8"):
    r = json.loads(l)
    tree = parse(r["core"])
    Tc, Hc = Counter(), Counter()
    szmap = {}
    def measure(nd):
        if isinstance(nd, str):
            szmap[id(nd)] = 1; return 1
        s = 1 + sum(measure(c) for c in nd[1:])
        szmap[id(nd)] = s; return s
    total = measure(tree)
    frag_pool = []
    for nd in walk(tree):
        if isinstance(nd, str):
            Tc[stem_k(nd[1:]) if nd.startswith("K") else nd] += 1
        else:
            Hc[nd[0]] += 1
            if 3 <= szmap[id(nd)] <= 6:
                frag_pool.append(render(nd))
    if len(frag_pool) > FRAG_CAP:
        step = len(frag_pool)/FRAG_CAP
        frag_pool = [frag_pool[int(i*step)] for i in range(FRAG_CAP)]
    if total > SIZE_CAP:
        n_large += 1
        frag_pool = []
    records[r["name"]] = {"area": r["area"], "module": r["module"],
                          "T": Tc, "H": Hc, "F": set(frag_pool)}
print("fingerprinted", len(records), "large(no fragments)", n_large,
      flush=True)

# ---------------- simhash over T ----------------
def token_bits(tok):
    h = 0
    for b in struct.pack("<QQ", hash(tok) & 0xFFFFFFFFFFFFFFFF,
                         hash(tok + "|salt2") & 0xFFFFFFFFFFFFFFFF):
        h = (h << 8) | b
    return h & 0xFFFFFFFFFFFFFFFF
tok_cache = {}
def simhash(Tc):
    acc = [0]*NBITS
    for tok, w in Tc.items():
        bits = tok_cache.setdefault(tok, token_bits(tok))
        for i in range(NBITS):
            acc[i] += w if (bits >> i) & 1 else -w
    out = 0
    for i in range(NBITS):
        if acc[i] > 0:
            out |= 1 << i
    return out
names = list(records)
hashes = {}
for i, n in enumerate(names):
    hashes[n] = simhash(records[n]["T"])
    if i % 20000 == 0:
        print("  simhash", i, flush=True)

# band buckets
band_w = NBITS // NBAND
buckets = defaultdict(list)
for n in names:
    h = hashes[n]
    for b in range(NBAND):
        key = (h >> (b*band_w)) & ((1 << band_w) - 1)
        buckets[(b, key)].append(n)
pair = set()
for idxs in buckets.values():
    if len(idxs) > 200:
        continue   # degenerate generic bucket
    for a in range(len(idxs)):
        for b in range(a+1, len(idxs)):
            pair.add((idxs[a], idxs[b]))
print("band candidate pairs:", len(pair), flush=True)

# ---------------- exact gates ----------------
def cos(A, B):
    if not A or not B:
        return 0.0
    small, big = (A, B) if len(A) <= len(B) else (B, A)
    dot = sum(v*big.get(k, 0) for k, v in small.items())
    na = math.sqrt(sum(v*v for v in A.values()))
    nb = math.sqrt(sum(v*v for v in B.values()))
    return dot/(na*nb) if na and nb else 0.0
def jac(F1, F2):
    if not F1 or not F2:
        return None
    inter = len(F1 & F2)
    return inter/(len(F1)+len(F2)-inter)

matches = []
for a, b in pair:
    r1, r2 = records[a], records[b]
    ct, ch = cos(r1["T"], r2["T"]), cos(r1["H"], r2["H"])
    if ct >= 0.80 and ch >= 0.55:
        s = .70*ct + .30*ch
        matches.append({"score": round(s, 3), "a": a, "b": b,
                        "cosT": round(ct, 3), "cosH": round(ch, 3),
                        "fragJ": (lambda x: round(x, 3) if x is not None
                                  else None)(jac(r1["F"], r2["F"])),
                        "crossArea": r1["area"] != r2["area"],
                        "areaA": r1["area"], "areaB": r2["area"]})
matches.sort(key=lambda m: -m["score"])
with open(os.path.join(DATA, "proof_matches.jsonl"), "w",
          encoding="utf-8") as f:
    for m in matches:
        f.write(json.dumps(m, ensure_ascii=False) + "\n")
print("matches:", len(matches), flush=True)

# ---------------- positive-control gate ----------------
ctrl = json.load(open(os.path.join(DATA, "positive_controls.json"),
                      encoding="utf-8"))
adj = defaultdict(set)
for m in matches:
    adj[m["a"]].add(m["b"]); adj[m["b"]].add(m["a"])
def coverage(members):
    members = set(members) & set(records)
    seen, comps = set(), []
    for m in members:
        if m in seen:
            continue
        stack, comp = [m], set()
        while stack:
            x = stack.pop()
            if x in comp:
                continue
            comp.add(x)
            for y in adj[x]:
                if y not in comp:
                    stack.append(y)
        seen |= comp; comps.append(comp)
    comps.sort(key=len, reverse=True)
    if not comps:
        return {"memberCoverage": 0.0, "outsiderRatio": 1.0,
                "components": 0}
    big = comps[0]
    return {"memberCoverage": round(len(big & members)/len(members), 3),
            "outsiderRatio": round(len(big - members)/max(1, len(big)), 3),
            "components": len(comps)}
gate = {f: coverage(m) for f, m in ctrl["families"].items()}
cross = sum(1 for m in matches if m["crossArea"])
summary = {"theorems": len(records), "largeNoFragments": n_large,
           "bandCandidates": len(pair), "matches": len(matches),
           "crossAreaMatches": cross, "controlGate": gate}
json.dump(summary, open(os.path.join(DATA, "proof_match_summary.json"), "w",
                        encoding="utf-8"), ensure_ascii=False, indent=1)
json.dump(gate, open(os.path.join(DATA, "control_gate.json"), "w",
                     encoding="utf-8"), ensure_ascii=False, indent=1)
print(json.dumps(summary, indent=1))
