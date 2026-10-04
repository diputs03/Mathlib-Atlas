#!/usr/bin/env python3
"""86_normalized_proof_trees.py — normalized proof representation.

Input : data/proof_skeletons_core.jsonl  (raw skeleton = ground truth)
Output: data/proof_norm_core.jsonl  rows {name, module, area, norm, core}

Layers:
  raw skeleton  (ground truth, untouched)
    -> norm  canonicalized tree:
         - leaves B/F/M -> V, Ln/Ls -> N/S, PRIV -> G
         - projection indices erased: (Jn -> (J
         - interval endpoint constants -> P (parameter, not strategy)
         - endpoint suffix of lemma names stemmed: image_castAdd_Icc
           -> image_castAdd_#
         - small coercion-headed application idioms -> C
         - small min/max endpoint constructions -> P
         - (A Kid x) -> x ; unused let bindings (no V in body) dropped
    -> core  norm with C/P leaves pruned and app spines re-collapsed;
         this is the strategy-only view for fingerprints.

The normalizer is deliberately conservative: theorem identity (K tokens)
is kept apart from endpoint/coercion canonicalization, so proofs cannot
all collapse into one generic skeleton.
"""
import json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")

ENDPOINTS = {"Icc", "Ico", "Ioc", "Ioo", "Iic", "Ici", "uIcc", "Ioi", "Iio"}
COERCE = {"ofNat", "ofInt", "cast", "ofFin", "natCast", "intCast",
          "toNat", "toInt", "ofBool", "uintCast", "ofNat'", "castNat"}
ENDPOINT_SUFFIX = re.compile(
    r"_(Icc|Ico|Ioc|Ioo|Iic|Ici|uIcc|Ioi|Iio)$")
HELPER = re.compile(r"^_private|._proof_|._simp_|\.eq_\d+$")

def is_helper(name):
    return (name.startswith("_private") or "._proof_" in name
            or "._simp_" in name
            or re.search(r"\.eq_\d+$", name) is not None)

# ---- S-expression parse (tokens already space separated) ----
def parse(sexp):
    toks = sexp.split()
    pos = 0
    def rd():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t.startswith("("):
            children = []
            while toks[pos] != ")":
                children.append(rd())
            pos += 1
            return [t] + children
        return t
    out = rd()
    assert pos == len(toks)
    return out

def size(t):
    return 1 if isinstance(t, str) else sum(size(c) for c in t)

def has_leaf(t, leaf):
    if isinstance(t, str):
        return t == leaf
    return any(has_leaf(c, leaf) for c in t)

def map_tree(t, f):
    """bottom-up transform; f returns (replaced, newnode-or-None)."""
    if isinstance(t, str):
        return f(t)
    children = [map_tree(c, f) for c in t]
    return f(children)

# ---- normalization ----
def norm_leaf(tok):
    if tok in ("B", "F", "M"):
        return "V"
    if tok == "Ln":
        return "N"
    if tok == "Ls":
        return "S"
    if tok == "PRIV":
        return "G"
    if tok in ("REC", "TOPROJ", "INST", "T"):
        return tok
    if tok.startswith("K"):
        nm = tok[1:]
        if nm in ENDPOINTS:
            return "P"
        if nm in COERCE:
            return "C"
        m = ENDPOINT_SUFFIX.search(nm)
        if m:
            return "K" + nm[:m.start()] + "_#"
        return tok
    if re.fullmatch(r"J\d+", tok):
        return "J"
    return tok

def normalize(t):
    """returns (node, size, hasBoundVar); size computed bottom-up once."""
    if isinstance(t, str):
        l = norm_leaf(t)
        return l, 1, (t == "B")
    head = t[0]
    ch = [normalize(c) for c in t[1:]]
    nodes = [c[0] for c in ch]
    sz = 1 + sum(c[1] for c in ch)
    hb = any(c[2] for c in ch)
    if re.fullmatch(r"\(J\d+", head):
        return ["(J"] + nodes, sz, hb
    if head == "(E":
        ty, val, body = nodes
        hb_body = ch[2][2]
        # drop unused let: body never references a bound variable
        if not hb_body:
            return body, ch[2][1], ch[2][2]
        return ["(E", ty, val, body], sz, hb
    if head == "(A":
        fn, arg = nodes
        fn_sz, arg_sz = ch[0][1], ch[1][1]
        # id wrapper
        if fn == "Kid":
            return arg, arg_sz, ch[1][2]
        # coercion idiom: coercion-headed small application
        if fn == "C" and 1 + fn_sz + arg_sz <= 12:
            return "C", 1, False
        if isinstance(fn, list) and fn[0] == "(A" and fn[1] == "C" \
           and 1 + fn_sz + arg_sz <= 12:
            return "C", 1, False
        # min/max endpoint construction
        if isinstance(fn, str) and fn in ("Kmin", "Kmax") \
           and 1 + fn_sz + arg_sz <= 14:
            return "P", 1, False
        if isinstance(fn, list) and fn[0] == "(A" \
           and isinstance(fn[1], str) and fn[1] in ("Kmin", "Kmax") \
           and 1 + fn_sz + arg_sz <= 14:
            return "P", 1, False
        return ["(A", fn, arg], sz, hb
    return [head] + nodes, sz, hb

# ---- core: prune C/P leaves, collapse app spines ----
def to_core(t):
    """returns (node-or-None, size)."""
    if isinstance(t, str):
        return (None, 0) if t in ("C", "P") else (t, 1)
    ch = []
    for c in t[1:]:
        n_, s_ = to_core(c)
        if n_ is not None:
            ch.append((n_, s_))
    head = t[0]
    if head == "(A":
        if not ch:
            return None, 0
        if len(ch) == 1:
            return ch[0]
        return ["(A"] + [x[0] for x in ch], 1 + sum(x[1] for x in ch)
    if re.fullmatch(r"\(J\d+", head) or head == "(J":
        return ch[0] if ch else (None, 0)
    if not ch:
        return None, 0
    return [head] + [x[0] for x in ch], 1 + sum(x[1] for x in ch)

def render(t):
    if isinstance(t, str):
        return t
    return " ".join([t[0]] + [render(c) for c in t[1:]] + [")"])

def main():
    outp = os.path.join(DATA, "proof_norm_core.jsonl")
    n = kept = 0
    per_area = {}
    with open(os.path.join(DATA, "proof_skeletons_core.jsonl"),
              encoding="utf-8") as f, \
         open(outp, "w", encoding="utf-8") as out:
        for line in f:
            r = json.loads(line)
            n += 1
            if is_helper(r["name"]):
                continue
            tree = parse(r["skeleton"])
            nt, _, _ = normalize(tree)
            ct, _ = to_core(nt)
            if ct is None:
                ct = "V"
            kept += 1
            per_area[r["area"]] = per_area.get(r["area"], 0) + 1
            out.write(json.dumps({"name": r["name"], "module": r["module"],
                                  "area": r["area"], "norm": render(nt),
                                  "core": render(ct)},
                                 ensure_ascii=False) + "\n")
            if kept % 2000 == 0:
                out.flush()
                print(f"  {kept} rows...", flush=True)
    print(f"read {n}; normalized real theorems {kept}")
    print(json.dumps(per_area, indent=1))

if __name__ == "__main__":
    main()
