#!/usr/bin/env python3
"""70_equiv_candidates.py — Equiv/transport candidate generation.

Decision-gate experiment, scope kept deliberately narrow:
* isomorphism type: plain `Equiv` only (every other bundled iso in Mathlib is
  an Equiv with extra fields; its transport questions reduce to this case).
* carriers: Equiv declarations whose conclusion is `(c Equiv) α β`, where BOTH
  α and β are constructor-headed types (bare-variable carriers have no API
  footprint to compare).
* API footprint of a constructor T = declarations referencing T (reference
  edges, core Mathlib areas).
* transported counterpart test: canonical statement key = 69's key (instance
  binder types holed) with the two carrier constants also replaced by a fixed
  token. Keys present on both sides = symmetric API; one-sided keys = gap.
* instance footprint: className sets (atlas_instances, targetHead) per side.

Outputs:
  data/equiv_candidates.jsonl          one row per constructor pair
  data/equiv_gap_declarations.jsonl    asymmetric declarations (capped)
  data/equiv_candidate_summary.json    funnel
Pure stdlib, deterministic.
"""
import json, os, time
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
TERMS = os.path.join(DATA, "atlas_conclusion_terms.jsonl")
EDGES = os.path.join(DATA, "atlas_edges.jsonl")
INSTANCES = os.path.join(DATA, "atlas_instances.jsonl")
MIN_FOOTPRINT = 20
MIN_GAP = 5
GAP_CAP = 400

def log(msg):
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)

# ------------------------------------------------------------- term parsing
def split_app(t):
    """(a fn arg) -> (fn, arg) at top level; else None."""
    if not t.startswith("(a "):
        return None
    d = 0
    parts = []
    start = 3
    for k in range(3, len(t)):
        ch = t[k]
        if ch == '(':
            d += 1
        elif ch == ')':
            if d == 0:
                parts.append(t[start:k]); break
            d -= 1
        elif ch == ' ' and d == 0:
            parts.append(t[start:k]); start = k + 1
    if len(parts) == 2:
        return parts[0], parts[1]
    return None

def spine(t):
    """head term + list of args."""
    args = []
    while True:
        s = split_app(t)
        if s is None:
            return t, args
        args.append(s[1]); t = s[0]

def const_name(t):
    t = t.strip()
    if t.startswith("(c ") and t.endswith(")"):
        inner = t[3:-1]
        if " " not in inner:
            return inner
    return None

def carrier_head(t):
    head, _ = spine(t)
    return const_name(head)

# --------------------------------------------- pass A: Equiv declarations
log("pass A: scanning conclusion terms for Equiv witnesses ...")
# keep term rows for every declaration we may need canonical keys for:
# store only prefix/conclusion compactly; the file is 1.16GB -> ~40-80k rows
# of raw strings for carrier-related decls only, decided after pass B. Instead
# retain ALL rows' (name, prefix list, conclusion) — measured acceptable:
# 225k rows of python strings previously ~ a few GB; safer to store only the
# pieces needed: name -> (prefix tuple, conclusion)
terms_store = {}
pairs = defaultdict(lambda: dict(witnesses=[], uniform=0))
n_iso = n_ctor = 0
for line in open(TERMS, encoding="utf-8"):
    r = json.loads(line)
    terms_store[r["name"]] = (r.get("prefix", []), r.get("conclusion", ""),
                              r.get("module", ""), r.get("kind", ""))
    concl = r.get("conclusion", "")
    s1 = split_app(concl)
    if s1 is None:
        continue
    fn1, beta = s1
    s0 = split_app(fn1)
    if s0 is None:
        continue
    head_t, alpha = s0
    if const_name(head_t) != "Equiv":
        continue
    n_iso += 1
    ca, cb = carrier_head(alpha), carrier_head(beta)
    if not ca or not cb or ca == cb:
        continue
    n_ctor += 1
    key = tuple(sorted((ca, cb)))
    rec = pairs[key]
    rec["witnesses"].append(dict(name=r["name"], alpha=alpha, beta=beta,
                                 module=r.get("module", "")))
    # uniform family equivalence: carriers agree after holing the two
    # constructor constants (e.g. WithBot α vs Option α with same bvar)
    def hole(t, x, y):
        return t.replace(f"(c {x})", "(c K)").replace(f"(c {y})", "(c K)")
    if hole(alpha, ca, cb) == hole(beta, ca, cb):
        rec["uniform"] += 1
log(f"Equiv witnesses: {n_iso}; with two constructor carriers: {n_ctor}; "
    f"constructor pairs: {len(pairs)}")

carriers = set()
for a, b in pairs:
    carriers.add(a); carriers.add(b)

# --------------------------------------------- pass B: reference footprints
log("pass B: streaming reference edges for carrier footprints ...")
# source -> bitmask of carriers referenced
carrier_idx = {c: i for i, c in enumerate(sorted(carriers))}
src_mask = {}
n_edges = n_kept = 0
for line in open(EDGES, encoding="utf-8"):
    n_edges += 1
    if n_edges % 4_000_000 == 0:
        log(f"  edges scanned {n_edges/1e6:.0f}M, kept {n_kept}")
    # cheap pre-filter
    if "(c " not in line[:0] or '"target"' not in line:
        pass
    r = json.loads(line)
    tgt = r["target"]
    ci = carrier_idx.get(tgt)
    if ci is None:
        continue
    src = r["source"]
    if src not in terms_store:
        continue  # outside core-area term layer
    src_mask[src] = src_mask.get(src, 0) | (1 << ci)
    n_kept += 1
log(f"edges scanned {n_edges}; carrier-related sources: {len(src_mask)}; "
    f"kept edge rows {n_kept}")

# --------------------------------------------- instance footprints
log("pass C: instance footprints ...")
inst_classes = defaultdict(set)
for line in open(INSTANCES, encoding="utf-8"):
    r = json.loads(line)
    if not r.get("mathlib"):
        continue
    th = r.get("targetHead")
    if th in carriers:
        inst_classes[th].add(r["className"])

# --------------------------------------------- canonical keys w/ carriers
def canon_key(prefix, conclusion, a, b):
    """69 key (instance binder types -> ?) with carrier consts -> K."""
    parts = []
    for e in prefix:
        tag, tm = e.split(":", 1)
        if tag == "c":
            parts.append("c:?")
        else:
            parts.append(tag + ":" + tm.replace(f"(c {a})", "(c K)")
                         .replace(f"(c {b})", "(c K)"))
    return "|".join(parts) + "::" + conclusion.replace(f"(c {a})", "(c K)") \
        .replace(f"(c {b})", "(c K)")

log("pass D: per-pair gap computation ...")
out_rows = []
gap_decl_rows = []
n_eligible = 0
for (a, b), rec in pairs.items():
    ia, ib = carrier_idx[a], carrier_idx[b]
    ba, bb = 1 << ia, 1 << ib
    side_a, side_b, bridges = {}, {}, 0
    for src, mask in src_mask.items():
        ina = bool(mask & ba); inb = bool(mask & bb)
        if ina and inb:
            bridges += 1
        elif ina:
            side_a[src] = mask
        elif inb:
            side_b[src] = mask
    if len(side_a) + bridges < MIN_FOOTPRINT or \
       len(side_b) + bridges < MIN_FOOTPRINT:
        continue
    # canonical keys per side, ignoring decls that reference OTHER carriers
    keys_a = defaultdict(list); keys_b = defaultdict(list)
    for src in side_a:
        if side_a[src] & ~(ba):
            continue  # decl about a third constructor: not clean API evidence
        pfx, concl, mod, kind = terms_store[src]
        keys_a[canon_key(pfx, concl, a, b)].append(src)
    for src in side_b:
        if side_b[src] & ~(bb):
            continue
        pfx, concl, mod, kind = terms_store[src]
        keys_b[canon_key(pfx, concl, a, b)].append(src)
    gap_a = {k: v for k, v in keys_a.items() if k not in keys_b}
    gap_b = {k: v for k, v in keys_b.items() if k not in keys_a}
    matched = sum(1 for k in keys_a if k in keys_b)
    n_gap_decls_a = sum(len(v) for v in gap_a.values())
    n_gap_decls_b = sum(len(v) for v in gap_b.values())
    if max(n_gap_decls_a, n_gap_decls_b) < MIN_GAP:
        continue
    n_eligible += 1
    ca_inst = inst_classes.get(a, set()); cb_inst = inst_classes.get(b, set())
    row = dict(
        pair=[a, b], nWitnesses=len(rec["witnesses"]),
        uniformWitnesses=rec["uniform"],
        witnesses=[w["name"] for w in rec["witnesses"]][:12],
        footprintA=len(side_a) + bridges, footprintB=len(side_b) + bridges,
        oneSidedA=len(side_a), oneSidedB=len(side_b), bridges=bridges,
        keysA=len(keys_a), keysB=len(keys_b), matchedKeys=matched,
        gapKeysA=len(gap_a), gapKeysB=len(gap_b),
        gapDeclsA=n_gap_decls_a, gapDeclsB=n_gap_decls_b,
        instanceClassesA=sorted(ca_inst), instanceClassesB=sorted(cb_inst),
        instanceGapA=sorted(ca_inst - cb_inst),
        instanceGapB=sorted(cb_inst - ca_inst),
        instanceShared=sorted(ca_inst & cb_inst))
    out_rows.append(row)
    # gap declaration evidence, capped per pair
    for side, gap, other in (("A", gap_a, b), ("B", gap_b, a)):
        n = 0
        for k, srcs in gap.items():
            for s in srcs:
                if n >= GAP_CAP // 2:
                    break
                _, _, mod, kind = terms_store[s]
                gap_decl_rows.append(dict(pair=[a, b], side=side, name=s,
                                          module=mod, kind=kind, key=k))
                n += 1
            if n >= GAP_CAP // 2:
                break

out_rows.sort(key=lambda r: -(r["gapDeclsA"] + r["gapDeclsB"]))
log(f"eligible pairs (footprint + gap floors): {n_eligible}")

with open(os.path.join(DATA, "equiv_candidates.jsonl"), "w",
          encoding="utf-8") as f:
    for r in out_rows:
        f.write(json.dumps(r, ensure_ascii=False) + "\n")
with open(os.path.join(DATA, "equiv_gap_declarations.jsonl"), "w",
          encoding="utf-8") as f:
    for r in gap_decl_rows:
        f.write(json.dumps(r, ensure_ascii=False) + "\n")
summary = dict(isoWitnesses=n_iso, ctorWitnesses=n_ctor,
               constructorPairs=len(pairs), eligiblePairs=n_eligible,
               gapDeclarationRows=len(gap_decl_rows),
               edgesScanned=n_edges, carrierRelatedSources=len(src_mask),
               params=dict(MIN_FOOTPRINT=MIN_FOOTPRINT, MIN_GAP=MIN_GAP,
                           GAP_CAP=GAP_CAP),
               topPairs=[{k: r[k] for k in
                          ("pair","nWitnesses","uniformWitnesses",
                           "footprintA","footprintB","matchedKeys",
                           "gapDeclsA","gapDeclsB","instanceGapA",
                           "instanceGapB","bridges")}
                         for r in out_rows[:30]])
with open(os.path.join(DATA, "equiv_candidate_summary.json"), "w",
          encoding="utf-8") as f:
    json.dump(summary, f, ensure_ascii=False, indent=2)
for r in out_rows[:15]:
    log(f"  {r['pair']}  w={r['nWitnesses']}(u{r['uniformWitnesses']}) "
        f"fp={r['footprintA']}/{r['footprintB']} matched={r['matchedKeys']} "
        f"gap={r['gapDeclsA']}/{r['gapDeclsB']} bridges={r['bridges']} "
        f"instGap={r['instanceGapA'][:4]}/{r['instanceGapB'][:4]}")
log("done")
