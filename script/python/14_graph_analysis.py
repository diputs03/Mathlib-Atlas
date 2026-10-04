#!/usr/bin/env python3
"""14 - Graph analysis over the serialized Atlas corpus.

Combines, with no further Lean run:
  * 13 features  -> node frame (574,391 Mathlib declarations, module, area)
  * 09 relations -> labelled term-reference graph (16,316,230 directed edges,
                    one row per distinct source->target, with multiplicity by
                    structural role: type/value x head/arg x main/binder)
  * 12 links     -> environment-encoded structural links (constructor,
                    recursor, projection, equationLemma, structExtends, ...)

Direct one-hop edges only (no transitive/axiom/reduction closure), and edge
labels are kept separate. Top-level "area" = the segment after `Mathlib.`
(Mathlib.Algebra.* -> Algebra).

Outputs:
  data/atlas_node_graph_stats.jsonl   per-declaration labelled degrees
  data/atlas_module_graph.jsonl       per-module aggregation + bridge signals
  data/atlas_area_summary.jsonl       per top-level area aggregation
  data/atlas_area_edges.jsonl         directed area->area weighted edges
  notes/14_graph_summary.txt          distributions / hubs / bridges / anomalies
"""

import json
import os
from array import array
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
FEATURES = os.path.join(ROOT, "data", "atlas_features.jsonl")
RELATIONS = os.path.join(ROOT, "data", "atlas_relations.jsonl")
LINKS = os.path.join(ROOT, "data", "atlas_decl_links.jsonl")
OUT_NODE = os.path.join(ROOT, "data", "atlas_node_graph_stats.jsonl")
OUT_MODULE = os.path.join(ROOT, "data", "atlas_module_graph.jsonl")
OUT_AREA = os.path.join(ROOT, "data", "atlas_area_summary.jsonl")
OUT_AREA_EDGE = os.path.join(ROOT, "data", "atlas_area_edges.jsonl")
OUT_SUMMARY = os.path.join(ROOT, "notes", "14_graph_summary.txt")

ROLE_KEYS = ["typeHeadMain", "typeArgMain", "typeHeadBinder", "typeArgBinder",
             "valueHeadMain", "valueArgMain", "valueHeadBinder", "valueArgBinder"]
# outgoing/incoming role buckets (collapsed across type+value)
BUCKETS = ["HeadMain", "ArgMain", "HeadBinder", "ArgBinder"]


def area_of(module):
    p = module.split(".")
    return p[1] if len(p) >= 2 else "(root)"


def pct(sorted_vals, q):
    if not sorted_vals:
        return 0
    return sorted_vals[min(len(sorted_vals) - 1, int(q * (len(sorted_vals) - 1)))]


def dist_line(name, vals):
    s = sorted(vals)
    return (f"{name:22s} n={len(s):7d} min={s[0]:6d} p50={pct(s,.5):7d} "
            f"p90={pct(s,.9):8d} p99={pct(s,.99):9d} max={s[-1]:10d} "
            f"mean={sum(s)/len(s):12.2f}")


def main():
    # ---- node frame from 13 ----
    names, modules, kinds, namespaces = [], [], [], []
    concl, is_class, is_inst, is_rfl = [], [], [], []
    value_nodes = []
    mod_of_name = {}
    print("loading features ...", flush=True)
    with open(FEATURES, "rb") as f:
        for line in f:
            r = json.loads(line)
            mod_of_name[r["name"]] = len(names)
            names.append(r["name"])
            modules.append(r["module"])
            kinds.append(r["kind"])
            namespaces.append(r["namespace"])
            concl.append(r["conclusionHead"])
            is_class.append(1 if r["isClass"] else 0)
            is_inst.append(1 if r["isInstance"] else 0)
            is_rfl.append(1 if r["valueIsRfl"] else 0)
            value_nodes.append(r["valueNodes"])
    N = len(names)
    print(f"  {N} nodes", flush=True)

    def zeros():
        return array("q", [0]) * N

    out_refs = zeros(); in_refs = zeros()
    out_neigh = zeros(); in_neigh = zeros()
    out_type = zeros(); out_value = zeros(); in_type = zeros(); in_value = zeros()
    out_b = {b: zeros() for b in BUCKETS}
    in_b = {b: zeros() for b in BUCKETS}
    self_refs = zeros()

    # ---- module frame ----
    module_list = sorted(set(modules))
    M = len(module_list)
    mod2idx = {m: i for i, m in enumerate(module_list)}
    node_mod = array("i", (mod2idx[m] for m in modules))
    mod_area = [area_of(m) for m in module_list]
    mod_decls = array("q", [0]) * M
    for mi in node_mod:
        mod_decls[mi] += 1

    mod_internal = array("q", [0]) * M
    mod_out = array("q", [0]) * M
    mod_in = array("q", [0]) * M
    mod_external = array("q", [0]) * M
    mod_cross_out = array("q", [0]) * M
    mod_cross_in = array("q", [0]) * M
    mod_struct = array("q", [0]) * M
    # encoded module pair (sm*M+tm) -> multiplicity, Mathlib<->Mathlib only
    mod_pair_w = {}
    total_relation_rows = 0
    total_mult = 0
    external_edges = 0

    print("streaming 09 relations ...", flush=True)
    with open(RELATIONS, "rb") as f:
        for line in f:
            r = json.loads(line)
            total_relation_rows += 1
            s = mod_of_name.get(r["source"])
            if s is None:
                continue  # relations are Mathlib-source; defensive
            tv = (r["typeHeadMain"] + r["typeArgMain"] +
                  r["typeHeadBinder"] + r["typeArgBinder"])
            vv = (r["valueHeadMain"] + r["valueArgMain"] +
                  r["valueHeadBinder"] + r["valueArgBinder"])
            w = tv + vv
            total_mult += w
            hm = r["typeHeadMain"] + r["valueHeadMain"]
            am = r["typeArgMain"] + r["valueArgMain"]
            hb = r["typeHeadBinder"] + r["valueHeadBinder"]
            ab = r["typeArgBinder"] + r["valueArgBinder"]

            out_refs[s] += w; out_neigh[s] += 1
            out_type[s] += tv; out_value[s] += vv
            out_b["HeadMain"][s] += hm; out_b["ArgMain"][s] += am
            out_b["HeadBinder"][s] += hb; out_b["ArgBinder"][s] += ab
            if r["isSelf"]:
                self_refs[s] += w
            sm = node_mod[s]

            t = mod_of_name.get(r["target"])
            if t is None:
                external_edges += 1
                mod_external[sm] += w
                continue
            in_refs[t] += w; in_neigh[t] += 1
            in_type[t] += tv; in_value[t] += vv
            in_b["HeadMain"][t] += hm; in_b["ArgMain"][t] += am
            in_b["HeadBinder"][t] += hb; in_b["ArgBinder"][t] += ab
            tm = node_mod[t]
            if sm == tm:
                mod_internal[sm] += w
            else:
                mod_out[sm] += w; mod_in[tm] += w
                key = sm * M + tm
                mod_pair_w[key] = mod_pair_w.get(key, 0) + w
                if mod_area[sm] != mod_area[tm]:
                    mod_cross_out[sm] += w; mod_cross_in[tm] += w
    print(f"  {total_relation_rows} relation rows, multiplicity {total_mult}, "
          f"external edges {external_edges}", flush=True)

    # ---- 12 structural links ----
    struct_total = zeros()
    struct_kind = defaultdict(zeros)
    link_rows = 0
    with open(LINKS, "rb") as f:
        for line in f:
            r = json.loads(line)
            link_rows += 1
            rel = r["relation"]
            for endpoint in (r["source"], r["target"]):
                idx = mod_of_name.get(endpoint)
                if idx is None:
                    continue
                struct_total[idx] += 1
                struct_kind[rel][idx] += 1
                mod_struct[node_mod[idx]] += 1

    # ---- module distinct neighbours / area reach ----
    mod_out_mods = defaultdict(set); mod_in_mods = defaultdict(set)
    for key in mod_pair_w:
        sm, tm = divmod(key, M)
        mod_out_mods[sm].add(tm); mod_in_mods[tm].add(sm)

    # ---- area aggregation ----
    area_list = sorted(set(mod_area))
    A = len(area_list)
    area2idx = {a: i for i, a in enumerate(area_list)}
    mod_area_idx = array("i", (area2idx[a] for a in mod_area))
    area_decls = array("q", [0]) * A
    area_modules = array("q", [0]) * A
    for mi in range(M):
        ai = mod_area_idx[mi]
        area_decls[ai] += mod_decls[mi]
        area_modules[ai] += 1
    area_internal = array("q", [0]) * A
    for mi in range(M):
        area_internal[mod_area_idx[mi]] += mod_internal[mi]
    area_pair_w = {}
    for key, w in mod_pair_w.items():
        sm, tm = divmod(key, M)
        asa, ata = mod_area_idx[sm], mod_area_idx[tm]
        if asa == ata:
            # intra-area but cross-module
            area_internal[asa] += w
        else:
            k = asa * A + ata
            area_pair_w[k] = area_pair_w.get(k, 0) + w
    area_out = array("q", [0]) * A; area_in = array("q", [0]) * A
    area_out_areas = defaultdict(set); area_in_areas = defaultdict(set)
    for key, w in area_pair_w.items():
        a, b = divmod(key, A)
        area_out[a] += w; area_in[b] += w
        area_out_areas[a].add(b); area_in_areas[b].add(a)

    # ---- write node rows ----
    print("writing node stats ...", flush=True)
    sk = sorted(struct_kind.keys())
    with open(OUT_NODE, "w", encoding="utf-8", newline="\n") as f:
        for i in range(N):
            bykind = {k: struct_kind[k][i] for k in sk if struct_kind[k][i]}
            row = {
                "name": names[i], "kind": kinds[i], "module": modules[i],
                "area": mod_area[node_mod[i]], "namespace": namespaces[i],
                "conclusionHead": concl[i],
                "isClass": bool(is_class[i]), "isInstance": bool(is_inst[i]),
                "valueIsRfl": bool(is_rfl[i]),
                "outRefs": out_refs[i], "outNeighbors": out_neigh[i],
                "inRefs": in_refs[i], "inNeighbors": in_neigh[i],
                "outType": out_type[i], "outValue": out_value[i],
                "inType": in_type[i], "inValue": in_value[i],
                "outHeadMain": out_b["HeadMain"][i], "outArgMain": out_b["ArgMain"][i],
                "outHeadBinder": out_b["HeadBinder"][i], "outArgBinder": out_b["ArgBinder"][i],
                "inHeadMain": in_b["HeadMain"][i], "inArgMain": in_b["ArgMain"][i],
                "inHeadBinder": in_b["HeadBinder"][i], "inArgBinder": in_b["ArgBinder"][i],
                "selfRefs": self_refs[i],
                "structLinks": struct_total[i], "structByKind": bykind,
            }
            f.write(json.dumps(row, ensure_ascii=False, separators=(",", ":")) + "\n")

    # ---- write module rows ----
    print("writing module graph ...", flush=True)
    with open(OUT_MODULE, "w", encoding="utf-8", newline="\n") as f:
        for mi in range(M):
            row = {
                "module": module_list[mi], "area": mod_area[mi],
                "nDecls": mod_decls[mi],
                "internalRefs": mod_internal[mi],
                "outRefs": mod_out[mi], "inRefs": mod_in[mi],
                "externalOutRefs": mod_external[mi],
                "crossAreaOut": mod_cross_out[mi], "crossAreaIn": mod_cross_in[mi],
                "outModules": len(mod_out_mods.get(mi, ())),
                "inModules": len(mod_in_mods.get(mi, ())),
                "areaOutCount": len({mod_area_idx[t] for t in mod_out_mods.get(mi, ())}),
                "areaInCount": len({mod_area_idx[s] for s in mod_in_mods.get(mi, ())}),
                "structLinks": mod_struct[mi],
            }
            f.write(json.dumps(row, ensure_ascii=False, separators=(",", ":")) + "\n")

    # ---- write area rows + edges ----
    with open(OUT_AREA, "w", encoding="utf-8", newline="\n") as fa, \
         open(OUT_AREA_EDGE, "w", encoding="utf-8", newline="\n") as fe:
        for ai in range(A):
            fa.write(json.dumps({
                "area": area_list[ai], "nModules": area_modules[ai],
                "nDecls": area_decls[ai], "internalRefs": area_internal[ai],
                "outRefs": area_out[ai], "inRefs": area_in[ai],
                "outAreas": len(area_out_areas.get(ai, ())),
                "inAreas": len(area_in_areas.get(ai, ())),
            }, separators=(",", ":")) + "\n")
        for key, w in sorted(area_pair_w.items(), key=lambda kv: -kv[1]):
            a, b = divmod(key, A)
            fe.write(json.dumps({"sourceArea": area_list[a],
                                 "targetArea": area_list[b], "refs": w},
                                separators=(",", ":")) + "\n")

    # ---- summary / candidate lists ----
    print("building summary ...", flush=True)
    L = []
    w = L.append
    w("Mathlib Atlas - script 14 graph analysis summary")
    w(f"nodes (Mathlib declarations): {N}")
    w(f"modules: {M}   top-level areas: {A}")
    w(f"09 relation rows (distinct directed edges): {total_relation_rows}")
    w(f"total reference multiplicity: {total_mult}")
    w(f"edges to non-Mathlib (core/Std) targets: {external_edges}")
    w(f"12 structural link rows scanned: {link_rows}")
    w("")
    w("== per-node degree distributions (multiplicity / distinct neighbours) ==")
    w(dist_line("outRefs", list(out_refs)))
    w(dist_line("outNeighbors", list(out_neigh)))
    w(dist_line("inRefs", list(in_refs)))
    w(dist_line("inNeighbors", list(in_neigh)))
    w(dist_line("structLinks", list(struct_total)))
    zero_out = sum(1 for i in range(N) if out_refs[i] == 0)
    zero_in = sum(1 for i in range(N) if in_refs[i] == 0)
    w(f"declarations with zero outgoing references: {zero_out}")
    w(f"declarations never referenced (inRefs=0):   {zero_in}")
    w("")

    def top(vals, k=20, key=None):
        idx = sorted(range(N), key=key or (lambda i: -vals[i]))[:k]
        return [(names[i], modules[i], kinds[i],
                 key(i) if key else vals[i]) for i in idx]

    w("== top 20 in-hubs (most referenced; multiplicity) ==")
    for nm, mo, ki, v in top(in_refs):
        w(f"  {v:9d}  {nm}  [{ki}, {mo}]")
    w("")
    w("== top 20 out-degree (most references made; multiplicity) ==")
    for nm, mo, ki, v in top(out_refs):
        w(f"  {v:9d}  {nm}  [{ki}, {mo}]")
    w("")
    # module bridge ranking: breadth of area reach then cross-area weight
    mrows = []
    for mi in range(M):
        mrows.append((module_list[mi], mod_area[mi], mod_decls[mi],
                      len(mod_out_mods.get(mi, ())), len(mod_in_mods.get(mi, ())),
                      mod_cross_out[mi], mod_cross_in[mi],
                      len({mod_area_idx[t] for t in mod_out_mods.get(mi, ())}),
                      len({mod_area_idx[s] for s in mod_in_mods.get(mi, ())})))
    w("== top 25 bridge modules (distinct other areas reached out, then cross-area out refs) ==")
    for mo, ar, nd, om, im, co, ci, ao, ai in sorted(
            mrows, key=lambda x: (-x[7], -x[5]))[:25]:
        w(f"  areasOut={ao:2d} crossOut={co:8d} outMods={om:4d} decls={nd:6d}  {mo}")
    w("")
    w("== areas (decls / modules / internal / out / in / area reach) ==")
    for ai in sorted(range(A), key=lambda i: -area_decls[i]):
        w(f"  {area_list[ai]:16s} decls={area_decls[ai]:7d} modules={area_modules[ai]:5d} "
          f"internal={area_internal[ai]:10d} out={area_out[ai]:9d} in={area_in[ai]:9d} "
          f"areasOut={len(area_out_areas.get(ai,())):2d}")
    w("")
    w("== top 30 cross-area edges (multiplicity) ==")
    for key, wv in sorted(area_pair_w.items(), key=lambda kv: -kv[1])[:30]:
        a, b = divmod(key, A)
        w(f"  {wv:9d}  {area_list[a]} -> {area_list[b]}")
    w("")
    # anomaly candidates: rfl proofs whose reduction term is enormous
    w("== anomaly candidates: rfl-closed proofs with largest value terms ==")
    rfl_big = sorted((i for i in range(N) if is_rfl[i]),
                     key=lambda i: -value_nodes[i])[:15]
    for i in rfl_big:
        w(f"  valueNodes={value_nodes[i]:7d} outRefs={out_refs[i]:6d}  {names[i]}  [{modules[i]}]")
    w("")
    w("== anomaly candidates: largest out-degree / value-term ratio skew ==")
    big_val = sorted(range(N), key=lambda i: -value_nodes[i])[:15]
    for i in big_val:
        w(f"  valueNodes={value_nodes[i]:7d} outRefs={out_refs[i]:6d} rfl={is_rfl[i]}  "
          f"{names[i]}  [{kinds[i]}, {modules[i]}]")
    w("")

    with open(OUT_SUMMARY, "w", encoding="utf-8", newline="\n") as f:
        f.write("\n".join(L) + "\n")
    print("\n".join(L[:12]))
    print("... full summary ->", OUT_SUMMARY)


if __name__ == "__main__":
    main()
