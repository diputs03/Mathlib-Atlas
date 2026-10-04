#!/usr/bin/env python3
"""Verification for script 14 graph analysis.

Independently re-streams 09 relations and 12 links and reconciles their totals
against the 14 node/module/area outputs.

Usage:
  verify_graph.py [--root DIR]
"""

import argparse
import json
import os


def load_jsonl(path):
    with open(path, "rb") as f:
        for line in f:
            yield json.loads(line)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=os.path.dirname(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
    args = ap.parse_args()
    D = os.path.join(args.root, "data")

    # node frame: name -> (module, area)
    name_module, name_area, modules = {}, {}, set()
    for r in load_jsonl(os.path.join(D, "atlas_features.jsonl")):
        p = r["module"].split(".")
        area = p[1] if len(p) >= 2 else "(root)"
        name_module[r["name"]] = r["module"]
        name_area[r["name"]] = area
        modules.add(r["module"])
    n_nodes = len(name_module)
    n_modules = len(modules)

    # independent re-aggregation from 09
    tot_rows = tot_mult = ext_mult = 0
    same_mod = cross_mod = 0
    same_area = cross_area = 0
    for r in load_jsonl(os.path.join(D, "atlas_relations.jsonl")):
        tot_rows += 1
        tv = r["typeHeadMain"] + r["typeArgMain"] + r["typeHeadBinder"] + r["typeArgBinder"]
        vv = r["valueHeadMain"] + r["valueArgMain"] + r["valueHeadBinder"] + r["valueArgBinder"]
        w = tv + vv
        tot_mult += w
        sm = name_module.get(r["source"])
        tm = name_module.get(r["target"])
        if tm is None:
            ext_mult += w
            continue
        if sm == tm:
            same_mod += w; same_area += w
        else:
            cross_mod += w
            if name_area[r["source"]] == name_area[r["target"]]:
                same_area += w
            else:
                cross_area += w

    # independent structural endpoint count (Mathlib endpoints only)
    link_rows = 0
    struct_endpoints = 0
    for r in load_jsonl(os.path.join(D, "atlas_decl_links.jsonl")):
        link_rows += 1
        for e in (r["source"], r["target"]):
            if e in name_module:
                struct_endpoints += 1

    # read 14 outputs
    nodes = list(load_jsonl(os.path.join(D, "atlas_node_graph_stats.jsonl")))
    mods = list(load_jsonl(os.path.join(D, "atlas_module_graph.jsonl")))
    areas = list(load_jsonl(os.path.join(D, "atlas_area_summary.jsonl")))
    area_edges = list(load_jsonl(os.path.join(D, "atlas_area_edges.jsonl")))

    errs = []
    # counts
    if len(nodes) != n_nodes:
        errs.append(f"node rows {len(nodes)} != features {n_nodes}")
    if len({r["name"] for r in nodes}) != len(nodes):
        errs.append("duplicate node names")
    if len(mods) != n_modules:
        errs.append(f"module rows {len(mods)} != {n_modules}")
    if len(areas) != 32:
        errs.append(f"area rows {len(areas)} != 32")

    # node-level reconciliation
    s_out = sum(r["outRefs"] for r in nodes)
    s_outn = sum(r["outNeighbors"] for r in nodes)
    s_in = sum(r["inRefs"] for r in nodes)
    if s_out != tot_mult:
        errs.append(f"sum outRefs {s_out} != total multiplicity {tot_mult}")
    if s_outn != tot_rows:
        errs.append(f"sum outNeighbors {s_outn} != relation rows {tot_rows}")
    if s_in + ext_mult != tot_mult:
        errs.append(f"sum inRefs {s_in} + external {ext_mult} != {tot_mult}")
    s_struct = sum(r["structLinks"] for r in nodes)
    if s_struct != struct_endpoints:
        errs.append(f"sum structLinks {s_struct} != Mathlib link endpoints {struct_endpoints}")
    for r in nodes:
        if r["outRefs"] < r["outNeighbors"] or r["inRefs"] < r["inNeighbors"]:
            errs.append(f"degree order violated at {r['name']}"); break
        if r["outType"] + r["outValue"] != r["outRefs"]:
            errs.append(f"out type+value != outRefs at {r['name']}"); break
        bsum = (r["outHeadMain"] + r["outArgMain"] +
                r["outHeadBinder"] + r["outArgBinder"])
        if bsum != r["outRefs"]:
            errs.append(f"out role buckets != outRefs at {r['name']}"); break

    # module-level reconciliation
    m_internal = sum(r["internalRefs"] for r in mods)
    m_out = sum(r["outRefs"] for r in mods)
    m_ext = sum(r["externalOutRefs"] for r in mods)
    if m_internal != same_mod:
        errs.append(f"module internal {m_internal} != {same_mod}")
    if m_out != cross_mod:
        errs.append(f"module cross {m_out} != {cross_mod}")
    if m_ext != ext_mult:
        errs.append(f"module external {m_ext} != {ext_mult}")
    if m_internal + m_out + m_ext != tot_mult:
        errs.append("module partition does not sum to total multiplicity")
    if sum(r["nDecls"] for r in mods) != n_nodes:
        errs.append("module nDecls does not sum to node count")

    # area-level reconciliation
    a_internal = sum(r["internalRefs"] for r in areas)
    a_out = sum(r["outRefs"] for r in areas)
    ae_sum = sum(r["refs"] for r in area_edges)
    if a_internal != same_area:
        errs.append(f"area internal {a_internal} != {same_area}")
    if a_out != cross_area or ae_sum != cross_area:
        errs.append(f"area out {a_out}/{ae_sum} != {cross_area}")
    # areas do not track non-Mathlib targets, so external multiplicity is the
    # third partition bucket (same as the module-level externalOutRefs).
    if a_internal + a_out + ext_mult != tot_mult:
        errs.append("area partition does not sum to total multiplicity")
    if sum(r["nDecls"] for r in areas) != n_nodes:
        errs.append("area nDecls does not sum to node count")

    print(f"features nodes {n_nodes}, modules {n_modules}")
    print(f"09 rows {tot_rows}, total multiplicity {tot_mult}")
    print(f"  same-module {same_mod}, cross-module {cross_mod}, external {ext_mult}")
    print(f"  same-area {same_area}, cross-area {cross_area}")
    print(f"12 link rows {link_rows}, Mathlib endpoints {struct_endpoints}")
    print(f"14 node rows {len(nodes)}, module rows {len(mods)}, area rows {len(areas)}, "
          f"area edges {len(area_edges)}")
    zero_out = sum(1 for r in nodes if r["outRefs"] == 0)
    zero_in = sum(1 for r in nodes if r["inRefs"] == 0)
    print(f"zero-out nodes {zero_out}, never-referenced nodes {zero_in}")

    if errs:
        print("\nFAILED:")
        for e in errs:
            print("  -", e)
        raise SystemExit(1)
    print("\nVERIFICATION OK")


if __name__ == "__main__":
    main()
