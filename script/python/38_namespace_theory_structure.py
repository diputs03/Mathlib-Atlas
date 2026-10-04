#!/usr/bin/env python3
"""38_namespace_theory_structure.py — separate module / namespace / theory.

A central Atlas distinction (transfer note sections 4, 27):
  * MODULE    = source file, from environment provenance (Mathlib.X.Y).
  * NAMESPACE = the name prefix a declaration is opened inside (Nat, Set, ...).
  * THEORY    = a coherent conceptual body that may span many modules AND many
               namespaces, and a single module may mix several namespaces.

This script quantifies the mismatch using per-declaration (namespace, module):
  - how many modules / areas a single namespace spans (portable abstractions),
  - how many distinct namespaces a single module mixes,
  - area coherence of each namespace (dominant-area share),
  - per-area rollup showing a "theory" bundles many namespaces & modules,
  - concrete divergence examples (namespace root != module area), e.g.
    Nat.one_mem_properDivisors_iff_one_lt lives in Mathlib.NumberTheory.Divisors.

Input : data/atlas_features.jsonl (name, namespace, module, kind for every decl)
Output: data/namespace_structure_summary.json
        data/namespace_crosscutting.jsonl   (one row per root namespace)
        data/module_namespace_mix.jsonl     (one row per module)
Pure stdlib, streaming, deterministic.
"""
import json, os, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
FEAT = os.path.join(DATA, "atlas_features.jsonl")
OUT_SUM = os.path.join(DATA, "namespace_structure_summary.json")
OUT_NS = os.path.join(DATA, "namespace_crosscutting.jsonl")
OUT_MOD = os.path.join(DATA, "module_namespace_mix.jsonl")


def area_of(module):
    p = module.split(".")
    return p[1] if len(p) >= 2 and p[0] == "Mathlib" else ""


def main():
    # per root-namespace aggregation
    ns = collections.defaultdict(lambda: {
        "decls": 0, "modules": set(), "areas": collections.Counter(),
        "kinds": collections.Counter(), "full": set(), "depth": 0})
    # per-module aggregation
    mod = collections.defaultdict(lambda: {
        "decls": 0, "nsroots": set(), "area": ""})
    n_total = n_mathlib = n_empty_ns = 0
    full_namespaces = set()
    ns_depth_hist = collections.Counter()
    divergence_examples = []

    for line in open(FEAT, encoding="utf-8"):
        r = json.loads(line)
        n_total += 1
        module = r.get("module", "")
        if not module.startswith("Mathlib"):
            continue
        n_mathlib += 1
        namespace = r.get("namespace", "") or ""
        kind = r.get("kind", "")
        area = area_of(module)
        if namespace:
            full_namespaces.add(namespace)
            root = namespace.split(".")[0]
            depth = namespace.count(".") + 1
        else:
            root = "(top-level)"
            depth = 0
            n_empty_ns += 1
        ns_depth_hist[depth] += 1

        g = ns[root]
        g["decls"] += 1
        g["modules"].add(module)
        if area:
            g["areas"][area] += 1
        g["kinds"][kind] += 1
        if namespace:
            g["full"].add(namespace)
        g["depth"] = max(g["depth"], depth)

        m = mod[module]
        m["decls"] += 1
        m["nsroots"].add(root)
        m["area"] = area

        # divergence: a core-datatype namespace whose decl sits in a different
        # conceptual area than the datatype's "home" (heuristic: collect a few)
        if (root in ("Nat", "Int", "Real", "Set", "Finset", "List", "Fin")
                and area and area not in ("Data", "Init")
                and len(divergence_examples) < 15):
            divergence_examples.append(
                {"name": r["name"], "namespaceRoot": root, "module": module,
                 "area": area})

    # ---- namespace rows ----
    ns_rows = []
    span_modules_hist = collections.Counter()
    span_areas_hist = collections.Counter()
    crosscutting = 0
    for root, g in ns.items():
        nmod = len(g["modules"])
        areas_total = sum(g["areas"].values())
        areas_sorted = sorted(g["areas"].items(), key=lambda kv: (-kv[1], kv[0]))
        dom_area, dom_n = areas_sorted[0] if areas_sorted else ("", 0)
        share = round(dom_n / areas_total, 4) if areas_total else 0.0
        nareas = len(g["areas"])
        span_modules_hist[min(nmod, 20)] += 1
        span_areas_hist[min(nareas, 20)] += 1
        if nareas >= 3:
            crosscutting += 1
        ns_rows.append({
            "root": root,
            "decls": g["decls"],
            "nModules": nmod,
            "nAreas": nareas,
            "nFullNamespaces": len(g["full"]),
            "maxDepth": g["depth"],
            "dominantArea": dom_area,
            "dominantShare": share,
            "areas": [{"area": a, "decls": c} for a, c in areas_sorted[:8]],
            "kinds": dict(sorted(g["kinds"].items()))})
    ns_rows.sort(key=lambda x: (-x["nAreas"], -x["decls"], x["root"]))
    with open(OUT_NS, "wb") as o:
        for row in ns_rows:
            o.write((json.dumps(row, ensure_ascii=False) + "\n").encode("utf-8"))

    # ---- module rows ----
    mod_rows = []
    mix_hist = collections.Counter()
    for module, m in mod.items():
        nn = len(m["nsroots"])
        mix_hist[min(nn, 30)] += 1
        mod_rows.append({"module": module, "area": m["area"],
                         "decls": m["decls"], "nNamespaceRoots": nn})
    mod_rows.sort(key=lambda x: (-x["nNamespaceRoots"], x["module"]))
    with open(OUT_MOD, "wb") as o:
        for row in mod_rows:
            o.write((json.dumps(row, ensure_ascii=False) + "\n").encode("utf-8"))

    # ---- area rollup (theory-level): bundles many namespaces & modules ----
    area_ns = collections.defaultdict(set)
    area_mod = collections.Counter()
    area_decl = collections.Counter()
    for module, m in mod.items():
        if m["area"]:
            area_mod[m["area"]] += 1
            area_decl[m["area"]] += m["decls"]
            area_ns[m["area"]] |= m["nsroots"]
    area_rows = sorted(
        ({"area": a, "modules": area_mod[a], "decls": area_decl[a],
          "namespaceRoots": len(area_ns[a])}
         for a in area_mod),
        key=lambda x: -x["decls"])

    most_mixed_modules = [{"module": r["module"],
                           "nNamespaceRoots": r["nNamespaceRoots"],
                           "decls": r["decls"]} for r in mod_rows[:15]]
    most_crosscutting = [{"root": r["root"], "nAreas": r["nAreas"],
                          "nModules": r["nModules"], "decls": r["decls"],
                          "dominantShare": r["dominantShare"]}
                         for r in ns_rows[:20] if r["nAreas"] >= 2]

    summary = {
        "totalDecls": n_total,
        "mathlibDecls": n_mathlib,
        "distinctModules": len(mod),
        "distinctFullNamespaces": len(full_namespaces),
        "distinctRootNamespaces": len(ns),
        "topLevelNoNamespace": n_empty_ns,
        "rootNamespacesSpanningGe3Areas": crosscutting,
        "namespaceDepthHist": dict(sorted(ns_depth_hist.items())),
        "modulesPerRootNsHist": dict(sorted(span_modules_hist.items())),
        "areasPerRootNsHist": dict(sorted(span_areas_hist.items())),
        "namespaceRootsPerModuleHist": dict(sorted(mix_hist.items())),
        "areas": area_rows,
        "mostCrosscuttingNamespaces": most_crosscutting,
        "mostNamespaceMixedModules": most_mixed_modules,
        "divergenceExamples": divergence_examples,
    }
    with open(OUT_SUM, "w", encoding="utf-8") as o:
        json.dump(summary, o, ensure_ascii=False, indent=2)

    print(f"decls {n_mathlib} (mathlib) | modules {len(mod)} | "
          f"full namespaces {len(full_namespaces)} | root namespaces {len(ns)}")
    print(f"root namespaces spanning >=3 areas (portable abstractions): "
          f"{crosscutting}")
    print("top cross-cutting namespaces (areas/modules/decls/domShare):")
    for r in most_crosscutting[:12]:
        print(f"  {r['root']:<16} areas={r['nAreas']:<2} "
              f"modules={r['nModules']:<4} decls={r['decls']:<5} "
              f"domShare={r['dominantShare']}")
    print("most namespace-mixed modules:")
    for r in most_mixed_modules[:8]:
        print(f"  {r['nNamespaceRoots']:<3} ns-roots, {r['decls']:<4} decls  "
              f"{r['module']}")
    print("areas (theory-level) by decls, with ns/module counts:")
    for r in area_rows[:10]:
        print(f"  {r['area']:<16} decls={r['decls']:<6} "
              f"modules={r['modules']:<4} nsRoots={r['namespaceRoots']}")


if __name__ == "__main__":
    main()
