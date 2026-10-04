#!/usr/bin/env python3
"""verify_namespace_structure.py — independent rebuild of script 38.

Re-aggregates (namespace, module, area) from atlas_features.jsonl with an
independent pass and asserts:
  * headline counts (decls / modules / namespaces),
  * per-namespace rows and per-module rows match the written files (bijection,
    deterministic order),
  * global conservation: decls summed over namespaces / modules / areas all
    equal the Mathlib declaration total,
  * invariants: nModules>=1, dominant area is the argmax, area histograms.
"""
import json, os, sys, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")


def area_of(module):
    p = module.split(".")
    return p[1] if len(p) >= 2 and p[0] == "Mathlib" else ""


def main():
    ns = collections.defaultdict(lambda: {"d": 0, "mod": set(),
                                          "ar": collections.Counter(),
                                          "full": set(), "depth": 0})
    mod = collections.defaultdict(lambda: {"d": 0, "roots": set()})
    full = set()
    n_math = n_empty = 0
    for line in open(os.path.join(DATA, "atlas_features.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        m = r.get("module", "")
        if not m.startswith("Mathlib"):
            continue
        n_math += 1
        namespace = r.get("namespace", "") or ""
        if namespace:
            full.add(namespace)
            root = namespace.split(".")[0]
            depth = namespace.count(".") + 1
        else:
            root, depth = "(top-level)", 0
            n_empty += 1
        a = area_of(m)
        g = ns[root]
        g["d"] += 1
        g["mod"].add(m)
        if a:
            g["ar"][a] += 1
        if namespace:
            g["full"].add(namespace)
        g["depth"] = max(g["depth"], depth)
        mm = mod[m]
        mm["d"] += 1
        mm["roots"].add(root)

    # rebuild rows
    ns_rows = {}
    ge3 = 0
    for root, g in ns.items():
        tot = sum(g["ar"].values())
        order = sorted(g["ar"].items(), key=lambda kv: (-kv[1], kv[0]))
        dom, dn = order[0] if order else ("", 0)
        if len(g["ar"]) >= 3:
            ge3 += 1
        ns_rows[root] = (g["d"], len(g["mod"]), len(g["ar"]), len(g["full"]),
                         g["depth"], dom, round(dn / tot, 4) if tot else 0.0)
    mod_rows = {m: (g["d"], len(g["roots"])) for m, g in mod.items()}

    # load written
    sumry = json.load(open(os.path.join(DATA, "namespace_structure_summary.json"),
                           encoding="utf-8"))
    written_ns = [json.loads(l) for l in open(
        os.path.join(DATA, "namespace_crosscutting.jsonl"), encoding="utf-8")]
    written_mod = [json.loads(l) for l in open(
        os.path.join(DATA, "module_namespace_mix.jsonl"), encoding="utf-8")]

    errs = []
    if sumry["mathlibDecls"] != n_math:
        errs.append(f"mathlib decls {sumry['mathlibDecls']} != {n_math}")
    if sumry["distinctModules"] != len(mod):
        errs.append("module count mismatch")
    if sumry["distinctFullNamespaces"] != len(full):
        errs.append("full ns count mismatch")
    if sumry["distinctRootNamespaces"] != len(ns):
        errs.append("root ns count mismatch")
    if sumry["topLevelNoNamespace"] != n_empty:
        errs.append("toplevel count mismatch")
    if sumry["rootNamespacesSpanningGe3Areas"] != ge3:
        errs.append("ge3 areas mismatch")

    # conservation
    if sum(g["d"] for g in ns.values()) != n_math:
        errs.append("namespace decls don't sum to total")
    if sum(g["d"] for g in mod.values()) != n_math:
        errs.append("module decls don't sum to total")
    if sum(a["decls"] for a in sumry["areas"]) != n_math:
        errs.append("area decls don't sum to total")

    # namespace file bijection + order
    if len(written_ns) != len(ns_rows):
        errs.append(f"ns rows {len(written_ns)} != {len(ns_rows)}")
    prev = None
    for w in written_ns:
        key = w["root"]
        b = ns_rows.get(key)
        if b is None:
            errs.append(f"written ns {key} not rebuilt")
            continue
        exp = (w["decls"], w["nModules"], w["nAreas"], w["nFullNamespaces"],
               w["maxDepth"], w["dominantArea"], w["dominantShare"])
        if exp != b:
            errs.append(f"ns {key}: {exp} != {b}")
        if w["nModules"] < 1:
            errs.append(f"ns {key} has no modules")
        # dominant area argmax check
        if w["areas"]:
            mx = max(a["decls"] for a in w["areas"])
            if w["areas"][0]["decls"] != mx:
                errs.append(f"ns {key} dominant not argmax")
        cur = (-w["nAreas"], -w["decls"], w["root"])
        if prev is not None and cur < prev:
            errs.append(f"ns rows not sorted at {key}")
        prev = cur

    # module file bijection
    if len(written_mod) != len(mod_rows):
        errs.append(f"mod rows {len(written_mod)} != {len(mod_rows)}")
    prev = None
    for w in written_mod:
        b = mod_rows.get(w["module"])
        if b is None:
            errs.append(f"written mod {w['module']} not rebuilt")
            continue
        if (w["decls"], w["nNamespaceRoots"]) != b:
            errs.append(f"mod {w['module']}: {(w['decls'], w['nNamespaceRoots'])} != {b}")
        cur = (-w["nNamespaceRoots"], w["module"])
        if prev is not None and cur < prev:
            errs.append(f"mod rows not sorted at {w['module']}")
        prev = cur

    # area rollup consistency
    for a in sumry["areas"]:
        if a["modules"] < 1 or a["decls"] < 1 or a["namespaceRoots"] < 1:
            errs.append(f"area {a['area']} degenerate")

    print(f"mathlib {n_math}: modules {len(mod)}, fullNs {len(full)}, "
          f"rootNs {len(ns)}, toplevel {n_empty}, nsSpan>=3areas {ge3}")
    print(f"rows: namespace {len(written_ns)}, module {len(written_mod)}; "
          f"areas {len(sumry['areas'])}")
    if errs:
        print("VERIFICATION FAILED")
        for e in errs[:30]:
            print("  FAIL:", e)
        sys.exit(1)
    print("counts, conservation sums, row bijections and order all match")
    print("VERIFICATION OK")


if __name__ == "__main__":
    main()
