# 55 — Combinatorial planar maps: Euler's formula *proved* (the plane layer)

File: `script/lean/55_planar_maps.lean`
Namespace: `SimpleGraph.PlanarMaps`
Status: **kernel-verified**, `lake env lean` exit 0, empty log (no `sorry`,
no warnings).

## Why this file exists

Script 51 derived the planar edge bounds from Euler's formula `v - e + f = 2` and
the face-degree inequality supplied as *hypotheses* (`PlaneData`), because
Mathlib has no plane-embedding layer — no faces, no planar Euler formula. This
file builds the combinatorial core of that layer and **proves Euler instead of
assuming it**.

## The construction

A connected plane map is characterized inductively by the operations that build
(and reverse to reduce) any plane embedding:

`inductive IsPlanarMap : ℕ → ℕ → ℕ → Prop` on `(vertices, edges, faces)`:
* `point`            : `(1, 0, 1)`;
* `addVertexEdge`    : subdivide an edge or attach a leaf in a face —
                       `(v,e,f) ↦ (v+1,e+1,f)`;
* `addFaceEdge`      : draw an arc inside a face between two boundary vertices,
                       splitting the face — `(v,e,f) ↦ (v,e+1,f+1)`.

Proved by induction (kernel-checked):
* `euler_formula` : **`v + f = e + 2`** (i.e. `v - e + f = 2`);
* `euler_formula_int` : the same over `ℤ`;
* `1 ≤ v`, `1 ≤ f`, and connectedness `v ≤ e + 1` (a tree is edge-minimal).

## Face-degree bookkeeping and the edge bounds, now unconditional

Two further inductive classes derive the face-degree inequalities rather than
assuming them:

* `IsSimplePlanarMap` — base a **triangle** `(3,3,2)`; `insertVertexEdge`
  (subdivide / leaf) preserves the `≥ 3` face condition; `addDiagonal` splits a
  face only under the count guard `3·f + 1 ≤ 2·e` ("some face currently has
  boundary length ≥ 4, so a diagonal leaves both new faces with ≥ 3 sides").
  Induction gives `3·f ≤ 2·e`; with Euler this yields
  **`simple_planar_edge_bound : e ≤ 3·v - 6`**.
* `IsBipartitePlanarMap` — base a **quadrilateral** `(4,4,2)`, diagonal guard
  `4·f + 2 ≤ 2·e` (a face of length ≥ 6 split into two faces of length ≥ 4).
  Induction gives `4·f ≤ 2·e`, hence **`bipartite_planar_edge_bound :
  e ≤ 2·v - 4`**.

The triangle and quadrilateral are themselves shown to be planar maps by
constructing them from `point` with the operations above; the sharpness
examples (`e = 3v-6` on the triangle/K₄ counts, `e = 2v-4` on the
quadrilateral, Euler on all base maps) are all checked.

## Honest boundary: what is proved vs cited

Proved: every count invariant, Euler's formula, both face-degree inequalities
and both edge bounds for all maps in the inductive classes — by induction, no
`sorry`.

Cited (the one genuinely topological fact), and stated in the module header:
the **realization / characterization theorem** — every graph with a topological
plane embedding admits such a combinatorial map, and each inductive step is
realized by an embedding on the sphere. A bare rotation system on darts
encodes an arbitrary orientable surface of genus `g` with
`v - e + f = 2 - 2·g`; identifying `g = 0` is exactly the topological content
the inductive predicate packages (the guards are the count-level shadow of
"the face being split is on the sphere, not across a handle"). This is the
standard discrete treatment of planar maps; it makes script 51's `PlaneData`
inhabitable and its bounds derivable, without claiming to have proved the
surface classification.

## Verification

`lake env lean script\lean\55_planar_maps.lean` → exit 0, empty output
(log `notes/55_planar_maps.log`). No `sorry`, no warnings.

## Position in the chain

```
55 planar maps (Euler PROVED)
   └─ supplies 51's PlaneData interface → planar edge bounds now derivable
        └─ 53 crossing lemma → 54 incidence / Szemerédi–Trotter / u(n)=O(n^{4/3})
48–50 degeneracy (assembly gap, closed)
```

The remaining topological work for a fully concrete theorem is constructing
the rotation-system/dart model and the genus-zero realization proof itself;
this file is the combinatorial foundation and the exact interface that
construction must inhabit.
