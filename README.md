# Lean verification for the stellated tetrahedron Rupert program

This is the Lean 4 + Mathlib workspace for the [stellated tetrahedron is not Rupert paper](https://omniscienceproject.com/papers/stellated-tetrahedron-1120-is-not-rupert-cylinder-theorems-and-863n6qbK).
It is intended to hold the abstract local theorems, the concrete `P_11/20` geometry, and the
critical-disk certificate statements in one Lake project.

It provides a Lean verification of the paper's analytic core: the cylinder theorems and the
marginal-reduction geometry are proved unconditionally (no `sorry`, no added axioms), and the
finite SB-box/SF certificate cells are machine-checked in exact rational arithmetic via
`native_decide`. From these it assembles the reduction to non-Rupertness of `P_11/20`, modulo the
four certified inputs' arithmetic-to-geometry bridges and the far / off-diagonal region exclusions,
which are supplied as hypotheses and discharged by the paper's external interval-arithmetic scripts.

## Initial Layout

- `RupertStellatedTetrahedron.lean` - library root.
- `RupertStellatedTetrahedron/Local/DepthCylinder.lean` - the existing Depth-Cylinder Theorem
  formalization, copied from `results/provisional/rupert-depth-cylinder-theorem/`.

## Planned Layout

- `RupertStellatedTetrahedron/Core/` - reusable geometry, convexity, flags, and certificate APIs.
- `RupertStellatedTetrahedron/Local/` - abstract local theorems: depth cylinder, epsilon-slack
  cylinder, contact-base cylinder.
- `RupertStellatedTetrahedron/Stellated/` - concrete `P_11/20` vertices, symmetries, reflection
  sheets, pinch, and `u*` data.
- `RupertStellatedTetrahedron/CriticalDisk/` - blow-up coordinates, translation kill,
  second-order slice, remainder constants, and open target statements.

## Build

```sh
lake build
```

The first build may need `lake exe cache get` if Mathlib artifacts are not already cached.
