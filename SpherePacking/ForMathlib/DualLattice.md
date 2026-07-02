# Mathlib PR-overlap report: `DualLattice.lean`

*Prepared June 2026. PR data verified directly against the GitHub REST API; `gh` was unavailable in
the build environment.*

## What this file contributes

`SpherePacking/ForMathlib/DualLattice.lean` proves that the dual of a `ℤ`-lattice is again a discrete
`ℤ`-lattice:

```
theorem LinearMap.BilinForm.discreteTopology_dualSubmodule
    {B : BilinForm ℝ M} (hB : B.Nondegenerate)
    (Λ : Submodule ℤ M) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    DiscreteTopology (B.dualSubmodule Λ)
```

for a nondegenerate bilinear form `B` on a finite-dimensional real space `M`. The proof uses the
existing `BilinForm.dualSubmodule_span_of_basis`: the dual submodule is spanned by the `B`-dual basis
of an integral basis of `Λ`, hence is itself the `ℤ`-span of an `ℝ`-basis — a lattice. For the
inner-product case the file registers the discreteness as the named instance
`instDiscreteTopology_dualSubmodule_innerₗ`; the Euclidean nondegeneracy fact (formerly the separate
`innerₗ_nondegenerate`, a one-call composition) is now inlined into that instance during cleanup. The
Cohn–Elkies bound consumes exactly this instance when summing over the dual lattice.

## Overlap with existing Mathlib / open PRs

**There is no open PR on dual lattices.** A search of the open queue for "dual lattice" returned only
unrelated order-theoretic "dualisation" PRs (e.g. lattice-of-cones, `to_dual` for filters). The
number-theoretic dual lattice is **uncontested**.

(An earlier automated survey did not invent any dual-lattice PRs; this nil result is confirmed.)

This file directly addresses an explicit Mathlib **TODO**. In
`Mathlib/LinearAlgebra/BilinearForm/DualLattice.lean`:

- the module header lists `BilinForm.dualSubmodule_span_of_basis` ("the dual of a lattice is spanned
  by the dual basis") and then a `## TODO` (around line 18) to **"Properly develop the material in the
  context of lattices"**;
- line 67 carries a further `-- TODO: Show that this is perfect when N is a lattice and B is
  nondegenerate.`

Our `discreteTopology_dualSubmodule` is precisely the first step of "develop the material in the
context of lattices": it upgrades the existing *spanning* fact to the *lattice* fact (discreteness /
being a `ZLattice`). It is built entirely on declarations already in that file
(`dualSubmodule_span_of_basis`, `dualBasis`) plus `Basis.ofZLatticeBasis_span`.

## Collaboration avenues

1. **Submit directly into `Mathlib/LinearAlgebra/BilinearForm/DualLattice.lean`**, quoting the TODO it
   resolves. Because it reuses that file's own API, the PR is self-contained and reviewer-friendly.
2. **Consider strengthening to `IsZLattice ℝ (B.dualSubmodule Λ)`**, not merely `DiscreteTopology` —
   the proof already exhibits the dual as the span of an `ℝ`-basis, so the full `ZLattice` instance is
   within reach and is the more useful statement (it lets downstream users invoke covolume / Poisson
   machinery on the dual). This also makes a larger dent in the "develop the material in the context
   of lattices" TODO.
3. **The inner-product instance** (`innerₗ_nondegenerate` + the `DiscreteTopology` instance for
   `dualSubmodule (innerₗ E) Λ`) belongs near `Mathlib/Analysis/InnerProductSpace/`; offer it as a
   second, smaller PR or a follow-up section so the bilinear-form file stays free of inner-product
   imports.

## Recommendation

**Clean, uncontested upstream contribution that closes a standing TODO.** Submit
`discreteTopology_dualSubmodule` (ideally upgraded to the full `IsZLattice` instance) into
`DualLattice.lean`, and the Euclidean instance into the inner-product hierarchy. No coordination with
other PRs is required; the only design choice is whether to ship `DiscreteTopology` or the stronger
`IsZLattice`.

**Upstream target:** `Mathlib/LinearAlgebra/BilinearForm/DualLattice.lean` (+ the inner-product
instance near `Mathlib/Analysis/InnerProductSpace/`).
