# Mathlib PR-overlap report: `UnitAddTorusQuotient.lean`

*Prepared June 2026. PR data verified directly against the GitHub REST API
(`api.github.com/repos/leanprover-community/mathlib4`); `gh` was unavailable in the build
environment.*

## What this file contributes

`SpherePacking/ForMathlib/UnitAddTorusQuotient.lean` packages the coordinatewise quotient map that
presents the `ι`-dimensional unit torus as a quotient of `ℝ^ι`, together with the analytic API a
harmonic-analysis user needs:

- `UnitAddTorus.coeFun (ι : Type*) : (ι → ℝ) → UnitAddTorus ι`, `x ↦ (i ↦ (x i : ℝ/ℤ))`, with
  `@[simp] coeFun_apply`;
- `continuous_coeFun` (tagged `@[continuity, fun_prop]`);
- `isOpenQuotientMap_coeFun` — `coeFun` is an open quotient map (via `IsOpenQuotientMap.piMap` and
  `QuotientAddGroup.isOpenQuotientMap_mk`);
- `mFourier_apply_coeFun_ofLp` — the value of the torus Fourier monomial `mFourier k` on the image
  of a Euclidean point;
- `integral_eq_integral_preimage_coeFun` — the pull-back of Haar integration on `(ℝ/ℤ)^ι` to a
  fundamental cube `∏ i, (t, t+1] ⊆ ℝ^ι`.

It is a companion to `Mathlib/Analysis/Fourier/AddCircleMulti.lean`, which already defines
`UnitAddTorus`, `mFourier`, and `mFourierCoeff`. The first two declarations are stated for an
arbitrary index type `ι`; the Fourier/integral facts add `[Fintype ι]`.

## Overlapping open PR

**PR #39460 — "feat(Algebra/Module/ZLattice): Quotient by `IsZLattice` is group isomorphic to
`UnitAddTorus`"** — <https://github.com/leanprover-community/mathlib4/pull/39460>
(author **Deicyde**, **draft**, opened 2026-05-16).

Its main result is `quotientAddEquivUnitAddTorus : (E ⧸ L) ≃+ UnitAddTorus ι` for any
`IsZLattice ℝ L`. The PR body states it is "currently left as a draft for educational purpose" and
points to a Zulip discussion about the right definition of the torus.

This is a **strong, complementary overlap**, not a collision:

- #39460 builds the **algebraic** object — the additive-group isomorphism between the lattice
  quotient `E ⧸ L` and `UnitAddTorus ι`. It works at the level of `IsZLattice`, i.e. an abstract
  full-rank lattice in a finite-dimensional space.
- Our file builds the **topological / measure-theoretic** layer of the *standard* quotient map
  `ℝ^ι → (ℝ/ℤ)^ι`: continuity, the open-quotient property, the action of the Fourier characters,
  and the Haar-measure pull-back to a fundamental cube. These are exactly the facts one needs to
  *do analysis* on the torus (descend periodic functions, compute Fourier coefficients as cube
  integrals) — which is how PSG consumes them in Poisson summation.

The two are layered: #39460's `≃+` is the algebraic identification, ours is the analytic interface
to the same quotient. A natural unified contribution would expose both — the group isomorphism *and*
the statement that the underlying map is an open quotient map that pulls Haar measure back to a
fundamental domain.

## Collaboration avenues

1. **Engage on the Zulip thread referenced by #39460.** Because the PR is an explicitly educational
   draft and the definition of the torus is still under discussion, this is the moment to align our
   `coeFun` with their `quotientAddEquivUnitAddTorus` so the maps compose definitionally — ideally
   `coeFun` factors as `(quotient mk) ≫ quotientAddEquivUnitAddTorus`, making our continuity and
   measure lemmas transport for free to their `≃+`.

2. **Offer the analytic API as a follow-up PR keyed off #39460.** Once their `≃+` lands, our
   `continuous_coeFun`, `isOpenQuotientMap_coeFun`, `mFourier_apply_coeFun_ofLp`, and
   `integral_eq_integral_preimage_coeFun` are the obvious next file in
   `Mathlib/Analysis/Fourier/AddCircleMulti.lean`. We should rebase our lemmas to be stated in terms
   of their canonical map rather than re-introducing a parallel `coeFun`, to avoid two
   near-duplicate projections in Mathlib.

3. **Help unstick the draft.** The PR is a draft and may be stalled on definitional bikeshedding
   (the Zulip thread). A concrete downstream use case — "here is the Poisson-summation machinery
   that needs exactly this quotient, with its measure pull-back" — is often what converts an
   educational draft into a merge-track PR. Linking our use case is low-effort, high-value.

## Adjacent context

`Mathlib/Analysis/Fourier/AddCircleMulti.lean` (the multidimensional-torus Fourier file our work sits
on top of) appears to be already merged with no active follow-up PR on `mFourier`/`mFourierCoeff`, so
the analytic API above is uncontested territory beyond #39460.

## Recommendation

**Do not upstream `coeFun` independently.** Coordinate with #39460: align `coeFun` to their
`quotientAddEquivUnitAddTorus`, then propose the continuity / open-quotient / measure-pull-back
lemmas as a companion PR. Until then, keep our file as-is (it is the working analytic interface for
PSG), and record the dependency so that import-narrowing time also becomes coordination time.

**Upstream target:** `Mathlib/Analysis/Fourier/AddCircleMulti.lean` (or a sibling), downstream of
#39460.
