# Mathlib PR-overlap report: `SchwartzLatticeSummable.lean`

*Prepared June 2026. PR data verified directly against the GitHub REST API; `gh` was unavailable in
the build environment.*

## What this file contributes

`SpherePacking/ForMathlib/SchwartzLatticeSummable.lean` proves that a Schwartz function is summable,
in norm, over the translates of any discrete `ℤ`-submodule of a finite-dimensional real normed
space — the basic input to (general) Poisson summation and to the Cohn–Elkies bound:

- `SchwartzMap.translateCM (f) (ℓ) : C(E, F)` — the translate `x ↦ f (x + ℓ)` as a continuous map
  (with `@[simp] translateCM_apply`);
- `ZLattice.finite_norm_le (L) (r) : {ℓ : L | ‖(ℓ:E)‖ ≤ r}.Finite` — a discrete `ℤ`-submodule meets
  any closed ball finitely;
- `SchwartzMap.summable_norm_comp_add (f) (L) (a) : Summable (fun ℓ : L ↦ ‖f (a + ℓ)‖)` and its
  unnormed companion `summable_comp_add`;
- `SchwartzMap.summable_norm_translateCM_restrict (f) (L) (K) : Summable (fun ℓ : L ↦
  ‖(f.translateCM ℓ).restrict K‖)` — the locally-uniform (sup-norm over a compact) version.

The engine is Schwartz decay (`SchwartzMap.decay`) dominated by the convergent series
`ZLattice.summable_norm_sub_inv_pow` / `summable_norm_pow_inv`. Crucially it needs **neither** an
inner-product structure **nor** that `L` be full rank (`IsZLattice`): only `[FiniteDimensional ℝ E]`
and `[DiscreteTopology L]`. This generality is what let us *deduplicate* — PSG and LPBound each
previously carried their own copy of this argument.

## Overlap with existing Mathlib / open PRs

There is **no Mathlib lemma and no open PR** that proves Schwartz summability over a lattice, nor a
higher-dimensional / general-lattice Poisson summation. `Mathlib/Analysis/Fourier/PoissonSummation.lean`
covers the one-dimensional `ℤ ⊆ ℝ` case and is not under active PR development. A search of the open
queue for "Poisson summation" returned nothing relevant. So the core summability lemmas here are
**uncontested**.

(Note: an earlier automated survey claimed several "Poisson summation" PRs; direct API checks showed
those were spurious. They are not cited here.)

Two API points worth recording, since an automated audit suggested otherwise:

- `ZLattice.finite_norm_le` is **not** subsumed by `ZSpan.setFinite_inter`: the latter is stated for
  the span of a basis, whereas our lemma handles an arbitrary discrete `Submodule ℤ E` and packages
  the result as a finite set in the subtype `L`. It is built on `Metric.finite_isBounded_inter_isClosed`
  and is worth keeping/upstreaming as the general statement.
- `SchwartzMap.translateCM` is **not** in Mathlib: `compCLM`/`compCLMOfContinuousLinearEquiv`
  precompose on the left; there is no right-translation-as-`ContinuousMap` constructor.

## Adjacent open PRs (Schwartz / distribution ecosystem)

The Schwartz-space corner of Mathlib is under active build-out, which is the right context for these
lemmas:

- **#37350 — "feat(Analysis/Distribution): define canonical maps between Schwartz/test functions,
  distributions/tempered distributions"** —
  <https://github.com/leanprover-community/mathlib4/pull/37350> (author **aditya-ramabadran**, open,
  opened 2026-03-30, assigned by **ADedecker**). Establishes `𝒟 → 𝒮` and `𝒮' → 𝒟'` maps.
- **#35291 — "feat(Fourier): improved version of Riemann-Lebesgue"** (author **mcdoll**, open) —
  relates the Schwartz Fourier transform to its `L¹` extension. <https://github.com/leanprover-community/mathlib4/pull/35291>
- **#40094 — "chore(Analysis/TemperedDistribution): add coercion and fix existing one"** (author
  **mcdoll**, open, June 2026). <https://github.com/leanprover-community/mathlib4/pull/40094>
- **#36326 — "Feat/gaussian schwartz map"** (author **Arnav-panjla**, open, opened 2026-03-07) —
  the Gaussian as a Schwartz function in finite dimensions; a canonical example consumer of Schwartz
  decay. <https://github.com/leanprover-community/mathlib4/pull/36326>

## Collaboration avenues

1. **Upstream the summability lemmas as their own small file**, downstream of `SchwartzSpace.Basic`
   and `Algebra/Module/ZLattice/Summable` — there is no dependency on the distribution PRs, so this
   can proceed independently and immediately. Proposed home:
   `Mathlib/Analysis/Distribution/SchwartzSpace/ZLattice.lean`.
2. **Coordinate naming with the Schwartz maintainers** (`mcdoll`, `ADedecker`, and `YaelDillies` who
   has reviewed #37350). The `translateCM` translation operator in particular should be named to fit
   whatever translation/precomposition conventions emerge from #37350/#40094.
3. **`finite_norm_le` is a natural addition to `Algebra/Module/ZLattice/`**, and pairs with the
   `setFinite_inter` already there; offer it as the general-discrete-submodule companion.

## Recommendation

Strong upstream candidate, **independent of the in-flight distribution PRs**. Land
`finite_norm_le` in the ZLattice folder and the `SchwartzMap.summable_*` lemmas in a new
`SchwartzSpace/ZLattice.lean`, coordinating names with the active Schwartz contributors. Keep
`translateCM` bundled with them.

**Upstream target:** `Mathlib/Analysis/Distribution/SchwartzSpace/ZLattice.lean` (+ `finite_norm_le`
to `Mathlib/Algebra/Module/ZLattice/`).
