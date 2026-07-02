# Mathlib PR-overlap report: `FourierComp.lean`

*Prepared June 2026. PR data verified directly against the GitHub REST API; `gh` was unavailable in
the build environment.*

## What this file contributes

`SpherePacking/ForMathlib/FourierComp.lean` proves the **Fourier transform under an invertible linear
change of variables**:

```
theorem fourier_comp_linearEquiv (A : V ≃ₗ[ℝ] V) (f : V → E) (w : V) :
    𝓕 (fun x ↦ f (A x)) w = |det A|⁻¹ • 𝓕 f (LinearMap.adjoint A.symm w)
```

over any `[NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]`, for any codomain
`E` with `[NormedSpace ℂ E]`. (During cleanup the codomain was generalised from `ℂ` to `E`, matching
mathlib's vector-valued `𝓕`, and the inverse-transform companion `fourierInv_comp_linearEquiv` was
added — see avenues 1–2 below.) The scalar `|det A|⁻¹` is the Jacobian factor (from
`Measure.map_linearMap_addHaar_eq_smul_addHaar`) and the adjoint of `A⁻¹` appears because the Fourier
pairing `⟪A x, w⟫ = ⟪x, A^* w⟫` moves `A` across the inner product. PSG uses the forward lemma as the
spectral-side change of variables that reduces lattice Poisson summation to the standard lattice.

## Overlap with existing Mathlib

Mathlib already has the **isometry special case** in
`Mathlib/Analysis/Fourier/FourierTransform.lean`:

- `fourier_comp_linearIsometry (A : W ≃ₗᵢ[ℝ] V) (f : V → E) (w : W)` (line 473), with alias
  `fourierIntegral_comp_linearIsometry`;
- `fourierInv_comp_linearIsometry` (line 506), with alias `fourierIntegralInv_comp_linearIsometry`.

For an isometry `det = ±1`, the `|det|⁻¹` factor is `1` and the adjoint equals the inverse, so the
isometry lemma is exactly our statement specialised. **Our lemma is the strict generalisation**: it
drops the isometry hypothesis to an arbitrary linear automorphism, introducing the determinant
factor. This is genuinely new content — there is no general-`A` change-of-variables for the Fourier
transform in Mathlib today.

No open PR was found that adds a general linear (non-isometric) change of variables for the Fourier
transform.

## Adjacent open PRs (Fourier ecosystem)

- **#40583 — "feat(Analysis/Fourier/Convolution): drop continuity hypotheses from the convolution
  theorems"** — <https://github.com/leanprover-community/mathlib4/pull/40583> (author **dennj**, open,
  June 2026). Hypothesis-weakening work in the Fourier module; not change-of-variables, but the same
  neighbourhood of the library and the same reviewers.
- **#35291 — "feat(Fourier): improved version of Riemann-Lebesgue"** —
  <https://github.com/leanprover-community/mathlib4/pull/35291> (author **mcdoll**, open, opened
  2026-02-14). Reframes Riemann–Lebesgue as a corollary of extending the Schwartz Fourier transform
  to `L¹`. `mcdoll` is the de-facto maintainer of the Fourier-analysis corner and the right reviewer
  to engage.

## Collaboration avenues

1. **Position the PR as "generalise `fourier_comp_linearIsometry`."** The cleanest framing for
   reviewers: keep the existing isometry lemma as the corollary, add `fourier_comp_linearEquiv` as
   the general statement, and prove the isometry version *from* it (or note the relationship). This
   slots directly into `FourierTransform.lean` next to the existing lemmas and is an easy review
   because it strictly extends an accepted result.

2. **Add the inverse-transform companion.** Mathlib pairs `fourier_comp_linearIsometry` with
   `fourierInv_comp_linearIsometry`. To match, our PR should add the `𝓕⁻` companion of
   `fourier_comp_linearEquiv` (via `fourierInv_eq_fourier_neg`), so the general case has the same API
   surface as the isometry case.

3. **Engage `mcdoll` early.** Given the active Fourier work (#35291, and the convolution
   generalisation #40583), a short Zulip note proposing the general change-of-variables — with the
   determinant factor and adjoint reparametrisation — will surface any naming/placement preferences
   (e.g. whether it belongs in `FourierTransform.lean` or a new
   `FourierTransformChangeOfVariables.lean`) before a PR is opened.

## Recommendation

**Upstream candidate, high confidence, low controversy.** Submit `fourier_comp_linearEquiv` (plus its
`𝓕⁻` companion) to `Mathlib/Analysis/Fourier/FourierTransform.lean`, framed as the general-`A`
extension of the existing isometry lemmas. No competing PR exists; the only coordination is naming/
placement with `mcdoll`.

**Upstream target:** `Mathlib/Analysis/Fourier/FourierTransform.lean`.
