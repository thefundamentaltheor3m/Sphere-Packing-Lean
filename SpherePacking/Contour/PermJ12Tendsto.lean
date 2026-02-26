module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Tendsto for the `Ψ₁'` integrand near `z = 1`

In the `perm_J12` contour deformation, one needs a limit statement of the form
`Tendsto (Ψ₁' r) (𝓝[closure wedgeSet] 1) (𝓝 0)`.

This file isolates that argument in a dimension-agnostic form. We assume:
- a factorization `Ψ₁' r z = ψT' z * cexp (π * I * r * z)`;
- a modular identity expressing `ψT'` in terms of a function `ψS` evaluated at `gAct z`; and
- basic geometric control of `gAct z` on `closure wedgeSet`.

## Main definitions
* `TendstoPsiOneHypotheses`

## Main statements
* `tendsto_Ψ₁'_one_within_closure_wedgeSet_of`
-/

open Set Filter
open scoped Topology Complex

namespace SpherePacking.Contour

noncomputable section

/-- Differentiability of `z ↦ ψ z * exp(π * I * r * z)` on a set. -/
public lemma differentiableOn_mul_cexp_pi_I_mul_real
    {s : Set ℂ} {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ s) (r : ℝ) :
    DifferentiableOn ℂ
      (fun z : ℂ => ψ z * cexp ((Real.pi : ℂ) * Complex.I * (r : ℂ) * z)) s := by
  have hexp :
      DifferentiableOn ℂ
        (fun z : ℂ => cexp (((Real.pi : ℂ) * Complex.I * (r : ℂ)) * z)) s :=
    (differentiable_id.const_mul ((Real.pi : ℂ) * Complex.I * (r : ℂ))).cexp.differentiableOn
  simpa [mul_assoc] using hψ.mul hexp

/--
`TendstoPsiOneHypotheses wedgeSet ψS ψT' Ψ₁' gAct k` bundles the hypotheses used to prove
`Tendsto (Ψ₁' r) (𝓝[closure wedgeSet] 1) (𝓝 0)`.

This keeps downstream call sites from having to thread a long list of modular-identity and
geometry hypotheses.
-/
public structure TendstoPsiOneHypotheses
    (wedgeSet : Set ℂ)
    (ψS : UpperHalfPlane → ℂ)
    (ψT' : ℂ → ℂ)
    (Ψ₁' : ℝ → ℂ → ℂ)
    (gAct : UpperHalfPlane → UpperHalfPlane)
    (k : ℕ) : Prop where
  hk : (1 : ℕ) ≤ k
  Ψ₁'_eq :
    ∀ r : ℝ, ∀ z : ℂ, Ψ₁' r z = ψT' z * cexp ((Real.pi : ℂ) * Complex.I * (r : ℂ) * z)
  ψT'_one : ψT' (1 : ℂ) = 0
  tendsto_ψS_atImInfty : Tendsto ψS UpperHalfPlane.atImInfty (𝓝 (0 : ℂ))
  gAct_im :
    ∀ {z : ℂ} (hz : 0 < z.im),
      (gAct (⟨z, hz⟩ : UpperHalfPlane)).im = z.im / Complex.normSq (z - 1)
  ψT'_eq_neg_ψS_mul :
    ∀ {z : ℂ} (hz : 0 < z.im),
      ψT' z = -ψS (gAct (⟨z, hz⟩ : UpperHalfPlane)) * (z - 1) ^ k
  mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one :
    ∀ {z : ℂ}, z ∈ closure wedgeSet → z ≠ (1 : ℂ) → z ∈ UpperHalfPlane.upperHalfPlaneSet
  closure_wedgeSet_subset_abs_re_sub_one_le_im :
    ∀ {z : ℂ}, z ∈ closure wedgeSet → |z.re - 1| ≤ z.im

private def expNorm (r : ℝ) : ℂ → ℝ :=
  fun z ↦ ‖cexp (z * (Complex.I * ((r : ℂ) * (Real.pi : ℂ))))‖

private lemma expNorm_continuousAt (r : ℝ) :
    ContinuousAt (expNorm r) (1 : ℂ) := by
  simpa [expNorm] using (continuousAt_id.mul continuousAt_const).cexp.norm

private lemma exists_expNorm_le_add_one (r : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {z : ℂ}, dist z (1 : ℂ) < δ → expNorm r z ≤ expNorm r (1 : ℂ) + 1 := by
  rcases (Metric.continuousAt_iff.1 (expNorm_continuousAt (r := r))) 1 (by norm_num) with
    ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, fun {z} hz => ?_⟩
  have habs : |expNorm r z - expNorm r (1 : ℂ)| < 1 := by
    simpa [Real.dist_eq] using hδ hz
  exact le_of_lt (sub_lt_iff_lt_add'.1 (abs_sub_lt_iff.1 habs).1)

private lemma exists_im_bound_norm_ψS_le_one {ψS : UpperHalfPlane → ℂ}
    (tendsto_ψS_atImInfty : Tendsto ψS UpperHalfPlane.atImInfty (𝓝 (0 : ℂ))) :
    ∃ A : ℝ, 0 < A ∧ ∀ τ : UpperHalfPlane, A ≤ τ.im → ‖ψS τ‖ ≤ (1 : ℝ) := by
  have htendNorm :
      Tendsto (fun τ : UpperHalfPlane => ‖ψS τ‖) UpperHalfPlane.atImInfty (𝓝 (0 : ℝ)) :=
    (tendsto_zero_iff_norm_tendsto_zero).1 tendsto_ψS_atImInfty
  let Sψ : Set UpperHalfPlane := {τ : UpperHalfPlane | ‖ψS τ‖ < (1 : ℝ)}
  have hSet_mem : Sψ ∈ UpperHalfPlane.atImInfty := by
    simpa [Sψ] using htendNorm.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  rcases (UpperHalfPlane.atImInfty_mem (S := Sψ)).1 hSet_mem with ⟨A0, hA0⟩
  refine ⟨max A0 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun τ hτ => ?_⟩
  exact le_of_lt (hA0 τ (le_trans (le_max_left _ _) hτ))

private lemma one_div_two_im_le_im_div_normSq_sub_one {z : ℂ}
    (hz_im_pos : 0 < z.im) (hz1 : z ≠ (1 : ℂ)) (habs_re : |z.re - 1| ≤ z.im) :
    (1 : ℝ) / (2 * z.im) ≤ z.im / Complex.normSq (z - 1) := by
  have hz_im_ne : z.im ≠ 0 := ne_of_gt hz_im_pos
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hnormSq_pos : 0 < Complex.normSq (z - 1) := (Complex.normSq_pos).2 hz1'
  have hnormSq_le : Complex.normSq (z - 1) ≤ 2 * z.im ^ 2 := by
    have hre_sq : (z.re - 1) ^ 2 ≤ z.im ^ 2 := by
      have : |z.re - 1| ^ 2 ≤ z.im ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs_re 2
      simpa [sq_abs] using this
    have hnormSq : Complex.normSq (z - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := by
      simp [Complex.normSq, sub_eq_add_neg, pow_two, add_comm]
    nlinarith [hnormSq, hre_sq]
  have hInv :
      (1 : ℝ) / (2 * z.im ^ 2) ≤ (1 : ℝ) / Complex.normSq (z - 1) :=
    one_div_le_one_div_of_le hnormSq_pos hnormSq_le
  have hMul :
      z.im * ((1 : ℝ) / (2 * z.im ^ 2)) ≤ z.im * ((1 : ℝ) / Complex.normSq (z - 1)) :=
    mul_le_mul_of_nonneg_left hInv (le_of_lt hz_im_pos)
  have h1 : (1 : ℝ) / (2 * z.im) = z.im * ((1 : ℝ) / (2 * z.im ^ 2)) := by
    field_simp [hz_im_ne]
  calc
    (1 : ℝ) / (2 * z.im) = z.im * ((1 : ℝ) / (2 * z.im ^ 2)) := h1
    _ ≤ z.im * ((1 : ℝ) / Complex.normSq (z - 1)) := hMul
    _ = z.im / Complex.normSq (z - 1) := by simp [div_eq_mul_inv]

private structure GActImNearOneHyp (wedgeSet : Set ℂ)
    (gAct : UpperHalfPlane → UpperHalfPlane) : Prop where
  gAct_im :
    ∀ {z : ℂ} (hz : 0 < z.im),
      (gAct (⟨z, hz⟩ : UpperHalfPlane)).im = z.im / Complex.normSq (z - 1)
  mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one :
    ∀ {z : ℂ}, z ∈ closure wedgeSet → z ≠ (1 : ℂ) → z ∈ UpperHalfPlane.upperHalfPlaneSet
  closure_wedgeSet_subset_abs_re_sub_one_le_im :
    ∀ {z : ℂ}, z ∈ closure wedgeSet → |z.re - 1| ≤ z.im

private lemma exists_gAct_im_ge_of_dist_lt
    {wedgeSet : Set ℂ}
    {gAct : UpperHalfPlane → UpperHalfPlane}
    (hg : GActImNearOneHyp wedgeSet gAct)
    {A : ℝ} (hApos : 0 < A)
    {z : ℂ} (hzcl : z ∈ closure wedgeSet) (hz1 : z ≠ (1 : ℂ))
    (hdist : dist z (1 : ℂ) < 1 / (2 * A)) :
    ∃ hz_im_pos : 0 < z.im, A ≤ (gAct (⟨z, hz_im_pos⟩ : UpperHalfPlane)).im := by
  have hz_im_pos : 0 < z.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using
      (hg.mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hzcl hz1)
  have hz_im_lt : z.im < 1 / (2 * A) := by
    have hnorm : ‖z - 1‖ < 1 / (2 * A) := by simpa [dist_eq_norm] using hdist
    have hz_im_le : z.im ≤ ‖z - 1‖ := by
      simpa [abs_of_nonneg (le_of_lt hz_im_pos)] using (Complex.abs_im_le_norm (z - 1))
    exact lt_of_le_of_lt hz_im_le hnorm
  have habs_re : |z.re - 1| ≤ z.im := hg.closure_wedgeSet_subset_abs_re_sub_one_le_im hzcl
  have hLower : (1 : ℝ) / (2 * z.im) ≤ z.im / Complex.normSq (z - 1) :=
    one_div_two_im_le_im_div_normSq_sub_one (z := z) hz_im_pos hz1 habs_re
  have hA_lt : A < (1 : ℝ) / (2 * z.im) := by
    have hmul : z.im * (2 * A) < (1 : ℝ) := (lt_div_iff₀ (by positivity)).1 hz_im_lt
    exact (lt_div_iff₀ (by positivity)).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
  refine ⟨hz_im_pos, ?_⟩
  have : A < (gAct (⟨z, hz_im_pos⟩ : UpperHalfPlane)).im := by
    have : A < z.im / Complex.normSq (z - 1) := lt_of_lt_of_le hA_lt hLower
    simpa [hg.gAct_im (z := z) (hz := hz_im_pos)] using this
  exact this.le

/--
Under `TendstoPsiOneHypotheses`, the integrand `Ψ₁' r` tends to `0` as `z → 1` within
`closure wedgeSet`.

This is the analytic input used to justify the `perm_J12` contour deformation at the corner
`z = 1`.
-/
public lemma tendsto_Ψ₁'_one_within_closure_wedgeSet_of
    {wedgeSet : Set ℂ}
    {ψS : UpperHalfPlane → ℂ}
    {ψT' : ℂ → ℂ}
    {Ψ₁' : ℝ → ℂ → ℂ}
    {gAct : UpperHalfPlane → UpperHalfPlane}
    {k : ℕ}
    (h : TendstoPsiOneHypotheses wedgeSet ψS ψT' Ψ₁' gAct k)
    (r : ℝ) :
    Tendsto (Ψ₁' r) (𝓝[closure wedgeSet] (1 : ℂ)) (𝓝 0) := by
  -- Bound the exponential factor near `1`.
  let M : ℝ := expNorm r (1 : ℂ) + 1
  have hMpos : 0 < M := by
    have : 0 ≤ expNorm r (1 : ℂ) := norm_nonneg _
    linarith
  rcases exists_expNorm_le_add_one (r := r) with ⟨δexp, hδexp_pos, hExpBound'⟩
  have hExpBound : ∀ {z : ℂ}, dist z (1 : ℂ) < δexp → expNorm r z ≤ M := by
    intro z hz
    simpa [M] using hExpBound' (z := z) hz
  -- From `ψS → 0` at `i∞`, get a uniform bound `‖ψS τ‖ ≤ 1` for large `im τ`.
  rcases exists_im_bound_norm_ψS_le_one (ψS := ψS) h.tendsto_ψS_atImInfty with ⟨A, hApos, hA⟩
  -- Metric characterization of `Tendsto` within a set.
  refine (Metric.tendsto_nhdsWithin_nhds).2 ?_
  intro ε hε
  let δ0 : ℝ := min 1 (ε / M)
  have hδ0_pos : 0 < δ0 := by
    have hdiv : 0 < ε / M := div_pos hε hMpos
    exact lt_min (by norm_num) hdiv
  let δ : ℝ := min δexp (min δ0 (1 / (2 * A)))
  have hδ_pos : 0 < δ := lt_min hδexp_pos (lt_min hδ0_pos (by positivity))
  refine ⟨δ, hδ_pos, ?_⟩
  intro z hzcl hdistz
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    simpa [h.Ψ₁'_eq, h.ψT'_one] using hε
  have hzU : z ∈ UpperHalfPlane.upperHalfPlaneSet :=
    h.mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hzcl hz1
  have hz_im_pos : 0 < z.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using hzU
  let zH : UpperHalfPlane := ⟨z, hz_im_pos⟩
  have hexpZ : expNorm r z ≤ M :=
    hExpBound (lt_of_lt_of_le hdistz (min_le_left _ _))
  have hdist_min : dist z (1 : ℂ) < min δ0 (1 / (2 * A)) :=
    lt_of_lt_of_le hdistz (min_le_right _ _)
  have hdist_lt : dist z (1 : ℂ) < δ0 :=
    lt_of_lt_of_le hdist_min (min_le_left _ _)
  have hdist_lt_one : dist z (1 : ℂ) < 1 :=
    lt_of_lt_of_le hdist_lt (min_le_left _ _)
  have hdist_lt_div : dist z (1 : ℂ) < ε / M :=
    lt_of_lt_of_le hdist_lt (min_le_right _ _)
  have hdist_pow : (dist z (1 : ℂ)) ^ k < ε / M := by
    have hnonneg : 0 ≤ dist z (1 : ℂ) := dist_nonneg
    have hle_one : dist z (1 : ℂ) ≤ 1 := le_of_lt hdist_lt_one
    have hpow_le : (dist z (1 : ℂ)) ^ k ≤ dist z (1 : ℂ) := by
      simpa [pow_one] using (pow_le_pow_of_le_one hnonneg hle_one h.hk)
    exact lt_of_le_of_lt hpow_le hdist_lt_div
  -- Force `z.im` to be small, so the transformed point has large imaginary part.
  have hdist_im : dist z (1 : ℂ) < 1 / (2 * A) :=
    lt_of_lt_of_le hdist_min (min_le_right _ _)
  have hA_le_im : A ≤ (gAct zH).im := by
    let hg : GActImNearOneHyp wedgeSet gAct :=
      { gAct_im := h.gAct_im
        mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one :=
          h.mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one
        closure_wedgeSet_subset_abs_re_sub_one_le_im :=
          h.closure_wedgeSet_subset_abs_re_sub_one_le_im }
    rcases
      exists_gAct_im_ge_of_dist_lt (wedgeSet := wedgeSet) (gAct := gAct)
        (hg := hg) hApos (hzcl := hzcl) (hz1 := hz1) hdist_im with ⟨hz', hA'⟩
    assumption
  have hψS_bound : ‖ψS (gAct zH)‖ ≤ (1 : ℝ) := hA _ hA_le_im
  have hψT_norm : ‖ψT' z‖ ≤ ‖(z - 1) ^ k‖ := by
    have hψ : ψT' z = -ψS (gAct zH) * (z - 1) ^ k := by
      simpa [zH] using (h.ψT'_eq_neg_ψS_mul (z := z) (hz := hz_im_pos))
    calc
      ‖ψT' z‖ = ‖ψS (gAct zH)‖ * ‖(z - 1) ^ k‖ := by
            simp [hψ, norm_neg]
      _ ≤ (1 : ℝ) * ‖(z - 1) ^ k‖ := by
            exact mul_le_mul_of_nonneg_right hψS_bound (norm_nonneg _)
      _ = ‖(z - 1) ^ k‖ := by simp
  have hmain :
      ‖Ψ₁' r z‖ ≤ (dist z (1 : ℂ)) ^ k * M := by
    have hmul :
        ((Real.pi : ℂ) * Complex.I * (r : ℂ) * z) =
          z * (Complex.I * ((r : ℂ) * (Real.pi : ℂ))) := by
      ac_rfl
    have hExpMul : ‖Ψ₁' r z‖ = ‖ψT' z‖ * expNorm r z := by
      have hcexp :
          ‖cexp ((Real.pi : ℂ) * Complex.I * (r : ℂ) * z)‖ = expNorm r z := by
        simp [expNorm, hmul]
      calc
        ‖Ψ₁' r z‖ = ‖ψT' z * cexp ((Real.pi : ℂ) * Complex.I * (r : ℂ) * z)‖ := by
          simp [h.Ψ₁'_eq]
        _ = ‖ψT' z‖ * ‖cexp ((Real.pi : ℂ) * Complex.I * (r : ℂ) * z)‖ := by
          simp
        _ = ‖ψT' z‖ * expNorm r z := by
          simp [hcexp]
    have hpow : ‖(z - 1) ^ k‖ = (dist z (1 : ℂ)) ^ k := by
      simp [dist_eq_norm, norm_pow]
    calc
      ‖Ψ₁' r z‖ = ‖ψT' z‖ * expNorm r z := hExpMul
      _ ≤ ‖(z - 1) ^ k‖ * expNorm r z := by
            have hexp : 0 ≤ expNorm r z := by simp [expNorm]
            exact mul_le_mul_of_nonneg_right hψT_norm hexp
      _ ≤ ‖(z - 1) ^ k‖ * M := by
            exact mul_le_mul_of_nonneg_left hexpZ (norm_nonneg _)
      _ = (dist z (1 : ℂ)) ^ k * M := by
            simp [hpow]
  have : ‖Ψ₁' r z‖ < ε := by
    have hε' : (dist z (1 : ℂ)) ^ k * M < ε := by
      have htmp : (dist z (1 : ℂ)) ^ k * M < (ε / M) * M :=
        mul_lt_mul_of_pos_right hdist_pow hMpos
      have hMne : M ≠ 0 := ne_of_gt hMpos
      have hcancel : (ε / M) * M = ε := by
        field_simp [hMne]
      simpa [hcancel] using htmp
    exact lt_of_le_of_lt hmain hε'
  simpa [dist_eq_norm] using this

end

end SpherePacking.Contour
