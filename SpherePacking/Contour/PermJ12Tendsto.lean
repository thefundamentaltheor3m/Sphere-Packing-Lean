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

private lemma exists_expNorm_le_add_one (r : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {z : ℂ}, dist z (1 : ℂ) < δ → expNorm r z ≤ expNorm r (1 : ℂ) + 1 := by
  have hcont : ContinuousAt (expNorm r) (1 : ℂ) := by
    simpa [expNorm] using (continuousAt_id.mul continuousAt_const).cexp.norm
  rcases (Metric.continuousAt_iff.1 hcont) 1 (by norm_num) with ⟨δ, hδ_pos, hδ⟩
  exact ⟨δ, hδ_pos, fun {z} hz => le_of_lt (sub_lt_iff_lt_add'.1
    (abs_sub_lt_iff.1 (by simpa [Real.dist_eq] using hδ hz)).1)⟩

private lemma exists_im_bound_norm_ψS_le_one {ψS : UpperHalfPlane → ℂ}
    (tendsto_ψS_atImInfty : Tendsto ψS UpperHalfPlane.atImInfty (𝓝 (0 : ℂ))) :
    ∃ A : ℝ, 0 < A ∧ ∀ τ : UpperHalfPlane, A ≤ τ.im → ‖ψS τ‖ ≤ (1 : ℝ) := by
  rcases (UpperHalfPlane.atImInfty_mem (S := {τ : UpperHalfPlane | ‖ψS τ‖ < (1 : ℝ)})).1
    (((tendsto_zero_iff_norm_tendsto_zero).1 tendsto_ψS_atImInfty).eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))) with ⟨A0, hA0⟩
  exact ⟨max A0 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun τ hτ =>
    le_of_lt (hA0 τ (le_trans (le_max_left _ _) hτ))⟩

private lemma one_div_two_im_le_im_div_normSq_sub_one {z : ℂ}
    (hz_im_pos : 0 < z.im) (hz1 : z ≠ (1 : ℂ)) (habs_re : |z.re - 1| ≤ z.im) :
    (1 : ℝ) / (2 * z.im) ≤ z.im / Complex.normSq (z - 1) := by
  have hnormSq_pos : 0 < Complex.normSq (z - 1) := Complex.normSq_pos.2 (sub_ne_zero.mpr hz1)
  have hnormSq_le : Complex.normSq (z - 1) ≤ 2 * z.im ^ 2 := by
    have hre_sq : (z.re - 1) ^ 2 ≤ z.im ^ 2 := by
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs_re 2
    have hnormSq : Complex.normSq (z - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := by
      simp [Complex.normSq, sub_eq_add_neg, pow_two, add_comm]
    nlinarith [hnormSq, hre_sq]
  calc (1 : ℝ) / (2 * z.im) = z.im * ((1 : ℝ) / (2 * z.im ^ 2)) := by field_simp
    _ ≤ z.im * ((1 : ℝ) / Complex.normSq (z - 1)) :=
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hnormSq_pos hnormSq_le) hz_im_pos.le
    _ = z.im / Complex.normSq (z - 1) := by simp [div_eq_mul_inv]


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
  let M : ℝ := expNorm r (1 : ℂ) + 1
  have hMpos : 0 < M := by
    have : (0 : ℝ) ≤ expNorm r (1 : ℂ) := norm_nonneg _; linarith
  obtain ⟨δexp, hδexp_pos, hExpBound⟩ := exists_expNorm_le_add_one (r := r)
  obtain ⟨A, hApos, hA⟩ := exists_im_bound_norm_ψS_le_one (ψS := ψS) h.tendsto_ψS_atImInfty
  refine (Metric.tendsto_nhdsWithin_nhds).2 fun ε hε => ?_
  refine ⟨min δexp (min (min 1 (ε / M)) (1 / (2 * A))),
    lt_min hδexp_pos (lt_min (lt_min (by norm_num) (div_pos hε hMpos)) (by positivity)),
    fun z hzcl hdistz => ?_⟩
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    simpa [h.Ψ₁'_eq, h.ψT'_one] using hε
  have hz_im_pos : 0 < z.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using
      (h.mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hzcl hz1)
  let zH : UpperHalfPlane := ⟨z, hz_im_pos⟩
  have hexpZ : expNorm r z ≤ M :=
    hExpBound (lt_of_lt_of_le hdistz (min_le_left _ _))
  have hdist_min := lt_of_lt_of_le hdistz (min_le_right _ _)
  have hdist_lt := lt_of_lt_of_le hdist_min (min_le_left _ _)
  have hdist_lt_one : dist z (1 : ℂ) < 1 := lt_of_lt_of_le hdist_lt (min_le_left _ _)
  have hdist_pow : (dist z (1 : ℂ)) ^ k < ε / M :=
    (by simpa [pow_one] using pow_le_pow_of_le_one dist_nonneg hdist_lt_one.le h.hk
      : (dist z (1 : ℂ)) ^ k ≤ dist z (1 : ℂ)).trans_lt
        (lt_of_lt_of_le hdist_lt (min_le_right _ _))
  have hdist_im : dist z (1 : ℂ) < 1 / (2 * A) :=
    lt_of_lt_of_le hdist_min (min_le_right _ _)
  have hA_le_im : A ≤ (gAct zH).im := by
    have hz_im_lt : z.im < 1 / (2 * A) :=
      lt_of_le_of_lt
        (by simpa [abs_of_nonneg (le_of_lt hz_im_pos)] using Complex.abs_im_le_norm (z - 1))
        (by simpa [dist_eq_norm] using hdist_im)
    have hA_lt : A < (1 : ℝ) / (2 * z.im) :=
      (lt_div_iff₀ (by positivity)).2 (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (lt_div_iff₀ (by positivity)).1 hz_im_lt)
    have := hA_lt.trans_le (one_div_two_im_le_im_div_normSq_sub_one (z := z) hz_im_pos hz1
      (h.closure_wedgeSet_subset_abs_re_sub_one_le_im hzcl))
    simpa [zH, h.gAct_im (z := z) (hz := hz_im_pos)] using this.le
  have hψT_norm : ‖ψT' z‖ ≤ ‖(z - 1) ^ k‖ := by
    have hψ : ψT' z = -ψS (gAct zH) * (z - 1) ^ k := by
      simpa [zH] using (h.ψT'_eq_neg_ψS_mul (z := z) (hz := hz_im_pos))
    calc ‖ψT' z‖ = ‖ψS (gAct zH)‖ * ‖(z - 1) ^ k‖ := by simp [hψ, norm_neg]
      _ ≤ 1 * ‖(z - 1) ^ k‖ := mul_le_mul_of_nonneg_right (hA _ hA_le_im) (norm_nonneg _)
      _ = _ := by simp
  have hmain : ‖Ψ₁' r z‖ ≤ (dist z (1 : ℂ)) ^ k * M := by
    have hcexp : ‖cexp ((Real.pi : ℂ) * Complex.I * (r : ℂ) * z)‖ = expNorm r z := by
      simp [expNorm, show ((Real.pi : ℂ) * Complex.I * (r : ℂ) * z) =
        z * (Complex.I * ((r : ℂ) * (Real.pi : ℂ))) by ac_rfl]
    calc ‖Ψ₁' r z‖ = ‖ψT' z‖ * expNorm r z := by simp [h.Ψ₁'_eq, hcexp]
      _ ≤ ‖(z - 1) ^ k‖ * expNorm r z :=
          mul_le_mul_of_nonneg_right hψT_norm (by simp [expNorm])
      _ ≤ ‖(z - 1) ^ k‖ * M := mul_le_mul_of_nonneg_left hexpZ (norm_nonneg _)
      _ = (dist z (1 : ℂ)) ^ k * M := by simp [dist_eq_norm, norm_pow]
  simpa [dist_eq_norm] using hmain.trans_lt ((lt_div_iff₀ hMpos).mp hdist_pow)

end

end SpherePacking.Contour
