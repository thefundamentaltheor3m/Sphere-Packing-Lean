module
public import SpherePacking.Basic.Domains.WedgeSet
public import SpherePacking.MagicFunction.a.Basic

import SpherePacking.MagicFunction.PolyFourierCoeffBound

/-!
# Wedge-domain limit for `Φ₃'` at `1`

We prove the boundary limit needed for the contour deformation argument in `perm_I₁_I₂`: the
integrand `Φ₃' r` tends to `0` as `z → 1` within the closure of the wedge domain `wedgeSet`.

## Main statements
* `tendsto_Φ₃'_one_within_closure_wedgeSet`
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology Interval
open Filter SpherePacking MeasureTheory Set Complex Real

/-- `Φ₃' r` tends to `0` as `z → 1` within `closure wedgeSet`. -/
public lemma tendsto_Φ₃'_one_within_closure_wedgeSet (r : ℝ) :
    Tendsto (MagicFunction.a.ComplexIntegrands.Φ₃' r) (𝓝[closure wedgeSet] (1 : ℂ)) (𝓝 0) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  let expNorm : ℂ → ℝ := fun z ↦ ‖cexp (Real.pi * Complex.I * r * z)‖
  have hExp : ContinuousAt expNorm (1 : ℂ) := by fun_prop
  let M : ℝ := expNorm (1 : ℂ) + 1
  have hMpos : 0 < M := by positivity
  obtain ⟨δexp, hδexp_pos, hδexp⟩ := (Metric.continuousAt_iff.1 hExp) 1 (by norm_num)
  have hExpBound : ∀ {z : ℂ}, dist z (1 : ℂ) < δexp → expNorm z ≤ M := by
    intro z hz
    have habs : |expNorm z - expNorm (1 : ℂ)| < 1 := by
      simpa [Real.dist_eq] using hδexp hz
    simp only [M]
    linarith [le_abs_self (expNorm z - expNorm (1 : ℂ))]
  refine (Metric.tendsto_nhdsWithin_nhds).2 ?_
  intro ε hε
  -- Get a radius making the simple upper bound `C₀ * dist(z,1)^2 * M` less than `ε`.
  have hub :
      Tendsto (fun z : ℂ => (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M) (𝓝 (1 : ℂ))
        (𝓝 (0 : ℝ)) := by
    have hcont : Continuous (fun z : ℂ => (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M) := by
      fun_prop
    simpa using hcont.tendsto (1 : ℂ)
  obtain ⟨δpow, hδpow_pos, hδpow⟩ :=
    Metric.mem_nhds_iff.1 <| Metric.tendsto_nhds.1 hub ε hε
  let δ : ℝ := min δexp (min 1 δpow)
  have hδ_pos : 0 < δ := lt_min hδexp_pos (lt_min (by norm_num) hδpow_pos)
  refine ⟨δ, hδ_pos, ?_⟩
  intro z hzcl hdistz
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    simpa [MagicFunction.a.ComplexIntegrands.Φ₃'] using hε
  have hdist_exp : dist z (1 : ℂ) < δexp :=
    lt_of_lt_of_le hdistz (min_le_left _ _)
  have hdist_lt1 : dist z (1 : ℂ) < 1 :=
    lt_of_lt_of_le hdistz (le_trans (min_le_right _ _) (min_le_left _ _))
  have hdist_pow : dist z (1 : ℂ) < δpow :=
    lt_of_lt_of_le hdistz (le_trans (min_le_right _ _) (min_le_right _ _))
  have hexpZ : expNorm z ≤ M := hExpBound hdist_exp
  have hzU : z ∈ UpperHalfPlane.upperHalfPlaneSet :=
    mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hzcl hz1
  have hz_im_pos : 0 < z.im := by simpa [UpperHalfPlane.upperHalfPlaneSet] using hzU
  have habs_re : |z.re - 1| ≤ z.im :=
    SpherePacking.closure_wedgeSet_subset_abs_re_sub_one_le_im hzcl
  -- Show `(-1/(z-1)).im > 1/2` for `z` close to `1` in the wedge closure.
  have hnormSq_pos : 0 < Complex.normSq (z - 1) :=
    Complex.normSq_pos.2 (sub_ne_zero.mpr hz1)
  have hz_im_lt1 : z.im < 1 := by
    have hz_im_le : z.im ≤ ‖z - 1‖ := by
      simpa [abs_of_nonneg hz_im_pos.le] using Complex.abs_im_le_norm (z - 1)
    exact hz_im_le.trans_lt (by simpa [dist_eq_norm] using hdist_lt1)
  have hnormSq_le : Complex.normSq (z - 1) ≤ 2 * z.im ^ 2 := by
    have hre_sq : (z.re - 1) ^ 2 ≤ z.im ^ 2 := by
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs_re 2
    have : Complex.normSq (z - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := by
      simp [Complex.normSq, sub_eq_add_neg, pow_two, add_comm]
    linarith
  have hw_half : (1 / 2 : ℝ) < (-1 / (z - 1)).im := by
    have him : (-1 / (z - 1)).im = z.im / Complex.normSq (z - 1) := by
      simp [div_eq_mul_inv, Complex.inv_im, sub_eq_add_neg]
    rw [him, lt_div_iff₀ hnormSq_pos]
    nlinarith [hnormSq_le, hz_im_pos, hz_im_lt1]
  have hw_pos : 0 < (-1 / (z - 1)).im := lt_trans (by norm_num) hw_half
  -- Bound `‖φ₀''(-1/(z-1))‖` by `C₀`.
  have hφ₀'' : ‖φ₀'' (-1 / (z - 1))‖ ≤ (C₀ : ℝ) := by
    let wH : UpperHalfPlane := ⟨-1 / (z - 1), hw_pos⟩
    have hφ₀_eq : φ₀ wH = φ₀'' (-1 / (z - 1)) := by
      simpa [wH] using (φ₀''_def (z := (-1 / (z - 1))) hw_pos).symm
    have hexp : Real.exp (-2 * Real.pi * wH.im) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have : 0 ≤ Real.pi * wH.im := mul_nonneg Real.pi_pos.le wH.2.le
      linarith
    calc ‖φ₀'' (-1 / (z - 1))‖
        = ‖φ₀ wH‖ := by rw [hφ₀_eq]
      _ ≤ (C₀ : ℝ) * Real.exp (-2 * Real.pi * wH.im) := hC₀ wH hw_half
      _ ≤ (C₀ : ℝ) * 1 := by gcongr
      _ = (C₀ : ℝ) := mul_one _
  have hmain :
      ‖MagicFunction.a.ComplexIntegrands.Φ₃' r z‖ ≤ (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M := by
    have heq : ‖MagicFunction.a.ComplexIntegrands.Φ₃' r z‖
        = ‖φ₀'' (-1 / (z - 1))‖ * (dist z (1 : ℂ)) ^ (2 : ℕ) * expNorm z := by
      simp [MagicFunction.a.ComplexIntegrands.Φ₃', expNorm, dist_eq_norm, mul_left_comm, mul_comm]
    rw [heq]
    gcongr
  have hpow_small : (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M < ε := by
    have hnn : 0 ≤ (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M := by positivity
    have h : dist ((C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M) (0 : ℝ) < ε :=
      hδpow (show z ∈ Metric.ball (1 : ℂ) δpow from hdist_pow)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at h
  simpa [dist_eq_norm] using lt_of_le_of_lt hmain hpow_small

end

end MagicFunction.a.Fourier
