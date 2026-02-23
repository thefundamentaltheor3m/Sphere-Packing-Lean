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

open scoped FourierTransform RealInnerProductSpace Topology
open Filter SpherePacking

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open MeasureTheory Set Complex Real
open scoped Interval


/-- `Φ₃' r` tends to `0` as `z → 1` within `closure wedgeSet`. -/
public lemma tendsto_Φ₃'_one_within_closure_wedgeSet (r : ℝ) :
    Tendsto (MagicFunction.a.ComplexIntegrands.Φ₃' r) (𝓝[closure wedgeSet] (1 : ℂ)) (𝓝 0) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  let expNorm : ℂ → ℝ := fun z ↦ ‖cexp (Real.pi * Complex.I * r * z)‖
  have hExp : ContinuousAt expNorm (1 : ℂ) := by
    dsimp [expNorm]
    fun_prop
  let M : ℝ := expNorm (1 : ℂ) + 1
  have hMpos : 0 < M := by
    have : 0 ≤ expNorm (1 : ℂ) := norm_nonneg _
    linarith
  obtain ⟨δexp, hδexp_pos, hδexp⟩ := (Metric.continuousAt_iff.1 hExp) 1 (by norm_num)
  have hExpBound : ∀ {z : ℂ}, dist z (1 : ℂ) < δexp → expNorm z ≤ M := by
    intro z hz
    have hdist : dist (expNorm z) (expNorm (1 : ℂ)) < 1 := hδexp hz
    have habs : |expNorm z - expNorm (1 : ℂ)| < 1 := by
      simpa [Real.dist_eq] using hdist
    have : expNorm z < expNorm (1 : ℂ) + 1 :=
      by linarith [lt_of_le_of_lt (le_abs_self _) habs]
    exact le_of_lt (by simpa [M] using this)
  refine (Metric.tendsto_nhdsWithin_nhds).2 ?_
  intro ε hε
  -- Get a radius making the simple upper bound `C₀ * dist(z,1)^2 * M` less than `ε`.
  have hCMpos : 0 < (C₀ : ℝ) * M := mul_pos hC₀_pos hMpos
  have hdist0 : Tendsto (fun z : ℂ => dist z (1 : ℂ)) (𝓝 (1 : ℂ)) (𝓝 (0 : ℝ)) := by
    simpa using
      ((tendsto_id : Tendsto (fun z : ℂ => z) (𝓝 (1 : ℂ)) (𝓝 (1 : ℂ))).dist
        (tendsto_const_nhds : Tendsto (fun _ : ℂ => (1 : ℂ)) (𝓝 (1 : ℂ)) (𝓝 (1 : ℂ))))
  have hpow0 :
      Tendsto (fun z : ℂ => (dist z (1 : ℂ)) ^ (2 : ℕ)) (𝓝 (1 : ℂ)) (𝓝 (0 : ℝ)) := by
    have hcont : ContinuousAt (fun t : ℝ => t ^ (2 : ℕ)) (0 : ℝ) := by
      fun_prop
    simpa using (hcont.tendsto.comp hdist0)
  have hub :
      Tendsto (fun z : ℂ => (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M) (𝓝 (1 : ℂ))
        (𝓝 (0 : ℝ)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hpow0.const_mul ((C₀ : ℝ) * M))
  have hEv :
      {z : ℂ | dist ((C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M) (0 : ℝ) < ε} ∈ 𝓝 (1 : ℂ) :=
    (Metric.tendsto_nhds.1 hub) ε hε
  rcases Metric.mem_nhds_iff.1 hEv with ⟨δpow, hδpow_pos, hδpow⟩
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
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hnormSq_pos : 0 < Complex.normSq (z - 1) := (Complex.normSq_pos).2 hz1'
  have hz_im_lt1 : z.im < 1 := by
    have hz_im_le : z.im ≤ ‖z - 1‖ := by
      have hz_im_nonneg : 0 ≤ z.im := le_of_lt hz_im_pos
      have habs : |(z - 1).im| ≤ ‖z - 1‖ := Complex.abs_im_le_norm (z - 1)
      simpa [sub_eq_add_neg, abs_of_nonneg hz_im_nonneg] using habs
    exact lt_of_le_of_lt hz_im_le (by simpa [dist_eq_norm] using hdist_lt1)
  have hnormSq_le : Complex.normSq (z - 1) ≤ 2 * z.im ^ 2 := by
    have hre_sq : (z.re - 1) ^ 2 ≤ z.im ^ 2 := by
      have h' : |z.re - 1| ^ 2 ≤ z.im ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs_re 2
      simpa [sq_abs] using h'
    have hnormSq :
        Complex.normSq (z - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := by
      simp [Complex.normSq, sub_eq_add_neg, pow_two, add_comm]
    calc
      Complex.normSq (z - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := hnormSq
      _ ≤ z.im ^ 2 + z.im ^ 2 := add_le_add hre_sq (le_rfl)
      _ = 2 * z.im ^ 2 := by ring
  have hInv :
      (1 : ℝ) / (2 * z.im ^ 2) ≤ (1 : ℝ) / Complex.normSq (z - 1) :=
    one_div_le_one_div_of_le hnormSq_pos hnormSq_le
  have hz_im_ne : z.im ≠ 0 := ne_of_gt hz_im_pos
  have hLower : (1 : ℝ) / (2 * z.im) ≤ z.im / Complex.normSq (z - 1) := by
    have hMul :
        z.im * ((1 : ℝ) / (2 * z.im ^ 2)) ≤ z.im * ((1 : ℝ) / Complex.normSq (z - 1)) :=
      mul_le_mul_of_nonneg_left hInv (le_of_lt hz_im_pos)
    have h1 : z.im * ((1 : ℝ) / (2 * z.im ^ 2)) = (1 : ℝ) / (2 * z.im) := by
      have hz_im_ne' : (z.im : ℝ) ≠ 0 := hz_im_ne
      -- `field_simp` is faster here than rewriting powers by hand.
      field_simp [hz_im_ne']
    have h2 : z.im * ((1 : ℝ) / Complex.normSq (z - 1)) = z.im / Complex.normSq (z - 1) := by
      simp [div_eq_mul_inv]
    have hMul' : (1 : ℝ) / (2 * z.im) ≤ z.im * ((1 : ℝ) / Complex.normSq (z - 1)) := by
      -- Rewrite the left side using `h1.symm`, then apply `hMul`.
      calc
        (1 : ℝ) / (2 * z.im) = z.im * ((1 : ℝ) / (2 * z.im ^ 2)) := h1.symm
        _ ≤ z.im * ((1 : ℝ) / Complex.normSq (z - 1)) := hMul
    -- Rewrite the right side as a division.
    calc
      (1 : ℝ) / (2 * z.im) ≤ z.im * ((1 : ℝ) / Complex.normSq (z - 1)) := hMul'
      _ = z.im / Complex.normSq (z - 1) := h2
  have hhalf : (1 / 2 : ℝ) < (1 : ℝ) / (2 * z.im) := by
    have hpos : 0 < 2 * z.im := by linarith [hz_im_pos]
    have hlt : 2 * z.im < 2 := by nlinarith [hz_im_lt1]
    simpa using (one_div_lt_one_div_of_lt hpos hlt)
  have hw_half : (1 / 2 : ℝ) < (-1 / (z - 1)).im := by
    have : (1 / 2 : ℝ) < z.im / Complex.normSq (z - 1) := lt_of_lt_of_le hhalf hLower
    -- `(-1/(z-1)).im = z.im / normSq(z-1)`.
    have him : (-1 / (z - 1)).im = z.im / Complex.normSq (z - 1) := by
      simp [div_eq_mul_inv, Complex.inv_im, sub_eq_add_neg]
    simpa [him] using this
  have hw_pos : 0 < (-1 / (z - 1)).im := lt_trans (by norm_num) hw_half
  -- Bound `‖φ₀''(-1/(z-1))‖` by `C₀`.
  have hφ₀'' : ‖φ₀'' (-1 / (z - 1))‖ ≤ (C₀ : ℝ) := by
    let wH : UpperHalfPlane := ⟨-1 / (z - 1), hw_pos⟩
    have hφ₀ : ‖φ₀ wH‖ ≤ (C₀ : ℝ) * Real.exp (-2 * Real.pi * wH.im) := by
      simpa using (hC₀ wH hw_half)
    have hφ₀_eq : φ₀ wH = φ₀'' (-1 / (z - 1)) := by
      simpa [wH] using (φ₀''_def (z := (-1 / (z - 1))) hw_pos).symm
    have hexp : Real.exp (-2 * Real.pi * wH.im) ≤ 1 := by
      have : (-2 * Real.pi * wH.im) ≤ 0 := by
        have hpi : 0 ≤ Real.pi := Real.pi_pos.le
        have hw : 0 ≤ wH.im := (le_of_lt wH.2)
        have hneg : (-2 : ℝ) ≤ 0 := by norm_num
        have h₁ : (-2 : ℝ) * Real.pi ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hpi
        exact mul_nonpos_of_nonpos_of_nonneg h₁ hw
      simpa using (Real.exp_le_one_iff.2 this)
    have hmul :
        (C₀ : ℝ) * Real.exp (-2 * Real.pi * wH.im) ≤ (C₀ : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hexp hC₀_pos.le
    have : ‖φ₀'' (-1 / (z - 1))‖ ≤ (C₀ : ℝ) * Real.exp (-2 * Real.pi * wH.im) := by
      simpa [hφ₀_eq] using hφ₀
    exact this.trans hmul
  have hmain :
      ‖MagicFunction.a.ComplexIntegrands.Φ₃' r z‖ ≤ (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M := by
    have hpow : ‖(z - 1) ^ (2 : ℕ)‖ = (dist z (1 : ℂ)) ^ (2 : ℕ) := by
      simp [dist_eq_norm]
    calc
      ‖MagicFunction.a.ComplexIntegrands.Φ₃' r z‖
          = ‖φ₀'' (-1 / (z - 1))‖ * ‖(z - 1) ^ (2 : ℕ)‖ * expNorm z := by
            simp [MagicFunction.a.ComplexIntegrands.Φ₃', expNorm, mul_left_comm, mul_comm]
      _ ≤ (C₀ : ℝ) * ‖(z - 1) ^ (2 : ℕ)‖ * expNorm z := by
            have hnonneg : 0 ≤ ‖(z - 1) ^ (2 : ℕ)‖ * expNorm z :=
              mul_nonneg (norm_nonneg _) (norm_nonneg _)
            simpa [mul_assoc] using mul_le_mul_of_nonneg_right hφ₀'' hnonneg
      _ ≤ (C₀ : ℝ) * ‖(z - 1) ^ (2 : ℕ)‖ * M := by
            have hnonneg : 0 ≤ (C₀ : ℝ) * ‖(z - 1) ^ (2 : ℕ)‖ :=
              mul_nonneg hC₀_pos.le (norm_nonneg _)
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left hexpZ hnonneg
      _ = (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M := by
            simp [hpow]
  have hpow_small :
      dist ((C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M) (0 : ℝ) < ε := by
    have hzmem : z ∈ Metric.ball (1 : ℂ) δpow := by
      simpa [Metric.mem_ball] using hdist_pow
    exact hδpow hzmem
  have hpow_small' : (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M < ε := by
    have habs : |(C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M| < ε := by
      simpa [Real.dist_eq] using hpow_small
    have hnonneg :
        0 ≤ (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M := by
      have hdist_nonneg : 0 ≤ dist z (1 : ℂ) := dist_nonneg
      have hpow_nonneg : 0 ≤ (dist z (1 : ℂ)) ^ (2 : ℕ) := pow_nonneg hdist_nonneg _
      exact mul_nonneg (mul_nonneg hC₀_pos.le hpow_nonneg) (le_of_lt hMpos)
    simpa [abs_of_nonneg hnonneg] using habs
  have : ‖MagicFunction.a.ComplexIntegrands.Φ₃' r z‖ < ε := lt_of_le_of_lt hmain hpow_small'
  simpa [dist_eq_norm] using this

end Integral_Permutations

end
end MagicFunction.a.Fourier
