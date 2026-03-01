module
public import SpherePacking.MagicFunction.a.IntegralEstimates.I1
public import SpherePacking.MagicFunction.a.Integrability.RealIntegrands
import SpherePacking.MagicFunction.a.IntegralEstimates.I3
import SpherePacking.MagicFunction.PolyFourierCoeffBound

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.Integration.Measure

/-!
# Schwartz decay for `RealIntegrals.I₁'`

This file proves the inverse-power decay estimates needed for the radial profile `RealIntegrals.I₁'`
in the construction of the Schwartz function `a'`.

The proof uses the change-of-variables representation
`MagicFunction.a.IntegralEstimates.I₁.Complete_Change_of_Variables`.

## Main statement
* `decay'`
-/


namespace MagicFunction.a.Schwartz.I1Decay

noncomputable section

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter
open SpherePacking.Integration (μIciOne)

open MagicFunction.a.RealIntegrals
open MagicFunction.a.IntegralEstimates.I₁

def μ : Measure ℝ := μIciOne

def coeff (s : ℝ) : ℂ := (-π : ℂ) * (I + (1 / (s : ℂ)))

def gN (n : ℕ) (r s : ℝ) : ℂ := (coeff s) ^ n * g r s

/--
A convenient constant controlling the bound on `‖φ₀ z‖` for `im z ≥ 1 / 2`, obtained from
`MagicFunction.PolyFourierCoeffBound.norm_φ₀_le`.
-/
public noncomputable def Cφ : ℝ :=
  (MagicFunction.PolyFourierCoeffBound.norm_φ₀_le).choose

/-- The constant `Cφ` is positive. -/
public lemma Cφ_pos : 0 < Cφ :=
  (MagicFunction.PolyFourierCoeffBound.norm_φ₀_le).choose_spec.1

/--
Bound `‖φ₀'' (I * s)‖` for `s ≥ 1` using the Fourier coefficient estimate for `φ₀`.
-/
public lemma norm_φ₀''_le (s : ℝ) (hs : 1 ≤ s) :
    ‖φ₀'' (I * (s : ℂ))‖ ≤ Cφ * rexp (-2 * π * s) := by
  have hs_pos : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hpos : 0 < (I * (s : ℂ)).im := by simpa using hs_pos
  let z : ℍ := ⟨I * (s : ℂ), hpos⟩
  have hz_im : z.im = s := by simp [z, UpperHalfPlane.im]
  have hz_half : (1 / 2 : ℝ) < z.im := by
    have : (1 / 2 : ℝ) < s := lt_of_lt_of_le (by norm_num) hs
    simpa [hz_im] using this
  have hbound := (MagicFunction.PolyFourierCoeffBound.norm_φ₀_le).choose_spec.2 z hz_half
  have hφ₀'' : φ₀'' (I * (s : ℂ)) = φ₀ z := by
    simpa [z] using (φ₀''_def (z := I * (s : ℂ)) hpos)
  simpa [Cφ, hz_im, hφ₀''] using hbound

lemma g_norm_bound (r s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
    ‖g r s‖ ≤ Cφ * rexp (-2 * π * s) * rexp (-π * r / s) := by
  have hs1 : 1 ≤ s := hs
  have hπ : ‖cexp (π * I * r)‖ = (1 : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (norm_exp_ofReal_mul_I (π * r))
  have hnegπ : ‖cexp (-(π * I * r))‖ = (1 : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (norm_exp_ofReal_mul_I (-π * r))
  have hnorm : ‖MagicFunction.a.IntegralEstimates.I₃.g r s‖ = ‖g r s‖ := by
    let A : ℂ := (-I) * φ₀'' (I * s) * (s ^ (-4 : ℤ)) * cexp (-π * r / s)
    have hI3 : MagicFunction.a.IntegralEstimates.I₃.g r s = A * cexp (π * I * r) := by
      simp [MagicFunction.a.IntegralEstimates.I₃.g, A, mul_assoc, mul_left_comm, mul_comm]
    have hI1 : g r s = A * cexp (-π * I * r) := by
      simp [g, A, mul_assoc, mul_left_comm, mul_comm]
    have hnormI3 : ‖MagicFunction.a.IntegralEstimates.I₃.g r s‖ = ‖A‖ := by
      simp [hI3, hπ]
    have hnormI1 : ‖g r s‖ = ‖A‖ := by
      simp [hI1, hnegπ]
    simp [hnormI3, hnormI1]
  have h1 : ‖g r s‖ ≤ ‖φ₀'' (I * (s : ℂ))‖ * rexp (-π * r / s) := by
    simpa [hnorm] using (MagicFunction.a.IntegralEstimates.I₃.I₃'_bounding_aux_1 (r := r) s hs)
  have hφ : ‖φ₀'' (I * (s : ℂ))‖ ≤ Cφ * rexp (-2 * π * s) := norm_φ₀''_le (s := s) hs1
  have : ‖g r s‖ ≤ (Cφ * rexp (-2 * π * s)) * rexp (-π * r / s) := by
    refine h1.trans ?_
    gcongr
  simpa [mul_assoc, mul_left_comm, mul_comm] using this

lemma coeff_norm_le (s : ℝ) (hs : s ∈ Ici (1 : ℝ)) : ‖coeff s‖ ≤ 2 * π := by
  have hs1 : (1 : ℝ) ≤ s := hs
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs1
  have hinv : ‖(1 / (s : ℂ))‖ ≤ 1 := by
    have hsabs : (1 : ℝ) ≤ |s| := by simpa [abs_of_nonneg hs0] using hs1
    have hnorm : ‖(1 / (s : ℂ))‖ = (|s|)⁻¹ := by
      simp [one_div, Complex.norm_real]
    simpa [hnorm] using (inv_le_one_of_one_le₀ hsabs)
  have hpi : ‖(-π : ℂ)‖ = (π : ℝ) := by
    simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]
  calc
    ‖coeff s‖ = ‖(-π : ℂ)‖ * ‖I + (1 / (s : ℂ))‖ := by
      simp [coeff]
    _ = (π : ℝ) * ‖I + (1 / (s : ℂ))‖ := by simp [hpi]
    _ ≤ (π : ℝ) * (‖I‖ + ‖(1 / (s : ℂ))‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (π : ℝ) * (1 + 1) := by
      have hI : ‖(I : ℂ)‖ = (1 : ℝ) := by simp
      have hsum : ‖(I : ℂ)‖ + ‖(1 / (s : ℂ))‖ ≤ (1 : ℝ) + 1 := by
        simpa [hI] using (add_le_add_left hinv ‖(I : ℂ)‖)
      exact mul_le_mul_of_nonneg_left hsum Real.pi_pos.le
    _ = 2 * π := by ring

lemma gN_norm_bound (n : ℕ) (r s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
    ‖gN n r s‖ ≤ (2 * π) ^ n * (Cφ * rexp (-2 * π * s) * rexp (-π * r / s)) := by
  have hcoeff : ‖coeff s‖ ^ n ≤ (2 * π) ^ n :=
    pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le (s := s) hs) n
  have hg : ‖g r s‖ ≤ Cφ * rexp (-2 * π * s) * rexp (-π * r / s) :=
    g_norm_bound (r := r) (s := s) hs
  have hmul :
      ‖coeff s‖ ^ n * ‖g r s‖ ≤ (2 * π) ^ n * (Cφ * rexp (-2 * π * s) * rexp (-π * r / s)) :=
    mul_le_mul hcoeff hg (norm_nonneg _) (by positivity)
  simpa [gN, norm_pow, mul_assoc, mul_left_comm, mul_comm] using hmul

lemma exp_r_mul_coeff (r s : ℝ) :
    cexp ((r : ℂ) * coeff s) =
      cexp ((-π : ℂ) * I * (r : ℂ)) * cexp ((-π : ℂ) * (r : ℂ) / (s : ℂ)) := by
  have harg :
      (r : ℂ) * coeff s = ((-π : ℂ) * I * (r : ℂ)) + ((-π : ℂ) * (r : ℂ) / (s : ℂ)) := by
    simp [coeff, mul_add, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    ring_nf
  simp [harg, Complex.exp_add, mul_assoc]

lemma hasDerivAt_g (r s : ℝ) :
    HasDerivAt (fun r : ℝ ↦ g r s) (coeff s * g r s) r := by
  let A : ℂ := (-I) * φ₀'' (I * (s : ℂ)) * (s ^ (-4 : ℤ) : ℂ)
  simpa [g, A, exp_r_mul_coeff, mul_assoc, mul_left_comm, mul_comm] using
    (SpherePacking.ForMathlib.hasDerivAt_mul_cexp_ofReal_mul_const (a := A) (c := coeff s) (x := r))

lemma hasDerivAt_gN (n : ℕ) (r s : ℝ) :
    HasDerivAt (fun r : ℝ ↦ gN n r s) (gN (n + 1) r s) r := by
  simpa [gN, pow_succ, mul_assoc] using (hasDerivAt_g r s).const_mul (coeff s ^ n)

lemma Φ₆_zero_eq_I_mul_φ₀'' (s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
    MagicFunction.a.RealIntegrands.Φ₆ (r := (0 : ℝ)) s = I * φ₀'' (I * (s : ℂ)) := by
  simp [MagicFunction.a.RealIntegrands.Φ₆, MagicFunction.a.ComplexIntegrands.Φ₆',
    MagicFunction.Parametrisations.z₆'_eq_of_mem hs, mul_comm]

/-- Continuity of `s ↦ φ₀'' (I * s)` on `Ici 1`. -/
public lemma φ₀''_I_mul_continuousOn :
    ContinuousOn (fun s : ℝ ↦ φ₀'' (I * (s : ℂ))) (Ici (1 : ℝ)) := by
  have hΦ :
      ContinuousOn (MagicFunction.a.RealIntegrands.Φ₆ (r := (0 : ℝ))) (Ici (1 : ℝ)) :=
    (MagicFunction.a.RealIntegrands.Φ₆_contDiffOn (r := (0 : ℝ))).continuousOn
  have hΦ' :
      ContinuousOn (fun s : ℝ ↦ (-I) * MagicFunction.a.RealIntegrands.Φ₆ (r := (0 : ℝ)) s)
        (Ici (1 : ℝ)) :=
    continuousOn_const.mul hΦ
  refine hΦ'.congr ?_
  intro s hs
  have hEq := Φ₆_zero_eq_I_mul_φ₀'' (s := s) hs
  have :
      (-I) * MagicFunction.a.RealIntegrands.Φ₆ (r := (0 : ℝ)) s = φ₀'' (I * (s : ℂ)) := by
    calc
      (-I) * MagicFunction.a.RealIntegrands.Φ₆ (r := (0 : ℝ)) s
          = (-I) * (I * φ₀'' (I * (s : ℂ))) := by simp [hEq]
      _ = φ₀'' (I * (s : ℂ)) := by
        calc
          (-I : ℂ) * (I * φ₀'' (I * (s : ℂ))) = ((-I : ℂ) * I) * φ₀'' (I * (s : ℂ)) := by
            simpa [mul_assoc] using
              (mul_assoc (-I : ℂ) I (φ₀'' (I * (s : ℂ)))).symm
          _ = φ₀'' (I * (s : ℂ)) := by simp
  simpa using this.symm

/-- Continuity of `s ↦ (s : ℂ) ^ (-4 : ℤ)` on `Ici 1`. -/
public lemma zpow_neg_four_continuousOn :
    ContinuousOn (fun s : ℝ ↦ (s : ℂ) ^ (-4 : ℤ)) (Ici (1 : ℝ)) := by
  refine (Complex.continuous_ofReal : Continuous fun s : ℝ ↦ (s : ℂ)).continuousOn.zpow₀ (-4 : ℤ) ?_
  intro s hs
  exact Or.inl (by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hs)))

lemma coeff_continuousOn : ContinuousOn coeff (Ici (1 : ℝ)) := by
  have hs0 : ∀ s ∈ Ici (1 : ℝ), (s : ℂ) ≠ 0 := by
    intro s hs
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hs))
  have hcoe : ContinuousOn (fun s : ℝ ↦ (s : ℂ)) (Ici (1 : ℝ)) :=
    (Complex.continuous_ofReal : Continuous fun s : ℝ ↦ (s : ℂ)).continuousOn
  have hinv : ContinuousOn (fun s : ℝ ↦ (s : ℂ)⁻¹) (Ici (1 : ℝ)) :=
    ContinuousOn.inv₀ hcoe hs0
  have h :
      ContinuousOn (fun s : ℝ ↦ (-π : ℂ) * ((I : ℂ) + (s : ℂ)⁻¹)) (Ici (1 : ℝ)) :=
    continuousOn_const.mul (continuousOn_const.add hinv)
  refine h.congr ?_
  intro s hs
  simp [coeff, one_div]

lemma exp_div_continuousOn (r : ℝ) :
    ContinuousOn (fun s : ℝ ↦ cexp ((-π : ℂ) * (r : ℂ) / (s : ℂ))) (Ici (1 : ℝ)) := by
  have hs0 : ∀ s ∈ Ici (1 : ℝ), (s : ℂ) ≠ 0 := by
    intro s hs
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hs))
  have hcoe : ContinuousOn (fun s : ℝ ↦ (s : ℂ)) (Ici (1 : ℝ)) :=
    (Complex.continuous_ofReal : Continuous fun s : ℝ ↦ (s : ℂ)).continuousOn
  have hinv : ContinuousOn (fun s : ℝ ↦ (s : ℂ)⁻¹) (Ici (1 : ℝ)) :=
    ContinuousOn.inv₀ hcoe hs0
  have hinner : ContinuousOn (fun s : ℝ ↦ ((-π : ℂ) * (r : ℂ)) * (s : ℂ)⁻¹) (Ici (1 : ℝ)) :=
    continuousOn_const.mul hinv
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hinner.cexp

lemma g_continuousOn (r : ℝ) : ContinuousOn (fun s : ℝ ↦ g r s) (Ici (1 : ℝ)) := by
  let h : ℝ → ℂ :=
    fun s : ℝ ↦
      ((((-I : ℂ) * φ₀'' (I * (s : ℂ))) * ((s : ℂ) ^ (-4 : ℤ))) *
            cexp ((-π : ℂ) * I * (r : ℂ))) *
          cexp ((-π : ℂ) * (r : ℂ) / (s : ℂ))
  have hconstI : ContinuousOn (fun _ : ℝ ↦ (-I : ℂ)) (Ici (1 : ℝ)) := continuousOn_const
  have hconstExp :
      ContinuousOn (fun _ : ℝ ↦ cexp ((-π : ℂ) * I * (r : ℂ))) (Ici (1 : ℝ)) := continuousOn_const
  have hh : ContinuousOn h (Ici (1 : ℝ)) := by
    have h1 : ContinuousOn (fun s : ℝ ↦ (-I : ℂ) * φ₀'' (I * (s : ℂ))) (Ici (1 : ℝ)) :=
      hconstI.mul φ₀''_I_mul_continuousOn
    have h2 :
        ContinuousOn (fun s : ℝ ↦ ((-I : ℂ) * φ₀'' (I * (s : ℂ))) * ((s : ℂ) ^ (-4 : ℤ)))
          (Ici (1 : ℝ)) := h1.mul zpow_neg_four_continuousOn
    have h3 :
        ContinuousOn
            (fun s : ℝ ↦
              (((-I : ℂ) * φ₀'' (I * (s : ℂ))) * ((s : ℂ) ^ (-4 : ℤ))) *
                cexp ((-π : ℂ) * I * (r : ℂ)))
            (Ici (1 : ℝ)) := h2.mul hconstExp
    dsimp [h]
    exact h3.mul (exp_div_continuousOn (r := r))
  assumption

lemma gN_measurable (n : ℕ) (r : ℝ) : AEStronglyMeasurable (gN n r) μ := by
  have h : ContinuousOn (fun s : ℝ ↦ gN n r s) (Ici (1 : ℝ)) := by
    simpa [gN] using (coeff_continuousOn.pow n).mul (g_continuousOn (r := r))
  simpa [μ, SpherePacking.Integration.μIciOne] using h.aestronglyMeasurable measurableSet_Ici

lemma integrable_exp_neg_two_pi : Integrable (fun s : ℝ ↦ rexp (-(2 * π) * s)) μ := by
  simpa [IntegrableOn, SpherePacking.Integration.μIciOne, mul_assoc, mul_left_comm, mul_comm] using
    (MagicFunction.a.IntegralEstimates.I₃.Bound_integrableOn (r := (0 : ℝ)) (C₀ := (1 : ℝ)))

lemma exp_neg_pi_mul_div_le_exp_pi_abs (r s : ℝ) (hs : 1 ≤ s) :
    rexp (-π * r / s) ≤ rexp (π * |r|) := by
  have hs0 : 0 ≤ s := (zero_le_one.trans hs)
  have hle1 : (-r / s : ℝ) ≤ |r| / s := by
    simpa [abs_div, abs_neg, abs_of_nonneg hs0] using (le_abs_self (-r / s))
  have hle : (-r / s : ℝ) ≤ |r| := hle1.trans (div_le_self (abs_nonneg r) hs)
  have h := mul_le_mul_of_nonneg_left hle Real.pi_pos.le
  exact Real.exp_le_exp.2 <| by
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h

lemma integrable_gN (n : ℕ) (r : ℝ) : Integrable (gN n r) μ := by
  let K : ℝ := (2 * π) ^ n * (Cφ * rexp (π * |r|))
  have hK : Integrable (fun s : ℝ ↦ K * rexp (-(2 * π) * s)) μ :=
    (integrable_exp_neg_two_pi.const_mul K)
  refine Integrable.mono' hK (gN_measurable (n := n) (r := r)) ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
  intro s hs
  have hExp : rexp (-π * r / s) ≤ rexp (π * |r|) :=
    exp_neg_pi_mul_div_le_exp_pi_abs (r := r) (s := s) hs
  have hgn : ‖gN n r s‖ ≤ (2 * π) ^ n * (Cφ * rexp (-2 * π * s) * rexp (-π * r / s)) :=
    gN_norm_bound (n := n) (r := r) (s := s) hs
  refine hgn.trans ?_
  have hcoef0 : 0 ≤ (2 * π) ^ n * (Cφ * rexp (-2 * π * s)) := by
    have : 0 ≤ (2 * π : ℝ) := by positivity
    exact mul_nonneg (pow_nonneg this n) (mul_nonneg Cφ_pos.le (Real.exp_pos _).le)
  have hmul := mul_le_mul_of_nonneg_left hExp hcoef0
  grind only

lemma hasDerivAt_integral_gN (n : ℕ) (r₀ : ℝ) :
    HasDerivAt (fun r : ℝ ↦ ∫ s, gN n r s ∂μ) (∫ s, gN (n + 1) r₀ s ∂μ) r₀ := by
  let R : ℝ := |r₀| + 1
  let bound : ℝ → ℝ := fun s ↦ (2 * π) ^ (n + 1) * (Cφ * rexp (π * R)) * rexp (-(2 * π) * s)
  have hF_meas : ∀ᶠ r in 𝓝 r₀, AEStronglyMeasurable (gN n r) μ :=
    Filter.Eventually.of_forall fun r => gN_measurable (n := n) (r := r)
  have hF_int : Integrable (gN n r₀) μ := integrable_gN (n := n) (r := r₀)
  have hF'_meas : AEStronglyMeasurable (gN (n + 1) r₀) μ :=
    gN_measurable (n := n + 1) (r := r₀)
  have hbound_int : Integrable bound μ := by
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      (integrable_exp_neg_two_pi.const_mul ((2 * π) ^ (n + 1) * (Cφ * rexp (π * R))))
  have h_bound :
      ∀ᵐ s ∂μ, ∀ r ∈ Metric.ball r₀ (1 : ℝ), ‖gN (n + 1) r s‖ ≤ bound s := by
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
    intro s hs r hr
    have hrabs : |r| ≤ R := by
      exact SpherePacking.ForMathlib.abs_le_abs_add_of_mem_ball hr
    have hExp : rexp (-π * r / s) ≤ rexp (π * R) := by
      refine (exp_neg_pi_mul_div_le_exp_pi_abs (r := r) (s := s) hs).trans ?_
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hrabs Real.pi_pos.le)
    have hgn : ‖gN (n + 1) r s‖ ≤
        (2 * π) ^ (n + 1) * (Cφ * rexp (-2 * π * s) * rexp (-π * r / s)) :=
      gN_norm_bound (n := n + 1) (r := r) (s := s) hs
    refine hgn.trans ?_
    have hcoef0 : 0 ≤ (2 * π) ^ (n + 1) * (Cφ * rexp (-2 * π * s)) := by
      have : 0 ≤ (2 * π : ℝ) := by positivity
      exact mul_nonneg (pow_nonneg this (n + 1)) (mul_nonneg Cφ_pos.le (Real.exp_pos _).le)
    have hmul := mul_le_mul_of_nonneg_left hExp hcoef0
    grind only
  have h_diff :
      ∀ᵐ s ∂μ, ∀ r ∈ Metric.ball r₀ (1 : ℝ),
        HasDerivAt (fun x : ℝ ↦ gN n x s) (gN (n + 1) r s) r := by
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
    intro s _ r _
    exact hasDerivAt_gN (n := n) (r := r) (s := s)
  simpa [μ, SpherePacking.Integration.μIciOne] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := fun r s ↦ gN n r s) (x₀ := r₀) (s := Metric.ball r₀ (1 : ℝ))
      (hs := by simpa using Metric.ball_mem_nhds r₀ (by norm_num))
      (hF_meas := hF_meas) (hF_int := hF_int) (hF'_meas := hF'_meas)
      (h_bound := h_bound) (bound_integrable := hbound_int) (h_diff := h_diff)).2
lemma iteratedDeriv_eq_integral_gN (n : ℕ) :
    iteratedDeriv n I₁' = fun r : ℝ ↦ ∫ s, gN n r s ∂μ := by
  induction n with
  | zero =>
      funext r
      simp [iteratedDeriv_zero, gN, μ, μIciOne, Complete_Change_of_Variables]
  | succ n ih =>
      funext r
      simpa [iteratedDeriv_succ, ih] using (hasDerivAt_integral_gN (n := n) (r₀ := r)).deriv

lemma pow_mul_exp_neg_bounded (k : ℕ) :
    ∃ C, ∀ u : ℝ, 0 ≤ u → u ^ k * rexp (-u) ≤ C := by
  let f : ℝ → ℝ := fun u ↦ u ^ k * rexp (-u)
  have hlim : Tendsto f atTop (𝓝 0) := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  have h_event : ∀ᶠ u in atTop, f u ≤ 1 := by
    exact (hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ hu => le_of_lt hu
  rcases (Filter.eventually_atTop.1 h_event) with ⟨N, hN⟩
  let N0 : ℝ := max N 0
  have hN0 : ∀ u ≥ N0, f u ≤ 1 := by
    intro u hu
    exact hN u (le_trans (le_max_left N 0) hu)
  have hf_cont : Continuous f := by
    dsimp [f]
    fun_prop
  have hcompact : IsCompact (Set.Icc (0 : ℝ) N0) := isCompact_Icc
  have hne : (Set.Icc (0 : ℝ) N0).Nonempty := ⟨0, by simp [N0]⟩
  obtain ⟨u0, hu0, hu0max⟩ := hcompact.exists_isMaxOn hne (hf_cont.continuousOn)
  refine ⟨max 1 (f u0), ?_⟩
  intro u hu
  by_cases huN : u ≤ N0
  · have huIcc : u ∈ Set.Icc (0 : ℝ) N0 := ⟨hu, huN⟩
    exact (hu0max huIcc).trans (le_max_right _ _)
  · have huge : N0 ≤ u := le_of_not_ge huN
    exact (hN0 u huge).trans (le_max_left _ _)

lemma norm_iteratedDeriv_le (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n I₁' x‖ ≤
      ∫ s in Ici (1 : ℝ), (2 * π) ^ n * (Cφ * rexp (-2 * π * s) * rexp (-π * x / s)) := by
  have hreprx : iteratedDeriv n I₁' x = ∫ s, gN n x s ∂μ := by
    simp [iteratedDeriv_eq_integral_gN (n := n)]
  have hL : IntegrableOn (fun s : ℝ ↦ ‖gN n x s‖) (Ici (1 : ℝ)) volume := by
    simpa [IntegrableOn, μIciOne] using
      (integrable_gN (n := n) (r := x)).norm
  have hR : IntegrableOn
      (fun s : ℝ ↦ (2 * π) ^ n * (Cφ * rexp (-2 * π * s) * rexp (-π * x / s)))
      (Ici (1 : ℝ)) volume := by
    have h0' :
        IntegrableOn (fun s : ℝ ↦ Cφ * rexp (-2 * π * s) *
          rexp (-π * x / s)) (Ici (1 : ℝ)) volume := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (MagicFunction.a.IntegralEstimates.I₃.Bound_integrableOn (r := x) (C₀ := Cφ))
    simpa [mul_assoc, mul_left_comm, mul_comm] using h0'.const_mul ((2 * π) ^ n)
  have hmono :
      (∫ s in Ici (1 : ℝ), ‖gN n x s‖) ≤
        ∫ s in Ici (1 : ℝ), (2 * π) ^ n * (Cφ * rexp (-2 * π * s) * rexp (-π * x / s)) :=
    setIntegral_mono_on hL hR measurableSet_Ici
    (fun s hs => gN_norm_bound (n := n) (r := x) (s := s) hs)
  calc
    ‖iteratedDeriv n I₁' x‖ = ‖∫ s, gN n x s ∂μ‖ := by simp [hreprx]
    _ ≤ ∫ s, ‖gN n x s‖ ∂μ := norm_integral_le_integral_norm (gN n x)
    _ = ∫ s in Ici (1 : ℝ), ‖gN n x s‖ := by simp [μ, SpherePacking.Integration.μIciOne]
    _ ≤ ∫ s in Ici (1 : ℝ), (2 * π) ^ n * (Cφ * rexp (-2 * π * s) * rexp (-π * x / s)) := hmono

lemma xpow_mul_exp_neg_pi_div_le (k : ℕ) {x s : ℝ} (hx : 0 ≤ x) (hs : 1 ≤ s)
    {Cpow : ℝ} (hCpow : ∀ u : ℝ, 0 ≤ u → u ^ k * rexp (-u) ≤ Cpow) :
    x ^ k * rexp (-π * x / s) ≤ (π ^ k)⁻¹ * Cpow * s ^ k := by
  have hs0 : s ≠ 0 := (lt_of_lt_of_le (by norm_num) hs).ne'
  have hpi0 : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  set u : ℝ := (π * x) / s
  have hu0 : 0 ≤ u := div_nonneg (by positivity) (zero_le_one.trans hs)
  have hu : u ^ k * rexp (-u) ≤ Cpow := hCpow u hu0
  have hu_mul : u * s = π * x := by
    exact div_mul_cancel₀ (π * x) hs0
  have hx' : x = u * s / π :=
    CancelDenoms.cancel_factors_eq_div (id (Eq.symm hu_mul)) hpi0
  have hxpow : x ^ k = (π ^ k)⁻¹ * s ^ k * u ^ k := by
    simp [hx', mul_pow, div_eq_mul_inv, inv_pow, mul_assoc, mul_left_comm, mul_comm]
  have hexp : rexp (-π * x / s) = rexp (-u) := by
    have hxarg : (-π * x / s : ℝ) = -u := by
      ring
    simpa using congrArg rexp hxarg
  calc
    x ^ k * rexp (-π * x / s) = x ^ k * rexp (-u) := by
      simpa using congrArg (fun t => x ^ k * t) hexp
    _ = ((π ^ k)⁻¹ * s ^ k * u ^ k) * rexp (-u) := by simp [hxpow]
    _ = (π ^ k)⁻¹ * s ^ k * (u ^ k * rexp (-u)) := by ac_rfl
    _ ≤ (π ^ k)⁻¹ * s ^ k * Cpow := by gcongr
    _ = (π ^ k)⁻¹ * Cpow * s ^ k := by ring

lemma xpow_integral_le_of_Cpow (k : ℕ) {Cpow : ℝ}
    (hCpow : ∀ u : ℝ, 0 ≤ u → u ^ k * rexp (-u) ≤ Cpow) :
    ∀ x : ℝ, 0 ≤ x →
      x ^ k * (∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * x / s)) ≤
        ((π ^ k)⁻¹ * Cpow) * (∫ s in Ici (1 : ℝ), s ^ k * rexp (-2 * π * s)) := by
  intro x hx
  have hb : 0 < (2 * π : ℝ) := by positivity
  have hInt :
      IntegrableOn (fun s : ℝ ↦ s ^ k * rexp (-2 * π * s)) (Ici (1 : ℝ)) volume := by
    simpa [mul_assoc] using
      (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := k) (b := (2 * π)) hb)
  let f : ℝ → ℝ := fun s ↦ x ^ k * (rexp (-2 * π * s) * rexp (-π * x / s))
  let g : ℝ → ℝ := fun s ↦ ((π ^ k)⁻¹ * Cpow) * (s ^ k * rexp (-2 * π * s))
  have hf_int : IntegrableOn f (Ici (1 : ℝ)) volume := by
    have hB := MagicFunction.a.IntegralEstimates.I₃.Bound_integrableOn (r := x) (C₀ := (1 : ℝ))
    simpa [f, mul_assoc, mul_left_comm, mul_comm] using
      hB.const_mul (x ^ k)
  have hg_int : IntegrableOn g (Ici (1 : ℝ)) volume := by
    simpa [g, mul_assoc, mul_left_comm, mul_comm] using (hInt.const_mul ((π ^ k)⁻¹ * Cpow))
  have hmono : ∀ s ∈ Ici (1 : ℝ), f s ≤ g s := by
    intro s hs
    have hpt :=
      xpow_mul_exp_neg_pi_div_le (k := k) (x := x) (s := s) hx hs (Cpow := Cpow) hCpow
    calc
      f s = rexp (-2 * π * s) * (x ^ k * rexp (-π * x / s)) := by
        simp [f, mul_assoc, mul_comm]
      _ ≤ rexp (-2 * π * s) * (((π ^ k)⁻¹ * Cpow) * s ^ k) := by gcongr
      _ = g s := by
        simp [g, mul_assoc, mul_left_comm, mul_comm]
  have hset := setIntegral_mono_on hf_int hg_int measurableSet_Ici hmono
  -- pull constants out of the integrals to match the desired shape
  have hf' :
      (∫ s in Ici (1 : ℝ), f s) = x ^ k * (∫ s in Ici (1 : ℝ),
        rexp (-2 * π * s) * rexp (-π * x / s)) :=
    integral_const_mul (x ^ k) fun a => rexp (-2 * π * a) * rexp (-π * x / a)
  have hg' :
      (∫ s in Ici (1 : ℝ), g s) = ((π ^ k)⁻¹ * Cpow) * (∫ s in Ici (1 : ℝ),
        s ^ k * rexp (-2 * π * s)) := by
    -- pull out the constant factor
    exact integral_const_mul ((π ^ k)⁻¹ * Cpow) fun a => a ^ k * rexp (-2 * π * a)
  simpa [hf', hg', mul_assoc, mul_left_comm, mul_comm] using hset

/--
Schwartz-style decay estimate for `RealIntegrals.I₁'`.

The prime in the name indicates that this is a statement about the auxiliary integral `I₁'`.
-/
public theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₁' x‖ ≤ C := by
  intro k n
  obtain ⟨Cpow, hCpow⟩ := pow_mul_exp_neg_bounded (k := k)
  let I : ℝ := ∫ s in Ici (1 : ℝ), s ^ k * rexp (-2 * π * s)
  let C : ℝ := (2 * π) ^ n * (Cφ * ((π ^ k)⁻¹ * Cpow) * I)
  refine ⟨C, ?_⟩
  intro x hx
  have hFDeriv :
      ‖iteratedFDeriv ℝ n I₁' x‖ = ‖iteratedDeriv n I₁' x‖ := by
    simpa using
      (norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := n) (f := I₁') (x := x))
  have hxpow :
      x ^ k * (∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * x / s)) ≤
        ((π ^ k)⁻¹ * Cpow) * I :=
    xpow_integral_le_of_Cpow (k := k) (Cpow := Cpow) hCpow x hx
  have hmult : 0 ≤ (2 * π) ^ n * Cφ := mul_nonneg (by positivity) Cφ_pos.le
  have hIntConst :
      (∫ s in Ici (1 : ℝ), (2 * π) ^ n * (Cφ * rexp (-2 * π * s) * rexp (-π * x / s))) =
        ((2 * π) ^ n * Cφ) * (∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * x / s)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ).restrict (Ici (1 : ℝ)))
        ((2 * π) ^ n * Cφ) (fun s : ℝ ↦ rexp (-2 * π * s) * rexp (-π * x / s)))
  have hxk0 : 0 ≤ x ^ k := by positivity
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₁' x‖ = x ^ k * ‖iteratedDeriv n I₁' x‖ := by
      simp [Real.norm_of_nonneg hx, hFDeriv]
    _ ≤ x ^ k * (∫ s in Ici (1:ℝ), (2*π) ^ n * (Cφ * rexp (-2*π*s) * rexp (-π*x/s))) :=
      mul_le_mul_of_nonneg_left (norm_iteratedDeriv_le (n := n) (x := x)) hxk0
    _ = x ^ k * (((2*π) ^ n * Cφ) * (∫ s in Ici (1:ℝ), rexp (-2*π*s) * rexp (-π*x/s))) := by
      simpa using congrArg (fun t ↦ x ^ k * t) hIntConst
    _ = ((2*π) ^ n * Cφ) * (x ^ k * (∫ s in Ici (1:ℝ), rexp (-2*π*s) * rexp (-π*x/s))) := by
      ring
    _ ≤ ((2 * π) ^ n * Cφ) * (((π ^ k)⁻¹ * Cpow) * I) :=
      mul_le_mul_of_nonneg_left hxpow hmult
    _ = C := by simp [C, I, mul_assoc, mul_left_comm, mul_comm]

end

end MagicFunction.a.Schwartz.I1Decay
