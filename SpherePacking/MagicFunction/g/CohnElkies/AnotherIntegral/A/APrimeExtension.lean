module
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
public import SpherePacking.MagicFunction.a.IntegralEstimates.I2
public import SpherePacking.MagicFunction.a.IntegralEstimates.I4
public import SpherePacking.Basic.Domains.RightHalfPlane
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral


/-!
# Complex analytic extension of `a'` (`aPrimeC`)

This file defines complexified integrals `I₁'C`, ..., `I₆'C` and their sum `aPrimeC`, which extends
the real function `a'`. We show that `aPrimeC` restricts to `a'` on real parameters and is analytic
on the right half-plane.

## Main definition
* `aPrimeC`

## Main statements
* `aPrimeC_ofReal`
* `aPrimeC_analyticOnNhd`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Topology Interval UpperHalfPlane

open MeasureTheory Real Complex Filter
open SpherePacking intervalIntegral
open MagicFunction.a.RealIntegrals

noncomputable section


/-! Complexified pieces `Iᵢ'C`. -/

def I₁'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (-Complex.I) * φ₀'' (-1 / ((Complex.I : ℂ) * (t : ℂ))) * (t ^ (2 : ℕ) : ℝ) *
      Complex.exp (-π * (Complex.I : ℂ) * u) * Complex.exp (-π * u * (t : ℂ))

def I₂'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / ((t : ℂ) + (Complex.I : ℂ))) * (((t : ℂ) + (Complex.I : ℂ)) ^ (2 : ℕ)) *
      Complex.exp (-π * (Complex.I : ℂ) * u) *
      Complex.exp (π * (Complex.I : ℂ) * u * (t : ℂ)) *
      Complex.exp (-π * u)

def I₃'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (-Complex.I) * φ₀'' (-1 / ((Complex.I : ℂ) * (t : ℂ))) * (t ^ (2 : ℕ) : ℝ) *
      Complex.exp (π * (Complex.I : ℂ) * u) * Complex.exp (-π * u * (t : ℂ))

def I₄'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (-1 : ℂ) * φ₀'' (-1 / (-(t : ℂ) + (Complex.I : ℂ))) *
      ((-(t : ℂ) + (Complex.I : ℂ)) ^ (2 : ℕ)) *
      Complex.exp (π * (Complex.I : ℂ) * u) *
      Complex.exp (-π * (Complex.I : ℂ) * u * (t : ℂ)) *
      Complex.exp (-π * u)

def I₅'C (u : ℂ) : ℂ :=
  -2 * ∫ t in (0 : ℝ)..1,
    (-Complex.I) * φ₀'' (-1 / ((Complex.I : ℂ) * (t : ℂ))) * (t ^ (2 : ℕ) : ℝ) *
      Complex.exp (-π * u * (t : ℂ))

def I₆'C (u : ℂ) : ℂ :=
  2 * ∫ t in Set.Ici (1 : ℝ),
    (Complex.I : ℂ) * φ₀'' ((Complex.I : ℂ) * (t : ℂ)) * Complex.exp (-π * u * (t : ℂ))

/-- Complex-parameter extension of `a'`, defined as the sum of the complexified integral pieces.

This is analytic on the right half-plane and restricts to `a'` on `ℝ`. -/
public def aPrimeC (u : ℂ) : ℂ :=
  I₁'C u + I₂'C u + I₃'C u + I₄'C u + I₅'C u + I₆'C u

/-! Restriction to real parameters. -/

@[simp] lemma I₁'C_ofReal (u : ℝ) : I₁'C (u : ℂ) = I₁' u := by
  simp [I₁'C, MagicFunction.a.RadialFunctions.I₁'_eq]

@[simp] lemma I₂'C_ofReal (u : ℝ) : I₂'C (u : ℂ) = I₂' u := by
  simp [I₂'C, MagicFunction.a.RadialFunctions.I₂'_eq]

@[simp] lemma I₃'C_ofReal (u : ℝ) : I₃'C (u : ℂ) = I₃' u := by
  simp [I₃'C, MagicFunction.a.RadialFunctions.I₃'_eq]

@[simp] lemma I₄'C_ofReal (u : ℝ) : I₄'C (u : ℂ) = I₄' u := by
  simp [I₄'C, MagicFunction.a.RadialFunctions.I₄'_eq]

@[simp] lemma I₅'C_ofReal (u : ℝ) : I₅'C (u : ℂ) = I₅' u := by
  simp [I₅'C, MagicFunction.a.RadialFunctions.I₅'_eq]

@[simp] lemma I₆'C_ofReal (u : ℝ) : I₆'C (u : ℂ) = I₆' u := by
  simp [I₆'C, MagicFunction.a.RadialFunctions.I₆'_eq]

/-- Restriction of `aPrimeC` to real parameters recovers `a'`. -/
public lemma aPrimeC_ofReal (u : ℝ) : aPrimeC (u : ℂ) = a' u := by
  simp [aPrimeC, MagicFunction.a.RealIntegrals.a']

/-! Analyticity on the right half-plane. -/
/-!
### Differentiability of the finite-interval pieces

We rewrite each `Iᵢ'C` (`i = 1, ..., 5`) into the form
`u ↦ ∫ t, base t * exp (u * k t)` and apply `differentiableAt_intervalIntegral_mul_exp`.
-/

lemma norm_φ₀''_le_of_half_lt {C₀ : ℝ}
    (hC₀_nonneg : 0 ≤ C₀)
    (hC₀ : ∀ z : ℍ, 1 / 2 < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    {z : ℂ} (hzpos : 0 < z.im) (hzhalf : 1 / 2 < z.im) :
    ‖φ₀'' z‖ ≤ C₀ := by
  have hexp : Real.exp (-2 * π * z.im) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, hzpos.le])
  refine (show ‖φ₀'' z‖ ≤ C₀ * Real.exp (-2 * π * z.im) from ?_).trans
    (mul_le_of_le_one_right hC₀_nonneg hexp)
  simpa [φ₀''_def hzpos] using hC₀ ⟨z, hzpos⟩ (by simpa [UpperHalfPlane.im] using hzhalf)

def arg₁ (t : ℝ) : ℂ := (Complex.I : ℂ) / (t : ℂ)

lemma neg_one_div_I_mul_eq_arg₁ (t : ℝ) :
    (-1 : ℂ) / ((Complex.I : ℂ) * (t : ℂ)) = arg₁ t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [arg₁]
  · have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have h : (-1 : ℂ) / ((Complex.I : ℂ) * (t : ℂ)) = (Complex.I : ℂ) / (t : ℂ) := by
      field_simp [ht', Complex.I_ne_zero]
      simp [Complex.I_sq]
    simpa [arg₁] using h

def base₁ (t : ℝ) : ℂ :=
  (-Complex.I) * φ₀'' (arg₁ t) * (t ^ (2 : ℕ) : ℝ)

def k₁ (t : ℝ) : ℂ := (-π * (Complex.I : ℂ)) + (-π * (t : ℂ))
def k₃ (t : ℝ) : ℂ := (π * (Complex.I : ℂ)) + (-π * (t : ℂ))
def k₅ (t : ℝ) : ℂ := (-π * (t : ℂ))

lemma I₁'C_eq (u : ℂ) :
    I₁'C u = ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k₁ t) :=
  intervalIntegral.integral_congr fun t _ => by
    simp [base₁, k₁, neg_one_div_I_mul_eq_arg₁, mul_add, Complex.exp_add,
      mul_assoc, mul_left_comm, mul_comm]

lemma I₃'C_eq (u : ℂ) :
    I₃'C u = ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k₃ t) :=
  intervalIntegral.integral_congr fun t _ => by
    simp [base₁, k₃, neg_one_div_I_mul_eq_arg₁, mul_add, Complex.exp_add,
      mul_assoc, mul_left_comm, mul_comm]

lemma I₅'C_eq (u : ℂ) :
    I₅'C u = -2 * ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k₅ t) :=
  congrArg (fun x : ℂ => -2 * x) <| intervalIntegral.integral_congr fun t _ => by
    simp [base₁, k₅, neg_one_div_I_mul_eq_arg₁, mul_left_comm, mul_comm]

lemma base₁_continuousOn : ContinuousOn base₁ (Ι (0 : ℝ) 1) := by
  have hden0 : ∀ t ∈ Ι (0 : ℝ) 1, (t : ℂ) ≠ 0 := fun t ht => by
    exact_mod_cast (by simpa using ht.1 : (0 : ℝ) < t).ne'
  have hcontArg : ContinuousOn arg₁ (Ι (0 : ℝ) 1) :=
    continuousOn_const.div (by fun_prop) hden0
  have hmaps : Set.MapsTo arg₁ (Ι (0 : ℝ) 1) UpperHalfPlane.upperHalfPlaneSet := fun t ht => by
    simpa [UpperHalfPlane.upperHalfPlaneSet, arg₁] using inv_pos.2 (by simpa using ht.1 : (0:ℝ) < t)
  exact (continuousOn_const.mul
    ((MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn).comp hcontArg hmaps)).mul
      (by fun_prop)

lemma base₁_bound :
    ∃ C₀ > 0, ∀ t ∈ Ι (0 : ℝ) 1, ‖base₁ t‖ ≤ C₀ := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun t ht => ?_⟩
  have ht0 : 0 < t := by simpa using ht.1
  have ht1 : t ≤ 1 := by simpa using ht.2
  have hzpos : 0 < (arg₁ t).im := by simpa [arg₁] using inv_pos.2 ht0
  have hzhalf : (1 / 2 : ℝ) < (arg₁ t).im := by
    simpa [arg₁] using lt_of_lt_of_le (by norm_num : (1/2:ℝ) < 1) (one_le_inv_iff₀.2 ⟨ht0, ht1⟩)
  have ht2 : ‖(t ^ (2 : ℕ) : ℝ)‖ ≤ 1 := by
    have : |t| ^ (2 : ℕ) ≤ (1 : ℝ) :=
      pow_le_one₀ (abs_nonneg t) (by simpa [abs_of_nonneg ht0.le] using ht1)
    simpa [Real.norm_eq_abs, abs_pow] using this
  calc ‖base₁ t‖
      = ‖φ₀'' (arg₁ t)‖ * ‖(t ^ (2 : ℕ) : ℝ)‖ := by simp [base₁]
    _ ≤ C₀ * 1 := mul_le_mul (norm_φ₀''_le_of_half_lt hC₀_pos.le hC₀ hzpos hzhalf) ht2
        (norm_nonneg _) hC₀_pos.le
    _ = C₀ := mul_one _

private lemma norm_of_mem_uIoc_le_one {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) : ‖(t : ℂ)‖ ≤ 1 := by
  simpa [Complex.norm_real, abs_of_nonneg (by simpa using ht.1 : (0:ℝ) < t).le] using ht.2

private lemma norm_neg_pi_mul_t_le {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) :
    ‖(-π : ℂ) * (t : ℂ)‖ ≤ Real.pi := by
  have : ‖(-π : ℂ) * (t : ℂ)‖ = Real.pi * ‖(t : ℂ)‖ := by
    simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]
  nlinarith [Real.pi_pos, norm_of_mem_uIoc_le_one ht]

private lemma norm_sign_pi_I_eq_pi {s : ℝ} (hs : |s| = 1) :
    ‖(s * π : ℂ) * (Complex.I : ℂ)‖ = Real.pi := by
  simp [Complex.norm_real, hs, abs_of_nonneg Real.pi_pos.le]

private lemma norm_sign_pi_I_mul_t_le {s : ℝ} (hs : |s| = 1) {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) :
    ‖(s * π : ℂ) * (Complex.I : ℂ) * (t : ℂ)‖ ≤ Real.pi := by
  have h : ‖(s * π : ℂ) * (Complex.I : ℂ) * (t : ℂ)‖ = Real.pi * ‖(t : ℂ)‖ := by
    simpa [mul_assoc] using congrArg (· * ‖(t : ℂ)‖) (norm_sign_pi_I_eq_pi hs)
  nlinarith [Real.pi_pos, norm_of_mem_uIoc_le_one ht]

/-- Shared bound for `k₁` and `k₃`: `‖±π * I + (-π * t)‖ ≤ 2π`. -/
private lemma k_bound_two_pi {s : ℝ} (hs : |s| = 1) (t : ℝ) (ht : t ∈ Ι (0 : ℝ) 1) :
    ‖(s * π : ℂ) * (Complex.I : ℂ) + (-π * (t : ℂ))‖ ≤ (2 * Real.pi) := by
  have := (norm_add_le _ _).trans
    (add_le_add (norm_sign_pi_I_eq_pi hs).le (norm_neg_pi_mul_t_le ht))
  linarith

lemma k₁_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k₁ t‖ ≤ (2 * Real.pi) := fun t ht => by
  simpa [k₁, show ((-1 : ℝ) * Real.pi : ℂ) = (-π : ℂ) by push_cast; ring] using
    k_bound_two_pi (s := -1) (by norm_num) t ht

lemma k₃_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k₃ t‖ ≤ (2 * Real.pi) := fun t ht => by
  simpa [k₃, show ((1 : ℝ) * Real.pi : ℂ) = (π : ℂ) by push_cast; ring] using
    k_bound_two_pi (s := 1) (by norm_num) t ht

lemma k₅_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k₅ t‖ ≤ Real.pi := fun t ht => by
  simpa [k₅] using norm_neg_pi_mul_t_le ht

/-- Shared wrapper: `u ↦ ∫ t in 0..1, base₁ t * exp (u * k t)` is differentiable at `u0`. -/
private lemma base₁_integral_differentiableAt {k : ℝ → ℂ} (u0 : ℂ) (K : ℝ)
    (hk : ContinuousOn k (Ι (0 : ℝ) 1)) (hk_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k t‖ ≤ K) :
    DifferentiableAt ℂ
      (fun u : ℂ => ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k t)) u0 := by
  obtain ⟨Cbase, _, hbase_bound⟩ := base₁_bound
  exact differentiableAt_intervalIntegral_mul_exp u0 Cbase K
    base₁_continuousOn hk hbase_bound hk_bound

lemma I₁'C_differentiableAt (u0 : ℂ) : DifferentiableAt ℂ I₁'C u0 := by
  simpa [show I₁'C = _ from funext fun u => I₁'C_eq u] using
    base₁_integral_differentiableAt u0 (2 * Real.pi) (by unfold k₁; fun_prop) k₁_bound

lemma I₃'C_differentiableAt (u0 : ℂ) : DifferentiableAt ℂ I₃'C u0 := by
  simpa [show I₃'C = _ from funext fun u => I₃'C_eq u] using
    base₁_integral_differentiableAt u0 (2 * Real.pi) (by unfold k₃; fun_prop) k₃_bound

lemma I₅'C_differentiableAt (u0 : ℂ) : DifferentiableAt ℂ I₅'C u0 := by
  simpa [show I₅'C = fun u : ℂ => (-2 : ℂ) * _ from funext fun u => by
      simpa [mul_assoc] using I₅'C_eq u, mul_assoc] using
    (base₁_integral_differentiableAt u0 Real.pi (by unfold k₅; fun_prop) k₅_bound).const_mul
      (-2 : ℂ)

lemma I₁'C_differentiableOn : DifferentiableOn ℂ I₁'C rightHalfPlane :=
  fun u _ => (I₁'C_differentiableAt u).differentiableWithinAt

lemma I₃'C_differentiableOn : DifferentiableOn ℂ I₃'C rightHalfPlane :=
  fun u _ => (I₃'C_differentiableAt u).differentiableWithinAt

lemma I₅'C_differentiableOn : DifferentiableOn ℂ I₅'C rightHalfPlane :=
  fun u _ => (I₅'C_differentiableAt u).differentiableWithinAt

/-!
### The remaining finite-interval pieces `I₂'` and `I₄'`
-/

def arg₂ (t : ℝ) : ℂ :=
  (-1 : ℂ) / ((t : ℂ) + (Complex.I : ℂ))

def base₂ (t : ℝ) : ℂ :=
  φ₀'' (arg₂ t) * (((t : ℂ) + (Complex.I : ℂ)) ^ (2 : ℕ))

def k₂ (t : ℝ) : ℂ :=
  (-π * (Complex.I : ℂ)) + (π * (Complex.I : ℂ) * (t : ℂ)) + (-π)

def arg₄ (t : ℝ) : ℂ :=
  (-1 : ℂ) / (-(t : ℂ) + (Complex.I : ℂ))

def base₄ (t : ℝ) : ℂ :=
  (-1 : ℂ) * φ₀'' (arg₄ t) * ((-(t : ℂ) + (Complex.I : ℂ)) ^ (2 : ℕ))

def k₄ (t : ℝ) : ℂ :=
  (π * (Complex.I : ℂ)) + (-π * (Complex.I : ℂ) * (t : ℂ)) + (-π)

lemma I₂'C_eq (u : ℂ) :
    I₂'C u = ∫ t in (0 : ℝ)..1, base₂ t * Complex.exp (u * k₂ t) :=
  intervalIntegral.integral_congr fun t _ => by
    simp [base₂, arg₂, k₂, mul_add, Complex.exp_add, add_assoc,
      mul_assoc, mul_left_comm, mul_comm]

lemma I₄'C_eq (u : ℂ) :
    I₄'C u = ∫ t in (0 : ℝ)..1, base₄ t * Complex.exp (u * k₄ t) :=
  intervalIntegral.integral_congr fun t _ => by
    simp [base₄, arg₄, k₄, mul_add, Complex.exp_add, add_assoc,
      mul_assoc, mul_left_comm, mul_comm]

/-- Shared continuity argument for `base₂` and `base₄`: if `d : ℝ → ℂ` is continuous with
imaginary part `1` (so nonzero), then `t ↦ φ₀'' (-1 / d t) * d t ^ 2` is continuous. -/
private lemma phi_div_pow_continuousOn {d : ℝ → ℂ} (hd : Continuous d)
    (hd_im : ∀ t, (d t).im = 1) :
    ContinuousOn (fun t : ℝ => φ₀'' (-1 / d t) * (d t) ^ (2 : ℕ)) (Ι (0 : ℝ) 1) := by
  have hden0 : ∀ t : ℝ, d t ≠ 0 := fun t ht0 => by
    have : (1 : ℝ) = 0 := by simpa [hd_im] using congrArg Complex.im ht0
    exact one_ne_zero this
  have hmaps :
      Set.MapsTo (fun t => (-1 : ℂ) / d t) (Ι (0 : ℝ) 1) UpperHalfPlane.upperHalfPlaneSet := by
    intro t _
    have him : ((-1 : ℂ) / d t).im = 1 / Complex.normSq (d t) := by
      rw [show ((-1 : ℂ) / d t).im = -(d t)⁻¹.im from by simp [div_eq_mul_inv],
        Complex.inv_im, hd_im]; field_simp
    simpa [UpperHalfPlane.upperHalfPlaneSet, him] using
      one_div_pos.2 (Complex.normSq_pos.2 (hden0 t))
  exact ((MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn).comp
    (continuousOn_const.div hd.continuousOn fun t _ => hden0 t) hmaps).mul (by fun_prop)

/-- Shared bound for `k₂` and `k₄`: `‖±π * I + ∓π * I * t + (-π)‖ ≤ 3π`. -/
private lemma k_bound_three_pi {s₁ s₂ : ℝ} (hs₁ : |s₁| = 1) (hs₂ : |s₂| = 1)
    (t : ℝ) (ht : t ∈ Ι (0 : ℝ) 1) :
    ‖(s₁ * π : ℂ) * (Complex.I : ℂ) + (s₂ * π : ℂ) * (Complex.I : ℂ) * (t : ℂ) + (-π)‖ ≤
      (3 * Real.pi) := by
  have hpi : ‖(-π : ℂ)‖ = Real.pi := by simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]
  have := (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_sign_pi_I_eq_pi hs₁).le
      (norm_sign_pi_I_mul_t_le hs₂ ht))) hpi.le)
  linarith

lemma k₂_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k₂ t‖ ≤ (3 * Real.pi) := fun t ht => by
  simpa [k₂, show ((-1 : ℝ) * Real.pi : ℂ) = (-π : ℂ) by push_cast; ring,
    show ((1 : ℝ) * Real.pi : ℂ) = (π : ℂ) by push_cast; ring] using
    k_bound_three_pi (s₁ := -1) (s₂ := 1) (by norm_num) (by norm_num) t ht

lemma k₄_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k₄ t‖ ≤ (3 * Real.pi) := fun t ht => by
  simpa [k₄, show ((-1 : ℝ) * Real.pi : ℂ) = (-π : ℂ) by push_cast; ring,
    show ((1 : ℝ) * Real.pi : ℂ) = (π : ℂ) by push_cast; ring] using
    k_bound_three_pi (s₁ := 1) (s₂ := -1) (by norm_num) (by norm_num) t ht

/-- Shared `‖d t ^ 2‖ ≤ 4` bound where `‖d t‖ ≤ ‖t‖ + 1`. -/
private lemma pow_two_bound_of_norm_sub {d : ℝ → ℂ}
    (hd : ∀ t : ℝ, ‖d t‖ ≤ ‖(t : ℂ)‖ + 1) :
    ∀ t ∈ Ι (0 : ℝ) 1, ‖(d t) ^ (2 : ℕ)‖ ≤ 4 := fun t ht => by
  have hnorm : ‖d t‖ ≤ 2 := (hd t).trans (by linarith [norm_of_mem_uIoc_le_one ht])
  calc ‖(d t) ^ (2 : ℕ)‖
      = ‖d t‖ ^ (2 : ℕ) := by simp
    _ ≤ (2 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = 4 := by norm_num

/-- Shared argument to bound `base` for pieces 2 and 4 on `Ι 0 1`.
Requires `im_lower t` witnessing `1/2 < (arg t).im` for `t ∈ Ioo 0 1`. -/
private lemma phi_on_arg_bounded
    (arg : ℝ → ℂ) (C₀ : ℝ) (hC₀_nonneg : 0 ≤ C₀)
    (hC₀ : ∀ z : ℍ, 1 / 2 < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (him : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (1 / 2 : ℝ) < (arg t).im) :
    ∀ t ∈ Ι (0 : ℝ) 1, ‖φ₀'' (arg t)‖ ≤ max C₀ ‖φ₀'' (arg 1)‖ := fun t ht => by
  by_cases ht1 : t = 1
  · exact ht1 ▸ le_max_right _ _
  · have hh := him t ⟨by simpa using ht.1, lt_of_le_of_ne (by simpa using ht.2) ht1⟩
    exact (norm_φ₀''_le_of_half_lt hC₀_nonneg hC₀ (one_half_pos.trans hh) hh).trans
      (le_max_left _ _)

/-- Shared differentiability wrapper for I₂/I₄. -/
private lemma base_pow_diffAt_of
    {base k : ℝ → ℂ} (arg d : ℝ → ℂ) (u0 : ℂ)
    (hbase_eq : ∀ t : ℝ, ‖base t‖ = ‖φ₀'' (arg t)‖ * ‖(d t) ^ (2 : ℕ)‖)
    (hbase_cont : ContinuousOn base (Ι (0 : ℝ) 1))
    (hd_norm : ∀ t : ℝ, ‖d t‖ ≤ ‖(t : ℂ)‖ + 1)
    (him : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (1 / 2 : ℝ) < (arg t).im)
    (hk_cont : ContinuousOn k (Ι (0 : ℝ) 1))
    (hk_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k t‖ ≤ (3 * Real.pi)) :
    DifferentiableAt ℂ (fun u : ℂ =>
      ∫ t in (0 : ℝ)..1, base t * Complex.exp (u * k t)) u0 := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  set Cφ : ℝ := max C₀ ‖φ₀'' (arg 1)‖
  exact differentiableAt_intervalIntegral_mul_exp u0 (4 * Cφ) (3 * Real.pi)
    hbase_cont hk_cont (fun t ht => (hbase_eq t).le.trans <| by
      calc ‖φ₀'' (arg t)‖ * ‖(d t) ^ (2 : ℕ)‖
          ≤ Cφ * 4 := mul_le_mul (phi_on_arg_bounded arg C₀ hC₀_pos.le hC₀ him t ht)
            (pow_two_bound_of_norm_sub (d := d) hd_norm t ht) (norm_nonneg _) (by positivity)
        _ = 4 * Cφ := by ring) hk_bound

lemma I₂'C_differentiableAt (u0 : ℂ) : DifferentiableAt ℂ I₂'C u0 := by
  have hbase_cont : ContinuousOn base₂ (Ι (0 : ℝ) 1) := by
    unfold base₂ arg₂; exact phi_div_pow_continuousOn (by fun_prop) (fun _ => by simp)
  simpa [show I₂'C = _ from funext fun u => I₂'C_eq u] using
    base_pow_diffAt_of arg₂ (fun t => (t : ℂ) + (Complex.I : ℂ)) u0
      (fun t => by simp [base₂]) hbase_cont
      (fun t => by simpa using (norm_add_le (t : ℂ) (Complex.I : ℂ)))
      (fun t htIoo => by
        simpa [arg₂] using MagicFunction.a.IntegralEstimates.I₂.im_parametrisation_lower t htIoo)
      (by unfold k₂; fun_prop) k₂_bound

lemma I₄'C_differentiableAt (u0 : ℂ) : DifferentiableAt ℂ I₄'C u0 := by
  have hbase_cont : ContinuousOn base₄ (Ι (0 : ℝ) 1) :=
    (show (fun t : ℝ => (-1 : ℂ) * (φ₀'' (arg₄ t) * (-(t : ℂ) + (Complex.I : ℂ)) ^ (2 : ℕ))) = base₄
      from funext fun _ => by simp [base₄, arg₄]) ▸
    continuousOn_const.mul (phi_div_pow_continuousOn
      (d := fun t : ℝ => -(t : ℂ) + (Complex.I : ℂ)) (by fun_prop) (fun _ => by simp))
  simpa [show I₄'C = _ from funext fun u => I₄'C_eq u] using
    base_pow_diffAt_of arg₄ (fun t => -(t : ℂ) + (Complex.I : ℂ)) u0
      (fun t => by simp [base₄]) hbase_cont
      (fun t => (norm_add_le _ _).trans (by simp))
      (fun t htIoo => by
        simpa [arg₄] using MagicFunction.a.IntegralEstimates.I₄.im_parametrisation_lower t htIoo)
      (by unfold k₄; fun_prop) k₄_bound

lemma I₂'C_differentiableOn : DifferentiableOn ℂ I₂'C rightHalfPlane :=
  fun u _ => (I₂'C_differentiableAt u).differentiableWithinAt

lemma I₄'C_differentiableOn : DifferentiableOn ℂ I₄'C rightHalfPlane :=
  fun u _ => (I₄'C_differentiableAt u).differentiableWithinAt

/-
## Differentiability of the `I₆'`-piece
-/

def base₆ (t : ℝ) : ℂ :=
  (Complex.I : ℂ) * φ₀'' ((t : ℂ) * (Complex.I : ℂ))

def I₆IntegrandC (u : ℂ) (t : ℝ) : ℂ :=
  base₆ t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

def I₆IntegrandC_deriv (u : ℂ) (t : ℝ) : ℂ :=
  (-(π : ℂ) * (t : ℂ)) * I₆IntegrandC u t

lemma I₆'C_eq_integrandC (u : ℂ) :
    I₆'C u = 2 * ∫ t in Set.Ici (1 : ℝ), I₆IntegrandC u t := by
  simp [I₆'C, I₆IntegrandC, base₆, mul_assoc, mul_left_comm, mul_comm]

lemma base₆_continuousOn : ContinuousOn base₆ (Set.Ici (1 : ℝ)) := by
  have hcomp : ContinuousOn (fun t : ℝ => φ₀'' ((t : ℂ) * (Complex.I : ℂ))) (Set.Ici (1:ℝ)) :=
    MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn.comp
      (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * (Complex.I : ℂ)).continuousOn
      fun t ht => by
        simpa [UpperHalfPlane.upperHalfPlaneSet, mul_assoc] using lt_of_lt_of_le (by norm_num) ht
  simpa [base₆, mul_assoc] using continuousOn_const.mul hcomp

lemma integrable_mul_exp_neg_mul_Ici {C b : ℝ} (hb : 0 < b) :
    MeasureTheory.Integrable (fun t : ℝ => C * t * Real.exp (-b * t))
      (MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))) := by
  have hIoi1 : MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-b * t)) (Set.Ioi (1 : ℝ))
      MeasureTheory.volume :=
    (by simpa [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
        (hs := by linarith) (hp := le_rfl) (b := b) hb) :
      MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-b * t)) (Set.Ioi (0:ℝ))
        MeasureTheory.volume).mono_set (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  simpa [MeasureTheory.IntegrableOn] using
    (integrableOn_Ici_iff_integrableOn_Ioi (μ := (MeasureTheory.volume : Measure ℝ))
          (f := fun t : ℝ => C * t * Real.exp (-b * t)) (b := (1 : ℝ)) (by finiteness)).2
      (by simpa [mul_assoc] using hIoi1.const_mul C)

lemma I₆'C_differentiableAt (u0 : ℂ) (hu0 : u0 ∈ rightHalfPlane) :
    DifferentiableAt ℂ I₆'C u0 := by
  have hu0re : 0 < u0.re := by simpa [rightHalfPlane] using hu0
  set ε : ℝ := u0.re / 2 with hε_def
  have hε : 0 < ε := by positivity
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  have hbase_bound : ∀ t ∈ Set.Ici (1 : ℝ), ‖base₆ t‖ ≤ C₀ := fun t ht => by
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    simpa [base₆, norm_mul] using norm_φ₀''_le_of_half_lt hC₀_pos.le hC₀
      (z := (t : ℂ) * (Complex.I : ℂ)) (by simpa [mul_assoc] using ht0)
      (by simpa [mul_assoc] using lt_of_lt_of_le (by norm_num : (1/2:ℝ) < 1) ht)
  have hIntegrand_le : ∀ z : ℂ, ∀ t ∈ Set.Ici (1 : ℝ),
      ‖I₆IntegrandC z t‖ ≤ C₀ * Real.exp (-Real.pi * z.re * t) := fun z t ht => by
    have hExp : ‖Complex.exp (-(π : ℂ) * z * (t : ℂ))‖ ≤ Real.exp (-Real.pi * z.re * t) := by
      simp [Complex.norm_exp, mul_assoc, Complex.mul_re, sub_eq_add_neg, add_comm]
    calc ‖I₆IntegrandC z t‖
        = ‖base₆ t‖ * ‖Complex.exp (-(π : ℂ) * z * (t : ℂ))‖ := by simp [I₆IntegrandC]
      _ ≤ C₀ * Real.exp (-Real.pi * z.re * t) :=
        mul_le_mul (hbase_bound t ht) hExp (norm_nonneg _) (by positivity)
  have hIntegrandC_continuousOn : ∀ z : ℂ,
      ContinuousOn (fun t : ℝ => I₆IntegrandC z t) (Set.Ici (1 : ℝ)) := fun z => by
    simpa [I₆IntegrandC] using base₆_continuousOn.mul
      (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(π : ℂ) * z * (t : ℂ))).continuousOn
  have hF_meas : ∀ z : ℂ, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => I₆IntegrandC z t) μ := fun z =>
    (hIntegrandC_continuousOn z).aestronglyMeasurable measurableSet_Ici
  have hF_int : MeasureTheory.Integrable (fun t : ℝ => I₆IntegrandC u0 t) μ := by
    have hExp : MeasureTheory.Integrable (fun t : ℝ => Real.exp (-((Real.pi * u0.re) * t)))
        (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
      simpa [mul_assoc] using
        exp_neg_integrableOn_Ioi (a := (1 : ℝ)) (b := (Real.pi * u0.re)) (by positivity)
    have hg_int : MeasureTheory.Integrable
        (fun t : ℝ => C₀ * Real.exp (-(Real.pi * u0.re) * t)) μ := by
      simpa [MeasureTheory.IntegrableOn, μ] using
        (integrableOn_Ici_iff_integrableOn_Ioi (μ := (MeasureTheory.volume : Measure ℝ))
          (f := fun t : ℝ => C₀ * Real.exp (-(Real.pi * u0.re) * t)) (b := (1 : ℝ))
          (by finiteness)).2
            (by simpa [MeasureTheory.IntegrableOn, mul_assoc] using hExp.const_mul C₀)
    refine MeasureTheory.Integrable.mono' (μ := μ) hg_int (hF_meas u0)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun t ht => ?_)
    simpa [← mul_assoc] using hIntegrand_le u0 t ht
  have hF'_meas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => I₆IntegrandC_deriv u0 t) μ :=
    (((by fun_prop : Continuous fun t : ℝ => (-(π : ℂ) * (t : ℂ))).continuousOn.mul
      (hIntegrandC_continuousOn u0)).congr
      fun t _ => by simp [I₆IntegrandC_deriv, mul_assoc]).aestronglyMeasurable measurableSet_Ici
  let bound : ℝ → ℝ := fun t => (C₀ * Real.pi) * t * Real.exp (-(Real.pi * ε) * t)
  have hbound :
      ∀ᵐ (t : ℝ) ∂μ, ∀ z ∈ Metric.ball u0 ε, ‖I₆IntegrandC_deriv z t‖ ≤ bound t := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun t ht z hz => ?_
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht
    have hzRe : ε ≤ z.re := by
      have habs := (abs_lt.mp (lt_of_le_of_lt
        (by simpa using abs_re_le_norm (z - u0) : |z.re - u0.re| ≤ ‖z - u0‖)
        (by simpa [Metric.mem_ball, dist_eq_norm] using hz : ‖z - u0‖ < ε))).1
      simp only [hε_def]; linarith
    have hle : -π * z.re * t ≤ -π * ε * t := by
      nlinarith [mul_nonneg Real.pi_pos.le ht0, hzRe]
    have hnorm_int : ‖I₆IntegrandC z t‖ ≤ C₀ * Real.exp (-π * ε * t) :=
      (hIntegrand_le z t ht).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hC₀_pos.le)
    have hlin_norm : ‖(-(π : ℂ) * (t : ℂ))‖ ≤ Real.pi * t := by
      simp [Complex.norm_real, abs_of_nonneg ht0, abs_of_nonneg Real.pi_pos.le]
    calc ‖I₆IntegrandC_deriv z t‖
        = ‖(-(π : ℂ) * (t : ℂ))‖ * ‖I₆IntegrandC z t‖ := by
          simp [I₆IntegrandC_deriv, mul_assoc]
      _ ≤ (Real.pi * t) * (C₀ * Real.exp (-π * ε * t)) := by gcongr
      _ = bound t := by simp [bound]; ring
  have hbound_int : MeasureTheory.Integrable bound μ := by
    simpa [bound, μ, mul_assoc] using
      integrable_mul_exp_neg_mul_Ici (C := C₀ * Real.pi) (b := Real.pi * ε) (by positivity)
  have hdiff :
      ∀ᵐ (t : ℝ) ∂μ, ∀ z ∈ Metric.ball u0 ε,
        HasDerivAt (fun w : ℂ => I₆IntegrandC w t) (I₆IntegrandC_deriv z t) z :=
    Filter.Eventually.of_forall fun t z _ => by
      have hlin : HasDerivAt (fun w : ℂ => (-(π : ℂ) * w * (t : ℂ))) (-(π : ℂ) * (t : ℂ)) z := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          ((hasDerivAt_id z).const_mul (-(π : ℂ) * (t : ℂ)))
      simpa [I₆IntegrandC_deriv, I₆IntegrandC, mul_assoc, mul_left_comm, mul_comm] using
        (by simpa using hlin.cexp : HasDerivAt (fun w : ℂ => Complex.exp (-(π : ℂ) * w * (t : ℂ)))
          (Complex.exp (-(π : ℂ) * z * (t : ℂ)) * (-(π : ℂ) * (t : ℂ))) z).const_mul (base₆ t)
  have hμ : (fun z : ℂ => ∫ t, I₆IntegrandC z t ∂μ) =
      fun z : ℂ => ∫ t in Set.Ici (1 : ℝ), I₆IntegrandC z t := funext fun _ => by simp [μ]
  exact (show HasDerivAt I₆'C (2 * ∫ t, I₆IntegrandC_deriv u0 t ∂μ) u0 by
    simpa [funext fun z : ℂ => (I₆'C_eq_integrandC z : I₆'C z = _), mul_assoc] using
      (hμ ▸ (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := u0)
        (F := I₆IntegrandC) (F' := I₆IntegrandC_deriv) (bound := bound)
        (hs := Metric.ball_mem_nhds u0 hε) (hF_meas := Filter.Eventually.of_forall hF_meas)
        (hF_int := hF_int) (hF'_meas := hF'_meas)
        (h_bound := hbound) (bound_integrable := hbound_int) (h_diff := hdiff)).2).const_mul
      (2 : ℂ)).differentiableAt

lemma I₆'C_differentiableOn : DifferentiableOn ℂ I₆'C rightHalfPlane :=
  fun u hu => (I₆'C_differentiableAt u hu).differentiableWithinAt

/-- `aPrimeC` is analytic on the right half-plane. -/
public lemma aPrimeC_analyticOnNhd :
    AnalyticOnNhd ℂ aPrimeC rightHalfPlane := by
  have hdiff : DifferentiableOn ℂ aPrimeC rightHalfPlane := by
    simpa [aPrimeC] using
      (((((I₁'C_differentiableOn.add I₂'C_differentiableOn).add I₃'C_differentiableOn).add
                I₄'C_differentiableOn).add I₅'C_differentiableOn).add I₆'C_differentiableOn)
  exact hdiff.analyticOnNhd rightHalfPlane_isOpen
end

end MagicFunction.g.CohnElkies.IntegralReps
