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

lemma norm_φ₀''_le_of_half_lt {C₀ : ℝ} (hC₀_nonneg : 0 ≤ C₀)
    (hC₀ : ∀ z : ℍ, 1 / 2 < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    {z : ℂ} (hzpos : 0 < z.im) (hzhalf : 1 / 2 < z.im) :
    ‖φ₀'' z‖ ≤ C₀ := by
  let zH : ℍ := ⟨z, hzpos⟩
  have hφ' : ‖φ₀'' z‖ ≤ C₀ * Real.exp (-2 * π * zH.im) := by
    simpa [φ₀''_def hzpos] using hC₀ zH (by simpa [zH, UpperHalfPlane.im] using hzhalf)
  exact hφ'.trans (mul_le_of_le_one_right hC₀_nonneg
    (Real.exp_le_one_iff.2 (by have : 0 ≤ zH.im := hzpos.le; nlinarith [Real.pi_pos])))

lemma im_I_div (t : ℝ) : (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im = t⁻¹ := by simp

lemma neg_one_div_I_mul (t : ℝ) :
    (-1 : ℂ) / ((Complex.I : ℂ) * (t : ℂ)) = (Complex.I : ℂ) / (t : ℂ) := by
  by_cases ht : t = 0
  · subst ht
    simp
  · have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    field_simp [ht', Complex.I_ne_zero]
    simp [Complex.I_sq]

def arg₁ (t : ℝ) : ℂ := (Complex.I : ℂ) / (t : ℂ)

lemma neg_one_div_I_mul_eq_arg₁ (t : ℝ) :
    (-1 : ℂ) / ((Complex.I : ℂ) * (t : ℂ)) = arg₁ t := by simpa [arg₁] using (neg_one_div_I_mul t)

def base₁ (t : ℝ) : ℂ :=
  (-Complex.I) * φ₀'' (arg₁ t) * (t ^ (2 : ℕ) : ℝ)

def k₁ (t : ℝ) : ℂ :=
  (-π * (Complex.I : ℂ)) + (-π * (t : ℂ))

def k₃ (t : ℝ) : ℂ :=
  (π * (Complex.I : ℂ)) + (-π * (t : ℂ))

def k₅ (t : ℝ) : ℂ :=
  (-π * (t : ℂ))

lemma exp_k₁ (u : ℂ) (t : ℝ) :
    Complex.exp (u * k₁ t) =
      Complex.exp (-π * (Complex.I : ℂ) * u) * Complex.exp (-π * u * (t : ℂ)) := by
  simp [k₁, mul_add, Complex.exp_add, mul_left_comm, mul_comm]

lemma exp_k₃ (u : ℂ) (t : ℝ) :
    Complex.exp (u * k₃ t) =
      Complex.exp (π * (Complex.I : ℂ) * u) * Complex.exp (-π * u * (t : ℂ)) := by
  simp [k₃, mul_add, Complex.exp_add, mul_left_comm, mul_comm]

lemma exp_k₅ (u : ℂ) (t : ℝ) :
    Complex.exp (u * k₅ t) = Complex.exp (-π * u * (t : ℂ)) := by simp [k₅, mul_left_comm, mul_comm]

lemma I₁'C_eq (u : ℂ) :
    I₁'C u = ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k₁ t) := by
  refine intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ))
    fun t _ => by simp [base₁, exp_k₁, neg_one_div_I_mul_eq_arg₁, mul_assoc]

lemma I₃'C_eq (u : ℂ) :
    I₃'C u = ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k₃ t) := by
  refine intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ))
    fun t _ => by simp [base₁, exp_k₃, neg_one_div_I_mul_eq_arg₁, mul_assoc]

lemma I₅'C_eq (u : ℂ) :
    I₅'C u = -2 * ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k₅ t) := by
  refine congrArg (fun x : ℂ => -2 * x) <|
    intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ))
      fun t _ => by simp [base₁, exp_k₅, neg_one_div_I_mul_eq_arg₁, mul_assoc]

lemma arg₁_continuousOn : ContinuousOn arg₁ (Ι (0 : ℝ) 1) := by
  simpa [arg₁] using continuousOn_const.div continuous_ofReal.continuousOn
    (fun t ht => by exact_mod_cast ne_of_gt (by simpa using ht.1))

lemma arg₁_mapsTo :
    Set.MapsTo arg₁ (Ι (0 : ℝ) 1) UpperHalfPlane.upperHalfPlaneSet := by
  intro t ht
  have ht0 : 0 < t := by simpa using ht.1
  simpa [UpperHalfPlane.upperHalfPlaneSet, arg₁, im_I_div] using inv_pos.2 ht0

lemma base₁_continuousOn : ContinuousOn base₁ (Ι (0 : ℝ) 1) := by
  change ContinuousOn (fun t : ℝ =>
    (-Complex.I) * φ₀'' (arg₁ t) * ((t ^ (2 : ℕ) : ℝ) : ℂ)) (Ι (0 : ℝ) 1)
  have hcontφ := (MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn
    (s := UpperHalfPlane.upperHalfPlaneSet)).comp arg₁_continuousOn arg₁_mapsTo
  exact (continuousOn_const.mul hcontφ).mul (by fun_prop : Continuous _).continuousOn

lemma k₁_continuousOn : ContinuousOn k₁ (Ι (0 : ℝ) 1) := by
  change ContinuousOn (fun t : ℝ => (-π * (Complex.I : ℂ)) + (-π * (t : ℂ))) (Ι (0 : ℝ) 1)
  exact (by fun_prop : Continuous fun t : ℝ => (-π * (Complex.I : ℂ)) + (-π * (t : ℂ))).continuousOn

lemma k₃_continuousOn : ContinuousOn k₃ (Ι (0 : ℝ) 1) := by
  change ContinuousOn (fun t : ℝ => (π * (Complex.I : ℂ)) + (-π * (t : ℂ))) (Ι (0 : ℝ) 1)
  exact (by fun_prop : Continuous fun t : ℝ => (π * (Complex.I : ℂ)) + (-π * (t : ℂ))).continuousOn

lemma k₅_continuousOn : ContinuousOn k₅ (Ι (0 : ℝ) 1) := by
  change ContinuousOn (fun t : ℝ => (-π * (t : ℂ))) (Ι (0 : ℝ) 1)
  exact (by fun_prop : Continuous fun t : ℝ => (-π * (t : ℂ))).continuousOn

lemma base₁_bound :
    ∃ C₀ > 0, ∀ t ∈ Ι (0 : ℝ) 1, ‖base₁ t‖ ≤ C₀ := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C₀, hC₀_pos, ?_⟩
  intro t ht
  have ht0 : 0 < t := by simpa using ht.1
  have ht1 : t ≤ 1 := by simpa using ht.2
  have hzpos : 0 < (arg₁ t).im := by simpa [arg₁, im_I_div] using inv_pos.2 ht0
  have hzhalf : (1 / 2 : ℝ) < (arg₁ t).im := by
    simpa [arg₁, im_I_div] using lt_of_lt_of_le (by norm_num) (one_le_inv_iff₀.2 ⟨ht0, ht1⟩)
  have hφ : ‖φ₀'' (arg₁ t)‖ ≤ C₀ := norm_φ₀''_le_of_half_lt hC₀_pos.le hC₀ hzpos hzhalf
  have ht2 : ‖(t ^ (2 : ℕ) : ℝ)‖ ≤ 1 := by
    simp only [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg t) (by simpa [abs_of_nonneg ht0.le])
  simpa [base₁] using hφ.trans' (mul_le_of_le_one_right (norm_nonneg _) ht2)

private lemma norm_of_mem_uIoc_le_one {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) : ‖(t : ℂ)‖ ≤ 1 := by
  have ht0 : 0 ≤ t := (by simpa using ht.1 : (0 : ℝ) < t).le
  simpa [Complex.norm_real, abs_of_nonneg ht0] using ht.2

private lemma norm_neg_pi_mul_le_pi {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖(-π : ℂ) * z‖ ≤ Real.pi := by
  have hnorm : ‖(-π : ℂ) * z‖ = Real.pi * ‖z‖ := by
    simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]
  nlinarith [Real.pi_pos, hz, hnorm]

private lemma norm_pi_I_mul_eq_pi : ‖(π : ℂ) * (Complex.I : ℂ)‖ = Real.pi := by
  simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]

private lemma norm_neg_pi_I_mul_eq_pi : ‖(-π : ℂ) * (Complex.I : ℂ)‖ = Real.pi := by
  simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]

private lemma norm_pi_I_mul_le_pi {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(π : ℂ) * (Complex.I : ℂ) * z‖ ≤ Real.pi := by
  have hnorm : ‖(π : ℂ) * (Complex.I : ℂ) * z‖ = Real.pi * ‖z‖ := by
    simpa [mul_assoc] using congrArg (fun x : ℝ => x * ‖z‖) norm_pi_I_mul_eq_pi
  nlinarith [Real.pi_pos, hz, hnorm]

private lemma norm_neg_pi_I_mul_le_pi {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(-π : ℂ) * (Complex.I : ℂ) * z‖ ≤ Real.pi := by
  have hnorm : ‖(-π : ℂ) * (Complex.I : ℂ) * z‖ = Real.pi * ‖z‖ := by
    simpa [mul_assoc] using congrArg (fun x : ℝ => x * ‖z‖) norm_neg_pi_I_mul_eq_pi
  nlinarith [Real.pi_pos, hz, hnorm]

lemma k₁_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k₁ t‖ ≤ (2 * Real.pi) := by
  intro t ht
  have htpi : ‖(-π : ℂ) * (t : ℂ)‖ ≤ Real.pi :=
    norm_neg_pi_mul_le_pi (z := (t : ℂ)) (norm_of_mem_uIoc_le_one ht)
  have hsum :
      ‖k₁ t‖ ≤ ‖(-π * (Complex.I : ℂ) : ℂ)‖ + ‖(-π * (t : ℂ) : ℂ)‖ :=
    by simpa [k₁] using (norm_add_le (-π * (Complex.I : ℂ) : ℂ) (-π * (t : ℂ) : ℂ))
  have hpiI : ‖(-π * (Complex.I : ℂ) : ℂ)‖ = Real.pi := by
    simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]
  have : ‖k₁ t‖ ≤ Real.pi + Real.pi :=
    hsum.trans (add_le_add (le_of_eq hpiI) (by simpa [mul_assoc] using htpi))
  simpa [two_mul] using this

lemma k₃_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k₃ t‖ ≤ (2 * Real.pi) := by
  intro t ht
  have htpi : ‖(-π : ℂ) * (t : ℂ)‖ ≤ Real.pi :=
    norm_neg_pi_mul_le_pi (z := (t : ℂ)) (norm_of_mem_uIoc_le_one ht)
  have hsum :
      ‖k₃ t‖ ≤ ‖(π * (Complex.I : ℂ) : ℂ)‖ + ‖(-π * (t : ℂ) : ℂ)‖ :=
    by simpa [k₃] using (norm_add_le (π * (Complex.I : ℂ) : ℂ) (-π * (t : ℂ) : ℂ))
  have hpiI : ‖(π * (Complex.I : ℂ) : ℂ)‖ = Real.pi := by
    simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]
  have : ‖k₃ t‖ ≤ Real.pi + Real.pi :=
    hsum.trans (add_le_add (le_of_eq hpiI) (by simpa [mul_assoc] using htpi))
  simpa [two_mul] using this

lemma k₅_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k₅ t‖ ≤ Real.pi := by
  intro t ht
  simpa [k₅] using norm_neg_pi_mul_le_pi (z := (t : ℂ)) (norm_of_mem_uIoc_le_one ht)

private lemma differentiableAt_base₁_mul_exp (k : ℝ → ℂ) (Ck : ℝ)
    (hk_cont : ContinuousOn k (Ι (0 : ℝ) 1)) (hk_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k t‖ ≤ Ck)
    (u0 : ℂ) : DifferentiableAt ℂ (fun u => ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k t))
    u0 := by
  rcases base₁_bound with ⟨Cbase, _, hbase_bound⟩
  exact differentiableAt_intervalIntegral_mul_exp u0 Cbase Ck
    base₁_continuousOn hk_cont hbase_bound hk_bound

lemma I₁'C_differentiableAt (u0 : ℂ) : DifferentiableAt ℂ I₁'C u0 := by
  simpa [show I₁'C = fun u => ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k₁ t) from
    funext fun u => by simpa using I₁'C_eq u] using
    differentiableAt_base₁_mul_exp k₁ (2 * Real.pi) k₁_continuousOn k₁_bound u0

lemma I₃'C_differentiableAt (u0 : ℂ) : DifferentiableAt ℂ I₃'C u0 := by
  simpa [show I₃'C = fun u => ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k₃ t) from
    funext fun u => by simpa using I₃'C_eq u] using
    differentiableAt_base₁_mul_exp k₃ (2 * Real.pi) k₃_continuousOn k₃_bound u0

lemma I₅'C_differentiableAt (u0 : ℂ) : DifferentiableAt ℂ I₅'C u0 := by
  simpa [show I₅'C = fun u => (-2 : ℂ) * ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k₅ t)
    from funext fun u => by simpa [mul_assoc] using I₅'C_eq u, mul_assoc] using
    (differentiableAt_base₁_mul_exp k₅ Real.pi k₅_continuousOn k₅_bound u0).const_mul (-2 : ℂ)

lemma I₁'C_differentiableOn : DifferentiableOn ℂ I₁'C rightHalfPlane :=
  fun u _hu => (I₁'C_differentiableAt u).differentiableWithinAt

lemma I₃'C_differentiableOn : DifferentiableOn ℂ I₃'C rightHalfPlane :=
  fun u _hu => (I₃'C_differentiableAt u).differentiableWithinAt

lemma I₅'C_differentiableOn : DifferentiableOn ℂ I₅'C rightHalfPlane :=
  fun u _hu => (I₅'C_differentiableAt u).differentiableWithinAt

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

lemma exp_k₂ (u : ℂ) (t : ℝ) :
    Complex.exp (u * k₂ t) =
      Complex.exp (-π * (Complex.I : ℂ) * u) *
        (Complex.exp (π * (Complex.I : ℂ) * u * (t : ℂ)) * Complex.exp (-π * u)) := by
  simp [k₂, mul_add, Complex.exp_add, add_assoc, mul_left_comm, mul_comm]

lemma exp_k₄ (u : ℂ) (t : ℝ) :
    Complex.exp (u * k₄ t) =
      Complex.exp (π * (Complex.I : ℂ) * u) *
        (Complex.exp (-π * (Complex.I : ℂ) * u * (t : ℂ)) * Complex.exp (-π * u)) := by
  simp [k₄, mul_add, Complex.exp_add, add_assoc, mul_left_comm, mul_comm]

lemma I₂'C_eq (u : ℂ) :
    I₂'C u = ∫ t in (0 : ℝ)..1, base₂ t * Complex.exp (u * k₂ t) := by
  refine intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ))
    fun t _ => by simp [base₂, arg₂, exp_k₂, mul_assoc, mul_left_comm, mul_comm]

lemma I₄'C_eq (u : ℂ) :
    I₄'C u = ∫ t in (0 : ℝ)..1, base₄ t * Complex.exp (u * k₄ t) := by
  refine intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ))
    fun t _ => by simp [base₄, arg₄, exp_k₄, mul_assoc, mul_left_comm, mul_comm]

lemma base₂_continuousOn : ContinuousOn base₂ (Ι (0 : ℝ) 1) := by
  change ContinuousOn (fun t : ℝ => φ₀'' (arg₂ t) * (((t : ℂ) + I) ^ (2 : ℕ))) (Ι (0 : ℝ) 1)
  have hden0 : ∀ t ∈ Ι (0 : ℝ) 1, ((t : ℂ) + I) ≠ 0 := by
    intro t _ ht0
    exact one_ne_zero (by simpa using congrArg Complex.im ht0 : (1 : ℝ) = 0)
  have hcontArg : ContinuousOn arg₂ (Ι (0 : ℝ) 1) := by
    simpa [arg₂] using continuousOn_const.div
      (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + I).continuousOn hden0
  have hmaps : Set.MapsTo arg₂ (Ι (0 : ℝ) 1) UpperHalfPlane.upperHalfPlaneSet := by
    intro t ht
    simp only [UpperHalfPlane.upperHalfPlaneSet, Set.mem_setOf_eq]
    have him : (arg₂ t).im = 1 / Complex.normSq ((t : ℂ) + I) := by
      simp [arg₂, div_eq_mul_inv, Complex.inv_im, Complex.normSq, Complex.neg_im]
    rw [him]
    exact one_div_pos.2 (Complex.normSq_pos.2 (hden0 t ht))
  exact ((MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn.comp hcontArg hmaps).mul
    (by fun_prop : Continuous _).continuousOn)

lemma base₄_continuousOn : ContinuousOn base₄ (Ι (0 : ℝ) 1) := by
  change ContinuousOn (fun t : ℝ =>
    (-1 : ℂ) * φ₀'' (arg₄ t) * ((-(t : ℂ) + I) ^ (2 : ℕ))) (Ι (0 : ℝ) 1)
  have hden0 : ∀ t ∈ Ι (0 : ℝ) 1, (-(t : ℂ) + I) ≠ 0 := by
    intro t _ ht0
    exact one_ne_zero (by simpa using congrArg Complex.im ht0 : (1 : ℝ) = 0)
  have hcontArg : ContinuousOn arg₄ (Ι (0 : ℝ) 1) := by
    simpa [arg₄] using continuousOn_const.div
      (by fun_prop : Continuous fun t : ℝ => -(t : ℂ) + I).continuousOn hden0
  have hmaps : Set.MapsTo arg₄ (Ι (0 : ℝ) 1) UpperHalfPlane.upperHalfPlaneSet := by
    intro t ht
    simp only [UpperHalfPlane.upperHalfPlaneSet, Set.mem_setOf_eq]
    have him : (arg₄ t).im = 1 / Complex.normSq (-(t : ℂ) + I) := by
      simp [arg₄, div_eq_mul_inv, Complex.inv_im, Complex.normSq, Complex.neg_im]
    rw [him]
    exact one_div_pos.2 (Complex.normSq_pos.2 (hden0 t ht))
  exact ((continuousOn_const.mul (MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn.comp
    hcontArg hmaps)).mul (by fun_prop : Continuous _).continuousOn)

lemma k₂_continuousOn : ContinuousOn k₂ (Ι (0 : ℝ) 1) := by
  let f : ℝ → ℂ := fun t => (-π * (Complex.I : ℂ)) + (π * (Complex.I : ℂ) * (t : ℂ)) + (-π)
  exact (by fun_prop : Continuous f).continuousOn

lemma k₄_continuousOn : ContinuousOn k₄ (Ι (0 : ℝ) 1) := by
  let f : ℝ → ℂ := fun t => (π * (Complex.I : ℂ)) + (-π * (Complex.I : ℂ) * (t : ℂ)) + (-π)
  exact (by fun_prop : Continuous f).continuousOn

private lemma norm_three_sum_le_three_pi (a b c : ℂ) (ha : ‖a‖ ≤ π) (hb : ‖b‖ ≤ π)
    (hc : ‖c‖ ≤ π) : ‖a + b + c‖ ≤ 3 * π := by
  have h : ‖a + b + c‖ ≤ π + π + π :=
    ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ha hb)) hc))
  linarith

lemma k₂_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k₂ t‖ ≤ (3 * Real.pi) := by
  intro t ht
  have htnorm : ‖(t : ℂ)‖ ≤ 1 := norm_of_mem_uIoc_le_one ht
  simpa [k₂] using norm_three_sum_le_three_pi _ _ _
    (le_of_eq norm_neg_pi_I_mul_eq_pi)
    (by simpa [mul_assoc] using norm_pi_I_mul_le_pi htnorm)
    (by simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le])

lemma k₄_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k₄ t‖ ≤ (3 * Real.pi) := by
  intro t ht
  have htnorm : ‖(t : ℂ)‖ ≤ 1 := norm_of_mem_uIoc_le_one ht
  simpa [k₄] using norm_three_sum_le_three_pi _ _ _
    (le_of_eq norm_pi_I_mul_eq_pi)
    (by simpa [mul_assoc] using norm_neg_pi_I_mul_le_pi htnorm)
    (by simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le])

private lemma φ₀''_bound_on_uIoc (arg : ℝ → ℂ)
    (him : ∀ t, t ∈ Set.Ioo (0 : ℝ) 1 → (1 / 2 : ℝ) < (arg t).im) :
    ∃ Cφ > 0, ∀ t ∈ Ι (0 : ℝ) 1, ‖φ₀'' (arg t)‖ ≤ Cφ := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨max C₀ ‖φ₀'' (arg 1)‖, by positivity, fun t ht => ?_⟩
  by_cases ht1 : t = 1
  · exact ht1 ▸ le_max_right _ _
  · have htIoo : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨by simpa using ht.1,
      lt_of_le_of_ne (by simpa using ht.2) ht1⟩
    exact (norm_φ₀''_le_of_half_lt hC₀_pos.le hC₀ (one_half_pos.trans (him t htIoo))
      (him t htIoo)).trans (le_max_left _ _)

lemma I₂'C_differentiableAt (u0 : ℂ) : DifferentiableAt ℂ I₂'C u0 := by
  obtain ⟨Cφ, _, hφ_bound⟩ := φ₀''_bound_on_uIoc arg₂ (fun t ht => by
    simpa [arg₂] using MagicFunction.a.IntegralEstimates.I₂.im_parametrisation_lower t ht)
  have hpow_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖(((t : ℂ) + I) ^ (2 : ℕ))‖ ≤ 4 := by
    intro t ht
    have : ‖(t : ℂ) + I‖ ≤ 2 :=
      (norm_add_le _ _).trans (by linarith [norm_of_mem_uIoc_le_one ht, Complex.norm_I])
    simp only [norm_pow]
    calc ‖(t : ℂ) + I‖ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = 4 := by norm_num
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base₂ t‖ ≤ (4 * Cφ) := fun t ht => by
    simpa [base₂, mul_comm] using
      mul_le_mul (hφ_bound t ht) (hpow_bound t ht) (norm_nonneg _) (by positivity)
  have h := differentiableAt_intervalIntegral_mul_exp u0 (4 * Cφ) (3 * Real.pi)
    base₂_continuousOn k₂_continuousOn hbase_bound k₂_bound
  simpa [show I₂'C = fun u => ∫ t in (0 : ℝ)..1, base₂ t * Complex.exp (u * k₂ t) from
    funext fun u => by simpa using I₂'C_eq u] using h

lemma I₄'C_differentiableAt (u0 : ℂ) : DifferentiableAt ℂ I₄'C u0 := by
  obtain ⟨Cφ, _, hφ_bound⟩ := φ₀''_bound_on_uIoc arg₄ (fun t ht => by
    simpa [arg₄] using MagicFunction.a.IntegralEstimates.I₄.im_parametrisation_lower t ht)
  have hpow_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖((-(t : ℂ) + I) ^ (2 : ℕ))‖ ≤ 4 := by
    intro t ht
    have : ‖-(t : ℂ) + I‖ ≤ 2 := by
      calc ‖-(t : ℂ) + I‖ ≤ ‖-(t : ℂ)‖ + ‖I‖ := norm_add_le _ _
        _ = ‖(t : ℂ)‖ + 1 := by simp
        _ ≤ 2 := by linarith [norm_of_mem_uIoc_le_one ht]
    simp only [norm_pow]
    calc ‖-(t : ℂ) + I‖ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = 4 := by norm_num
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base₄ t‖ ≤ (4 * Cφ) := fun t ht => by
    simpa [base₄, mul_comm] using
      mul_le_mul (hφ_bound t ht) (hpow_bound t ht) (norm_nonneg _) (by positivity)
  have h := differentiableAt_intervalIntegral_mul_exp u0 (4 * Cφ) (3 * Real.pi)
    base₄_continuousOn k₄_continuousOn hbase_bound k₄_bound
  simpa [show I₄'C = fun u => ∫ t in (0 : ℝ)..1, base₄ t * Complex.exp (u * k₄ t) from
    funext fun u => by simpa using I₄'C_eq u] using h

lemma I₂'C_differentiableOn : DifferentiableOn ℂ I₂'C rightHalfPlane :=
  fun u _hu => (I₂'C_differentiableAt u).differentiableWithinAt

lemma I₄'C_differentiableOn : DifferentiableOn ℂ I₄'C rightHalfPlane :=
  fun u _hu => (I₄'C_differentiableAt u).differentiableWithinAt

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
  have hcomp :
      ContinuousOn (fun t : ℝ => φ₀'' ((t : ℂ) * (Complex.I : ℂ))) (Set.Ici (1 : ℝ)) := by
    refine (MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn).comp
      (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * (Complex.I : ℂ)).continuousOn ?_
    intro t ht
    simpa [UpperHalfPlane.upperHalfPlaneSet, mul_assoc] using (lt_of_lt_of_le (by norm_num) ht)
  simpa [base₆, mul_assoc] using (continuousOn_const.mul hcomp)

lemma re_sub_lt_of_mem_ball {u0 u : ℂ} {ε : ℝ} (hu : u ∈ Metric.ball u0 ε) :
    u0.re - ε < u.re := by
  have habs : |u.re - u0.re| < ε := by
    simpa using (abs_re_le_norm (u - u0)).trans_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hu)
  linarith [(abs_lt.mp habs).1]

lemma re_half_le_of_mem_ball {u0 u : ℂ}
    (hu : u ∈ Metric.ball u0 (u0.re / 2)) : u0.re / 2 ≤ u.re := by
  nlinarith [re_sub_lt_of_mem_ball (u0 := u0) (u := u) (ε := u0.re / 2) hu]

lemma integrableOn_mul_exp_neg_mul_Ioi {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-b * t)) (Set.Ioi (1 : ℝ))
      MeasureTheory.volume := by
  have hIoi0 : MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-b * t)) (Set.Ioi (0 : ℝ))
      MeasureTheory.volume := by
    simpa [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
        (hs := by linarith) (hp := le_rfl) (b := b) hb)
  exact hIoi0.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))

lemma integrable_mul_exp_neg_mul_Ici {C b : ℝ} (hb : 0 < b) :
    MeasureTheory.Integrable (fun t : ℝ => C * t * Real.exp (-b * t))
      (MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))) := by
  simpa [MeasureTheory.IntegrableOn] using
    (integrableOn_Ici_iff_integrableOn_Ioi (μ := (MeasureTheory.volume : Measure ℝ))
          (f := fun t : ℝ => C * t * Real.exp (-b * t)) (b := (1 : ℝ)) (by finiteness)).2
      (by simpa [mul_assoc] using (integrableOn_mul_exp_neg_mul_Ioi (b := b) hb).const_mul C)

lemma hasDerivAt_integral_I₆IntegrandC
    (μ : Measure ℝ) (u0 : ℂ) (ε : ℝ) (bound : ℝ → ℝ) (hε : 0 < ε)
    (hF_meas' :
      ∀ᶠ z in 𝓝 u0, MeasureTheory.AEStronglyMeasurable (fun t : ℝ => I₆IntegrandC z t) μ)
    (hF_int : MeasureTheory.Integrable (fun t : ℝ => I₆IntegrandC u0 t) μ)
    (hF'_meas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => I₆IntegrandC_deriv u0 t) μ)
    (hbound :
      ∀ᵐ (t : ℝ) ∂μ, ∀ z ∈ Metric.ball u0 ε, ‖I₆IntegrandC_deriv z t‖ ≤ bound t)
    (hbound_int : MeasureTheory.Integrable bound μ)
    (hdiff :
      ∀ᵐ (t : ℝ) ∂μ, ∀ z ∈ Metric.ball u0 ε,
        HasDerivAt (fun w : ℂ => I₆IntegrandC w t) (I₆IntegrandC_deriv z t) z) :
    HasDerivAt (fun z : ℂ => ∫ t, I₆IntegrandC z t ∂μ)
      (∫ t, I₆IntegrandC_deriv u0 t ∂μ) u0 := by
  exact
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := u0) (s := Metric.ball u0 ε)
      (hs := Metric.ball_mem_nhds u0 hε) (F := I₆IntegrandC) (F' := I₆IntegrandC_deriv)
      (bound := bound) (hF_meas := hF_meas') (hF_int := hF_int) (hF'_meas := hF'_meas)
      (h_bound := hbound) (bound_integrable := hbound_int) (h_diff := hdiff)).2

lemma I₆'C_differentiableAt (u0 : ℂ) (hu0 : u0 ∈ rightHalfPlane) :
    DifferentiableAt ℂ I₆'C u0 := by
  have hu0re : 0 < u0.re := by simpa [rightHalfPlane] using hu0
  set ε : ℝ := u0.re / 2
  have hε : 0 < ε := by positivity
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  have hbase_bound : ∀ t ∈ Set.Ici (1 : ℝ), ‖base₆ t‖ ≤ C₀ := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    have htHalf : (1 / 2 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht
    have hzpos : 0 < (((t : ℂ) * (Complex.I : ℂ)) : ℂ).im := by simpa [mul_assoc] using ht0
    have hhalf : (1 / 2 : ℝ) < (((t : ℂ) * (Complex.I : ℂ)) : ℂ).im := by
      simpa [mul_assoc] using htHalf
    have hφ : ‖φ₀'' ((t : ℂ) * (Complex.I : ℂ))‖ ≤ C₀ :=
      norm_φ₀''_le_of_half_lt hC₀_pos.le hC₀ hzpos hhalf
    simpa [base₆, norm_mul] using hφ
  have hF_meas :
      ∀ z : ℂ, MeasureTheory.AEStronglyMeasurable (fun t : ℝ => I₆IntegrandC z t) μ := by
    intro z
    have hcont : ContinuousOn (fun t : ℝ => I₆IntegrandC z t) (Set.Ici (1 : ℝ)) := by
      dsimp [I₆IntegrandC]
      exact base₆_continuousOn.mul (by fun_prop : Continuous _).continuousOn
    exact
      hcont.aestronglyMeasurable (measurableSet_Ici : MeasurableSet (Set.Ici (1 : ℝ)))
  have hF_meas' : ∀ᶠ z in 𝓝 u0,
      MeasureTheory.AEStronglyMeasurable (fun t : ℝ => I₆IntegrandC z t) μ :=
    .of_forall hF_meas
  have hF_int : MeasureTheory.Integrable (fun t : ℝ => I₆IntegrandC u0 t) μ := by
    have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => I₆IntegrandC u0 t) μ := hF_meas u0
    let g : ℝ → ℝ := fun t : ℝ => C₀ * Real.exp (-(Real.pi * u0.re) * t)
    have hg_int : MeasureTheory.Integrable g μ := by
      have hu0' : 0 < Real.pi * u0.re := by positivity
      have hExp : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-(Real.pi * u0.re) * t))
          (Set.Ioi (1 : ℝ)) := by
        simpa [mul_assoc] using exp_neg_integrableOn_Ioi (a := 1) (b := Real.pi * u0.re) hu0'
      simpa [MeasureTheory.IntegrableOn, μ, g, mul_assoc] using
        ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2
          (hExp.const_mul C₀))
    refine MeasureTheory.Integrable.mono' (μ := μ) hg_int hmeas ?_
    refine
      MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici : MeasurableSet (Set.Ici (1 : ℝ))) ?_
    intro t ht
    have hbase : ‖base₆ t‖ ≤ C₀ := hbase_bound t ht
    have hExp :
        ‖Complex.exp (-(π : ℂ) * u0 * (t : ℂ))‖ ≤ Real.exp (-(Real.pi * u0.re) * t) := by
      simp [Complex.norm_exp, mul_assoc, Complex.mul_re, sub_eq_add_neg, add_comm]
    simpa [g, I₆IntegrandC] using mul_le_mul hbase hExp (norm_nonneg _) (by positivity)
  have hF'_meas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => I₆IntegrandC_deriv u0 t) μ := by
    have hcont : ContinuousOn (fun t : ℝ => I₆IntegrandC_deriv u0 t) (Set.Ici (1 : ℝ)) := by
      have hint : ContinuousOn (fun t : ℝ => I₆IntegrandC u0 t) (Set.Ici (1 : ℝ)) := by
        simpa [I₆IntegrandC] using base₆_continuousOn.mul (by fun_prop : Continuous _).continuousOn
      refine (((by fun_prop : Continuous fun t : ℝ => (-(π : ℂ) * (t : ℂ))).continuousOn).mul
        hint).congr ?_
      intro t _ht
      simp [I₆IntegrandC_deriv, mul_assoc]
    exact hcont.aestronglyMeasurable measurableSet_Ici
  let bound : ℝ → ℝ := fun t => (C₀ * Real.pi) * t * Real.exp (-(Real.pi * ε) * t)
  have hbound :
      ∀ᵐ (t : ℝ) ∂μ, ∀ z ∈ Metric.ball u0 ε,
        ‖I₆IntegrandC_deriv z t‖ ≤ bound t := by
    refine
      MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici : MeasurableSet (Set.Ici (1 : ℝ))) ?_
    intro t ht z hz
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht
    have hzRe : ε ≤ z.re := by
      have : z ∈ Metric.ball u0 (u0.re / 2) := by simpa [ε] using hz
      simpa [ε] using (re_half_le_of_mem_ball (u0 := u0) (u := z) this)
    have hExp :
        ‖Complex.exp (-(π : ℂ) * z * (t : ℂ))‖ ≤ Real.exp (-π * ε * t) := by
      simp only [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hre : (-(π : ℂ) * z * (t : ℂ)).re = -π * z.re * t := by
        simp [mul_assoc, Complex.mul_re, sub_eq_add_neg, add_comm]
      rw [hre]
      nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right hzRe ht0]
    have hbase : ‖base₆ t‖ ≤ C₀ := hbase_bound t ht
    have hnorm_int : ‖I₆IntegrandC z t‖ ≤ C₀ * Real.exp (-π * ε * t) := by
      simpa [I₆IntegrandC] using mul_le_mul hbase hExp (norm_nonneg _) (by positivity)
    have hlin_norm : ‖(-(π : ℂ) * (t : ℂ))‖ = Real.pi * t := by
      simp [Complex.norm_real, Real.pi_pos.le, abs_of_nonneg ht0]
    simp only [bound, I₆IntegrandC_deriv]
    calc ‖(-(π : ℂ) * (t : ℂ)) * I₆IntegrandC z t‖
        = ‖(-(π : ℂ) * (t : ℂ))‖ * ‖I₆IntegrandC z t‖ := norm_mul _ _
      _ ≤ (Real.pi * t) * (C₀ * Real.exp (-π * ε * t)) := by rw [hlin_norm]; gcongr
      _ = _ := by ring_nf
  have hbound_int : MeasureTheory.Integrable bound μ := by
    have hb : 0 < Real.pi * ε := by positivity
    simpa [bound, μ, mul_assoc] using
      (integrable_mul_exp_neg_mul_Ici (C := (C₀ * Real.pi)) (b := (Real.pi * ε)) hb)
  have hdiffCore :
      HasDerivAt (fun z : ℂ => ∫ t, I₆IntegrandC z t ∂μ)
        (∫ t, I₆IntegrandC_deriv u0 t ∂μ) u0 := by
    have hdiff :
        ∀ᵐ (t : ℝ) ∂μ, ∀ z ∈ Metric.ball u0 ε,
          HasDerivAt (fun w : ℂ => I₆IntegrandC w t) (I₆IntegrandC_deriv z t) z := by
      refine (Filter.Eventually.of_forall fun t => ?_)
      intro z _hz
      have hlin :
          HasDerivAt (fun w : ℂ => (-(π : ℂ) * w * (t : ℂ))) (-(π : ℂ) * (t : ℂ)) z := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          ((hasDerivAt_id z).const_mul (-(π : ℂ) * (t : ℂ)))
      have hexp := (by simpa using hlin.cexp :
        HasDerivAt (fun w => Complex.exp (-(π : ℂ) * w * (t : ℂ)))
          (Complex.exp (-(π : ℂ) * z * (t : ℂ)) * (-(π : ℂ) * (t : ℂ))) z)
      simpa [I₆IntegrandC_deriv, I₆IntegrandC, mul_assoc, mul_left_comm, mul_comm] using
        (by simpa [mul_assoc, mul_left_comm, mul_comm] using hexp.const_mul (base₆ t))
    exact
      hasDerivAt_integral_I₆IntegrandC μ u0 ε bound hε hF_meas' hF_int hF'_meas hbound hbound_int
        hdiff
  have hEqfun : I₆'C = fun z : ℂ => 2 * ∫ t in Set.Ici (1 : ℝ), I₆IntegrandC z t := by
    funext z
    simpa using I₆'C_eq_integrandC z
  have hfun : (fun z : ℂ => ∫ t, I₆IntegrandC z t ∂μ) =
      fun z => ∫ t in Set.Ici (1 : ℝ), I₆IntegrandC z t := by
    funext z
    simp [μ]
  rw [hfun] at hdiffCore
  have : HasDerivAt I₆'C (2 * ∫ t, I₆IntegrandC_deriv u0 t ∂μ) u0 := by
    simpa [hEqfun, mul_assoc] using hdiffCore.const_mul (2 : ℂ)
  exact this.differentiableAt

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
