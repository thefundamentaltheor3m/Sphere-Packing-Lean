module
public import SpherePacking.MagicFunction.b.Basic
public import SpherePacking.Basic.Domains.RightHalfPlane
public import Mathlib.Analysis.Analytic.Basic
import SpherePacking.ModularForms.SlashActionAuxil
import SpherePacking.MagicFunction.b.PsiBounds
import SpherePacking.MagicFunction.g.CohnElkies.IntegralReductions
import SpherePacking.MagicFunction.b.PsiParamRelations
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ5
import SpherePacking.Integration.UpperHalfPlaneComp
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity
import SpherePacking.MagicFunction.PsiTPrimeZ1
import SpherePacking.Integration.Measure
import SpherePacking.ForMathlib.IntegrablePowMulExp
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Complex analytic extension of `b'` (`bPrimeC`)

For the identity-theorem argument in `AnotherIntegral.B`, we need a function `ℂ → ℂ` that is
analytic on the right half-plane and whose restriction to real `u > 0` agrees with `b' u`.
This file defines complexified integrals `J₁'C`, ..., `J₆'C` and their sum `bPrimeC`, then proves
the real restriction lemma `bPrimeC_ofReal` and analyticity `bPrimeC_analyticOnNhd`.

## Main definition
* `bPrimeC`

## Main statements
* `bPrimeC_ofReal`
* `bPrimeC_analyticOnNhd`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Interval Topology

open MeasureTheory Real Complex Filter Set
open SpherePacking.Integration (μIciOne)

open SpherePacking

open intervalIntegral
open MagicFunction.b.RealIntegrals
open MagicFunction.Parametrisations

noncomputable section

/-- Complexified `J₁'`. -/
def J₁'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (Complex.I : ℂ) * ψT' (z₁' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₁' t))

/-- Complexified `J₂'`. -/
def J₂'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    ψT' (z₂' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₂' t))

/-- Complexified `J₃'`. -/
def J₃'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (Complex.I : ℂ) * ψT' (z₃' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₃' t))

/-- Complexified `J₄'`. -/
def J₄'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (-1 : ℂ) * ψT' (z₄' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₄' t))

/-- Complexified `J₅'`. -/
def J₅'C (u : ℂ) : ℂ :=
  -2 * ∫ t in (0 : ℝ)..1,
    (Complex.I : ℂ) * ψI' (z₅' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₅' t))

/-- Complexified `J₆'`. -/
def J₆'C (u : ℂ) : ℂ :=
  -2 * ∫ t in Set.Ici (1 : ℝ),
    (Complex.I : ℂ) * ψS' (z₆' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₆' t))

/-- Analytic extension of `b'` to complex parameters, defined as the sum of `J₁'C`, ..., `J₆'C`. -/
public def bPrimeC (u : ℂ) : ℂ :=
  J₁'C u + J₂'C u + J₃'C u + J₄'C u + J₅'C u + J₆'C u

/-- On real parameters, `bPrimeC` agrees with the real function `b'`. -/
public lemma bPrimeC_ofReal (u : ℝ) : bPrimeC (u : ℂ) = MagicFunction.b.RealIntegrals.b' u := by
  simp [bPrimeC, MagicFunction.b.RealIntegrals.b', J₁'C, J₂'C, J₃'C, J₄'C, J₅'C, J₆'C,
    J₁', J₂', J₃', J₄', J₅', J₆']


open ModularForm ModularGroup UpperHalfPlane

lemma mem_Ioc_of_mem_uIoc {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) : t ∈ Ioc (0 : ℝ) 1 := by
  simpa using ht

private lemma continuousOn_ψT'_comp (z : ℝ → ℂ) (hz : Continuous z)
    (hIm : ∀ t ∈ Ι (0 : ℝ) 1, 0 < (z t).im) :
    ContinuousOn (fun t : ℝ => ψT' (z t)) (Ι (0 : ℝ) 1) := by
  let zsub : Ι (0 : ℝ) 1 → ℂ := fun t => z (t : ℝ)
  have hzsub : Continuous zsub := hz.comp continuous_subtype_val
  have him : ∀ t : Ι (0 : ℝ) 1, 0 < (zsub t).im := fun t => hIm (t : ℝ) t.2
  have hcont : Continuous fun t : Ι (0 : ℝ) 1 => ψT' (zsub t) := by
    refine
      SpherePacking.Integration.continuous_comp_upperHalfPlane_mk
        (α := Ι (0 : ℝ) 1) (ψT := ψT) (ψT' := ψT') (MagicFunction.b.PsiBounds.continuous_ψT)
        (z := zsub) hzsub him ?_
    intro t
    have hz_im : 0 < (zsub t).im := him t
    simp [ψT', zsub, hz_im]
  refine (continuousOn_iff_continuous_restrict).2 ?_
  simpa [Set.restrict] using hcont

private lemma norm_pi_mul_I : ‖(π : ℂ) * (Complex.I : ℂ)‖ = (π : ℝ) := by
  simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]

private lemma norm_pi_mul_I_mul_le (z : ℂ) {N : ℝ} (hz : ‖z‖ ≤ N) :
    ‖(π : ℂ) * (Complex.I : ℂ) * z‖ ≤ N * π := by
  calc
    ‖(π : ℂ) * (Complex.I : ℂ) * z‖ = ‖(π : ℂ) * (Complex.I : ℂ)‖ * ‖z‖ := by
      simp [mul_assoc]
    _ ≤ ‖(π : ℂ) * (Complex.I : ℂ)‖ * N :=
      mul_le_mul_of_nonneg_left hz (norm_nonneg ((π : ℂ) * (Complex.I : ℂ)))
    _ = N * π := by
      simpa [mul_comm, mul_assoc] using congrArg (fun r : ℝ => r * N) norm_pi_mul_I

private lemma exists_bound_norm_ψT'_comp_of_im_pos_all (z : ℝ → ℂ) (hz : Continuous z)
    (hIm : ∀ t : ℝ, 0 < (z t).im) :
    ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z t)‖ ≤ M := by
  have hcont : Continuous fun t : ℝ => ψT' (z t) := by
    refine
      SpherePacking.Integration.continuous_comp_upperHalfPlane_mk
        (ψT := ψT) (ψT' := ψT') (MagicFunction.b.PsiBounds.continuous_ψT) (z := z) hz hIm ?_
    intro t
    simp [ψT', hIm t]
  exact Integration.exists_bound_norm_uIoc_zero_one_of_continuous (fun t => ψT' (z t)) hcont

lemma ψI'_z₅'_eq (t : ℝ) (ht : t ∈ Ι (0 : ℝ) 1) :
    ψI' (z₅' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) := by
  simpa using
    (MagicFunction.b.Schwartz.J5Smooth.ψI'_z₅'_eq (t := t) (ht := mem_Ioc_of_mem_uIoc ht))

lemma exists_bound_norm_ψI'_z₅' :
    ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψI' (z₅' t)‖ ≤ M := by
  rcases MagicFunction.b.PsiBounds.exists_bound_norm_ψS_resToImagAxis_Ici_one with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro t ht
  have htIoc : t ∈ Ioc (0 : ℝ) 1 := mem_Ioc_of_mem_uIoc ht
  have ht0 : 0 < t := htIoc.1
  have ht1 : t ≤ 1 := htIoc.2
  have htIci : (1 : ℝ) ≤ 1 / t := by
    simpa using (one_le_div (show 0 < t from ht0)).2 ht1
  have hψS : ‖ψS.resToImagAxis (1 / t)‖ ≤ M := hM (1 / t) htIci
  have ht2 : t ^ 2 ≤ (1 : ℝ) := by
    simpa using (pow_le_pow_left₀ ht0.le ht1 2)
  have hM0 : 0 ≤ M := (norm_nonneg (ψS.resToImagAxis 1)).trans (hM 1 (by norm_num))
  have hEqIoc :
      ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
        ψI' (z₅' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) := by
    exact fun t a => b.Schwartz.J5Smooth.ψI'_z₅'_eq t a
  have hψIle : ‖ψI' (z₅' t)‖ ≤ M * t ^ 2 := by
    exact norm_modular_rewrite_Ioc_bound 2 ψS ψI' z₅' hEqIoc htIoc (hM (1 / t) htIci)
  calc
    ‖ψI' (z₅' t)‖ ≤ M * t ^ 2 := hψIle
    _ ≤ M := by simpa [mul_one] using (mul_le_mul_of_nonneg_left ht2 hM0)

lemma exists_bound_norm_ψT'_z₁' :
    ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z₁' t)‖ ≤ M := by
  rcases exists_bound_norm_ψI'_z₅' with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro t ht
  have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)
  have hEq : ψT' (z₁' t) = ψI' (z₅' t) :=
    MagicFunction.b.PsiParamRelations.ψT'_z₁'_eq_ψI'_z₅' (t := t) htIcc
  simpa [hEq] using hM t ht

lemma exists_bound_norm_ψT'_z₃' :
    ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z₃' t)‖ ≤ M := by
  rcases exists_bound_norm_ψI'_z₅' with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro t ht
  have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)
  have hEq : ψT' (z₃' t) = ψI' (z₅' t) :=
    MagicFunction.b.PsiParamRelations.ψT'_z₃'_eq_ψI'_z₅' (t := t) htIcc
  simpa [hEq] using hM t ht

lemma exists_bound_norm_ψT'_z₂' :
    ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z₂' t)‖ ≤ M := by
  simpa using
    exists_bound_norm_ψT'_comp_of_im_pos_all z₂' continuous_z₂' (fun t => im_z₂'_pos_all t)

lemma exists_bound_norm_ψT'_z₄' :
    ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z₄' t)‖ ≤ M := by
  simpa using
    exists_bound_norm_ψT'_comp_of_im_pos_all z₄' continuous_z₄' (fun t => im_z₄'_pos_all t)

private lemma norm_add_I_mul_le_two (a : ℂ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ha : ‖a‖ = 1) :
    ‖a + (Complex.I : ℂ) * (t : ℂ)‖ ≤ 2 := by
  calc
    ‖a + (Complex.I : ℂ) * (t : ℂ)‖ ≤ ‖a‖ + ‖(Complex.I : ℂ) * (t : ℂ)‖ := norm_add_le _ _
    _ = 1 + t := by simp [ha, Complex.norm_real, abs_of_nonneg ht.1]
    _ ≤ 2 := by nlinarith [ht.2]

lemma norm_z₃'_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖z₃' t‖ ≤ 2 := by
  have hz : z₃' t = (1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) := by
    simp [z₃'_eq_of_mem (t := t) ht]
  simpa [hz] using norm_add_I_mul_le_two (1 : ℂ) t ht (by simp)

private lemma norm_add_I_le_three (a : ℂ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (ha : ‖a‖ ≤ 1 + t) : ‖a + (Complex.I : ℂ)‖ ≤ 3 := by
  calc
    ‖a + (Complex.I : ℂ)‖ ≤ ‖a‖ + ‖(Complex.I : ℂ)‖ := norm_add_le _ _
    _ ≤ (1 + t) + 1 := by simpa using (add_le_add_right ha ‖(Complex.I : ℂ)‖)
    _ ≤ 3 := by nlinarith [ht.2]

lemma norm_z₂'_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖z₂' t‖ ≤ 3 := by
  have ht0 : 0 ≤ t := ht.1
  have hz : z₂' t = ((-1 : ℂ) + (t : ℂ)) + (Complex.I : ℂ) := by
    simp [z₂'_eq_of_mem (t := t) ht, add_comm]
  have ha : ‖(-1 : ℂ) + (t : ℂ)‖ ≤ 1 + t := by
    simpa [Complex.norm_real, abs_of_nonneg ht0] using norm_add_le (-1 : ℂ) (t : ℂ)
  simpa [hz] using norm_add_I_le_three ((-1 : ℂ) + (t : ℂ)) t ht ha

lemma norm_z₄'_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖z₄' t‖ ≤ 3 := by
  have ht0 : 0 ≤ t := ht.1
  have hz : z₄' t = ((1 : ℂ) + (-(t : ℂ))) + (Complex.I : ℂ) := by
    simp [z₄'_eq_of_mem (t := t) ht, sub_eq_add_neg, add_comm]
  have ha : ‖(1 : ℂ) + (-(t : ℂ))‖ ≤ 1 + t := by
    calc
      ‖(1 : ℂ) + (-(t : ℂ))‖ ≤ ‖(1 : ℂ)‖ + ‖-(t : ℂ)‖ := norm_add_le _ _
      _ = 1 + t := by simp [Complex.norm_real, abs_of_nonneg ht0]
  simpa [hz] using norm_add_I_le_three ((1 : ℂ) + (-(t : ℂ))) t ht ha

lemma norm_z₅'_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖z₅' t‖ ≤ 1 := by
  have ht0 : 0 ≤ t := ht.1
  simpa [z₅'_eq_of_mem (t := t) ht, Complex.norm_real, abs_of_nonneg ht0] using ht.2

lemma J₁'C_differentiable : Differentiable ℂ J₁'C := by
  intro u0
  -- Prove differentiability of the integral, then pull out the constant factor `I`.
  let base : ℝ → ℂ := fun t => ψT' (z₁' t)
  let k : ℝ → ℂ := fun t => (π : ℂ) * (Complex.I : ℂ) * z₁' t
  have hbase_cont : ContinuousOn base (Ι (0 : ℝ) 1) := by
    simpa [base] using
      continuousOn_ψT'_comp z₁' continuous_z₁' (fun t ht =>
        im_z₁'_pos (t := t) (mem_Ioc_of_mem_uIoc ht))
  have hk_cont : ContinuousOn k (Ι (0 : ℝ) 1) := by
    have : Continuous k := by
      simpa [k, mul_assoc] using (continuous_const.mul (continuous_const.mul continuous_z₁'))
    exact this.continuousOn
  obtain ⟨Mψ, hMψ⟩ := exists_bound_norm_ψT'_z₁'
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Mψ := by
    intro t ht
    simpa [base] using hMψ t ht
  have hk_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k t‖ ≤ 2 * π := by
    intro t ht
    have hz : ‖z₁' t‖ ≤ 2 := norm_z₁'_le_two t
    simpa [k, mul_assoc, mul_left_comm, mul_comm] using
      (norm_pi_mul_I_mul_le (z := z₁' t) (N := (2 : ℝ)) hz)
  have hdInt :=
    differentiableAt_intervalIntegral_mul_exp (u0 := u0) (Cbase := Mψ) (K := (2 * π))
      hbase_cont hk_cont hbase_bound hk_bound
  have hd :
      DifferentiableAt ℂ
        (fun u : ℂ =>
          (Complex.I : ℂ) * ∫ t in (0 : ℝ)..1, base t * Complex.exp (u * k t)) u0 := by
    simpa using (differentiableAt_const (c := (Complex.I : ℂ))).mul hdInt
  have hEq :
      (fun u : ℂ =>
          (Complex.I : ℂ) * ∫ t in (0 : ℝ)..1, base t * Complex.exp (u * k t)) = J₁'C := by
    funext u
    simp [J₁'C, base, k, mul_assoc, mul_comm]
  simpa [hEq] using hd

lemma J₂'C_differentiable : Differentiable ℂ J₂'C := by
  intro u0
  let base : ℝ → ℂ := fun t => ψT' (z₂' t)
  let k : ℝ → ℂ := fun t => (π : ℂ) * (Complex.I : ℂ) * z₂' t
  have hbase_cont : ContinuousOn base (Ι (0 : ℝ) 1) := by
    simpa [base] using
      continuousOn_ψT'_comp z₂' continuous_z₂' (fun t ht =>
        im_z₂'_pos (t := t) (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)))
  have hk_cont : ContinuousOn k (Ι (0 : ℝ) 1) := by
    have : Continuous k := by
      simpa [k, mul_assoc] using (continuous_const.mul (continuous_const.mul continuous_z₂'))
    exact this.continuousOn
  obtain ⟨Mψ, hMψ⟩ := exists_bound_norm_ψT'_z₂'
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Mψ := by
    intro t ht
    simpa [base] using hMψ t ht
  have hk_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k t‖ ≤ 3 * π := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)
    have hz : ‖z₂' t‖ ≤ 3 := norm_z₂'_le t htIcc
    simpa [k, mul_assoc, mul_left_comm, mul_comm] using
      (norm_pi_mul_I_mul_le (z := z₂' t) (N := (3 : ℝ)) hz)
  have hd :=
    differentiableAt_intervalIntegral_mul_exp (u0 := u0) (Cbase := Mψ) (K := (3 * π))
      hbase_cont hk_cont hbase_bound hk_bound
  have hEq :
      (fun u : ℂ => ∫ t in (0 : ℝ)..1, base t * Complex.exp (u * k t)) = J₂'C := by
    funext u
    simp [J₂'C, base, k, mul_assoc, mul_comm]
  simpa [hEq] using hd

lemma J₃'C_differentiable : Differentiable ℂ J₃'C := by
  intro u0
  let base : ℝ → ℂ := fun t => ψT' (z₃' t)
  let k : ℝ → ℂ := fun t => (π : ℂ) * (Complex.I : ℂ) * z₃' t
  have hbase_cont : ContinuousOn base (Ι (0 : ℝ) 1) := by
    simpa [base] using
      continuousOn_ψT'_comp z₃' continuous_z₃' (fun t ht =>
        im_z₃'_pos (t := t) (mem_Ioc_of_mem_uIoc ht))
  have hk_cont : ContinuousOn k (Ι (0 : ℝ) 1) := by
    have : Continuous k := by
      simpa [k, mul_assoc] using (continuous_const.mul (continuous_const.mul continuous_z₃'))
    exact this.continuousOn
  obtain ⟨Mψ, hMψ⟩ := exists_bound_norm_ψT'_z₃'
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Mψ := by
    intro t ht
    simpa [base] using hMψ t ht
  have hk_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k t‖ ≤ 2 * π := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)
    have hz : ‖z₃' t‖ ≤ 2 := norm_z₃'_le t htIcc
    simpa [k, mul_assoc, mul_left_comm, mul_comm] using
      (norm_pi_mul_I_mul_le (z := z₃' t) (N := (2 : ℝ)) hz)
  have hdInt :=
    differentiableAt_intervalIntegral_mul_exp (u0 := u0) (Cbase := Mψ) (K := (2 * π))
      hbase_cont hk_cont hbase_bound hk_bound
  have hd :
      DifferentiableAt ℂ
        (fun u : ℂ =>
          (Complex.I : ℂ) * ∫ t in (0 : ℝ)..1, base t * Complex.exp (u * k t)) u0 := by
    simpa using (differentiableAt_const (c := (Complex.I : ℂ))).mul hdInt
  have hEq :
      (fun u : ℂ =>
          (Complex.I : ℂ) * ∫ t in (0 : ℝ)..1, base t * Complex.exp (u * k t)) = J₃'C := by
    funext u
    simp [J₃'C, base, k, mul_assoc, mul_comm]
  simpa [hEq] using hd

lemma J₄'C_differentiable : Differentiable ℂ J₄'C := by
  intro u0
  let base0 : ℝ → ℂ := fun t => ψT' (z₄' t)
  let base : ℝ → ℂ := fun t => (-1 : ℂ) * base0 t
  let k : ℝ → ℂ := fun t => (π : ℂ) * (Complex.I : ℂ) * z₄' t
  have hbase0_cont : ContinuousOn base0 (Ι (0 : ℝ) 1) := by
    simpa [base0] using
      continuousOn_ψT'_comp z₄' continuous_z₄' (fun t ht =>
        im_z₄'_pos (t := t) (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)))
  have hbase_cont : ContinuousOn base (Ι (0 : ℝ) 1) :=
    (continuousOn_const.mul hbase0_cont)
  have hk_cont : ContinuousOn k (Ι (0 : ℝ) 1) := by
    have : Continuous k := by
      simpa [k, mul_assoc] using (continuous_const.mul (continuous_const.mul continuous_z₄'))
    exact this.continuousOn
  obtain ⟨Mψ, hMψ⟩ := exists_bound_norm_ψT'_z₄'
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Mψ := by
    intro t ht
    simpa [base, base0] using hMψ t ht
  have hk_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k t‖ ≤ 3 * π := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)
    have hz : ‖z₄' t‖ ≤ 3 := norm_z₄'_le t htIcc
    simpa [k, mul_assoc, mul_left_comm, mul_comm] using
      (norm_pi_mul_I_mul_le (z := z₄' t) (N := (3 : ℝ)) hz)
  have hd :=
    differentiableAt_intervalIntegral_mul_exp (u0 := u0) (Cbase := Mψ) (K := (3 * π))
      hbase_cont hk_cont hbase_bound hk_bound
  have hEq :
      (fun u : ℂ => ∫ t in (0 : ℝ)..1, base t * Complex.exp (u * k t)) = J₄'C := by
    funext u
    simp [J₄'C, base, base0, k, mul_assoc, mul_comm]
  simpa [hEq] using hd

lemma J₅'C_differentiable : Differentiable ℂ J₅'C := by
  intro u0
  let base0 : ℝ → ℂ := fun t => (Complex.I : ℂ) * ψI' (z₅' t)
  let base : ℝ → ℂ := fun t => (-2 : ℂ) * base0 t
  let k : ℝ → ℂ := fun t => (π : ℂ) * (Complex.I : ℂ) * z₅' t
  have hbase0_cont : ContinuousOn base0 (Ι (0 : ℝ) 1) := by
    -- `ψI` is continuous on `ℍ`, hence on `Ioc`.
    -- Use `ψI' = ψI` on `Ioc` since `0 < Im (z₅' t)`.
    have hψI : Continuous ψI := b.PsiBounds.continuous_ψI
    have hcont : Continuous fun t : Ioc (0 : ℝ) 1 => base0 (t : ℝ) := by
      let zH : Ioc (0 : ℝ) 1 → ℍ :=
        fun t => ⟨z₅' (t : ℝ), im_z₅'_pos (t := (t : ℝ)) t.2⟩
      have hzH : Continuous zH := by
        have hz : Continuous fun t : Ioc (0 : ℝ) 1 => z₅' (t : ℝ) :=
          continuous_z₅'.comp continuous_subtype_val
        simpa [zH] using
          Continuous.upperHalfPlaneMk hz (fun t => im_z₅'_pos (t := (t : ℝ)) t.2)
      have hψ : Continuous fun t : Ioc (0 : ℝ) 1 => ψI (zH t) := hψI.comp hzH
      have hEq : (fun t : Ioc (0 : ℝ) 1 => ψI' (z₅' (t : ℝ))) = fun t => ψI (zH t) := by
        funext t
        have hz_im : 0 < (z₅' (t : ℝ)).im := im_z₅'_pos (t := (t : ℝ)) t.2
        simp [ψI', zH, hz_im]
      have hψ' : Continuous fun t : Ioc (0 : ℝ) 1 => ψI' (z₅' (t : ℝ)) := by
        simpa [hEq] using hψ
      simpa [base0] using (continuous_const.mul hψ')
    have hOn : ContinuousOn base0 (Ioc (0 : ℝ) 1) := by
      refine (continuousOn_iff_continuous_restrict).2 ?_
      simpa [Set.restrict] using hcont
    simpa using hOn
  have hbase_cont : ContinuousOn base (Ι (0 : ℝ) 1) :=
    (continuousOn_const.mul hbase0_cont)
  have hk_cont : ContinuousOn k (Ι (0 : ℝ) 1) := by
    have : Continuous k := by
      simpa [k, mul_assoc] using (continuous_const.mul (continuous_const.mul continuous_z₅'))
    exact this.continuousOn
  obtain ⟨Mψ, hMψ⟩ := exists_bound_norm_ψI'_z₅'
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ 2 * Mψ := by
    intro t ht
    have h0 : ‖base0 t‖ ≤ Mψ := by simpa [base0] using hMψ t ht
    calc
      ‖base t‖ = ‖(-2 : ℂ)‖ * ‖base0 t‖ := by simp [base]
      _ ≤ ‖(-2 : ℂ)‖ * Mψ := by gcongr
      _ = 2 * Mψ := by simp
  have hk_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k t‖ ≤ π := by
    intro t ht
    simpa [k, mul_assoc, mul_left_comm, mul_comm] using
      (norm_pi_mul_I_mul_le (z := z₅' t) (N := (1 : ℝ))
        (norm_z₅'_le t (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht))))
  have hd :=
    differentiableAt_intervalIntegral_mul_exp (u0 := u0) (Cbase := (2 * Mψ)) (K := π)
      hbase_cont hk_cont hbase_bound hk_bound
  have hEq :
      (fun u : ℂ => ∫ t in (0 : ℝ)..1, base t * Complex.exp (u * k t)) = J₅'C := by
    funext u
    -- Pull the constant `(-2)` out of the integral to match the definition.
    simp [J₅'C, base, base0, k, mul_assoc, mul_left_comm, mul_comm]
  simpa [hEq] using hd

set_option maxHeartbeats 1000000 in
-- The `J₆'C` differentiability proof is large and needs more heartbeats.
lemma J₆'C_differentiableOn : DifferentiableOn ℂ J₆'C rightHalfPlane := by
  intro u0 hu0
  have hu0re : 0 < u0.re := by simpa [rightHalfPlane] using hu0
  -- Work with `μ = volume.restrict (Ici 1)`.
  let μ : Measure ℝ := μIciOne
  -- Rewrite `ψS' (z₆' t)` on `t ≥ 1` using the restriction to the imaginary axis.
  have hψS'_eq :
      ∀ t : ℝ, t ∈ Set.Ici (1 : ℝ) → ψS' (z₆' t) = ψS.resToImagAxis t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    have hz : z₆' t = (Complex.I : ℂ) * (t : ℂ) := by
      simpa using (z₆'_eq_of_mem (t := t) ht)
    -- Both sides are defined by restricting `ψS` to the positive imaginary axis.
    simp [hz, ψS', Function.resToImagAxis, ResToImagAxis, ht0, mul_comm]
  -- Use the simplified integrand `ψS.resToImagAxis t * exp (-(π : ℂ) * u * t)`.
  let base : ℝ → ℂ := fun t => (Complex.I : ℂ) * ψS.resToImagAxis t
  let k : ℝ → ℂ := fun t => (-(π : ℂ)) * (t : ℂ)
  let F : ℂ → ℝ → ℂ := fun u t => base t * Complex.exp (u * k t)
  let F' : ℂ → ℝ → ℂ := fun u t => base t * k t * Complex.exp (u * k t)
  have hcont_res : ContinuousOn ψS.resToImagAxis (Set.Ici (1 : ℝ)) :=
    Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS) MagicFunction.b.PsiBounds.continuous_ψS
  have hcont_base : ContinuousOn base (Set.Ici (1 : ℝ)) := by
    simpa [base] using (continuousOn_const.mul hcont_res)
  have hk_cont : ContinuousOn k (Set.Ici (1 : ℝ)) := by
    fun_prop
  have hF_meas :
      ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (F u) μ := by
    refine Filter.Eventually.of_forall (fun u => ?_)
    have hmul : ContinuousOn (fun t : ℝ => u * k t) (Set.Ici (1 : ℝ)) :=
      (continuousOn_const.mul hk_cont)
    have hexp : ContinuousOn (fun t : ℝ => Complex.exp (u * k t)) (Set.Ici (1 : ℝ)) := by
      exact ContinuousOn.cexp hmul
    have hcont : ContinuousOn (fun t : ℝ => F u t) (Set.Ici (1 : ℝ)) := hcont_base.mul hexp
    simpa [μ] using (hcont.aestronglyMeasurable (μ := (volume : Measure ℝ)) measurableSet_Ici)
  have hF'_meas :
      AEStronglyMeasurable (F' u0) μ := by
    have hmul : ContinuousOn (fun t : ℝ => u0 * k t) (Set.Ici (1 : ℝ)) :=
      (continuousOn_const.mul hk_cont)
    have hexp : ContinuousOn (fun t : ℝ => Complex.exp (u0 * k t)) (Set.Ici (1 : ℝ)) := by
      exact ContinuousOn.cexp hmul
    have hcont : ContinuousOn (fun t : ℝ => F' u0 t) (Set.Ici (1 : ℝ)) := by
      have hbk : ContinuousOn (fun t : ℝ => base t * k t) (Set.Ici (1 : ℝ)) :=
        hcont_base.mul hk_cont
      simpa [F'] using (hbk.mul hexp)
    have hmeas := (hcont.aestronglyMeasurable (μ := (volume : Measure ℝ)) measurableSet_Ici)
    simpa [F', μ, mul_assoc] using hmeas
  -- Bounds on `ψS.resToImagAxis` for `t ≥ 1`.
  obtain ⟨Mψ, hMψ⟩ := MagicFunction.b.PsiBounds.exists_bound_norm_ψS_resToImagAxis_Ici_one
  have hbase_bound : ∀ t : ℝ, 1 ≤ t → ‖base t‖ ≤ Mψ := by
    intro t ht
    have : ‖ψS.resToImagAxis t‖ ≤ Mψ := hMψ t ht
    simpa [base] using (by
      simpa [norm_mul] using (mul_le_mul_of_nonneg_left this (norm_nonneg (Complex.I : ℂ))))
  -- Integrability of `F u0` on `Ici 1` using the decay of `exp (-(π : ℂ) * u0 * t)`.
  have hF_int : Integrable (F u0) μ := by
    have hmeas : AEStronglyMeasurable (F u0) μ := hF_meas.self_of_nhds
    let b : ℝ := Real.pi * u0.re
    have hb : 0 < b := by positivity
    let g : ℝ → ℝ := fun t => Real.exp (-b * t)
    have hExpIci : IntegrableOn g (Set.Ici (1 : ℝ)) (volume : Measure ℝ) := by
      -- `n = 0` in the shared lemma: `t^0 * exp(-b*t)` on `[1,∞)`.
      simpa [g, pow_zero, one_mul] using
        (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 0) (b := b) hb)
    have hG_int :
        Integrable (fun t : ℝ => (Mψ : ℝ) * Real.exp (-b * t)) μ := by
      have : IntegrableOn (fun t : ℝ => (Mψ : ℝ) * Real.exp (-b * t)) (Set.Ici (1 : ℝ))
          (volume : Measure ℝ) :=
        hExpIci.const_mul Mψ
      simpa [μ, MeasureTheory.IntegrableOn] using this
    refine Integrable.mono' hG_int hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
    intro t ht
    have ht' : 1 ≤ t := ht
    have hb0 : ‖base t‖ ≤ Mψ := hbase_bound t ht'
    have hexp :
        ‖Complex.exp (u0 * k t)‖ = Real.exp (-b * t) := by
      have hk_re : (k t).re = -Real.pi * t := by simp [k]
      have hk_im : (k t).im = 0 := by simp [k]
      have hre : (u0 * k t).re = -Real.pi * u0.re * t := by
        -- `k t` is real, so only the real part of `u0` contributes.
        simp [mul_re, hk_re, hk_im, mul_left_comm, mul_comm]
      simp [Complex.norm_exp, hre, b, mul_comm]
    calc
      ‖F u0 t‖ = ‖base t‖ * ‖Complex.exp (u0 * k t)‖ := by
        simp [F]
      _ ≤ Mψ * Real.exp (-b * t) := by
        -- Use the bounds on `base` and the exact expression for `‖exp‖`.
        have :
            ‖base t‖ * ‖Complex.exp (u0 * k t)‖ ≤ Mψ * ‖Complex.exp (u0 * k t)‖ :=
          mul_le_mul_of_nonneg_right hb0 (norm_nonneg _)
        simpa [hexp] using this
  -- Uniform bound for `F'` on a ball around `u0`.
  let ε : ℝ := u0.re / 2
  have ε_pos : 0 < ε := by
    have : 0 < u0.re / (2 : ℝ) := div_pos hu0re (by norm_num)
    simpa [ε] using this
  let b : ℝ := Real.pi * ε
  have hb : 0 < b := by positivity
  let bound : ℝ → ℝ := fun t => (Mψ * Real.pi) * t * Real.exp (-b * t)
  have bound_int : Integrable bound μ := by
    have hIci :
        IntegrableOn (fun t : ℝ => t * Real.exp (-b * t)) (Set.Ici (1 : ℝ))
          (volume : Measure ℝ) := by
      -- `n = 1` in the shared lemma: `t^1 * exp(-b*t)` on `[1,∞)`.
      simpa [pow_one] using
        (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 1) (b := b) hb)
    have : IntegrableOn bound (Set.Ici (1 : ℝ)) (volume : Measure ℝ) := by
      -- pull out the constant `(Mψ * π)`.
      simpa [bound, mul_assoc, mul_left_comm, mul_comm] using (hIci.const_mul (Mψ * Real.pi))
    simpa [μ, MeasureTheory.IntegrableOn] using this
  have hre_lower :
      ∀ u : ℂ, u ∈ Metric.ball u0 ε → (u0.re / 2) ≤ u.re := by
    intro u hu
    have hu' : ‖u - u0‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hu
    have hre : |u.re - u0.re| ≤ ‖u - u0‖ := by
      simpa using (abs_re_le_norm (u - u0))
    grind only [= abs.eq_1, = max_def]
  have h_bound :
      ∀ᵐ t ∂μ, ∀ u ∈ Metric.ball u0 ε, ‖F' u t‖ ≤ bound t := by
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
    intro t ht u hu
    have ht' : 1 ≤ t := ht
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht'
    have hb0 : ‖base t‖ ≤ Mψ := hbase_bound t ht'
    have hu_re : (u0.re / 2) ≤ u.re := hre_lower u hu
    have hexp_le : ‖Complex.exp (u * k t)‖ ≤ Real.exp (-b * t) := by
      have hk_re : (k t).re = -Real.pi * t := by simp [k]
      have hk_im : (k t).im = 0 := by simp [k]
      have hre : (u * k t).re = -Real.pi * u.re * t := by
        simp [mul_re, hk_re, hk_im, mul_left_comm, mul_comm]
      have hre_le : -Real.pi * u.re * t ≤ -Real.pi * (u0.re / 2) * t := by
        have hneg : (-Real.pi * t) ≤ 0 := by
          have : 0 ≤ Real.pi * t := mul_nonneg Real.pi_pos.le ht0
          linarith
        -- `u.re` is bounded below in the ball around `u0`, and `(-π*t) ≤ 0`.
        have hmul : (-Real.pi * t) * u.re ≤ (-Real.pi * t) * (u0.re / 2) :=
          (mul_le_mul_of_nonpos_left hu_re hneg)
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      have : Real.exp ((u * k t).re) ≤ Real.exp (-b * t) := by
        -- Note: `b = π * (u0.re / 2)`.
        simpa [hre, b, ε, mul_assoc, mul_left_comm, mul_comm] using Real.exp_le_exp.2 hre_le
      simpa [Complex.norm_exp] using this
    have hk_norm : ‖k t‖ = Real.pi * t := by
      -- `k t = -(π * t)` is a real number, and `t ≥ 0` on `Ici 1`.
      simp [k, Complex.norm_real, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg ht0, mul_comm]
    calc
      ‖F' u t‖ = ‖base t‖ * (‖k t‖ * ‖Complex.exp (u * k t)‖) := by
        simp [F', mul_assoc]
      _ ≤ Mψ * ((Real.pi * t) * Real.exp (-b * t)) := by
        have h1 :
            ‖k t‖ * ‖Complex.exp (u * k t)‖ ≤ (Real.pi * t) * Real.exp (-b * t) := by
          -- bound `‖k t‖` exactly and `‖exp‖` by `hexp_le`.
          have h2 : ‖k t‖ ≤ Real.pi * t :=
            le_of_eq hk_norm
          exact mul_le_mul h2 hexp_le (norm_nonneg _) (mul_nonneg Real.pi_pos.le ht0)
        have h2 :
            ‖base t‖ * (‖k t‖ * ‖Complex.exp (u * k t)‖) ≤
              Mψ * ((Real.pi * t) * Real.exp (-b * t)) := by
          have hstep1 :
              ‖base t‖ * (‖k t‖ * ‖Complex.exp (u * k t)‖) ≤
                ‖base t‖ * ((Real.pi * t) * Real.exp (-b * t)) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg (base t))
          have hstep2 :
              ‖base t‖ * ((Real.pi * t) * Real.exp (-b * t)) ≤
                Mψ * ((Real.pi * t) * Real.exp (-b * t)) :=
            mul_le_mul_of_nonneg_right hb0 (by positivity)
          exact hstep1.trans hstep2
        simpa [mul_assoc, mul_left_comm, mul_comm] using h2
      _ = bound t := by
        simp [bound, mul_assoc, mul_left_comm, mul_comm]
  have h_diff :
      ∀ᵐ t ∂μ, ∀ u ∈ Metric.ball u0 ε,
        HasDerivAt (fun u : ℂ => F u t) (F' u t) u := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    intro u hu
    have hmul : HasDerivAt (fun u : ℂ => u * k t) (k t) u :=
      (hasDerivAt_mul_const (k t) (x := u))
    have hexp :
        HasDerivAt (fun u : ℂ => Complex.exp (u * k t)) (Complex.exp (u * k t) * k t) u :=
      HasDerivAt.comp u (Complex.hasDerivAt_exp (u * k t)) hmul
    simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using hexp.const_mul (base t)
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := F) (x₀ := u0) (s := Metric.ball u0 ε) (hs := Metric.ball_mem_nhds u0 ε_pos)
      (bound := bound) (hF_meas := hF_meas) (hF_int := hF_int) (hF'_meas := hF'_meas)
      (h_bound := h_bound) (bound_integrable := bound_int) (h_diff := h_diff)
  have hEq : (fun u : ℂ => (-2 : ℂ) * ∫ t, F u t ∂μ) = J₆'C := by
    funext u
    -- Convert both sides to integrals over `Ici 1`.
    simp only [J₆'C, μ]
    have hμ : (∫ t, F u t ∂μIciOne) = ∫ t in Set.Ici (1 : ℝ), F u t := by
      simp [μIciOne]
    -- Match the integrands almost everywhere on `Ici 1`.
    have hInt :
        (∫ t in Set.Ici (1 : ℝ), F u t) =
          ∫ t in Set.Ici (1 : ℝ),
            (Complex.I : ℂ) * ψS' (z₆' t) *
              Complex.exp (π * (Complex.I : ℂ) * u * (z₆' t)) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
      intro t ht
      have ht0 : 0 < t := by
        have : (0 : ℝ) < 1 := by norm_num
        exact lt_of_lt_of_le this ht
      have hz : z₆' t = (Complex.I : ℂ) * (t : ℂ) := by
        simpa using (z₆'_eq_of_mem (t := t) ht)
      have hψ : ψS' (z₆' t) = ψS.resToImagAxis t := hψS'_eq t ht
      -- Rewrite `F` and use `z₆' t = I * t` to simplify the exponent.
      have hψ' : ψS' ((Complex.I : ℂ) * (t : ℂ)) = ψS.resToImagAxis t := by
        simpa [hz] using hψ
      have hIexp := I_mul_I_mul (↑t * ↑π)
      have hIexp' :
          u * ((Complex.I : ℂ) * (Complex.I * ((t : ℂ) * (π : ℂ)))) =
            -(u * ((t : ℂ) * (π : ℂ))) := by
        simp [hIexp]
      -- `mul_assoc` is intentionally omitted here to avoid linter warnings.
      simp [F, base, k, hz, hψ', hIexp', mul_left_comm, mul_comm]
    -- Finish by rewriting the integral.
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hμ.trans hInt)
  have hdiffAt :
      DifferentiableAt ℂ (fun u : ℂ => (-2 : ℂ) * ∫ t, F u t ∂μ) u0 :=
    (h.2.differentiableAt.const_mul (-2 : ℂ))
  have hdiffAtJ : DifferentiableAt ℂ J₆'C u0 := by
    -- Rewrite the target using the proven integral identity.
    rw [← hEq]
    exact hdiffAt
  exact hdiffAtJ.differentiableWithinAt

/-- `bPrimeC` is analytic on the right half-plane. -/
public lemma bPrimeC_analyticOnNhd :
    AnalyticOnNhd ℂ bPrimeC rightHalfPlane := by
  simpa [bPrimeC] using
    (((((J₁'C_differentiable.differentiableOn.add J₂'C_differentiable.differentiableOn).add
              J₃'C_differentiable.differentiableOn).add J₄'C_differentiable.differentiableOn).add
            J₅'C_differentiable.differentiableOn).add J₆'C_differentiableOn).analyticOnNhd
        rightHalfPlane_isOpen

end

end MagicFunction.g.CohnElkies.IntegralReps
