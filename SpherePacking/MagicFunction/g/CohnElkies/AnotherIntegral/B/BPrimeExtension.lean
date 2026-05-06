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
open SpherePacking intervalIntegral
open MagicFunction.b.RealIntegrals MagicFunction.Parametrisations

noncomputable section

/-- Complexified `J₁'`. -/
def J₁'C (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1,
  (Complex.I : ℂ) * ψT' (z₁' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₁' t))

/-- Complexified `J₂'`. -/
def J₂'C (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1,
  ψT' (z₂' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₂' t))

/-- Complexified `J₃'`. -/
def J₃'C (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1,
  (Complex.I : ℂ) * ψT' (z₃' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₃' t))

/-- Complexified `J₄'`. -/
def J₄'C (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1,
  (-1 : ℂ) * ψT' (z₄' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₄' t))

/-- Complexified `J₅'`. -/
def J₅'C (u : ℂ) : ℂ := -2 * ∫ t in (0 : ℝ)..1,
  (Complex.I : ℂ) * ψI' (z₅' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₅' t))

/-- Complexified `J₆'`. -/
def J₆'C (u : ℂ) : ℂ := -2 * ∫ t in Set.Ici (1 : ℝ),
  (Complex.I : ℂ) * ψS' (z₆' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₆' t))

/-- Analytic extension of `b'` to complex parameters, defined as the sum of `J₁'C`, ..., `J₆'C`. -/
public def bPrimeC (u : ℂ) : ℂ :=
  J₁'C u + J₂'C u + J₃'C u + J₄'C u + J₅'C u + J₆'C u

/-- On real parameters, `bPrimeC` agrees with the real function `b'`. -/
public lemma bPrimeC_ofReal (u : ℝ) : bPrimeC (u : ℂ) = MagicFunction.b.RealIntegrals.b' u := by
  simp [bPrimeC, MagicFunction.b.RealIntegrals.b', J₁'C, J₂'C, J₃'C, J₄'C, J₅'C, J₆'C,
    J₁', J₂', J₃', J₄', J₅', J₆']

open ModularForm ModularGroup UpperHalfPlane

lemma mem_Ioc_of_mem_uIoc {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht

private lemma continuousOn_ψT'_comp (z : ℝ → ℂ) (hz : Continuous z)
    (hIm : ∀ t ∈ Ι (0 : ℝ) 1, 0 < (z t).im) :
    ContinuousOn (fun t : ℝ => ψT' (z t)) (Ι (0 : ℝ) 1) :=
  continuousOn_iff_continuous_restrict.2 <| by
    simpa [Set.restrict] using SpherePacking.Integration.continuous_comp_upperHalfPlane_mk
      (α := Ι (0 : ℝ) 1) (ψT := ψT) (ψT' := ψT') MagicFunction.b.PsiBounds.continuous_ψT
      (z := fun t : Ι (0 : ℝ) 1 => z (t : ℝ)) (hz.comp continuous_subtype_val)
      (fun t => hIm (t : ℝ) t.2) (fun t => by simp [ψT', hIm (t : ℝ) t.2])

private lemma norm_pi_mul_I_mul_le (z : ℂ) {N : ℝ} (hz : ‖z‖ ≤ N) :
    ‖(π : ℂ) * (Complex.I : ℂ) * z‖ ≤ N * π := by
  rw [norm_mul, show ‖(π : ℂ) * (Complex.I : ℂ)‖ = (π : ℝ) by
    simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le], mul_comm]
  gcongr

private lemma exists_bound_norm_ψT'_comp_of_im_pos_all (z : ℝ → ℂ) (hz : Continuous z)
    (hIm : ∀ t : ℝ, 0 < (z t).im) :
    ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z t)‖ ≤ M :=
  Integration.exists_bound_norm_uIoc_zero_one_of_continuous (fun t => ψT' (z t))
    (SpherePacking.Integration.continuous_comp_upperHalfPlane_mk (ψT := ψT) (ψT' := ψT')
      MagicFunction.b.PsiBounds.continuous_ψT (z := z) hz hIm fun t => by simp [ψT', hIm t])

lemma ψI'_z₅'_eq (t : ℝ) (ht : t ∈ Ι (0 : ℝ) 1) :
    ψI' (z₅' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) := by
  simpa using MagicFunction.b.Schwartz.J5Smooth.ψI'_z₅'_eq (ht := mem_Ioc_of_mem_uIoc ht)

lemma exists_bound_norm_ψI'_z₅' :
    ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψI' (z₅' t)‖ ≤ M := by
  obtain ⟨M, hM⟩ := MagicFunction.b.PsiBounds.exists_bound_norm_ψS_resToImagAxis_Ici_one
  refine ⟨M, fun t ht => ?_⟩
  have htIoc : t ∈ Ioc (0 : ℝ) 1 := mem_Ioc_of_mem_uIoc ht
  refine (norm_modular_rewrite_Ioc_bound 2 ψS ψI' z₅' b.Schwartz.J5Smooth.ψI'_z₅'_eq htIoc
    (hM (1 / t) (by simpa using (one_le_div htIoc.1).2 htIoc.2))).trans ?_
  simpa [mul_one] using mul_le_mul_of_nonneg_left
    (by simpa using pow_le_pow_left₀ htIoc.1.le htIoc.2 2 : t ^ 2 ≤ (1 : ℝ))
    ((norm_nonneg (ψS.resToImagAxis 1)).trans (hM 1 (by norm_num)))

lemma exists_bound_norm_ψT'_z₁' : ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z₁' t)‖ ≤ M :=
  exists_bound_norm_ψI'_z₅'.imp fun _ hM t ht => by
    simpa [MagicFunction.b.PsiParamRelations.ψT'_z₁'_eq_ψI'_z₅' (t := t)
      (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht))] using hM t ht

lemma exists_bound_norm_ψT'_z₃' : ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z₃' t)‖ ≤ M :=
  exists_bound_norm_ψI'_z₅'.imp fun _ hM t ht => by
    simpa [MagicFunction.b.PsiParamRelations.ψT'_z₃'_eq_ψI'_z₅' (t := t)
      (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht))] using hM t ht

lemma exists_bound_norm_ψT'_z₂' : ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z₂' t)‖ ≤ M := by
  simpa using exists_bound_norm_ψT'_comp_of_im_pos_all z₂' continuous_z₂' im_z₂'_pos_all

lemma exists_bound_norm_ψT'_z₄' : ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z₄' t)‖ ≤ M := by
  simpa using exists_bound_norm_ψT'_comp_of_im_pos_all z₄' continuous_z₄' im_z₄'_pos_all

lemma norm_z₃'_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖z₃' t‖ ≤ 2 := by
  have hz : z₃' t = (1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) := by simp [z₃'_eq_of_mem (t := t) ht]
  rw [hz]
  have h := norm_add_le (1 : ℂ) ((Complex.I : ℂ) * (t : ℂ))
  simp [Complex.norm_real, abs_of_nonneg ht.1] at h; linarith [ht.2]

private lemma norm_add_I_le_three (a : ℂ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (ha : ‖a‖ ≤ 1 + t) : ‖a + (Complex.I : ℂ)‖ ≤ 3 := by
  have h := norm_add_le a (Complex.I : ℂ); simp at h; linarith [ht.2]

lemma norm_z₂'_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖z₂' t‖ ≤ 3 :=
  (show z₂' t = ((-1 : ℂ) + (t : ℂ)) + (Complex.I : ℂ) by
    simp [z₂'_eq_of_mem (t := t) ht, add_comm]) ▸ norm_add_I_le_three _ t ht
    (by simpa [Complex.norm_real, abs_of_nonneg ht.1] using norm_add_le (-1 : ℂ) (t : ℂ))

lemma norm_z₄'_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖z₄' t‖ ≤ 3 :=
  (show z₄' t = ((1 : ℂ) + (-(t : ℂ))) + (Complex.I : ℂ) by
    simp [z₄'_eq_of_mem (t := t) ht, sub_eq_add_neg, add_comm]) ▸ norm_add_I_le_three _ t ht
    ((norm_add_le _ _).trans (by simp [Complex.norm_real, abs_of_nonneg ht.1]))

lemma norm_z₅'_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖z₅' t‖ ≤ 1 := by
  simpa [z₅'_eq_of_mem (t := t) ht, Complex.norm_real, abs_of_nonneg ht.1] using ht.2

/-- Shared differentiability wrapper for `J₁'C`–`J₅'C`:
`u ↦ ∫ t in (0:ℝ)..1, ψ (z t) * exp (π*I*u*z t)` is differentiable, given continuity of the
composed map, continuity of `z`, and `‖ψ (z t)‖ ≤ Mψ`, `‖z t‖ ≤ Cz` on `Ι 0 1`. -/
private lemma integral_ψ_exp_differentiable
    {ψ : ℂ → ℂ} {z : ℝ → ℂ} {Mψ Cz : ℝ}
    (hψz_cont : ContinuousOn (fun t : ℝ => ψ (z t)) (Ι (0 : ℝ) 1))
    (hz_cont : Continuous z)
    (hψz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖ψ (z t)‖ ≤ Mψ)
    (hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ Cz) :
    Differentiable ℂ
      (fun u : ℂ => ∫ t in (0 : ℝ)..1,
        ψ (z t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z t)) := fun u0 => by
  let k : ℝ → ℂ := fun t => (π : ℂ) * (Complex.I : ℂ) * z t
  have hEq : (fun u : ℂ => ∫ t in (0 : ℝ)..1, ψ (z t) * Complex.exp (u * k t)) =
        fun u : ℂ => ∫ t in (0 : ℝ)..1,
          ψ (z t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z t) := by
    funext u; congr 1; funext t; congr 2; simp [k, mul_left_comm, mul_comm]
  exact hEq ▸ differentiableAt_intervalIntegral_mul_exp (u0 := u0) (Cbase := Mψ) (K := Cz * π)
    hψz_cont (continuous_const.mul hz_cont).continuousOn hψz_bound
    (fun t ht => norm_pi_mul_I_mul_le (z := z t) (N := Cz) (hz_bound t ht))

lemma J₁'C_differentiable : Differentiable ℂ J₁'C :=
  let ⟨_, hMψ⟩ := exists_bound_norm_ψT'_z₁'
  (show J₁'C = fun u : ℂ => (Complex.I : ℂ) * ∫ t in (0 : ℝ)..1,
      ψT' (z₁' t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z₁' t) from
    funext fun u => by simp [J₁'C, ← intervalIntegral.integral_const_mul, mul_assoc]) ▸
    (differentiable_const (Complex.I : ℂ)).mul (integral_ψ_exp_differentiable (Cz := 2)
      (continuousOn_ψT'_comp z₁' continuous_z₁' fun t ht => im_z₁'_pos (mem_Ioc_of_mem_uIoc ht))
      continuous_z₁' hMψ (fun t _ => norm_z₁'_le_two t))

lemma J₂'C_differentiable : Differentiable ℂ J₂'C :=
  let ⟨_, hMψ⟩ := exists_bound_norm_ψT'_z₂'
  integral_ψ_exp_differentiable (Cz := 3)
    (continuousOn_ψT'_comp z₂' continuous_z₂'
      fun t ht => im_z₂'_pos (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)))
    continuous_z₂' hMψ (fun t ht => norm_z₂'_le t (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)))

lemma J₃'C_differentiable : Differentiable ℂ J₃'C :=
  let ⟨_, hMψ⟩ := exists_bound_norm_ψT'_z₃'
  (show J₃'C = fun u : ℂ => (Complex.I : ℂ) * ∫ t in (0 : ℝ)..1,
      ψT' (z₃' t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z₃' t) from
    funext fun u => by simp [J₃'C, ← intervalIntegral.integral_const_mul, mul_assoc]) ▸
    (differentiable_const (Complex.I : ℂ)).mul (integral_ψ_exp_differentiable (Cz := 2)
      (continuousOn_ψT'_comp z₃' continuous_z₃' fun t ht => im_z₃'_pos (mem_Ioc_of_mem_uIoc ht))
      continuous_z₃' hMψ (fun t ht => norm_z₃'_le t (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht))))

lemma J₄'C_differentiable : Differentiable ℂ J₄'C :=
  let ⟨_, hMψ⟩ := exists_bound_norm_ψT'_z₄'
  (show J₄'C = fun u : ℂ => (-1 : ℂ) * ∫ t in (0 : ℝ)..1,
      ψT' (z₄' t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z₄' t) from
    funext fun u => by simp [J₄'C, ← intervalIntegral.integral_const_mul, mul_assoc]) ▸
    (differentiable_const (-1 : ℂ)).mul (integral_ψ_exp_differentiable (Cz := 3)
      (continuousOn_ψT'_comp z₄' continuous_z₄'
        fun t ht => im_z₄'_pos (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)))
      continuous_z₄' hMψ (fun t ht => norm_z₄'_le t (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht))))

/-- Continuity of `t ↦ ψI' (z₅' t)` on `Ι 0 1`, using `ψI' = ψI` on the upper half-plane. -/
private lemma continuousOn_ψI'_z₅' :
    ContinuousOn (fun t : ℝ => ψI' (z₅' t)) (Ι (0 : ℝ) 1) := by
  have hcont : Continuous fun t : Ioc (0 : ℝ) 1 => ψI' (z₅' (t : ℝ)) := by
    let zH : Ioc (0 : ℝ) 1 → ℍ := fun t => ⟨z₅' (t : ℝ), im_z₅'_pos (t := (t : ℝ)) t.2⟩
    have hzH : Continuous zH := by
      simpa [zH] using Continuous.upperHalfPlaneMk
        (continuous_z₅'.comp continuous_subtype_val : Continuous fun t : Ioc (0:ℝ) 1 => z₅' (t:ℝ))
        (fun t => im_z₅'_pos (t := (t : ℝ)) t.2)
    have hEq : (fun t : Ioc (0 : ℝ) 1 => ψI' (z₅' (t : ℝ))) = fun t => ψI (zH t) := by
      funext t; simp [ψI', zH, im_z₅'_pos (t := (t : ℝ)) t.2]
    simpa [hEq] using b.PsiBounds.continuous_ψI.comp hzH
  simpa using (continuousOn_iff_continuous_restrict).2 (by simpa [Set.restrict] using hcont)

lemma J₅'C_differentiable : Differentiable ℂ J₅'C :=
  let ⟨_, hMψ⟩ := exists_bound_norm_ψI'_z₅'
  (show J₅'C = fun u : ℂ => (-2 * Complex.I : ℂ) * ∫ t in (0 : ℝ)..1,
      ψI' (z₅' t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z₅' t) from
    funext fun u => by simp [J₅'C, ← intervalIntegral.integral_const_mul, mul_assoc,
      mul_left_comm, mul_comm]) ▸
    (differentiable_const (-2 * Complex.I : ℂ)).mul (integral_ψ_exp_differentiable (Cz := 1)
      continuousOn_ψI'_z₅' continuous_z₅' hMψ
      (fun t ht => norm_z₅'_le t (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht))))

set_option maxHeartbeats 1000000 in
lemma J₆'C_differentiableOn : DifferentiableOn ℂ J₆'C rightHalfPlane := by
  intro u0 hu0
  have hu0re : 0 < u0.re := by simpa [rightHalfPlane] using hu0
  let μ : Measure ℝ := μIciOne
  have hψS'_eq : ∀ t : ℝ, t ∈ Set.Ici (1 : ℝ) → ψS' (z₆' t) = ψS.resToImagAxis t := fun t ht => by
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    simp [show z₆' t = (Complex.I : ℂ) * (t : ℂ) by simpa using (z₆'_eq_of_mem (t := t) ht),
      ψS', Function.resToImagAxis, ResToImagAxis, ht0, mul_comm]
  let base : ℝ → ℂ := fun t => (Complex.I : ℂ) * ψS.resToImagAxis t
  let k : ℝ → ℂ := fun t => (-(π : ℂ)) * (t : ℂ)
  let F : ℂ → ℝ → ℂ := fun u t => base t * Complex.exp (u * k t)
  let F' : ℂ → ℝ → ℂ := fun u t => base t * k t * Complex.exp (u * k t)
  have hcont_base : ContinuousOn base (Set.Ici (1 : ℝ)) := by
    simpa [base] using continuousOn_const.mul (Function.continuousOn_resToImagAxis_Ici_one_of
      (F := ψS) MagicFunction.b.PsiBounds.continuous_ψS)
  have hk_cont : ContinuousOn k (Set.Ici (1 : ℝ)) := by fun_prop
  have hExp : ∀ u : ℂ, ContinuousOn (fun t : ℝ => Complex.exp (u * k t)) (Set.Ici (1 : ℝ)) :=
    fun u => ContinuousOn.cexp (continuousOn_const.mul hk_cont)
  have hF_meas : ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (F u) μ := .of_forall fun u => by
    simpa [μ] using ((hcont_base.mul (hExp u)).aestronglyMeasurable (μ := volume) measurableSet_Ici)
  have hF'_meas : AEStronglyMeasurable (F' u0) μ := by
    simpa [F', μ, mul_assoc] using ((hcont_base.mul hk_cont).mul (hExp u0)).aestronglyMeasurable
      (μ := volume) measurableSet_Ici
  obtain ⟨Mψ, hMψ⟩ := MagicFunction.b.PsiBounds.exists_bound_norm_ψS_resToImagAxis_Ici_one
  have hbase_bound : ∀ t : ℝ, 1 ≤ t → ‖base t‖ ≤ Mψ := fun t ht => by
    simpa [base, norm_mul] using mul_le_mul_of_nonneg_left (hMψ t ht) (norm_nonneg (Complex.I : ℂ))
  have hF_int : Integrable (F u0) μ := by
    let b : ℝ := Real.pi * u0.re
    have hb : 0 < b := by positivity
    refine Integrable.mono' (by
      simpa [μ, MeasureTheory.IntegrableOn, pow_zero, one_mul] using
        ((SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 0) (b := b)
          hb) : IntegrableOn _ _ (volume : Measure ℝ)).const_mul Mψ :
      Integrable (fun t : ℝ => Mψ * Real.exp (-b * t)) μ) hF_meas.self_of_nhds
      ((ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht => ?_)
    have hexp : ‖Complex.exp (u0 * k t)‖ = Real.exp (-b * t) := by
      simp [Complex.norm_exp, mul_re, show (k t).re = -Real.pi * t by simp [k],
        show (k t).im = 0 by simp [k], b, mul_left_comm, mul_comm]
    rw [show ‖F u0 t‖ = ‖base t‖ * ‖Complex.exp (u0 * k t)‖ by simp [F], hexp]
    exact mul_le_mul_of_nonneg_right (hbase_bound t ht) (Real.exp_pos _).le
  let ε : ℝ := u0.re / 2
  have ε_pos : 0 < ε := div_pos hu0re (by norm_num)
  let b : ℝ := Real.pi * ε
  have hb : 0 < b := by positivity
  let bound : ℝ → ℝ := fun t => (Mψ * Real.pi) * t * Real.exp (-b * t)
  have bound_int : Integrable bound μ := by
    simpa [μ, MeasureTheory.IntegrableOn, bound, mul_assoc, mul_left_comm, mul_comm] using
      (by simpa [pow_one] using
          (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 1) (b := b) hb) :
        IntegrableOn (fun t : ℝ => t * Real.exp (-b * t)) (Set.Ici (1 : ℝ))
          (volume : Measure ℝ)).const_mul (Mψ * Real.pi)
  have hre_lower : ∀ u : ℂ, u ∈ Metric.ball u0 ε → (u0.re / 2) ≤ u.re := fun u hu => by
    have hu' : ‖u - u0‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hu
    have hre : |u.re - u0.re| ≤ ‖u - u0‖ := by simpa using abs_re_le_norm (u - u0)
    grind only [= abs.eq_1, = max_def]
  have h_bound : ∀ᵐ t ∂μ, ∀ u ∈ Metric.ball u0 ε, ‖F' u t‖ ≤ bound t :=
    (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht u hu => by
      have ht0 : 0 ≤ t := le_trans (by norm_num) ht
      have hexp_le : ‖Complex.exp (u * k t)‖ ≤ Real.exp (-b * t) := by
        simpa [Complex.norm_exp, mul_re, show (k t).re = -Real.pi * t by simp [k],
          show (k t).im = 0 by simp [k], b, ε, mul_assoc, mul_left_comm, mul_comm] using
          Real.exp_le_exp.2 (show -Real.pi * u.re * t ≤ -Real.pi * (u0.re / 2) * t by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonpos_left (hre_lower u hu)
                (by nlinarith [mul_nonneg Real.pi_pos.le ht0] : (-Real.pi * t) ≤ 0))
      have hk_norm : ‖k t‖ = Real.pi * t := by
        simp [k, Complex.norm_real, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg ht0, mul_comm]
      calc ‖F' u t‖
          = ‖base t‖ * (‖k t‖ * ‖Complex.exp (u * k t)‖) := by simp [F', mul_assoc]
        _ ≤ Mψ * ((Real.pi * t) * Real.exp (-b * t)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (mul_le_mul_of_nonneg_left (mul_le_mul (le_of_eq hk_norm) hexp_le (norm_nonneg _)
                (mul_nonneg Real.pi_pos.le ht0)) (norm_nonneg (base t))).trans
                (mul_le_mul_of_nonneg_right (hbase_bound t ht) (by positivity))
        _ = bound t := by simp [bound, mul_assoc, mul_left_comm, mul_comm]
  have h_diff : ∀ᵐ t ∂μ, ∀ u ∈ Metric.ball u0 ε,
      HasDerivAt (fun u : ℂ => F u t) (F' u t) u :=
    .of_forall fun t u _ => by simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using
      (HasDerivAt.comp u (Complex.hasDerivAt_exp (u * k t))
        (hasDerivAt_mul_const (k t) (x := u))).const_mul (base t)
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := F) (x₀ := u0) (s := Metric.ball u0 ε) (hs := Metric.ball_mem_nhds u0 ε_pos)
      (bound := bound) (hF_meas := hF_meas) (hF_int := hF_int) (hF'_meas := hF'_meas)
      (h_bound := h_bound) (bound_integrable := bound_int) (h_diff := h_diff)
  have hEq : (fun u : ℂ => (-2 : ℂ) * ∫ t, F u t ∂μ) = J₆'C := by
    funext u
    simp only [J₆'C, μ]
    have hμ : (∫ t, F u t ∂μIciOne) = ∫ t in Set.Ici (1 : ℝ), F u t := by simp [μIciOne]
    rw [hμ]
    refine congrArg ((-2 : ℂ) * ·) (MeasureTheory.integral_congr_ae <|
      (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht => ?_)
    have hz : z₆' t = (Complex.I : ℂ) * (t : ℂ) := by simpa using (z₆'_eq_of_mem (t := t) ht)
    have hψ' : ψS' ((Complex.I : ℂ) * (t : ℂ)) = ψS.resToImagAxis t := by
      simpa [hz] using hψS'_eq t ht
    have hIexp : Complex.I * (Complex.I * (↑t * ↑π)) = -(↑t * ↑π) := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    have hIexp' : u * ((Complex.I : ℂ) * (Complex.I * ((t : ℂ) * (π : ℂ)))) =
          -(u * ((t : ℂ) * (π : ℂ))) := by simp [hIexp]
    simp [F, base, k, hz, hψ', hIexp', mul_left_comm, mul_comm]
  exact (hEq ▸ (h.2.differentiableAt.const_mul (-2 : ℂ)) : DifferentiableAt ℂ J₆'C u0)
    |>.differentiableWithinAt

/-- `bPrimeC` is analytic on the right half-plane. -/
public lemma bPrimeC_analyticOnNhd : AnalyticOnNhd ℂ bPrimeC rightHalfPlane := by
  simpa [bPrimeC] using
    (((((J₁'C_differentiable.differentiableOn.add J₂'C_differentiable.differentiableOn).add
      J₃'C_differentiable.differentiableOn).add J₄'C_differentiable.differentiableOn).add
      J₅'C_differentiable.differentiableOn).add J₆'C_differentiableOn).analyticOnNhd
      rightHalfPlane_isOpen

end

end MagicFunction.g.CohnElkies.IntegralReps
