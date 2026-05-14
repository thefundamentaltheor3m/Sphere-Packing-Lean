module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.Cancellation
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.IntegralLemmas
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceLemmas
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceB.LaplaceRepresentation
public import SpherePacking.MagicFunction.b.Psi
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import SpherePacking.ModularForms.SlashActionAuxil
import SpherePacking.MagicFunction.b.PsiBounds
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ5
import SpherePacking.Integration.UpperHalfPlaneComp
import SpherePacking.Integration.Measure
import SpherePacking.ForMathlib.DerivHelpers
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# "Another integral" representation for `b'` (`AnotherIntegral.B`)

This file proves the blueprint proposition `prop:b-another-integral`: for real `u` with `0 < u`
and `u ≠ 2`, the function `b' u` is given by an explicit algebraic prefactor times an integral of
`bAnotherIntegrand u`. The proof combines the `u > 2` computation with analytic continuation on
the punctured right half-plane `ACDomain = {u : ℂ | 0 < Re u} \ {2}`.

Also defines the complex analytic extension `bPrimeC := J₁'C + ... + J₆'C` of `b'`, which agrees
with `b'` on the positive real axis and is analytic on the right half-plane.

## Main definitions
* `bAnotherIntegrand`
* `bAnotherIntegrandC`, `bAnotherIntegralC`, `bAnotherRHS`
* `bPrimeC`

## Main statement
* `bRadial_eq_another_integral_main`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Interval Topology
open MeasureTheory Real Complex Filter Set
open SpherePacking.Integration (μIciOne)
open SpherePacking intervalIntegral

noncomputable section BPrimeExtension

open MagicFunction.b.RealIntegrals MagicFunction.Parametrisations

/-- Complexifications `J₁'C` … `J₆'C` of the real integrals `J₁'` … `J₆'`. -/
def J₁'C (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1,
  (Complex.I : ℂ) * ψT' (z₁' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₁' t))

def J₂'C (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1,
  ψT' (z₂' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₂' t))

def J₃'C (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1,
  (Complex.I : ℂ) * ψT' (z₃' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₃' t))

def J₄'C (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1,
  (-1 : ℂ) * ψT' (z₄' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₄' t))

def J₅'C (u : ℂ) : ℂ := -2 * ∫ t in (0 : ℝ)..1,
  (Complex.I : ℂ) * ψI' (z₅' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₅' t))

def J₆'C (u : ℂ) : ℂ := -2 * ∫ t in Set.Ici (1 : ℝ),
  (Complex.I : ℂ) * ψS' (z₆' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₆' t))

/-- Analytic extension of `b'` defined as the sum `J₁'C + … + J₆'C`. -/
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

private lemma exists_bound_norm_ψT'_comp_of_im_pos_all (z : ℝ → ℂ) (hz : Continuous z)
    (hIm : ∀ t : ℝ, 0 < (z t).im) :
    ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z t)‖ ≤ M :=
  Integration.exists_bound_norm_uIoc_zero_one_of_continuous (fun t => ψT' (z t))
    (SpherePacking.Integration.continuous_comp_upperHalfPlane_mk (ψT := ψT) (ψT' := ψT')
      MagicFunction.b.PsiBounds.continuous_ψT (z := z) hz hIm fun t => by simp [ψT', hIm t])

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

lemma norm_z₃'_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖z₃' t‖ ≤ 2 := by
  have hz : z₃' t = (1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) := by simp [z₃'_eq_of_mem (t := t) ht]
  have h := norm_add_le (1 : ℂ) ((Complex.I : ℂ) * (t : ℂ))
  rw [hz]; simp [Complex.norm_real, abs_of_nonneg ht.1] at h; linarith [ht.2]

private lemma norm_add_I_le_three (a : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ha : ‖a‖ ≤ 1 + t) : ‖a + (Complex.I : ℂ)‖ ≤ 3 := by
  have h := norm_add_le a (Complex.I : ℂ); simp at h; linarith [ht.2]

/-- Shared differentiability wrapper for `J₁'C`–`J₅'C`. -/
private lemma integral_ψ_exp_differentiable
    {ψ : ℂ → ℂ} {z : ℝ → ℂ} {Mψ Cz : ℝ}
    (hψz_cont : ContinuousOn (fun t : ℝ => ψ (z t)) (Ι (0 : ℝ) 1))
    (hz_cont : Continuous z)
    (hψz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖ψ (z t)‖ ≤ Mψ)
    (hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ Cz) :
    Differentiable ℂ
      (fun u : ℂ => ∫ t in (0 : ℝ)..1,
        ψ (z t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z t)) := fun u0 => by
  have hEq : (fun u : ℂ => ∫ t in (0 : ℝ)..1,
        ψ (z t) * Complex.exp (u * ((π : ℂ) * (Complex.I : ℂ) * z t))) =
      fun u : ℂ => ∫ t in (0 : ℝ)..1,
        ψ (z t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z t) := by
    funext u; congr 1; funext t; congr 2; ring
  exact hEq ▸ differentiableAt_intervalIntegral_mul_exp (u0 := u0) (Cbase := Mψ) (K := Cz * π)
    hψz_cont (continuous_const.mul hz_cont).continuousOn hψz_bound
    (fun t ht => by
      rw [norm_mul, show ‖(π : ℂ) * (Complex.I : ℂ)‖ = (π : ℝ) by
        simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le], mul_comm]
      gcongr; exact hz_bound t ht)

lemma J₁'C_differentiable : Differentiable ℂ J₁'C :=
  let ⟨_, hMψ⟩ : ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z₁' t)‖ ≤ M :=
    exists_bound_norm_ψI'_z₅'.imp fun _ hM t ht => by
      simpa [MagicFunction.b.PsiParamRelations.ψT'_z₁'_eq_ψI'_z₅' (t := t)
        (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht))] using hM t ht
  (show J₁'C = fun u : ℂ => (Complex.I : ℂ) * ∫ t in (0 : ℝ)..1,
      ψT' (z₁' t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z₁' t) from
    funext fun u => by simp [J₁'C, ← intervalIntegral.integral_const_mul, mul_assoc]) ▸
    (differentiable_const (Complex.I : ℂ)).mul (integral_ψ_exp_differentiable (Cz := 2)
      (continuousOn_ψT'_comp z₁' continuous_z₁' fun t ht => im_z₁'_pos (mem_Ioc_of_mem_uIoc ht))
      continuous_z₁' hMψ (fun t _ => norm_z₁'_le_two t))

lemma J₂'C_differentiable : Differentiable ℂ J₂'C :=
  let ⟨_, hMψ⟩ := exists_bound_norm_ψT'_comp_of_im_pos_all z₂' continuous_z₂' im_z₂'_pos_all
  integral_ψ_exp_differentiable (Cz := 3)
    (continuousOn_ψT'_comp z₂' continuous_z₂'
      fun _ ht => im_z₂'_pos (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)))
    continuous_z₂' hMψ (fun t ht => by
      have htic := mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)
      exact (show z₂' t = ((-1 : ℂ) + (t : ℂ)) + (Complex.I : ℂ) by
          simp [z₂'_eq_of_mem (t := t) htic, add_comm]) ▸ norm_add_I_le_three _ htic
            (by simpa [Complex.norm_real, abs_of_nonneg htic.1] using norm_add_le (-1 : ℂ) (t : ℂ)))

lemma J₃'C_differentiable : Differentiable ℂ J₃'C :=
  let ⟨_, hMψ⟩ : ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z₃' t)‖ ≤ M :=
    exists_bound_norm_ψI'_z₅'.imp fun _ hM t ht => by
      simpa [MagicFunction.b.PsiParamRelations.ψT'_z₃'_eq_ψI'_z₅' (t := t)
        (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht))] using hM t ht
  (show J₃'C = fun u : ℂ => (Complex.I : ℂ) * ∫ t in (0 : ℝ)..1,
      ψT' (z₃' t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z₃' t) from
    funext fun u => by simp [J₃'C, ← intervalIntegral.integral_const_mul, mul_assoc]) ▸
    (differentiable_const (Complex.I : ℂ)).mul (integral_ψ_exp_differentiable (Cz := 2)
      (continuousOn_ψT'_comp z₃' continuous_z₃' fun t ht => im_z₃'_pos (mem_Ioc_of_mem_uIoc ht))
      continuous_z₃' hMψ (fun t ht => norm_z₃'_le t (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht))))

lemma J₄'C_differentiable : Differentiable ℂ J₄'C :=
  let ⟨_, hMψ⟩ := exists_bound_norm_ψT'_comp_of_im_pos_all z₄' continuous_z₄' im_z₄'_pos_all
  (show J₄'C = fun u : ℂ => (-1 : ℂ) * ∫ t in (0 : ℝ)..1,
      ψT' (z₄' t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z₄' t) from
    funext fun u => by simp [J₄'C, ← intervalIntegral.integral_const_mul, mul_assoc]) ▸
    (differentiable_const (-1 : ℂ)).mul (integral_ψ_exp_differentiable (Cz := 3)
      (continuousOn_ψT'_comp z₄' continuous_z₄'
        fun t ht => im_z₄'_pos (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)))
      continuous_z₄' hMψ (fun t ht => by
        have htic := mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)
        exact (show z₄' t = ((1 : ℂ) + (-(t : ℂ))) + (Complex.I : ℂ) by
            simp [z₄'_eq_of_mem (t := t) htic, sub_eq_add_neg, add_comm]) ▸ norm_add_I_le_three _ htic
              ((norm_add_le _ _).trans (by simp [Complex.norm_real, abs_of_nonneg htic.1]))))

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
      (fun t ht => by
        have htic := mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)
        simpa [z₅'_eq_of_mem (t := t) htic, Complex.norm_real, abs_of_nonneg htic.1] using htic.2))

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
  have hF'_meas : AEStronglyMeasurable (F' u0) μ := by simpa [F', μ, mul_assoc] using
    ((hcont_base.mul hk_cont).mul (hExp u0)).aestronglyMeasurable (μ := volume) measurableSet_Ici
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
    have hIexp' : u * ((Complex.I : ℂ) * (Complex.I * ((t : ℂ) * (π : ℂ)))) =
          -(u * ((t : ℂ) * (π : ℂ))) := by ring_nf; simp [Complex.I_sq]
    simp [F, base, k, hz, hψ', hIexp', mul_left_comm, mul_comm]
  exact (hEq ▸ (h.2.differentiableAt.const_mul (-2 : ℂ)) : DifferentiableAt ℂ J₆'C u0)
    |>.differentiableWithinAt

/-- `bPrimeC` is analytic on the right half-plane. -/
public lemma bPrimeC_analyticOnNhd : AnalyticOnNhd ℂ bPrimeC rightHalfPlane := by
  simpa [bPrimeC] using
    ((((J₁'C_differentiable.add J₂'C_differentiable).add J₃'C_differentiable).add
      J₄'C_differentiable).add J₅'C_differentiable).differentiableOn.add
      J₆'C_differentiableOn |>.analyticOnNhd rightHalfPlane_isOpen

end BPrimeExtension

/-! ## "Another integral" representation for `b'` -/

noncomputable section

open MagicFunction.FourierEigenfunctions

/-- Complex-parameter integrand for the "another integral" representation of `b'`. -/
@[expose] public def bAnotherIntegrandC (u : ℂ) (t : ℝ) : ℂ :=
  bAnotherBase t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

/-- Complex-parameter "another integral" associated to `b'`. -/
@[expose] public def bAnotherIntegralC (u : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrandC u t

/-- Restriction of `bAnotherIntegralC` to real parameters. -/
public lemma bAnotherIntegralC_ofReal (u : ℝ) :
    bAnotherIntegralC (u : ℂ) =
      ∫ t in Set.Ioi (0 : ℝ), bAnotherBase t * (Real.exp (-π * u * t) : ℂ) :=
  MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun t _ ↦ by simp [bAnotherIntegrandC, mul_assoc])

def bAnotherRHS (u : ℂ) : ℂ :=
  (-4 * (Complex.I : ℂ)) *
    (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) *
      ((144 : ℂ) / ((π : ℂ) * u) + (1 : ℂ) / ((π : ℂ) * (u - 2)) + bAnotherIntegralC u)

lemma bAnotherRHS_analyticOnNhd :
    AnalyticOnNhd ℂ bAnotherRHS ACDomain := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hterm1 :
      AnalyticOnNhd ℂ (fun u : ℂ => (144 : ℂ) / ((π : ℂ) * u)) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul analyticOnNhd_id) fun u hu =>
      mul_ne_zero hπ fun h0 =>
        (ne_of_gt (by simpa [rightHalfPlane] using hu.1)) (by simp [h0])
  have hterm2 :
      AnalyticOnNhd ℂ (fun u : ℂ => (1 : ℂ) / ((π : ℂ) * (u - 2))) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const))
      fun u hu => mul_ne_zero hπ (sub_ne_zero.2 (by simpa [Set.mem_singleton_iff] using hu.2))
  unfold bAnotherRHS
  exact analyticOnNhd_sinSq_prefactor_mul (sign := (-4 * (Complex.I : ℂ))) <| by
    simpa [add_assoc] using
      (hterm1.add hterm2).add ((show AnalyticOnNhd ℂ bAnotherIntegralC rightHalfPlane by
        convert analyticOnNhd_integral_base_exp (base := bAnotherBase) continuousOn_bAnotherBase
          (fun u hu ↦ bAnotherBase_integrable_exp (u := u) hu) using 1).mono fun u hu => hu.1)

/--
Analytic-continuation step: extend the "another integral" identity for `b'` from `u > 2` to all
real `0 < u` with `u ≠ 2`.
-/
public theorem bRadial_eq_another_integral_analytic_continuation_of_gt2
    (h_gt2 :
      ∀ r : ℝ, 2 < r →
        b' r =
          (-4 * (Complex.I : ℂ)) *
            (Real.sin (π * r / 2)) ^ (2 : ℕ) *
              ((144 : ℂ) / (π * r) + (1 : ℂ) / (π * (r - 2)) +
                ∫ t in Set.Ioi (0 : ℝ),
                  bAnotherBase t * (Real.exp (-π * r * t) : ℂ)))
    {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    b' u =
      (-4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) +
            ∫ t in Set.Ioi (0 : ℝ),
              bAnotherBase t * (Real.exp (-π * u * t) : ℂ)) :=
  analytic_continuation_of_gt2
    ⟨bPrimeC, bPrimeC_analyticOnNhd.mono (fun u hu => hu.1), fun u hu _ => by
      simpa [show MagicFunction.b.RealIntegrals.b' u = b' u by
        simpa using (MagicFunction.g.CohnElkies.b'_eq_realIntegrals_b' (u := u) hu.le).symm]
        using bPrimeC_ofReal u⟩
    bAnotherRHS_analyticOnNhd
    (fun u => by
      simp [bAnotherRHS, bAnotherIntegralC_ofReal, sub_eq_add_neg, add_assoc, add_comm,
        add_left_comm, mul_assoc])
    h_gt2 hu hu2

/-- The integrand used in the "another integral" representation of `b'`. -/
@[expose] public def bAnotherIntegrand (u t : ℝ) : ℂ :=
  bAnotherBase t * (Real.exp (-π * u * t) : ℂ)

lemma bRadial_eq_another_integral_of_gt2 {u : ℝ} (hu : 2 < u) : b' u =
    (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
      ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) +
        ∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrand u t) := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hpoint (t : ℝ) : bLaplaceIntegrand u t = bAnotherIntegrand u t +
      ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t) := by
    simp [bLaplaceIntegrand, bAnotherIntegrand, bAnotherBase, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm, mul_left_comm, mul_comm, mul_add]
  have hExpInt : IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_neg_pi_mul_Ioi_complex (u := u) hu0
  have h2ExpInt : IntegrableOn (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ))
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu
  have hCorrInt : IntegrableOn
      (fun t : ℝ => ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t))
      (Set.Ioi (0 : ℝ)) :=
    ((hExpInt.const_mul (144 : ℂ)).add h2ExpInt).congr <|
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => by
        simp [-Complex.ofReal_exp, add_mul, mul_assoc]
  have hAnotherInt : IntegrableOn (fun t : ℝ => bAnotherIntegrand u t) (Set.Ioi (0 : ℝ)) := by
    simpa [show (fun t : ℝ => bAnotherIntegrand u t) =
        fun t : ℝ => bLaplaceIntegrand u t -
          ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t) from
      funext fun t => by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (eq_sub_of_add_eq (hpoint t).symm)] using
      (bLaplaceIntegral_convergent (u := u) hu).sub hCorrInt
  have hLapInt_decomp : (∫ t in Set.Ioi (0 : ℝ), bLaplaceIntegrand u t) =
      (∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrand u t) + (∫ t in Set.Ioi (0 : ℝ),
        ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t)) := by
    rw [show (∫ t in Set.Ioi (0 : ℝ), bLaplaceIntegrand u t) =
          ∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrand u t +
            ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t) from
      MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi (fun t _ => by simp [hpoint t])]
    exact integral_add hAnotherInt hCorrInt
  have hCorr_eval : (∫ t in Set.Ioi (0 : ℝ),
      ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t)) =
      (144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) := by
    rw [show (fun t : ℝ => ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t)) =
          fun t => (144 : ℂ) * (Real.exp (-π * u * t) : ℂ) +
            (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) from
        funext fun t => by simp [-Complex.ofReal_exp, add_mul, mul_assoc],
      MeasureTheory.integral_add (hExpInt.const_mul (144 : ℂ)) h2ExpInt,
      MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))
        (144 : ℂ) (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)),
      integral_exp_neg_pi_mul_Ioi_complex (u := u) hu0,
      integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu]
    push_cast; ring
  rw [show b' u = (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
        (∫ t in Set.Ioi (0 : ℝ), bLaplaceIntegrand u t) from by
      simpa [bLaplaceIntegrand] using bRadial_eq_laplace_psiI_main (u := u) hu,
    hLapInt_decomp, hCorr_eval]
  ring_nf

/-- Main lemma for blueprint proposition `prop:b-another-integral`. -/
public theorem bRadial_eq_another_integral_main {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    b' u = (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
      ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + ∫ t in Set.Ioi (0 : ℝ),
        (ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) - ((Real.exp (2 * π * t)) : ℂ)) *
          Real.exp (-π * u * t)) := by
  simpa [bAnotherIntegrand] using bRadial_eq_another_integral_analytic_continuation_of_gt2
    (h_gt2 := fun r hr => by
      simpa [bAnotherIntegrand] using bRadial_eq_another_integral_of_gt2 (u := r) hr)
    (u := u) hu hu2

end

end MagicFunction.g.CohnElkies.IntegralReps
