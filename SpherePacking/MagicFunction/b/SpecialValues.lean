/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.b.Schwartz.Basic
import SpherePacking.MagicFunction.b.PsiParamRelations
import SpherePacking.ModularForms.SlashActionAuxil
import SpherePacking.MagicFunction.b.PsiBounds
import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
import Mathlib.Analysis.Complex.Periodic
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Special values for `b`

This file proves special values for Viazovska's magic function `b`, notably the evaluation
`b 0 = 0`.

## Main statement
* `MagicFunction.b.SpecialValues.b_zero`
-/

namespace MagicFunction.b.SpecialValuesProof

open scoped UpperHalfPlane Topology

open Set SchwartzMap Real Complex Filter UpperHalfPlane

open MagicFunction.FourierEigenfunctions
open MagicFunction.b.RealIntegrals
open MagicFunction.b.RadialFunctions
open MagicFunction.Parametrisations
open ModularForm

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section Zero

lemma b_zero_reduction :
    MagicFunction.FourierEigenfunctions.b (0 : ℝ⁸) =
      J₁' (0 : ℝ) + J₂' 0 + J₃' 0 + J₄' 0 + J₅' 0 + J₆' 0 := by
  simpa [MagicFunction.b.RadialFunctions.J₁, MagicFunction.b.RadialFunctions.J₂,
    MagicFunction.b.RadialFunctions.J₃, MagicFunction.b.RadialFunctions.J₄,
    MagicFunction.b.RadialFunctions.J₅, MagicFunction.b.RadialFunctions.J₆] using
    congrArg (fun f : ℝ⁸ → ℂ => f (0 : ℝ⁸))
      MagicFunction.FourierEigenfunctions.b_eq_sum_integrals_RadialFunctions

lemma J₁'_J₃_eq_neg_J₅'_zero : J₁' (0 : ℝ) + J₃' 0 = -J₅' 0 := by
  have hI (z : ℝ → ℂ) (hz : ∀ t ∈ Icc (0 : ℝ) 1, ψT' (z t) = ψI' (z₅' t)) :
      (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψT' (z t)) =
        ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) :=
    intervalIntegral.integral_congr fun t ht => by
      simp [hz t (by simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht)]
  have hJ1 : J₁' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) := by
    simpa [J₁'] using hI z₁' fun t => MagicFunction.b.PsiParamRelations.ψT'_z₁'_eq_ψI'_z₅' (t := t)
  have hJ3 : J₃' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) := by
    simpa [J₃'] using hI z₃' fun t => MagicFunction.b.PsiParamRelations.ψT'_z₃'_eq_ψI'_z₅' (t := t)
  simp [hJ1, hJ3, show J₅' (0 : ℝ) = (-2 : ℂ) *
    ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) by simp [J₅']]; ring

private lemma continuous_addIφ :
    Continuous fun t : ℝ => (⟨(t : ℂ) + Complex.I, by simp⟩ : ℍ) :=
  Continuous.upperHalfPlaneMk (by fun_prop) (fun _ => by simp)

lemma continuous_ψI'_add_I : Continuous fun t : ℝ => ψI' ((t : ℂ) + Complex.I) := by
  simpa [ψI'] using MagicFunction.b.PsiBounds.continuous_ψI.comp continuous_addIφ

lemma continuous_ψT'_add_I : Continuous fun t : ℝ => ψT' ((t : ℂ) + Complex.I) := by
  simpa [ψT'] using MagicFunction.b.PsiBounds.continuous_ψT.comp continuous_addIφ

lemma ψT'_z₂'_eq_ψI'_add_one (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ψT' (z₂' t) = ψI' ((t : ℂ) + Complex.I) := by
  have hz2 : 0 < (z₂' t).im := im_z₂'_pos (t := t) (by simpa using ht)
  simpa [ψT', ψI', hz2, show ((1 : ℝ) +ᵥ ⟨z₂' t, hz2⟩ : ℍ) = ⟨(t : ℂ) + Complex.I, by simp⟩ from by
    ext1; simp [z₂'_eq_of_mem (t := t) ht, add_left_comm, add_comm]] using
    (show ψT ⟨z₂' t, hz2⟩ = ψI ((1 : ℝ) +ᵥ ⟨z₂' t, hz2⟩) by simp [ψT, modular_slash_T_apply])

/-! Contour identity for `b_zero`: `J₂'(0)+J₄'(0)+J₆'(0)=0` via rectangular deformation. -/

lemma htendsto_ψS' :
    ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖ψS' z‖ < ε := fun ε hε => by
  rcases (Filter.eventually_atImInfty).1 (show ∀ᶠ z in UpperHalfPlane.atImInfty, ‖ψS z‖ < ε by
    simpa [dist_eq_norm] using
      (Metric.tendsto_nhds.1 MagicFunction.b.PsiBounds.tendsto_ψS_atImInfty) ε hε) with ⟨M, hM⟩
  refine ⟨max M 1, fun z hz => ?_⟩
  have hzpos : 0 < z.im := lt_of_lt_of_le (by norm_num) hz
  simpa [ψS', hzpos] using hM ⟨z, hzpos⟩ ((le_max_left _ _).trans hz)

lemma ψS'_add_one (t : ℝ) (ht : 0 < t) :
    ψS' ((1 : ℂ) + t * Complex.I) = -ψS' (t * Complex.I) := by
  have hz0 : 0 < (t * Complex.I).im := by simpa using ht
  have hz1 : 0 < ((1 : ℂ) + t * Complex.I).im := by simpa using ht
  let z0H : ℍ := ⟨t * Complex.I, hz0⟩
  simpa [ψS', hz0, hz1, ht, z0H, show ((1 : ℝ) +ᵥ z0H : ℍ) = ⟨(1 : ℂ) + t * Complex.I, hz1⟩ from by
    ext1; simp [z0H, add_comm]] using show ψS ((1 : ℝ) +ᵥ z0H) = -ψS z0H from by
      simpa [modular_slash_T_apply] using congrArg (fun F : ℍ → ℂ => F z0H) ψS_slash_T

lemma integrableOn_ψS'_vertical_left :
    MeasureTheory.IntegrableOn (fun t : ℝ => ψS' (t * Complex.I)) (Ioi (1 : ℝ))
      MeasureTheory.volume := by
  rcases MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
    ⟨C0, hC0⟩
  let C : ℝ := max C0 0
  have hC : ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ C * Real.exp (-Real.pi * t) :=
    fun t ht => (hC0 t ht).trans (by gcongr; exact le_max_left _ _)
  have hgi : MeasureTheory.IntegrableOn (fun t : ℝ => C * Real.exp (-Real.pi * t)) (Ioi (1 : ℝ))
      MeasureTheory.volume := by
    simpa [MeasureTheory.IntegrableOn, mul_assoc] using
      ((exp_neg_integrableOn_Ioi (a := (1 : ℝ)) (b := Real.pi) Real.pi_pos).const_mul C)
  have hEq : ∀ t : ℝ, 0 < t → ψS' (t * Complex.I) = ψS.resToImagAxis t := fun t ht0 => by
    simp [ψS', Function.resToImagAxis, ResToImagAxis, ht0, mul_comm]
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => ψS' (t * Complex.I))
      (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) :=
    (((Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS)
        MagicFunction.b.PsiBounds.continuous_ψS).mono Set.Ioi_subset_Ici_self).congr
      fun t ht => hEq t (lt_trans (by norm_num) ht)).aestronglyMeasurable measurableSet_Ioi
  refine MeasureTheory.Integrable.mono' (μ := MeasureTheory.volume.restrict (Ioi (1 : ℝ)))
    (by simpa [MeasureTheory.IntegrableOn] using hgi) hmeas <|
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      simpa [hEq t (lt_trans (by norm_num) ht)] using hC t ht.le

lemma integrableOn_ψS'_vertical_right :
    MeasureTheory.IntegrableOn (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I)) (Ioi (1 : ℝ))
      MeasureTheory.volume := by
  simpa [MeasureTheory.IntegrableOn] using (integrableOn_ψS'_vertical_left.neg).congr
    (show (fun t : ℝ => -ψS' (t * Complex.I)) =ᵐ[MeasureTheory.volume.restrict (Ioi (1 : ℝ))]
        fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I) from
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        simp [ψS'_add_one t (lt_trans (by norm_num) ht)])

lemma J₂'_J₄_eq_neg_J₆'_zero : J₂' (0 : ℝ) + J₄' 0 = -J₆' 0 := by
  have hJ24 : J₂' (0 : ℝ) + J₄' 0 = ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) := by
    have hJ2 : J₂' (0 : ℝ) = ∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) := by
      simp only [J₂']; exact intervalIntegral.integral_congr fun t ht => by
        simp [ψT'_z₂'_eq_ψI'_add_one (t := t)
          (by simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht)]
    have hJ4 : J₄' (0 : ℝ) = -∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) := by
      rw [show J₄' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' (z₄' t) from by simp [J₄']]
      have hEq :
          (∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' (z₄' t)) =
            ∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' ((1 - t : ℂ) + Complex.I) :=
        intervalIntegral.integral_congr fun t ht => by
          have htIcc : t ∈ Icc (0 : ℝ) 1 := by
            simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
          simp [show z₄' t = (1 - (t : ℂ)) + Complex.I from by simpa using z₄'_eq_of_mem htIcc]
      let f : ℝ → ℂ := fun u => ψT' ((u : ℂ) + Complex.I)
      have h2 : (∫ t in (0 : ℝ)..1, ψT' ((1 - t : ℂ) + Complex.I)) =
          ∫ t in (0 : ℝ)..1, f (1 - t) :=
        intervalIntegral.integral_congr fun t _ => by
          simp [f, show ((1 - t : ℝ) : ℂ) = (1 - t : ℂ) from by push_cast; ring]
      rw [hEq, intervalIntegral.integral_const_mul, h2,
        (by simp : (∫ t in (0 : ℝ)..1, f (1 - t)) = ∫ t in (0 : ℝ)..1, f t), neg_one_mul]
    have hrel : ∀ t : ℝ, ψI' ((t : ℂ) + Complex.I) - ψT' ((t : ℂ) + Complex.I) =
          ψS' ((t : ℂ) + Complex.I) := fun t => by
      have hz : 0 < (((t : ℂ) + Complex.I).im) := by simp
      exact sub_eq_of_eq_add' <| by
        simpa [ψI', ψT', ψS', hz] using
          congrArg (fun F : ℍ → ℂ => F ⟨(t : ℂ) + Complex.I, hz⟩) ψI_eq_add_ψT_ψS
    have hInt : (∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I)) -
        ∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) =
          ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) := by
      have := intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := 0) (b := 1)
        (continuous_ψI'_add_I.intervalIntegrable _ _) (continuous_ψT'_add_I.intervalIntegrable _ _)
      simp_all
    simpa [hJ2, hJ4, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hInt
  have hdiffψS :
      DifferentiableOn ℂ (fun z : ℂ => ψS (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} := by
    have hH2 := (UpperHalfPlane.mdifferentiable_iff (f := H₂)).1 mdifferentiable_H₂
    have hH3 := (UpperHalfPlane.mdifferentiable_iff (f := H₃)).1 mdifferentiable_H₃
    have hH4 := (UpperHalfPlane.mdifferentiable_iff (f := H₄)).1 mdifferentiable_H₄
    have hExpr :
        DifferentiableOn ℂ
          (fun z : ℂ => (128 : ℂ) *
            (((H₄ (UpperHalfPlane.ofComplex z) - H₂ (UpperHalfPlane.ofComplex z)) /
                  (H₃ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ)) -
              ((H₂ (UpperHalfPlane.ofComplex z) + H₃ (UpperHalfPlane.ofComplex z)) /
                  (H₄ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ))))
          {z : ℂ | 0 < z.im} := by
      simpa [mul_assoc] using (DifferentiableOn.const_mul
        (((hH4.sub hH2).div (hH3.pow 2) (fun _ _ => pow_ne_zero 2 (H₃_ne_zero _))).sub
          ((hH2.add hH3).div (hH4.pow 2) (fun _ _ => pow_ne_zero 2 (H₄_ne_zero _))))
        (128 : ℂ))
    refine hExpr.congr fun z _ => ?_
    simpa [show (H₂_MF : ℍ → ℂ) = H₂ from rfl, show (H₃_MF : ℍ → ℂ) = H₃ from rfl,
      show (H₄_MF : ℍ → ℂ) = H₄ from rfl] using
      congrArg (fun f : ℍ → ℂ => f (UpperHalfPlane.ofComplex z)) ψS_eq'
  have hcont : ContinuousOn ψS' (Set.uIcc (0 : ℝ) 1 ×ℂ (Ici (1 : ℝ))) := by
    have hsubset : (Set.uIcc (0 : ℝ) 1 ×ℂ (Ici (1 : ℝ))) ⊆ {z : ℂ | 0 < z.im} := fun z hz =>
      lt_of_lt_of_le (by norm_num) (by simpa [mem_Ici] using hz.2 : (1 : ℝ) ≤ z.im)
    refine (hdiffψS.continuousOn.mono hsubset).congr fun z hz => ?_
    have hz' : 0 < z.im := hsubset hz
    simp [ψS', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  have hdiff : ∀ z ∈ ((Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) ×ℂ (Ioi (1 : ℝ))) \ (∅ : Set ℂ),
      DifferentiableAt ℂ ψS' z := fun z hz => by
    have hzpos : 0 < z.im := lt_trans (by norm_num)
      (by simpa [mem_Ioi] using hz.1.2 : (1 : ℝ) < z.im)
    refine ((hdiffψS z hzpos).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds hzpos)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hzpos] with w hw
    simp [ψS', hw, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  have hrect :
      (∫ (x : ℝ) in (0 : ℝ)..1, ψS' (x + (1 : ℝ) * Complex.I)) +
          (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((1 : ℂ) + t * Complex.I)) -
            (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((0 : ℂ) + t * Complex.I)) = 0 := by
    simpa [min_eq_left (zero_le_one : (0 : ℝ) ≤ 1), max_eq_right (zero_le_one : (0 : ℝ) ≤ 1)] using
    (Complex.integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
        (y := (1 : ℝ)) (f := ψS') (x₁ := (0 : ℝ)) (x₂ := (1 : ℝ)) hcont (s := (∅ : Set ℂ))
        (by simp) hdiff (by simpa using integrableOn_ψS'_vertical_left)
        integrableOn_ψS'_vertical_right htendsto_ψS')
  have hright : (∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((1 : ℂ) + t * Complex.I)) =
      -∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I) := by
    simpa [MeasureTheory.integral_neg] using MeasureTheory.integral_congr_ae
      (g := fun t : ℝ => -ψS' (t * Complex.I))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        simp [ψS'_add_one t (lt_trans (by norm_num) ht)])
  have hhor : (∫ (x : ℝ) in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I)) -
      (2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) = 0 := by
    simpa [two_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_neg]
      using show (∫ (x : ℝ) in (0 : ℝ)..1, ψS' (x + (1 : ℝ) * Complex.I)) +
        (Complex.I • (-∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I))) -
          (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) = 0 by
        simpa [hright] using hrect
  have hJ6 : J₆' (0 : ℝ) =
      (-2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) := by
    rw [show J₆' (0 : ℝ) = (-2 : ℂ) *
        ∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t) from by simp [J₆']]
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi,
      MeasureTheory.integral_congr_ae (g := fun t : ℝ => (Complex.I : ℂ) * ψS' (t * Complex.I))
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
          simp [MagicFunction.Parametrisations.z₆'_eq_of_mem (t := t)
            (le_of_lt (by simpa [Set.mem_Ioi] using ht)), mul_comm])]
    simp [MeasureTheory.integral_const_mul, smul_eq_mul]
  have htail : (∫ (x : ℝ) in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I)) + J₆' (0 : ℝ) = 0 := by
    simp [show (∫ (x : ℝ) in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I)) =
        (2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) from by
      simpa [sub_eq_zero] using hhor, hJ6]
  exact hJ24.trans (eq_neg_of_add_eq_zero_left htail)

theorem b_zero : MagicFunction.FourierEigenfunctions.b (0 : ℝ⁸) = 0 := by
  rw [b_zero_reduction]; linear_combination J₂'_J₄_eq_neg_J₆'_zero + J₁'_J₃_eq_neg_J₅'_zero

end MagicFunction.b.SpecialValuesProof.Zero

namespace MagicFunction.b.SpecialValues

open SchwartzMap Real Complex MagicFunction.FourierEigenfunctions

section Zero

/-- The magic function `b` vanishes at the origin. -/
public theorem b_zero : b 0 = 0 := by
  simpa using MagicFunction.b.SpecialValuesProof.b_zero

end MagicFunction.b.SpecialValues.Zero
