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
import SpherePacking.ForMathlib.IntervalIntegral

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
        ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
    simp [hz t htIcc]
  have hJ1 : J₁' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) := by
    simpa [J₁'] using
      hI (z := z₁') (fun t ht => MagicFunction.b.PsiParamRelations.ψT'_z₁'_eq_ψI'_z₅' (t := t) ht)
  have hJ3 : J₃' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) := by
    simpa [J₃'] using
      hI (z := z₃') (fun t ht => MagicFunction.b.PsiParamRelations.ψT'_z₃'_eq_ψI'_z₅' (t := t) ht)
  have hJ5 :
      J₅' (0 : ℝ) = (-2 : ℂ) * ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) := by
    simp [J₅']
  simp [hJ1, hJ3, hJ5]
  ring

private def addIφ (t : ℝ) : ℍ := ⟨(t : ℂ) + Complex.I, by simp⟩

private lemma continuous_addIφ : Continuous addIφ := by
  simpa [addIφ] using (Continuous.upperHalfPlaneMk (by fun_prop) (fun _ => by simp))

lemma continuous_ψI'_add_I : Continuous fun t : ℝ => ψI' ((t : ℂ) + Complex.I) := by
  simpa [ψI', addIφ] using (MagicFunction.b.PsiBounds.continuous_ψI.comp continuous_addIφ)

lemma continuous_ψT'_add_I : Continuous fun t : ℝ => ψT' ((t : ℂ) + Complex.I) := by
  simpa [ψT', addIφ] using (MagicFunction.b.PsiBounds.continuous_ψT.comp continuous_addIφ)

lemma ψT'_z₂'_eq_ψI'_add_one (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ψT' (z₂' t) = ψI' ((t : ℂ) + Complex.I) := by
  have hz2 : 0 < (z₂' t).im := im_z₂'_pos (t := t) (by simpa using ht)
  have hT : ψT ⟨z₂' t, hz2⟩ = ψI ((1 : ℝ) +ᵥ ⟨z₂' t, hz2⟩) := by
    simp [ψT, modular_slash_T_apply]
  have htrans :
      ((1 : ℝ) +ᵥ ⟨z₂' t, hz2⟩ : ℍ) = ⟨(t : ℂ) + Complex.I, by simp⟩ := by
    ext1
    simp [z₂'_eq_of_mem (t := t) ht, add_left_comm, add_comm]
  simpa [ψT', ψI', hz2, htrans] using hT

/-! Contour identity for `b_zero`: `J₂'(0)+J₄'(0)+J₆'(0)=0` via rectangular deformation. -/

lemma htendsto_ψS' :
    ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖ψS' z‖ < ε := by
  intro ε hε
  have hEv : ∀ᶠ z in UpperHalfPlane.atImInfty, ‖ψS z‖ < ε := by
    simpa [dist_eq_norm] using
      (Metric.tendsto_nhds.1 MagicFunction.b.PsiBounds.tendsto_ψS_atImInfty) ε hε
  rcases (Filter.eventually_atImInfty).1 hEv with ⟨M, hM⟩
  refine ⟨max M 1, ?_⟩
  intro z hz
  have hzpos : 0 < z.im := lt_of_lt_of_le (by norm_num) hz
  have := hM ⟨z, hzpos⟩ (le_trans (le_max_left _ _) hz)
  simpa [ψS', hzpos] using this

lemma ψS'_add_one (t : ℝ) (ht : 0 < t) :
    ψS' ((1 : ℂ) + t * Complex.I) = -ψS' (t * Complex.I) := by
  have hz0 : 0 < (t * Complex.I).im := by simpa using ht
  have hz1 : 0 < ((1 : ℂ) + t * Complex.I).im := by simpa using ht
  let z0H : ℍ := ⟨t * Complex.I, hz0⟩
  have h := congrArg (fun F : ℍ → ℂ => F z0H) ψS_slash_T
  have hT : ψS ((1 : ℝ) +ᵥ z0H) = -ψS z0H := by simpa [modular_slash_T_apply] using h
  have hvadd : ((1 : ℝ) +ᵥ z0H : ℍ) = ⟨(1 : ℂ) + t * Complex.I, hz1⟩ := by
    ext1
    simp [z0H, add_comm]
  have hT' : ψS (⟨(1 : ℂ) + t * Complex.I, hz1⟩ : ℍ) = -ψS z0H := by simpa [hvadd] using hT
  simpa [ψS', hz0, hz1, ht, z0H] using hT'

lemma integrableOn_ψS'_vertical_left :
    MeasureTheory.IntegrableOn (fun t : ℝ => ψS' (t * Complex.I)) (Ioi (1 : ℝ))
      MeasureTheory.volume := by
  rcases MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
    ⟨C0, hC0⟩
  let C : ℝ := max C0 0
  have hC :
      ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ C * Real.exp (-Real.pi * t) := by
    intro t ht
    exact (hC0 t ht).trans (by gcongr; exact le_max_left _ _)
  have hgi :
      MeasureTheory.IntegrableOn (fun t : ℝ => C * Real.exp (-Real.pi * t)) (Ioi (1 : ℝ))
        MeasureTheory.volume := by
    have hExp :
        MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-Real.pi * t)) (Ioi (1 : ℝ))
          MeasureTheory.volume := by
      simpa using (exp_neg_integrableOn_Ioi (a := (1 : ℝ)) (b := Real.pi) Real.pi_pos)
    simpa [MeasureTheory.IntegrableOn, mul_assoc] using hExp.const_mul C
  have hmeas :
      MeasureTheory.AEStronglyMeasurable (fun t : ℝ => ψS' (t * Complex.I))
        (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
    have hψS : Continuous ψS := MagicFunction.b.PsiBounds.continuous_ψS
    have hcont : ContinuousOn ψS.resToImagAxis (Ioi (1 : ℝ)) := by
      exact (Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS) hψS).mono
        (Set.Ioi_subset_Ici_self : Ioi (1 : ℝ) ⊆ Ici (1 : ℝ))
    have hcont' : ContinuousOn (fun t : ℝ => ψS' (t * Complex.I)) (Ioi (1 : ℝ)) := by
      refine hcont.congr ?_
      intro t ht
      have ht0 : 0 < t := lt_trans (by norm_num) ht
      simp [ψS', Function.resToImagAxis, ResToImagAxis, ht0, mul_comm]
    exact ContinuousOn.aestronglyMeasurable hcont' measurableSet_Ioi
  have hgi' :
      MeasureTheory.Integrable (fun t : ℝ => C * Real.exp (-Real.pi * t))
        (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
    simpa [MeasureTheory.IntegrableOn] using hgi
  refine MeasureTheory.Integrable.mono' (μ := MeasureTheory.volume.restrict (Ioi (1 : ℝ)))
    hgi' hmeas ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
  intro t ht
  have ht1 : 1 ≤ t := le_of_lt ht
  have ht0 : 0 < t := lt_trans (by norm_num) ht
  have hEq : ψS' (t * Complex.I) = ψS.resToImagAxis t := by
    simp [ψS', Function.resToImagAxis, ResToImagAxis, ht0, mul_comm]
  simpa [hEq] using hC t ht1

lemma integrableOn_ψS'_vertical_right :
    MeasureTheory.IntegrableOn (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I)) (Ioi (1 : ℝ))
      MeasureTheory.volume := by
  have hleft :
      MeasureTheory.IntegrableOn (fun t : ℝ => ψS' (t * Complex.I)) (Ioi (1 : ℝ))
        MeasureTheory.volume := integrableOn_ψS'_vertical_left
  have hEq :
      (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I)) =ᵐ[MeasureTheory.volume.restrict (Ioi (1 : ℝ))]
        fun t : ℝ => -ψS' (t * Complex.I) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have ht0 : 0 < t := lt_trans (by norm_num) ht
    simp [ψS'_add_one t ht0]
  have hneg :
      MeasureTheory.Integrable (fun t : ℝ => -ψS' (t * Complex.I))
        (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
    have : MeasureTheory.Integrable (fun t : ℝ => ψS' (t * Complex.I))
        (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
      simpa [MeasureTheory.IntegrableOn] using hleft
    exact this.neg
  have :
      MeasureTheory.Integrable (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I))
        (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) :=
    hneg.congr hEq.symm
  simpa [MeasureTheory.IntegrableOn] using this

lemma J₂'_J₄_eq_neg_J₆'_zero : J₂' (0 : ℝ) + J₄' 0 = -J₆' 0 := by
  have hJ24 : J₂' (0 : ℝ) + J₄' 0 = ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) := by
    -- Rewrite `J₂' 0` using `ψT(z) = ψI(z+1)` on the segment `Im z = 1`.
    have hJ2 : J₂' (0 : ℝ) = ∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) := by
      have h0 : J₂' (0 : ℝ) = ∫ t in (0 : ℝ)..1, ψT' (z₂' t) := by
        simp [J₂']
      rw [h0]
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have htIcc : t ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
      simp [ψT'_z₂'_eq_ψI'_add_one (t := t) htIcc]
    -- Rewrite `J₄' 0` as the negatively oriented integral over `t ∈ [0,1]` along `Im z = 1`.
    have hJ4 : J₄' (0 : ℝ) = -∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) := by
      have h0 : J₄' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' (z₄' t) := by
        simp [J₄']
      rw [h0]
      -- First, rewrite the parametrisation `z₄' t = (1 - t) + I`.
      have hEq :
          (∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' (z₄' t)) =
            ∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' ((1 - t : ℂ) + Complex.I) := by
        refine intervalIntegral.integral_congr ?_
        intro t ht
        have htIcc : t ∈ Icc (0 : ℝ) 1 := by
          simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
        have hz4 : z₄' t = (1 - (t : ℂ)) + Complex.I := by
          simpa using z₄'_eq_of_mem (t := t) htIcc
        simp [hz4]
      -- Now substitute `u = 1 - t` in the integral.
      let f : ℝ → ℂ := fun u => ψT' ((u : ℂ) + Complex.I)
      have hneg :
          (∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' ((1 - t : ℂ) + Complex.I)) =
            -∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) := by
        simpa [f] using
          (SpherePacking.ForMathlib.intervalIntegral_neg_one_mul_comp_one_sub_eq_neg (f := f))
      -- Avoid `simp` loops: use `hEq` as a rewrite step.
      calc
        (∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' (z₄' t))
            = ∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' ((1 - t : ℂ) + Complex.I) := hEq
        _ = -∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) := hneg
    -- Use `ψI = ψT + ψS` pointwise on `Im z = 1`.
    have hrel :
        ∀ t : ℝ, ψI' ((t : ℂ) + Complex.I) - ψT' ((t : ℂ) + Complex.I) =
          ψS' ((t : ℂ) + Complex.I) := by
      intro t
      have hz : 0 < (((t : ℂ) + Complex.I).im) := by simp
      -- Evaluate `ψI = ψT + ψS` on the corresponding point of `ℍ`.
      have h := congrArg (fun F : ℍ → ℂ => F ⟨(t : ℂ) + Complex.I, hz⟩) ψI_eq_add_ψT_ψS
      have h' :
          ψI' ((t : ℂ) + Complex.I) =
            ψT' ((t : ℂ) + Complex.I) + ψS' ((t : ℂ) + Complex.I) := by
        simpa [ψI', ψT', ψS', hz] using h
      exact sub_eq_of_eq_add' h'
    -- Integrate the pointwise identity.
    have hInt :
        (∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I)) -
            ∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) =
          ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) := by
      -- Use `∫ f - ∫ g = ∫ (f - g)` and then apply pointwise congruence.
      have hSub :
          ∫ t in (0 : ℝ)..1, (ψI' ((t : ℂ) + Complex.I) - ψT' ((t : ℂ) + Complex.I)) =
            (∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I)) -
              ∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) := by
        simpa using
          (intervalIntegral.integral_sub (μ := MeasureTheory.volume)
            (a := (0 : ℝ)) (b := (1 : ℝ))
            (f := fun t : ℝ => ψI' ((t : ℂ) + Complex.I))
            (g := fun t : ℝ => ψT' ((t : ℂ) + Complex.I))
            (continuous_ψI'_add_I.intervalIntegrable
              (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ)))
            (continuous_ψT'_add_I.intervalIntegrable
              (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))))
      have hCongr :
          (∫ t in (0 : ℝ)..1, (ψI' ((t : ℂ) + Complex.I) - ψT' ((t : ℂ) + Complex.I))) =
            ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) := by
        refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
        intro t ht
        exact Complex.ext (congrArg Complex.re (hrel t)) (congrArg Complex.im (hrel t))
      simpa [hSub] using hCongr
    simpa [hJ2, hJ4, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hInt
  have hdiffψS :
      DifferentiableOn ℂ (fun z : ℂ => ψS (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} := by
    -- Get differentiability of `H₂,H₃,H₄` from their manifold differentiability.
    have hH2 :
        DifferentiableOn ℂ (fun z : ℂ => H₂ (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} :=
      (UpperHalfPlane.mdifferentiable_iff
        (f := H₂)).1 mdifferentiable_H₂
    have hH3 :
        DifferentiableOn ℂ (fun z : ℂ => H₃ (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} :=
      (UpperHalfPlane.mdifferentiable_iff
        (f := H₃)).1 mdifferentiable_H₃
    have hH4 :
        DifferentiableOn ℂ (fun z : ℂ => H₄ (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} :=
      (UpperHalfPlane.mdifferentiable_iff
        (f := H₄)).1 mdifferentiable_H₄
    have hden3 :
        ∀ z : ℂ, z ∈ {z : ℂ | 0 < z.im} →
          (H₃ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ) ≠ 0 := by
      intro z hz
      exact pow_ne_zero 2 (H₃_ne_zero (UpperHalfPlane.ofComplex z))
    have hden4 :
        ∀ z : ℂ, z ∈ {z : ℂ | 0 < z.im} →
          (H₄ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ) ≠ 0 := by
      intro z hz
      exact pow_ne_zero 2 (H₄_ne_zero (UpperHalfPlane.ofComplex z))
    -- Prove differentiability of the explicit expression and rewrite using `ψS_eq'`.
    have hExpr :
        DifferentiableOn ℂ
          (fun z : ℂ =>
            (128 : ℂ) *
              (((H₄ (UpperHalfPlane.ofComplex z) - H₂ (UpperHalfPlane.ofComplex z)) /
                      (H₃ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ)) -
                  ((H₂ (UpperHalfPlane.ofComplex z) + H₃ (UpperHalfPlane.ofComplex z)) /
                      (H₄ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ))))
          {z : ℂ | 0 < z.im} := by
      have hleft :
          DifferentiableOn ℂ
            (fun z : ℂ =>
              (H₄ (UpperHalfPlane.ofComplex z) - H₂ (UpperHalfPlane.ofComplex z)) /
                (H₃ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ))
            {z : ℂ | 0 < z.im} :=
        (hH4.sub hH2).div (hH3.pow 2) hden3
      have hright :
          DifferentiableOn ℂ
            (fun z : ℂ =>
              (H₂ (UpperHalfPlane.ofComplex z) + H₃ (UpperHalfPlane.ofComplex z)) /
                (H₄ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ))
            {z : ℂ | 0 < z.im} :=
        (hH2.add hH3).div (hH4.pow 2) hden4
      simpa [mul_assoc] using (DifferentiableOn.const_mul (hleft.sub hright) (128 : ℂ))
    refine hExpr.congr ?_
    intro z hz
    have hh2 : (H₂_MF : ℍ → ℂ) = H₂ := rfl
    have hh3 : (H₃_MF : ℍ → ℂ) = H₃ := rfl
    have hh4 : (H₄_MF : ℍ → ℂ) = H₄ := rfl
    have h := congrArg (fun f : ℍ → ℂ => f (UpperHalfPlane.ofComplex z)) ψS_eq'
    -- Rewrite the modular-form aliases and simplify.
    simpa [hh2, hh3, hh4] using h
  have hcont : ContinuousOn ψS' (Set.uIcc (0 : ℝ) 1 ×ℂ (Ici (1 : ℝ))) := by
    -- On `Im z ≥ 1`, we are inside the upper half-plane so `ψS'` is analytic hence continuous.
    -- We use the explicit holomorphic expression for `ψS ∘ ofComplex` on `Im z > 0`.
    have hcontG :
        ContinuousOn (fun z : ℂ => ψS (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} :=
      hdiffψS.continuousOn
    have hsubset : (Set.uIcc (0 : ℝ) 1 ×ℂ (Ici (1 : ℝ))) ⊆ {z : ℂ | 0 < z.im} := by
      intro z hz
      have : (1 : ℝ) ≤ z.im := by
        -- membership in a reProdIm strip provides the imaginary bound
        rcases hz with ⟨hzRe, hzIm⟩
        simpa [mem_Ici] using hzIm
      exact lt_of_lt_of_le (by norm_num) this
    -- On this strip, `ψS'` agrees with `ψS ∘ ofComplex`.
    have hEq :
        ∀ z : ℂ, z ∈ (Set.uIcc (0 : ℝ) 1 ×ℂ (Ici (1 : ℝ))) →
          ψS' z = ψS (UpperHalfPlane.ofComplex z) := by
      intro z hz
      have hz' : 0 < z.im := hsubset hz
      simp [ψS', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    exact (hcontG.mono hsubset).congr hEq
  have hdiff :
      ∀ z ∈ ((Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) ×ℂ (Ioi (1 : ℝ))) \ (∅ : Set ℂ),
        DifferentiableAt ℂ ψS' z := by
    intro z hz
    rcases hz with ⟨hz, -⟩
    have hzIm : (1 : ℝ) < z.im := by
      rcases hz with ⟨-, hzIm⟩
      simpa [mem_Ioi] using hzIm
    -- Use differentiability of `ψS ∘ ofComplex` on the upper half-plane, and transfer to `ψS'`.
    have hzpos : 0 < z.im := lt_trans (by norm_num) hzIm
    have hAt :
        DifferentiableAt ℂ (fun z : ℂ => ψS (UpperHalfPlane.ofComplex z)) z :=
      (hdiffψS z hzpos).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hzpos)
    have hEq :
        (fun z : ℂ => ψS' z) =ᶠ[𝓝 z] fun z : ℂ => ψS (UpperHalfPlane.ofComplex z) := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hzpos] with w hw
      simp [ψS', hw, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    exact hAt.congr_of_eventuallyEq hEq
  have hint₁ :
      MeasureTheory.IntegrableOn (fun t : ℝ => ψS' ((0 : ℂ) + t * Complex.I)) (Ioi (1 : ℝ))
        MeasureTheory.volume := by
    simpa using integrableOn_ψS'_vertical_left
  have hint₂ :
      MeasureTheory.IntegrableOn (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I)) (Ioi (1 : ℝ))
        MeasureTheory.volume := integrableOn_ψS'_vertical_right
  have hrect :
      (∫ (x : ℝ) in (0 : ℝ)..1, ψS' (x + (1 : ℝ) * Complex.I)) +
          (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((1 : ℂ) + t * Complex.I)) -
            (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((0 : ℂ) + t * Complex.I)) = 0 := by
    simpa [min_eq_left (zero_le_one : (0 : ℝ) ≤ 1), max_eq_right (zero_le_one : (0 : ℝ) ≤ 1)] using
    (Complex.integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
        (y := (1 : ℝ)) (f := ψS') (x₁ := (0 : ℝ)) (x₂ := (1 : ℝ)) hcont (s := (∅ : Set ℂ))
        (by simp) hdiff hint₁ hint₂ htendsto_ψS')
  -- Rewrite the right vertical integral using `ψS'(1+it) = -ψS'(it)`.
  have hright :
      (∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((1 : ℂ) + t * Complex.I)) =
        -∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I) := by
    have hEq :
        (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I)) =ᵐ[MeasureTheory.volume.restrict (Ioi (1 : ℝ))]
          fun t : ℝ => -ψS' (t * Complex.I) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_of_lt ht)
      simp [ψS'_add_one t ht0]
    have hEqInt :
        (∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((1 : ℂ) + t * Complex.I)) =
          ∫ (t : ℝ) in Ioi (1 : ℝ), -ψS' (t * Complex.I) := by
      simpa using (MeasureTheory.integral_congr_ae hEq)
    simpa [MeasureTheory.integral_neg] using hEqInt
  -- Use the deformation identity to relate the horizontal integral to the vertical tail.
  have hhor :
      (∫ (x : ℝ) in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I)) -
          (2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) = 0 := by
    -- Substitute `hright` into `hrect` and simplify.
    have h' : (∫ (x : ℝ) in (0 : ℝ)..1, ψS' (x + (1 : ℝ) * Complex.I)) +
        (Complex.I • (-∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I))) -
          (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) = 0 := by
      simpa [hright] using hrect
    -- Convert to the claimed form.
    simpa [two_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_neg] using h'
  -- Rewrite `J₆'(0)` as the (scaled) vertical integral from `Im z = 1` to `∞`.
  have hJ6 :
      J₆' (0 : ℝ) =
        (-2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) := by
    -- Rewrite the parametrisation `z₆' t = it`, and change `Ici` to `Ioi`.
    have h0 :
        J₆' (0 : ℝ) = (-2 : ℂ) * ∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t) := by
      simp [J₆']
    rw [h0]
    have hIci :
        (∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t)) =
          ∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t) := by
      simpa using
        (MeasureTheory.integral_Ici_eq_integral_Ioi (μ := MeasureTheory.volume)
          (f := fun t : ℝ => (Complex.I : ℂ) * ψS' (z₆' t)) (x := (1 : ℝ)))
    have hparam :
        (∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t)) =
          ∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * ψS' (t * Complex.I) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht' : t ∈ Set.Ici (1 : ℝ) := by
        exact le_of_lt (by simpa [Set.mem_Ioi] using ht)
      simp [MagicFunction.Parametrisations.z₆'_eq_of_mem (t := t) ht', mul_comm]
    -- Pull `I` outside as a scalar and simplify.
    simp [hIci, hparam, MeasureTheory.integral_const_mul, smul_eq_mul]
  -- Combine: `J₂'(0)+J₄'(0)` is the horizontal integral, and `J₆'(0)` is
  -- `-2` times the vertical tail.
  have htail :
      (∫ (x : ℝ) in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I)) + J₆' (0 : ℝ) = 0 := by
    -- `hhor` gives `horizontal - 2*(I•vertical) = 0`.
    -- Replace the tail by `hJ6` and rearrange.
    have : (∫ (x : ℝ) in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I)) =
        (2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) := by
      -- solve `a - b = 0` as `a = b`
      simpa [sub_eq_zero] using hhor
    -- Now substitute.
    simp [this, hJ6]
  have hint :
      (∫ (x : ℝ) in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I)) = -J₆' (0 : ℝ) :=
    eq_neg_of_add_eq_zero_left htail
  calc
    J₂' (0 : ℝ) + J₄' 0 = ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) := hJ24
    _ = -J₆' (0 : ℝ) := hint

theorem b_zero : MagicFunction.FourierEigenfunctions.b (0 : ℝ⁸) = 0 := by
  rw [b_zero_reduction]
  have h246 : J₂' (0 : ℝ) + J₄' 0 + J₆' 0 = 0 := by
    have h := congrArg (fun z : ℂ => z + J₆' (0 : ℝ)) J₂'_J₄_eq_neg_J₆'_zero
    simpa [add_assoc] using h
  have h135 : J₁' (0 : ℝ) + J₃' 0 + J₅' 0 = 0 := by
    have h := congrArg (fun z : ℂ => z + J₅' (0 : ℝ)) J₁'_J₃_eq_neg_J₅'_zero
    simpa [add_assoc] using h
  calc
    J₁' (0 : ℝ) + J₂' 0 + J₃' 0 + J₄' 0 + J₅' 0 + J₆' 0
        = (J₁' (0 : ℝ) + J₃' 0 + J₅' 0) + (J₂' 0 + J₄' 0 + J₆' 0) := by
            ac_rfl
    _ = 0 := by simp [h135, h246]

end MagicFunction.b.SpecialValuesProof.Zero

namespace MagicFunction.b.SpecialValues

open SchwartzMap Real Complex MagicFunction.FourierEigenfunctions

section Zero

/-- The magic function `b` vanishes at the origin. -/
public theorem b_zero : b 0 = 0 := by
  simpa using MagicFunction.b.SpecialValuesProof.b_zero

end MagicFunction.b.SpecialValues.Zero
