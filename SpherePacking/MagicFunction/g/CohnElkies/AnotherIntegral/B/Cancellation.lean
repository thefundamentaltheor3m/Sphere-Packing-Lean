module
public import SpherePacking.MagicFunction.b.Psi
public import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common

/-! Cancellation and integrability estimates for the `bAnotherBase` bracket. -/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators UpperHalfPlane

open MeasureTheory Real Complex
open Filter Topology

noncomputable section

/-- The bracket appearing in the "another integral" representation of `b'`. -/
@[expose] public def bAnotherBase (t : ℝ) : ℂ :=
  ψI' (Complex.I * (t : ℂ)) - (144 : ℂ) - (Real.exp (2 * π * t) : ℂ)

@[simp] public lemma bAnotherBase_eq (t : ℝ) :
    bAnotherBase t = ψI' (Complex.I * (t : ℂ)) - (144 : ℂ) - (Real.exp (2 * π * t) : ℂ) := rfl

public lemma continuousOn_bAnotherBase : ContinuousOn bAnotherBase (Set.Ioi (0 : ℝ)) := by
  refine (((Function.continuousOn_resToImagAxis_Ioi_of (F := ψI)
    MagicFunction.b.PsiBounds.continuous_ψI).congr fun t ht => ?_).sub continuousOn_const).sub
      (by fun_prop)
  simpa using
    MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation.psiI'_mul_I_eq_resToImagAxis t ht

lemma exists_bound_norm_bAnotherBase_Ioi :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ‖bAnotherBase t‖ ≤ C := by
  rcases
      MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
    ⟨Cψ, hCψ⟩
  let Cψ0 : ℝ := max Cψ 0
  have hCψ0 : 0 ≤ Cψ0 := le_max_right _ _
  have hψS_bound (s : ℝ) (hs : 1 ≤ s) :
      ‖ψS.resToImagAxis s‖ ≤ Cψ0 * Real.exp (-π * s) :=
    (hCψ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hψI'_small (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
      ‖ψI' (Complex.I * (t : ℂ))‖ ≤ Cψ0 := by
    have ht' : 1 ≤ (1 / t : ℝ) := by simpa [one_div] using (one_le_div ht0).2 ht1
    have hψS' : ‖ψS.resToImagAxis (1 / t : ℝ)‖ ≤ Cψ0 := by
      simpa using (hψS_bound (1 / t : ℝ) ht').trans
        (mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, (one_div_pos.2 ht0).le]))
          hCψ0)
    rw [MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation.psiI'_mul_I_eq_resToImagAxis
      t ht0, show ψI.resToImagAxis t = (-(t ^ (2 : ℕ)) : ℂ) * ψS.resToImagAxis (1 / t) by
        simpa [ψS_slash_S, zpow_two, pow_two] using
          ResToImagAxis.SlashActionS (F := ψS) (k := (-2 : ℤ)) (t := t) ht0, norm_mul]
    nlinarith [show ‖(-(t ^ (2 : ℕ)) : ℂ)‖ = t ^ (2 : ℕ) from by simp, hψS', hCψ0,
      show t ^ (2 : ℕ) ≤ 1 from by simpa using pow_le_one₀ (n := 2) ht0.le ht1]
  open MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation in
    rcases exists_bound_norm_psiI'_mul_I_sub_exp_add_const_Ici_one with ⟨Ctail, hCtail⟩
  let Ctail0 : ℝ := max Ctail 0
  have hCtail0 : 0 ≤ Ctail0 := le_max_right _ _
  have htail (t : ℝ) (ht : 1 ≤ t) : ‖bAnotherBase t‖ ≤ Ctail0 := by
    have h1 : ‖bAnotherBase t‖ ≤ Ctail0 * Real.exp (-Real.pi * t) :=
      (hCtail t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hexp_le : Real.exp (-Real.pi * t) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    exact h1.trans (by simpa [mul_one] using mul_le_mul_of_nonneg_left hexp_le hCtail0)
  let Csmall : ℝ := Cψ0 + 144 + Real.exp (2 * π)
  refine ⟨max Csmall Ctail0, ?_⟩
  intro t ht0
  by_cases ht1 : t ≤ 1
  · have hexp : ‖(Real.exp (2 * π * t) : ℂ)‖ ≤ Real.exp (2 * π) := by
      rw [Complex.ofReal_exp, Complex.norm_exp_ofReal]
      exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    have htri :
        ‖bAnotherBase t‖ ≤ ‖ψI' (Complex.I * (t : ℂ))‖ + ‖(144 : ℂ)‖ +
            ‖(Real.exp (2 * π * t) : ℂ)‖ := by
      simpa [bAnotherBase, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (calc
          ‖ψI' (Complex.I * (t : ℂ)) - ((144 : ℂ) + (Real.exp (2 * π * t) : ℂ))‖
              ≤ ‖ψI' (Complex.I * (t : ℂ))‖ +
                  ‖(144 : ℂ) + (Real.exp (2 * π * t) : ℂ)‖ := norm_sub_le _ _
          _ ≤ ‖ψI' (Complex.I * (t : ℂ))‖ +
                (‖(144 : ℂ)‖ + ‖(Real.exp (2 * π * t) : ℂ)‖) := by
                gcongr; exact norm_add_le _ _)
    exact (by
      grind only [hψI'_small t ht0 ht1, show ‖(144 : ℂ)‖ = (144 : ℝ) from by norm_num] :
      ‖bAnotherBase t‖ ≤ Csmall).trans (le_max_left _ _)
  · exact (htail t (le_of_not_ge ht1)).trans (le_max_right _ _)

private lemma exists_bound_norm_bAnotherBase_nonneg :
    ∃ C0 : ℝ, ∀ t : ℝ, 0 < t → ‖bAnotherBase t‖ ≤ C0 :=
  let ⟨C, hC⟩ := exists_bound_norm_bAnotherBase_Ioi
  ⟨max C 0, fun t ht => (hC t ht).trans (le_max_left _ _)⟩

/-- Integrability of `t ↦ bAnotherBase t * exp (-π u t)` on `t > 0`, for `u > 0`. -/
public lemma bAnotherBase_integrable_exp {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => bAnotherBase t * (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
  obtain ⟨C0, hb⟩ := exists_bound_norm_bAnotherBase_nonneg
  have hg :
      Integrable (fun t : ℝ => C0 * Real.exp (-(π * u) * t))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
    simpa [MeasureTheory.IntegrableOn, mul_assoc] using
      (exp_neg_integrableOn_Ioi (a := (0 : ℝ)) (mul_pos Real.pi_pos hu)).const_mul C0
  have hf_meas :
      AEStronglyMeasurable (fun t : ℝ => bAnotherBase t * (Real.exp (-π * u * t) : ℂ))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) :=
    (continuousOn_bAnotherBase.mul (by fun_prop : ContinuousOn
      (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)))).aestronglyMeasurable
        measurableSet_Ioi
  have hbound :
      ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))),
        ‖bAnotherBase t * (Real.exp (-π * u * t) : ℂ)‖ ≤
          C0 * Real.exp (-(π * u) * t) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    rw [norm_mul, show ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-(π * u) * t) from by
      rw [show (-π * u * t) = (-(π * u) * t) from by ring, Complex.ofReal_exp,
        Complex.norm_exp_ofReal]]
    gcongr; exact hb t ht
  simpa [MeasureTheory.IntegrableOn] using Integrable.mono' hg hf_meas hbound

end

end MagicFunction.g.CohnElkies.IntegralReps
