module
public import SpherePacking.MagicFunction.b.Psi
public import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common


/-!
# Cancellation and integrability for `AnotherIntegral.B`

This file proves boundedness and weighted integrability estimates for the bracket `bAnotherBase`,
used to justify dominated differentiation for the complex-parameter "another integral" of `b'`.
We split `t > 0` into the ranges `t ≤ 1` (use the `S`-relation to reduce to the `ψS` bound at
infinity) and `1 ≤ t` (use the cancellation estimate from `PsiICancellation`).

## Main definition
* `bAnotherBase`

## Main statements
* `bAnotherBase_integrable_exp`
* `bAnotherBase_integrable_mul_exp`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators UpperHalfPlane

open MeasureTheory Real Complex
open Filter Topology

noncomputable section


lemma psiI_resToImagAxis_eq_mul_psiS (t : ℝ) (ht : 0 < t) :
    ψI.resToImagAxis t = (-(t ^ (2 : ℕ)) : ℂ) * ψS.resToImagAxis (1 / t) := by
  simpa [ψS_slash_S, zpow_two, pow_two] using
    ResToImagAxis.SlashActionS (F := ψS) (k := (-2 : ℤ)) (t := t) ht

lemma continuousOn_psiI'_mul_I :
    ContinuousOn (fun t : ℝ => ψI' (Complex.I * (t : ℂ))) (Set.Ioi (0 : ℝ)) := by
  refine (Function.continuousOn_resToImagAxis_Ioi_of (F := ψI)
    MagicFunction.b.PsiBounds.continuous_ψI).congr fun t ht => ?_
  simpa using
    MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation.psiI'_mul_I_eq_resToImagAxis t ht

/-- The bracket appearing in the "another integral" representation of `b'`. -/
@[expose] public def bAnotherBase (t : ℝ) : ℂ :=
  ψI' (Complex.I * (t : ℂ)) - (144 : ℂ) - (Real.exp (2 * π * t) : ℂ)

/-- Unfolding lemma for `bAnotherBase`. -/
@[simp] public lemma bAnotherBase_eq (t : ℝ) :
    bAnotherBase t =
      ψI' (Complex.I * (t : ℂ)) - (144 : ℂ) - (Real.exp (2 * π * t) : ℂ) := rfl

public lemma continuousOn_bAnotherBase : ContinuousOn bAnotherBase (Set.Ioi (0 : ℝ)) := by
  have hexp : ContinuousOn (fun t : ℝ => (Real.exp (2 * π * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
    fun_prop
  exact (continuousOn_psiI'_mul_I.sub continuousOn_const).sub hexp

/-!
## Global boundedness on the positive imaginary axis

This is the cancellation estimate needed for convergence for all `u > 0`.
-/

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
    have ht' : 1 ≤ (1 / t : ℝ) := by
      simpa [one_div] using (one_le_div (show 0 < t from ht0)).2 ht1
    have hψS' : ‖ψS.resToImagAxis (1 / t : ℝ)‖ ≤ Cψ0 := by
      simpa using (hψS_bound (1 / t : ℝ) ht').trans
        (mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, le_of_lt (one_div_pos.2 ht0)]))
          hCψ0)
    have ht2le : t ^ (2 : ℕ) ≤ 1 := by
      simpa using pow_le_one₀ (n := 2) (le_of_lt ht0) ht1
    rw [MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation.psiI'_mul_I_eq_resToImagAxis
      t ht0, psiI_resToImagAxis_eq_mul_psiS t ht0]
    have hcoeff : ‖(-(t ^ (2 : ℕ)) : ℂ)‖ = t ^ (2 : ℕ) := by simp
    calc
      ‖(-(t ^ (2 : ℕ)) : ℂ) * ψS.resToImagAxis (1 / t)‖
          = ‖(-(t ^ (2 : ℕ)) : ℂ)‖ * ‖ψS.resToImagAxis (1 / t)‖ := by simp
      _ ≤ (t ^ (2 : ℕ)) * Cψ0 := by nlinarith [hcoeff, hψS']
      _ ≤ Cψ0 := by nlinarith [ht2le]
  open MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation in
    rcases exists_bound_norm_psiI'_mul_I_sub_exp_add_const_Ici_one with ⟨Ctail, hCtail⟩
  let Ctail0 : ℝ := max Ctail 0
  have hCtail0 : 0 ≤ Ctail0 := le_max_right _ _
  have htail (t : ℝ) (ht : 1 ≤ t) : ‖bAnotherBase t‖ ≤ Ctail0 := by
    have h1 : ‖bAnotherBase t‖ ≤ Ctail0 * Real.exp (-Real.pi * t) :=
      (hCtail t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hexp_le : Real.exp (-Real.pi * t) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, le_trans (by norm_num : (0:ℝ) ≤ 1) ht])
    exact h1.trans (by simpa [mul_one] using mul_le_mul_of_nonneg_left hexp_le hCtail0)
  let Csmall : ℝ := Cψ0 + 144 + Real.exp (2 * π)
  refine ⟨max Csmall Ctail0, ?_⟩
  intro t ht0
  by_cases ht1 : t ≤ 1
  · have hexp : ‖(Real.exp (2 * π * t) : ℂ)‖ ≤ Real.exp (2 * π) := by
      have hle'' : 2 * π * t ≤ 2 * π := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left ht1 (show 0 ≤ (2 * π : ℝ) by positivity)
      have hn : ‖Complex.exp (2 * π * t)‖ = Real.exp (2 * π * t) := by
        simpa using Complex.norm_exp_ofReal (2 * π * t)
      simpa [Complex.ofReal_exp, hn] using Real.exp_le_exp.2 hle''
    have htri :
        ‖bAnotherBase t‖ ≤ ‖ψI' (Complex.I * (t : ℂ))‖ + ‖(144 : ℂ)‖ +
            ‖(Real.exp (2 * π * t) : ℂ)‖ := by
      simpa [bAnotherBase, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (calc
          ‖ψI' (Complex.I * (t : ℂ)) - ((144 : ℂ) + (Real.exp (2 * π * t) : ℂ))‖
              ≤ ‖ψI' (Complex.I * (t : ℂ))‖ +
                  ‖(144 : ℂ) + (Real.exp (2 * π * t) : ℂ)‖ := norm_sub_le _ _
          _ ≤
              ‖ψI' (Complex.I * (t : ℂ))‖ +
                (‖(144 : ℂ)‖ + ‖(Real.exp (2 * π * t) : ℂ)‖) := by
                gcongr
                exact norm_add_le _ _)
    have h144 : ‖(144 : ℂ)‖ = (144 : ℝ) := by norm_num
    have hψ : ‖ψI' (Complex.I * (t : ℂ))‖ ≤ Cψ0 := hψI'_small t ht0 ht1
    have hb : ‖bAnotherBase t‖ ≤ Csmall := by grind only
    exact hb.trans (le_max_left _ _)
  · exact (htail t (le_of_not_ge ht1)).trans (le_max_right _ _)

/-!
## Weighted integrability

These are the integrability inputs needed for the parametric-integral analyticity proof.
-/

/-- Integrability of `t ↦ bAnotherBase t * exp (-π u t)` on `t > 0`, for `u > 0`. -/
public lemma bAnotherBase_integrable_exp {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => bAnotherBase t * (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
  rcases exists_bound_norm_bAnotherBase_Ioi with ⟨C, hC⟩
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hb : ∀ t : ℝ, 0 < t → ‖bAnotherBase t‖ ≤ C0 :=
    fun t ht => (hC t ht).trans (le_max_left _ _)
  have hpu : 0 < π * u := mul_pos Real.pi_pos hu
  have hg :
      Integrable (fun t : ℝ => C0 * Real.exp (-(π * u) * t))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
    simpa [MeasureTheory.IntegrableOn, mul_assoc] using
      (exp_neg_integrableOn_Ioi (a := (0 : ℝ)) hpu).const_mul C0
  have hf_meas :
      AEStronglyMeasurable (fun t : ℝ => bAnotherBase t * (Real.exp (-π * u * t) : ℂ))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
    have hexp : ContinuousOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
      fun_prop
    exact (continuousOn_bAnotherBase.mul hexp).aestronglyMeasurable measurableSet_Ioi
  have hbound :
      ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))),
        ‖bAnotherBase t * (Real.exp (-π * u * t) : ℂ)‖ ≤
          C0 * Real.exp (-(π * u) * t) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have hnormExp : ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-(π * u) * t) := by
      have h' : ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) := by
        simpa [Complex.ofReal_exp] using Complex.norm_exp_ofReal (-π * u * t)
      simpa [show (-π * u * t) = (-(π * u) * t) by ring_nf] using h'
    calc
      ‖bAnotherBase t * (Real.exp (-π * u * t) : ℂ)‖
          = ‖bAnotherBase t‖ * ‖(Real.exp (-π * u * t) : ℂ)‖ := by simp
      _ = ‖bAnotherBase t‖ * Real.exp (-(π * u) * t) := by rw [hnormExp]
      _ ≤ C0 * Real.exp (-(π * u) * t) := by gcongr; exact hb t ht
  simpa [MeasureTheory.IntegrableOn] using Integrable.mono' hg hf_meas hbound

/-- Integrability of `t ↦ t * bAnotherBase t * exp (-π u t)` on `t > 0`, for `u > 0`. -/
public lemma bAnotherBase_integrable_mul_exp {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * bAnotherBase t * (Real.exp (-π * u * t) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  have hpu : 0 < π * u := mul_pos Real.pi_pos hu
  have hmul_exp :
      IntegrableOn (fun t : ℝ => t * Real.exp (-(π * u) * t)) (Set.Ioi (0 : ℝ)) := by
    let f : ℝ → ℝ := fun t => t * Real.exp (-(π * u) * t)
    have hf_cont : Continuous f := by dsimp [f]; fun_prop
    have hf_Ioc : IntegrableOn f (Set.Ioc (0 : ℝ) 1) :=
      hf_cont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    let b' : ℝ := (π * u) / 2
    have hb' : 0 < b' := by positivity
    have hO : f =O[atTop] fun t : ℝ => Real.exp (-b' * t) := by
      refine Asymptotics.isBigO_of_div_tendsto_nhds (l := atTop) ?_ (c := (0 : ℝ)) ?_
      · exact Filter.Eventually.of_forall fun t ht =>
          False.elim ((Real.exp_ne_zero (-b' * t)) ht)
      · have htend : Tendsto (fun t : ℝ => t * Real.exp (-b' * t)) atTop (𝓝 0) := by
          simpa [Real.rpow_one] using
            tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (1 : ℝ)) (b := b') hb'
        have hEq :
            (fun t : ℝ => f t / Real.exp (-b' * t)) = fun t : ℝ => t * Real.exp (-b' * t) := by
          funext t
          dsimp [f, b']
          have hdiv :
              Real.exp (-(π * u) * t) / Real.exp (-(π * u / 2) * t) =
                Real.exp ((-(π * u) * t) - (-(π * u / 2) * t)) :=
            (Real.exp_sub (-(π * u) * t) (-(π * u / 2) * t)).symm
          grind only
        exact (tendsto_congr' (Filter.Eventually.of_forall fun t => by
          simpa using congrArg (fun g : ℝ → ℝ => g t) hEq)).2 htend
    have hf_Ioi : IntegrableOn f (Set.Ioi (1 : ℝ)) :=
      integrable_of_isBigO_exp_neg (a := (1 : ℝ)) (b := b') hb' hf_cont.continuousOn hO
    have hset : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) :=
      (Set.Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one).symm
    rw [hset]; exact hf_Ioc.union hf_Ioi
  rcases exists_bound_norm_bAnotherBase_Ioi with ⟨C, hC⟩
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hb : ∀ t : ℝ, 0 < t → ‖bAnotherBase t‖ ≤ C0 :=
    fun t ht => (hC t ht).trans (le_max_left _ _)
  have hg :
      Integrable (fun t : ℝ => C0 * (t * Real.exp (-(π * u) * t)))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
    simpa [MeasureTheory.IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using
      hmul_exp.const_mul C0
  have hf_meas :
      AEStronglyMeasurable
          (fun t : ℝ => (t : ℂ) * bAnotherBase t * (Real.exp (-π * u * t) : ℂ))
          ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
    have ht : ContinuousOn (fun t : ℝ => (t : ℂ)) (Set.Ioi (0 : ℝ)) := by fun_prop
    have hexp : ContinuousOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
      fun_prop
    exact ((ht.mul continuousOn_bAnotherBase).mul hexp).aestronglyMeasurable measurableSet_Ioi
  have hbound :
      ∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))),
        ‖((t : ℝ) : ℂ) * bAnotherBase t * (Real.exp (-π * u * t) : ℂ)‖ ≤
          C0 * (t * Real.exp (-(π * u) * t)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have ht0 : 0 < t := ht
    have hnorm_t : ‖((t : ℝ) : ℂ)‖ = t := by simp [abs_of_pos ht0]
    have hnormExp : ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-(π * u) * t) := by
      have h' : ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) := by
        simpa [Complex.ofReal_exp] using Complex.norm_exp_ofReal (-π * u * t)
      simpa [show (-π * u * t) = (-(π * u) * t) by ring_nf] using h'
    calc
      ‖((t : ℝ) : ℂ) * bAnotherBase t * (Real.exp (-π * u * t) : ℂ)‖
          = ‖((t : ℝ) : ℂ)‖ * ‖bAnotherBase t‖ * ‖(Real.exp (-π * u * t) : ℂ)‖ := by
              simp [mul_left_comm, mul_comm]
      _ = t * ‖bAnotherBase t‖ * Real.exp (-(π * u) * t) := by rw [hnorm_t, hnormExp]
      _ ≤ t * C0 * Real.exp (-(π * u) * t) := by gcongr; exact hb t ht0
      _ = C0 * (t * Real.exp (-(π * u) * t)) := by ring_nf
  simpa [MeasureTheory.IntegrableOn] using Integrable.mono' hg hf_meas hbound

end

end MagicFunction.g.CohnElkies.IntegralReps
