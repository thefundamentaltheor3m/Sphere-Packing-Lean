module
public import SpherePacking.MagicFunction.b.psi
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
    (ResToImagAxis.SlashActionS (F := ψS) (k := (-2 : ℤ)) (t := t) ht)

lemma continuousOn_psiI'_mul_I :
    ContinuousOn (fun t : ℝ => ψI' (Complex.I * (t : ℂ))) (Set.Ioi (0 : ℝ)) := by
  have h :=
    Function.continuousOn_resToImagAxis_Ioi_of (F := ψI) MagicFunction.b.PsiBounds.continuous_ψI
  refine ContinuousOn.congr h ?_
  intro t ht
  simpa using
    MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation.psiI'_mul_I_eq_resToImagAxis t ht

/-- The bracket appearing in the "another integral" representation of `b'`. -/
@[expose] public def bAnotherBase (t : ℝ) : ℂ :=
  ψI' (Complex.I * (t : ℂ)) - (144 : ℂ) - (Real.exp (2 * π * t) : ℂ)

/-- Unfolding lemma for `bAnotherBase`. -/
@[simp] public lemma bAnotherBase_eq (t : ℝ) :
    bAnotherBase t =
      ψI' (Complex.I * (t : ℂ)) - (144 : ℂ) - (Real.exp (2 * π * t) : ℂ) := by
  rfl

lemma continuousOn_bAnotherBase : ContinuousOn bAnotherBase (Set.Ioi (0 : ℝ)) := by
  have hψ : ContinuousOn (fun t : ℝ => ψI' (Complex.I * (t : ℂ))) (Set.Ioi (0 : ℝ)) :=
    continuousOn_psiI'_mul_I
  have hexp : ContinuousOn (fun t : ℝ => (Real.exp (2 * π * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
    fun_prop
  have h :
      ContinuousOn
        (fun t : ℝ => ψI' (Complex.I * (t : ℂ)) - (144 : ℂ) - (Real.exp (2 * π * t) : ℂ))
        (Set.Ioi (0 : ℝ)) := (hψ.sub continuousOn_const).sub hexp
  refine h.congr ?_
  intro t ht
  simp [bAnotherBase]

/-!
## Global boundedness on the positive imaginary axis

This is the cancellation estimate needed for convergence for all `u > 0`.
-/

lemma exists_bound_norm_bAnotherBase_Ioi :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ‖bAnotherBase t‖ ≤ C := by
  -- 1) Control `ψI' (I * t)` on `0 < t ≤ 1` via `ψS` bounds on `t ≥ 1`.
  rcases
      MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
    ⟨Cψ, hCψ⟩
  let Cψ0 : ℝ := max Cψ 0
  have hCψ0 : 0 ≤ Cψ0 := le_max_right _ _
  have hψS_bound (s : ℝ) (hs : 1 ≤ s) :
      ‖ψS.resToImagAxis s‖ ≤ Cψ0 * Real.exp (-π * s) := by
    have hs0 : 0 ≤ Real.exp (-π * s) := by positivity
    have hle : Cψ ≤ Cψ0 := le_max_left _ _
    exact (hCψ s hs).trans (mul_le_mul_of_nonneg_right hle hs0)
  have hψI'_small (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
      ‖ψI' (Complex.I * (t : ℂ))‖ ≤ Cψ0 := by
    have ht' : 1 ≤ (1 / t : ℝ) := by
      have := (one_le_div (show 0 < t from ht0)).2 ht1
      simpa [one_div] using this
    have hψS :
        ‖ψS.resToImagAxis (1 / t : ℝ)‖ ≤ Cψ0 * Real.exp (-π * (1 / t : ℝ)) :=
      hψS_bound (1 / t : ℝ) ht'
    have hexp_le : Real.exp (-π * (1 / t : ℝ)) ≤ 1 := by
      have hle : (-π * (1 / t : ℝ)) ≤ 0 := by
        have : 0 ≤ (1 / t : ℝ) := le_of_lt (one_div_pos.2 ht0)
        nlinarith [Real.pi_pos, this]
      simpa using (Real.exp_le_one_iff.2 hle)
    have hψS' : ‖ψS.resToImagAxis (1 / t : ℝ)‖ ≤ Cψ0 := by
      have : Cψ0 * Real.exp (-π * (1 / t : ℝ)) ≤ Cψ0 * (1 : ℝ) :=
        mul_le_mul_of_nonneg_left hexp_le hCψ0
      simpa using (hψS.trans this)
    have ht2le : t ^ (2 : ℕ) ≤ 1 := by
      have ht0' : 0 ≤ t := le_of_lt ht0
      simpa using (pow_le_one₀ (n := 2) ht0' ht1)
    have hres : ψI' (Complex.I * (t : ℂ)) = ψI.resToImagAxis t :=
      MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation.psiI'_mul_I_eq_resToImagAxis
        t ht0
    -- Use the `S`-relation: `ψI(it) = -(t^2) * ψS(i/t)`.
    rw [hres, psiI_resToImagAxis_eq_mul_psiS t ht0]
    have hcoeff : ‖(-(t ^ (2 : ℕ)) : ℂ)‖ = t ^ (2 : ℕ) := by simp
    calc
      ‖(-(t ^ (2 : ℕ)) : ℂ) * ψS.resToImagAxis (1 / t)‖
          = ‖(-(t ^ (2 : ℕ)) : ℂ)‖ * ‖ψS.resToImagAxis (1 / t)‖ := by simp
      _ ≤ (t ^ (2 : ℕ)) * Cψ0 := by
            nlinarith [hcoeff, hψS']
      _ ≤ Cψ0 := by
            nlinarith [ht2le]
  -- 2) Control `‖bAnotherBase t‖` for `1 ≤ t` via the cancellation estimate `O(exp(-π*t))`.
  open MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation in
    rcases exists_bound_norm_psiI'_mul_I_sub_exp_add_const_Ici_one with ⟨Ctail, hCtail⟩
  let Ctail0 : ℝ := max Ctail 0
  have hCtail0 : 0 ≤ Ctail0 := le_max_right _ _
  have htail (t : ℝ) (ht : 1 ≤ t) : ‖bAnotherBase t‖ ≤ Ctail0 := by
    have ht0 : 0 ≤ Real.exp (-Real.pi * t) := by positivity
    have hle : Ctail * Real.exp (-Real.pi * t) ≤ Ctail0 * Real.exp (-Real.pi * t) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) ht0
    have h1 : ‖bAnotherBase t‖ ≤ Ctail0 * Real.exp (-Real.pi * t) :=
      (hCtail t ht).trans hle
    have hexp_le : Real.exp (-Real.pi * t) ≤ 1 := by
      have : (-Real.pi * t) ≤ 0 := by
        nlinarith [Real.pi_pos, (le_trans (by norm_num : (0 : ℝ) ≤ 1) ht)]
      exact (Real.exp_le_one_iff).2 this
    have : Ctail0 * Real.exp (-Real.pi * t) ≤ Ctail0 := by
      simpa [mul_one] using (mul_le_mul_of_nonneg_left hexp_le hCtail0)
    simpa [mul_one] using (h1.trans this)
  -- 3) Combine the two regimes into a single global bound on `t > 0`.
  let Csmall : ℝ := Cψ0 + 144 + Real.exp (2 * π)
  refine ⟨max Csmall Ctail0, ?_⟩
  intro t ht0
  by_cases ht1 : t ≤ 1
  · -- `0 < t ≤ 1`
    have hb : ‖bAnotherBase t‖ ≤ Csmall := by
      have hψ : ‖ψI' (Complex.I * (t : ℂ))‖ ≤ Cψ0 := hψI'_small t ht0 ht1
      have hexp : ‖(Real.exp (2 * π * t) : ℂ)‖ ≤ Real.exp (2 * π) := by
        have h2π : 0 ≤ (2 * π : ℝ) := by positivity
        have hle' : (2 * π) * t ≤ (2 * π) * (1 : ℝ) := mul_le_mul_of_nonneg_left ht1 h2π
        have hle'' : 2 * π * t ≤ 2 * π := by simpa [mul_assoc] using hle'
        have hleExp : Real.exp (2 * π * t) ≤ Real.exp (2 * π) := Real.exp_le_exp.2 hle''
        have hn : ‖Complex.exp (2 * π * t)‖ = Real.exp (2 * π * t) := by
          simpa using (Complex.norm_exp_ofReal (2 * π * t))
        simpa [Complex.ofReal_exp, hn] using hleExp
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
      have : ‖bAnotherBase t‖ ≤ Cψ0 + 144 + Real.exp (2 * π) := by
        nlinarith [htri, hψ, hexp, h144]
      simpa [Csmall] using this
    exact hb.trans (le_max_left _ _)
  · -- `t > 1`, hence `1 ≤ t`
    have ht : (1 : ℝ) ≤ t := le_of_not_ge ht1
    exact (htail t ht).trans (le_max_right _ _)

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
  -- Use domination by `C0 * exp (-(π*u)*t)`.
  have hpu : 0 < π * u := mul_pos Real.pi_pos hu
  have hg' :
      IntegrableOn (fun t : ℝ => Real.exp (-(π * u) * t)) (Set.Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi (a := (0 : ℝ)) hpu
  have hg :
      Integrable (fun t : ℝ => C0 * Real.exp (-(π * u) * t))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
    simpa [MeasureTheory.IntegrableOn, mul_assoc] using (hg'.const_mul C0)
  have hf_meas :
      AEStronglyMeasurable (fun t : ℝ => bAnotherBase t * (Real.exp (-π * u * t) : ℂ))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
    have hcont :
        ContinuousOn (fun t : ℝ => bAnotherBase t * (Real.exp (-π * u * t) : ℂ))
          (Set.Ioi (0 : ℝ)) := by
      have hexp : ContinuousOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
        have : Continuous fun t : ℝ => (Real.exp (-π * u * t) : ℂ) := by fun_prop
        exact this.continuousOn
      exact continuousOn_bAnotherBase.mul hexp
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hbound :
      ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))),
        ‖bAnotherBase t * (Real.exp (-π * u * t) : ℂ)‖ ≤
          C0 * Real.exp (-(π * u) * t) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have ht0 : 0 < t := ht
    have hExp0 : 0 ≤ Real.exp (-(π * u) * t) := by positivity
    have hnormExp : ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-(π * u) * t) := by
      have h' : ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) := by
        simpa [Complex.ofReal_exp] using (Complex.norm_exp_ofReal (-π * u * t))
      simpa [show (-π * u * t) = (-(π * u) * t) by ring_nf] using h'
    calc
      ‖bAnotherBase t * (Real.exp (-π * u * t) : ℂ)‖
          = ‖bAnotherBase t‖ * ‖(Real.exp (-π * u * t) : ℂ)‖ := by simp
      _ = ‖bAnotherBase t‖ * Real.exp (-(π * u) * t) := by
            rw [hnormExp]
      _ ≤ C0 * Real.exp (-(π * u) * t) := by
            gcongr
            exact hb t ht0
  -- Apply `Integrable.mono'` on the restricted measure.
  have hf :
      Integrable (fun t : ℝ => bAnotherBase t * (Real.exp (-π * u * t) : ℂ))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) :=
    Integrable.mono' hg hf_meas hbound
  simpa [MeasureTheory.IntegrableOn] using hf

/-- Integrability of `t ↦ t * bAnotherBase t * exp (-π u t)` on `t > 0`, for `u > 0`. -/
public lemma bAnotherBase_integrable_mul_exp {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * bAnotherBase t * (Real.exp (-π * u * t) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  -- First, `t ↦ t * exp (-(π*u)*t)` is integrable on `(0, ∞)`.
  have hpu : 0 < π * u := mul_pos Real.pi_pos hu
  have hmul_exp :
      IntegrableOn (fun t : ℝ => t * Real.exp (-(π * u) * t)) (Set.Ioi (0 : ℝ)) := by
    -- Split into `(0,1]` and `[1,∞)`, and use exponential decay at infinity.
    let f : ℝ → ℝ := fun t => t * Real.exp (-(π * u) * t)
    have hf_cont : Continuous f := by
      dsimp [f]
      fun_prop
    have hf_Ioc : IntegrableOn f (Set.Ioc (0 : ℝ) 1) := by
      have hf_Icc : IntegrableOn f (Set.Icc (0 : ℝ) 1) := (hf_cont.continuousOn).integrableOn_Icc
      exact hf_Icc.mono_set Set.Ioc_subset_Icc_self
    -- Tail integrability on `t > 1`.
    let b' : ℝ := (π * u) / 2
    have hb' : 0 < b' := by dsimp [b']; linarith
    have hf_Ici : ContinuousOn f (Set.Ici (1 : ℝ)) := hf_cont.continuousOn
    have hO : f =O[atTop] fun t : ℝ => Real.exp (-b' * t) := by
      refine Asymptotics.isBigO_of_div_tendsto_nhds (l := atTop) ?_ (c := (0 : ℝ)) ?_
      · exact Filter.Eventually.of_forall fun t : ℝ => by
          intro ht
          exact False.elim ((Real.exp_ne_zero (-b' * t)) ht)
      · have htend :
            Tendsto (fun t : ℝ => t * Real.exp (-b' * t)) atTop (𝓝 0) := by
          simpa [Real.rpow_one] using
            (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (1 : ℝ)) (b := b') hb')
        have hEq :
            (fun t : ℝ => f t / Real.exp (-b' * t)) = fun t : ℝ => t * Real.exp (-b' * t) := by
          funext t
          dsimp [f, b']
          have hdiv :
              Real.exp (-(π * u) * t) / Real.exp (-(π * u / 2) * t) =
                Real.exp ((-(π * u) * t) - (-(π * u / 2) * t)) := by
            simpa using (Real.exp_sub (-(π * u) * t) (-(π * u / 2) * t)).symm
          have hExp : (-(π * u) * t) - (-(π * u / 2) * t) = (-(π * u / 2) * t) := by
            ring
          calc
            (t * Real.exp (-(π * u) * t)) / Real.exp (-(π * u / 2) * t)
                = t * (Real.exp (-(π * u) * t) / Real.exp (-(π * u / 2) * t)) := by
                    simpa [mul_assoc] using
                      (mul_div_assoc t (Real.exp (-(π * u) * t)) (Real.exp (-(π * u / 2) * t)))
            _ = t * Real.exp ((-(π * u) * t) - (-(π * u / 2) * t)) := by
                  rw [hdiv]
            _ = t * Real.exp (-(π * u / 2) * t) := by
                  rw [hExp]
        have hEq' :
            (fun t : ℝ => f t / Real.exp (-b' * t)) =ᶠ[atTop] fun t : ℝ => t * Real.exp (-b' * t) :=
          Filter.Eventually.of_forall fun t => by
            simpa using congrArg (fun g : ℝ → ℝ => g t) hEq
        exact (tendsto_congr' hEq').2 htend
    have hf_Ioi : IntegrableOn f (Set.Ioi (1 : ℝ)) :=
      integrable_of_isBigO_exp_neg (a := (1 : ℝ)) (b := b') hb' hf_Ici hO
    have hset : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
      ext t
      constructor
      · intro ht
        by_cases h1 : t ≤ 1
        · exact Or.inl ⟨ht, h1⟩
        · exact Or.inr (lt_of_not_ge h1)
      · intro ht
        rcases ht with ht | ht
        · exact ht.1
        · have h01 : (0 : ℝ) < 1 := by norm_num
          exact h01.trans ht
    -- Combine the integrability on the two pieces.
    rw [hset]
    exact hf_Ioc.union hf_Ioi
  -- Now dominate `‖(t:ℂ) * bAnotherBase t * exp(-π*u*t)‖` by a constant multiple of `t*exp`.
  rcases exists_bound_norm_bAnotherBase_Ioi with ⟨C, hC⟩
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hb : ∀ t : ℝ, 0 < t → ‖bAnotherBase t‖ ≤ C0 :=
    fun t ht => (hC t ht).trans (le_max_left _ _)
  have hg :
      Integrable (fun t : ℝ => C0 * (t * Real.exp (-(π * u) * t)))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
    simpa [MeasureTheory.IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using
      (hmul_exp.const_mul C0)
  have hf_meas :
      AEStronglyMeasurable
          (fun t : ℝ => (t : ℂ) * bAnotherBase t * (Real.exp (-π * u * t) : ℂ))
          ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
    have hcont :
        ContinuousOn
            (fun t : ℝ => (t : ℂ) * bAnotherBase t * (Real.exp (-π * u * t) : ℂ))
            (Set.Ioi (0 : ℝ)) := by
      have ht : ContinuousOn (fun t : ℝ => (t : ℂ)) (Set.Ioi (0 : ℝ)) := by
        have : Continuous fun t : ℝ => (t : ℂ) := by fun_prop
        exact this.continuousOn
      have hexp : ContinuousOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
        have : Continuous fun t : ℝ => (Real.exp (-π * u * t) : ℂ) := by fun_prop
        exact this.continuousOn
      exact (ht.mul continuousOn_bAnotherBase).mul hexp
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hbound :
      ∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))),
        ‖((t : ℝ) : ℂ) * bAnotherBase t * (Real.exp (-π * u * t) : ℂ)‖ ≤
          C0 * (t * Real.exp (-(π * u) * t)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have ht0 : 0 < t := ht
    have hnorm_t : ‖((t : ℝ) : ℂ)‖ = t := by
      simp [abs_of_pos ht0]
    have hnormExp : ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-(π * u) * t) := by
      have h' : ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) := by
        simpa [Complex.ofReal_exp] using (Complex.norm_exp_ofReal (-π * u * t))
      simpa [show (-π * u * t) = (-(π * u) * t) by ring_nf] using h'
    calc
      ‖((t : ℝ) : ℂ) * bAnotherBase t * (Real.exp (-π * u * t) : ℂ)‖
          = ‖((t : ℝ) : ℂ)‖ * ‖bAnotherBase t‖ * ‖(Real.exp (-π * u * t) : ℂ)‖ := by
              simp [mul_left_comm, mul_comm]
      _ = t * ‖bAnotherBase t‖ * Real.exp (-(π * u) * t) := by
            rw [hnorm_t, hnormExp]
      _ ≤ t * C0 * Real.exp (-(π * u) * t) := by
            have hExp0 : 0 ≤ Real.exp (-(π * u) * t) := by positivity
            gcongr
            exact hb t ht0
      _ = C0 * (t * Real.exp (-(π * u) * t)) := by ring_nf
  have hf :
      Integrable (fun t : ℝ => (t : ℂ) * bAnotherBase t * (Real.exp (-π * u * t) : ℂ))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) :=
    Integrable.mono' hg hf_meas hbound
  simpa [MeasureTheory.IntegrableOn] using hf

end

end MagicFunction.g.CohnElkies.IntegralReps
