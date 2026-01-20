/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tito Sacchi
-/

import SpherePacking.ModularForms.Eisenstein
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.a.VerticalIntegrability

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}

lemma const_add_variable_change [MulOneClass E] {hf : Continuous f} (x₁ x₂ x₁' : ℝ) :
  ∫ t in x₁..x₂, f t =
  ∫ t in x₁'..(x₁' + (x₂ - x₁)), f (t - (x₁' - x₁)) := by
  set g := fun t ↦ t - (x₁' - x₁)
  have : g x₁' = x₁ := by unfold g; simp
  rw [← this]
  have : g (x₁' + (x₂ - x₁)) = x₂ := by unfold g; simp
  rw [← this]
  conv_lhs =>
    pattern (f _)
    rw [← one_mul (f t)]
  have : ∀ x, HasDerivAt g 1 x := by
    intro x
    unfold g;
    simpa using (hasDerivAt_id' x)
  have : ∀ t, g t = (t - (x₁' - x₁)) := by unfold g; simp
  rw [← intervalIntegral.integral_comp_smul_deriv (f := g) (f' := fun _ ↦ 1)]
  · unfold g
    simp
  · intro x
    unfold g; simp only [hasDerivAt_sub_const_iff]; intro
    exact hasDerivAt_id' x
  · exact continuousOn_const
  · simpa

lemma sign_variable_change (x₁ x₂ : ℝ) :
  ∫ t in x₁..x₂, f t =
  ∫ t in -x₁..-x₂, - f (- t) := by
  rw [intervalIntegral.integral_symm]
  simp

end

noncomputable section

open Set Complex Real MeasureTheory
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals
open MagicFunction.a.RealIntegrands MagicFunction.a.ComplexIntegrands
open MagicFunction.a.RadialFunctions MagicFunction.VerticalIntegrability


-- These are needed to prove the hypotheses for unbounded Cauchy-Gour
lemma φ₀_bound_exp_decay : ∃ C₀ > 0, ∀ z : ℂ, ‖φ₀'' z‖ ≤
  C₀ * Real.exp (-2 * Real.pi * (Complex.im z)) := by sorry
lemma φ₂_bound_exp_decay : ∃ C₂ > 0, ∀ z : ℂ, ‖φ₂'' z‖ ≤ C₂ := by sorry
lemma φ₄_bound_exp_decay : ∃ C₄ > 0, ∀ z : ℂ, ‖φ₄'' z‖ ≤
  C₄ * Real.exp (2 * Real.pi * (Complex.im z)) := by sorry
def d (r : ℝ) := -4 * (Complex.sin (Real.pi * r / 2) ^ 2) *  ∫ t in Ici (0 : ℝ),
  I * φ₀'' (-1 / (I * t)) * (I * t)^2 *
  cexp (I * π * r * (I * t))

variable (r : ℝ) {hr : r > 2}

lemma sin_eq_exp : -4 * (Complex.sin (Real.pi * r / 2))^2 =
  Complex.exp (I * Real.pi * r) - 2 + Complex.exp (-I * Real.pi * r) := by
  unfold Complex.sin
  ring_nf; simp only [I_sq, neg_mul, one_mul, one_div, neg_neg, sub_neg_eq_add]
  rw [← Complex.exp_add, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  ring_nf; simp

def integrand_1 (z : ℂ) := φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (↑π * I * ↑r * z)

def φ₀_int_1 := ∫ t in Ici (0 : ℝ), I * integrand_1 r (-1 + t * I)

def integrand_3 (z : ℂ) := φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (↑π * I * ↑r * z)

def φ₀_int_3 := ∫ t in Ici (0 : ℝ), I * integrand_3 r (1 + t * I)

lemma φ₀_int_1_eq : φ₀_int_1 r = ∫ t in Ici (0 : ℝ),
  I * φ₀'' (-1 / (I * t)) * (I * t)^2 *
  cexp (I * π * r * (I * t - 1)) := by
  unfold φ₀_int_1 integrand_1
  refine setIntegral_congr_ae (by measurability) (ae_of_all _ (fun a ha => ?_))
  ring_nf

lemma φ₀_int_3_eq : φ₀_int_3 r = ∫ t in Ici (0 : ℝ),
  I * φ₀'' (-1 / (I * t)) * (I * t)^2 *
  cexp (I * π * r * (I * t + 1)) := by
  unfold φ₀_int_3 integrand_3
  refine setIntegral_congr_ae (by measurability) (ae_of_all _ (fun a ha => ?_))
  ring_nf

def φ₀_int_4 := -2 * ∫ t in Ici (0 : ℝ),
  I * φ₀'' (-1 / (I * t)) * (I * t)^2 *
  cexp (I * π * r * (I * t))

def φ₀_int_5 := -2 * ∫ t in Ici (1 : ℝ),
  I * φ₀'' (-1 / (I * t)) * (I * t)^2 *
  cexp (I * π * r * (I * t))

include hr

lemma φ₀_int_4_eq : φ₀_int_4 r = I₅' r + φ₀_int_5 r := by
  unfold φ₀_int_4
  rw [← integral_add_compl (@measurableSet_Icc _ _ _ _ _ _ 0 1) _]
  · simp only [measurableSet_Icc, Measure.restrict_restrict, MeasurableSet.compl_iff]
    have : Icc (0 : ℝ) 1 ∩ Ici 0 = Icc 0 1 := by grind
    rw [this]
    have : (Icc (0 : ℝ) 1)ᶜ ∩ Ici 0 = Ioi 1 := by grind
    rw [this]
    rw [I₅'_eq, intervalIntegral.intervalIntegral_eq_integral_uIoc]
    unfold φ₀_int_5
    rw [mul_add]

    congr 1
    · simp only [neg_mul, zero_le_one, ↓reduceIte, uIoc_of_le, one_smul, neg_inj,
        mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
      rw [← integral_Icc_eq_integral_Ioc]
      refine (setIntegral_congr_ae (by measurability) ?_)
      apply ae_of_all
      intros a ia
      ring_nf; simp
    · simp only [neg_mul, neg_inj, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
      rw [← integral_Ici_eq_integral_Ioi]
  · apply IntegrableOn.integrable
    exact (integrableOn_goal1 (hb := sorry) r hr)

lemma cauchy_goursat_int_1 : ∫ (t : ℝ) in Ioi 1, I * integrand_1 r (-1 + t * I) =
  (∫ (x : ℝ) in -1..0, integrand_1 r (x + 1 * I)) +
  I • ∫ (t : ℝ) in Ioi 1, integrand_1 r (0 + t * I) := by
  rw [integral_const_mul]
  rw [← smul_eq_mul]
  have : (-1 : ℝ) = (-1 : ℂ) := by simp
  rw [← this, ← sub_eq_zero.1
   (integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
    1 _ ∅ _ _ _ _ _)]
  · rfl

  -- Need to fill all hypotheses to apply Cauchy-Goursat
  · sorry
  · exact countable_empty
  · intros x hx
    sorry
  · unfold integrand_1
    simp only [ofReal_neg, ofReal_one, neg_add_cancel_comm]
    exact (integrableOn_goal2 sorry r hr)
  · unfold integrand_1
    simp only [ofReal_zero, zero_add]
    apply (integrableOn_goal3 sorry r hr)
  · sorry

lemma cauchy_goursat_int_3 : ∫ (t : ℝ) in Ioi 1, I * integrand_3 r (1 + t * I) =
  (∫ (x : ℝ) in 1..0, integrand_3 r (x + 1 * I)) +
  I • ∫ (t : ℝ) in Ioi 1, integrand_3 r (0 + t * I) := by
  rw [integral_const_mul]
  rw [← smul_eq_mul]
  have : (1 : ℝ) = (1 : ℂ) := by simp
  rw [← this, ← sub_eq_zero.1
   (integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
    1 _ ∅ _ _ _ _ _)]
  · rfl

  -- Need to fill all hypotheses to apply Cauchy-Goursat
  · sorry
  · exact countable_empty
  · intros x hx
    sorry
  · unfold integrand_3
    simp only [ofReal_one, add_sub_cancel_left]
    exact (integrableOn_goal4 sorry r hr)
  · unfold integrand_3
    simp only [ofReal_zero, zero_add]
    apply (integrableOn_goal5 sorry r hr)
  · sorry

lemma int_1_eq : φ₀_int_1 r = I₁' r + I₂' r + ∫ t in Ici (1 : ℝ),
 I * φ₀'' (-1 / (I * t + 1)) * (I * t + 1)^2 *
 cexp (I * π * r * (I * t)) := by
  unfold φ₀_int_1
  rw [← integral_add_compl (@measurableSet_Icc _ _ _ _ _ _ 0 1) _]
  · simp only [measurableSet_Icc, Measure.restrict_restrict, MeasurableSet.compl_iff]
    have : Icc (0 : ℝ) 1 ∩ Ici 0 = Icc 0 1 := by grind
    rw [this]
    have : (Icc (0 : ℝ) 1)ᶜ ∩ Ici 0 = Ioi 1 := by grind
    rw [this]

    unfold I₁'
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_Icc_eq_integral_Ioc]
    rw [mul_comm I, add_assoc]; simp only [zero_le_one, ↓reduceIte, uIoc_of_le, one_smul]
    congr 1
    · refine (setIntegral_congr_ae (by measurability) ?_)
      apply ae_of_all
      intros a ia
      rw [mul_comm _ I, ← z₁'_eq_of_mem (by grind)]
      unfold integrand_1 Φ₁ Φ₁'
      ring

    · rw [cauchy_goursat_int_1 (hr := hr)]
      congr 1
      · rw [MagicFunction.a.RadialFunctions.I₂'_eq]
        unfold integrand_1
        rw [const_add_variable_change (hf := sorry) 0 1 (-1)]
        simp only [sub_zero, neg_add_cancel]
        apply intervalIntegral.integral_congr
        simp only [EqOn, Left.neg_nonpos_iff, zero_le_one, uIcc_of_le, mem_Icc, one_mul,
          sub_neg_eq_add, ofReal_add, ofReal_one, neg_mul, and_imp]
        intro x hx hx'
        conv_rhs =>
          rw [mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
        congr 3 <;> ring_nf
        rw [I_sq]; ring

      · rw [smul_eq_mul, ← integral_const_mul, integral_Ici_eq_integral_Ioi]
        refine (setIntegral_congr_ae (by measurability) (ae_of_all _ (fun x hx => ?_)))
        unfold integrand_1
        ring_nf

  · apply IntegrableOn.integrable
    unfold integrand_1
    simp only [neg_add_cancel_comm]
    exact (integrableOn_goal6 (hb := sorry) r hr)

lemma int_3_eq : φ₀_int_3 r = I₃' r + I₄' r + ∫ t in Ici (1 : ℝ),
  I * φ₀'' (-1 / (I * t - 1)) * (I * t - 1)^2 *
  cexp (I * π * r * (I * t)) := by
  unfold φ₀_int_3
  rw [← integral_add_compl (@measurableSet_Icc _ _ _ _ _ _ 0 1) _]
  · simp only [measurableSet_Icc, Measure.restrict_restrict, MeasurableSet.compl_iff]
    have : Icc (0 : ℝ) 1 ∩ Ici 0 = Icc 0 1 := by grind
    rw [this]
    have : (Icc (0 : ℝ) 1)ᶜ ∩ Ici 0 = Ioi 1 := by grind
    rw [this]

    unfold I₃'
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_Icc_eq_integral_Ioc]
    rw [mul_comm I, add_assoc]
    simp only [zero_le_one, ↓reduceIte, uIoc_of_le, one_smul]
    congr 1
    · refine (setIntegral_congr_ae (by measurability) ?_)
      apply ae_of_all
      intros a ia
      rw [mul_comm _ I, ← z₃'_eq_of_mem (by grind)]
      unfold integrand_3 Φ₃ Φ₃'
      ring

    · rw [cauchy_goursat_int_3 (hr := hr)]
      congr 1
      · unfold integrand_3
        rw [I₄'_eq]
        rw [const_add_variable_change (hf := sorry) 1 0 0];
        simp only [zero_sub, sub_neg_eq_add, ofReal_add,
          ofReal_one, one_mul, zero_add, neg_mul]
        rw [sign_variable_change 0 (-1)]
        simp only [ofReal_neg, neg_zero, neg_neg, intervalIntegral.integral_neg, neg_inj]
        apply intervalIntegral.integral_congr
        simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, and_imp]; intro x hx hx'
        conv_rhs =>
          rw [mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
        congr 3 <;> ring_nf
        rw [I_sq]; ring

      · rw [smul_eq_mul, ← integral_const_mul, integral_Ici_eq_integral_Ioi]
        refine (setIntegral_congr_ae (by measurability) (ae_of_all _ (fun x hx => ?_)))
        unfold integrand_3
        ring_nf

  · apply IntegrableOn.integrable
    unfold integrand_3
    simp only [add_sub_cancel_left]
    sorry -- Required nonexistent goal
    -- exact (integrableOn_goal6 (hb := sorry) r hr)

lemma d_eq_2 : d r = φ₀_int_1 r + I₅' r + φ₀_int_5 r + φ₀_int_3 r := by
  calc
      _ =  -4 * (Complex.sin (Real.pi * r / 2) ^ 2) *
              ∫ t in Ici (0 : ℝ), I * φ₀'' (-1 / (I * t)) *
              (I * t)^2 * cexp (I * π * r * (I * t)) := rfl
      _ = φ₀_int_1 r + φ₀_int_4 r + φ₀_int_3 r := ?_
      _ = φ₀_int_1 r + I₅' r + φ₀_int_5 r + φ₀_int_3 r := by
        simp only [φ₀_int_4_eq r (hr := hr), add_left_inj]
        ring

  · have rw1 (z : ℂ) : cexp (I * ↑π * ↑r) * (I * φ₀'' (-1 / (I * z)) *
      (I *  z) ^ 2 * cexp (I * ↑π * ↑r * (I * z))) =
      I * φ₀'' (-1 / (I * z)) * (I * z) ^ 2 * cexp (I * ↑π * ↑r * (I * z + 1)) := by
      conv_lhs =>
        pattern (cexp _ * _)
        rw [mul_comm, mul_assoc, ← Complex.exp_add]
      conv_lhs =>
        pattern cexp (_ + _)
        rw [add_comm, ← mul_one_add, add_comm]

    have rw2 (z : ℂ) : (cexp (-(I * ↑π * ↑r)) * (I * φ₀'' (-1 / (I * z)) *
      (I * z) ^ 2 * cexp (↑I * π * ↑r * (I * z)))) =
      I * φ₀'' (-1 / (I * z)) * (I * z) ^ 2 * cexp (I * ↑π * ↑r * (I * z - 1)) := by
      conv_lhs =>
        pattern (cexp _ * _)
        rw [mul_comm, mul_assoc, ← Complex.exp_add]
      conv_lhs =>
        pattern cexp (_ + _)
        rw [add_comm, ← neg_one_mul]
      have : forall a, (-1 * (I * ↑π * ↑r) + I * ↑π * ↑r * (I * ↑a)) = I * ↑π * ↑r *
        (I * ↑a - 1) := by intros; ring
      conv_lhs =>
        pattern cexp _
        rw [this]

    have hI : IntegrableOn (fun (a : ℝ) ↦ cexp (I * ↑π * ↑r) * (I * φ₀'' (-1 / (I * ↑a)) *
      (I *  ↑a) ^ 2 * cexp (I * ↑π * ↑r * (I * ↑a)))) (Ici 0) := by
      conv =>
        pattern (_ * _)
        rw [rw1]
      sorry -- nonexistent goal

    have hI' : IntegrableOn (fun (a : ℝ) ↦ cexp (-(I * ↑π * ↑r)) * (I * φ₀'' (-1 / (I * ↑a)) *
      (I * ↑a) ^ 2 * cexp (I * ↑π * ↑r * (I * ↑a)))) (Ici 0) := by
      conv =>
        pattern (_ * _)
        rw [rw2, mul_comm I a, mul_comm I π, mul_assoc I, mul_assoc I]
      conv =>
        pattern (_ - 1)
        rw [sub_eq_add_neg, add_comm]
      exact (integrableOn_goal6 (hb := sorry) r hr)

    rw [sin_eq_exp]
    rw [← integral_const_mul_of_integrable _]
    · simp only [neg_mul, add_mul, sub_mul]
      rw [integral_add (hf := _) (hg := _),
        integral_sub (hf := _) (hg := _)]

      · have : (∫ (a : ℝ) in Ici 0, (cexp (I * ↑π * ↑r) * (I * φ₀'' (-1 / (I * ↑a)) *
          (I * ↑a) ^ 2 * cexp (↑I * π * ↑r * (I * ↑a))))) = φ₀_int_3 r := by
          simp only [rw1, φ₀_int_3_eq r]
        rw [this]

        have : (∫ (a : ℝ) in Ici 0, (cexp (-(I * ↑π * ↑r)) * (I * φ₀'' (-1 / (I * ↑a)) *
          (I * ↑a) ^ 2 * cexp (↑I * π * ↑r * (I * ↑a))))) = φ₀_int_1 r := by
          simp only [rw2, φ₀_int_1_eq r]
        rw [this]

        rw [sub_eq_add_neg, integral_const_mul, ← neg_mul, ← φ₀_int_4]
        ring

      · exact hI
      · apply IntegrableOn.const_mul'
        exact integrableOn_goal1 (hb := sorry) r hr
      · apply Integrable.sub
        · exact hI
        · apply IntegrableOn.const_mul'
          exact integrableOn_goal1 (hb := sorry) r hr
      · apply IntegrableOn.integrable
        exact hI'
    · apply IntegrableOn.integrable
      exact (integrableOn_goal1 (hb := sorry) r hr)


lemma d_eq_1 : d r = I₁' r + I₂' r + I₃' r + I₄' r + I₅' r +
  ∫ t in Ici (1 : ℝ),
  (I * φ₀'' (-1 / (I * t + 1)) * (I * t + 1)^2 *
  cexp (I * π * r * (I * t)) +
  I * φ₀'' (-1 / (I * t - 1)) * (I * t - 1)^2 *
  cexp (I * π * r * (I * t)) +
  -2 * I * φ₀'' (-1 / (I * t)) * (I * t)^2 *
  cexp (I * π * r * (I * t))) := by
  rw [d_eq_2 (hr := hr) _, int_1_eq (hr := hr), int_3_eq (hr := hr)]
  ac_nf; simp only [neg_mul, mul_neg, add_right_inj]
  unfold φ₀_int_5

  rw [← integral_const_mul, ← integral_add sorry sorry]
  ac_nf; simp only [neg_mul, mul_neg]
  rw [← integral_add _ _]

  · refine setIntegral_congr_ae (by measurability) (ae_of_all _ (fun x hx => ?_))
    ring
  · apply Integrable.add
    · apply IntegrableOn.integrable
      apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2
      sorry -- nonexistent goal
    · apply IntegrableOn.integrable
      apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2
      have := integrableOn_goal5 sorry r hr
      ac_nf at this
      exact (IntegrableOn.const_mul' this)
  · sorry

lemma integrand_eq_2φ₀ : ∀ z : ℂ, I * φ₀'' (-1 / (z + 1)) * (z + 1)^2 +
  I * φ₀'' (-1 / (z - 1)) * (z - 1)^2 +
  -2 * I * φ₀'' (-1 / z) * z^2 = 2 * I * φ₀'' z := by
  sorry

theorem d_eq_a : d r = a' r := by
  rw [d_eq_1 (hr := hr) _]
  conv_lhs =>
    pattern (_ * (cexp _) + _ * (cexp _) + _ * (cexp _))
    rw [← add_mul, ← add_mul]
  conv_lhs =>
    pattern (_ * cexp (_))
    rw [integrand_eq_2φ₀ (hr := hr)]
    rw [mul_assoc, mul_assoc]
  unfold a'; simp only [add_right_inj]
  rw [integral_const_mul]
  unfold I₆'; simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
  refine (setIntegral_congr_ae (by measurability) ?_)
  apply ae_of_all; intros a ia
  rw [← z₆'_eq_of_mem ia]
  unfold Φ₆ Φ₆'
  ring_nf
