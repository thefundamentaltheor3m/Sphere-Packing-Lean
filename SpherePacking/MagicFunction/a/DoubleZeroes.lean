/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tito Sacchi
-/

import SpherePacking.ModularForms.Eisenstein
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.a.VerticalIntegrability
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}

lemma const_add_variable_change [MulOneClass E] (x₁ x₂ x₁' : ℝ)
  {hf : ContinuousOn f (Set.uIcc x₁ x₂)} :
  ∫ t in x₁..x₂, f t =
  ∫ t in x₁'..(x₁' + (x₂ - x₁)), f (t - (x₁' - x₁)) := by
  set g := fun t ↦ t - (x₁' - x₁)
  have gx₁ : g x₁' = x₁ := by unfold g; simp
  rw [← gx₁]
  have gx₂ : g (x₁' + (x₂ - x₁)) = x₂ := by unfold g; simp
  rw [← gx₂]
  conv_lhs =>
    pattern (f _)
    rw [← one_mul (f t)]
  have : ∀ x, HasDerivAt g 1 x := by
    intro x
    unfold g;
    simpa using (hasDerivAt_id' x)
  have : ∀ t, g t = (t - (x₁' - x₁)) := by unfold g; simp
  rw [← intervalIntegral.integral_comp_smul_deriv' (f := g) (f' := fun _ ↦ 1)]
  · unfold g
    simp
  · intro x
    unfold g; simp only [hasDerivAt_sub_const_iff]; intro
    exact hasDerivAt_id' x
  · exact continuousOn_const
  · have : g '' Set.uIcc x₁' (x₁' + (x₂ - x₁)) ⊆ Set.uIcc x₁ x₂ := by
      conv_rhs =>
        rw [← gx₁, ← gx₂]
      apply Monotone.image_uIcc_subset
      exact Monotone.add_const monotone_id _
    simp only [one_mul]
    exact (ContinuousOn.mono hf this)

lemma sign_variable_change (x₁ x₂ : ℝ) :
  ∫ t in x₁..x₂, f t =
  ∫ t in -x₁..-x₂, - f (- t) := by
  rw [intervalIntegral.integral_symm]
  simp

end

noncomputable section

open Set Complex Real MeasureTheory
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
open MagicFunction.a.RealIntegrands MagicFunction.a.ComplexIntegrands
open MagicFunction.VerticalIntegrability MagicFunction.ContourEndpoints

lemma φ₀''_differentiable : DifferentiableOn ℂ φ₀'' (Set.univ ×ℂ Ioi 0) := by
  convert φ₀''_holo
  ext
  constructor
  · intro ⟨_, hx⟩; exact hx
  · intro hx; exact ⟨Set.mem_univ _, hx⟩

lemma cadd_real_neq_zero {r : ℝ} {x : ℂ} {hx : x ∈ Set.univ ×ℂ Ioi 0} : x + r ≠ 0 := by
  obtain ⟨_, hx_im⟩ := hx
  simp at hx_im
  by_contra
  have h : (x + r).im = x.im := by simp only [add_im, ofReal_im, add_zero]
  simp only [← h, this, zero_im, lt_self_iff_false] at hx_im

lemma inv_cadd_real_continuous {r : ℝ} :
  ContinuousOn (fun (x : ℂ) ↦ -1 / (x + r)) (Set.univ ×ℂ Ioi 0) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact cadd_real_neq_zero (hx := hx)

lemma inv_cadd_real_continuous' {a b c r : ℝ} {hc : c > 0} :
  ContinuousOn (fun (x : ℂ) ↦ -1 / (x + r)) (Set.uIcc a b ×ℂ Ici c) := by
  refine (ContinuousOn.mono inv_cadd_real_continuous ?_)
  intro x ⟨hx_re, hx_im⟩
  exact ⟨Set.mem_univ _, (lt_of_lt_of_le hc hx_im)⟩

lemma inv_cadd_real_differentiable {r : ℝ} :
  DifferentiableOn ℂ (fun (x : ℂ) ↦ -1 / (x + r)) (Set.univ ×ℂ Ioi 0) := by
  apply DifferentiableOn.div
  · fun_prop
  · fun_prop
  · intros x hx; exact cadd_real_neq_zero (hx := hx)

lemma inv_cadd_real_image {r : ℝ} : MapsTo (fun (x : ℂ) ↦ -1 / (x + r))
  (univ ×ℂ Ioi 0) (univ ×ℂ Ioi 0) := by
  intro x ⟨hx_re, hx_im⟩
  obtain ⟨Re_x, ⟨Im_x, hx_eq, hIm_x⟩⟩ :
    ∃ Re_x : ℝ, ∃ Im_x : ℝ, x = Re_x + Im_x * Complex.I ∧ Im_x > 0 := by
    exact ⟨ x.re, x.im, by simp only [re_add_im], hx_im⟩;
  have : Complex.im (-1 / (x + r)) > 0 := by
    simp [hx_eq, Complex.div_im]
    refine (div_neg_of_neg_of_pos (by simpa [hx_im]) (Complex.normSq_pos.mpr ?_))
    by_contra
    obtain ⟨_, this⟩ := (Complex.ext_iff.1 this)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add, zero_im] at this
    simp [this] at hIm_x
  exact ⟨Set.mem_univ _, this⟩

lemma φ₀''_integrand_differentiable {r : ℝ} :
  DifferentiableOn ℂ (fun z ↦ φ₀'' (-1 / (z + r))) (Set.univ ×ℂ Ioi 0) := by
  apply DifferentiableOn.fun_comp
  · exact φ₀''_differentiable
  · exact inv_cadd_real_differentiable
  · exact inv_cadd_real_image

lemma UpperHalfPlane_open_nhd {x : ℂ} {hx : x ∈ Set.univ ×ℂ Set.Ioi 0} :
  Set.univ ×ℂ Set.Ioi 0 ∈ nhds x := by
  refine IsOpen.mem_nhds ?_ hx
  have h_open : IsOpen (Set.univ : Set (ℝ × ℝ)) ∧ IsOpen (Set.Ioi (0 : ℝ)) := by
    exact ⟨ isOpen_univ, isOpen_Ioi ⟩;
  convert h_open.1.prod h_open.2
  constructor
  · exact fun h => h_open.1.prod h_open.2;
  · intro h
    convert h.preimage _
    rotate_left
    · exact fun x => ( ( x.re, x.im ), x.im );
    · fun_prop
    · exact Subset.antisymm (fun ⦃a⦄ a_1 ↦ a_1) fun ⦃a⦄ a_1 ↦ a_1

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
    exact (integrableOn_goal1 r hr)

lemma cauchy_goursat_int_1 : ∫ (t : ℝ) in Ioi 1, I * integrand_1 r (-1 + t * I) =
  (∫ (x : ℝ) in -1..0, integrand_1 r (x + 1 * I)) +
  I • ∫ (t : ℝ) in Ioi 1, integrand_1 r (0 + t * I) := by
  rw [integral_const_mul]
  rw [← smul_eq_mul]
  -- set g := fun (z : ℂ) => if z.re ∈ Icc (-1) 1 then integrand_1 r z else 0

  -- -- Big rewriting to do here with g
  -- have integrand_1_eq_g : integrand_1 r = g := by sorry
  -- rw [integrand_1_eq_g]

  have : (-1 : ℝ) = (-1 : ℂ) := by simp
  rw [← this, ← sub_eq_zero.1
   (integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
    1 _ ∅ _ _ _ _ _)]
  · rfl

  · unfold integrand_1
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · refine (ContinuousOn.comp' φ₀''_differentiable.continuousOn
          (?_ : ContinuousOn (fun (t : ℂ) => (-1 / (t + 1))) _) ?_)
        · apply inv_cadd_real_continuous'; simp
        · refine MapsTo.mono_left inv_cadd_real_image ?_
          intro x ⟨hx_re, hx_im⟩
          exact ⟨Set.mem_univ _, (lt_of_lt_of_le ((by simp) : (0 : ℝ) < 1) hx_im)⟩
      · fun_prop
    · fun_prop
  · exact countable_empty
  · intros x hx
    unfold integrand_1
    apply DifferentiableAt.mul
    · apply DifferentiableAt.mul
      · apply DifferentiableOn.differentiableAt φ₀''_integrand_differentiable
        apply UpperHalfPlane_open_nhd
        obtain ⟨⟨hx_re, hx_im⟩, _⟩ := hx
        constructor
        · simp
        · simp only [mem_preimage, mem_Ioi] at hx_im
          exact (lt_trans (by simp) hx_im)
      · fun_prop
    · fun_prop
  · unfold integrand_1
    simp only [ofReal_neg, ofReal_one, neg_add_cancel_comm]
    exact (integrableOn_goal2 r hr)
  · unfold integrand_1
    simp only [ofReal_zero, zero_add]
    apply (integrableOn_goal3 r hr)
  · intro ε hε
    sorry
    -- obtain ⟨M, s⟩ := uniform_vanishing_topEdgeIntegrand r hr ε hε
    -- use M
    -- intro z hz
    -- have s := s (z.re + 1) z.im hz
    -- convert s
    -- unfold integrand_1; unfold verticalIntegrandX


lemma cauchy_goursat_int_3 : ∫ (t : ℝ) in Ioi 1, I * integrand_3 r (1 + t * I) =
  (∫ (x : ℝ) in 1..0, integrand_3 r (x + 1 * I)) +
  I • ∫ (t : ℝ) in Ioi 1, integrand_3 r (0 + t * I) := by
  have neg_one_coe : ↑(-1 : ℝ) = (-1 : ℂ) := by simp
  rw [integral_const_mul]
  rw [← smul_eq_mul]
  have : (1 : ℝ) = (1 : ℂ) := by simp
  rw [← this, ← (sub_eq_zero.1)
   (integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
    1 _ ∅ _ _ _ _ _)]
  · rfl
  · unfold integrand_3
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · conv =>
          pattern (_ - _)
          rw [sub_eq_add_neg, ← neg_one_coe]
        refine (ContinuousOn.comp' φ₀''_differentiable.continuousOn
          (?_ : ContinuousOn (fun (t : ℂ) => (-1 / (t + ↑(-1 : ℝ)))) _) ?_)
        · apply inv_cadd_real_continuous'; simp
        · refine MapsTo.mono_left inv_cadd_real_image ?_
          intro x ⟨hx_re, hx_im⟩
          exact ⟨Set.mem_univ _, (lt_of_lt_of_le ((by simp) : (0 : ℝ) < 1) hx_im)⟩
      · fun_prop
    · fun_prop
  · exact countable_empty
  · intros x hx
    unfold integrand_3
    conv =>
      pattern (_ - _)
      rw [sub_eq_add_neg, ← neg_one_coe]
    apply DifferentiableAt.mul
    · apply DifferentiableAt.mul
      · apply DifferentiableOn.differentiableAt φ₀''_integrand_differentiable
        apply UpperHalfPlane_open_nhd
        obtain ⟨⟨hx_re, hx_im⟩, _⟩ := hx
        constructor
        · simp
        · simp only [mem_preimage, mem_Ioi] at hx_im
          exact (lt_trans (by simp) hx_im)
      · fun_prop
    · fun_prop
  · unfold integrand_3
    simp only [ofReal_one, add_sub_cancel_left]
    exact (integrableOn_goal4 r hr)
  · unfold integrand_3
    simp only [ofReal_zero, zero_add]
    apply (integrableOn_goal5 r hr)
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
        rw [const_add_variable_change (hf := _) 0 1 (-1)]
        · simp only [sub_zero, neg_add_cancel]
          apply intervalIntegral.integral_congr
          simp only [EqOn, Left.neg_nonpos_iff, zero_le_one, uIcc_of_le, mem_Icc, one_mul,
            sub_neg_eq_add, ofReal_add, ofReal_one, neg_mul, and_imp]
          intro x hx hx'
          conv_rhs =>
            rw [mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
          congr 3 <;> ring_nf
          rw [I_sq]; ring
        · repeat refine (ContinuousOn.mul ?_ (by fun_prop))
          have : (fun (t : ℝ) => φ₀'' (-1 / (↑t + I))) =
            (fun z => φ₀'' (-1 / (z + ↑(0 : ℝ)))) ∘ (fun (t : ℝ) => ↑t + I) := by funext; simp
          rw [this]
          apply ContinuousOn.comp (ContinuousOn.comp φ₀''_differentiable.continuousOn
            inv_cadd_real_continuous inv_cadd_real_image)
          · fun_prop
          · intros x hx
            exact ⟨Set.mem_univ _, (by simp)⟩
      · rw [smul_eq_mul, ← integral_const_mul, integral_Ici_eq_integral_Ioi]
        refine (setIntegral_congr_ae (by measurability) (ae_of_all _ (fun x hx => ?_)))
        unfold integrand_1
        ring_nf
  · apply IntegrableOn.integrable
    unfold integrand_1
    simp only [neg_add_cancel_comm]
    exact (integrableOn_goal6 r hr)

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
        rw [const_add_variable_change (hf := _) 1 0 0];
        · simp only [zero_sub, sub_neg_eq_add, ofReal_add,
            ofReal_one, one_mul, zero_add, neg_mul]
          rw [sign_variable_change 0 (-1)]
          simp only [ofReal_neg, neg_zero, neg_neg, intervalIntegral.integral_neg, neg_inj]
          apply intervalIntegral.integral_congr
          simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, and_imp]; intro x hx hx'
          conv_rhs =>
            rw [mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
          congr 3 <;> ring_nf
          rw [I_sq]; ring
        · repeat refine (ContinuousOn.mul ?_ (by fun_prop))
          have : (fun (t : ℝ) => φ₀'' (-1 / (↑t + 1 * I - 1))) =
            (fun z => φ₀'' (-1 / (z + ↑(-1 : ℝ)))) ∘ (fun (t : ℝ) => ↑t + I) := by funext; simp; rfl
          rw [this]
          apply ContinuousOn.comp (ContinuousOn.comp φ₀''_differentiable.continuousOn
            inv_cadd_real_continuous inv_cadd_real_image)
          · fun_prop
          · intros x hx
            exact ⟨Set.mem_univ _, (by simp)⟩
      · rw [smul_eq_mul, ← integral_const_mul, integral_Ici_eq_integral_Ioi]
        refine (setIntegral_congr_ae (by measurability) (ae_of_all _ (fun x hx => ?_)))
        unfold integrand_3
        ring_nf
  · apply IntegrableOn.integrable
    unfold integrand_3
    simp only [add_sub_cancel_left]
    exact (integrableOn_goal7 r hr)

lemma d_eq_2 : d r = φ₀_int_1 r + I₅' r + φ₀_int_5 r + φ₀_int_3 r := by
  calc
      _ =  -4 * (Complex.sin (Real.pi * r / 2) ^ 2) *
              ∫ t in Ici (0 : ℝ), I * φ₀'' (-1 / (I * t)) *
              (I * t)^2 * cexp (I * π * r * (I * t)) := rfl
      _ = φ₀_int_1 r + φ₀_int_4 r + φ₀_int_3 r := ?_
      _ = φ₀_int_1 r + I₅' r + φ₀_int_5 r + φ₀_int_3 r := by
        simp only [φ₀_int_4_eq r (hr := hr), add_left_inj]
        ring
  have rw1 (z : ℂ) : cexp (I * ↑π * ↑r) * (I * φ₀'' (-1 / (I * z)) *
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
      rw [rw1, mul_comm I a, mul_comm I π, mul_assoc I, mul_assoc I]
    conv =>
      pattern (_ + 1)
      rw [add_comm]
    exact (integrableOn_goal7 r hr)
  have hI' : IntegrableOn (fun (a : ℝ) ↦ cexp (-(I * ↑π * ↑r)) * (I * φ₀'' (-1 / (I * ↑a)) *
    (I * ↑a) ^ 2 * cexp (I * ↑π * ↑r * (I * ↑a)))) (Ici 0) := by
    conv =>
      pattern (_ * _)
      rw [rw2, mul_comm I a, mul_comm I π, mul_assoc I, mul_assoc I]
    conv =>
      pattern (_ - 1)
      rw [sub_eq_add_neg, add_comm]
    exact (integrableOn_goal6 r hr)
  rw [sin_eq_exp, ← integral_const_mul_of_integrable _]
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
      exact integrableOn_goal1 r hr
    · apply Integrable.sub
      · exact hI
      · apply IntegrableOn.const_mul'
        exact integrableOn_goal1 r hr
    · apply IntegrableOn.integrable
      exact hI'
  · apply IntegrableOn.integrable
    exact (integrableOn_goal1 r hr)


lemma d_eq_1 : d r = I₁' r + I₂' r + I₃' r + I₄' r + I₅' r +
  ∫ t in Ici (1 : ℝ),
  (I * φ₀'' (-1 / (I * t + 1)) * (I * t + 1)^2 *
  cexp (I * π * r * (I * t)) +
  I * φ₀'' (-1 / (I * t - 1)) * (I * t - 1)^2 *
  cexp (I * π * r * (I * t)) +
  -2 * I * φ₀'' (-1 / (I * t)) * (I * t)^2 *
  cexp (I * π * r * (I * t))) := by
  have hI : Integrable (fun (t : ℝ) ↦ I * (cexp (I * (I * (↑r * (↑t * ↑π)))) *
    (φ₀'' (-1 / (1 + I * ↑t)) * (1 + I * ↑t) ^ 2))) (volume.restrict (Ici 1)) := by
    apply IntegrableOn.integrable
    apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2
    have := integrableOn_goal3 r hr
    ac_nf at this
    exact (IntegrableOn.const_mul' this)
  have hI' : Integrable (fun (a : ℝ) ↦ I * (cexp (I * (I * (↑r * (↑a * ↑π)))) *
    (φ₀'' (-1 / (I * ↑a - 1)) * (I * ↑a - 1) ^ 2))) (volume.restrict (Ici 1)) := by
    apply IntegrableOn.integrable
    apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2
    have := integrableOn_goal5 r hr
    ac_nf at this
    exact (IntegrableOn.const_mul' this)
  rw [d_eq_2 (hr := hr) _, int_1_eq (hr := hr), int_3_eq (hr := hr)]
  ac_nf; simp only [neg_mul, mul_neg, add_right_inj]
  unfold φ₀_int_5
  rw [← integral_const_mul, ← integral_add _ _]
  · ac_nf; simp only [neg_mul, mul_neg]
    rw [← integral_add _ _]
    · refine setIntegral_congr_ae (by measurability) (ae_of_all _ (fun x hx => ?_))
      ring
    · exact (Integrable.add hI hI')
    · apply Integrable.neg
      apply Integrable.const_mul
      conv =>
        pattern (_ * _)
        rw [← mul_assoc, mul_comm, mul_assoc]
      apply Integrable.const_mul
      have := integrableOn_shiftedMöbius 0 r hr
      simp only [ofReal_zero, add_zero] at this
      ac_nf; ac_nf at this
      apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2
      exact this
  · exact hI
  · exact hI'

lemma integrand_eq_2φ₀ : ∀ z : ℂ, I * φ₀'' (-1 / (z + 1)) * (z + 1)^2 +
  I * φ₀'' (-1 / (z - 1)) * (z - 1)^2 +
  -2 * I * φ₀'' (-1 / z) * z^2 = 2 * I * φ₀'' z := by
  intro z
  by_cases z ∈ UpperHalfPlane.upperHalfPlaneSet
  unfold φ₀''

theorem d_eq_a : d r = a' r := by
  rw [d_eq_1 (hr := hr) _]
  conv_lhs =>
    pattern (_ * (cexp _) + _ * (cexp _) + _ * (cexp _))
    rw [← add_mul, ← add_mul]
  -- TODO: Rewrite under binder here using assumption
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
