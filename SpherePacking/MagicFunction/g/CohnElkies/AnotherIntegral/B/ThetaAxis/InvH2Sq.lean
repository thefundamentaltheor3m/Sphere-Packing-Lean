module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis.HExpansions
import SpherePacking.ModularForms.JacobiTheta

/-!
# Inverse-square expansion for `H₂(it)`

This file proves a refined approximation for `((H₂(it))^2)⁻¹` on `t ≥ 1`. We extract the leading
term `exp (2π t) / 256` and the constant correction `-1/32`, and bound the remaining error term by
`O(exp (-2π t))`.

## Main statement
* `exists_bound_norm_inv_H2_sq_sub_exp_add_const_Ici_one`
-/

namespace MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis

open scoped BigOperators UpperHalfPlane

open Real Complex Filter Topology
open Set

noncomputable section

private lemma norm_sub_one_le_of_norm_sub_one_sub (w : ℂ) (u C : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hw_tail : ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ ≤ C * (u ^ (2 : ℕ))) :
    ‖w - (1 : ℂ)‖ ≤ (8 + |C|) * u := by
  have htail' : ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ ≤ |C| * u :=
    hw_tail.trans <| (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hu0 _)).trans
      (mul_le_mul_of_nonneg_left (by simpa [pow_two] using mul_le_of_le_one_right hu0 hu1)
        (abs_nonneg C))
  have h8u : ‖((8 * u : ℝ) : ℂ)‖ = 8 * u := by
    simpa [RCLike.norm_ofReal, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 * u)]
  linarith [show ‖w - 1‖ ≤ ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ + ‖((8 * u : ℝ) : ℂ)‖ by
    simpa [show (w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)) + ((8 * u : ℝ) : ℂ) = w - 1 from by ring] using
      norm_add_le (w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)) ((8 * u : ℝ) : ℂ), htail', h8u.ge]

private lemma Theta2_term_resToImagAxis_eq (n : ℤ) (t : ℝ) (ht : 0 < t) :
    Θ₂_term n ⟨(Complex.I : ℂ) * t, by simp [ht]⟩ =
      (Real.exp (-Real.pi * (((n : ℝ) + (1 / 2 : ℝ)) ^ 2) * t) : ℂ) := by
  set r : ℝ := (n : ℝ) + (2⁻¹ : ℝ)
  have hr : (n + (2⁻¹ : ℂ)) = (r : ℂ) := by apply Complex.ext <;> simp [r]
  have harg : (π * I * (n + (2⁻¹ : ℂ)) ^ 2 * ((Complex.I : ℂ) * t) : ℂ) =
      (-(Real.pi * (r ^ 2) * t) : ℂ) := by
    have hI : (I : ℂ) * ((I : ℂ) * (t : ℂ)) = -(t : ℂ) := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    have hsq : (n + (2⁻¹ : ℂ)) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by simp_all
    grind only
  simpa [Θ₂_term, one_div, r, pow_two, mul_assoc, mul_left_comm, mul_comm] using
    (show Θ₂_term n ⟨(Complex.I : ℂ) * t, by simp [ht]⟩ =
      (Real.exp (-(Real.pi * (r ^ 2) * t)) : ℂ) by simp [Θ₂_term, one_div, harg])

private lemma theta2_norm_ge_two_exp_quarter (t : ℝ) (ht : 0 < t) :
    (2 : ℝ) * Real.exp (-Real.pi * t / 4) ≤ ‖Θ₂.resToImagAxis t‖ := by
  set τ : ℍ := ⟨(Complex.I : ℂ) * t, by simp [ht]⟩
  let g : ℤ → ℝ := fun n => Real.exp (-Real.pi * (((n : ℝ) + (1 / 2 : ℝ)) ^ 2) * t)
  have hterm : ∀ n : ℤ, Θ₂_term n τ = (g n : ℂ) := fun n => by
    simpa [g] using (Theta2_term_resToImagAxis_eq (n := n) (t := t) ht)
  have hsum : Summable (fun n : ℤ => Θ₂_term n τ) := by
    simpa [Θ₂_term_as_jacobiTheta₂_term, mul_assoc] using
      ((summable_jacobiTheta₂_term_iff (z := (τ : ℂ) / 2) (τ := (τ : ℂ))).2
        (by simpa using τ.im_pos)).mul_left (cexp (Real.pi * Complex.I * (τ : ℂ) / 4))
  have hnonneg : ∀ n : ℤ, 0 ≤ g n := fun _ => by positivity
  have hfin : (∑ n ∈ ({0, (-1 : ℤ)} : Finset ℤ), g n) ≤ ∑' n : ℤ, g n := by
    simpa using ((Complex.summable_ofReal).1 (by simpa [hterm] using hsum)).sum_le_tsum
      ({0, (-1 : ℤ)} : Finset ℤ) (fun n _ ↦ hnonneg n)
  have hsum2 : (∑ n ∈ ({0, (-1 : ℤ)} : Finset ℤ), g n) = 2 * Real.exp (-Real.pi * t / 4) := by
    simp [Finset.sum_insert, g, pow_two]; ring_nf
  simpa [Function.resToImagAxis, show ‖ResToImagAxis Θ₂ t‖ = (∑' n : ℤ, g n) from by
    simp [ResToImagAxis, ht, τ, show Θ₂ τ = (↑(∑' n : ℤ, g n) : ℂ) from by
      simp [Θ₂, hterm, g, Complex.ofReal_tsum], abs_of_nonneg (tsum_nonneg hnonneg)]] using
    (by simpa [hsum2] using hfin : 2 * Real.exp (-Real.pi * t / 4) ≤ (∑' n : ℤ, g n))

lemma H2_norm_pow_two_ge (t : ℝ) (ht0 : 0 < t) :
    (256 : ℝ) * Real.exp (-(2 : ℝ) * Real.pi * t) ≤ ‖H₂.resToImagAxis t‖ ^ (2 : ℕ) := by
  have hx_ge : (16 : ℝ) * Real.exp (-Real.pi * t) ≤ ‖H₂.resToImagAxis t‖ := by
    rw [show ‖H₂.resToImagAxis t‖ = ‖Θ₂.resToImagAxis t‖ ^ (4 : ℕ) from by
      simp [H₂, Function.resToImagAxis, ResToImagAxis, ht0, norm_pow],
      show (16 : ℝ) * Real.exp (-Real.pi * t) = (2 * Real.exp (-Real.pi * t / 4)) ^ (4 : ℕ) from by
        rw [mul_pow, ← Real.exp_nat_mul]; ring_nf]
    exact pow_le_pow_left₀ (by positivity) (theta2_norm_ge_two_exp_quarter t ht0) 4
  linarith [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 16 * Real.exp (-Real.pi * t)) hx_ge 2,
    show (16 * Real.exp (-Real.pi * t)) ^ (2 : ℕ) = (256 : ℝ) * Real.exp (-(2 : ℝ) * Real.pi * t)
      from by rw [mul_pow, ← Real.exp_nat_mul]; ring_nf]

private lemma bound_w_inv_sub_one_sub (t u C0 : ℝ) (w : ℂ)
    (hw_norm_ge : (1 : ℝ) ≤ ‖w‖)
    (hw_inv : ‖w⁻¹‖ ≤ 1)
    (hw_tail : ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ ≤ C0 * Real.exp (-(4 : ℝ) * Real.pi * t))
    (hw_one : ‖w - (1 : ℂ)‖ ≤ (8 + C0) * Real.exp (-(2 : ℝ) * Real.pi * t)) :
    ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ ≤ ((8 + C0) ^ 2 + C0) * Real.exp (-(4 : ℝ) * Real.pi * t) := by
  have hid : w⁻¹ - (2 - w) = (w - 1) ^ (2 : ℕ) * w⁻¹ := by
    have : w ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le zero_lt_one hw_norm_ge)
    field_simp; ring
  have htri : ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ ≤
      ‖w⁻¹ - (2 - w)‖ + ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ := by
    rw [show w⁻¹ - (1 - ((8 * u : ℝ) : ℂ)) =
      (w⁻¹ - (2 - w)) - (w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)) from by ring]; exact norm_sub_le _ _
  nlinarith [htri, hw_tail, calc ‖w⁻¹ - (2 - w)‖
        = ‖w - 1‖ ^ (2 : ℕ) * ‖w⁻¹‖ := by simp [hid, norm_pow]
      _ ≤ ‖w - 1‖ ^ (2 : ℕ) := by
          simpa using mul_le_mul_of_nonneg_left hw_inv (by positivity : 0 ≤ ‖w - 1‖ ^ (2 : ℕ))
      _ ≤ ((8 + C0) * Real.exp (-(2 : ℝ) * Real.pi * t)) ^ (2 : ℕ) :=
          pow_le_pow_left₀ (norm_nonneg _) hw_one 2
      _ = (8 + C0) ^ 2 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
          rw [mul_pow, ← Real.exp_nat_mul]; ring_nf]

private lemma hw_tail_bound (t : ℝ) (ht : 1 ≤ t) (CH2 : ℝ)
    (hx_err :
      ‖H₂.resToImagAxis t - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) - (64 : ℂ) *
          (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) :
    ‖(((Real.exp (2 * Real.pi * t) / 256 : ℝ) : ℂ) * (H₂.resToImagAxis t) ^ (2 : ℕ))
          - (1 : ℂ) - ((8 * Real.exp (-(2 : ℝ) * Real.pi * t) : ℝ) : ℂ)‖
        ≤ (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256) * Real.exp (-(4 : ℝ) * Real.pi * t) := by
  set e : ℝ := Real.exp (2 * Real.pi * t)
  set u : ℝ := Real.exp (-(2 : ℝ) * Real.pi * t)
  set A : ℂ := ((e / 256 : ℝ) : ℂ)
  set x : ℂ := H₂.resToImagAxis t
  set w : ℂ := A * (x ^ (2 : ℕ))
  have heu : e * u = 1 := by simp [e, u, ← Real.exp_add]
  set C0 : ℝ := 16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256
  have hw_tail :
      ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ ≤ C0 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
    set main : ℂ :=
      (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) + (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)
    set r : ℂ := x - main
    have hr : ‖r‖ ≤ CH2 * Real.exp (-(5 : ℝ) * Real.pi * t) := by
      simpa [x, show r = x - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) - (64 : ℂ) *
        (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) from by
          simp [r, main, sub_eq_add_neg, add_assoc, add_comm]] using hx_err
    have hq3_le : Real.exp (-(3 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])
    have hmain_norm : ‖main‖ ≤ 80 * Real.exp (-Real.pi * t) := by
      nlinarith [show ‖main‖ ≤
          16 * Real.exp (-Real.pi * t) + 64 * Real.exp (-(3 : ℝ) * Real.pi * t) by
        simpa [main, abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp] using
          norm_add_le ((16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ))
            ((64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)), hq3_le]
    have hu_sq : (u ^ (2 : ℕ) : ℝ) = Real.exp (-(4 : ℝ) * Real.pi * t) := by
      simp only [u, ← Real.exp_nat_mul]; ring_nf
    have hmain_sq :
        ‖main ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)‖ ≤
          (4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t) := by
      have hq1_sq_c : (Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ) = (u : ℂ) := by
        exact_mod_cast congrArg (fun r : ℝ ↦ (r : ℂ))
          (show (Real.exp (-Real.pi * t)) ^ (2 : ℕ) = u by
            simp only [u]; rw [← Real.exp_nat_mul]; congr 1; ring)
      have hq1q3_c : (Real.exp (-Real.pi * t) : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) =
          ((u ^ (2 : ℕ) : ℝ) : ℂ) := by
        rw [hu_sq]; exact_mod_cast congrArg (fun r : ℝ ↦ (r : ℂ))
          (show Real.exp (-Real.pi * t) * Real.exp (-(3 : ℝ) * Real.pi * t) =
              Real.exp (-(4 : ℝ) * Real.pi * t) by rw [← Real.exp_add]; congr 1; ring)
      have hq3_sq_c : (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) ^ (2 : ℕ) =
          (Real.exp (-(6 : ℝ) * Real.pi * t) : ℂ) := by
        exact_mod_cast congrArg (fun r : ℝ ↦ (r : ℂ))
          (show (Real.exp (-(3 : ℝ) * Real.pi * t)) ^ (2 : ℕ) = Real.exp (-(6 : ℝ) * Real.pi * t) by
            rw [← Real.exp_nat_mul]; congr 1; ring)
      rw [show main ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ) =
        (4096 : ℂ) * (Real.exp (-(6 : ℝ) * Real.pi * t) : ℂ) from by grind only]
      simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
    have hsq : ‖x ^ (2 : ℕ) - main ^ (2 : ℕ)‖ ≤
          (160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) +
            (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2 :=
      calc ‖x ^ (2 : ℕ) - main ^ (2 : ℕ)‖ = ‖r‖ * ‖x + main‖ := by
            rw [show x ^ 2 - main ^ 2 = (x - main) * (x + main) from by ring, norm_mul]
        _ ≤ ‖r‖ * ((160 * Real.exp (-Real.pi * t)) + ‖r‖) := by
            gcongr
            nlinarith [norm_add_le x main, norm_le_norm_add_norm_sub' x main, hmain_norm]
        _ = (160 * Real.exp (-Real.pi * t)) * ‖r‖ + ‖r‖ ^ 2 := by ring
        _ ≤ (160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) +
              (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2 := by gcongr
    have he256 : 0 ≤ e / 256 := by positivity
    have hA_norm : ‖A‖ = e / 256 := by
      simpa [A, abs_of_nonneg he256] using (RCLike.norm_ofReal (K := ℂ) (e / 256))
    have hw_rewrite : w - (1 : ℂ) - ((8 * u : ℝ) : ℂ) =
        A * (x ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)) := by
      have h256' : A * ((256 * u : ℝ) : ℂ) = (1 : ℂ) := by
        simp only [A]; exact_mod_cast congrArg (fun r : ℝ ↦ (r : ℂ))
          (show (e / 256) * (256 * u) = 1 by linear_combination heu)
      have h2048' : A * ((2048 * (u ^ (2 : ℕ) : ℝ) : ℝ) : ℂ) = ((8 * u : ℝ) : ℂ) := by
        simp only [A]; exact_mod_cast congrArg (fun r : ℝ ↦ (r : ℂ))
          (show (e / 256) * (2048 * (u ^ (2 : ℕ) : ℝ)) = 8 * u by
            rw [show (u ^ (2 : ℕ) : ℝ) = u * u from by ring]; linear_combination 8 * u * heu)
      rw [show A * (x ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)) =
        A * (x ^ (2 : ℕ)) - A * ((256 * u : ℝ) : ℂ) - A * ((2048 * (u ^ (2 : ℕ) : ℝ) : ℝ) : ℂ)
        from by push_cast; ring, h256', h2048']
    have hbr : ‖x ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)‖
        ≤ (4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t) +
            (160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) +
            (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2 := by
      have htri := norm_add_le (x ^ (2 : ℕ) - main ^ (2 : ℕ))
        (main ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ))
      grind only
    have he6 : e * Real.exp (-(6 : ℝ) * Real.pi * t) = Real.exp (-(4 : ℝ) * Real.pi * t) := by
      simp only [e, ← Real.exp_add]; congr 1; ring
    have he15 : e * (Real.exp (-Real.pi * t) * Real.exp (-(5 : ℝ) * Real.pi * t)) =
        Real.exp (-(4 : ℝ) * Real.pi * t) := by
      simp only [e, ← Real.exp_add]; congr 1; ring
    have h1 : (e / 256) * ((4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t)) =
        16 * Real.exp (-(4 : ℝ) * Real.pi * t) := by linear_combination 16 * he6
    have h2 :
      (e / 256) * ((160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t))) =
        (160 / 256) * CH2 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
      linear_combination (160 / 256 : ℝ) * CH2 * he15
    have h3 : (e / 256) * ((CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2) ≤
        (CH2 ^ 2) / 256 * Real.exp (-(4 : ℝ) * Real.pi * t) :=
      calc (e / 256) * ((CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2)
          = (CH2 ^ 2) / 256 * (e * (Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2) := by ring
        _ = (CH2 ^ 2) / 256 * Real.exp (-(8 : ℝ) * Real.pi * t) := by
            rw [show e * (Real.exp (-(5 : ℝ) * Real.pi * t)) ^ (2 : ℕ) =
                Real.exp (-(8 : ℝ) * Real.pi * t) by
              simp only [e, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring]
        _ ≤ (CH2 ^ 2) / 256 * Real.exp (-(4 : ℝ) * Real.pi * t) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
              (by nlinarith [Real.pi_pos, ht])) (by positivity)
    calc
      ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖
          = ‖A‖ * ‖x ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)‖ := by
            rw [hw_rewrite]; simp
      _ ≤ (e / 256) *
            ((4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t) +
              (160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) +
              (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2) := by
            rw [hA_norm]; exact mul_le_mul_of_nonneg_left hbr he256
      _ ≤ C0 * Real.exp (-(4 : ℝ) * Real.pi * t) := by grind only
  simpa [w, A, x, e, u, C0] using hw_tail

/-- Refined inverse-square expansion for `H₂(it)` extracting the constant `-1/32`. -/
public lemma exists_bound_norm_inv_H2_sq_sub_exp_add_const_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖((H₂.resToImagAxis t) ^ (2 : ℕ))⁻¹
          - ((Real.exp (2 * Real.pi * t) / 256 : ℝ) : ℂ)
          + ((1 / 32 : ℝ) : ℂ)‖
        ≤ C * Real.exp (-(2 : ℝ) * Real.pi * t) := by
  rcases exists_bound_norm_H2_resToImagAxis_sub_two_terms_Ici_one with ⟨CH2, hH2⟩
  refine ⟨(256 * ((8 + (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256)) ^ 2 +
        (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256))) , ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set e : ℝ := Real.exp (2 * Real.pi * t)
  set u : ℝ := Real.exp (-(2 : ℝ) * Real.pi * t)
  set A : ℂ := ((e / 256 : ℝ) : ℂ)
  set x : ℂ := H₂.resToImagAxis t
  set w : ℂ := A * (x ^ (2 : ℕ))
  have he256 : 0 ≤ e / 256 := by positivity
  have hA_norm : ‖A‖ = e / 256 := by
    simpa [A, abs_of_nonneg he256] using (RCLike.norm_ofReal (K := ℂ) (e / 256))
  have hCH2 : 0 ≤ CH2 :=
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hH2 1 le_rfl)) (Real.exp_pos _)
  set C0 : ℝ := 16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256
  have hC0 : 0 ≤ C0 := by positivity
  have heu : e * u = 1 := by simp [e, u, ← Real.exp_add]
  have hmain_id :
      ((x ^ (2 : ℕ))⁻¹ - A + ((1 / 32 : ℝ) : ℂ)) = A * (w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))) := by
    have hA0 : A ≠ 0 := ofReal_ne_zero.mpr (div_ne_zero (ne_of_gt (Real.exp_pos _)) (by norm_num))
    have hAw : A * w⁻¹ = (x ^ (2 : ℕ))⁻¹ := by
      simp [w, mul_inv_rev, hA0, mul_comm, mul_left_comm]
    have hA8u : A * ((8 * u : ℝ) : ℂ) = ((1 / 32 : ℝ) : ℂ) := by
      simpa [A, Complex.ofReal_mul, mul_assoc, mul_left_comm, mul_comm] using
        congrArg (fun r : ℝ ↦ (r : ℂ))
          (show (e / 256) * (8 * u) = (1 / 32 : ℝ) by linear_combination (8 / 256 : ℝ) * heu)
    rw [show (x ^ (2 : ℕ))⁻¹ - A + ((1 / 32 : ℝ) : ℂ)
        = A * w⁻¹ - A + A * ((8 * u : ℝ) : ℂ) from by rw [hAw, hA8u]]; ring
  have hw_tail : ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ ≤ C0 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
    simpa [w, A, x, e, u, C0] using
      (hw_tail_bound (t := t) (ht := ht) (CH2 := CH2) (by simpa [x] using hH2 t ht))
  have hu_sq : u ^ (2 : ℕ) = Real.exp (-(4 : ℝ) * Real.pi * t) := by
    simp only [u, ← Real.exp_nat_mul]; ring_nf
  have hw_one : ‖w - (1 : ℂ)‖ ≤ (8 + C0) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
    simpa [u, abs_of_nonneg hC0] using
      norm_sub_one_le_of_norm_sub_one_sub w u C0 (Real.exp_pos _).le
        (Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht])) (by simpa [hu_sq] using hw_tail)
  have hw_norm_ge : (1 : ℝ) ≤ ‖w‖ := by
    rw [show ‖w‖ = (e / 256) * ‖x‖ ^ (2 : ℕ) from by simp [w, hA_norm, norm_pow]]
    linarith [mul_le_mul_of_nonneg_left (show (256 : ℝ) * u ≤ ‖x‖ ^ (2 : ℕ) by
        simpa [x, u] using H2_norm_pow_two_ge (t := t) ht0) he256,
      show (e / 256) * ((256 : ℝ) * u) = 1 from by linear_combination heu]
  have hw_inv : ‖w⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hw_norm_ge
  have hdiff : ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ ≤
      ((8 + C0) ^ 2 + C0) * Real.exp (-(4 : ℝ) * Real.pi * t) :=
    bound_w_inv_sub_one_sub (t := t) (u := u) (C0 := C0) (w := w)
      hw_norm_ge hw_inv hw_tail hw_one
  set K : ℝ := (8 + C0) ^ 2 + C0
  calc ‖((H₂.resToImagAxis t) ^ (2 : ℕ))⁻¹
          - ((Real.exp (2 * Real.pi * t) / 256 : ℝ) : ℂ)
          + ((1 / 32 : ℝ) : ℂ)‖
      = ‖A‖ * ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ := by rw [hmain_id, norm_mul]
    _ ≤ (e / 256) * (K * Real.exp (-(4 : ℝ) * Real.pi * t)) := by
        rw [hA_norm]; exact mul_le_mul_of_nonneg_left hdiff he256
    _ = (1 / 256 : ℝ) * K * Real.exp (-(2 : ℝ) * Real.pi * t) := by
        have he4 : e * Real.exp (-(4 : ℝ) * Real.pi * t) =
            Real.exp (-(2 : ℝ) * Real.pi * t) := by
          simp only [e, ← Real.exp_add]; congr 1; ring
        linear_combination (K / 256 : ℝ) * he4
    _ ≤ (256 * ((8 + (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256)) ^ 2 +
          (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256))) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
        simp only [show (8 + (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256)) ^ 2 +
          (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256) = K from by simp [K, C0]]
        gcongr; nlinarith [show (0:ℝ) ≤ K from by positivity]

end

end MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis
