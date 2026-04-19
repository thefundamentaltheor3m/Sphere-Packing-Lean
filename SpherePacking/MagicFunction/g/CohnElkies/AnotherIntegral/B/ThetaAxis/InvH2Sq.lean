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

/-
The final estimate for `((H₂(it))^2)⁻¹` needs a lower bound for `H₂(it)` (to control `‖w⁻¹‖`)
and a small quadratic estimate for inverting a number close to `1`.
These auxiliary lemmas are proven below.
-/

lemma norm_sub_one_le_of_norm_sub_one_sub (w : ℂ) (u C : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hw_tail : ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ ≤ C * (u ^ (2 : ℕ))) :
    ‖w - (1 : ℂ)‖ ≤ (8 + |C|) * u := by
  have h8u : ‖((8 * u : ℝ) : ℂ)‖ = 8 * u := by
    have hnonneg : (0 : ℝ) ≤ 8 * u := mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hu0
    simpa [RCLike.norm_ofReal, abs_of_nonneg hnonneg]
  have htail' : ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ ≤ |C| * u := by
    have hE0 : 0 ≤ (u ^ (2 : ℕ) : ℝ) := pow_nonneg hu0 _
    have hC : C * (u ^ (2 : ℕ) : ℝ) ≤ |C| * (u ^ (2 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hE0
    have hpow : (u ^ (2 : ℕ) : ℝ) ≤ u := by
      simpa [pow_two] using (mul_le_of_le_one_right hu0 hu1)
    exact hw_tail.trans <| hC.trans <| mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
  calc
    ‖w - (1 : ℂ)‖ = ‖(w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)) + ((8 * u : ℝ) : ℂ)‖ := by ring_nf
    _ ≤ ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ + ‖((8 * u : ℝ) : ℂ)‖ := by
          simpa using
            (norm_add_le (w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)) ((8 * u : ℝ) : ℂ))
    _ ≤ (|C| * u) + (8 * u) := add_le_add htail' (le_of_eq h8u)
    _ = (8 + |C|) * u := by ring

lemma Theta2_term_resToImagAxis_eq (n : ℤ) (t : ℝ) (ht : 0 < t) :
    Θ₂_term n ⟨(Complex.I : ℂ) * t, by simp [ht]⟩ =
      (Real.exp (-Real.pi * (((n : ℝ) + (1 / 2 : ℝ)) ^ 2) * t) : ℂ) := by
  set r : ℝ := (n : ℝ) + (2⁻¹ : ℝ)
  have hr : (n + (2⁻¹ : ℂ)) = (r : ℂ) := by
    apply Complex.ext <;> simp [r]
  have hsq : (n + (2⁻¹ : ℂ)) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by
    simp_all
  have harg :
      (π * I * (n + (2⁻¹ : ℂ)) ^ 2 * ((Complex.I : ℂ) * t) : ℂ) =
        (-(Real.pi * (r ^ 2) * t) : ℂ) := by
    have hI : (I : ℂ) * ((I : ℂ) * (t : ℂ)) = -(t : ℂ) := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    grind only
  have :
      Θ₂_term n ⟨(Complex.I : ℂ) * t, by simp [ht]⟩ =
        (Real.exp (-(Real.pi * (r ^ 2) * t)) : ℂ) := by
    simp [Θ₂_term, one_div, harg]
  simpa [Θ₂_term, one_div, r, pow_two, mul_assoc, mul_left_comm, mul_comm] using this

lemma theta2_norm_ge_two_exp_quarter (t : ℝ) (ht : 0 < t) :
    (2 : ℝ) * Real.exp (-Real.pi * t / 4) ≤ ‖Θ₂.resToImagAxis t‖ := by
  set τ : ℍ := ⟨(Complex.I : ℂ) * t, by simp [ht]⟩
  let g : ℤ → ℝ := fun n => Real.exp (-Real.pi * (((n : ℝ) + (1 / 2 : ℝ)) ^ 2) * t)
  have hterm : ∀ n : ℤ, Θ₂_term n τ = (g n : ℂ) := by
    intro n
    simpa [g] using (Theta2_term_resToImagAxis_eq (n := n) (t := t) ht)
  have hsum : Summable (fun n : ℤ => Θ₂_term n τ) := by
    have hs : Summable (fun n : ℤ => jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)) :=
      (summable_jacobiTheta₂_term_iff (z := (τ : ℂ) / 2) (τ := (τ : ℂ))).2
        (by simpa using τ.im_pos)
    simpa [Θ₂_term_as_jacobiTheta₂_term, mul_assoc] using
      hs.mul_left (cexp (Real.pi * Complex.I * (τ : ℂ) / 4))
  have hsumg : Summable g := (Complex.summable_ofReal).1 (by simpa [hterm] using hsum)
  have hnonneg : ∀ n : ℤ, 0 ≤ g n := fun _ => by positivity
  have hfin :
      (∑ n ∈ ({0, (-1 : ℤ)} : Finset ℤ), g n) ≤ ∑' n : ℤ, g n := by
    simpa using hsumg.sum_le_tsum ({0, (-1 : ℤ)} : Finset ℤ) (fun n _ => hnonneg n)
  have hsum2 :
      (∑ n ∈ ({0, (-1 : ℤ)} : Finset ℤ), g n) = 2 * Real.exp (-Real.pi * t / 4) := by
    have hne : (0 : ℤ) ≠ (-1 : ℤ) := by decide
    calc
      (∑ n ∈ ({0, (-1 : ℤ)} : Finset ℤ), g n) = g 0 + g (-1) := by
        simp [Finset.sum_insert, hne]
      _ = 2 * Real.exp (-Real.pi * t / 4) := by
        simp [g, pow_two]
        ring_nf
  have htsum : Θ₂ τ = (↑(∑' n : ℤ, g n) : ℂ) := by
    simp [Θ₂, hterm, g, Complex.ofReal_tsum]
  have hnorm : ‖ResToImagAxis Θ₂ t‖ = (∑' n : ℤ, g n) := by
    have hpos : 0 ≤ (∑' n : ℤ, g n) := tsum_nonneg hnonneg
    simp [ResToImagAxis, ht, τ, htsum, abs_of_nonneg hpos]
  have hsum_ge : 2 * Real.exp (-Real.pi * t / 4) ≤ (∑' n : ℤ, g n) := by
    simpa [hsum2] using hfin
  simpa [Function.resToImagAxis, hnorm] using hsum_ge

lemma pow_four_two_mul_exp (t : ℝ) :
    (2 * Real.exp (-Real.pi * t / 4)) ^ (4 : ℕ) = (16 : ℝ) * Real.exp (-Real.pi * t) := by
  rw [mul_pow, ← Real.exp_nat_mul]
  ring_nf

lemma H2_norm_pow_two_ge (t : ℝ) (ht0 : 0 < t) :
    (256 : ℝ) * Real.exp (-(2 : ℝ) * Real.pi * t) ≤ ‖H₂.resToImagAxis t‖ ^ (2 : ℕ) := by
  have hTheta2_ge : (2 : ℝ) * Real.exp (-Real.pi * t / 4) ≤ ‖Θ₂.resToImagAxis t‖ :=
    theta2_norm_ge_two_exp_quarter t ht0
  have hx_ge : (16 : ℝ) * Real.exp (-Real.pi * t) ≤ ‖H₂.resToImagAxis t‖ := by
    have hH2norm : ‖H₂.resToImagAxis t‖ = ‖Θ₂.resToImagAxis t‖ ^ (4 : ℕ) := by
      simp [H₂, Function.resToImagAxis, ResToImagAxis, ht0, norm_pow]
    rw [hH2norm, ← pow_four_two_mul_exp t]
    exact pow_le_pow_left₀ (by positivity) hTheta2_ge 4
  have hpow : (16 * Real.exp (-Real.pi * t)) ^ (2 : ℕ) ≤ ‖H₂.resToImagAxis t‖ ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hx_ge 2
  have hleft :
      (16 * Real.exp (-Real.pi * t)) ^ (2 : ℕ) = (256 : ℝ) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
    rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  linarith [hpow, hleft]

lemma bound_w_inv_sub_one_sub (t u C0 : ℝ) (w : ℂ)
    (hw_norm_ge : (1 : ℝ) ≤ ‖w‖)
    (hw_inv : ‖w⁻¹‖ ≤ 1)
    (hw_tail :
      ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ ≤ C0 * Real.exp (-(4 : ℝ) * Real.pi * t))
    (hw_one :
      ‖w - (1 : ℂ)‖ ≤ (8 + C0) * Real.exp (-(2 : ℝ) * Real.pi * t)) :
    ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ ≤ ((8 + C0) ^ 2 + C0) * Real.exp (-(4 : ℝ) * Real.pi * t) := by
  have hw_ne : w ≠ 0 := (norm_pos_iff).1 (lt_of_lt_of_le zero_lt_one hw_norm_ge)
  have hid : w⁻¹ - (2 - w) = (w - 1) ^ (2 : ℕ) * w⁻¹ := by
    have hmul : (w⁻¹ - (2 - w)) * w = (w - 1) ^ (2 : ℕ) := by
      calc
        (w⁻¹ - (2 - w)) * w = (w⁻¹ * w) - (2 - w) * w := by ring
        _ = (1 : ℂ) - (2 - w) * w := by simp [hw_ne]
        _ = (w - 1) ^ (2 : ℕ) := by
              simp [pow_two]
              ring
    simpa [mul_assoc, hw_ne, mul_inv_cancel, sub_eq_add_neg, pow_two] using
      congrArg (fun z : ℂ => z * w⁻¹) hmul
  have htri :
      ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ ≤ ‖w⁻¹ - (2 - w)‖ + ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ := by
    have hnorm :
        ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ =
          ‖(w⁻¹ - (2 - w)) - (w - (1 : ℂ) - ((8 * u : ℝ) : ℂ))‖ := by
      simpa using congrArg norm (by
        ring : w⁻¹ - (1 - ((8 * u : ℝ) : ℂ)) =
          (w⁻¹ - (2 - w)) - (w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)))
    rw [hnorm]
    exact norm_sub_le (w⁻¹ - (2 - w)) (w - (1 : ℂ) - ((8 * u : ℝ) : ℂ))
  have hquad :
      ‖w⁻¹ - (2 - w)‖ ≤ (8 + C0) ^ 2 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
    calc
      ‖w⁻¹ - (2 - w)‖ = ‖(w - 1) ^ (2 : ℕ) * w⁻¹‖ := by simp [hid]
      _ = ‖w - 1‖ ^ (2 : ℕ) * ‖w⁻¹‖ := by simp [norm_pow]
      _ ≤ ‖w - 1‖ ^ (2 : ℕ) := by
            simpa [mul_one] using
              (mul_le_mul_of_nonneg_left hw_inv (by positivity : 0 ≤ ‖w - 1‖ ^ (2 : ℕ)))
      _ ≤ ((8 + C0) * Real.exp (-(2 : ℝ) * Real.pi * t)) ^ (2 : ℕ) := by
            exact pow_le_pow_left₀ (by positivity : 0 ≤ ‖w - 1‖) hw_one 2
      _ = (8 + C0) ^ 2 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
            have hexp :
                (Real.exp (-(2 : ℝ) * Real.pi * t)) ^ (2 : ℕ) =
                  Real.exp (-(4 : ℝ) * Real.pi * t) := by
              calc
                (Real.exp (-(2 : ℝ) * Real.pi * t)) ^ (2 : ℕ) =
                    Real.exp ((2 : ℝ) * (-(2 : ℝ) * Real.pi * t)) := by
                      simpa using (Real.exp_nat_mul (-(2 : ℝ) * Real.pi * t) 2).symm
                _ = Real.exp (-(4 : ℝ) * Real.pi * t) := by
                      congr 1
                      ring_nf
            calc
              ((8 + C0) * Real.exp (-(2 : ℝ) * Real.pi * t)) ^ (2 : ℕ)
                  = (8 + C0) ^ (2 : ℕ) * (Real.exp (-(2 : ℝ) * Real.pi * t)) ^ (2 : ℕ) := by
                      simp [mul_pow]
              _ = (8 + C0) ^ 2 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
                    rw [hexp]
  nlinarith [htri, hquad, hw_tail]

lemma hw_tail_bound (t : ℝ) (ht : 1 ≤ t) (CH2 : ℝ)
    (hx_err :
      ‖H₂.resToImagAxis t - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) - (64 : ℂ) *
          (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) :
    ‖(((Real.exp (2 * Real.pi * t) / 256 : ℝ) : ℂ) * (H₂.resToImagAxis t) ^ (2 : ℕ))
          - (1 : ℂ) - ((8 * Real.exp (-(2 : ℝ) * Real.pi * t) : ℝ) : ℂ)‖
        ≤ (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256) * Real.exp (-(4 : ℝ) * Real.pi * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set e : ℝ := Real.exp (2 * Real.pi * t)
  set u : ℝ := Real.exp (-(2 : ℝ) * Real.pi * t)
  set A : ℂ := ((e / 256 : ℝ) : ℂ)
  set x : ℂ := H₂.resToImagAxis t
  set w : ℂ := A * (x ^ (2 : ℕ))
  have heu : e * u = 1 := by
    calc
      e * u = Real.exp (2 * Real.pi * t) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
              simp [e, u]
        _ = Real.exp ((2 * Real.pi * t) + (-(2 : ℝ) * Real.pi * t)) := by
                simpa using
                  (Real.exp_add (2 * Real.pi * t) (-(2 : ℝ) * Real.pi * t)).symm
        _ = Real.exp 0 := by
                simp
        _ = 1 := by simp
  set C0 : ℝ := 16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256
  have hw_tail :
      ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ ≤ C0 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
    -- This lemma is proved here for self-containment.
    -- The main lemma becomes much lighter when this is isolated.
    set main : ℂ :=
      (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) + (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)
    set r : ℂ := x - main
    have hr : ‖r‖ ≤ CH2 * Real.exp (-(5 : ℝ) * Real.pi * t) := by
      have : r = x - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) - (64 : ℂ) *
          (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) := by
        simp [r, main, sub_eq_add_neg, add_assoc, add_comm]
      simpa [x, this] using hx_err
    have hmain_norm :
        ‖main‖ ≤ 80 * Real.exp (-Real.pi * t) := by
        have hq3_le : Real.exp (-(3 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) := by
          apply Real.exp_le_exp.mpr
          nlinarith [Real.pi_pos, ht]
        have h1 : ‖(16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖ = 16 * Real.exp (-Real.pi * t) := by
          simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
        have h2 : ‖(64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖ =
            64 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
          simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
        have htri : ‖main‖ ≤ ‖(16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖ +
            ‖(64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖ := by
          simpa [main] using
            (norm_add_le ((16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ))
              ((64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)))
        nlinarith [htri, h1, h2, hq3_le]
    have hmain_sq :
        ‖main ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)‖ ≤
          (4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t) := by
        have hq1_sq : (Real.exp (-Real.pi * t)) ^ (2 : ℕ) = u := by
          simpa [u, mul_assoc] using (Real.exp_nat_mul (-(Real.pi * t)) 2).symm
        have hu_sq : (u ^ (2 : ℕ) : ℝ) = Real.exp (-(4 : ℝ) * Real.pi * t) := by
          have h : (2 : ℝ) * ((2 : ℝ) * (Real.pi * t)) = (4 : ℝ) * (Real.pi * t) := by ring
          simpa [u, mul_assoc, h] using (Real.exp_nat_mul (-(2 : ℝ) * (Real.pi * t)) 2).symm
        have hq1q3 :
            Real.exp (-Real.pi * t) * Real.exp (-(3 : ℝ) * Real.pi * t) = (u ^ (2 : ℕ) : ℝ) := by
          have :
              Real.exp (-(Real.pi * t)) * Real.exp (-(3 : ℝ) * (Real.pi * t)) =
                Real.exp (-(4 : ℝ) * (Real.pi * t)) := by
            have hx :
                (-(Real.pi * t)) + (-(3 * (Real.pi * t))) = (-(4 * (Real.pi * t))) := by
              ring
            simpa [hx] using
              (Real.exp_add (-(Real.pi * t)) ((-3 : ℝ) * (Real.pi * t))).symm
          simpa [mul_assoc, hu_sq] using this
        have hq3_sq :
            (Real.exp (-(3 : ℝ) * Real.pi * t)) ^ (2 : ℕ) = Real.exp (-(6 : ℝ) * Real.pi * t) := by
          have h : (2 : ℝ) * ((3 : ℝ) * (Real.pi * t)) = (6 : ℝ) * (Real.pi * t) := by ring
          simpa [mul_assoc, h] using (Real.exp_nat_mul (-(3 : ℝ) * (Real.pi * t)) 2).symm
        have hq1_sq_c : (Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ) = (u : ℂ) := by
          simpa using congrArg (fun r : ℝ => (r : ℂ)) hq1_sq
        have hq1q3_c :
            (Real.exp (-Real.pi * t) : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) =
              ((u ^ (2 : ℕ) : ℝ) : ℂ) := by
          simpa [Complex.ofReal_mul, mul_assoc, mul_left_comm, mul_comm, -Complex.ofReal_exp] using
            congrArg (fun r : ℝ => (r : ℂ)) hq1q3
        have hq3_sq_c :
            (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) ^ (2 : ℕ) =
              (Real.exp (-(6 : ℝ) * Real.pi * t) : ℂ) := by
          simpa using congrArg (fun r : ℝ => (r : ℂ)) hq3_sq
        have hEq :
            main ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ) =
              (4096 : ℂ) * (Real.exp (-(6 : ℝ) * Real.pi * t) : ℂ) := by
          grind only
        have hnorm :
            ‖(4096 : ℂ) * (Real.exp (-(6 : ℝ) * Real.pi * t) : ℂ)‖ =
              (4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t) := by
          simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
        have hfinal :
            ‖main ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)‖ =
              (4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t) := by
          calc
            ‖main ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)‖
                = ‖(4096 : ℂ) * (Real.exp (-(6 : ℝ) * Real.pi * t) : ℂ)‖ := by
                    simpa using congrArg norm hEq
            _ = (4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t) := hnorm
        exact le_of_eq hfinal
    have hsq :
        ‖x ^ (2 : ℕ) - main ^ (2 : ℕ)‖ ≤
          (160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) +
            (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2 := by
      have hfac : x ^ (2 : ℕ) - main ^ (2 : ℕ) = (x - main) * (x + main) := by ring
      have hx_le : ‖x‖ ≤ ‖main‖ + ‖r‖ := norm_le_norm_add_norm_sub' x main
      have hxplus :
          ‖x + main‖ ≤ (160 * Real.exp (-Real.pi * t)) + ‖r‖ := by
        have : ‖x + main‖ ≤ ‖x‖ + ‖main‖ := norm_add_le _ _
        nlinarith [this, hx_le, hmain_norm]
      calc
        ‖x ^ (2 : ℕ) - main ^ (2 : ℕ)‖ = ‖(x - main) * (x + main)‖ := by simp [hfac]
        _ = ‖r‖ * ‖x + main‖ := by simp [r]
        _ ≤ ‖r‖ * ((160 * Real.exp (-Real.pi * t)) + ‖r‖) := by gcongr
        _ = (160 * Real.exp (-Real.pi * t)) * ‖r‖ + ‖r‖ ^ 2 := by ring
        _ ≤ (160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) +
              (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2 := by
                gcongr
    have hA_norm : ‖A‖ = e / 256 := by
      have he0 : 0 ≤ e := by positivity [e]
      have he256 : 0 ≤ e / 256 := div_nonneg he0 (by norm_num)
      simpa [A, abs_of_nonneg he256] using (RCLike.norm_ofReal (K := ℂ) (e / 256))
    have hA256u : A * ((256 * u : ℝ) : ℂ) = (1 : ℂ) := by
      have heu' : (e : ℂ) * (u : ℂ) = (1 : ℂ) := by
        simpa using congrArg (fun r : ℝ => (r : ℂ)) heu
      calc
        A * ((256 * u : ℝ) : ℂ)
            = ((e / 256 : ℝ) : ℂ) * ((256 * u : ℝ) : ℂ) := by rfl
          _ = (((e / 256) * (256 * u) : ℝ) : ℂ) := by simp [Complex.ofReal_mul]
          _ = ((e * u : ℝ) : ℂ) := by ring_nf
          _ = (1 : ℂ) := by simp [heu]
    have hA2048u2 :
      A * ((2048 * (u ^ (2 : ℕ) : ℝ) : ℝ) : ℂ) = ((8 * u : ℝ) : ℂ) := by
      have heuu : e * (u ^ (2 : ℕ) : ℝ) = u := by
        calc
          e * (u ^ (2 : ℕ) : ℝ) = e * (u * u) := by simp [pow_two]
          _ = (e * u) * u := by ring
          _ = (1 : ℝ) * u := by simp [heu]
          _ = u := by ring
      calc
        A * ((2048 * (u ^ (2 : ℕ) : ℝ) : ℝ) : ℂ)
            = ((e / 256 : ℝ) : ℂ) * ((2048 * (u ^ (2 : ℕ) : ℝ) : ℝ) : ℂ) := by rfl
        _ = (((e / 256) * (2048 * (u ^ (2 : ℕ) : ℝ)) : ℝ) : ℂ) := by simp [Complex.ofReal_mul]
        _ = (((8 * (e * (u ^ (2 : ℕ) : ℝ))) : ℝ) : ℂ) := by ring_nf
        _ = ((8 * u : ℝ) : ℂ) := by simp [heuu]
    have hw_rewrite :
      w - (1 : ℂ) - ((8 * u : ℝ) : ℂ) =
        A * (x ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)) := by
      have h :
            A * (x ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)) =
              w - (1 : ℂ) - ((8 * u : ℝ) : ℂ) := by
        calc
          A * (x ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ))
                = A * (x ^ (2 : ℕ)) - A * ((256 * u : ℝ) : ℂ) -
                    A * ((2048 * (u ^ (2 : ℕ) : ℝ) : ℝ) : ℂ) := by
                    ring_nf
                    simp [Complex.ofReal_mul, mul_left_comm, mul_comm]
          _ = w - (1 : ℂ) - ((8 * u : ℝ) : ℂ) := by
                grind only
      simpa using h.symm
    have hbr :
      ‖x ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)‖
        ≤ (4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t) +
            (160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) +
            (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2 := by
      have hsplit :
          x ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ) =
            (x ^ (2 : ℕ) - main ^ (2 : ℕ)) +
              (main ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)) := by
        ring
      have htri :=
        norm_add_le (x ^ (2 : ℕ) - main ^ (2 : ℕ))
          (main ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ))
      grind only
    have h1 :
      (e / 256) * ((4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t)) =
        16 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
      have he6 : e * Real.exp (-(6 : ℝ) * Real.pi * t) = Real.exp (-(4 : ℝ) * Real.pi * t) := by
        have h := (Real.exp_add (2 * Real.pi * t) (-(6 : ℝ) * Real.pi * t)).symm
        have hsum :
            (2 * Real.pi * t) + (-(6 : ℝ) * Real.pi * t) = (-(4 : ℝ) * Real.pi * t) := by ring
        calc
          e * Real.exp (-(6 : ℝ) * Real.pi * t)
              = Real.exp (2 * Real.pi * t) * Real.exp (-(6 : ℝ) * Real.pi * t) := by simp [e]
          _ = Real.exp ((2 * Real.pi * t) + (-(6 : ℝ) * Real.pi * t)) := by
                simpa using h
          _ = Real.exp (-(4 : ℝ) * Real.pi * t) := by
                simpa using congrArg Real.exp hsum
      calc
        (e / 256) * ((4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t))
            = 16 * (e * Real.exp (-(6 : ℝ) * Real.pi * t)) := by ring
        _ = 16 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
              simpa using congrArg (fun z : ℝ => 16 * z) he6
    have h2 :
      (e / 256) * ((160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t))) =
        (160 / 256) * CH2 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
      have he4 :
          e * (Real.exp (-Real.pi * t) * Real.exp (-(5 : ℝ) * Real.pi * t)) =
            Real.exp (-(4 : ℝ) * Real.pi * t) := by
        have hbc :
            Real.exp (-Real.pi * t) * Real.exp (-(5 : ℝ) * Real.pi * t) =
              Real.exp (-(6 : ℝ) * Real.pi * t) := by
          have h := (Real.exp_add (-Real.pi * t) (-(5 : ℝ) * Real.pi * t)).symm
          have hsum :
              (-Real.pi * t) + (-(5 : ℝ) * Real.pi * t) = (-(6 : ℝ) * Real.pi * t) := by ring
          calc
            Real.exp (-Real.pi * t) * Real.exp (-(5 : ℝ) * Real.pi * t)
                = Real.exp ((-Real.pi * t) + (-(5 : ℝ) * Real.pi * t)) := by
                    simpa using h
            _ = Real.exp (-(6 : ℝ) * Real.pi * t) := by
                  simpa using congrArg Real.exp hsum
        have hab :
            Real.exp (2 * Real.pi * t) * Real.exp (-(6 : ℝ) * Real.pi * t) =
              Real.exp (-(4 : ℝ) * Real.pi * t) := by
          have h := (Real.exp_add (2 * Real.pi * t) (-(6 : ℝ) * Real.pi * t)).symm
          have hsum :
              (2 * Real.pi * t) + (-(6 : ℝ) * Real.pi * t) = (-(4 : ℝ) * Real.pi * t) := by ring
          calc
            Real.exp (2 * Real.pi * t) * Real.exp (-(6 : ℝ) * Real.pi * t)
                = Real.exp ((2 * Real.pi * t) + (-(6 : ℝ) * Real.pi * t)) := by
                    simpa using h
            _ = Real.exp (-(4 : ℝ) * Real.pi * t) := by
                  simpa using congrArg Real.exp hsum
        exact CancelDenoms.derive_trans hbc hab
      calc
        (e / 256) * ((160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)))
              =
            (160 / 256) * CH2 *
              (e * (Real.exp (-Real.pi * t) * Real.exp (-(5 : ℝ) * Real.pi * t))) := by
              ring
        _ = (160 / 256) * CH2 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
              rw [he4]
    have h3 :
      (e / 256) * ((CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2) ≤
        (CH2 ^ 2) / 256 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
      have hexp :
          (Real.exp (-(5 : ℝ) * Real.pi * t)) ^ (2 : ℕ) =
            Real.exp (-(10 : ℝ) * Real.pi * t) := by
        set a : ℝ := (-(5 : ℝ) * Real.pi * t)
        have ha : a + a = -(10 * Real.pi * t) := by
          simp [a] ; ring
        have hmul : Real.exp a * Real.exp a = Real.exp (a + a) := by
          simpa using (Real.exp_add a a).symm
        calc
          (Real.exp (-(5 : ℝ) * Real.pi * t)) ^ (2 : ℕ)
              = Real.exp a * Real.exp a := by simp [a, pow_two]
          _ = Real.exp (a + a) := hmul
          _ = Real.exp (-(10 : ℝ) * Real.pi * t) := by simp [ha]
      have hsq' :
          (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2 =
            (CH2 ^ 2) * Real.exp (-(10 : ℝ) * Real.pi * t) := by
        calc
          (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2
              = (CH2 ^ 2) * (Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2 := by
                  simp [mul_pow]
          _ = (CH2 ^ 2) * Real.exp (-(10 : ℝ) * Real.pi * t) := by
                rw [hexp]
      have he8 : e * Real.exp (-(10 : ℝ) * Real.pi * t) = Real.exp (-(8 : ℝ) * Real.pi * t) := by
        set a : ℝ := 2 * Real.pi * t
        set b : ℝ := (-(10 : ℝ) * Real.pi * t)
        have h := (Real.exp_add a b).symm
        have hsum : a + b = (-(8 : ℝ) * Real.pi * t) := by
          simp [a, b] ; ring
        calc
          e * Real.exp (-(10 : ℝ) * Real.pi * t) = Real.exp a * Real.exp b := by simp [e, a, b]
          _ = Real.exp (a + b) := h
          _ = Real.exp (-(8 : ℝ) * Real.pi * t) := by simp [hsum]
      have h8 :
          Real.exp (-(8 : ℝ) * Real.pi * t) ≤ Real.exp (-(4 : ℝ) * Real.pi * t) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos, ht]
      calc
        (e / 256) * ((CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2)
            = (e / 256) * ((CH2 ^ 2) * Real.exp (-(10 : ℝ) * Real.pi * t)) := by
                rw [hsq']
        _ = (CH2 ^ 2) / 256 * (e * Real.exp (-(10 : ℝ) * Real.pi * t)) := by ring
        _ = (CH2 ^ 2) / 256 * Real.exp (-(8 : ℝ) * Real.pi * t) := by
              rw [he8]
        _ ≤ (CH2 ^ 2) / 256 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
              exact mul_le_mul_of_nonneg_left h8 (by positivity : 0 ≤ (CH2 ^ 2) / 256)
    calc
      ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖
          = ‖A‖ * ‖x ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)‖ := by
              rw [hw_rewrite]
              simp
    _ ≤ ‖A‖ *
          ( (4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t) +
            (160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) +
            (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2 ) := by
          exact mul_le_mul_of_nonneg_left hbr (norm_nonneg A)
    _ = (e / 256) *
          ( (4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t) +
            (160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) +
            (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2 ) := by
          simp [hA_norm]
    _ ≤ C0 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
          grind only
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
  have he0e : 0 ≤ e := by positivity [e]
  have he256 : 0 ≤ e / 256 := div_nonneg he0e (by norm_num : (0 : ℝ) ≤ (256 : ℝ))
  have hA_norm : ‖A‖ = e / 256 := by
    simpa [A, abs_of_nonneg he256] using (RCLike.norm_ofReal (K := ℂ) (e / 256))
  have hCH2 : 0 ≤ CH2 := by
    have h := hH2 1 (le_rfl : (1 : ℝ) ≤ 1)
    have h0 : 0 ≤ ‖H₂.resToImagAxis 1 - (16 : ℂ) * (Real.exp (-Real.pi * 1) : ℂ) -
          (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * 1) : ℂ)‖ := norm_nonneg _
    have hmul : 0 ≤ CH2 * Real.exp (-(5 : ℝ) * Real.pi * (1 : ℝ)) := h0.trans h
    exact nonneg_of_mul_nonneg_left hmul (Real.exp_pos _)
  set C0 : ℝ := 16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256
  have hC0 : 0 ≤ C0 := by positivity
  have heu : e * u = 1 := by
    calc
      e * u = Real.exp (2 * Real.pi * t) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
              simp [e, u]
        _ = Real.exp ((2 * Real.pi * t) + (-(2 : ℝ) * Real.pi * t)) := by
                simpa using
                  (Real.exp_add (2 * Real.pi * t) (-(2 : ℝ) * Real.pi * t)).symm
        _ = Real.exp 0 := by
                simp
        _ = 1 := by simp
  have hA8u : A * ((8 * u : ℝ) : ℂ) = ((1 / 32 : ℝ) : ℂ) := by
    have hfrac : (8 : ℝ) / 256 = (1 / 32 : ℝ) := by norm_num
    have h : (e / 256) * (8 * u) = (1 / 32 : ℝ) := by
      calc
        (e / 256) * (8 * u) = (e * u) * ((8 : ℝ) / 256) := by ring
        _ = (1 : ℝ) * (1 / 32 : ℝ) := by simp [heu, hfrac]
        _ = (1 / 32 : ℝ) := by ring
    simpa [A, Complex.ofReal_mul, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun r : ℝ => (r : ℂ)) h
  have hmain_id :
      ((x ^ (2 : ℕ))⁻¹ - A + ((1 / 32 : ℝ) : ℂ)) = A * (w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))) := by
    have hw : w = A * (x ^ (2 : ℕ)) := rfl
    calc
      (x ^ (2 : ℕ))⁻¹ - A + ((1 / 32 : ℝ) : ℂ)
          = (x ^ (2 : ℕ))⁻¹ - A + A * ((8 * u : ℝ) : ℂ) := by
              simpa using
                congrArg (fun z : ℂ => (x ^ (2 : ℕ))⁻¹ - A + z) hA8u.symm
      _ = A * w⁻¹ - A + A * ((8 * u : ℝ) : ℂ) := by
            have : A * w⁻¹ = (x ^ (2 : ℕ))⁻¹ := by
              have hA0 : A ≠ 0 := by
                have he0 : e ≠ 0 := by
                  have : 0 < e := by simp [e, Real.exp_pos]
                  exact ne_of_gt this
                have hR : (e / 256 : ℝ) ≠ 0 := by
                  exact div_ne_zero he0 (by norm_num)
                exact ofReal_ne_zero.mpr hR
              calc
                A * w⁻¹ = A * ((x ^ (2 : ℕ))⁻¹ * A⁻¹) := by
                  simp [w, mul_inv_rev]
                _ = (x ^ (2 : ℕ))⁻¹ * (A * A⁻¹) := by ac_rfl
                _ = (x ^ (2 : ℕ))⁻¹ := by simp [hA0]
            simp [this]
      _ = A * (w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))) := by ring
  have hx_err :
      ‖x - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) - (64 : ℂ) *
          (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ CH2 * Real.exp (-(5 : ℝ) * Real.pi * t) := hH2 t ht
  have hw_tail :
      ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ ≤
        C0 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
    simpa [w, A, x, e, u, C0] using
      (hw_tail_bound (t := t) (ht := ht) (CH2 := CH2) (by simpa [x] using hx_err))
  have hw_one :
      ‖w - (1 : ℂ)‖ ≤
        (8 + C0) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
    have hu0 : 0 ≤ u := (Real.exp_pos _).le
    have hu1 : u ≤ 1 := by
      have ht0' : 0 ≤ t := le_trans zero_le_one ht
      have hnonneg : 0 ≤ (2 : ℝ) * Real.pi * t := by
        have h2 : 0 ≤ (2 : ℝ) := by norm_num
        exact mul_nonneg (mul_nonneg h2 Real.pi_pos.le) ht0'
      have hneg : (-(2 : ℝ) * Real.pi * t) = -((2 : ℝ) * Real.pi * t) := by ring
      have hle' : -((2 : ℝ) * Real.pi * t) ≤ 0 := neg_nonpos.mpr hnonneg
      have hle : (-(2 : ℝ) * Real.pi * t) ≤ 0 := by simpa [hneg] using hle'
      have : Real.exp (-(2 : ℝ) * Real.pi * t) ≤ 1 := (Real.exp_le_one_iff).2 hle
      simpa [u] using this
    have hu_sq : u ^ (2 : ℕ) = Real.exp (-(4 : ℝ) * Real.pi * t) := by
      have :
          (-(2 : ℝ) * Real.pi * t) + (-(2 : ℝ) * Real.pi * t) = (-(4 : ℝ) * Real.pi * t) := by
        ring
      calc
        u ^ (2 : ℕ) = (Real.exp (-(2 : ℝ) * Real.pi * t)) ^ (2 : ℕ) := by simp [u]
        _ = Real.exp ((-(2 : ℝ) * Real.pi * t) + (-(2 : ℝ) * Real.pi * t)) := by
              simp [pow_two, Real.exp_add]
        _ = Real.exp (-(4 : ℝ) * Real.pi * t) := by
              simpa using congrArg Real.exp this
    have hw_tail' :
        ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ ≤
          C0 * (u ^ (2 : ℕ)) := by
      simpa [hu_sq] using hw_tail
    have h :=
      norm_sub_one_le_of_norm_sub_one_sub w u C0 hu0 hu1 hw_tail'
    simpa [u, abs_of_nonneg hC0] using h
  have hw_norm_ge : (1 : ℝ) ≤ ‖w‖ := by
    have hx2_ge : (256 : ℝ) * u ≤ ‖x‖ ^ (2 : ℕ) := by
      dsimp [x, u]
      simpa using (H2_norm_pow_two_ge (t := t) ht0)
    have hw_eq : ‖w‖ = (e / 256) * ‖x‖ ^ (2 : ℕ) := by
      simp [w, hA_norm, norm_pow]
    have hmono : (e / 256) * ((256 : ℝ) * u) ≤ (e / 256) * ‖x‖ ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hx2_ge he256
    have h1 : (e / 256) * ((256 : ℝ) * u) = 1 := by
      calc
        (e / 256) * ((256 : ℝ) * u) = e * u := by ring
        _ = 1 := heu
    have h : (1 : ℝ) ≤ (e / 256) * ‖x‖ ^ (2 : ℕ) := by
      simpa [h1] using hmono
    simpa [hw_eq] using h
  have hw_inv : ‖w⁻¹‖ ≤ 1 := by
    have hinv : (‖w‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hw_norm_ge
    calc
      ‖w⁻¹‖ = (‖w‖)⁻¹ := by simp [norm_inv]
      _ ≤ 1 := hinv
  have hdiff :
      ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ ≤
        ((8 + C0) ^ 2 + C0) * Real.exp (-(4 : ℝ) * Real.pi * t) :=
    bound_w_inv_sub_one_sub (t := t) (u := u) (C0 := C0) (w := w)
      hw_norm_ge hw_inv hw_tail hw_one
  have hexp :
      (e / 256) * Real.exp (-(4 : ℝ) * Real.pi * t) =
        (1 / 256 : ℝ) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
    have : e * Real.exp (-(4 : ℝ) * Real.pi * t) = Real.exp (-(2 : ℝ) * Real.pi * t) := by
      have hsum :
          (2 * Real.pi * t) + (-(4 * Real.pi * t)) = (-(2 * Real.pi * t)) := by
        ring
      simpa [e, hsum] using
        (Real.exp_add (2 * Real.pi * t) (-(4 * Real.pi * t))).symm
    nlinarith [this]
  calc
    ‖((H₂.resToImagAxis t) ^ (2 : ℕ))⁻¹
          - ((Real.exp (2 * Real.pi * t) / 256 : ℝ) : ℂ)
          + ((1 / 32 : ℝ) : ℂ)‖
        = ‖A * (w⁻¹ - (1 - ((8 * u : ℝ) : ℂ)))‖ := by
            simpa [x, A, w, e, u] using congrArg norm hmain_id
    _ = ‖A‖ * ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ := by simp
    _ ≤ (e / 256) *
          (((8 + (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256)) ^ 2 +
              (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256)) *
            Real.exp (-(4 : ℝ) * Real.pi * t)) := by
          have hA_le : ‖A‖ ≤ e / 256 := by simp [hA_norm]
          have hdiff' :
              ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ ≤
                ((8 + (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256)) ^ 2 +
                    (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256)) *
                  Real.exp (-(4 : ℝ) * Real.pi * t) := by
            simpa [C0] using hdiff
          have hmulA :
              ‖A‖ * ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ ≤
                (e / 256) * ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ :=
            mul_le_mul_of_nonneg_right hA_le (norm_nonneg _)
          exact le_mul_of_le_mul_of_nonneg_left hmulA hdiff he256
    _ ≤ (256 * ((8 + (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256)) ^ 2 +
          (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256))) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
          set K : ℝ := (8 + C0) ^ 2 + C0
          have hK : 0 ≤ K := by
            have hsq : 0 ≤ (8 + C0) ^ 2 := by positivity
            have : 0 ≤ (8 + C0) ^ 2 + C0 := by positivity
            simpa [K] using this
          have hcoeff : (1 / 256 : ℝ) * K ≤ 256 * K := by
            have h : (1 / 256 : ℝ) ≤ 256 := by norm_num
            exact mul_le_mul_of_nonneg_right h hK
          have hmul :
              ((1 / 256 : ℝ) * K) * Real.exp (-(2 : ℝ) * Real.pi * t) ≤
                (256 * K) * Real.exp (-(2 : ℝ) * Real.pi * t) :=
            mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le
          have hrewrite :
              (e / 256) *
                  (((8 + (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256)) ^ 2 +
                      (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256)) *
                    Real.exp (-(4 : ℝ) * Real.pi * t)) =
                ((1 / 256 : ℝ) * K) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
            have hK' :
                (8 + (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256)) ^ 2 +
                    (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256) =
                  K := by
              simp [K, C0]
            have hE :
                (e / 256) * Real.exp (-(4 : ℝ) * Real.pi * t) =
                  (1 / 256 : ℝ) * Real.exp (-(2 : ℝ) * Real.pi * t) := hexp
            calc
              (e / 256) *
                  (((8 + (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256)) ^ 2 +
                      (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256)) *
                    Real.exp (-(4 : ℝ) * Real.pi * t))
                  = (e / 256) * (K * Real.exp (-(4 : ℝ) * Real.pi * t)) := by
                      simp [hK', mul_assoc]
              _ = K * ((e / 256) * Real.exp (-(4 : ℝ) * Real.pi * t)) := by
                    ac_rfl
              _ = K * ((1 / 256 : ℝ) * Real.exp (-(2 : ℝ) * Real.pi * t)) := by
                    simpa using congrArg (fun z : ℝ => K * z) hE
              _ = ((1 / 256 : ℝ) * K) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
                    ac_rfl
          exact le_of_eq_of_le hrewrite hmul

end

end MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis
