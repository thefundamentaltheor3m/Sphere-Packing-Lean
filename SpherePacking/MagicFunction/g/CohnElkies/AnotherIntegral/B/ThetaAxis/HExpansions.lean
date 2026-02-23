module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis.QExpansion

/-!
# Expansions for `H₂`, `H₃`, and `H₄` on the imaginary axis

This file proves `q`-expansion style bounds for the modular functions `H₂`, `H₃`, and `H₄` on the
positive imaginary axis. These estimates are used to control `ψI' (it)` in the cancellation
argument for `AnotherIntegral.B`.

## Main statements
* `exists_bound_norm_H2_resToImagAxis_sub_two_terms_Ici_one`
* `exists_bound_norm_H4_resToImagAxis_sub_two_terms_Ici_one`
* `exists_bound_norm_H3_add_H4_resToImagAxis_sub_two_sub_main_Ici_one`
* `exists_bound_norm_inv_H3_sq_sub_one_Ici_one`
-/

namespace MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis

open scoped BigOperators UpperHalfPlane

open Real Complex Filter Topology
open Set

noncomputable section

/-! Helper inequalities for `Θⱼ` and `Hⱼ` norms. -/

lemma norm_add_add_add_le (a b c d : ℂ) :
    ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  nlinarith [norm_add_le (a + b + c) d, norm_add_le (a + b) c, norm_add_le a b]

lemma norm_pow4_sub_le (x y : ℂ) :
    ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤ 4 * ‖x - y‖ * (‖x‖ + ‖y‖) ^ 3 := by
  have hfac :
      x ^ (4 : ℕ) - y ^ (4 : ℕ) =
        (x - y) * (x ^ (3 : ℕ) + x ^ (2 : ℕ) * y + x * y ^ (2 : ℕ) + y ^ (3 : ℕ)) := by
    ring
  have hx : ‖x‖ ≤ ‖x‖ + ‖y‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hy : ‖y‖ ≤ ‖x‖ + ‖y‖ := le_add_of_nonneg_left (norm_nonneg _)
  have hx3 : ‖x ^ (3 : ℕ)‖ ≤ (‖x‖ + ‖y‖) ^ 3 := by
    simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hx 3
  have hy3 : ‖y ^ (3 : ℕ)‖ ≤ (‖x‖ + ‖y‖) ^ 3 := by
    simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hy 3
  have hx2y : ‖x ^ (2 : ℕ) * y‖ ≤ (‖x‖ + ‖y‖) ^ 3 := by
    calc
      ‖x ^ (2 : ℕ) * y‖ = ‖x‖ ^ 2 * ‖y‖ := by simp [norm_pow]
      _ ≤ (‖x‖ + ‖y‖) ^ 2 * (‖x‖ + ‖y‖) := by
            refine mul_le_mul ?_ hy (by positivity) (by positivity)
            simpa using pow_le_pow_left₀ (norm_nonneg _) hx 2
      _ = (‖x‖ + ‖y‖) ^ 3 := by ring
  have hxy2 : ‖x * y ^ (2 : ℕ)‖ ≤ (‖x‖ + ‖y‖) ^ 3 := by
    calc
      ‖x * y ^ (2 : ℕ)‖ = ‖x‖ * (‖y‖ ^ 2) := by simp [norm_pow]
      _ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) ^ 2 := by
            refine mul_le_mul hx ?_ (by positivity) (by positivity)
            simpa using pow_le_pow_left₀ (norm_nonneg _) hy 2
      _ = (‖x‖ + ‖y‖) ^ 3 := by ring
  have hsum :
      ‖x ^ (3 : ℕ) + x ^ (2 : ℕ) * y + x * y ^ (2 : ℕ) + y ^ (3 : ℕ)‖
        ≤ 4 * (‖x‖ + ‖y‖) ^ 3 := by
    have h0 :=
      norm_add_add_add_le (x ^ (3 : ℕ)) (x ^ (2 : ℕ) * y) (x * y ^ (2 : ℕ)) (y ^ (3 : ℕ))
    nlinarith [h0, hx3, hx2y, hxy2, hy3]
  calc
    ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖
        = ‖(x - y) * (x ^ (3 : ℕ) + x ^ (2 : ℕ) * y + x * y ^ (2 : ℕ) + y ^ (3 : ℕ))‖ := by
          simp [hfac]
    _ = ‖x - y‖ *
          ‖x ^ (3 : ℕ) + x ^ (2 : ℕ) * y + x * y ^ (2 : ℕ) + y ^ (3 : ℕ)‖ := by
          simp
    _ ≤ ‖x - y‖ * (4 * (‖x‖ + ‖y‖) ^ 3) := by
          exact mul_le_mul_of_nonneg_left hsum (norm_nonneg (x - y))
    _ = 4 * ‖x - y‖ * (‖x‖ + ‖y‖) ^ 3 := by ring

/-- `H₂(it)` expansion up to the `exp(-3π t)` term on `t ≥ 1`. -/
public lemma exists_bound_norm_H2_resToImagAxis_sub_two_terms_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖H₂.resToImagAxis t
          - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
          - (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(5 : ℝ) * Real.pi * t) := by
  rcases exists_bound_norm_Theta2_resToImagAxis_Ici_one with ⟨M, hM⟩
  rcases exists_bound_norm_Theta2_resToImagAxis_sub_two_terms_Ici_one with ⟨Cθ, hCθ⟩
  have hCθ0 : 0 ≤ Cθ := by
    have h := hCθ 1 (le_rfl : (1 : ℝ) ≤ 1)
    have : 0 ≤ Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * (1 : ℝ)) :=
      (norm_nonneg _).trans h
    have he : 0 < Real.exp (-(25 / 4 : ℝ) * Real.pi * (1 : ℝ)) := Real.exp_pos _
    nlinarith
  have hM0 : 0 ≤ M := by
    exact (norm_nonneg _).trans (hM 1 (le_rfl : (1 : ℝ) ≤ 1))
  refine ⟨(4 * (M + 4) ^ 3) * Cθ + 176, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set a : ℂ := (Real.exp (-Real.pi * t / 4) : ℂ)
  set b : ℂ := (Real.exp (-(9 / 4 : ℝ) * Real.pi * t) : ℂ)
  set x : ℂ := Θ₂.resToImagAxis t
  set y : ℂ := (2 : ℂ) * a + (2 : ℂ) * b
  have hx : ‖x‖ ≤ M := hM t ht
  have hy : ‖y‖ ≤ 4 := by
    have ha : ‖a‖ = Real.exp (-Real.pi * t / 4) := by
      simp [-Complex.ofReal_exp, a, abs_of_nonneg (Real.exp_pos _).le]
    have hb : ‖b‖ = Real.exp (-(9 / 4 : ℝ) * Real.pi * t) := by
      simp [-Complex.ofReal_exp, b, abs_of_nonneg (Real.exp_pos _).le]
    have hya : ‖(2 : ℂ) * a‖ = 2 * Real.exp (-Real.pi * t / 4) := by
      simp [ha]
    have hyb : ‖(2 : ℂ) * b‖ = 2 * Real.exp (-(9 / 4 : ℝ) * Real.pi * t) := by
      simp [hb]
    have hle1 : Real.exp (-Real.pi * t / 4) ≤ 1 := by
      have : (-Real.pi * t / 4 : ℝ) ≤ 0 := by
        nlinarith [Real.pi_pos, (le_trans zero_le_one ht)]
      simpa [Real.exp_le_one_iff] using this
    have hle2 : Real.exp (-(9 / 4 : ℝ) * Real.pi * t) ≤ 1 := by
      have : (-(9 / 4 : ℝ) * Real.pi * t) ≤ 0 := by
        nlinarith [Real.pi_pos, ht]
      simpa [Real.exp_le_one_iff] using this
    have htri : ‖y‖ ≤ ‖(2 : ℂ) * a‖ + ‖(2 : ℂ) * b‖ := by
      simpa [y] using (norm_add_le ((2 : ℂ) * a) ((2 : ℂ) * b))
    linarith [htri, hya, hyb, hle1, hle2]
  have hxy : ‖x - y‖ ≤ Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t) := by
    simpa
      [-Complex.ofReal_exp, x, y, a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hCθ t ht
  have hpow :
      ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤
        (4 * (M + 4) ^ 3) * (Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t)) := by
    have h := norm_pow4_sub_le x y
    have hsum : (‖x‖ + ‖y‖) ^ 3 ≤ (M + 4) ^ 3 := by
      have hx' : ‖x‖ + ‖y‖ ≤ M + 4 := by linarith
      exact pow_le_pow_left₀ (by positivity : 0 ≤ ‖x‖ + ‖y‖) hx' 3
    have hA : 0 ≤ Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t) :=
      mul_nonneg hCθ0 (Real.exp_pos _).le
    have h1 : 4 * ‖x - y‖ ≤ 4 * (Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t)) := by
      exact mul_le_mul_of_nonneg_left hxy (by positivity : (0 : ℝ) ≤ 4)
    have h2 :
        (4 * ‖x - y‖) * (‖x‖ + ‖y‖) ^ 3 ≤
          (4 * (Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t))) * (‖x‖ + ‖y‖) ^ 3 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 :
        (4 * (Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t))) * (‖x‖ + ‖y‖) ^ 3 ≤
          (4 * (Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t))) * (M + 4) ^ 3 :=
      have hnonneg : (0 : ℝ) ≤ 4 * (Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t)) := by
        nlinarith [hA]
      mul_le_mul_of_nonneg_left hsum hnonneg
    have h' :
        4 * ‖x - y‖ * (‖x‖ + ‖y‖) ^ 3 ≤
          4 * (Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t)) * (M + 4) ^ 3 := by
      -- reassociate and combine the two multiplications
      have := le_trans (by simpa [mul_assoc] using h2) (by simpa [mul_assoc] using h3)
      simpa [mul_assoc] using this
    -- Rearrange to the chosen coefficient.
    have h'' :
        4 * (Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t)) * (M + 4) ^ 3
          = (4 * (M + 4) ^ 3) * (Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t)) := by
      ring
    exact (h.trans h').trans_eq h''
  have hpow' :
      ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤
        (4 * (M + 4) ^ 3) * Cθ * Real.exp (-(5 : ℝ) * Real.pi * t) := by
    have hexp :
        Real.exp (-(25 / 4 : ℝ) * Real.pi * t) ≤ Real.exp (-(5 : ℝ) * Real.pi * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, ht]
    have hCθexp :
        Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t) ≤ Cθ * Real.exp (-(5 : ℝ) * Real.pi * t) :=
      mul_le_mul_of_nonneg_left hexp hCθ0
    have hpow0 := hpow
    have hstep :
        (4 * (M + 4) ^ 3) * (Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t)) ≤
          (4 * (M + 4) ^ 3) * (Cθ * Real.exp (-(5 : ℝ) * Real.pi * t)) :=
      mul_le_mul_of_nonneg_left hCθexp (by
        have hM4 : 0 ≤ M + 4 := by linarith
        exact mul_nonneg (by positivity : (0 : ℝ) ≤ 4) (pow_nonneg hM4 3))
    have := le_trans hpow0 hstep
    -- rearrange to match the stated RHS
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have ha4 : a ^ (4 : ℕ) = (Real.exp (-Real.pi * t) : ℂ) := by
    have hpow : (Real.exp (-Real.pi * t / 4)) ^ (4 : ℕ) = Real.exp (-Real.pi * t) := by
      calc
        (Real.exp (-Real.pi * t / 4)) ^ (4 : ℕ) = Real.exp ((4 : ℕ) * (-Real.pi * t / 4)) := by
          simpa using (Real.exp_nat_mul (-Real.pi * t / 4) 4).symm
        _ = Real.exp (-Real.pi * t) := by
          congr 1
          ring
    have hpowC :
        (Real.exp (-Real.pi * t / 4) : ℂ) ^ (4 : ℕ) = (Real.exp (-Real.pi * t) : ℂ) := by
      simpa [Complex.ofReal_pow] using congrArg (fun r : ℝ => (r : ℂ)) hpow
    simpa [-Complex.ofReal_exp, a] using hpowC
  have ha3b : a ^ (3 : ℕ) * b = (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) := by
    have ha3 : a ^ (3 : ℕ) = (Real.exp (-(3 / 4 : ℝ) * Real.pi * t) : ℂ) := by
      have hpow :
          (Real.exp (-Real.pi * t / 4)) ^ (3 : ℕ) = Real.exp ((3 : ℕ) * (-Real.pi * t / 4)) := by
        simpa using (Real.exp_nat_mul (-Real.pi * t / 4) 3).symm
      have : (Real.exp (-Real.pi * t / 4)) ^ (3 : ℕ) = Real.exp (-(3 / 4 : ℝ) * Real.pi * t) := by
        calc
          (Real.exp (-Real.pi * t / 4)) ^ (3 : ℕ) = Real.exp ((3 : ℕ) * (-Real.pi * t / 4)) := hpow
          _ = Real.exp (-(3 / 4 : ℝ) * Real.pi * t) := by
                congr 1
                ring
      have hpowC :
          (Real.exp (-Real.pi * t / 4) : ℂ) ^ (3 : ℕ) =
            (Real.exp (-(3 / 4 : ℝ) * Real.pi * t) : ℂ) := by
        simpa [Complex.ofReal_pow] using congrArg (fun r : ℝ => (r : ℂ)) this
      simpa [-Complex.ofReal_exp, a] using hpowC
    have hmulR :
        Real.exp (-(3 / 4 : ℝ) * Real.pi * t) * Real.exp (-(9 / 4 : ℝ) * Real.pi * t) =
          Real.exp (-(3 : ℝ) * Real.pi * t) := by
      calc
        Real.exp (-(3 / 4 : ℝ) * Real.pi * t) * Real.exp (-(9 / 4 : ℝ) * Real.pi * t) =
            Real.exp (-(3 / 4 : ℝ) * Real.pi * t + (-(9 / 4 : ℝ) * Real.pi * t)) := by
              exact
                (Real.exp_add (-(3 / 4 : ℝ) * Real.pi * t) (-(9 / 4 : ℝ) * Real.pi * t)).symm
        _ = Real.exp (-(3 : ℝ) * Real.pi * t) := by
              congr 1
              ring
    have hmulC :
        (Real.exp (-(3 / 4 : ℝ) * Real.pi * t) : ℂ) * (Real.exp (-(9 / 4 : ℝ) * Real.pi * t) : ℂ) =
          (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) := by
      simpa using congrArg (fun r : ℝ => (r : ℂ)) hmulR
    calc
      a ^ (3 : ℕ) * b
          = (Real.exp (-(3 / 4 : ℝ) * Real.pi * t) : ℂ) *
              (Real.exp (-(9 / 4 : ℝ) * Real.pi * t) : ℂ) := by
                simp [ha3, b]
      _ = (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) := hmulC
  have hy_main :
      y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) - (64 : ℂ) *
            (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)
        = (96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ)) + (64 : ℂ) * (a * b ^ (3 : ℕ)) +
            (16 : ℂ) * (b ^ (4 : ℕ)) := by
    -- (All algebraic, coefficients match the binomial expansion.)
    have : y ^ (4 : ℕ) =
        (16 : ℂ) * a ^ (4 : ℕ) + (64 : ℂ) * (a ^ (3 : ℕ) * b) +
          (96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ)) + (64 : ℂ) * (a * b ^ (3 : ℕ)) +
            (16 : ℂ) * b ^ (4 : ℕ) := by
      simp [y] ; ring
    -- Then rearrange.
    calc
      y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
            (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)
          = ((16 : ℂ) * a ^ (4 : ℕ) + (64 : ℂ) * (a ^ (3 : ℕ) * b) +
              (96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ)) + (64 : ℂ) * (a * b ^ (3 : ℕ)) +
                (16 : ℂ) * b ^ (4 : ℕ))
              - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) := by simp [this]
      _ = (96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ)) + (64 : ℂ) * (a * b ^ (3 : ℕ)) +
            (16 : ℂ) * (b ^ (4 : ℕ)) := by
          -- Pure algebra after rewriting the two main terms.
          rw [ha4, ha3b]
          ring
  have hy_tail :
      ‖y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
            (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ 176 * Real.exp (-(5 : ℝ) * Real.pi * t) := by
    have ha : ‖a‖ = Real.exp (-Real.pi * t / 4) := by
      simp [-Complex.ofReal_exp, a, abs_of_nonneg (Real.exp_pos _).le]
    have hb : ‖b‖ = Real.exp (-(9 / 4 : ℝ) * Real.pi * t) := by
      simp [-Complex.ofReal_exp, b, abs_of_nonneg (Real.exp_pos _).le]
    have hsquare (u : ℝ) : (Real.exp u) ^ (2 : ℕ) = Real.exp ((2 : ℕ) * u) := by
      simpa using (Real.exp_nat_mul u 2).symm
    have hcube (u : ℝ) : (Real.exp u) ^ (3 : ℕ) = Real.exp ((3 : ℕ) * u) := by
      simpa using (Real.exp_nat_mul u 3).symm
    have hquart (u : ℝ) : (Real.exp u) ^ (4 : ℕ) = Real.exp ((4 : ℕ) * u) := by
      simpa using (Real.exp_nat_mul u 4).symm
    have hab :
        ‖a ^ (2 : ℕ) * b ^ (2 : ℕ)‖ = Real.exp (-(5 : ℝ) * Real.pi * t) := by
      set u1 : ℝ := -Real.pi * t / 4
      set u2 : ℝ := (-(9 / 4 : ℝ) * Real.pi * t)
      calc
        ‖a ^ (2 : ℕ) * b ^ (2 : ℕ)‖ = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
          simp [norm_pow]
        _ = (Real.exp u1) ^ 2 * (Real.exp u2) ^ 2 := by simp [ha, hb, u1, u2]
        _ = Real.exp ((2 : ℕ) * u1) * Real.exp ((2 : ℕ) * u2) := by simp [hsquare]
        _ = Real.exp (((2 : ℕ) * u1) + ((2 : ℕ) * u2)) := by
            simpa using (Real.exp_add ((2 : ℕ) * u1) ((2 : ℕ) * u2)).symm
        _ = Real.exp (-(5 : ℝ) * Real.pi * t) := by
            congr 1
            simp [u1, u2]
            ring_nf
    have hab3 :
        ‖a * b ^ (3 : ℕ)‖ = Real.exp (-(7 : ℝ) * Real.pi * t) := by
      set u1 : ℝ := -Real.pi * t / 4
      set u2 : ℝ := (-(9 / 4 : ℝ) * Real.pi * t)
      calc
        ‖a * b ^ (3 : ℕ)‖ = ‖a‖ * ‖b ^ (3 : ℕ)‖ := by simp
        _ = ‖a‖ * (‖b‖ ^ 3) := by simp [norm_pow]
        _ = (Real.exp u1) * (Real.exp u2) ^ 3 := by simp [ha, hb, u1, u2]
        _ = Real.exp u1 * Real.exp ((3 : ℕ) * u2) := by simp [hcube]
        _ = Real.exp (u1 + ((3 : ℕ) * u2)) := by
            simpa using (Real.exp_add u1 ((3 : ℕ) * u2)).symm
        _ = Real.exp (-(7 : ℝ) * Real.pi * t) := by
            congr 1
            simp [u1, u2]
            ring_nf
    have hb4 : ‖b ^ (4 : ℕ)‖ = Real.exp (-(9 : ℝ) * Real.pi * t) := by
      set u2 : ℝ := (-(9 / 4 : ℝ) * Real.pi * t)
      calc
        ‖b ^ (4 : ℕ)‖ = ‖b‖ ^ 4 := by simp [norm_pow]
        _ = (Real.exp u2) ^ 4 := by simp [hb, u2]
        _ = Real.exp ((4 : ℕ) * u2) := by simp [hquart]
        _ = Real.exp (-(9 : ℝ) * Real.pi * t) := by
              congr 1
              simp [u2]
              ring_nf
    have hab3_le : ‖a * b ^ (3 : ℕ)‖ ≤ Real.exp (-(5 : ℝ) * Real.pi * t) := by
      calc
        ‖a * b ^ (3 : ℕ)‖ = Real.exp (-(7 : ℝ) * Real.pi * t) := hab3
        _ ≤ Real.exp (-(5 : ℝ) * Real.pi * t) := by
              refine Real.exp_monotone ?_
              nlinarith [Real.pi_pos, ht]
    have hb4_le : ‖b ^ (4 : ℕ)‖ ≤ Real.exp (-(5 : ℝ) * Real.pi * t) := by
      calc
        ‖b ^ (4 : ℕ)‖ = Real.exp (-(9 : ℝ) * Real.pi * t) := hb4
        _ ≤ Real.exp (-(5 : ℝ) * Real.pi * t) := by
              refine Real.exp_monotone ?_
              nlinarith [Real.pi_pos, ht]
    have h1 :
        ‖(96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ))‖ ≤ 96 * Real.exp (-(5 : ℝ) * Real.pi * t) := by
      calc
        ‖(96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ))‖ = 96 * ‖a ^ (2 : ℕ) * b ^ (2 : ℕ)‖ := by
          simp
        _ = 96 * Real.exp (-(5 : ℝ) * Real.pi * t) := by
          simpa using congrArg (fun r : ℝ => 96 * r) hab
        _ ≤ 96 * Real.exp (-(5 : ℝ) * Real.pi * t) := le_rfl
    have h2 :
        ‖(64 : ℂ) * (a * b ^ (3 : ℕ))‖ ≤ 64 * Real.exp (-(5 : ℝ) * Real.pi * t) := by
      calc
        ‖(64 : ℂ) * (a * b ^ (3 : ℕ))‖ = 64 * ‖a * b ^ (3 : ℕ)‖ := by
          simp
        _ ≤ 64 * Real.exp (-(5 : ℝ) * Real.pi * t) := by
          gcongr
    have h3 : ‖(16 : ℂ) * (b ^ (4 : ℕ))‖ ≤ 16 * Real.exp (-(5 : ℝ) * Real.pi * t) := by
      calc
        ‖(16 : ℂ) * (b ^ (4 : ℕ))‖ = 16 * ‖b ^ (4 : ℕ)‖ := by
          simp
        _ ≤ 16 * Real.exp (-(5 : ℝ) * Real.pi * t) := by
          gcongr
    have hsum :
        ‖(96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ)) + (64 : ℂ) * (a * b ^ (3 : ℕ)) +
            (16 : ℂ) * (b ^ (4 : ℕ))‖ ≤ 176 * Real.exp (-(5 : ℝ) * Real.pi * t) := by
      have htri1 :=
        norm_add_le
          ((96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ)) + (64 : ℂ) * (a * b ^ (3 : ℕ)))
          ((16 : ℂ) * (b ^ (4 : ℕ)))
      have htri2 :=
        norm_add_le
          ((96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ)))
          ((64 : ℂ) * (a * b ^ (3 : ℕ)))
      nlinarith [htri1, htri2, h1, h2, h3]
    rw [hy_main]
    exact hsum
  -- Put it together.
  have hH2_res : ResToImagAxis H₂ t = x ^ (4 : ℕ) := by
    simp [x, H₂, ResToImagAxis, ht0]
  have hH2 : H₂.resToImagAxis t = x ^ (4 : ℕ) := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0] using hH2_res
  calc
    ‖H₂.resToImagAxis t
          - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
          - (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
        = ‖x ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
              (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖ := by
          rw [hH2]
    _ ≤ ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ +
          ‖y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
              (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖ := by
          have hdecomp :
              (x ^ (4 : ℕ) - y ^ (4 : ℕ)) +
                  (y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                    (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ))
                =
                x ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                  (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) := by
            ring
          have htri' :=
            norm_add_le (x ^ (4 : ℕ) - y ^ (4 : ℕ))
              (y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ))
          rw [hdecomp] at htri'
          exact htri'
    _ ≤ ((4 * (M + 4) ^ 3) * Cθ) * Real.exp (-(5 : ℝ) * Real.pi * t) +
          176 * Real.exp (-(5 : ℝ) * Real.pi * t) := add_le_add hpow' hy_tail
    _ ≤ (((4 * (M + 4) ^ 3) * Cθ + 176) * Real.exp (-(5 : ℝ) * Real.pi * t)) := by
          ring_nf
          linarith
    _ = ((4 * (M + 4) ^ 3) * Cθ + 176) * Real.exp (-(5 : ℝ) * Real.pi * t) := rfl

/-- `H₃(it)` expansion up to the `exp(-2π t)` term on `t ≥ 1`. -/
lemma exists_bound_norm_H3_resToImagAxis_sub_two_terms_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖H₃.resToImagAxis t
          - (1 : ℂ)
          - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
          - (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(3 : ℝ) * Real.pi * t) := by
  rcases exists_bound_norm_Theta3_resToImagAxis_sub_one_Ici_one with ⟨C1, hC1⟩
  rcases exists_bound_norm_Theta3_resToImagAxis_sub_one_sub_two_exp_Ici_one with ⟨C2, hC2⟩
  have hC10 : 0 ≤ C1 := by
    have h := hC1 1 (le_rfl : (1 : ℝ) ≤ 1)
    have he : 0 < Real.exp (-Real.pi * (1 : ℝ)) := Real.exp_pos _
    have : 0 ≤ C1 * Real.exp (-Real.pi * (1 : ℝ)) := (norm_nonneg _).trans h
    nlinarith
  have hC20 : 0 ≤ C2 := by
    have h := hC2 1 (le_rfl : (1 : ℝ) ≤ 1)
    have he : 0 < Real.exp (-(4 : ℝ) * Real.pi * (1 : ℝ)) := Real.exp_pos _
    have : 0 ≤ C2 * Real.exp (-(4 : ℝ) * Real.pi * (1 : ℝ)) := (norm_nonneg _).trans h
    nlinarith
  refine ⟨(4 * (1 + C1 + 3) ^ 3) * C2 + 48, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set q' : ℂ := (Real.exp (-Real.pi * t) : ℂ)
  set x : ℂ := Θ₃.resToImagAxis t
  set y : ℂ := (1 : ℂ) + (2 : ℂ) * q'
  have hx : ‖x‖ ≤ 1 + C1 := by
    have hx1 : ‖x - 1‖ ≤ C1 := by
      have h := hC1 t ht
      have hexp : Real.exp (-Real.pi * t) ≤ 1 := by
        have : (-Real.pi * t) ≤ 0 := by nlinarith [Real.pi_pos, ht0.le]
        exact (Real.exp_le_one_iff).2 this
      have : C1 * Real.exp (-Real.pi * t) ≤ C1 := by
        simpa [mul_one] using (mul_le_mul_of_nonneg_left hexp hC10)
      exact h.trans this
    have htri : ‖x‖ ≤ ‖x - 1‖ + 1 := by
      simpa [sub_eq_add_neg, add_assoc] using (norm_add_le (x - 1) (1 : ℂ))
    calc
      ‖x‖ ≤ ‖x - 1‖ + 1 := htri
      _ ≤ C1 + 1 := by gcongr
      _ = 1 + C1 := by ring
  have hy : ‖y‖ ≤ 3 := by
    have hq : ‖q'‖ ≤ 1 := by
      simpa [q'] using (norm_exp_neg_pi_mul_le_one t ht0)
    have : ‖(1 : ℂ) + (2 : ℂ) * q'‖ ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) * q'‖ := norm_add_le _ _
    have : ‖y‖ ≤ 1 + 2 * ‖q'‖ := by
      simpa [y, norm_mul, Complex.norm_two] using this
    nlinarith [this, hq]
  have hxy : ‖x - y‖ ≤ C2 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
    simpa [x, y, q', sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using hC2 t ht
  have hpow :
      ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤
        (4 * (1 + C1 + 3) ^ 3) * (C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) := by
    have h := norm_pow4_sub_le x y
    have hsum : (‖x‖ + ‖y‖) ^ 3 ≤ (1 + C1 + 3) ^ 3 := by
      have : ‖x‖ + ‖y‖ ≤ (1 + C1) + 3 := by linarith [hx, hy]
      simpa [add_assoc] using pow_le_pow_left₀ (by positivity : 0 ≤ ‖x‖ + ‖y‖) this 3
    have h' :
        4 * ‖x - y‖ * (‖x‖ + ‖y‖) ^ 3 ≤
          4 * (C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) * (1 + C1 + 3) ^ 3 := by
      gcongr
    have :
        4 * (C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) * (1 + C1 + 3) ^ 3 =
          (4 * (1 + C1 + 3) ^ 3) * (C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) := by
      ring
    exact (h.trans h').trans_eq this
  have hpow' :
      ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤
        (4 * (1 + C1 + 3) ^ 3) * C2 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
    have hexp :
        Real.exp (-(4 : ℝ) * Real.pi * t) ≤ Real.exp (-(3 : ℝ) * Real.pi * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, ht]
    have hmul : C2 * Real.exp (-(4 : ℝ) * Real.pi * t) ≤ C2 * Real.exp (-(3 : ℝ) * Real.pi * t) :=
      mul_le_mul_of_nonneg_left hexp hC20
    have hscale :
        (4 * (1 + C1 + 3) ^ 3) * (C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) ≤
          (4 * (1 + C1 + 3) ^ 3) * (C2 * Real.exp (-(3 : ℝ) * Real.pi * t)) :=
      mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ (4 * (1 + C1 + 3) ^ 3))
    have := le_trans hpow hscale
    -- reassociate the scalar factors
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hy4 :
      ‖y ^ (4 : ℕ) - (1 : ℂ) - (8 : ℂ) * q' - (24 : ℂ) * (q' ^ (2 : ℕ))‖ ≤
        48 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
    have : y ^ (4 : ℕ) - (1 : ℂ) - (8 : ℂ) * q' - (24 : ℂ) * (q' ^ (2 : ℕ))
        = (32 : ℂ) * (q' ^ (3 : ℕ)) + (16 : ℂ) * (q' ^ (4 : ℕ)) := by
      simp [y] ; ring
    have hq : ‖q'‖ ≤ 1 := by
      simpa [q'] using (norm_exp_neg_pi_mul_le_one t ht0)
    have hq4_le : ‖q' ^ (4 : ℕ)‖ ≤ ‖q' ^ (3 : ℕ)‖ := by
      have ha0 : 0 ≤ ‖q'‖ := norm_nonneg _
      have ha3 : 0 ≤ ‖q'‖ ^ (3 : ℕ) := by positivity
      have hpow : ‖q'‖ ^ (4 : ℕ) ≤ ‖q'‖ ^ (3 : ℕ) := by
        calc
          ‖q'‖ ^ (4 : ℕ) = ‖q'‖ ^ (3 : ℕ) * ‖q'‖ := by
            simp [pow_succ, pow_zero, mul_assoc]
          _ ≤ ‖q'‖ ^ (3 : ℕ) * 1 := by
            exact mul_le_mul_of_nonneg_left hq ha3
          _ = ‖q'‖ ^ (3 : ℕ) := by ring
      simpa [norm_pow] using hpow
    have hq3' : ‖q' ^ (3 : ℕ)‖ = Real.exp (-(3 : ℝ) * Real.pi * t) := by
      have hx : (Real.exp (-Real.pi * t)) ^ (3 : ℕ) = Real.exp (-(3 : ℝ) * Real.pi * t) := by
        have harg : ((3 : ℕ) : ℝ) * (-Real.pi * t) = (-(3 : ℝ) * (Real.pi * t)) := by ring
        have hx' : (Real.exp (-Real.pi * t)) ^ (3 : ℕ) = Real.exp (-(3 : ℝ) * (Real.pi * t)) := by
          simpa [harg] using (Real.exp_nat_mul (-Real.pi * t) 3).symm
        simpa [mul_assoc] using hx'
      have hnormq : ‖q'‖ = Real.exp (-Real.pi * t) := by
        simp [q', abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
      calc
        ‖q' ^ (3 : ℕ)‖ = ‖q'‖ ^ (3 : ℕ) := by simp [norm_pow]
        _ = (Real.exp (-Real.pi * t)) ^ (3 : ℕ) := by simp [hnormq]
        _ = Real.exp (-(3 : ℝ) * Real.pi * t) := hx
    have hnorm :
        ‖(32 : ℂ) * (q' ^ (3 : ℕ)) + (16 : ℂ) * (q' ^ (4 : ℕ))‖
          ≤ 48 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
      have htri :=
        norm_add_le ((32 : ℂ) * (q' ^ (3 : ℕ))) ((16 : ℂ) * (q' ^ (4 : ℕ)))
      calc
        ‖(32 : ℂ) * (q' ^ (3 : ℕ)) + (16 : ℂ) * (q' ^ (4 : ℕ))‖
            ≤ ‖(32 : ℂ) * (q' ^ (3 : ℕ))‖ + ‖(16 : ℂ) * (q' ^ (4 : ℕ))‖ := htri
        _ = 32 * ‖q' ^ (3 : ℕ)‖ + 16 * ‖q' ^ (4 : ℕ)‖ := by simp
        _ ≤ 32 * ‖q' ^ (3 : ℕ)‖ + 16 * ‖q' ^ (3 : ℕ)‖ := by
              gcongr
        _ = 48 * ‖q' ^ (3 : ℕ)‖ := by ring
        _ = 48 * Real.exp (-(3 : ℝ) * Real.pi * t) := by simp [hq3']
    simpa [this] using hnorm
  have hH3_res : ResToImagAxis H₃ t = x ^ (4 : ℕ) := by
    simp [x, H₃, ResToImagAxis, ht0]
  have hH3 : H₃.resToImagAxis t = x ^ (4 : ℕ) := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0] using hH3_res
  calc
    ‖H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
        (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
        = ‖x ^ (4 : ℕ) - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
              (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ))‖ := by
          rw [hH3]
          have ha0 : Real.exp (-(2 : ℝ) * (Real.pi * t)) = (Real.exp (-Real.pi * t)) ^ (2 : ℕ) := by
            have harg : ((2 : ℕ) : ℝ) * (-Real.pi * t) = (-(2 : ℝ) * (Real.pi * t)) := by ring
            simpa [harg] using (Real.exp_nat_mul (-Real.pi * t) 2)
          have ha : Real.exp (-(2 : ℝ) * Real.pi * t) = (Real.exp (-Real.pi * t)) ^ (2 : ℕ) := by
            simpa [mul_assoc] using ha0
          have haC0 := congrArg (fun r : ℝ => (r : ℂ)) ha
          have haC :
              (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ) =
                (Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ) := by
            simpa using haC0
          rw [haC]
    _ ≤ ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ +
          ‖y ^ (4 : ℕ) - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ))‖ := by
          have hdecomp :
              (x ^ (4 : ℕ) - y ^ (4 : ℕ)) +
                  (y ^ (4 : ℕ) - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                    (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ)))
                =
                x ^ (4 : ℕ) - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                  (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ)) := by
            ring
          have htri' :=
            norm_add_le (x ^ (4 : ℕ) - y ^ (4 : ℕ))
              (y ^ (4 : ℕ) - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ)))
          rw [hdecomp] at htri'
          exact htri'
    _ ≤ ((4 * (1 + C1 + 3) ^ 3) * C2) * Real.exp (-(3 : ℝ) * Real.pi * t) +
          48 * Real.exp (-(3 : ℝ) * Real.pi * t) := add_le_add hpow' hy4
    _ ≤ (((4 * (1 + C1 + 3) ^ 3) * C2 + 48) * Real.exp (-(3 : ℝ) * Real.pi * t)) := by
          ring_nf
          linarith
    _ = ((4 * (1 + C1 + 3) ^ 3) * C2 + 48) * Real.exp (-(3 : ℝ) * Real.pi * t) := rfl

/-- `H₄(it)` expansion up to the `exp(-2π t)` term on `t ≥ 1`. -/
public lemma exists_bound_norm_H4_resToImagAxis_sub_two_terms_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖H₄.resToImagAxis t
          - (1 : ℂ)
          + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
          - (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(3 : ℝ) * Real.pi * t) := by
  rcases exists_bound_norm_Theta4_resToImagAxis_sub_one_Ici_one with ⟨C1, hC1⟩
  rcases exists_bound_norm_Theta4_resToImagAxis_sub_one_add_two_exp_Ici_one with ⟨C2, hC2⟩
  have hC10 : 0 ≤ C1 := by
    have h := hC1 1 (le_rfl : (1 : ℝ) ≤ 1)
    have he : 0 < Real.exp (-Real.pi * (1 : ℝ)) := Real.exp_pos _
    have : 0 ≤ C1 * Real.exp (-Real.pi * (1 : ℝ)) := (norm_nonneg _).trans h
    nlinarith
  have hC20 : 0 ≤ C2 := by
    have h := hC2 1 (le_rfl : (1 : ℝ) ≤ 1)
    have he : 0 < Real.exp (-(4 : ℝ) * Real.pi * (1 : ℝ)) := Real.exp_pos _
    have : 0 ≤ C2 * Real.exp (-(4 : ℝ) * Real.pi * (1 : ℝ)) := (norm_nonneg _).trans h
    nlinarith
  refine ⟨(4 * (1 + C1 + 3) ^ 3) * C2 + 48, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set q' : ℂ := (Real.exp (-Real.pi * t) : ℂ)
  set x : ℂ := Θ₄.resToImagAxis t
  set y : ℂ := (1 : ℂ) - (2 : ℂ) * q'
  have hx : ‖x‖ ≤ 1 + C1 := by
    have hx1 : ‖x - 1‖ ≤ C1 := by
      have h := hC1 t ht
      have hexp : Real.exp (-Real.pi * t) ≤ 1 := by
        have : (-Real.pi * t) ≤ 0 := by nlinarith [Real.pi_pos, ht0.le]
        exact (Real.exp_le_one_iff).2 this
      have : C1 * Real.exp (-Real.pi * t) ≤ C1 := by
        simpa [mul_one] using (mul_le_mul_of_nonneg_left hexp hC10)
      exact h.trans this
    have htri : ‖x‖ ≤ ‖x - 1‖ + 1 := by
      simpa [sub_eq_add_neg, add_assoc] using (norm_add_le (x - 1) (1 : ℂ))
    calc
      ‖x‖ ≤ ‖x - 1‖ + 1 := htri
      _ ≤ C1 + 1 := by gcongr
      _ = 1 + C1 := by ring
  have hy : ‖y‖ ≤ 3 := by
    have hq : ‖q'‖ ≤ 1 := by
      simpa [q'] using (norm_exp_neg_pi_mul_le_one t ht0)
    have hsum : ‖(1 : ℂ) - (2 : ℂ) * q'‖ ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) * q'‖ := by
      simpa [sub_eq_add_neg] using (norm_add_le (1 : ℂ) (-(2 : ℂ) * q'))
    have hbd : ‖y‖ ≤ 1 + 2 * ‖q'‖ := by
      simpa [y, norm_mul, Complex.norm_two] using hsum
    nlinarith [hbd, hq]
  have hxy : ‖x - y‖ ≤ C2 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
    simpa [x, y, q', sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using hC2 t ht
  have hpow :
      ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤
        (4 * (1 + C1 + 3) ^ 3) * (C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) := by
    have h := norm_pow4_sub_le x y
    have hsum : (‖x‖ + ‖y‖) ^ 3 ≤ (1 + C1 + 3) ^ 3 := by
      have : ‖x‖ + ‖y‖ ≤ (1 + C1) + 3 := by linarith [hx, hy]
      simpa [add_assoc] using pow_le_pow_left₀ (by positivity : 0 ≤ ‖x‖ + ‖y‖) this 3
    have hxy' :
        4 * ‖x - y‖ * (‖x‖ + ‖y‖) ^ 3 ≤
          4 * (C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) * (‖x‖ + ‖y‖) ^ 3 := by
      gcongr
    have hscale :
        4 * (C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) * (‖x‖ + ‖y‖) ^ 3 ≤
          4 * (C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) * (1 + C1 + 3) ^ 3 := by
      have hnonneg : 0 ≤ 4 * (C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) := by positivity
      exact mul_le_mul_of_nonneg_left hsum hnonneg
    have h' :
        4 * ‖x - y‖ * (‖x‖ + ‖y‖) ^ 3 ≤
          4 * (C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) * (1 + C1 + 3) ^ 3 :=
      le_trans hxy' hscale
    have hrearr :
        4 * (C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) * (1 + C1 + 3) ^ 3 =
          (4 * (1 + C1 + 3) ^ 3) * (C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) := by
      ring
    exact (h.trans h').trans_eq hrearr
  have hpow' :
      ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤
        (4 * (1 + C1 + 3) ^ 3) * C2 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
    have hexp : Real.exp (-(4 : ℝ) * Real.pi * t) ≤ Real.exp (-(3 : ℝ) * Real.pi * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, ht]
    have hmul : C2 * Real.exp (-(4 : ℝ) * Real.pi * t) ≤ C2 * Real.exp (-(3 : ℝ) * Real.pi * t) :=
      mul_le_mul_of_nonneg_left hexp hC20
    have hscale :
        (4 * (1 + C1 + 3) ^ 3) * (C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) ≤
          (4 * (1 + C1 + 3) ^ 3) * (C2 * Real.exp (-(3 : ℝ) * Real.pi * t)) :=
      mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ (4 * (1 + C1 + 3) ^ 3))
    have := le_trans hpow hscale
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hy4 :
      ‖y ^ (4 : ℕ) - (1 : ℂ) + (8 : ℂ) * q' - (24 : ℂ) * (q' ^ (2 : ℕ))‖ ≤
        48 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
    have hmain :
        y ^ (4 : ℕ) - (1 : ℂ) + (8 : ℂ) * q' - (24 : ℂ) * (q' ^ (2 : ℕ))
          = (-(32 : ℂ)) * (q' ^ (3 : ℕ)) + (16 : ℂ) * (q' ^ (4 : ℕ)) := by
      simp [y] ; ring
    have hq : ‖q'‖ ≤ 1 := by
      simpa [q'] using (norm_exp_neg_pi_mul_le_one t ht0)
    have hq4_le : ‖q' ^ (4 : ℕ)‖ ≤ ‖q' ^ (3 : ℕ)‖ := by
      have ha3 : 0 ≤ ‖q'‖ ^ (3 : ℕ) := by positivity
      have hpow : ‖q'‖ ^ (4 : ℕ) ≤ ‖q'‖ ^ (3 : ℕ) := by
        calc
          ‖q'‖ ^ (4 : ℕ) = ‖q'‖ ^ (3 : ℕ) * ‖q'‖ := by simp [pow_succ]
          _ ≤ ‖q'‖ ^ (3 : ℕ) * 1 := mul_le_mul_of_nonneg_left hq ha3
          _ = ‖q'‖ ^ (3 : ℕ) := by ring
      simpa [norm_pow] using hpow
    have hq3' : ‖q' ^ (3 : ℕ)‖ = Real.exp (-(3 : ℝ) * Real.pi * t) := by
      have hx : (Real.exp (-Real.pi * t)) ^ (3 : ℕ) = Real.exp (-(3 : ℝ) * Real.pi * t) := by
        have harg : ((3 : ℕ) : ℝ) * (-Real.pi * t) = (-(3 : ℝ) * (Real.pi * t)) := by ring
        have hx' : (Real.exp (-Real.pi * t)) ^ (3 : ℕ) = Real.exp (-(3 : ℝ) * (Real.pi * t)) := by
          simpa [harg] using (Real.exp_nat_mul (-Real.pi * t) 3).symm
        simpa [mul_assoc] using hx'
      have hnormq : ‖q'‖ = Real.exp (-Real.pi * t) := by
        simp [q', abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
      calc
        ‖q' ^ (3 : ℕ)‖ = ‖q'‖ ^ (3 : ℕ) := by simp [norm_pow]
        _ = (Real.exp (-Real.pi * t)) ^ (3 : ℕ) := by simp [hnormq]
        _ = Real.exp (-(3 : ℝ) * Real.pi * t) := hx
    have htri := norm_add_le ((-(32 : ℂ)) * (q' ^ (3 : ℕ))) ((16 : ℂ) * (q' ^ (4 : ℕ)))
    have hnorm :
        ‖(-(32 : ℂ)) * (q' ^ (3 : ℕ)) + (16 : ℂ) * (q' ^ (4 : ℕ))‖ ≤
          48 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
      calc
        ‖(-(32 : ℂ)) * (q' ^ (3 : ℕ)) + (16 : ℂ) * (q' ^ (4 : ℕ))‖
            ≤ ‖(-(32 : ℂ)) * (q' ^ (3 : ℕ))‖ + ‖(16 : ℂ) * (q' ^ (4 : ℕ))‖ := htri
        _ = 32 * ‖q' ^ (3 : ℕ)‖ + 16 * ‖q' ^ (4 : ℕ)‖ := by simp
        _ ≤ 32 * ‖q' ^ (3 : ℕ)‖ + 16 * ‖q' ^ (3 : ℕ)‖ := by gcongr
        _ = 48 * ‖q' ^ (3 : ℕ)‖ := by ring
        _ = 48 * Real.exp (-(3 : ℝ) * Real.pi * t) := by simp [hq3']
    simpa [hmain] using hnorm
  have hH4_res : ResToImagAxis H₄ t = x ^ (4 : ℕ) := by
    simp [x, H₄, ResToImagAxis, ht0]
  have hH4 : H₄.resToImagAxis t = x ^ (4 : ℕ) := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0] using hH4_res
  calc
    ‖H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
        (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
        = ‖x ^ (4 : ℕ) - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
              (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ))‖ := by
          rw [hH4]
          have ha0 : Real.exp (-(2 : ℝ) * (Real.pi * t)) = (Real.exp (-Real.pi * t)) ^ (2 : ℕ) := by
            have harg : ((2 : ℕ) : ℝ) * (-Real.pi * t) = (-(2 : ℝ) * (Real.pi * t)) := by ring
            simpa [harg] using (Real.exp_nat_mul (-Real.pi * t) 2)
          have ha : Real.exp (-(2 : ℝ) * Real.pi * t) = (Real.exp (-Real.pi * t)) ^ (2 : ℕ) := by
            simpa [mul_assoc] using ha0
          have haC0 := congrArg (fun r : ℝ => (r : ℂ)) ha
          have haC :
              (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ) =
                (Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ) := by
            simpa using haC0
          rw [haC]
    _ ≤ ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ +
          ‖y ^ (4 : ℕ) - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ))‖ := by
          have hdecomp :
              (x ^ (4 : ℕ) - y ^ (4 : ℕ)) +
                  (y ^ (4 : ℕ) - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                    (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ)))
                =
                x ^ (4 : ℕ) - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                  (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ)) := by
            ring
          have htri' :=
            norm_add_le (x ^ (4 : ℕ) - y ^ (4 : ℕ))
              (y ^ (4 : ℕ) - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ)))
          rw [hdecomp] at htri'
          exact htri'
    _ ≤ ((4 * (1 + C1 + 3) ^ 3) * C2) * Real.exp (-(3 : ℝ) * Real.pi * t) +
          48 * Real.exp (-(3 : ℝ) * Real.pi * t) := add_le_add hpow' hy4
    _ ≤ (((4 * (1 + C1 + 3) ^ 3) * C2 + 48) * Real.exp (-(3 : ℝ) * Real.pi * t)) := by
          ring_nf
          linarith
    _ = ((4 * (1 + C1 + 3) ^ 3) * C2 + 48) * Real.exp (-(3 : ℝ) * Real.pi * t) := rfl

/-- `H₃(it) + H₄(it)` cancellation up to the `exp(-2π t)` term on `t ≥ 1`. -/
public lemma exists_bound_norm_H3_add_H4_resToImagAxis_sub_two_sub_main_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖(H₃.resToImagAxis t + H₄.resToImagAxis t)
          - (2 : ℂ)
          - (48 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(3 : ℝ) * Real.pi * t) := by
  rcases exists_bound_norm_H3_resToImagAxis_sub_two_terms_Ici_one with ⟨C3, hC3⟩
  rcases exists_bound_norm_H4_resToImagAxis_sub_two_terms_Ici_one with ⟨C4, hC4⟩
  refine ⟨C3 + C4, fun t ht => ?_⟩
  calc
    ‖(H₃.resToImagAxis t + H₄.resToImagAxis t) - (2 : ℂ) -
          (48 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ ‖H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
              (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ +
            ‖H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
              (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ := by
          have htri' :=
            norm_add_le
              (H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
              (H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
          rw [show
              (H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                    (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)) +
                  (H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                    (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
                  =
                  (H₃.resToImagAxis t + H₄.resToImagAxis t) - (2 : ℂ) -
                    (48 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ) by ring] at htri'
          exact htri'
    _ ≤ (C3 + C4) * Real.exp (-(3 : ℝ) * Real.pi * t) := by
          nlinarith [hC3 t ht, hC4 t ht]

/-- Crude inverse-square bound for `H₃(it)` on `t ≥ 1`. -/
public lemma exists_bound_norm_inv_H3_sq_sub_one_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖((H₃.resToImagAxis t) ^ (2 : ℕ))⁻¹ - (1 : ℂ)‖ ≤ C * Real.exp (-Real.pi * t) := by
  rcases exists_bound_norm_H3_resToImagAxis_sub_two_terms_Ici_one with ⟨C3, hC3⟩
  let C0 : ℝ := C3 + 32
  have hC30 : 0 ≤ C3 := by
    have hmul : 0 ≤ C3 * Real.exp (-(3 : ℝ) * Real.pi * (1 : ℝ)) :=
      (norm_nonneg _).trans (hC3 1 (le_rfl : (1 : ℝ) ≤ 1))
    exact nonneg_of_mul_nonneg_left hmul (Real.exp_pos _)
  have hsub1 : ∀ t : ℝ, 1 ≤ t → ‖H₃.resToImagAxis t - (1 : ℂ)‖ ≤ C0 * Real.exp (-Real.pi * t) := by
    intro t ht
    have h := hC3 t ht
    have hq2_le : Real.exp (-(2 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, ht]
    have hq3_le : Real.exp (-(3 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, ht]
    have hexp :
        ‖(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
            (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
          ≤ 32 * Real.exp (-Real.pi * t) := by
      have h1 : ‖(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖ = 8 * Real.exp (-Real.pi * t) := by
        simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
      have h2 : ‖(24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ =
          24 * Real.exp (-(2 : ℝ) * Real.pi * t) := by
        simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
      have htri := norm_add_le ((8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ))
        ((24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
      have : 8 * Real.exp (-Real.pi * t) + 24 * Real.exp (-(2 : ℝ) * Real.pi * t)
          ≤ 32 * Real.exp (-Real.pi * t) := by
        nlinarith [hq2_le]
      nlinarith [htri, h1, h2, this]
    have htri' :
        ‖H₃.resToImagAxis t - (1 : ℂ)‖ ≤
          ‖H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
              (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ +
            ‖(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
              (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ := by
      have : H₃.resToImagAxis t - (1 : ℂ) =
          (H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
              (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)) +
            ((8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
              (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)) := by
        ring
      simpa [this] using
        (norm_add_le
          (H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
              (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
          ((8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
            (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)))
    have hmul :
        C3 * Real.exp (-(3 : ℝ) * Real.pi * t) ≤ C3 * Real.exp (-Real.pi * t) :=
      mul_le_mul_of_nonneg_left hq3_le hC30
    have hmain :
        ‖H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
              (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
          ≤ C3 * Real.exp (-Real.pi * t) :=
      h.trans hmul
    calc
      ‖H₃.resToImagAxis t - (1 : ℂ)‖
          ≤
          ‖H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
                (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ +
            ‖(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
                (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ := htri'
      _ ≤ C3 * Real.exp (-Real.pi * t) + 32 * Real.exp (-Real.pi * t) := by
            exact add_le_add hmain hexp
      _ = C0 * Real.exp (-Real.pi * t) := by
            simp [C0]
            ring
  have hnorm_H3_ge_one : ∀ t : ℝ, 1 ≤ t → (1 : ℝ) ≤ ‖H₃.resToImagAxis t‖ := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    set τ : ℂ := (Complex.I : ℂ) * (t : ℂ)
    have hτ : 0 < τ.im := by simpa [τ] using ht0
    let f : ℕ → ℝ := fun n => Real.exp (-Real.pi * (((n : ℝ) + 1) ^ 2) * t)
    have hterm : ∀ n : ℕ, cexp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ) = (f n : ℂ) := by
      intro n
      -- On the imaginary axis, the exponent is real and negative.
      have hcast : ((n : ℂ) + 1) ^ 2 = (((n : ℝ) + 1) ^ 2 : ℂ) := by
        norm_cast
      have hI_mul (z : ℂ) : (Complex.I : ℂ) * ((Complex.I : ℂ) * z) = -z := I_mul_I_mul z
      have hexp :
          (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ : ℂ)
            = (-(Real.pi * (((n : ℝ) + 1) ^ 2) * t) : ℂ) := by
        calc
          (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ : ℂ)
              = (Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * ((Complex.I : ℂ) * τ) := by
                  ac_rfl
          _ = (Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * (-(t : ℂ)) := by
                  simp [τ, hI_mul]
          _ = (-(Real.pi : ℂ)) * ((n : ℂ) + 1) ^ 2 * (t : ℂ) := by ring
          _ = (-(Real.pi : ℂ)) * (((n : ℝ) + 1) ^ 2 : ℂ) * (t : ℂ) := by
                  simp [hcast]
          _ = (-(Real.pi * (((n : ℝ) + 1) ^ 2) * t) : ℂ) := by
                  simp [mul_assoc]
      simp [f, hexp]
    have hsumA : Summable (fun n : ℕ => cexp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ)) :=
      (hasSum_nat_jacobiTheta (τ := τ) hτ).summable
    have hsumF : Summable f := by
      have : Summable (fun n : ℕ => (f n : ℂ)) := by
        simpa [hterm] using hsumA
      exact (Complex.summable_ofReal).1 this
    have hFnonneg : 0 ≤ (∑' n : ℕ, f n) := by
      exact tsum_nonneg (fun n => by positivity)
    have hjac : jacobiTheta τ = ((1 + 2 * (∑' n : ℕ, f n) : ℝ) : ℂ) := by
      have hj := jacobiTheta_eq_tsum_nat (τ := τ) hτ
      have htsum : (∑' n : ℕ, cexp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ))
          = (↑(∑' n : ℕ, f n) : ℂ) := by
        simp [Complex.ofReal_tsum, hterm]
      -- Put together.
      calc
        jacobiTheta τ
            = (1 : ℂ) + (2 : ℂ) * (↑(∑' n : ℕ, f n) : ℂ) := by
                simpa [htsum] using hj
        _ = ((1 + 2 * (∑' n : ℕ, f n) : ℝ) : ℂ) := by
              simp [Complex.ofReal_mul]
    have hΘ₃ : Θ₃.resToImagAxis t = jacobiTheta τ := by
      simp [Function.resToImagAxis, ResToImagAxis, ht0, Theta3_eq_jacobiTheta, τ]
    have hnormΘ₃ : (1 : ℝ) ≤ ‖Θ₃.resToImagAxis t‖ := by
      have hnorm_jac : ‖jacobiTheta τ‖ = (1 + 2 * (∑' n : ℕ, f n)) := by
        have hnonneg : 0 ≤ (1 + 2 * (∑' n : ℕ, f n)) := by nlinarith [hFnonneg]
        rw [hjac]
        calc
          ‖(↑(1 + 2 * ∑' n : ℕ, f n) : ℂ)‖ = |1 + 2 * ∑' n : ℕ, f n| :=
            RCLike.norm_ofReal (1 + 2 * ∑' n : ℕ, f n)
          _ = 1 + 2 * ∑' n : ℕ, f n := abs_of_nonneg hnonneg
      have hjac_ge : (1 : ℝ) ≤ ‖jacobiTheta τ‖ := by
        have : (1 : ℝ) ≤ (1 + 2 * (∑' n : ℕ, f n)) := by nlinarith [hFnonneg]
        simpa [hnorm_jac] using this
      have hnorm_eq : ‖Θ₃.resToImagAxis t‖ = ‖jacobiTheta τ‖ := congrArg norm hΘ₃
      simpa [hnorm_eq.symm] using hjac_ge
    have hnormH3_eq : ‖ResToImagAxis H₃ t‖ = ‖ResToImagAxis Θ₃ t‖ ^ (4 : ℕ) := by
      simp [H₃, ResToImagAxis, ht0, norm_pow]
    have hnormH3_ge : (1 : ℝ) ≤ ‖ResToImagAxis H₃ t‖ := by
      have hpow :
          (1 : ℝ) ^ (4 : ℕ) ≤ ‖ResToImagAxis Θ₃ t‖ ^ (4 : ℕ) :=
        pow_le_pow_left₀ (by positivity : 0 ≤ (1 : ℝ)) hnormΘ₃ 4
      have hpow' : (1 : ℝ) ≤ ‖ResToImagAxis Θ₃ t‖ ^ (4 : ℕ) := by
        simpa using hpow
      simpa [hnormH3_eq] using hpow'
    exact hnormH3_ge
  refine ⟨C0 * (C0 + 2), ?_⟩
  intro t ht
  set x : ℂ := H₃.resToImagAxis t
  have hx_inv : ‖(x ^ (2 : ℕ))⁻¹‖ ≤ 1 := by
    have hx : (1 : ℝ) ≤ ‖x‖ := hnorm_H3_ge_one t ht
    have hx2 : (1 : ℝ) ≤ ‖x‖ ^ (2 : ℕ) := by
      have : (1 : ℝ) ^ (2 : ℕ) ≤ ‖x‖ ^ (2 : ℕ) :=
        pow_le_pow_left₀ (by positivity : 0 ≤ (1 : ℝ)) hx 2
      simpa using this
    have hinv : (‖x‖ ^ (2 : ℕ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx2
    simpa [x, norm_inv, norm_pow] using hinv
  have hxsub : ‖x - (1 : ℂ)‖ ≤ C0 * Real.exp (-Real.pi * t) := by
    simpa [x] using hsub1 t ht
  have hx_le : ‖x‖ + 1 ≤ C0 + 2 := by
    have h1 : ‖x‖ ≤ ‖x - (1 : ℂ)‖ + 1 := by
      simpa [sub_eq_add_neg, add_assoc] using norm_add_le (x - 1) (1 : ℂ)
    have hexp_le : Real.exp (-Real.pi * t) ≤ 1 := by
      have : (-Real.pi * t) ≤ 0 := by nlinarith [Real.pi_pos, (le_trans zero_le_one ht)]
      exact (Real.exp_le_one_iff).2 this
    have : ‖x‖ ≤ C0 + 1 := by nlinarith [h1, hxsub, hexp_le]
    nlinarith [this]
  have hx2sub :
      ‖x ^ (2 : ℕ) - (1 : ℂ)‖ ≤ (C0 + 2) * (C0 * Real.exp (-Real.pi * t)) := by
    have hfac : x ^ (2 : ℕ) - (1 : ℂ) = (x - 1) * (x + 1) := by ring
    calc
      ‖x ^ (2 : ℕ) - (1 : ℂ)‖ = ‖(x - 1) * (x + 1)‖ := by simp [hfac]
      _ = ‖x - 1‖ * ‖x + 1‖ := by simp
      _ ≤ ‖x - 1‖ * (‖x‖ + 1) := by
            gcongr
            simpa using norm_add_le x (1 : ℂ)
      _ ≤ (C0 * Real.exp (-Real.pi * t)) * (C0 + 2) := by
            gcongr
      _ = (C0 + 2) * (C0 * Real.exp (-Real.pi * t)) := by ring
  have hmain :
      ‖(x ^ (2 : ℕ))⁻¹ - (1 : ℂ)‖ ≤ (C0 * (C0 + 2)) * Real.exp (-Real.pi * t) := by
    have hx0 : x ≠ 0 := by
      have hxpos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one (hnorm_H3_ge_one t ht)
      exact (norm_pos_iff).1 hxpos
    have hx2_0 : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hx0
    have hfac : (x ^ (2 : ℕ))⁻¹ - (1 : ℂ) = ((1 : ℂ) - x ^ (2 : ℕ)) * (x ^ (2 : ℕ))⁻¹ := by
      have : ((1 : ℂ) - x ^ (2 : ℕ)) * (x ^ (2 : ℕ))⁻¹ = (x ^ (2 : ℕ))⁻¹ - (1 : ℂ) := by
        calc
          ((1 : ℂ) - x ^ (2 : ℕ)) * (x ^ (2 : ℕ))⁻¹
              = (1 : ℂ) * (x ^ (2 : ℕ))⁻¹ - (x ^ (2 : ℕ)) * (x ^ (2 : ℕ))⁻¹ := by
                  simpa using (sub_mul (1 : ℂ) (x ^ (2 : ℕ)) (x ^ (2 : ℕ))⁻¹)
          _ = (x ^ (2 : ℕ))⁻¹ - (1 : ℂ) := by
                  simp [hx2_0]
      exact this.symm
    calc
      ‖(x ^ (2 : ℕ))⁻¹ - (1 : ℂ)‖
          = ‖((1 : ℂ) - x ^ (2 : ℕ)) * (x ^ (2 : ℕ))⁻¹‖ := by simp [hfac]
      _ = ‖x ^ (2 : ℕ) - (1 : ℂ)‖ * ‖(x ^ (2 : ℕ))⁻¹‖ := by
            have hrev : ‖(1 : ℂ) - x ^ (2 : ℕ)‖ = ‖x ^ (2 : ℕ) - (1 : ℂ)‖ := by
              simpa using (norm_sub_rev (1 : ℂ) (x ^ (2 : ℕ)))
            simp [hrev]
      _ ≤ ‖x ^ (2 : ℕ) - (1 : ℂ)‖ := by
            have hmul :=
              mul_le_mul_of_nonneg_left hx_inv (norm_nonneg (x ^ (2 : ℕ) - (1 : ℂ)))
            simpa [mul_one] using hmul
      _ ≤ (C0 * (C0 + 2)) * Real.exp (-Real.pi * t) := by
            nlinarith [hx2sub]
  simpa [x, mul_assoc] using hmain


end

end MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis
