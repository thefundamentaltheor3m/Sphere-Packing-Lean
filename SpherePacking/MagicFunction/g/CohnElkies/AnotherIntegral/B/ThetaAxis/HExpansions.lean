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

private lemma norm_pow4_sub_le (x y : ℂ) :
    ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤ 4 * ‖x - y‖ * (‖x‖ + ‖y‖) ^ 3 := by
  have hfac :
      x ^ (4 : ℕ) - y ^ (4 : ℕ) =
        (x - y) * (x ^ (3 : ℕ) + x ^ (2 : ℕ) * y + x * y ^ (2 : ℕ) + y ^ (3 : ℕ)) := by ring
  have hx : ‖x‖ ≤ ‖x‖ + ‖y‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hy : ‖y‖ ≤ ‖x‖ + ‖y‖ := le_add_of_nonneg_left (norm_nonneg _)
  have hx3 : ‖x ^ (3 : ℕ)‖ ≤ (‖x‖ + ‖y‖) ^ 3 := by
    simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hx 3
  have hy3 : ‖y ^ (3 : ℕ)‖ ≤ (‖x‖ + ‖y‖) ^ 3 := by
    simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hy 3
  have hx2 : ‖x‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hy2 : ‖y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hx2y : ‖x ^ (2 : ℕ) * y‖ ≤ (‖x‖ + ‖y‖) ^ 3 := by
    have : ‖x‖ ^ 2 * ‖y‖ ≤ (‖x‖ + ‖y‖) ^ 2 * (‖x‖ + ‖y‖) :=
      mul_le_mul hx2 hy (norm_nonneg _) (by positivity)
    simpa [norm_pow, pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
  have hxy2 : ‖x * y ^ (2 : ℕ)‖ ≤ (‖x‖ + ‖y‖) ^ 3 := by
    have : ‖x‖ * ‖y‖ ^ 2 ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) ^ 2 :=
      mul_le_mul hx hy2 (by positivity) (by positivity)
    simpa [norm_pow, pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
  have hsum :
      ‖x ^ (3 : ℕ) + x ^ (2 : ℕ) * y + x * y ^ (2 : ℕ) + y ^ (3 : ℕ)‖
        ≤ 4 * (‖x‖ + ‖y‖) ^ 3 := by
    have h0 := norm_add_le (x ^ (3 : ℕ) + x ^ (2 : ℕ) * y + x * y ^ (2 : ℕ)) (y ^ (3 : ℕ))
    have h1 := norm_add_le (x ^ (3 : ℕ) + x ^ (2 : ℕ) * y) (x * y ^ (2 : ℕ))
    have h2 := norm_add_le (x ^ (3 : ℕ)) (x ^ (2 : ℕ) * y)
    nlinarith [h0, h1, h2, hx3, hx2y, hxy2, hy3]
  calc
    ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖
        = ‖x - y‖ * ‖x ^ (3 : ℕ) + x ^ (2 : ℕ) * y + x * y ^ (2 : ℕ) + y ^ (3 : ℕ)‖ := by
          rw [hfac, norm_mul]
    _ ≤ ‖x - y‖ * (4 * (‖x‖ + ‖y‖) ^ 3) :=
          mul_le_mul_of_nonneg_left hsum (norm_nonneg (x - y))
    _ = 4 * ‖x - y‖ * (‖x‖ + ‖y‖) ^ 3 := by ring

/-- Complex cast of `exp(-πt)^N = exp(-N π t)`. -/
private lemma ofReal_exp_neg_pi_pow_eq (t : ℝ) (N : ℕ) :
    (Real.exp (-Real.pi * t) : ℂ) ^ N = (Real.exp (-(N : ℝ) * Real.pi * t) : ℂ) := by
  have hr : (Real.exp (-Real.pi * t)) ^ N = Real.exp (-(N : ℝ) * Real.pi * t) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  simpa [Complex.ofReal_pow] using congrArg (fun r : ℝ => (r : ℂ)) hr

/-- `‖(Real.exp(-πt) : ℂ)^N‖ = exp(-N π t)`. -/
private lemma norm_ofReal_exp_neg_pi_pow (t : ℝ) (N : ℕ) :
    ‖(Real.exp (-Real.pi * t) : ℂ) ^ N‖ = Real.exp (-(N : ℝ) * Real.pi * t) := by
  rw [ofReal_exp_neg_pi_pow_eq]
  simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]

/-- Nonnegativity of a bounding constant: if `‖a‖ ≤ C * exp r` then `0 ≤ C`. -/
private lemma nonneg_of_norm_le_mul_exp {α : Type*} [SeminormedAddCommGroup α]
    {a : α} {C r : ℝ} (h : ‖a‖ ≤ C * Real.exp r) : 0 ≤ C :=
  nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) (Real.exp_pos _)

/-- `H₂(it)` expansion up to the `exp(-3π t)` term on `t ≥ 1`. -/
public lemma exists_bound_norm_H2_resToImagAxis_sub_two_terms_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖H₂.resToImagAxis t
          - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
          - (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(5 : ℝ) * Real.pi * t) := by
  rcases exists_bound_norm_Theta2_resToImagAxis_Ici_one with ⟨M, hM⟩
  rcases exists_bound_norm_Theta2_resToImagAxis_sub_two_terms_Ici_one with ⟨Cθ, hCθ⟩
  have hCθ0 : 0 ≤ Cθ := nonneg_of_norm_le_mul_exp (hCθ 1 le_rfl)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 le_rfl)
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
    have hle1 : Real.exp (-Real.pi * t / 4) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, le_trans zero_le_one ht])
    have hle2 : Real.exp (-(9 / 4 : ℝ) * Real.pi * t) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht])
    have htri : ‖y‖ ≤ ‖(2 : ℂ) * a‖ + ‖(2 : ℂ) * b‖ := by
      simpa [y] using norm_add_le ((2 : ℂ) * a) ((2 : ℂ) * b)
    simp only [norm_mul, Complex.norm_ofNat, ha, hb] at htri
    linarith [htri]
  have hxy : ‖x - y‖ ≤ Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t) := by
    grind only
  have hpow' :
      ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤
        (4 * (M + 4) ^ 3) * Cθ * Real.exp (-(5 : ℝ) * Real.pi * t) := by
    have h := norm_pow4_sub_le x y
    have hsum : (‖x‖ + ‖y‖) ^ 3 ≤ (M + 4) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 3
    have hexp : Real.exp (-(25 / 4 : ℝ) * Real.pi * t) ≤ Real.exp (-(5 : ℝ) * Real.pi * t) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])
    have hbd :
        4 * ‖x - y‖ * (‖x‖ + ‖y‖) ^ 3 ≤
          4 * (Cθ * Real.exp (-(5 : ℝ) * Real.pi * t)) * (M + 4) ^ 3 := by
      gcongr
      exact hxy.trans (mul_le_mul_of_nonneg_left hexp hCθ0)
    linarith [h.trans hbd]
  -- Replace `y = 2a + 2b` into `y^4` and express `a^4`, `a^3·b` via exp-arithmetic.
  have ha4 : a ^ (4 : ℕ) = (Real.exp (-Real.pi * t) : ℂ) := by
    have hr : (Real.exp (-Real.pi * t / 4)) ^ (4 : ℕ) = Real.exp (-Real.pi * t) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    simpa [a, Complex.ofReal_pow] using congrArg (fun r : ℝ => (r : ℂ)) hr
  have ha3b : a ^ (3 : ℕ) * b = (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) := by
    have hr : (Real.exp (-Real.pi * t / 4)) ^ (3 : ℕ) *
        Real.exp (-(9 / 4 : ℝ) * Real.pi * t) = Real.exp (-(3 : ℝ) * Real.pi * t) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
    simpa [a, b, Complex.ofReal_pow, Complex.ofReal_mul] using
      congrArg (fun r : ℝ => (r : ℂ)) hr
  have hy_main :
      y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) - (64 : ℂ) *
            (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)
        = (96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ)) + (64 : ℂ) * (a * b ^ (3 : ℕ)) +
            (16 : ℂ) * (b ^ (4 : ℕ)) := by
    grind only
  have hy_tail :
      ‖y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
            (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ 176 * Real.exp (-(5 : ℝ) * Real.pi * t) := by
    have ha : ‖a‖ = Real.exp (-Real.pi * t / 4) := by
      simp [-Complex.ofReal_exp, a, abs_of_nonneg (Real.exp_pos _).le]
    have hb : ‖b‖ = Real.exp (-(9 / 4 : ℝ) * Real.pi * t) := by
      simp [-Complex.ofReal_exp, b, abs_of_nonneg (Real.exp_pos _).le]
    -- General form: ‖a^i · b^j‖ = exp((i·(-π/4) + j·(-9π/4)) · t) up to sign.
    have hab : ‖a ^ (2 : ℕ) * b ^ (2 : ℕ)‖ = Real.exp (-(5 : ℝ) * Real.pi * t) := by
      have hr : (Real.exp (-Real.pi * t / 4)) ^ 2 * (Real.exp (-(9 / 4 : ℝ) * Real.pi * t)) ^ 2
          = Real.exp (-(5 : ℝ) * Real.pi * t) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
      simpa [norm_mul, norm_pow, ha, hb] using hr
    have hab3 : ‖a * b ^ (3 : ℕ)‖ = Real.exp (-(7 : ℝ) * Real.pi * t) := by
      have hr : Real.exp (-Real.pi * t / 4) * (Real.exp (-(9 / 4 : ℝ) * Real.pi * t)) ^ 3
          = Real.exp (-(7 : ℝ) * Real.pi * t) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
      simpa [norm_mul, norm_pow, ha, hb] using hr
    have hb4 : ‖b ^ (4 : ℕ)‖ = Real.exp (-(9 : ℝ) * Real.pi * t) := by
      have hr : (Real.exp (-(9 / 4 : ℝ) * Real.pi * t)) ^ 4 =
          Real.exp (-(9 : ℝ) * Real.pi * t) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      simpa [norm_pow, hb] using hr
    have hab3_le : ‖a * b ^ (3 : ℕ)‖ ≤ Real.exp (-(5 : ℝ) * Real.pi * t) := by
      rw [hab3]; exact Real.exp_monotone (by nlinarith [Real.pi_pos, ht])
    have hb4_le : ‖b ^ (4 : ℕ)‖ ≤ Real.exp (-(5 : ℝ) * Real.pi * t) := by
      rw [hb4]; exact Real.exp_monotone (by nlinarith [Real.pi_pos, ht])
    rw [hy_main]
    have htri1 :=
      norm_add_le ((96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ)) + (64 : ℂ) * (a * b ^ (3 : ℕ)))
        ((16 : ℂ) * (b ^ (4 : ℕ)))
    have htri2 :=
      norm_add_le ((96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ))) ((64 : ℂ) * (a * b ^ (3 : ℕ)))
    have hn1 : ‖(96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ))‖ = 96 * ‖a ^ (2 : ℕ) * b ^ (2 : ℕ)‖ := by
      simp
    have hn2 : ‖(64 : ℂ) * (a * b ^ (3 : ℕ))‖ = 64 * ‖a * b ^ (3 : ℕ)‖ := by simp
    have hn3 : ‖(16 : ℂ) * (b ^ (4 : ℕ))‖ = 16 * ‖b ^ (4 : ℕ)‖ := by simp
    nlinarith [htri1, htri2, hab, hab3_le, hb4_le, hn1, hn2, hn3]
  have hH2 : H₂.resToImagAxis t = x ^ (4 : ℕ) := by
    simp [x, H₂, Function.resToImagAxis, ResToImagAxis, ht0]
  have htri : ‖x ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
        (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖ ≤
      ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ +
        ‖y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
          (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖ := by
    have h := norm_add_le (x ^ (4 : ℕ) - y ^ (4 : ℕ))
      (y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
        (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ))
    convert h using 2; ring
  rw [hH2]
  linarith [htri.trans (add_le_add hpow' hy_tail)]

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
  have hC10 : 0 ≤ C1 := nonneg_of_norm_le_mul_exp (hC1 1 le_rfl)
  have hC20 : 0 ≤ C2 := nonneg_of_norm_le_mul_exp (hC2 1 le_rfl)
  refine ⟨(4 * (1 + C1 + 3) ^ 3) * C2 + 48, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set q' : ℂ := (Real.exp (-Real.pi * t) : ℂ)
  set x : ℂ := Θ₃.resToImagAxis t
  set y : ℂ := (1 : ℂ) + (2 : ℂ) * q'
  have hq : ‖q'‖ ≤ 1 := by simpa [q'] using norm_exp_neg_pi_mul_le_one t ht0
  have hexp1 : Real.exp (-Real.pi * t) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht0.le])
  have hx : ‖x‖ ≤ 1 + C1 := by
    have hx1 : ‖x - 1‖ ≤ C1 := (hC1 t ht).trans <| by
      simpa [mul_one] using mul_le_mul_of_nonneg_left hexp1 hC10
    have htri : ‖x‖ ≤ ‖x - 1‖ + 1 := by
      simpa [sub_eq_add_neg, add_assoc] using norm_add_le (x - 1) (1 : ℂ)
    linarith
  have hy : ‖y‖ ≤ 3 := by
    have : ‖y‖ ≤ 1 + 2 * ‖q'‖ := by
      simpa [y, norm_mul, Complex.norm_two] using norm_add_le (1 : ℂ) ((2 : ℂ) * q')
    linarith
  have hxy : ‖x - y‖ ≤ C2 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
    simpa [x, y, q', sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using hC2 t ht
  have hpow' :
      ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤
        (4 * (1 + C1 + 3) ^ 3) * C2 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
    have h := norm_pow4_sub_le x y
    have hsum : (‖x‖ + ‖y‖) ^ 3 ≤ (1 + C1 + 3) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith [hx, hy]) 3
    have hexp : Real.exp (-(4 : ℝ) * Real.pi * t) ≤ Real.exp (-(3 : ℝ) * Real.pi * t) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])
    have hbd :
        4 * ‖x - y‖ * (‖x‖ + ‖y‖) ^ 3 ≤
          4 * (C2 * Real.exp (-(3 : ℝ) * Real.pi * t)) * (1 + C1 + 3) ^ 3 := by
      gcongr
      exact hxy.trans (mul_le_mul_of_nonneg_left hexp hC20)
    linarith [h.trans hbd]
  have hy4 :
      ‖y ^ (4 : ℕ) - (1 : ℂ) - (8 : ℂ) * q' - (24 : ℂ) * (q' ^ (2 : ℕ))‖ ≤
        48 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
    have hmain : y ^ (4 : ℕ) - (1 : ℂ) - (8 : ℂ) * q' - (24 : ℂ) * (q' ^ (2 : ℕ))
        = (32 : ℂ) * (q' ^ (3 : ℕ)) + (16 : ℂ) * (q' ^ (4 : ℕ)) := by
      simp [y] ; ring
    have hq3' : ‖q' ^ (3 : ℕ)‖ = Real.exp (-(3 : ℝ) * Real.pi * t) := by
      simpa [q'] using norm_ofReal_exp_neg_pi_pow t 3
    have hq4_le : ‖q' ^ (4 : ℕ)‖ ≤ ‖q' ^ (3 : ℕ)‖ := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, norm_mul]
      simpa using mul_le_mul_of_nonneg_left hq (norm_nonneg (q' ^ (3 : ℕ)))
    have htri := norm_add_le ((32 : ℂ) * (q' ^ (3 : ℕ))) ((16 : ℂ) * (q' ^ (4 : ℕ)))
    simp only [norm_mul, Complex.norm_ofNat] at htri
    rw [hmain]
    nlinarith [htri, hq4_le, hq3', norm_nonneg (q' ^ (3 : ℕ))]
  have hH3 : H₃.resToImagAxis t = x ^ (4 : ℕ) := by
    simp [x, H₃, Function.resToImagAxis, ResToImagAxis, ht0]
  have hexpN2 : (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ) =
      (Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ) :=
    (ofReal_exp_neg_pi_pow_eq t 2).symm
  have htri : ‖x ^ (4 : ℕ) - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
        (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ))‖ ≤
      ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ +
        ‖y ^ (4 : ℕ) - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
          (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ))‖ := by
    have h := norm_add_le (x ^ (4 : ℕ) - y ^ (4 : ℕ))
      (y ^ (4 : ℕ) - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
        (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ)))
    convert h using 2; ring
  rw [hH3, hexpN2]
  linarith [htri.trans (add_le_add hpow' hy4)]

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
  have hC10 : 0 ≤ C1 := nonneg_of_norm_le_mul_exp (hC1 1 le_rfl)
  have hC20 : 0 ≤ C2 := nonneg_of_norm_le_mul_exp (hC2 1 le_rfl)
  refine ⟨(4 * (1 + C1 + 3) ^ 3) * C2 + 48, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set q' : ℂ := (Real.exp (-Real.pi * t) : ℂ)
  set x : ℂ := Θ₄.resToImagAxis t
  set y : ℂ := (1 : ℂ) - (2 : ℂ) * q'
  have hq : ‖q'‖ ≤ 1 := by simpa [q'] using norm_exp_neg_pi_mul_le_one t ht0
  have hexp1 : Real.exp (-Real.pi * t) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht0.le])
  have hx : ‖x‖ ≤ 1 + C1 := by
    have hx1 : ‖x - 1‖ ≤ C1 := (hC1 t ht).trans <| by
      simpa [mul_one] using mul_le_mul_of_nonneg_left hexp1 hC10
    have htri : ‖x‖ ≤ ‖x - 1‖ + 1 := by
      simpa [sub_eq_add_neg, add_assoc] using norm_add_le (x - 1) (1 : ℂ)
    linarith
  have hy : ‖y‖ ≤ 3 := by
    have : ‖y‖ ≤ 1 + 2 * ‖q'‖ := by
      simpa [y, sub_eq_add_neg, norm_mul, Complex.norm_two] using
        norm_add_le (1 : ℂ) (-((2 : ℂ) * q'))
    linarith
  have hxy : ‖x - y‖ ≤ C2 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
    simpa [x, y, q', sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using hC2 t ht
  have hpow' :
      ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤
        (4 * (1 + C1 + 3) ^ 3) * C2 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
    have h := norm_pow4_sub_le x y
    have hsum : (‖x‖ + ‖y‖) ^ 3 ≤ (1 + C1 + 3) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith [hx, hy]) 3
    have hexp : Real.exp (-(4 : ℝ) * Real.pi * t) ≤ Real.exp (-(3 : ℝ) * Real.pi * t) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])
    have hbd :
        4 * ‖x - y‖ * (‖x‖ + ‖y‖) ^ 3 ≤
          4 * (C2 * Real.exp (-(3 : ℝ) * Real.pi * t)) * (1 + C1 + 3) ^ 3 := by
      gcongr
      exact hxy.trans (mul_le_mul_of_nonneg_left hexp hC20)
    linarith [h.trans hbd]
  have hy4 :
      ‖y ^ (4 : ℕ) - (1 : ℂ) + (8 : ℂ) * q' - (24 : ℂ) * (q' ^ (2 : ℕ))‖ ≤
        48 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
    have hmain :
        y ^ (4 : ℕ) - (1 : ℂ) + (8 : ℂ) * q' - (24 : ℂ) * (q' ^ (2 : ℕ))
          = (-(32 : ℂ)) * (q' ^ (3 : ℕ)) + (16 : ℂ) * (q' ^ (4 : ℕ)) := by
      simp [y] ; ring
    have hq3' : ‖q' ^ (3 : ℕ)‖ = Real.exp (-(3 : ℝ) * Real.pi * t) := by
      simpa [q'] using norm_ofReal_exp_neg_pi_pow t 3
    have hq4_le : ‖q' ^ (4 : ℕ)‖ ≤ ‖q' ^ (3 : ℕ)‖ := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, norm_mul]
      simpa using mul_le_mul_of_nonneg_left hq (norm_nonneg (q' ^ (3 : ℕ)))
    have htri := norm_add_le ((-(32 : ℂ)) * (q' ^ (3 : ℕ))) ((16 : ℂ) * (q' ^ (4 : ℕ)))
    simp only [norm_mul, norm_neg, Complex.norm_ofNat] at htri
    rw [hmain]
    nlinarith [htri, hq4_le, hq3', norm_nonneg (q' ^ (3 : ℕ))]
  have hH4 : H₄.resToImagAxis t = x ^ (4 : ℕ) := by
    simp [x, H₄, Function.resToImagAxis, ResToImagAxis, ht0]
  have hexpN2 : (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ) =
      (Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ) :=
    (ofReal_exp_neg_pi_pow_eq t 2).symm
  have htri : ‖x ^ (4 : ℕ) - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
        (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ))‖ ≤
      ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ +
        ‖y ^ (4 : ℕ) - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
          (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ))‖ := by
    have h := norm_add_le (x ^ (4 : ℕ) - y ^ (4 : ℕ))
      (y ^ (4 : ℕ) - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
        (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ)))
    convert h using 2; ring
  rw [hH4, hexpN2]
  linarith [htri.trans (add_le_add hpow' hy4)]

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
  have htri :=
    norm_add_le
      (H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
        (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
      (H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
        (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
  have hcong : ‖(H₃.resToImagAxis t + H₄.resToImagAxis t) - (2 : ℂ) -
        (48 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ ≤
      ‖H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
        (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ +
      ‖H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
        (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ := by
    convert htri using 2; ring
  linarith [hcong, hC3 t ht, hC4 t ht]

/-- Crude inverse-square bound for `H₃(it)` on `t ≥ 1`. -/
public lemma exists_bound_norm_inv_H3_sq_sub_one_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖((H₃.resToImagAxis t) ^ (2 : ℕ))⁻¹ - (1 : ℂ)‖ ≤ C * Real.exp (-Real.pi * t) := by
  rcases exists_bound_norm_H3_resToImagAxis_sub_two_terms_Ici_one with ⟨C3, hC3⟩
  let C0 : ℝ := C3 + 32
  have hC30 : 0 ≤ C3 := nonneg_of_norm_le_mul_exp (hC3 1 le_rfl)
  have hsub1 : ∀ t : ℝ, 1 ≤ t → ‖H₃.resToImagAxis t - (1 : ℂ)‖ ≤ C0 * Real.exp (-Real.pi * t) := by
    intro t ht
    have hq2_le : Real.exp (-(2 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])
    have hq3_le : Real.exp (-(3 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])
    have htri := norm_add_le
      ((8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ))
      ((24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
    have h1 : ‖(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖ = 8 * Real.exp (-Real.pi * t) := by
      simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
    have h2 : ‖(24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ =
        24 * Real.exp (-(2 : ℝ) * Real.pi * t) := by
      simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
    have htri' :=
      norm_add_le
        (H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
          (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
        ((8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
          (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
    have heq : (H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
          (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)) +
          ((8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
          (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)) =
        H₃.resToImagAxis t - (1 : ℂ) := by ring
    rw [heq] at htri'
    have hmul := mul_le_mul_of_nonneg_left hq3_le hC30
    simp only [C0]
    nlinarith [htri, htri', h1, h2, hmul, hC3 t ht, hq2_le, Real.exp_pos (-Real.pi * t)]
  have hnorm_H3_ge_one : ∀ t : ℝ, 1 ≤ t → (1 : ℝ) ≤ ‖H₃.resToImagAxis t‖ := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    set τ : ℂ := (Complex.I : ℂ) * (t : ℂ)
    have hτ : 0 < τ.im := by simpa [τ] using ht0
    let f : ℕ → ℝ := fun n => Real.exp (-Real.pi * (((n : ℝ) + 1) ^ 2) * t)
    have hterm : ∀ n : ℕ, cexp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ) = (f n : ℂ) := by
      intro n
      have hcast : ((n : ℂ) + 1) ^ 2 = (((n : ℝ) + 1) ^ 2 : ℂ) := by norm_cast
      have hI_mul (z : ℂ) : (Complex.I : ℂ) * ((Complex.I : ℂ) * z) = -z := by
        rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
      have hexp :
          (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ : ℂ)
            = (-(Real.pi * (((n : ℝ) + 1) ^ 2) * t) : ℂ) := by
        have : (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ : ℂ)
            = (Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * ((Complex.I : ℂ) * τ) := by ac_rfl
        rw [this, show τ = Complex.I * (t : ℂ) from rfl, hI_mul, hcast]
        push_cast; ring
      simp [f, hexp]
    have hsumA : Summable (fun n : ℕ => cexp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ)) :=
      (hasSum_nat_jacobiTheta (τ := τ) hτ).summable
    have hFnonneg : 0 ≤ (∑' n : ℕ, f n) := tsum_nonneg (fun n => by positivity)
    have hjac : jacobiTheta τ = ((1 + 2 * (∑' n : ℕ, f n) : ℝ) : ℂ) := by
      have hj := jacobiTheta_eq_tsum_nat (τ := τ) hτ
      have htsum : (∑' n : ℕ, cexp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ))
          = (↑(∑' n : ℕ, f n) : ℂ) := by
        simp [Complex.ofReal_tsum, hterm]
      rw [hj, htsum]; push_cast; ring
    have hΘ₃ : Θ₃.resToImagAxis t = jacobiTheta τ := by
      simp [Function.resToImagAxis, ResToImagAxis, ht0, Theta3_eq_jacobiTheta, τ]
    have hnormΘ₃ : (1 : ℝ) ≤ ‖Θ₃.resToImagAxis t‖ := by
      rw [hΘ₃, hjac, Complex.norm_of_nonneg (by positivity)]
      linarith [hFnonneg]
    have hnormH3_eq : ‖ResToImagAxis H₃ t‖ = ‖ResToImagAxis Θ₃ t‖ ^ (4 : ℕ) := by
      simp [H₃, ResToImagAxis, ht0, norm_pow]
    have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1) hnormΘ₃ 4
    simpa [hnormH3_eq] using this
  refine ⟨C0 * (C0 + 2), ?_⟩
  intro t ht
  set x : ℂ := H₃.resToImagAxis t
  have hxge : (1 : ℝ) ≤ ‖x‖ := hnorm_H3_ge_one t ht
  have hx_inv : ‖(x ^ (2 : ℕ))⁻¹‖ ≤ 1 := by
    simpa [x, norm_inv, norm_pow] using inv_le_one_of_one_le₀ (one_le_pow₀ hxge)
  have hxsub : ‖x - (1 : ℂ)‖ ≤ C0 * Real.exp (-Real.pi * t) := hsub1 t ht
  have hx_le : ‖x‖ + 1 ≤ C0 + 2 := by
    have h1 : ‖x‖ ≤ ‖x - (1 : ℂ)‖ + 1 := by
      simpa [sub_eq_add_neg, add_assoc] using norm_add_le (x - 1) (1 : ℂ)
    have hexp_le : Real.exp (-Real.pi * t) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, le_trans zero_le_one ht])
    nlinarith [h1, hxsub, hexp_le]
  have hx2sub :
      ‖x ^ (2 : ℕ) - (1 : ℂ)‖ ≤ (C0 + 2) * (C0 * Real.exp (-Real.pi * t)) := by
    have hfac : ‖x ^ (2 : ℕ) - (1 : ℂ)‖ = ‖x - 1‖ * ‖x + 1‖ := by
      rw [show x ^ (2 : ℕ) - (1 : ℂ) = (x - 1) * (x + 1) from by ring, norm_mul]
    have h1 : ‖x + 1‖ ≤ C0 + 2 :=
      ((by simpa using norm_add_le x (1 : ℂ)) : ‖x + 1‖ ≤ ‖x‖ + 1).trans hx_le
    rw [hfac]
    calc ‖x - 1‖ * ‖x + 1‖
        ≤ (C0 * Real.exp (-Real.pi * t)) * (C0 + 2) := by gcongr
      _ = (C0 + 2) * (C0 * Real.exp (-Real.pi * t)) := by ring
  have hx0 : x ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le zero_lt_one hxge)
  have hfac : (x ^ (2 : ℕ))⁻¹ - (1 : ℂ) = ((1 : ℂ) - x ^ (2 : ℕ)) * (x ^ (2 : ℕ))⁻¹ := by
    field_simp
  have : ‖(x ^ (2 : ℕ))⁻¹ - (1 : ℂ)‖ ≤ ‖x ^ (2 : ℕ) - (1 : ℂ)‖ := by
    rw [hfac, norm_mul, norm_sub_rev]
    simpa using mul_le_mul_of_nonneg_left hx_inv (norm_nonneg (x ^ (2 : ℕ) - (1 : ℂ)))
  have := this.trans hx2sub
  simpa [x, mul_assoc, mul_left_comm, mul_comm] using this


end

end MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis
