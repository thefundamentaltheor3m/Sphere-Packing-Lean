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
  have hx : ‖x‖ ≤ ‖x‖ + ‖y‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hy : ‖y‖ ≤ ‖x‖ + ‖y‖ := le_add_of_nonneg_left (norm_nonneg _)
  have hx3 : ‖x ^ (3 : ℕ)‖ ≤ (‖x‖ + ‖y‖) ^ 3 := by
    simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hx 3
  have hy3 : ‖y ^ (3 : ℕ)‖ ≤ (‖x‖ + ‖y‖) ^ 3 := by
    simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hy 3
  have hx2y : ‖x ^ (2 : ℕ) * y‖ ≤ (‖x‖ + ‖y‖) ^ 3 := by
    simpa [norm_pow, pow_succ, mul_comm] using
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx 2) hy (norm_nonneg _) (by positivity)
  have hxy2 : ‖x * y ^ (2 : ℕ)‖ ≤ (‖x‖ + ‖y‖) ^ 3 := by
    simpa [norm_pow, pow_succ, mul_comm] using
      mul_le_mul hx (pow_le_pow_left₀ (norm_nonneg _) hy 2) (by positivity) (by positivity)
  rw [show x ^ (4 : ℕ) - y ^ (4 : ℕ) =
    (x - y) * (x ^ (3 : ℕ) + x ^ (2 : ℕ) * y + x * y ^ (2 : ℕ) + y ^ (3 : ℕ)) by ring, norm_mul]
  nlinarith [norm_add_le (x ^ (3 : ℕ) + x ^ (2 : ℕ) * y + x * y ^ (2 : ℕ)) (y ^ (3 : ℕ)),
    norm_add_le (x ^ (3 : ℕ) + x ^ (2 : ℕ) * y) (x * y ^ (2 : ℕ)),
    norm_add_le (x ^ (3 : ℕ)) (x ^ (2 : ℕ) * y), hx3, hx2y, hxy2, hy3, norm_nonneg (x - y)]

/-- Complex cast of `exp(-πt)^N = exp(-N π t)`. -/
private lemma ofReal_exp_neg_pi_pow_eq (t : ℝ) (N : ℕ) :
    (Real.exp (-Real.pi * t) : ℂ) ^ N = (Real.exp (-(N : ℝ) * Real.pi * t) : ℂ) := by
  rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]; push_cast; ring_nf

/-- `‖(Real.exp(-πt) : ℂ)^N‖ = exp(-N π t)`. -/
private lemma norm_ofReal_exp_neg_pi_pow (t : ℝ) (N : ℕ) :
    ‖(Real.exp (-Real.pi * t) : ℂ) ^ N‖ = Real.exp (-(N : ℝ) * Real.pi * t) := by
  rw [ofReal_exp_neg_pi_pow_eq]; simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]

/-- Nonnegativity of a bounding constant: if `‖a‖ ≤ C * exp r` then `0 ≤ C`. -/
private lemma nonneg_of_norm_le_mul_exp {α : Type*} [SeminormedAddCommGroup α] {a : α} {C r : ℝ}
    (h : ‖a‖ ≤ C * Real.exp r) : 0 ≤ C :=
  nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) (Real.exp_pos _)

private lemma norm_le_one_add_of_sub_one (x : ℂ) {C : ℝ} (h : ‖x - 1‖ ≤ C) : ‖x‖ ≤ 1 + C := by
  linarith [show ‖x‖ ≤ ‖x - 1‖ + 1 by
    simpa [sub_eq_add_neg, add_assoc] using norm_add_le (x - 1) (1 : ℂ)]

private lemma norm_pow4_le_pow3 {q : ℂ} (hq : ‖q‖ ≤ 1) : ‖q ^ (4 : ℕ)‖ ≤ ‖q ^ (3 : ℕ)‖ := by
  simpa [pow_succ, norm_mul] using mul_le_mul_of_nonneg_left hq (norm_nonneg (q ^ (3 : ℕ)))

/-- `H₂(it)` expansion up to the `exp(-3π t)` term on `t ≥ 1`. -/
public lemma exists_bound_norm_H2_resToImagAxis_sub_two_terms_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖H₂.resToImagAxis t
          - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
          - (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(5 : ℝ) * Real.pi * t) := by
  obtain ⟨M, hM⟩ := exists_bound_norm_Theta2_resToImagAxis_Ici_one
  obtain ⟨Cθ, hCθ⟩ := exists_bound_norm_Theta2_resToImagAxis_sub_two_terms_Ici_one
  have hCθ0 : 0 ≤ Cθ := nonneg_of_norm_le_mul_exp (hCθ 1 le_rfl)
  refine ⟨(4 * (M + 4) ^ 3) * Cθ + 176, fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set a : ℂ := (Real.exp (-Real.pi * t / 4) : ℂ)
  set b : ℂ := (Real.exp (-(9 / 4 : ℝ) * Real.pi * t) : ℂ)
  set x : ℂ := Θ₂.resToImagAxis t
  set y : ℂ := (2 : ℂ) * a + (2 : ℂ) * b
  have hx : ‖x‖ ≤ M := hM t ht
  have ha_norm : ‖a‖ = Real.exp (-Real.pi * t / 4) := by
    simp [-Complex.ofReal_exp, a, abs_of_nonneg (Real.exp_pos _).le]
  have hb_norm : ‖b‖ = Real.exp (-(9 / 4 : ℝ) * Real.pi * t) := by
    simp [-Complex.ofReal_exp, b, abs_of_nonneg (Real.exp_pos _).le]
  have hy : ‖y‖ ≤ 4 := by
    have htri : ‖y‖ ≤ ‖(2 : ℂ) * a‖ + ‖(2 : ℂ) * b‖ := by
      simpa [y] using norm_add_le ((2 : ℂ) * a) ((2 : ℂ) * b)
    simp only [norm_mul, Complex.norm_ofNat, ha_norm, hb_norm] at htri
    linarith [Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, le_trans zero_le_one ht] :
        -Real.pi * t / 4 ≤ 0),
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht] : -(9 / 4 : ℝ) * Real.pi * t ≤ 0)]
  have hxy : ‖x - y‖ ≤ Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t) := by grind only
  have hpow' : ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤
        (4 * (M + 4) ^ 3) * Cθ * Real.exp (-(5 : ℝ) * Real.pi * t) := by
    have hbd : 4 * ‖x - y‖ * (‖x‖ + ‖y‖) ^ 3 ≤
        4 * (Cθ * Real.exp (-(5 : ℝ) * Real.pi * t)) * (M + 4) ^ 3 := by
      gcongr (4 * ?_ * ?_) with _ _
      exacts [hxy.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])) hCθ0),
        pow_le_pow_left₀ (by positivity) (by linarith) 3]
    linarith [(norm_pow4_sub_le x y).trans hbd]
  have hy_main : y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) - (64 : ℂ) *
      (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) = (96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ)) +
        (64 : ℂ) * (a * b ^ (3 : ℕ)) + (16 : ℂ) * (b ^ (4 : ℕ)) := by
    have ha4 : a ^ (4 : ℕ) = (Real.exp (-Real.pi * t) : ℂ) := by
      rw [show a = ((Real.exp (-Real.pi * t / 4) : ℝ) : ℂ) from rfl, ← Complex.ofReal_pow,
        ← Real.exp_nat_mul]; push_cast; ring_nf
    have ha3b : a ^ (3 : ℕ) * b = (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) := by
      rw [show a = ((Real.exp (-Real.pi * t / 4) : ℝ) : ℂ) from rfl,
        show b = ((Real.exp (-(9/4 : ℝ) * Real.pi * t) : ℝ) : ℂ) from rfl,
        ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      push_cast; ring_nf
    grind only
  have hy_tail : ‖y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
        (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖ ≤
          176 * Real.exp (-(5 : ℝ) * Real.pi * t) := by
    have hab : ‖a ^ (2 : ℕ) * b ^ (2 : ℕ)‖ = Real.exp (-(5 : ℝ) * Real.pi * t) := by
      simpa [norm_mul, norm_pow, ha_norm, hb_norm, ← Real.exp_nat_mul, ← Real.exp_add] using
        congrArg Real.exp (show (2 : ℕ) * (-Real.pi * t / 4) + (2 : ℕ) *
          (-(9 / 4 : ℝ) * Real.pi * t) = -(5 : ℝ) * Real.pi * t by ring)
    have hab3_le : ‖a * b ^ (3 : ℕ)‖ ≤ Real.exp (-(5 : ℝ) * Real.pi * t) := by
      rw [show ‖a * b ^ (3 : ℕ)‖ = Real.exp (-(7 : ℝ) * Real.pi * t) by
        simpa [norm_mul, norm_pow, ha_norm, hb_norm, ← Real.exp_nat_mul, ← Real.exp_add] using
          congrArg Real.exp (show -Real.pi * t / 4 + (3 : ℕ) * (-(9 / 4 : ℝ) * Real.pi * t) =
            -(7 : ℝ) * Real.pi * t by ring)]
      exact Real.exp_monotone (by nlinarith [Real.pi_pos, ht])
    have hb4_le : ‖b ^ (4 : ℕ)‖ ≤ Real.exp (-(5 : ℝ) * Real.pi * t) := by
      rw [show ‖b ^ (4 : ℕ)‖ = Real.exp (-(9 : ℝ) * Real.pi * t) by
        simpa [norm_pow, hb_norm, ← Real.exp_nat_mul] using congrArg Real.exp
          (show (4 : ℕ) * (-(9 / 4 : ℝ) * Real.pi * t) = -(9 : ℝ) * Real.pi * t by ring)]
      exact Real.exp_monotone (by nlinarith [Real.pi_pos, ht])
    rw [hy_main]
    nlinarith [norm_add_le ((96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ)) +
      (64 : ℂ) * (a * b ^ (3 : ℕ))) ((16 : ℂ) * (b ^ (4 : ℕ))),
      norm_add_le ((96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ))) ((64 : ℂ) * (a * b ^ (3 : ℕ))),
      hab, hab3_le, hb4_le,
      (by simp : ‖(96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ))‖ = 96 * ‖a ^ (2 : ℕ) * b ^ (2 : ℕ)‖),
      (by simp : ‖(64 : ℂ) * (a * b ^ (3 : ℕ))‖ = 64 * ‖a * b ^ (3 : ℕ)‖),
      (by simp : ‖(16 : ℂ) * (b ^ (4 : ℕ))‖ = 16 * ‖b ^ (4 : ℕ)‖)]
  rw [show H₂.resToImagAxis t = x ^ (4 : ℕ) by
    simp [x, H₂, Function.resToImagAxis, ResToImagAxis, ht0]]
  have htri := norm_add_le (x ^ (4 : ℕ) - y ^ (4 : ℕ))
    (y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
      (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ))
  rw [show x ^ (4 : ℕ) - y ^ (4 : ℕ) + (y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
    (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)) = x ^ (4 : ℕ) -
    (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
    (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) by ring] at htri
  linarith [htri.trans (add_le_add hpow' hy_tail)]

/-- Generic `H_j(it)` expansion up to the `exp(-2π t)` term on `t ≥ 1`, parametrized by sign.
The sign `σ = +1` gives the H₃ case (`y = 1 + 2q`), `σ = -1` gives H₄ (`y = 1 - 2q`). -/
private lemma exists_bound_H3_or_H4_aux {Hj Θj : ℝ → ℂ} {σ : ℂ} (hσ : σ = 1 ∨ σ = -1)
    (hHj : ∀ t : ℝ, 0 < t → Hj t = (Θj t) ^ (4 : ℕ))
    {C1 C2 : ℝ} (hC10 : 0 ≤ C1) (hC20 : 0 ≤ C2)
    (hC1 : ∀ t : ℝ, 1 ≤ t → ‖Θj t - 1‖ ≤ C1 * Real.exp (-Real.pi * t))
    (hC2 : ∀ t : ℝ, 1 ≤ t →
      ‖Θj t - 1 - σ * (2 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖ ≤
        C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖Hj t - (1 : ℂ) - σ * (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
          - (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(3 : ℝ) * Real.pi * t) := by
  refine ⟨(4 * (1 + C1 + 3) ^ 3) * C2 + 48, fun t ht ↦ ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set q' : ℂ := (Real.exp (-Real.pi * t) : ℂ)
  set x : ℂ := Θj t
  set y : ℂ := (1 : ℂ) + σ * (2 : ℂ) * q'
  have hq : ‖q'‖ ≤ 1 := by simpa [q'] using norm_exp_neg_pi_mul_le_one t ht0
  have hx : ‖x‖ ≤ 1 + C1 := norm_le_one_add_of_sub_one x <| (hC1 t ht).trans <| by
    simpa [mul_one] using mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht0.le])) hC10
  have hσ_norm : ‖σ‖ = 1 := by rcases hσ with rfl | rfl <;> simp
  have hy : ‖y‖ ≤ 3 := by
    have h := norm_add_le (1 : ℂ) (σ * (2 : ℂ) * q')
    simp only [norm_one, norm_mul, hσ_norm, Complex.norm_ofNat, one_mul] at h; linarith
  have hxy : ‖x - y‖ ≤ C2 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
    simpa [x, y, q', sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using hC2 t ht
  have hpow' : ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤
        (4 * (1 + C1 + 3) ^ 3) * C2 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
    have hbd : 4 * ‖x - y‖ * (‖x‖ + ‖y‖) ^ 3 ≤
        4 * (C2 * Real.exp (-(3 : ℝ) * Real.pi * t)) * (1 + C1 + 3) ^ 3 := by
      gcongr (4 * ?_ * ?_) with _ _
      exacts [hxy.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])) hC20),
        pow_le_pow_left₀ (by positivity) (by linarith [hx, hy]) 3]
    linarith [(norm_pow4_sub_le x y).trans hbd]
  have hy4 : ‖y ^ (4 : ℕ) - (1 : ℂ) - σ * (8 : ℂ) * q' - (24 : ℂ) * (q' ^ (2 : ℕ))‖ ≤
        48 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
    have hq3' : ‖q' ^ (3 : ℕ)‖ = Real.exp (-(3 : ℝ) * Real.pi * t) := by
      simpa [q'] using norm_ofReal_exp_neg_pi_pow t 3
    have htri := norm_add_le ((32 : ℂ) * σ ^ 3 * (q' ^ (3 : ℕ))) ((16 : ℂ) * (q' ^ (4 : ℕ)))
    simp only [norm_mul, Complex.norm_ofNat,
      show ‖σ ^ 3‖ = 1 by rw [norm_pow, hσ_norm]; ring, mul_one] at htri
    rw [show y ^ (4 : ℕ) - (1 : ℂ) - σ * (8 : ℂ) * q' - (24 : ℂ) * (q' ^ (2 : ℕ)) =
      (32 : ℂ) * σ ^ 3 * (q' ^ (3 : ℕ)) + (16 : ℂ) * (q' ^ (4 : ℕ)) by
      rcases hσ with rfl | rfl <;> simp [y] <;> ring]
    nlinarith [htri, norm_pow4_le_pow3 hq, hq3', norm_nonneg (q' ^ (3 : ℕ))]
  rw [hHj t ht0,
    show (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ) =
      (Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ) from (ofReal_exp_neg_pi_pow_eq t 2).symm]
  have htri := norm_add_le (x ^ (4 : ℕ) - y ^ (4 : ℕ))
    (y ^ (4 : ℕ) - (1 : ℂ) - σ * (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
      (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ)))
  rw [show x ^ (4 : ℕ) - y ^ (4 : ℕ) + (y ^ (4 : ℕ) - (1 : ℂ) -
    σ * (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
    (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ))) = x ^ (4 : ℕ) - (1 : ℂ) -
    σ * (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
    (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ)) by ring] at htri
  linarith [htri.trans (add_le_add hpow' hy4)]

/-- `H₃(it)` expansion up to the `exp(-2π t)` term on `t ≥ 1`. -/
lemma exists_bound_norm_H3_resToImagAxis_sub_two_terms_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖H₃.resToImagAxis t
          - (1 : ℂ)
          - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
          - (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(3 : ℝ) * Real.pi * t) := by
  obtain ⟨C1, hC1⟩ := exists_bound_norm_Theta3_resToImagAxis_sub_one_Ici_one
  obtain ⟨C2, hC2⟩ := exists_bound_norm_Theta3_resToImagAxis_sub_one_sub_two_exp_Ici_one
  obtain ⟨C, hC⟩ := exists_bound_H3_or_H4_aux (Hj := H₃.resToImagAxis) (Θj := Θ₃.resToImagAxis)
    (σ := 1) (Or.inl rfl)
    (fun t ht0 => by simp [H₃, Function.resToImagAxis, ResToImagAxis, ht0])
    (nonneg_of_norm_le_mul_exp (hC1 1 le_rfl)) (nonneg_of_norm_le_mul_exp (hC2 1 le_rfl)) hC1
    fun t ht => by simpa [sub_eq_add_neg, mul_assoc] using hC2 t ht
  exact ⟨C, fun t ht => by simpa [one_mul] using hC t ht⟩

/-- `H₄(it)` expansion up to the `exp(-2π t)` term on `t ≥ 1`. -/
public lemma exists_bound_norm_H4_resToImagAxis_sub_two_terms_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖H₄.resToImagAxis t
          - (1 : ℂ)
          + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
          - (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(3 : ℝ) * Real.pi * t) := by
  obtain ⟨C1, hC1⟩ := exists_bound_norm_Theta4_resToImagAxis_sub_one_Ici_one
  obtain ⟨C2, hC2⟩ := exists_bound_norm_Theta4_resToImagAxis_sub_one_add_two_exp_Ici_one
  obtain ⟨C, hC⟩ := exists_bound_H3_or_H4_aux (Hj := H₄.resToImagAxis) (Θj := Θ₄.resToImagAxis)
    (σ := -1) (Or.inr rfl)
    (fun t ht0 => by simp [H₄, Function.resToImagAxis, ResToImagAxis, ht0])
    (nonneg_of_norm_le_mul_exp (hC1 1 le_rfl)) (nonneg_of_norm_le_mul_exp (hC2 1 le_rfl)) hC1
    fun t ht => by
      simpa [sub_eq_add_neg, mul_assoc, neg_mul, neg_neg, add_assoc, add_left_comm, add_comm]
        using hC2 t ht
  exact ⟨C, fun t ht => by simpa [neg_mul, sub_eq_add_neg, neg_neg] using hC t ht⟩

/-- `H₃(it) + H₄(it)` cancellation up to the `exp(-2π t)` term on `t ≥ 1`. -/
public lemma exists_bound_norm_H3_add_H4_resToImagAxis_sub_two_sub_main_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖(H₃.resToImagAxis t + H₄.resToImagAxis t)
          - (2 : ℂ)
          - (48 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(3 : ℝ) * Real.pi * t) := by
  obtain ⟨C3, hC3⟩ := exists_bound_norm_H3_resToImagAxis_sub_two_terms_Ici_one
  obtain ⟨C4, hC4⟩ := exists_bound_norm_H4_resToImagAxis_sub_two_terms_Ici_one
  refine ⟨C3 + C4, fun t ht => ?_⟩
  have hcong := norm_add_le
    (H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
      (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
    (H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
      (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
  rw [show (H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
    (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)) +
    (H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
    (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)) =
    (H₃.resToImagAxis t + H₄.resToImagAxis t) - (2 : ℂ) -
    (48 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ) by ring] at hcong
  linarith [hC3 t ht, hC4 t ht]

/-- Crude inverse-square bound for `H₃(it)` on `t ≥ 1`. -/
public lemma exists_bound_norm_inv_H3_sq_sub_one_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖((H₃.resToImagAxis t) ^ (2 : ℕ))⁻¹ - (1 : ℂ)‖ ≤ C * Real.exp (-Real.pi * t) := by
  obtain ⟨C3, hC3⟩ := exists_bound_norm_H3_resToImagAxis_sub_two_terms_Ici_one
  let C0 : ℝ := C3 + 32
  have hC30 : 0 ≤ C3 := nonneg_of_norm_le_mul_exp (hC3 1 le_rfl)
  have hsub1 : ∀ t : ℝ, 1 ≤ t → ‖H₃.resToImagAxis t - (1 : ℂ)‖ ≤ C0 * Real.exp (-Real.pi * t) :=
    fun t ht => by
      have hq2_le : Real.exp (-(2 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])
      have hq3_le : Real.exp (-(3 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])
      have htri := norm_add_le ((8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ))
        ((24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
      have h1 : ‖(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖ = 8 * Real.exp (-Real.pi * t) := by
        simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
      have h2 : ‖(24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ =
          24 * Real.exp (-(2 : ℝ) * Real.pi * t) := by
        simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
      have htri' := norm_add_le
        (H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
          (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
        ((8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
          (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
      rw [show (H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
          (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)) +
          ((8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
          (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)) =
        H₃.resToImagAxis t - (1 : ℂ) by ring] at htri'
      nlinarith [htri, htri', h1, h2, mul_le_mul_of_nonneg_left hq3_le hC30, hC3 t ht, hq2_le]
  have hnorm_H3_ge_one : ∀ t : ℝ, 1 ≤ t → (1 : ℝ) ≤ ‖H₃.resToImagAxis t‖ := fun t ht => by
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    set τ : ℂ := (Complex.I : ℂ) * (t : ℂ)
    have hτ : 0 < τ.im := by simpa [τ] using ht0
    let f : ℕ → ℝ := fun n => Real.exp (-Real.pi * (((n : ℝ) + 1) ^ 2) * t)
    have hterm : ∀ n : ℕ, cexp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ) = (f n : ℂ) :=
      fun n => by
        have hexp : (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ : ℂ)
            = (-(Real.pi * (((n : ℝ) + 1) ^ 2) * t) : ℂ) := by
          rw [show (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ : ℂ)
              = (Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * ((Complex.I : ℂ) * τ) by ac_rfl,
            show τ = Complex.I * (t : ℂ) from rfl,
            show (Complex.I : ℂ) * ((Complex.I : ℂ) * (t : ℂ)) = -(t : ℂ) by
              rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]]
          push_cast; ring
        simp [f, hexp]
    have hFnonneg : 0 ≤ (∑' n : ℕ, f n) := tsum_nonneg (fun n => by positivity)
    have hnormΘ₃ : (1 : ℝ) ≤ ‖Θ₃.resToImagAxis t‖ := by
      rw [show Θ₃.resToImagAxis t = jacobiTheta τ by
        simp [Function.resToImagAxis, ResToImagAxis, ht0, Theta3_eq_jacobiTheta, τ],
        show jacobiTheta τ = ((1 + 2 * (∑' n : ℕ, f n) : ℝ) : ℂ) by
          rw [jacobiTheta_eq_tsum_nat (τ := τ) hτ, show
            (∑' n : ℕ, cexp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ))
              = (↑(∑' n : ℕ, f n) : ℂ) by simp [Complex.ofReal_tsum, hterm]]
          push_cast; ring,
        Complex.norm_of_nonneg (by positivity)]
      linarith [hFnonneg]
    simpa [show ‖ResToImagAxis H₃ t‖ = ‖ResToImagAxis Θ₃ t‖ ^ (4 : ℕ) by
      simp [H₃, ResToImagAxis, ht0, norm_pow]] using
      pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1) hnormΘ₃ 4
  refine ⟨C0 * (C0 + 2), fun t ht => ?_⟩
  set x : ℂ := H₃.resToImagAxis t
  have hxge : (1 : ℝ) ≤ ‖x‖ := hnorm_H3_ge_one t ht
  have hx_inv : ‖(x ^ (2 : ℕ))⁻¹‖ ≤ 1 := by
    simpa [norm_inv, norm_pow] using inv_le_one_of_one_le₀ (one_le_pow₀ hxge)
  have hxsub : ‖x - (1 : ℂ)‖ ≤ C0 * Real.exp (-Real.pi * t) := hsub1 t ht
  have hx_le : ‖x‖ + 1 ≤ C0 + 2 := by
    nlinarith [norm_le_one_add_of_sub_one x hxsub,
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, le_trans zero_le_one ht] :
        -Real.pi * t ≤ 0)]
  have hx2sub :
      ‖x ^ (2 : ℕ) - (1 : ℂ)‖ ≤ (C0 + 2) * (C0 * Real.exp (-Real.pi * t)) := by
    rw [show x ^ (2 : ℕ) - (1 : ℂ) = (x - 1) * (x + 1) by ring, norm_mul, mul_comm]
    gcongr
    exact ((by simpa using norm_add_le x (1 : ℂ)) : ‖x + 1‖ ≤ ‖x‖ + 1).trans hx_le
  have hx0 : x ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le zero_lt_one hxge)
  have hinv_le : ‖(x ^ (2 : ℕ))⁻¹ - (1 : ℂ)‖ ≤ ‖x ^ (2 : ℕ) - (1 : ℂ)‖ := by
    rw [show (x ^ (2 : ℕ))⁻¹ - (1 : ℂ) = ((1 : ℂ) - x ^ (2 : ℕ)) * (x ^ (2 : ℕ))⁻¹ by
      field_simp, norm_mul, norm_sub_rev]
    simpa using mul_le_mul_of_nonneg_left hx_inv (norm_nonneg (x ^ (2 : ℕ) - (1 : ℂ)))
  simpa [x, mul_assoc, mul_left_comm, mul_comm] using hinv_le.trans hx2sub

end

end MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis
