module
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Mul
public import SpherePacking.ModularForms.JacobiTheta
public import SpherePacking.ModularForms.ResToImagAxis
public import SpherePacking.MagicFunction.b.PsiBounds
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Topology.Order.Compact
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common


/-!
# Theta-function bounds on the imaginary axis (AnotherIntegral.B)

This file proves `q`-expansion bounds for the Jacobi theta functions along the imaginary axis,
specialized to the modular forms `Θ₂`, `Θ₃`, and `Θ₄`. These estimates feed into the bounds on
`H₂`, `H₃`, `H₄` used to extract the constant term `144` in the cancellation estimate for
`ψI'(it)`.

## Main statements
* `exists_bound_norm_Theta2_resToImagAxis_Ici_one`
* `exists_bound_norm_Theta2_resToImagAxis_sub_two_terms_Ici_one`
* `exists_bound_norm_Theta3_resToImagAxis_sub_one_Ici_one`
* `exists_bound_norm_Theta4_resToImagAxis_sub_one_Ici_one`
-/

namespace MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis

open scoped BigOperators UpperHalfPlane

open Real Complex Filter Topology
open Set

noncomputable section

/-- For `t > 0`, the norm of `exp (-π t)` in `ℂ` is at most `1`. -/
public lemma norm_exp_neg_pi_mul_le_one (t : ℝ) (ht : 0 < t) :
    ‖(Real.exp (-Real.pi * t) : ℂ)‖ ≤ 1 := by
  have : (-Real.pi * t) ≤ 0 := by nlinarith [Real.pi_pos, ht.le]
  simpa [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp] using (Real.exp_le_one_iff).2 this

lemma norm_Theta2_term_resToImagAxis (n : ℤ) (t : ℝ) (ht : 0 < t) :
    ‖Θ₂_term n ⟨(Complex.I : ℂ) * t, by simp [ht]⟩‖ =
      Real.exp (-Real.pi * (((n : ℝ) + (1 / 2)) ^ 2) * t) := by
  set τ : ℍ := ⟨(Complex.I : ℂ) * t, by simp [ht]⟩
  set r : ℝ := (n : ℝ) + (2⁻¹ : ℝ)
  have hr : (n + (2⁻¹ : ℂ) : ℂ) = (r : ℂ) := by
    refine Complex.ext ?_ ?_ <;> simp [r]
  have harg :
      (Real.pi * Complex.I * (n + (2⁻¹ : ℂ) : ℂ) ^ 2 * (τ : ℂ) : ℂ) =
        ((-(Real.pi * r ^ 2 * t) : ℝ) : ℂ) := by
    simp [τ, hr]; ring_nf; simp
  have : ‖Θ₂_term n τ‖ = Real.exp (-(Real.pi * r ^ 2 * t)) := by
    simp_rw [Θ₂_term, div_eq_mul_inv, one_mul]
    rw [harg]
    exact Complex.norm_exp_ofReal (-(Real.pi * r ^ 2 * t))
  simpa [τ, r] using this

/-- Rewrite `Θ₃` in terms of the one-variable Jacobi theta function `jacobiTheta`. -/
public lemma Theta3_eq_jacobiTheta (τ : ℍ) : Θ₃ τ = jacobiTheta (τ : ℂ) := by
  simp [Θ₃, Θ₃_term, jacobiTheta]

lemma exp_pi_I_mul_sq_int (n : ℤ) :
    Complex.exp (Real.pi * Complex.I * (n : ℂ) ^ 2) = (-1 : ℂ) ^ n := by
  have hEven : Even (n ^ 2 : ℤ) ↔ Even n := by
    simpa using (Int.even_pow' (m := n) (n := 2) (by simp : (2 : ℕ) ≠ 0))
  have hsq : (-1 : ℂ) ^ (n ^ 2 : ℤ) = (-1 : ℂ) ^ n := by simp [neg_one_zpow_eq_ite, hEven]
  have harg : (Real.pi * Complex.I * (n : ℂ) ^ 2 : ℂ) = (n ^ 2 : ℤ) * (Real.pi * Complex.I) := by
    push_cast; ring
  rw [harg, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  simpa using hsq

lemma Theta4_eq_jacobiTheta_add_one (τ : ℍ) : Θ₄ τ = jacobiTheta ((τ : ℂ) + 1) := by
  unfold Θ₄ jacobiTheta
  refine tsum_congr fun n => ?_
  have hadd :
      (Real.pi * Complex.I * (n : ℂ) ^ 2 * ((τ : ℂ) + 1) : ℂ) =
        (Real.pi * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ)) + (Real.pi * Complex.I * (n : ℂ) ^ 2) := by
    simp [mul_add, mul_assoc]
  calc
    Θ₄_term n τ
        = (-1 : ℂ) ^ n * Complex.exp (Real.pi * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ)) := by
            simp [Θ₄_term]
    _ = Complex.exp (Real.pi * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ)) *
          Complex.exp (Real.pi * Complex.I * (n : ℂ) ^ 2) := by
          simp [mul_assoc, mul_comm, (exp_pi_I_mul_sq_int n).symm]
    _ = Complex.exp (Real.pi * Complex.I * (n : ℂ) ^ 2 * ((τ : ℂ) + 1)) := by
          simpa [hadd] using
            (Complex.exp_add (Real.pi * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ))
              (Real.pi * Complex.I * (n : ℂ) ^ 2)).symm

/-- Uniform bound for `Θ₂` on `t ≥ 1` along the imaginary axis. -/
public lemma exists_bound_norm_Theta2_resToImagAxis_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖Θ₂.resToImagAxis t‖ ≤ C := by
  let majorant : ℤ → ℝ :=
    fun n ↦ Real.exp (-Real.pi / 4) *
      Real.exp (-Real.pi * ((1 : ℝ) * (n ^ 2) - 2 * (1 / 2 : ℝ) * |n|))
  have hmajorant : Summable majorant := by
    simpa [majorant, pow_zero, one_mul] using
      (summable_pow_mul_jacobiTheta₂_term_bound (S := (1 / 2 : ℝ)) (T := (1 : ℝ))
        (by positivity) 0).mul_left (Real.exp (-Real.pi / 4))
  refine ⟨∑' n : ℤ, majorant n, ?_⟩
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set τ : ℍ := ⟨Complex.I * t, by simp [htpos]⟩
  have hterm : ∀ n : ℤ, ‖Θ₂_term n τ‖ ≤ majorant n := by
    intro n
    -- Rewrite the term using the two-variable theta summand.
    have hterm' :
        Θ₂_term n τ =
          Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4) *
            jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ) := by
      simp [Θ₂_term_as_jacobiTheta₂_term]
    -- Bound the two factors separately.
    have hpref :
        ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)‖ ≤ Real.exp (-Real.pi / 4) := by
      have hpref' :
          ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)‖ = Real.exp (-Real.pi * t / 4) := by
        simp [Complex.norm_exp, τ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      rw [hpref']
      have hle : (-Real.pi * t / 4) ≤ (-Real.pi / 4) := by
        nlinarith [Real.pi_pos, ht]
      exact Real.exp_le_exp.mpr hle
    have habs_le_sq : (|n| : ℤ) ≤ n ^ 2 := by
      simpa [Int.natCast_natAbs] using (Int.natAbs_le_self_sq n)
    have hcore :
        ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ ≤
          Real.exp (-Real.pi * ((1 : ℝ) * (n ^ 2) - 2 * (1 / 2 : ℝ) * |n|)) := by
      -- Evaluate the norm exactly, then compare exponents.
      have hn :
          ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ =
            Real.exp (-Real.pi * (t * ((n ^ 2 : ℤ) : ℝ) + t * (n : ℝ))) := by
        -- Use the closed-form expression for the norm and normalize the resulting exponent.
        simp [norm_jacobiTheta₂_term, τ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        ring_nf
      rw [hn]
      have hdiff_nonneg : 0 ≤ ((n ^ 2 : ℤ) : ℝ) - (|n| : ℝ) := by
        have : (|n| : ℝ) ≤ ((n ^ 2 : ℤ) : ℝ) := by exact_mod_cast habs_le_sq
        linarith
      have hn_ge : (-(|n| : ℝ)) ≤ (n : ℝ) := by
        exact_mod_cast (neg_abs_le n)
      have hbase :
          t * (((n ^ 2 : ℤ) : ℝ) + (n : ℝ)) ≥ ((n ^ 2 : ℤ) : ℝ) - (|n| : ℝ) := by
        calc
          t * (((n ^ 2 : ℤ) : ℝ) + (n : ℝ)) ≥ t * (((n ^ 2 : ℤ) : ℝ) - (|n| : ℝ)) := by
            nlinarith [hn_ge, htpos.le]
          _ ≥ (1 : ℝ) * (((n ^ 2 : ℤ) : ℝ) - (|n| : ℝ)) := by
            nlinarith [ht, hdiff_nonneg]
          _ = ((n ^ 2 : ℤ) : ℝ) - (|n| : ℝ) := by simp
      have hexp :
          -Real.pi * (t * (((n ^ 2 : ℤ) : ℝ) + (n : ℝ))) ≤
            -Real.pi * (((n ^ 2 : ℤ) : ℝ) - (|n| : ℝ)) := by
        nlinarith [hbase, Real.pi_pos]
      simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using
        (Real.exp_le_exp.mpr hexp)
    simpa [hterm', majorant, mul_assoc] using mul_le_mul hpref hcore (by positivity) (by positivity)
  have htsum :
      ‖∑' n : ℤ, Θ₂_term n τ‖ ≤ ∑' n : ℤ, majorant n :=
    tsum_of_norm_bounded hmajorant.hasSum hterm
  simpa [Function.resToImagAxis, ResToImagAxis, htpos, Θ₂, τ] using htsum

private lemma two_div_one_sub_exp_pi_mul_le (t : ℝ) (ht : 1 ≤ t) :
    2 / (1 - Real.exp (-Real.pi * t)) ≤ 2 / (1 - Real.exp (-Real.pi)) := by
  have hden_pos : 0 < (1 - Real.exp (-Real.pi)) := by
    refine sub_pos.2 ?_
    simpa [Real.exp_lt_one_iff] using (by nlinarith [Real.pi_pos] : (-Real.pi : ℝ) < 0)
  have hInv :
      (1 / (1 - Real.exp (-Real.pi * t))) ≤ (1 / (1 - Real.exp (-Real.pi))) := by
    refine one_div_le_one_div_of_le hden_pos ?_
    have : Real.exp (-Real.pi * t) ≤ Real.exp (-Real.pi) := by
      exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, ht])
    linarith
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (mul_le_mul_of_nonneg_left hInv (by norm_num : (0 : ℝ) ≤ 2))

private lemma norm_jacobiTheta_I_mul_add_real_sub_one_le (a : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    ‖jacobiTheta (((Complex.I : ℂ) * (t : ℂ)) + a) - 1‖ ≤
      (2 / (1 - Real.exp (-Real.pi))) * Real.exp (-Real.pi * t) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hbound :
      ‖jacobiTheta (((Complex.I : ℂ) * (t : ℂ)) + a) - 1‖ ≤
        (2 / (1 - Real.exp (-Real.pi * t))) * Real.exp (-Real.pi * t) := by
    simpa using
      (norm_jacobiTheta_sub_one_le (τ := ((Complex.I : ℂ) * (t : ℂ)) + a) (by simpa using htpos))
  exact hbound.trans <|
    mul_le_mul_of_nonneg_right (two_div_one_sub_exp_pi_mul_le t ht) (by positivity)

private lemma exp_neg_pi_mul_sq_add_two_mul_le_geom (t : ℝ) (ht : 1 ≤ t) (n : ℕ) :
    Real.exp (-Real.pi * (((n : ℝ) + 2) ^ 2 * t)) ≤
      Real.exp (-(4 : ℝ) * Real.pi * t) * (Real.exp (-Real.pi) ^ n) := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have h4t1 : 0 ≤ (4 : ℝ) * t - 1 := by nlinarith [ht]
  have hdiff :
      0 ≤ (((n : ℝ) + 2) ^ 2 * t) - ((4 : ℝ) * t + (n : ℝ)) := by
    have : (((n : ℝ) + 2) ^ 2 * t) - ((4 : ℝ) * t + (n : ℝ)) =
        t * (n : ℝ) ^ 2 + (((4 : ℝ) * t - 1) * (n : ℝ)) := by ring
    rw [this]
    exact add_nonneg (mul_nonneg ht0 (sq_nonneg (n : ℝ))) (mul_nonneg h4t1 (by positivity))
  have hbase : (4 : ℝ) * t + (n : ℝ) ≤ ((n : ℝ) + 2) ^ 2 * t := by linarith
  have hpi : (-Real.pi : ℝ) ≤ 0 := by nlinarith [Real.pi_pos]
  have hexpArg :
      (-Real.pi) * (((n : ℝ) + 2) ^ 2 * t) ≤ (-Real.pi) * ((4 : ℝ) * t + (n : ℝ)) :=
    mul_le_mul_of_nonpos_left hbase hpi
  have hexp := Real.exp_le_exp.mpr hexpArg
  have hrpow : Real.exp (-Real.pi) ^ n = Real.exp ((n : ℝ) * (-Real.pi)) := by
    simpa [mul_comm] using (Real.exp_nat_mul (-Real.pi) n).symm
  have hrhs :
      Real.exp ((-Real.pi) * ((4 : ℝ) * t + (n : ℝ))) =
        Real.exp (-(4 : ℝ) * Real.pi * t) * (Real.exp (-Real.pi) ^ n) := by
    calc
      Real.exp ((-Real.pi) * ((4 : ℝ) * t + (n : ℝ)))
          = Real.exp ((-(4 : ℝ) * Real.pi * t) + ((n : ℝ) * (-Real.pi))) := by
              congr 1; ring
      _ = Real.exp (-(4 : ℝ) * Real.pi * t) * Real.exp ((n : ℝ) * (-Real.pi)) := by
              simp [Real.exp_add]
      _ = Real.exp (-(4 : ℝ) * Real.pi * t) * (Real.exp (-Real.pi) ^ n) := by
              simp [hrpow]
  simpa [mul_assoc] using (hexp.trans_eq hrhs)

/-- Exponential bound for `Θ₃(it) - 1` on `t ≥ 1`. -/
public lemma exists_bound_norm_Theta3_resToImagAxis_sub_one_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖Θ₃.resToImagAxis t - 1‖ ≤ C * Real.exp (-Real.pi * t) := by
  refine ⟨2 / (1 - Real.exp (-Real.pi)), fun t ht => ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  simpa [Function.resToImagAxis, ResToImagAxis, htpos, Theta3_eq_jacobiTheta] using
    (norm_jacobiTheta_I_mul_add_real_sub_one_le (a := (0 : ℝ)) (t := t) ht)

/-- Exponential bound for `Θ₄(it) - 1` on `t ≥ 1`. -/
public lemma exists_bound_norm_Theta4_resToImagAxis_sub_one_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖Θ₄.resToImagAxis t - 1‖ ≤ C * Real.exp (-Real.pi * t) := by
  refine ⟨2 / (1 - Real.exp (-Real.pi)), fun t ht => ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  simpa [Function.resToImagAxis, ResToImagAxis, htpos, Theta4_eq_jacobiTheta_add_one] using
    (norm_jacobiTheta_I_mul_add_real_sub_one_le (a := (1 : ℝ)) (t := t) ht)


/-- Isolate the first two terms of `Θ₂(it)` for `t ≥ 1`. -/
public lemma exists_bound_norm_Theta2_resToImagAxis_sub_two_terms_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖Θ₂.resToImagAxis t
          - (2 : ℂ) * (Real.exp (-Real.pi * t / 4) : ℂ)
          - (2 : ℂ) * (Real.exp (-(9 / 4 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(25 / 4 : ℝ) * Real.pi * t) := by
  refine ⟨2 / (1 - Real.exp (-Real.pi)), ?_⟩
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set τ : ℍ := ⟨Complex.I * t, by simp [htpos]⟩
  set f : ℕ → ℂ := fun n ↦ Θ₂_term (n : ℤ) τ
  have hsumZ : Summable (fun n : ℤ ↦ Θ₂_term n τ) := by
    have hs : Summable (fun n : ℤ ↦ jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)) :=
      (summable_jacobiTheta₂_term_iff (z := (τ : ℂ) / 2) (τ := (τ : ℂ))).2
        (by simpa using τ.im_pos)
    have h' :
        (fun n : ℤ ↦ Θ₂_term n τ) =
          fun n : ℤ ↦ Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4) *
            jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ) := by
      funext n
      simp [Θ₂_term_as_jacobiTheta₂_term, mul_assoc]
    simpa [h'] using (hs.mul_left (Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)))
  have hsymmZ : ∀ n : ℤ, Θ₂_term (-n - 1) τ = Θ₂_term n τ := by
    intro n
    unfold Θ₂_term
    -- It suffices to show that the exponents coincide.
    refine congrArg Complex.exp ?_
    simp [one_div, pow_two, sub_eq_add_neg, add_assoc, mul_assoc, mul_comm]
    ring
  have hTheta2_nat :
      Θ₂.resToImagAxis t = (2 : ℂ) * ∑' n : ℕ, f n := by
    have hres : Θ₂.resToImagAxis t = Θ₂ τ := by
      simp [Function.resToImagAxis, ResToImagAxis, htpos, τ]
    rw [hres, Θ₂]
    have hpair :
        (∑' n : ℤ, Θ₂_term n τ) =
          ∑' n : ℕ, (Θ₂_term (n : ℤ) τ + Θ₂_term (-(n + 1 : ℤ)) τ) :=
      (tsum_nat_add_neg_add_one (f := fun n : ℤ ↦ Θ₂_term n τ) hsumZ).symm
    have hsymm : ∀ n : ℕ, Θ₂_term (-(n + 1 : ℤ)) τ = Θ₂_term (n : ℤ) τ := by
      intro n
      have : (-(n + 1 : ℤ)) = -(n : ℤ) - 1 := by ring
      simpa [this, sub_eq_add_neg, add_assoc] using hsymmZ (n := (n : ℤ))
    rw [hpair]
    calc
      (∑' n : ℕ, (Θ₂_term (n : ℤ) τ + Θ₂_term (-(n + 1 : ℤ)) τ))
          = ∑' n : ℕ, (f n + f n) := by
              refine tsum_congr ?_
              intro n
              have hidx : (-(n + 1 : ℤ)) = -(n : ℤ) - 1 := by ring
              have hz : Θ₂_term (- (n : ℤ) + (-1 : ℤ)) τ = Θ₂_term (n : ℤ) τ := by
                have : (- (n : ℤ) + (-1 : ℤ)) = -(n : ℤ) - 1 := by ring
                simpa [this] using hsymmZ (n := (n : ℤ))
              simp [f, hidx, hz, sub_eq_add_neg]
      _ = ∑' n : ℕ, (2 : ℂ) * f n := by
            refine tsum_congr ?_
            intro n
            exact (two_mul (f n)).symm
      _ = (2 : ℂ) * ∑' n : ℕ, f n := by
            simp [tsum_mul_left]
  have hf : Summable f := hsumZ.comp_injective Nat.cast_injective
  have hshift :
      (∑' n : ℕ, f n) - (f 0 + f 1) = ∑' n : ℕ, f (n + 2) := by
    refine (sub_eq_iff_eq_add).2 ?_
    have h := (Summable.sum_add_tsum_nat_add (k := 2) hf)
    simpa [Finset.range_add_one, add_comm, add_left_comm, add_assoc] using h.symm
  have hf0 : f 0 = (Real.exp (-Real.pi * t / 4) : ℂ) := by
    -- Rewrite the RHS as a complex exponential of a real number, then compare exponents.
    unfold f
    unfold Θ₂_term
    rw [Complex.ofReal_exp (-Real.pi * t / 4)]
    apply congrArg Complex.exp
    simp [τ, pow_two, div_eq_mul_inv, mul_assoc, mul_comm]
    ring_nf
    simp [div_eq_mul_inv, mul_assoc, mul_comm]
  have hf1 : f 1 = (Real.exp (-(9 / 4 : ℝ) * Real.pi * t) : ℂ) := by
    unfold f
    unfold Θ₂_term
    rw [Complex.ofReal_exp (-(9 / 4 : ℝ) * Real.pi * t)]
    apply congrArg Complex.exp
    simp [τ, pow_two, div_eq_mul_inv, mul_assoc, mul_comm]
    ring_nf
    simp [div_eq_mul_inv, mul_assoc, mul_comm]
  have hrew :
      Θ₂.resToImagAxis t
          - (2 : ℂ) * (Real.exp (-Real.pi * t / 4) : ℂ)
          - (2 : ℂ) * (Real.exp (-(9 / 4 : ℝ) * Real.pi * t) : ℂ)
        = (2 : ℂ) * ∑' n : ℕ, f (n + 2) := by
    have htail : (∑' n : ℕ, f n) - f 0 - f 1 = ∑' n : ℕ, f (n + 2) := by
      calc
        (∑' n : ℕ, f n) - f 0 - f 1 = (∑' n : ℕ, f n) - (f 0 + f 1) := by abel
        _ = ∑' n : ℕ, f (n + 2) := hshift
    have htail' :
        (2 : ℂ) * ((∑' n : ℕ, f n) - f 0 - f 1) = (2 : ℂ) * ∑' n : ℕ, f (n + 2) := by
      exact congrArg (fun x : ℂ => (2 : ℂ) * x) htail
    have hfac :
        Θ₂.resToImagAxis t
            - (2 : ℂ) * (Real.exp (-Real.pi * t / 4) : ℂ)
            - (2 : ℂ) * (Real.exp (-(9 / 4 : ℝ) * Real.pi * t) : ℂ)
          =
          (2 : ℂ) * ((∑' n : ℕ, f n) - f 0 - f 1) := by
      rw [← hf0, ← hf1]
      rw [hTheta2_nat]
      ring_nf
    exact hfac.trans htail'
  set r : ℝ := Real.exp (-Real.pi)
  have hr : r < 1 := by
    simpa [r, Real.exp_lt_one_iff] using (by nlinarith [Real.pi_pos] : (-Real.pi : ℝ) < 0)
  have hgeom : HasSum (fun n : ℕ ↦ r ^ n) ((1 - r)⁻¹) :=
    hasSum_geometric_of_lt_one (Real.exp_pos _).le hr
  have hterm :
      ∀ n : ℕ, ‖f (n + 2)‖ ≤ Real.exp (-(25 / 4 : ℝ) * Real.pi * t) * (r ^ n) := by
    intro n
    -- Compute the norm exactly (the exponent is real on the imaginary axis).
    have hnorm :
        ‖f (n + 2)‖ = Real.exp (-Real.pi * (((n : ℝ) + (5 / 2 : ℝ)) ^ 2) * t) := by
      have h0 :
          ‖f (n + 2)‖ =
            Real.exp (-Real.pi * ((↑n + 2 + (2 : ℝ)⁻¹) ^ 2) * t) := by
        simpa [f, τ, Nat.cast_add, add_assoc, add_left_comm, add_comm] using
          (norm_Theta2_term_resToImagAxis (n := (n + 2 : ℕ)) (t := t) htpos)
      have hlin : (↑n + 2 + (2 : ℝ)⁻¹) = (n : ℝ) + (5 / 2 : ℝ) := by
        have hinv : (2 : ℝ)⁻¹ = (1 / 2 : ℝ) := by norm_num
        nlinarith [hinv]
      simpa [hlin] using h0
    rw [hnorm]
    have hbase : ((n : ℝ) + (5 / 2 : ℝ)) ^ 2 * t ≥ (25 / 4 : ℝ) * t + n := by
      have hn : 0 ≤ (n : ℝ) := by positivity
      have ht0 : 0 ≤ t := le_trans (show (0 : ℝ) ≤ 1 by norm_num) ht
      have hn_le : (n : ℝ) ≤ (n : ℝ) * t := by
        simpa [mul_one] using (mul_le_mul_of_nonneg_left ht hn)
      have hsq_ge : ((n : ℝ) + (5 / 2 : ℝ)) ^ 2 ≥ (25 / 4 : ℝ) + n := by
        nlinarith [hn]
      have hmul :
          ((25 / 4 : ℝ) + n) * t ≤ ((n : ℝ) + (5 / 2 : ℝ)) ^ 2 * t :=
        mul_le_mul_of_nonneg_right hsq_ge ht0
      calc
        (25 / 4 : ℝ) * t + n ≤ (25 / 4 : ℝ) * t + (n : ℝ) * t := by
          have h := add_le_add_right hn_le ((25 / 4 : ℝ) * t)
          simpa [add_assoc, add_left_comm, add_comm] using h
        _ = ((25 / 4 : ℝ) + n) * t := by ring
        _ ≤ ((n : ℝ) + (5 / 2 : ℝ)) ^ 2 * t := hmul
    have hexp :
        Real.exp (-Real.pi * (((n : ℝ) + (5 / 2 : ℝ)) ^ 2) * t) ≤
          Real.exp (-(25 / 4 : ℝ) * Real.pi * t + n * (-Real.pi)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hbase, Real.pi_pos]
    have hrpow : r ^ n = Real.exp (n * (-Real.pi)) := by
      simpa [r] using (Real.exp_nat_mul (-Real.pi) n).symm
    calc
      Real.exp (-Real.pi * (((n : ℝ) + (5 / 2 : ℝ)) ^ 2) * t)
          ≤ Real.exp (-(25 / 4 : ℝ) * Real.pi * t + n * (-Real.pi)) := hexp
      _ = Real.exp (-(25 / 4 : ℝ) * Real.pi * t) * Real.exp (n * (-Real.pi)) := by
            exact Real.exp_add (-(25 / 4 : ℝ) * Real.pi * t) (n * (-Real.pi))
      _ = Real.exp (-(25 / 4 : ℝ) * Real.pi * t) * (r ^ n) := by simp [hrpow]
  have hu : HasSum (fun n : ℕ ↦ Real.exp (-(25 / 4 : ℝ) * Real.pi * t) * (r ^ n))
      (Real.exp (-(25 / 4 : ℝ) * Real.pi * t) * ((1 - r)⁻¹)) :=
    hgeom.mul_left (Real.exp (-(25 / 4 : ℝ) * Real.pi * t))
  have hsumMajor : Summable (fun n : ℕ ↦ Real.exp (-(25 / 4 : ℝ) * Real.pi * t) * (r ^ n)) :=
    hu.summable
  have hsumNorm : Summable (fun n : ℕ ↦ ‖f (n + 2)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm hsumMajor
  have htail :
      ‖∑' n : ℕ, f (n + 2)‖ ≤ Real.exp (-(25 / 4 : ℝ) * Real.pi * t) * ((1 - r)⁻¹) := by
    have h0 := norm_tsum_le_tsum_norm hsumNorm
    refine h0.trans ?_
    have hmono := hsumNorm.tsum_mono hsumMajor (by
      intro n; exact hterm n)
    have hsum :
        (∑' n : ℕ, Real.exp (-(25 / 4 : ℝ) * Real.pi * t) * (r ^ n)) =
          Real.exp (-(25 / 4 : ℝ) * Real.pi * t) * ((1 - r)⁻¹) := by
      simpa using hu.tsum_eq
    exact hmono.trans (le_of_eq hsum)
  rw [hrew]
  calc
    ‖(2 : ℂ) * ∑' n : ℕ, f (n + 2)‖ = (2 : ℝ) * ‖∑' n : ℕ, f (n + 2)‖ := by
      simp
    _ ≤ (2 : ℝ) * (Real.exp (-(25 / 4 : ℝ) * Real.pi * t) * ((1 - r)⁻¹)) := by
      gcongr
    _ = (2 / (1 - r)) * Real.exp (-(25 / 4 : ℝ) * Real.pi * t) := by
      simp [div_eq_mul_inv, mul_assoc, mul_comm]
/-- Isolate the `n = ±1` contribution to `Θ₃(it)` for `t ≥ 1`. -/
public lemma exists_bound_norm_Theta3_resToImagAxis_sub_one_sub_two_exp_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖Θ₃.resToImagAxis t - (1 : ℂ) - (2 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(4 : ℝ) * Real.pi * t) := by
  refine ⟨2 / (1 - Real.exp (-Real.pi)), ?_⟩
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set τ : ℂ := (Complex.I : ℂ) * t
  have hτ : 0 < τ.im := by simpa [τ] using htpos
  have hΘ₃ : Θ₃.resToImagAxis t = jacobiTheta τ := by
    simp [Function.resToImagAxis, ResToImagAxis, htpos, τ, Theta3_eq_jacobiTheta]
  set a : ℕ → ℂ := fun n ↦ Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ)
  have ha : Summable a := (hasSum_nat_jacobiTheta (τ := τ) hτ).summable
  have hjac : jacobiTheta τ = (1 : ℂ) + (2 : ℂ) * ∑' n : ℕ, a n := by
    simpa [a] using (jacobiTheta_eq_tsum_nat (τ := τ) hτ)
  have ha0 : a 0 = (Real.exp (-Real.pi * t) : ℂ) := by
    have hI_mul (z : ℂ) : (Complex.I : ℂ) * ((Complex.I : ℂ) * z) = -z := I_mul_I_mul z
    have : a 0 = Complex.exp ((-Real.pi * t : ℝ) : ℂ) := by
      simp [a, τ, pow_two, mul_assoc, mul_left_comm, mul_comm, hI_mul]
    simpa [Complex.ofReal_exp] using this
  have hshift : (∑' n : ℕ, a n) - a 0 = ∑' n : ℕ, a (n + 1) := by
    refine (sub_eq_iff_eq_add).2 ?_
    simpa [Finset.range_one, add_comm, add_left_comm, add_assoc] using
      (ha.sum_add_tsum_nat_add 1).symm
  set r : ℝ := Real.exp (-Real.pi)
  have hr : r < 1 := by
    simpa [r, Real.exp_lt_one_iff] using (by nlinarith [Real.pi_pos] : (-Real.pi : ℝ) < 0)
  have hgeom : HasSum (fun n : ℕ ↦ r ^ n) ((1 - r)⁻¹) :=
    hasSum_geometric_of_lt_one (Real.exp_pos _).le hr
  let b : ℕ → ℝ := fun n ↦ Real.exp (-(4 : ℝ) * Real.pi * t) * (r ^ n)
  have hb_summable : Summable b := (hgeom.summable.mul_left (Real.exp (-(4 : ℝ) * Real.pi * t)))
  have hterm : ∀ n : ℕ, ‖a (n + 1)‖ ≤ b n := by
    intro n
    have hnorm : ‖a (n + 1)‖ = Real.exp (-Real.pi * (((n : ℝ) + 2) ^ 2 * t)) := by
      have ha_eq : a (n + 1) = jacobiTheta₂_term (n + 2 : ℤ) (0 : ℂ) τ := by
        simp [a, jacobiTheta₂_term, mul_assoc, mul_left_comm, mul_comm, add_left_comm,
          add_comm, pow_two, one_add_one_eq_two]
      have hnorm0 :
          ‖jacobiTheta₂_term (n + 2 : ℤ) (0 : ℂ) τ‖ =
            Real.exp
              (-Real.pi * ((n + 2 : ℤ) : ℝ) ^ 2 * τ.im
                - 2 * Real.pi * ((n + 2 : ℤ) : ℝ) * (0 : ℂ).im) := by
        simpa using (norm_jacobiTheta₂_term (n + 2 : ℤ) (0 : ℂ) τ)
      have hcast : ((n + 2 : ℤ) : ℝ) = (n : ℝ) + 2 := by norm_cast
      calc
        ‖a (n + 1)‖ = ‖jacobiTheta₂_term (n + 2 : ℤ) (0 : ℂ) τ‖ := by simp [ha_eq]
        _ = Real.exp (-Real.pi * ((n + 2 : ℤ) : ℝ) ^ 2 * τ.im) := by
              simp [hnorm0]
        _ = Real.exp (-Real.pi * (((n + 2 : ℤ) : ℝ) ^ 2 * t)) := by
              simp [τ, mul_assoc]
        _ = Real.exp (-Real.pi * (((n : ℝ) + 2) ^ 2 * t)) := by
              simp [hcast]
    rw [hnorm]
    simpa [b, r, pow_two] using exp_neg_pi_mul_sq_add_two_mul_le_geom t ht n
  have hsumNorm : Summable (fun n : ℕ ↦ ‖a (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm hb_summable
  have htail :
      ‖∑' n : ℕ, a (n + 1)‖ ≤ Real.exp (-(4 : ℝ) * Real.pi * t) * ((1 - r)⁻¹) := by
    have h0 := norm_tsum_le_tsum_norm hsumNorm
    refine h0.trans ?_
    have hmono :
        (∑' n : ℕ, ‖a (n + 1)‖) ≤ ∑' n : ℕ, b n :=
      hsumNorm.tsum_le_tsum (fun n => hterm n) hb_summable
    have hbsum : (∑' n : ℕ, b n) = Real.exp (-(4 : ℝ) * Real.pi * t) * ((1 - r)⁻¹) := by
      simpa [b] using (hgeom.mul_left (Real.exp (-(4 : ℝ) * Real.pi * t))).tsum_eq
    exact hmono.trans (le_of_eq hbsum)
  have hΘ₃' : Θ₃.resToImagAxis t = (1 : ℂ) + (2 : ℂ) * ∑' n : ℕ, a n := by
    calc
      Θ₃.resToImagAxis t = jacobiTheta τ := hΘ₃
      _ = (1 : ℂ) + (2 : ℂ) * ∑' n : ℕ, a n := hjac
  have hrew :
      Θ₃.resToImagAxis t - (1 : ℂ) - (2 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) =
        (2 : ℂ) * ((∑' n : ℕ, a n) - a 0) := by
    rw [hΘ₃']
    rw [← ha0]
    ring
  calc
    ‖Θ₃.resToImagAxis t - (1 : ℂ) - (2 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖
        = ‖(2 : ℂ) * ((∑' n : ℕ, a n) - a 0)‖ := by
          simpa [-Complex.ofReal_exp] using congrArg norm hrew
    _ = (2 : ℝ) * ‖(∑' n : ℕ, a n) - a 0‖ := by simp
    _ = (2 : ℝ) * ‖∑' n : ℕ, a (n + 1)‖ := by simp [hshift]
    _ ≤ (2 : ℝ) * (Real.exp (-(4 : ℝ) * Real.pi * t) * ((1 - r)⁻¹)) := by
          gcongr
    _ = (2 / (1 - Real.exp (-Real.pi))) * Real.exp (-(4 : ℝ) * Real.pi * t) := by
          have : (2 : ℝ) * (Real.exp (-(4 : ℝ) * Real.pi * t) * ((1 - r)⁻¹)) =
              (2 / (1 - r)) * Real.exp (-(4 : ℝ) * Real.pi * t) := by
            simp [div_eq_mul_inv, mul_assoc, mul_comm]
          simpa [r, this]

/-- Isolate the `n = ±1` contribution to `Θ₄(it)` for `t ≥ 1`. -/
public lemma exists_bound_norm_Theta4_resToImagAxis_sub_one_add_two_exp_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖Θ₄.resToImagAxis t - (1 : ℂ) + (2 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(4 : ℝ) * Real.pi * t) := by
  refine ⟨2 / (1 - Real.exp (-Real.pi)), ?_⟩
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set τ : ℂ := (Complex.I : ℂ) * t + 1
  have hτ : 0 < τ.im := by simpa [τ] using htpos
  have hΘ₄ : Θ₄.resToImagAxis t = jacobiTheta τ := by
    simp [Function.resToImagAxis, ResToImagAxis, htpos, τ, Theta4_eq_jacobiTheta_add_one]
  set a : ℕ → ℂ := fun n ↦ Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ)
  have ha : Summable a := (hasSum_nat_jacobiTheta (τ := τ) hτ).summable
  have hjac : jacobiTheta τ = (1 : ℂ) + (2 : ℂ) * ∑' n : ℕ, a n := by
    simpa [a] using (jacobiTheta_eq_tsum_nat (τ := τ) hτ)
  have ha0 : a 0 = - (Real.exp (-Real.pi * t) : ℂ) := by
    have hI_mul (z : ℂ) : (Complex.I : ℂ) * ((Complex.I : ℂ) * z) = -z := I_mul_I_mul z
    have hIIt : (Real.pi * Complex.I * ((Complex.I : ℂ) * t) : ℂ) = ((-Real.pi * t : ℝ) : ℂ) := by
      calc
        (Real.pi * Complex.I * ((Complex.I : ℂ) * t) : ℂ)
            = (Real.pi : ℂ) * ((Complex.I : ℂ) * ((Complex.I : ℂ) * t)) := by
                simp [mul_assoc]
        _ = (Real.pi : ℂ) * (-(t : ℂ)) := by simp [hI_mul]
        _ = (-Real.pi : ℂ) * (t : ℂ) := by ring
        _ = ((-Real.pi * t : ℝ) : ℂ) := by simp
    calc
      a 0 = Complex.exp (Real.pi * Complex.I * τ) := by
        simp [a, pow_two, mul_assoc, mul_left_comm, mul_comm]
      _ = Complex.exp (Real.pi * Complex.I * ((Complex.I : ℂ) * t) + Real.pi * Complex.I) := by
        simp [τ, mul_add, mul_assoc]
      _ =
          Complex.exp (Real.pi * Complex.I * ((Complex.I : ℂ) * t))
            * Complex.exp (Real.pi * Complex.I) := by
        exact
          Complex.exp_add (Real.pi * Complex.I * ((Complex.I : ℂ) * t)) (Real.pi * Complex.I)
      _ = Complex.exp ((-Real.pi * t : ℝ) : ℂ) * (-1 : ℂ) := by
        rw [hIIt]
        simp [Complex.exp_pi_mul_I]
      _ = - (Real.exp (-Real.pi * t) : ℂ) := by
        simp
  have hshift : (∑' n : ℕ, a n) - a 0 = ∑' n : ℕ, a (n + 1) := by
    refine (sub_eq_iff_eq_add).2 ?_
    simpa [Finset.range_one, add_comm, add_left_comm, add_assoc] using
      (ha.sum_add_tsum_nat_add 1).symm
  set r : ℝ := Real.exp (-Real.pi)
  have hr : r < 1 := by
    simpa [r, Real.exp_lt_one_iff] using (by nlinarith [Real.pi_pos] : (-Real.pi : ℝ) < 0)
  have hgeom : HasSum (fun n : ℕ ↦ r ^ n) ((1 - r)⁻¹) :=
    hasSum_geometric_of_lt_one (Real.exp_pos _).le hr
  let b : ℕ → ℝ := fun n ↦ Real.exp (-(4 : ℝ) * Real.pi * t) * (r ^ n)
  have hb_summable : Summable b := (hgeom.summable.mul_left (Real.exp (-(4 : ℝ) * Real.pi * t)))
  have hterm : ∀ n : ℕ, ‖a (n + 1)‖ ≤ b n := by
    intro n
    have hnorm : ‖a (n + 1)‖ = Real.exp (-Real.pi * (((n : ℝ) + 2) ^ 2 * t)) := by
      have ha_eq : a (n + 1) = jacobiTheta₂_term (n + 2 : ℤ) (0 : ℂ) τ := by
        simp [a, jacobiTheta₂_term, mul_assoc, mul_left_comm, mul_comm, add_left_comm,
          add_comm, pow_two, one_add_one_eq_two]
      have hnorm0 :
          ‖jacobiTheta₂_term (n + 2 : ℤ) (0 : ℂ) τ‖ =
            Real.exp
              (-Real.pi * ((n + 2 : ℤ) : ℝ) ^ 2 * τ.im
                - 2 * Real.pi * ((n + 2 : ℤ) : ℝ) * (0 : ℂ).im) := by
        simpa using (norm_jacobiTheta₂_term (n + 2 : ℤ) (0 : ℂ) τ)
      have hcast : ((n + 2 : ℤ) : ℝ) = (n : ℝ) + 2 := by norm_cast
      calc
        ‖a (n + 1)‖ = ‖jacobiTheta₂_term (n + 2 : ℤ) (0 : ℂ) τ‖ := by simp [ha_eq]
        _ = Real.exp (-Real.pi * ((n + 2 : ℤ) : ℝ) ^ 2 * τ.im) := by
              simp [hnorm0]
        _ = Real.exp (-Real.pi * (((n + 2 : ℤ) : ℝ) ^ 2 * t)) := by
              simp [τ, mul_assoc]
        _ = Real.exp (-Real.pi * (((n : ℝ) + 2) ^ 2 * t)) := by
              simp [hcast]
    rw [hnorm]
    simpa [b, r, pow_two] using exp_neg_pi_mul_sq_add_two_mul_le_geom t ht n
  have hsumNorm : Summable (fun n : ℕ ↦ ‖a (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm hb_summable
  have htail :
      ‖∑' n : ℕ, a (n + 1)‖ ≤ Real.exp (-(4 : ℝ) * Real.pi * t) * ((1 - r)⁻¹) := by
    have h0 := norm_tsum_le_tsum_norm hsumNorm
    refine h0.trans ?_
    have hmono :
        (∑' n : ℕ, ‖a (n + 1)‖) ≤ ∑' n : ℕ, b n :=
      hsumNorm.tsum_le_tsum (fun n => hterm n) hb_summable
    have hbsum : (∑' n : ℕ, b n) = Real.exp (-(4 : ℝ) * Real.pi * t) * ((1 - r)⁻¹) := by
      simpa [b] using (hgeom.mul_left (Real.exp (-(4 : ℝ) * Real.pi * t))).tsum_eq
    exact hmono.trans (le_of_eq hbsum)
  have hΘ₄' : Θ₄.resToImagAxis t = (1 : ℂ) + (2 : ℂ) * ∑' n : ℕ, a n := by
    calc
      Θ₄.resToImagAxis t = jacobiTheta τ := hΘ₄
      _ = (1 : ℂ) + (2 : ℂ) * ∑' n : ℕ, a n := hjac
  have hrew :
      Θ₄.resToImagAxis t - (1 : ℂ) + (2 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) =
        (2 : ℂ) * ((∑' n : ℕ, a n) - a 0) := by
    rw [hΘ₄']
    have hexp : (Real.exp (-Real.pi * t) : ℂ) = -a 0 := by
      simpa using (congrArg Neg.neg ha0).symm
    rw [hexp]
    ring
  calc
    ‖Θ₄.resToImagAxis t - (1 : ℂ) + (2 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖
        = ‖(2 : ℂ) * ((∑' n : ℕ, a n) - a 0)‖ := by
          simpa using congrArg norm hrew
    _ = (2 : ℝ) * ‖(∑' n : ℕ, a n) - a 0‖ := by simp
    _ = (2 : ℝ) * ‖∑' n : ℕ, a (n + 1)‖ := by simp [hshift]
    _ ≤ (2 : ℝ) * (Real.exp (-(4 : ℝ) * Real.pi * t) * ((1 - r)⁻¹)) := by
          gcongr
    _ = (2 / (1 - Real.exp (-Real.pi))) * Real.exp (-(4 : ℝ) * Real.pi * t) := by
          have : (2 : ℝ) * (Real.exp (-(4 : ℝ) * Real.pi * t) * ((1 - r)⁻¹)) =
              (2 / (1 - r)) * Real.exp (-(4 : ℝ) * Real.pi * t) := by
            simp [div_eq_mul_inv, mul_assoc, mul_comm]
          simpa [r, this]


end

end MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis
