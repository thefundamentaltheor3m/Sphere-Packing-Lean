module
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


/-!
# Exponential bounds

Uniform bounds of the form `x ^ k * exp (-b * x)` on `0 ≤ x`, and a few closely related variants.
-/

namespace SpherePacking.ForMathlib

open Filter Real

/-- Uniform bound for `x ^ k * exp (-b * x)` on `0 ≤ x` when `0 < b`. -/
public lemma exists_bound_pow_mul_exp_neg_mul (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → x ^ k * Real.exp (-b * x) ≤ C := by
  let f : ℝ → ℝ := fun x ↦ x ^ k * Real.exp (-b * x)
  have ht : Tendsto f atTop (nhds (0 : ℝ)) := by
    simpa [f, Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (k : ℝ)) (b := b) hb)
  rcases (eventually_atTop.1 <|
    ht.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one))) with ⟨A, hA⟩
  let A' : ℝ := max A 0
  have hA' : ∀ x, A' ≤ x → f x ≤ 1 :=
    fun x hx => le_of_lt <| hA x <| le_trans (le_max_left _ _) hx
  have hcont : Continuous f := by
    have hlin : Continuous fun x : ℝ ↦ (-b) * x :=
      (continuous_const.mul continuous_id : Continuous fun x : ℝ ↦ (-b) * x)
    simpa [f, mul_assoc] using (continuous_id.pow k).mul (Real.continuous_exp.comp hlin)
  have hne : (Set.Icc (0 : ℝ) A').Nonempty := by
    refine Set.nonempty_Icc.2 ?_
    dsimp [A']
    exact le_max_right A 0
  rcases (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) A')).exists_isMaxOn hne
      hcont.continuousOn with ⟨x0, hx0, hxmax⟩
  refine ⟨max (f x0) 1, ?_⟩
  intro x hx
  by_cases hxA : x ≤ A'
  · exact (hxmax ⟨hx, hxA⟩).trans (le_max_left _ _)
  · have hxge : A' ≤ x := le_of_not_ge hxA
    exact (hA' x hxge).trans (le_max_right _ _)

/-- Uniform bound for `x ^ k * exp (-b * sqrt x)` on `0 ≤ x`. -/
public lemma exists_bound_pow_mul_exp_neg_mul_sqrt (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → x ^ k * Real.exp (-b * Real.sqrt x) ≤ C := by
  rcases exists_bound_pow_mul_exp_neg_mul (k := 2 * k) (b := b) hb with ⟨C, hC⟩
  refine ⟨C, fun x hx => by
    simpa [pow_mul, Real.sq_sqrt hx] using hC (Real.sqrt x) (Real.sqrt_nonneg _)⟩

/-- AM-GM style inequality for the exponential weight.

For `0 ≤ x` and `0 < t`, we have
`exp (-π / t) * exp (-π * x * t) ≤ exp (-2 * π * sqrt x)`.
-/
public lemma exp_neg_pi_div_mul_exp_neg_pi_mul_le (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    Real.exp (-Real.pi / t) * Real.exp (-Real.pi * x * t) ≤
      Real.exp (-2 * Real.pi * Real.sqrt x) := by
  have ht0 : 0 ≤ t := le_of_lt ht
  have hxt : 0 ≤ x * t := mul_nonneg hx ht0
  have hAMGM :
      2 * Real.sqrt (x * t) * (Real.sqrt t)⁻¹ ≤ x * t + 1 / t := by
    have h := two_mul_le_add_sq (Real.sqrt (x * t)) ((Real.sqrt t)⁻¹)
    have hinv : ((Real.sqrt t)⁻¹ : ℝ) ^ 2 = (1 / t : ℝ) := by
      simp [one_div, Real.sq_sqrt ht0]
    simpa [Real.sq_sqrt hxt, hinv, mul_assoc, mul_left_comm, mul_comm] using h
  have hmul_sqrt : Real.sqrt (x * t) * (Real.sqrt t)⁻¹ = Real.sqrt x := by
    have hsqrt : Real.sqrt (x * t) = Real.sqrt x * Real.sqrt t := by
      simpa [mul_comm] using (Real.sqrt_mul hx t)
    grind
  have hIneq : 2 * Real.sqrt x ≤ x * t + 1 / t := by
    simpa [hmul_sqrt, mul_assoc] using hAMGM
  have hIneqπ : Real.pi * (2 * Real.sqrt x) ≤ Real.pi * (x * t + 1 / t) :=
    mul_le_mul_of_nonneg_left hIneq Real.pi_pos.le
  have hExpArg :
      (-Real.pi / t) + (-Real.pi * x * t) ≤ -2 * Real.pi * Real.sqrt x := by
    have hsum :
        (-Real.pi / t) + (-Real.pi * x * t) = -(Real.pi * (x * t + 1 / t)) := by
      ring_nf
    have hrhs : -2 * Real.pi * Real.sqrt x = -(Real.pi * (2 * Real.sqrt x)) := by ring_nf
    rw [hsum, hrhs]
    exact neg_le_neg hIneqπ
  have hprod :
      Real.exp (-Real.pi / t) * Real.exp (-Real.pi * x * t) =
        Real.exp ((-Real.pi / t) + (-Real.pi * x * t)) := by
    simp [Real.exp_add]
  rw [hprod]
  exact Real.exp_le_exp.2 hExpArg

/-- For `b, x ≥ 0` and `t ≥ 1`, we have `exp (-b*x*t) ≤ exp (-b*x)`. -/
public lemma exp_neg_mul_mul_le_exp_neg_mul_of_one_le {b x t : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x)
    (ht : (1 : ℝ) ≤ t) :
    Real.exp (-b * x * t) ≤ Real.exp (-b * x) := by
  have hAt : b * x ≤ b * x * t := by
    simpa [mul_assoc] using le_mul_of_one_le_right (mul_nonneg hb hx) ht
  simpa [mul_assoc, mul_left_comm, mul_comm] using Real.exp_le_exp.2 (neg_le_neg hAt)

end SpherePacking.ForMathlib
