import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.E2

/-!
# Boundedness at Infinity for Eisenstein Series and Derivatives

This file establishes that E₂, E₄, and their products/derivatives are bounded at infinity.
These lemmas are used for asymptotic analysis and dimension arguments.

## Main results

* `E₂_isBoundedAtImInfty` : E₂ is bounded as im(z) → ∞
* `E₄_isBoundedAtImInfty` : E₄ is bounded at infinity (as a modular form)
* `E₂_mul_E₄_isBoundedAtImInfty` : The product E₂ · E₄ is bounded at infinity
* `D_E₄_isBoundedAtImInfty` : D(E₄) is bounded at infinity
* `serre_D_E₄_isBoundedAtImInfty` : serre_D 4 E₄ is bounded at infinity
-/

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap
open ModularForm EisensteinSeries TopologicalSpace Set MeasureTheory
open Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped ModularForm MatrixGroups Manifold Interval Real NNReal ENNReal Topology BigOperators

noncomputable section

/-- E₂ is bounded at infinity.

Uses `E₂_eq`: E₂(z) = 1 - 24·Σn·qⁿ/(1-qⁿ) where q = exp(2πiz).
As im(z) → ∞, ‖q‖ → 0, so the sum → 0, hence E₂(z) → 1.

**Proof strategy** (partially implemented below):
1. For im(z) ≥ 1, |q| ≤ exp(-2π) < 0.002
2. Bound: |n·q^n/(1-q^n)| ≤ n·|q|^n/(1-|q|) since |1-q^n| ≥ 1-|q| for n ≥ 1
3. The tsum is bounded by |q|/(1-|q|)³ < 0.003
4. Therefore |E₂| ≤ 1 + 24·0.003 < 2

**Remaining**: Complete the tsum bound using `norm_tsum_le_tsum_norm` and
geometric series. See JacobiTheta.lean:374 (`isBoundedAtImInfty_H₂`) for similar proofs. -/
lemma E₂_isBoundedAtImInfty : IsBoundedAtImInfty E₂ := by
  -- Use E₂_eq: E₂ z = 1 - 24 * ∑' n : ℕ+, n * q^n / (1 - q^n) where q = exp(2πiz)
  -- As im(z) → ∞, |q| → 0, so the sum → 0, hence E₂ → 1 (bounded).
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  -- We'll show: ∃ M A : ℝ, ∀ z : ℍ, A ≤ im z → ‖E₂ z‖ ≤ M
  -- Use explicit constant to avoid numeric grind: M = 1 + 24 * exp(-2π) / (1 - exp(-2π))³
  set r₀ : ℝ := Real.exp (-2 * π) with hr₀_def
  refine ⟨1 + 24 * (r₀ / (1 - r₀) ^ 3), 1, ?_⟩
  intro z hz
  rw [E₂_eq]
  -- E₂ z = 1 - 24 * ∑' n, n * q^n / (1 - q^n)
  -- Need to bound ‖1 - 24 * tsum‖ ≤ 1 + 24 * ‖tsum‖
  have hq : ‖cexp (2 * π * Complex.I * z)‖ < 1 := norm_exp_two_pi_I_lt_one z
  -- When im(z) ≥ 1, |q| ≤ exp(-2π) < 0.002, so the sum is very small
  have hq_bound : ‖cexp (2 * π * Complex.I * z)‖ ≤ Real.exp (-2 * π) := by
    have h1 : (2 * ↑π * Complex.I * (z : ℂ)).re = -2 * π * z.im := by
      rw [show (2 : ℂ) * ↑π * Complex.I * z = Complex.I * (2 * π * z) by ring]
      simp [Complex.I_re, Complex.I_im, mul_comm]
    rw [Complex.norm_exp, h1, Real.exp_le_exp]
    have hpi : 0 < π := Real.pi_pos
    have him : 1 ≤ z.im := hz
    nlinarith
  -- Step 1: Triangle inequality: ‖1 - 24 * tsum‖ ≤ 1 + 24 * ‖tsum‖
  calc ‖1 - 24 * ∑' (n : ℕ+), ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
          (1 - cexp (2 * π * Complex.I * ↑n * ↑z))‖
      ≤ ‖(1 : ℂ)‖ +
          ‖24 * ∑' (n : ℕ+), ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
            (1 - cexp (2 * π * Complex.I * ↑n * ↑z))‖ := norm_sub_le _ _
    _ = 1 + 24 * ‖∑' (n : ℕ+), ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
          (1 - cexp (2 * π * Complex.I * ↑n * ↑z))‖ := by
        simp only [norm_one, norm_mul, RCLike.norm_ofNat]
    _ ≤ 1 + 24 * (r₀ / (1 - r₀) ^ 3) := ?_
  -- Step 2: Need to show ‖tsum‖ ≤ r₀ / (1 - r₀)³ where r₀ = exp(-2π)
  -- Strategy: Use norm_tsum_le_tsum_norm + term bound + geometric series
  -- Let q = exp(2πiz). We need to bound the tsum.
  set q : ℂ := cexp (2 * π * Complex.I * z) with hq_def
  -- Rewrite the sum in terms of q: exp(2πinz) = (exp(2πiz))^n = q^n
  have hexp_pow : ∀ n : ℕ, cexp (2 * π * Complex.I * n * z) = q ^ n := fun n => by
    rw [hq_def, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hsum_eq : (fun n : ℕ+ => ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
      (1 - cexp (2 * π * Complex.I * ↑n * ↑z))) =
      (fun n : ℕ+ => ↑n * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))) := by
    ext n
    simp only [hexp_pow]
  rw [hsum_eq]
  -- Key bounds on r₀
  have hr₀_pos : 0 < r₀ := Real.exp_pos _
  have hr₀_lt_one : r₀ < 1 := by
    simp only [hr₀_def]
    have hpi : 0 < π := Real.pi_pos
    calc Real.exp (-2 * π) < Real.exp 0 := Real.exp_strictMono (by linarith)
      _ = 1 := Real.exp_zero
  have hone_sub_r₀_pos : 0 < 1 - r₀ := by linarith
  -- Key bounds on q
  have hq_lt_one : ‖q‖ < 1 := hq
  have hq_pos : 0 < ‖q‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hone_sub_q_pos : 0 < 1 - ‖q‖ := by linarith
  -- Term bound: ‖n * q^n / (1 - q^n)‖ ≤ n * ‖q‖^n / (1 - ‖q‖)
  have hterm_bound : ∀ n : ℕ+, ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤
      n * ‖q‖ ^ (n : ℕ) / (1 - ‖q‖) := fun n => by
    have hqn_lt : ‖q ^ (n : ℕ)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq_lt_one n.ne_zero
    have hdenom_ne : 1 - q ^ (n : ℕ) ≠ 0 := by
      intro h; simp only [sub_eq_zero] at h
      have : ‖q ^ (n : ℕ)‖ = 1 := by rw [← h]; exact norm_one
      linarith
    rw [norm_div, norm_mul, Complex.norm_natCast]
    -- |1 - q^n| ≥ 1 - |q^n| ≥ 1 - |q| (reverse triangle inequality)
    have hdenom_lower : 1 - ‖q‖ ≤ ‖1 - q ^ (n : ℕ)‖ := by
      have h1 : 1 - ‖q ^ (n : ℕ)‖ ≤ ‖1 - q ^ (n : ℕ)‖ := by
        have := norm_sub_norm_le (1 : ℂ) (q ^ (n : ℕ))
        simp only [norm_one] at this
        linarith
      have h2 : ‖q‖ ^ (n : ℕ) ≤ ‖q‖ := by
        have := pow_le_pow_of_le_one (norm_nonneg _) hq_lt_one.le n.one_le
        simp at this; exact this
      calc 1 - ‖q‖ ≤ 1 - ‖q‖ ^ (n : ℕ) := by linarith
        _ = 1 - ‖q ^ (n : ℕ)‖ := by rw [norm_pow]
        _ ≤ _ := h1
    -- Now: (n * |q|^n) / |1 - q^n| ≤ (n * |q|^n) / (1 - |q|)
    calc ↑n * ‖q ^ (n : ℕ)‖ / ‖1 - q ^ (n : ℕ)‖
        ≤ ↑n * ‖q ^ (n : ℕ)‖ / (1 - ‖q‖) := by
          apply div_le_div_of_nonneg_left _ hone_sub_q_pos hdenom_lower
          exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
      _ = ↑n * ‖q‖ ^ (n : ℕ) / (1 - ‖q‖) := by rw [norm_pow]
  -- Set r = ‖q‖ for convenience
  set r : ℝ := ‖q‖ with hr_def
  have hr_pos : 0 < r := hq_pos
  have hr_lt_one : r < 1 := hq_lt_one
  have hr_le_r₀ : r ≤ r₀ := hq_bound
  have hone_sub_r_pos : 0 < 1 - r := hone_sub_q_pos
  have hr_norm_lt_one : ‖r‖ < 1 := by
    simp only [Real.norm_eq_abs, abs_of_nonneg hr_pos.le, hr_lt_one]
  -- Summability of n * r^n on ℕ (from mathlib)
  have hsumm_nat : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 hr_norm_lt_one
    simp only [pow_one] at this
    exact this
  -- Convert to ℕ+ via nat_pos_tsum2 (using f 0 = 0)
  have hsumm_pnat : Summable (fun n : ℕ+ => (n : ℝ) * r ^ (n : ℕ)) := by
    have h0 : (fun n : ℕ => (n : ℝ) * r ^ n) 0 = 0 := by simp
    exact (nat_pos_tsum2 _ h0).mpr hsumm_nat
  -- Summability with (1 - r)⁻¹ factor
  have hsumm_majorant : Summable (fun n : ℕ+ => (n : ℝ) * r ^ (n : ℕ) / (1 - r)) := by
    have hr_ne : (1 - r) ≠ 0 := hone_sub_r_pos.ne'
    simpa [div_eq_mul_inv] using hsumm_pnat.mul_right (1 - r)⁻¹
  -- Summability of the complex sum norms
  have hsumm_norms : Summable
      (fun n : ℕ+ => ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsumm_majorant
    convert hterm_bound n using 2
  -- Bound: ‖tsum‖ ≤ ∑' (n : ℕ+), ‖term‖ ≤ ∑' (n : ℕ+), n * r^n / (1 - r)
  have htsum_le : ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤
      ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r) := by
    calc ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
        ≤ ∑' n : ℕ+, ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ :=
          norm_tsum_le_tsum_norm hsumm_norms
      _ ≤ ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r) :=
          Summable.tsum_le_tsum (fun n => by convert hterm_bound n using 2)
            hsumm_norms hsumm_majorant
  -- Compute ∑' n : ℕ, n * r^n = r / (1 - r)²
  have hsum_nat : (∑' n : ℕ, (n : ℝ) * r ^ n) = r / (1 - r) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hr_norm_lt_one
  -- Convert ℕ+ sum via tsum_pnat_eq_tsum_succ4 (f 0 = 0 so sums match)
  have hsum_pnat : (∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ)) = r / (1 - r) ^ 2 := by
    have heq := tsum_pnat_eq_tsum_succ4 (fun n => (n : ℝ) * r ^ n) hsumm_nat
    simp only [Nat.cast_zero, zero_mul, zero_add] at heq
    rw [← hsum_nat]; exact heq
  -- With (1-r)⁻¹ factor: r / (1-r)³
  have hsum_majorant_eq :
      (∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r)) = r / (1 - r) ^ 3 := by
    have hr_ne : (1 - r) ≠ 0 := hone_sub_r_pos.ne'
    rw [tsum_div_const, hsum_pnat]
    field_simp
  -- Now: ‖tsum‖ ≤ r / (1-r)³ ≤ r₀ / (1-r₀)³
  -- Monotonicity: f(x) = x/(1-x)³ is increasing on [0,1) since f'(x) = (1+2x)/(1-x)⁴ > 0
  have hmono : r / (1 - r) ^ 3 ≤ r₀ / (1 - r₀) ^ 3 := by
    -- Since 0 ≤ r ≤ r₀ < 1, and x/(1-x)³ is increasing on [0,1)
    have h1 : 0 ≤ r := hr_pos.le
    have h2 : r ≤ r₀ := hr_le_r₀
    have h3 : r₀ < 1 := hr₀_lt_one
    -- Use gcongr for numerator and denominator separately
    gcongr
  -- Chain the bounds
  have htsum_bound : ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤
      r₀ / (1 - r₀) ^ 3 := by
    calc ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
        ≤ ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r) := htsum_le
      _ = r / (1 - r) ^ 3 := hsum_majorant_eq
      _ ≤ r₀ / (1 - r₀) ^ 3 := hmono
  -- Final: 24 * ‖tsum‖ ≤ 24 * r₀ / (1 - r₀)³
  gcongr

/-- E₄ is bounded at infinity (as a modular form). -/
lemma E₄_isBoundedAtImInfty : IsBoundedAtImInfty E₄.toFun :=
  ModularFormClass.bdd_at_infty E₄

/-- The product E₂ · E₄ is bounded at infinity. -/
lemma E₂_mul_E₄_isBoundedAtImInfty : IsBoundedAtImInfty (E₂ * E₄.toFun) := by
  exact E₂_isBoundedAtImInfty.mul E₄_isBoundedAtImInfty

/-- D E₄ is bounded at infinity.

The q-expansion D(E₄) = 240·Σn·σ₃(n)·qⁿ has no constant term,
so D(E₄) → 0 as im(z) → ∞.
This is even stronger than boundedness: D(E₄) vanishes at infinity.

**Proof outline**: D commutes with the q-expansion tsum (by uniform convergence),
and D(qⁿ) = n·qⁿ for q = exp(2πiz) (up to normalizing constants).
Since the sum has no q⁰ term, it vanishes as ‖q‖ → 0.

**Blocker**: Need D-tsum interchange lemma. See Issue #90 for the q-expansion approach
to Ramanujan's identities. Could use `D_E4_qexp` once that's proved. -/
lemma D_E₄_isBoundedAtImInfty : IsBoundedAtImInfty (D E₄.toFun) := by
  sorry

/-- serre_D 4 E₄ is bounded at infinity. -/
lemma serre_D_E₄_isBoundedAtImInfty : IsBoundedAtImInfty (serre_D 4 E₄.toFun) := by
  -- serre_D 4 E₄ = D E₄ - (4/12)·E₂·E₄ = D E₄ - (1/3)·E₂·E₄
  -- Both terms are bounded at infinity
  unfold serre_D
  -- The subtraction of bounded functions is bounded
  have h1 : IsBoundedAtImInfty (D E₄.toFun) := D_E₄_isBoundedAtImInfty
  have h2 : IsBoundedAtImInfty (fun z => (4 : ℂ) * 12⁻¹ * E₂ z * E₄.toFun z) := by
    have hconst : IsBoundedAtImInfty (fun _ : ℍ => (4 : ℂ) * 12⁻¹) :=
      Filter.const_boundedAtFilter _ _
    convert hconst.mul E₂_mul_E₄_isBoundedAtImInfty using 1
    ext z
    simp only [Pi.mul_apply]
    ring
  exact h1.sub h2

end
