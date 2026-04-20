module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Core
public import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
public import SpherePacking.ModularForms.PhiTransformLemmas
public import SpherePacking.ModularForms.Delta
public import SpherePacking.ModularForms.DimensionFormulas
public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.g.CohnElkies.DeltaBounds
public import SpherePacking.ForMathlib.SigmaBounds
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.Periodic


/-!
# Helpers on the imaginary axis (AnotherIntegral.A)

This file provides helper definitions and bounds for evaluating modular objects on the positive
imaginary axis, used in the `AnotherIntegral.A` estimates.

## Main definitions
* `zI`

## Main statements
* `norm_φ₀_imag_le`
* `exists_E4_sub_one_bound`, `exists_Delta_sub_q_bound`
-/


namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Topology MatrixGroups CongruenceSubgroup ModularForm NNReal ENNReal
open scoped ArithmeticFunction.sigma

open Real Complex MeasureTheory Filter Function
open ArithmeticFunction

open MagicFunction.FourierEigenfunctions
open UpperHalfPlane ModularForm EisensteinSeries
open SlashInvariantFormClass ModularFormClass

noncomputable section

/-- The point `it` in the upper half-plane, as an element of `ℍ`. -/
@[expose] public def zI (t : ℝ) (ht : 0 < t) : ℍ :=
  ⟨(Complex.I : ℂ) * (t : ℂ), by simpa using ht⟩

/-- Imaginary part of `zI t ht` is `t`. -/
public lemma zI_im (t : ℝ) (ht : 0 < t) : (zI t ht).im = t := by
  simp [zI, UpperHalfPlane.im]

lemma qParam_zI (t : ℝ) (ht : 0 < t) :
    Periodic.qParam (1 : ℝ) (zI t ht) = (Real.exp (-2 * π * t) : ℂ) := by
  simp [Periodic.qParam, zI, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
    show (Complex.I : ℂ) * (Complex.I * (↑t * (↑π * 2))) = -(↑t * (↑π * 2)) by ring_nf; simp]

lemma qParam_zI_norm (t : ℝ) (ht : 0 < t) :
    ‖Periodic.qParam (1 : ℝ) (zI t ht)‖ = Real.exp (-2 * π * t) := by
  simpa [zI, mul_assoc, mul_left_comm, mul_comm, div_one] using
    (Periodic.norm_qParam (h := (1 : ℝ)) (z := ((zI t ht : ℍ) : ℂ)))

/-- The imaginary part of `(Complex.I : ℂ) / t` is `t⁻¹` (as a real number). -/
public lemma imag_I_div (t : ℝ) : ((Complex.I : ℂ) / (t : ℂ)).im = t⁻¹ := by
  simp [Complex.div_im, Complex.normSq]

/-- Norm of a real exponential viewed in `ℂ`. -/
public lemma norm_ofReal_exp (x : ℝ) : ‖(Real.exp x : ℂ)‖ = Real.exp x := by
  simp

/-- Action of the modular matrix `S` on the imaginary-axis point `zI t ht`. -/
public lemma modular_S_smul_zI (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • zI t ht = zI t⁻¹ (inv_pos.2 ht) := by
  ext1
  simpa [zI, Complex.ofReal_inv, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (ModularGroup.coe_S_smul (z := zI t ht))

/-- `exp (-2π) < 1`. -/
public lemma exp_neg_two_pi_lt_one : Real.exp (-2 * π) < 1 := by
  simpa using (Real.exp_lt_one_iff).2 (by nlinarith [Real.pi_pos] : (-2 * π : ℝ) < 0)

/-- Monotonicity estimate `exp (-2π t) ≤ exp (-2π)` for `1 ≤ t`. -/
public lemma q_le_q1 {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-2 * π * t) ≤ Real.exp (-2 * π) :=
  Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, ht])

/-! ## Bounds for `φ₀` on the imaginary axis -/

/-- Exponential decay bound for `φ₀'' (it)` on `t ≥ 1`. -/
public lemma norm_φ₀_imag_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖φ₀'' ((Complex.I : ℂ) * (t : ℂ))‖ ≤ C * Real.exp (-2 * π * t) := by
  rcases MagicFunction.PolyFourierCoeffBound.norm_φ₀_le with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  simpa [show φ₀ (zI t ht0) = φ₀'' ((Complex.I : ℂ) * (t : ℂ)) by
    simpa [zI] using
      (φ₀''_def (z := (Complex.I : ℂ) * (t : ℂ)) (by simpa using ht0)).symm,
    zI_im t ht0] using
    hC (zI t ht0) (by simpa [zI_im t ht0] using lt_of_lt_of_le (by norm_num : (1/2 : ℝ) < 1) ht)

/-! ## `q`-expansion remainder bounds on the imaginary axis. -/

open scoped ComplexConjugate
open SlashInvariantFormClass ModularFormClass

lemma exp_neg_pi_lt_one : Real.exp (-π) < 1 := by
  simpa using (Real.exp_lt_one_iff).2 (neg_lt_zero.mpr Real.pi_pos)

lemma exp_neg_two_pi_lt_exp_neg_pi {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-2 * π * t) < Real.exp (-π) :=
  Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos, ht])

lemma qParam_zI_norm_lt_exp_neg_pi {t : ℝ} (ht : 1 ≤ t) :
    ‖Periodic.qParam (1 : ℝ) (zI t (lt_of_lt_of_le (by norm_num) ht))‖ < Real.exp (-π) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  simpa [qParam_zI_norm t ht0] using exp_neg_two_pi_lt_exp_neg_pi (t := t) ht

lemma cuspFunction_qParam_eq {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)}
    {k : ℤ} (f : F) [SlashInvariantFormClass F Γ k] (z : ℍ)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) :
    cuspFunction (1 : ℝ) f (Periodic.qParam (1 : ℝ) z) = f z := by
  simpa using
    SlashInvariantFormClass.eq_cuspFunction (h := (1 : ℝ)) (f := f) (τ := z) hΓ one_ne_zero

/-- Helper: bound `‖cexp(2π i m z)‖` by `q^j * q1^k` whenever `m = j + k`. -/
private lemma norm_cexp_mul_le_split {z : ℍ} {q q1 : ℝ} (hq_nonneg : 0 ≤ q) (hq_le : q ≤ q1)
    (hqC : (Periodic.qParam (1 : ℝ) z) = (q : ℂ)) (j k : ℕ) :
    ‖cexp (2 * π * Complex.I * ((j + k : ℕ) : ℂ) * z)‖ ≤ q ^ j * q1 ^ k := by
  rw [show ‖cexp (2 * π * Complex.I * ((j + k : ℕ) : ℂ) * z)‖ = q ^ (j + k) from by
      rw [show cexp (2 * π * Complex.I * ((j + k : ℕ) : ℂ) * z) =
          (cexp (2 * π * Complex.I * z)) ^ (j + k) from by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (Complex.exp_nat_mul (2 * π * Complex.I * z) (j + k)),
        show cexp (2 * π * Complex.I * z) = (q : ℂ) from by
          simpa [Periodic.qParam] using hqC]
      simp [abs_of_nonneg hq_nonneg],
    pow_add]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hq_nonneg hq_le _) (pow_nonneg hq_nonneg _)

/-- Helper: bound `‖m * σ₃(m)‖` by `M ^ 5` when `m ≤ M`. -/
private lemma norm_mul_sigma_le (m M : ℕ) (hM : m ≤ M) :
    ‖((m : ℂ) * (σ 3 m : ℂ))‖ ≤ ((M : ℝ) ^ 5 : ℝ) := by
  have hcoeff_nat : m * (σ 3 m) ≤ m ^ 5 := by
    have := Nat.mul_le_mul_left m (SpherePacking.ForMathlib.sigma_three_le_pow_four m)
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
  calc ‖((m : ℂ) * (σ 3 m : ℂ))‖ = (m * (σ 3 m) : ℝ) := by
        have : ‖(m : ℂ)‖ = (m : ℝ) := by simp
        simp_all
    _ ≤ (m ^ 5 : ℝ) := by exact_mod_cast hcoeff_nat
    _ ≤ ((M : ℝ) ^ 5 : ℝ) := by exact_mod_cast Nat.pow_le_pow_left hM 5

lemma qExpansionFormalMultilinearSeries_partialSum_one
    {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : F)
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (q : ℂ) :
    (qExpansionFormalMultilinearSeries (h := (1 : ℝ)) f).partialSum 1 q =
      (qExpansion (1 : ℝ) f).coeff 0 := by
        simp [qExpansionFormalMultilinearSeries, FormalMultilinearSeries.partialSum]

lemma qExpansionFormalMultilinearSeries_partialSum_two
    {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : F)
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (q : ℂ) :
    (qExpansionFormalMultilinearSeries (h := (1 : ℝ)) f).partialSum 2 q =
      (qExpansion (1 : ℝ) f).coeff 0 + (qExpansion (1 : ℝ) f).coeff 1 * q := by
  simp [qExpansionFormalMultilinearSeries, FormalMultilinearSeries.partialSum,
    Finset.sum_range_succ, mul_comm]

lemma qExpansionFormalMultilinearSeries_partialSum_three
    {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : F)
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (q : ℂ) :
    (qExpansionFormalMultilinearSeries (h := (1 : ℝ)) f).partialSum 3 q =
      (qExpansion (1 : ℝ) f).coeff 0 + (qExpansion (1 : ℝ) f).coeff 1 * q +
        (qExpansion (1 : ℝ) f).coeff 2 * q ^ (2 : ℕ) := by
  simp [qExpansionFormalMultilinearSeries, FormalMultilinearSeries.partialSum,
    Finset.sum_range_succ, mul_comm, add_assoc]

/-! Uniform `q`-expansion bounds on the imaginary axis (for `t ≥ 1`). -/

private lemma hh : (0 : ℝ) < (1 : ℝ) := by norm_num

private lemma hΓ1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma (↑1)).strictPeriods := by simp

private def r0 : ℝ≥0 := ⟨Real.exp (-π), (Real.exp_pos _).le⟩

private lemma hr0 : (r0 : ℝ≥0∞) < (1 : ℝ≥0∞) := by
  refine ENNReal.coe_lt_one_iff.2 ?_
  change Real.exp (-π) < 1
  exact exp_neg_pi_lt_one

private lemma qParam_zI_mem_ball {t : ℝ} (ht : 0 < t) (ht1 : 1 ≤ t) :
    Periodic.qParam (1 : ℝ) (zI t ht) ∈ Metric.ball (0 : ℂ) (r0 : ℝ) := by
  have : ‖Periodic.qParam (1 : ℝ) (zI t ht)‖ < (r0 : ℝ) := by
    simpa [r0] using qParam_zI_norm_lt_exp_neg_pi (t := t) ht1
  simpa [Metric.mem_ball, dist_zero_right] using this

private lemma exists_sub_partialSum_bound
    {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : F)
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖f (zI t ht) -
          (qExpansionFormalMultilinearSeries (h := (1 : ℝ)) f).partialSum n
            (Periodic.qParam (1 : ℝ) (zI t ht))‖ ≤
        C * (Real.exp (-2 * π * t)) ^ n := by
  rcases (ModularFormClass.hasFPowerSeries_cuspFunction
      (f := f) (h := (1 : ℝ)) hh hΓ).uniform_geometric_approx' (r' := r0)
      (by simpa using hr0) with ⟨a, ha, C, hCpos, hbound⟩
  refine ⟨C * (a / (r0 : ℝ)) ^ n,
    mul_pos hCpos (pow_pos (div_pos ha.1 (Real.exp_pos (-π))) _),
    fun t ht ht1 => ?_⟩
  let z : ℍ := zI t ht
  let q : ℂ := Periodic.qParam (1 : ℝ) z
  have hqnorm : ‖q‖ = Real.exp (-2 * π * t) := by
    simpa [q, z] using qParam_zI_norm t ht
  have hmain :
      ‖f z - (qExpansionFormalMultilinearSeries (h := (1 : ℝ)) f).partialSum n q‖ ≤
        (C * (a / (r0 : ℝ)) ^ n) * ‖q‖ ^ n := by
    simpa [show cuspFunction (1 : ℝ) f q = f z from by
        simpa [q] using cuspFunction_qParam_eq (f := f) z hΓ,
      show C * (a * (‖q‖ / r0)) ^ n = (C * (a / (r0 : ℝ)) ^ n) * ‖q‖ ^ n from by
        simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_pow]] using
      hbound q (by simpa [q, z] using qParam_zI_mem_ball (t := t) ht ht1) n
  simpa [z, q, hqnorm] using hmain

/-- Uniform bound `‖E₄ (it) - 1‖ = O(exp (-2πt))` valid for all `t ≥ 1`. -/
public lemma exists_E4_sub_one_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖E₄ (zI t ht) - (1 : ℂ)‖ ≤ C * Real.exp (-2 * π * t) := by
  rcases exists_sub_partialSum_bound (f := E₄) (Γ := CongruenceSubgroup.Gamma (↑1)) (k := 4)
      hΓ1 1 with ⟨C, hCpos, hC⟩
  exact ⟨C, hCpos, fun t ht0 ht1 => by
    simpa [qExpansionFormalMultilinearSeries_partialSum_one (f := E₄), E4_q_exp_zero]
      using hC t ht0 ht1⟩

/--
Second-order remainder bound for `E₄ (it)` after subtracting `1 + 240 q`, where
`q = exp (-2π t)`, valid for all `t ≥ 1`.
-/
public lemma exists_E4_sub_one_sub_240q_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖E₄ (zI t ht) - ((1 : ℂ) + (240 : ℂ) * (Real.exp (-2 * π * t) : ℂ))‖ ≤
        C * (Real.exp (-2 * π * t)) ^ (2 : ℕ) := by
  rcases exists_sub_partialSum_bound (f := E₄) (Γ := CongruenceSubgroup.Gamma (↑1)) (k := 4)
      hΓ1 2 with ⟨C, hCpos, hC⟩
  exact ⟨C, hCpos, fun t ht0 ht1 => by
    simpa [qExpansionFormalMultilinearSeries_partialSum_two (f := E₄), E4_q_exp_zero,
      E4_q_exp_one, qParam_zI t ht0] using hC t ht0 ht1⟩

lemma Delta_q_exp_zero : (qExpansion 1 Delta).coeff 0 = (0 : ℂ) := by
  simp [ModularFormClass.qExpansion_coeff_zero (f := Delta) (h := (1 : ℝ)) hh hΓ1,
    show valueAtInfty (Delta : ℍ → ℂ) = (0 : ℂ) by
      simpa using
        (ModularFormClass.cuspFunction_apply_zero (f := Delta) (h := (1 : ℝ)) hh hΓ1).symm.trans
          (CuspFormClass.cuspFunction_apply_zero (f := Delta) (h := (1 : ℝ)) hh hΓ1)]

/--
Second-order remainder bound for `Δ (it)` after subtracting `q = exp (-2π t)`, valid for all
`t ≥ 1`.
-/
public lemma exists_Delta_sub_q_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖Δ (zI t ht) - (Real.exp (-2 * π * t) : ℂ)‖ ≤
        C * (Real.exp (-2 * π * t)) ^ (2 : ℕ) := by
  rcases exists_sub_partialSum_bound (f := Delta) (Γ := CongruenceSubgroup.Gamma (↑1)) (k := 12)
      hΓ1 2 with ⟨C, hCpos, hC⟩
  exact ⟨C, hCpos, fun t ht0 ht1 => by
    simpa [qExpansionFormalMultilinearSeries_partialSum_two (f := Delta), Delta_q_exp_zero,
      Delta_q_one_term, qParam_zI t ht0, Delta_apply] using hC t ht0 ht1⟩

/--
Third-order remainder bound for `Δ (it)` after subtracting `q - 24 q^2`, where `q = exp (-2π t)`,
valid for all `t ≥ 1`.
-/
public lemma exists_Delta_sub_q_sub_neg24_qsq_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖Δ (zI t ht) -
          ((Real.exp (-2 * π * t) : ℂ) + (-24 : ℂ) * ((Real.exp (-2 * π * t)) ^ (2 : ℕ) : ℂ))‖ ≤
        C * (Real.exp (-2 * π * t)) ^ (3 : ℕ) := by
  rcases exists_sub_partialSum_bound (f := Delta) (Γ := CongruenceSubgroup.Gamma (↑1)) (k := 12)
      hΓ1 3 with ⟨C, hCpos, hC⟩
  exact ⟨C, hCpos, fun t ht0 ht1 => by
    simpa [qExpansionFormalMultilinearSeries_partialSum_three (f := Delta), Delta_q_exp_zero,
      Delta_q_one_term, Delta_q_exp_two, qParam_zI t ht0, Delta_apply] using hC t ht0 ht1⟩

/-! ### Bounding `E₂E₄ - E₆` on the imaginary axis. -/

/--
Second-order remainder bound for `E₂(it)E₄(it) - E₆(it)` after subtracting `720 q`, where
`q = exp (-2π t)`, valid for all `t ≥ 1`.
-/
public lemma exists_E2E4_sub_E6_sub_720q_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖(E₂ (zI t ht)) * (E₄ (zI t ht)) - (E₆ (zI t ht)) -
            (720 : ℂ) * (Real.exp (-2 * π * t) : ℂ)‖ ≤
        C * (Real.exp (-2 * π * t)) ^ (2 : ℕ) := by
  -- A fixed geometric ratio (valid for all `t ≥ 1`).
  let q1 : ℝ := Real.exp (-2 * π)
  have hq1_nonneg : 0 ≤ q1 := (Real.exp_pos _).le
  have hq1_lt_one : q1 < 1 := by
    simpa [q1] using exp_neg_two_pi_lt_one
  -- A summable majorant series.
  let b : ℕ → ℝ := fun n => ((n + 2 : ℝ) ^ 5) * q1 ^ n
  have hb_summ : Summable b := by
    have hq1_norm : ‖q1‖ < 1 := by
      simpa [Real.norm_of_nonneg hq1_nonneg] using hq1_lt_one
    have hsummA :
        Summable (fun n : ℕ => (((n : ℝ) ^ 5 + 1) : ℝ) * q1 ^ n) := by
      simpa [show (fun n : ℕ => (((n : ℝ) ^ 5 + 1) : ℝ) * q1 ^ n) =
          (fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * q1 ^ n) + fun n : ℕ => q1 ^ n from by
        funext n; simp [add_mul]] using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5 hq1_norm).add
          (summable_geometric_of_lt_one hq1_nonneg hq1_lt_one)
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => (512 : ℝ) * ((((n : ℝ) ^ 5 + 1) : ℝ) * q1 ^ n))
      (g := b) (by intro n; positivity) (fun n => ?_) (hsummA.mul_left (512 : ℝ))
    have hpow : ((n + 2 : ℝ) ^ 5) ≤ (512 : ℝ) * ((n : ℝ) ^ 5 + 1) := by
      have hbase :
          ((n : ℝ) + (2 : ℝ)) ^ 5 ≤ 2 ^ (5 - 1) * ((n : ℝ) ^ 5 + (2 : ℝ) ^ 5) := by
        simpa using add_pow_le (a := (n : ℝ)) (b := (2 : ℝ)) (by positivity) (by positivity) 5
      have hn5 : 0 ≤ (n : ℝ) ^ 5 := by positivity
      grind only
    calc b n = ((n + 2 : ℝ) ^ 5) * q1 ^ n := rfl
      _ ≤ ((512 : ℝ) * ((n : ℝ) ^ 5 + 1)) * q1 ^ n := by gcongr
      _ = (512 : ℝ) * (((n : ℝ) ^ 5 + 1) * q1 ^ n) := by ring
  -- Choose a convenient positive constant.
  refine ⟨1 + (720 : ℝ) * (∑' n : ℕ, b n), by positivity, ?_⟩
  intro t ht0 ht1
  let z : ℍ := zI t ht0
  -- `q = exp(-2πt)` and `q ≤ q1` for `t ≥ 1`.
  let q : ℝ := Real.exp (-2 * π * t)
  have hq_nonneg : 0 ≤ q := (Real.exp_pos _).le
  have hq_le : q ≤ q1 := by
    simpa [q, q1] using q_le_q1 (t := t) ht1
  have hqC : (Periodic.qParam (1 : ℝ) z) = (q : ℂ) := by
    simpa [q, z] using qParam_zI t ht0
  -- Abbreviate the coefficient function.
  let f : ℕ → ℂ :=
    fun n =>
      ((n + 2 : ℂ) * (σ 3 (n + 2) : ℂ)) *
        cexp (2 * π * Complex.I * (n + 2 : ℂ) * z)
  have hf_le : ∀ n : ℕ, ‖f n‖ ≤ q ^ (2 : ℕ) * b n := fun n => by
    have hcoeff : ‖((n + 2 : ℂ) * (σ 3 (n + 2) : ℂ))‖ ≤ ((n + 2 : ℝ) ^ 5 : ℝ) := by
      have h := norm_mul_sigma_le (n + 2) (n + 2) le_rfl
      push_cast at h ⊢; exact h
    have hexp : ‖cexp (2 * π * Complex.I * (n + 2 : ℂ) * z)‖ ≤ q ^ (2 : ℕ) * q1 ^ n := by
      simpa [show ((2 + n : ℕ) : ℂ) = (n : ℂ) + 2 by push_cast; ring] using
        norm_cexp_mul_le_split (z := z) hq_nonneg hq_le hqC 2 n
    calc
      ‖f n‖ = ‖((n + 2 : ℂ) * (σ 3 (n + 2) : ℂ))‖ *
            ‖cexp (2 * π * Complex.I * (n + 2 : ℂ) * z)‖ := by simp [f, mul_assoc]
      _ ≤ ((n + 2 : ℝ) ^ 5 : ℝ) * (q ^ (2 : ℕ) * q1 ^ n) := by gcongr
      _ = q ^ (2 : ℕ) * b n := by simp [b]; ring
  -- Use Ramanujan's identity and isolate the `n=1` term.
  have hRam := E₂_mul_E₄_sub_E₆ z
  have hqexp : cexp (2 * π * Complex.I * z) = (q : ℂ) := by
    simpa [Periodic.qParam] using hqC
  -- Convert the `ℕ+`-sum to a shifted `ℕ`-sum.
  have htsum :
      (∑' n : ℕ+, n * (σ 3 n) * cexp (2 * π * Complex.I * n * z)) =
        ∑' n : ℕ, (n + 1) * (σ 3 (n + 1)) * cexp (2 * π * Complex.I * (n + 1) * z) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ => (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * n * z)))
  -- Summability to justify splitting the first term.
  let g : ℕ → ℂ :=
    fun n =>
      (n + 1) * (σ 3 (n + 1)) * cexp (2 * π * Complex.I * (n + 1) * z)
  have hg_summ : Summable g := by
    refine Summable.of_norm_bounded (hb_summ.mul_left q) fun n => ?_
    have hexp : ‖cexp (2 * π * Complex.I * (n + 1) * z)‖ ≤ q * q1 ^ n := by
      simpa [pow_one, show ((1 + n : ℕ) : ℂ) = (n : ℂ) + 1 by push_cast; ring] using
        norm_cexp_mul_le_split (z := z) hq_nonneg hq_le hqC 1 n
    have hcoeff : ‖((n + 1 : ℂ) * (σ 3 (n + 1) : ℂ))‖ ≤ ((n + 2 : ℝ) ^ 5 : ℝ) := by
      have h := norm_mul_sigma_le (n + 1) (n + 2) (by omega)
      push_cast at h ⊢; exact h
    calc
      ‖g n‖ = ‖((n + 1 : ℂ) * (σ 3 (n + 1) : ℂ))‖ *
            ‖cexp (2 * π * Complex.I * (n + 1) * z)‖ := by simp [g, mul_assoc]
      _ ≤ ((n + 2 : ℝ) ^ 5 : ℝ) * (q * q1 ^ n) := by gcongr
      _ = q * b n := by simp [b]; ring
  have hsplit :
      (∑' n : ℕ+, n * (σ 3 n) * cexp (2 * π * Complex.I * n * z)) - cexp (2 * π * Complex.I * z) =
        ∑' n : ℕ, f n := by
    have h0 :
        (∑' n : ℕ+, n * (σ 3 n) * cexp (2 * π * Complex.I * n * z)) = ∑' n : ℕ, g n := by
      simpa [g, mul_assoc, mul_left_comm, mul_comm] using htsum
    have hg0 : g 0 = cexp (2 * π * Complex.I * z) := by simp [g]
    calc
      (∑' n : ℕ+, n * (σ 3 n) * cexp (2 * π * Complex.I * n * z)) - cexp (2 * π * Complex.I * z)
          = (∑' n : ℕ, g n) - g 0 := by simp [h0, hg0]
      _ = ∑' n : ℕ, g (n + 1) := (sub_eq_iff_eq_add).2 (by
            simpa [Finset.range_one, add_comm, add_left_comm, add_assoc] using
              (hg_summ.sum_add_tsum_nat_add 1).symm)
      _ = ∑' n : ℕ, f n := by grind only
  -- Now bound the tail series using the majorant `b`.
  have hnorm_summ : Summable (fun n : ℕ => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hf_le (hb_summ.mul_left (q ^ (2 : ℕ)))
  have htail :
      ‖∑' n : ℕ, f n‖ ≤ q ^ (2 : ℕ) * (∑' n : ℕ, b n) := by
    refine (norm_tsum_le_tsum_norm hnorm_summ).trans ?_
    have h2 : (∑' n : ℕ, ‖f n‖) ≤ ∑' n : ℕ, (q ^ (2 : ℕ) * b n) :=
      hnorm_summ.tsum_le_tsum hf_le (hb_summ.mul_left (q ^ (2 : ℕ)))
    exact h2.trans_eq (tsum_mul_left)
  have hmain :
      ‖(E₂ z) * (E₄ z) - (E₆ z) - (720 : ℂ) * (q : ℂ)‖ ≤
        (720 : ℝ) * (q ^ (2 : ℕ)) * (∑' n : ℕ, b n) := by
    have hrew : (E₂ z) * (E₄ z) - (E₆ z) - (720 : ℂ) * (q : ℂ) = (720 : ℂ) * (∑' n : ℕ, f n) := by
      rw [hRam, ← show (∑' n : ℕ+, n * (σ 3 n) * cexp (2 * π * Complex.I * n * z)) - (q : ℂ) =
        ∑' n : ℕ, f n from by simpa [hqexp] using hsplit]; ring
    calc
      ‖(E₂ z) * (E₄ z) - (E₆ z) - (720 : ℂ) * (q : ℂ)‖
          = ‖(720 : ℂ) * (∑' n : ℕ, f n)‖ := by rw [hrew]
      _ = (720 : ℝ) * ‖∑' n : ℕ, f n‖ := by simp
      _ ≤ (720 : ℝ) * (q ^ (2 : ℕ) * (∑' n : ℕ, b n)) := by gcongr
      _ = (720 : ℝ) * (q ^ (2 : ℕ)) * (∑' n : ℕ, b n) := by ring
  have hq_def : q = Real.exp (-2 * π * t) := rfl
  have hmain' :
      ‖(E₂ z) * (E₄ z) - (E₆ z) - (720 : ℂ) * (Real.exp (-2 * π * t) : ℂ)‖ ≤
        ((720 : ℝ) * (∑' n : ℕ, b n)) * (Real.exp (-2 * π * t)) ^ (2 : ℕ) := by
    simpa [hq_def, mul_assoc, mul_left_comm, mul_comm] using hmain
  simpa [z, q] using hmain'.trans
    (mul_le_mul_of_nonneg_right (by linarith : (720 : ℝ) * (∑' n : ℕ, b n) ≤
      1 + (720 : ℝ) * (∑' n : ℕ, b n)) (pow_nonneg hq_nonneg _))


end

end MagicFunction.g.CohnElkies.IntegralReps
