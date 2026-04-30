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
  simpa [zI, mul_comm, div_one] using Periodic.norm_qParam (h := (1 : ℝ)) (z := (zI t ht : ℂ))

/-- The imaginary part of `(Complex.I : ℂ) / t` is `t⁻¹` (as a real number). -/
public lemma imag_I_div (t : ℝ) : ((Complex.I : ℂ) / (t : ℂ)).im = t⁻¹ := by
  simp [Complex.div_im, Complex.normSq]

/-- Norm of a real exponential viewed in `ℂ`. -/
public lemma norm_ofReal_exp (x : ℝ) : ‖(Real.exp x : ℂ)‖ = Real.exp x := by simp

/-- Action of the modular matrix `S` on the imaginary-axis point `zI t ht`. -/
public lemma modular_S_smul_zI (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • zI t ht = zI t⁻¹ (inv_pos.2 ht) := by
  ext1
  simpa [zI, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using
    ModularGroup.coe_S_smul (z := zI t ht)

/-- `exp (-2π) < 1`. -/
public lemma exp_neg_two_pi_lt_one : Real.exp (-2 * π) < 1 :=
  Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])

/-- Monotonicity estimate `exp (-2π t) ≤ exp (-2π)` for `1 ≤ t`. -/
public lemma q_le_q1 {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-2 * π * t) ≤ Real.exp (-2 * π) :=
  Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])

/-! ## Bounds for `φ₀` on the imaginary axis -/

/-- Exponential decay bound for `φ₀'' (it)` on `t ≥ 1`. -/
public lemma norm_φ₀_imag_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖φ₀'' ((Complex.I : ℂ) * (t : ℂ))‖ ≤ C * Real.exp (-2 * π * t) := by
  obtain ⟨C, hCpos, hC⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C, hCpos, fun t ht => ?_⟩
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  simpa [show φ₀ (zI t ht0) = φ₀'' ((Complex.I : ℂ) * (t : ℂ)) by
    simpa [zI] using (φ₀''_def (z := (Complex.I : ℂ) * (t : ℂ)) (by simpa using ht0)).symm,
    zI_im t ht0] using hC (zI t ht0) (by linarith [zI_im t ht0])

/-! ## `q`-expansion remainder bounds on the imaginary axis. -/

open scoped ComplexConjugate

lemma exp_neg_pi_lt_one : Real.exp (-π) < 1 :=
  Real.exp_lt_one_iff.2 (neg_lt_zero.mpr Real.pi_pos)

/-- Helper: bound `‖cexp(2π i m z)‖` by `q^j * q1^k` whenever `m = j + k`. -/
private lemma norm_cexp_mul_le_split {z : ℍ} {q q1 : ℝ} (hq_nonneg : 0 ≤ q) (hq_le : q ≤ q1)
    (hqC : (Periodic.qParam (1 : ℝ) z) = (q : ℂ)) (j k : ℕ) :
    ‖cexp (2 * π * Complex.I * ((j + k : ℕ) : ℂ) * z)‖ ≤ q ^ j * q1 ^ k := by
  have hqexp : cexp (2 * π * Complex.I * z) = (q : ℂ) := by simpa [Periodic.qParam] using hqC
  rw [show ‖cexp (2 * π * Complex.I * ((j + k : ℕ) : ℂ) * z)‖ = q ^ (j + k) by
      rw [show cexp (2 * π * Complex.I * ((j + k : ℕ) : ℂ) * z) = (q : ℂ) ^ (j + k) by
        rw [← hqexp]
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          Complex.exp_nat_mul (2 * π * Complex.I * z) (j + k)]
      simp [abs_of_nonneg hq_nonneg], pow_add]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hq_nonneg hq_le _) (pow_nonneg hq_nonneg _)

/-- Helper: bound `‖m * σ₃(m)‖` by `M ^ 5` when `m ≤ M`. -/
private lemma norm_mul_sigma_le (m M : ℕ) (hM : m ≤ M) :
    ‖((m : ℂ) * (σ 3 m : ℂ))‖ ≤ ((M : ℝ) ^ 5 : ℝ) := by
  simpa using (by exact_mod_cast
    ((by simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_le_mul_left m (SpherePacking.ForMathlib.sigma_three_le_pow_four m) :
        m * (σ 3 m) ≤ m ^ 5).trans (Nat.pow_le_pow_left hM 5)) :
      (m * (σ 3 m) : ℝ) ≤ ((M : ℝ) ^ 5 : ℝ))

lemma qExpansionFormalMultilinearSeries_partialSum_two
    {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : F)
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ] (q : ℂ) :
    (qExpansionFormalMultilinearSeries (h := (1 : ℝ)) f).partialSum 2 q =
      (qExpansion (1 : ℝ) f).coeff 0 + (qExpansion (1 : ℝ) f).coeff 1 * q := by
  simp [qExpansionFormalMultilinearSeries, FormalMultilinearSeries.partialSum,
    Finset.sum_range_succ, mul_comm]

/-! Uniform `q`-expansion bounds on the imaginary axis (for `t ≥ 1`). -/

private lemma hh : (0 : ℝ) < (1 : ℝ) := by norm_num
private lemma hΓ1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma (↑1)).strictPeriods := by simp
private def r0 : ℝ≥0 := ⟨Real.exp (-π), (Real.exp_pos _).le⟩

private lemma exists_sub_partialSum_bound
    {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : F)
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖f (zI t ht) -
          (qExpansionFormalMultilinearSeries (h := (1 : ℝ)) f).partialSum n
            (Periodic.qParam (1 : ℝ) (zI t ht))‖ ≤
        C * (Real.exp (-2 * π * t)) ^ n := by
  obtain ⟨a, ha, C, hCpos, hbound⟩ := (ModularFormClass.hasFPowerSeries_cuspFunction
    (f := f) (h := (1 : ℝ)) hh hΓ).uniform_geometric_approx' (r' := r0)
    (by simpa using ENNReal.coe_lt_one_iff.2 exp_neg_pi_lt_one)
  refine ⟨C * (a / (r0 : ℝ)) ^ n,
    mul_pos hCpos (pow_pos (div_pos ha.1 (Real.exp_pos (-π))) _), fun t ht ht1 => ?_⟩
  let z : ℍ := zI t ht
  let q : ℂ := Periodic.qParam (1 : ℝ) z
  have hqnorm : ‖q‖ = Real.exp (-2 * π * t) := by simpa [q, z] using qParam_zI_norm t ht
  simpa [z, q, hqnorm] using
    (show ‖f z - (qExpansionFormalMultilinearSeries (h := (1 : ℝ)) f).partialSum n q‖ ≤
        (C * (a / (r0 : ℝ)) ^ n) * ‖q‖ ^ n by
      simpa [show cuspFunction (1 : ℝ) f q = f z by
          simpa [q] using SlashInvariantFormClass.eq_cuspFunction (f := f) (τ := z) hΓ one_ne_zero,
        show C * (a * (‖q‖ / r0)) ^ n = (C * (a / (r0 : ℝ)) ^ n) * ‖q‖ ^ n by
          simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_pow]] using
        hbound q (by simpa [Metric.mem_ball, dist_zero_right, r0, q, z, qParam_zI_norm t ht] using
          Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos, ht1])) n)

/-- Uniform bound `‖E₄ (it) - 1‖ = O(exp (-2πt))` valid for all `t ≥ 1`. -/
public lemma exists_E4_sub_one_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖E₄ (zI t ht) - (1 : ℂ)‖ ≤ C * Real.exp (-2 * π * t) :=
  (exists_sub_partialSum_bound (f := E₄) (Γ := CongruenceSubgroup.Gamma (↑1)) (k := 4) hΓ1 1).imp
    fun _ ⟨hCpos, hC⟩ => ⟨hCpos, fun t ht0 ht1 => by
      simpa [qExpansionFormalMultilinearSeries, FormalMultilinearSeries.partialSum, E4_q_exp_zero]
        using hC t ht0 ht1⟩

/--
Second-order remainder bound for `E₄ (it)` after subtracting `1 + 240 q`, where
`q = exp (-2π t)`, valid for all `t ≥ 1`.
-/
public lemma exists_E4_sub_one_sub_240q_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖E₄ (zI t ht) - ((1 : ℂ) + (240 : ℂ) * (Real.exp (-2 * π * t) : ℂ))‖ ≤
        C * (Real.exp (-2 * π * t)) ^ (2 : ℕ) :=
  (exists_sub_partialSum_bound (f := E₄) (Γ := CongruenceSubgroup.Gamma (↑1)) (k := 4) hΓ1 2).imp
    fun _ ⟨hCpos, hC⟩ => ⟨hCpos, fun t ht0 ht1 => by
      simpa [qExpansionFormalMultilinearSeries_partialSum_two (f := E₄), E4_q_exp_zero,
        E4_q_exp_one, qParam_zI t ht0] using hC t ht0 ht1⟩

lemma Delta_q_exp_zero : (qExpansion 1 Delta).coeff 0 = (0 : ℂ) := by
  have hval : valueAtInfty (Delta : ℍ → ℂ) = (0 : ℂ) := by
    simpa using
      (ModularFormClass.cuspFunction_apply_zero (f := Delta) (h := (1 : ℝ)) hh hΓ1).symm.trans
        (CuspFormClass.cuspFunction_apply_zero (f := Delta) (h := (1 : ℝ)) hh hΓ1)
  simp [ModularFormClass.qExpansion_coeff_zero (f := Delta) (h := (1 : ℝ)) hh hΓ1, hval]

/--
Second-order remainder bound for `Δ (it)` after subtracting `q = exp (-2π t)`, valid for all
`t ≥ 1`.
-/
public lemma exists_Delta_sub_q_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖Δ (zI t ht) - (Real.exp (-2 * π * t) : ℂ)‖ ≤
        C * (Real.exp (-2 * π * t)) ^ (2 : ℕ) :=
  (exists_sub_partialSum_bound (f := Delta) (Γ := CongruenceSubgroup.Gamma (↑1)) (k := 12)
      hΓ1 2).imp fun _ ⟨hCpos, hC⟩ => ⟨hCpos, fun t ht0 ht1 => by
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
        C * (Real.exp (-2 * π * t)) ^ (3 : ℕ) :=
  (exists_sub_partialSum_bound (f := Delta) (Γ := CongruenceSubgroup.Gamma (↑1)) (k := 12)
      hΓ1 3).imp fun _ ⟨hCpos, hC⟩ => ⟨hCpos, fun t ht0 ht1 => by
    simpa [qExpansionFormalMultilinearSeries, FormalMultilinearSeries.partialSum,
      Finset.sum_range_succ, mul_comm, Delta_q_exp_zero,
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
  let q1 : ℝ := Real.exp (-2 * π)
  have hq1_nonneg : 0 ≤ q1 := (Real.exp_pos _).le
  have hq1_lt_one : q1 < 1 := exp_neg_two_pi_lt_one
  let b : ℕ → ℝ := fun n => ((n + 2 : ℝ) ^ 5) * q1 ^ n
  have hb_summ : Summable b := by
    have hsummA : Summable (fun n : ℕ => (((n : ℝ) ^ 5 + 1) : ℝ) * q1 ^ n) := by
      simpa [show (fun n : ℕ => (((n : ℝ) ^ 5 + 1) : ℝ) * q1 ^ n) =
          (fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * q1 ^ n) + fun n : ℕ => q1 ^ n by
        funext n; simp [add_mul]] using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5
          (by simpa [Real.norm_of_nonneg hq1_nonneg] using hq1_lt_one)).add
          (summable_geometric_of_lt_one hq1_nonneg hq1_lt_one)
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => (512 : ℝ) * ((((n : ℝ) ^ 5 + 1) : ℝ) * q1 ^ n))
      (g := b) (fun n => by positivity) (fun n => ?_) (hsummA.mul_left (512 : ℝ))
    have hpow : ((n + 2 : ℝ) ^ 5) ≤ (512 : ℝ) * ((n : ℝ) ^ 5 + 1) := by
      have hbase : ((n : ℝ) + (2 : ℝ)) ^ 5 ≤ 2 ^ (5 - 1) * ((n : ℝ) ^ 5 + (2 : ℝ) ^ 5) := by
        simpa using add_pow_le (a := (n : ℝ)) (b := (2 : ℝ)) (by positivity) (by positivity) 5
      have : (0 : ℝ) ≤ (n : ℝ) ^ 5 := by positivity
      grind only
    nlinarith [hpow, pow_nonneg hq1_nonneg n]
  refine ⟨1 + (720 : ℝ) * (∑' n : ℕ, b n), by positivity, ?_⟩
  intro t ht0 ht1
  let z : ℍ := zI t ht0
  let q : ℝ := Real.exp (-2 * π * t)
  have hq_nonneg : 0 ≤ q := (Real.exp_pos _).le
  have hq_le : q ≤ q1 := q_le_q1 (t := t) ht1
  have hqC : (Periodic.qParam (1 : ℝ) z) = (q : ℂ) := by simpa [q, z] using qParam_zI t ht0
  let f : ℕ → ℂ := fun n =>
    ((n + 2 : ℂ) * (σ 3 (n + 2) : ℂ)) * cexp (2 * π * Complex.I * (n + 2 : ℂ) * z)
  have hf_le : ∀ n : ℕ, ‖f n‖ ≤ q ^ (2 : ℕ) * b n := fun n => by
    calc
      ‖f n‖ = ‖((n + 2 : ℂ) * (σ 3 (n + 2) : ℂ))‖ *
            ‖cexp (2 * π * Complex.I * (n + 2 : ℂ) * z)‖ := by simp [f, mul_assoc]
      _ ≤ ((n + 2 : ℝ) ^ 5 : ℝ) * (q ^ (2 : ℕ) * q1 ^ n) := by
            gcongr
            · exact_mod_cast norm_mul_sigma_le (n + 2) (n + 2) le_rfl
            · simpa [show ((2 + n : ℕ) : ℂ) = (n : ℂ) + 2 by push_cast; ring] using
                norm_cexp_mul_le_split (z := z) hq_nonneg hq_le hqC 2 n
      _ = q ^ (2 : ℕ) * b n := by simp [b]; ring
  have hqexp : cexp (2 * π * Complex.I * z) = (q : ℂ) := by simpa [Periodic.qParam] using hqC
  let g : ℕ → ℂ := fun n =>
    (n + 1) * (σ 3 (n + 1)) * cexp (2 * π * Complex.I * (n + 1) * z)
  have hg_summ : Summable g := by
    refine Summable.of_norm_bounded (hb_summ.mul_left q) fun n => ?_
    calc
      ‖g n‖ = ‖((n + 1 : ℂ) * (σ 3 (n + 1) : ℂ))‖ *
            ‖cexp (2 * π * Complex.I * (n + 1) * z)‖ := by simp [g, mul_assoc]
      _ ≤ ((n + 2 : ℝ) ^ 5 : ℝ) * (q * q1 ^ n) := by
            gcongr
            · exact_mod_cast norm_mul_sigma_le (n + 1) (n + 2) (by omega)
            · simpa [pow_one, show ((1 + n : ℕ) : ℂ) = (n : ℂ) + 1 by push_cast; ring] using
                norm_cexp_mul_le_split (z := z) hq_nonneg hq_le hqC 1 n
      _ = q * b n := by simp [b]; ring
  have hsplit :
      (∑' n : ℕ+, n * (σ 3 n) * cexp (2 * π * Complex.I * n * z)) - cexp (2 * π * Complex.I * z) =
        ∑' n : ℕ, f n := by
    rw [show (∑' n : ℕ+, n * (σ 3 n) * cexp (2 * π * Complex.I * n * z)) = ∑' n : ℕ, g n from by
        simpa [g, mul_assoc, mul_left_comm, mul_comm] using
          tsum_pnat_eq_tsum_succ
            (f := fun n : ℕ => (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * n * z)),
      show cexp (2 * π * Complex.I * z) = g 0 by simp [g]]
    refine (sub_eq_iff_eq_add).2 ?_
    rw [show (∑' n : ℕ, f n) + g 0 = g 0 + ∑' n : ℕ, g (n + 1) by
      grind only [tsum_eq_tsum_of_ne_zero_bij]]
    simpa [Finset.range_one] using (hg_summ.sum_add_tsum_nat_add 1).symm
  have hnorm_summ : Summable (fun n : ℕ => ‖f n‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) hf_le (hb_summ.mul_left (q ^ (2 : ℕ)))
  have hmain :
      ‖(E₂ z) * (E₄ z) - (E₆ z) - (720 : ℂ) * (q : ℂ)‖ ≤
        (720 : ℝ) * (q ^ (2 : ℕ)) * (∑' n : ℕ, b n) := by
    rw [show (E₂ z) * (E₄ z) - (E₆ z) - (720 : ℂ) * (q : ℂ) = (720 : ℂ) * (∑' n : ℕ, f n) by
        rw [E₂_mul_E₄_sub_E₆ z,
          ← show (∑' n : ℕ+, n * (σ 3 n) * cexp (2 * π * Complex.I * n * z)) - (q : ℂ) =
            ∑' n : ℕ, f n by simpa [hqexp] using hsplit]
        ring,
      norm_mul, show ‖(720 : ℂ)‖ = 720 by simp, mul_assoc]
    gcongr; exact (norm_tsum_le_tsum_norm hnorm_summ).trans <|
      (hnorm_summ.tsum_le_tsum hf_le (hb_summ.mul_left _)).trans_eq tsum_mul_left
  simpa [z, q] using (show ‖(E₂ z) * (E₄ z) - (E₆ z) - (720 : ℂ) * (Real.exp (-2 * π * t) : ℂ)‖ ≤
        ((720 : ℝ) * (∑' n : ℕ, b n)) * (Real.exp (-2 * π * t)) ^ (2 : ℕ) by
      simpa [q, mul_assoc, mul_left_comm, mul_comm] using hmain).trans
    (mul_le_mul_of_nonneg_right (by linarith : (720 : ℝ) * (∑' n : ℕ, b n) ≤
      1 + (720 : ℝ) * (∑' n : ℕ, b n)) (pow_nonneg hq_nonneg _))

end

end MagicFunction.g.CohnElkies.IntegralReps
