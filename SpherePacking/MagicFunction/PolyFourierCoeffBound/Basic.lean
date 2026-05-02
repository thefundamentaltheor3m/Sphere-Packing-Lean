/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.ForMathlib.SpecificLimits
public import SpherePacking.ForMathlib.Tprod
public import SpherePacking.ModularForms.Eisenstein

/-!
# Polynomial Fourier coefficient bounds — core definitions and main bound

This file contains the core definitions and the main quantitative bound
`DivDiscBoundOfPolyFourierCoeff`, which gives an explicit upper bound on the
ratio `‖f / Δ‖` for a function `f : ℍ → ℂ` whose Fourier expansion (in the
`π i` convention) has polynomially bounded coefficients.

This is Lemma 7.4 in the blueprint. Corollaries for the specific magic function
setup live in sibling files under `SpherePacking.MagicFunction.PolyFourierCoeffBound`.

## Main definitions
* `MagicFunction.PolyFourierCoeffBound.fouterm`
* `MagicFunction.PolyFourierCoeffBound.DivDiscBound`

## Main statements
* `MagicFunction.PolyFourierCoeffBound.DivDiscBoundOfPolyFourierCoeff`
* `MagicFunction.PolyFourierCoeffBound.DivDiscBound_pos`
-/

namespace MagicFunction.PolyFourierCoeffBound

noncomputable section

open scoped UpperHalfPlane BigOperators

open Filter Complex Real Asymptotics

/-- A single Fourier term in the `π i` convention.

This is the basic building block used to express `f : ℍ → ℂ` as a Fourier series in `cexp (π * I *
z)`.
-/
@[expose] public def fouterm (coeff : ℤ → ℂ) (x : ℂ) (i : ℤ) : ℂ :=
  (coeff i) * cexp (π * I * i * x)

variable (z : ℍ) (hz : 1 / 2 < z.im) (c : ℤ → ℂ) (n₀ : ℤ) (hcn₀ : c n₀ ≠ 0)
  (hcsum : Summable fun i : ℕ ↦ fouterm c z (i + n₀)) (k : ℕ)
  (hpoly : c =O[atTop] fun n ↦ (n ^ k : ℝ))
  (f : ℍ → ℂ) (hf : ∀ x : ℍ, f x = ∑' n : ℕ, fouterm c x (n + n₀))

/-- A constant bounding the ratio `f / Δ` in terms of Fourier coefficients.

This is the explicit factor which appears in `DivDiscBoundOfPolyFourierCoeff`.
-/
public def DivDiscBound : ℝ :=
  (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24)

section summable_aux

include hpoly in
lemma summable_norm_mul_rexp_neg_pi_div_two :
    Summable (fun n : ℕ => ‖c (n + n₀)‖ * rexp (-π * n / 2)) := by
  refine (summable_real_norm_mul_geometric_of_norm_lt_one (k := k) (r := cexp (-(π : ℂ) / 2))
    (by simpa [Complex.norm_exp] using
      Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos] : (-(π : ℝ) / 2) < 0)) (by
    simpa using ((show (fun n : ℕ ↦ c (n + n₀)) =O[atTop]
        (fun n : ℕ ↦ ((n + n₀ : ℤ) : ℝ) ^ k) by
      simp only [isBigO_iff, eventually_atTop] at hpoly ⊢
      obtain ⟨C, m, hCa⟩ := hpoly
      exact ⟨C, (m - n₀).toNat, fun n _ ↦ hCa (n + n₀) (by grind)⟩).trans (by
      simp only [isBigO_iff, eventually_atTop]
      exact ⟨2 ^ k, n₀.natAbs, fun n _ ↦ by
        simp only [Real.norm_eq_abs, abs_pow, abs_of_nonneg, Nat.cast_nonneg, ← mul_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (by
          norm_cast; cases abs_cases (n + n₀ : ℤ) <;> grind) _⟩)))).congr fun n => ?_
  rw [norm_mul, norm_pow, show ‖cexp (-(π : ℂ) / 2)‖ = rexp (-(π : ℝ) / 2) by
      simp [Complex.norm_exp, div_eq_mul_inv], ← Real.exp_nat_mul]
  congr 2; ring

end summable_aux

section calc_aux

include hcsum in
lemma aux_3 : Summable fun (i : ℕ) ↦ ‖c (i + n₀) * cexp (↑π * I * i * z)‖ :=
  summable_norm_iff.mpr <|
    (Summable.mul_right (cexp (↑π * I * (n₀ : ℂ) * z))⁻¹ hcsum).congr fun i => by
      simp only [fouterm, show cexp (↑π * I * (↑(↑i + n₀) : ℂ) * z) =
          cexp (↑π * I * (i : ℂ) * z) * cexp (↑π * I * (n₀ : ℂ) * z) by
        rw [← Complex.exp_add]; congr 1; push_cast; ring]
      field_simp [Complex.exp_ne_zero]

lemma aux_5 (z : ℍ) : norm (∏' (n : ℕ+), (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24) =
    ∏' (n : ℕ+), norm (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 := by
  simpa [← norm_pow] using Multipliable.norm_tprod (MultipliableDeltaProductExpansion_pnat z)

lemma aux_6 (z : ℍ) : 0 ≤ ∏' (n : ℕ+), norm (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 :=
  (aux_5 z).symm ▸ norm_nonneg _

lemma aux_tprod_one_sub_rexp_pow_24_pos (c : ℝ) (hc : 0 < c) :
    0 < ∏' (n : ℕ+), (1 - rexp (-c * (n : ℝ))) ^ 24 := by
  rw [← Real.rexp_tsum_eq_tprod (fun i ↦ by simp_all)]
  exacts [Real.exp_pos _,
    by simpa [log_pow, Nat.cast_ofNat, sub_eq_add_neg, smul_eq_mul] using
      Summable.const_smul (24 : ℝ) (Real.summable_log_one_add_of_summable ((by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          ((Real.summable_exp_nat_mul_iff (a := -c)).2 (by nlinarith)).comp_injective
            PNat.coe_injective :
        Summable fun b : ℕ+ ↦ Real.exp (-c * (b : ℝ))).neg))]

lemma aux_8 : 0 < ∏' (n : ℕ+), (1 - rexp (-2 * π * ↑↑n * z.im)) ^ 24 := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    aux_tprod_one_sub_rexp_pow_24_pos (c := 2 * π * z.im) (by positivity)

include hcsum in
lemma aux_10 : Summable fun (n : ℕ) ↦ norm (c (n + n₀)) * rexp (-π * ↑n * z.im) := by
  refine (aux_3 z c n₀ hcsum).congr fun i => ?_
  rw [norm_mul, show (↑π * I * (i : ℂ) * z) = I * ((↑π * i) * z) by ring, Complex.norm_exp]; simp

lemma aux_11 : 0 < ∏' (n : ℕ+), (1 - rexp (-π * ↑↑n)) ^ 24 := by
  simpa using aux_tprod_one_sub_rexp_pow_24_pos (c := π) pi_pos

lemma multipliable_pow {ι : Type*} (f : ι → ℝ) (hf : Multipliable f) (n : ℕ) :
    Multipliable (fun i => f i ^ n) := by
  induction n with | zero => simp | succ n hn => simpa [pow_succ] using hn.mul hf

lemma step_12a {r : ℝ} (hr : 0 < r) :
    Multipliable fun b : ℕ+ ↦ (1 - rexp (-r * (b : ℝ))) ^ 24 := by
  refine Real.multipliable_of_summable_log (fun i ↦ ?_) ?_
  · refine pow_pos (sub_pos.2 (Real.exp_lt_one_iff.2 ?_)) _
    nlinarith [show (0 : ℝ) < (i : ℝ) from mod_cast i.pos]
  simpa [log_pow, sub_eq_add_neg, smul_eq_mul] using Summable.const_smul (24 : ℝ)
    (Real.summable_log_one_add_of_summable ((by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        ((Real.summable_exp_nat_mul_iff (a := -r)).2 (by nlinarith)).comp_injective
          PNat.coe_injective :
      Summable fun b : ℕ+ ↦ Real.exp (-r * (b : ℝ))).neg))

lemma step_10 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := by
  gcongr
  · exact aux_8 z
  refine tprod_le_of_nonneg_of_multipliable (fun n => by positivity) (fun n => ?_) ?_
    (multipliable_pow _ (MultipliableEtaProductExpansion_pnat z).norm 24)
  · simp only [neg_mul]; gcongr
    · simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff]; positivity
    · rw [show -(2 * π * n * z.im) = (2 * π * I * n * z).re by simp]
      exact (le_abs_self _).trans <| by
        simpa [Complex.norm_exp] using abs_norm_sub_norm_le (1 : ℂ) (cexp (2 * π * I * n * z))
  · simpa [mul_assoc, mul_left_comm, mul_comm] using
      step_12a (r := 2 * π * z.im) (mul_pos two_pi_pos (UpperHalfPlane.im_pos z))

include hz hcsum hpoly in
lemma step_11 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
    (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := by
  gcongr ?_ * ?_ / _
  · exact (aux_8 z).le
  refine Summable.tsum_le_tsum (fun n ↦ mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 ?_) (norm_nonneg _)) (aux_10 z c n₀ hcsum)
    (summable_norm_mul_rexp_neg_pi_div_two (c := c) (n₀ := n₀) (k := k) hpoly)
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, neg_mul] using
    neg_le_neg (mul_le_mul_of_nonneg_left hz.le (by positivity : 0 ≤ (π : ℝ) * (n : ℝ)))

include hz in
lemma step_12 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
    (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
    (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := by
  have h0 (n : ℕ+) : 0 ≤ 1 - rexp (-π * (n : ℝ)) :=
    sub_nonneg.2 <| Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, n.pos])
  gcongr
  · exact aux_11
  refine tprod_le_of_nonneg_of_multipliable (fun n => pow_nonneg (h0 n) 24) (fun n =>
    pow_le_pow_left₀ (h0 n) (sub_le_sub_left (Real.exp_le_exp.2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm, mul_one] using
        neg_le_neg (mul_le_mul_of_nonneg_left (by nlinarith [hz] : (1 : ℝ) ≤ 2 * z.im)
          (by positivity : 0 ≤ (π : ℝ) * (n : ℝ))))) 1) 24)
    (step_12a pi_pos)
    (by simpa [mul_assoc, mul_left_comm, mul_comm] using
      step_12a (r := 2 * π * z.im) (mul_pos two_pi_pos (UpperHalfPlane.im_pos z)))

end calc_aux

section main_theorem

include f hf z hz c n₀ hcsum k hpoly in
/-- A uniform bound on `‖(f z) / (Δ z)‖` for a function given by a Fourier series with polynomially
bounded coefficients, in terms of `DivDiscBound` and an exponential factor depending on `n₀`. -/
public theorem DivDiscBoundOfPolyFourierCoeff : norm ((f z) / (Δ z)) ≤
  (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := calc
  _ = norm ((∑' (n : ℕ), c (n + n₀) * cexp (π * I * (n + n₀) * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
        simp [DiscriminantProductFormula, hf, fouterm]
  _ = norm ((cexp (π * I * n₀ * z) * ∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
        congr; rw [← tsum_mul_left]; refine tsum_congr fun n => ?_
        rw [mul_left_comm, ← Complex.exp_add]; congr 2; ring
  _ = norm ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by field_simp
  _ = norm ((cexp (π * I * (n₀ - 2) * z)) *
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
        rw [mul_sub, sub_mul, ← Complex.exp_sub]; congr 6; ac_rfl
  _ = norm (cexp (π * I * (n₀ - 2) * z)) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      ∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24 := by simp [← aux_5 z]
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
        gcongr; exacts [aux_6 z, by simp [Complex.norm_exp, mul_assoc, mul_left_comm, mul_comm]]
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (π * I * n * z))) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
        gcongr
        exacts [aux_6 z, by simpa [norm_mul] using norm_tsum_le_tsum_norm (aux_3 z c n₀ hcsum)]
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
        gcongr; exacts [aux_6 z, by simpa [norm_mul] using aux_3 z c n₀ hcsum,
          aux_10 z c n₀ hcsum, by simp [Complex.norm_exp, mul_assoc, mul_left_comm, mul_comm]]
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := step_10 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := step_11 z hz c n₀ hcsum k hpoly
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := step_12 z hz c n₀
  _ = (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := by
      simp [DivDiscBound, mul_div_assoc, mul_comm, mul_assoc]

include hpoly hcn₀ in
public theorem DivDiscBound_pos : 0 < DivDiscBound c n₀ := by
  rw [DivDiscBound]
  refine div_pos (Summable.tsum_pos
    (summable_norm_mul_rexp_neg_pi_div_two (c := c) (n₀ := n₀) (k := k) hpoly)
    (fun _ => by positivity) 0 ?_) aux_11
  simpa using norm_pos_iff.2 hcn₀

end main_theorem

end

end MagicFunction.PolyFourierCoeffBound
