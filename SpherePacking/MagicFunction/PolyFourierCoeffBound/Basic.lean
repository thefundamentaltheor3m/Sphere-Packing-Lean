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

open scoped UpperHalfPlane ArithmeticFunction.sigma BigOperators

open Filter Complex Real Asymptotics ArithmeticFunction

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

section hpoly_aux

include hpoly in
theorem hpoly' : (fun (n : ℕ) ↦ c (n + n₀)) =O[atTop] (fun (n : ℕ) ↦ (n ^ k : ℝ)) := by
  have h_shift : (fun n : ℕ ↦ c (n + n₀)) =O[atTop] (fun n : ℕ ↦ ((n + n₀ : ℤ) : ℝ) ^ k) := by
    simp only [isBigO_iff, eventually_atTop] at hpoly ⊢
    rcases hpoly with ⟨C, m, hCa⟩
    refine ⟨C, (m - n₀).toNat, fun n hn ↦ ?_⟩
    exact hCa (n + n₀) (by grind)
  refine h_shift.trans ?_
  simp only [isBigO_iff, eventually_atTop]
  refine ⟨2 ^ k, n₀.natAbs, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, abs_pow, abs_of_nonneg, Nat.cast_nonneg]
  rw [← mul_pow]
  apply pow_le_pow_left₀ (abs_nonneg _)
  norm_cast
  cases abs_cases (n + n₀ : ℤ) <;> grind

end hpoly_aux

section summable_aux

include hpoly in
lemma summable_norm_mul_rexp_neg_pi_div_two :
    Summable (fun n : ℕ => ‖c (n + n₀)‖ * rexp (-π * n / 2)) := by
  let r : ℂ := cexp (-(π : ℂ) / 2)
  have hr : ‖r‖ < 1 := by
    have : (-(π : ℝ) / 2) < 0 := by nlinarith [Real.pi_pos]
    -- `‖exp z‖ = exp (re z)`.
    simpa [r, Complex.norm_exp] using (Real.exp_lt_one_iff.2 this)
  have hu : (fun n : ℕ => c (n + n₀)) =O[atTop] fun n ↦ (↑(n ^ k) : ℝ) := by
    simpa using (hpoly' (c := c) (n₀ := n₀) (k := k) hpoly)
  have hs : Summable (fun n : ℕ => ‖c (n + n₀) * r ^ n‖) :=
    summable_real_norm_mul_geometric_of_norm_lt_one (k := k) (r := r) hr hu
  refine hs.congr fun n => ?_
  have hpow : ‖r ^ n‖ = rexp (-π * n / 2) := by
    calc
      ‖r ^ n‖ = ‖r‖ ^ n := by simp [norm_pow]
      _ = (rexp (-(π : ℝ) / 2)) ^ n := by simp [r, Complex.norm_exp, div_eq_mul_inv]
      _ = rexp ((n : ℝ) * (-(π : ℝ) / 2)) := by
            simpa using (Real.exp_nat_mul (-(π : ℝ) / 2) n).symm
      _ = rexp (-π * n / 2) := by congr 1; ring
  simp [hpow]

end summable_aux

section calc_aux

-- These could even go in Mathlib... they look useful (if a bit random)

lemma aux_1 (x : ℂ) : norm (cexp (I * x)) = rexp (-x.im) := by
  simpa using (Complex.norm_exp (I * x))

-- Below was written by Bhavik
lemma aux_2 (x : ℂ) : 1 - Real.exp x.re ≤ norm (1 - cexp x) := by
  refine (le_abs_self (1 - Real.exp x.re)).trans ?_
  simpa [Complex.norm_exp] using (abs_norm_sub_norm_le (1 : ℂ) (cexp x))

include hcsum in
lemma aux_3 : Summable fun (i : ℕ) ↦ ‖c (i + n₀) * cexp (↑π * I * i * z)‖ := by
  rw [summable_norm_iff]
  have h := Summable.mul_right (cexp (↑π * I * (n₀ : ℂ) * z))⁻¹ hcsum
  simp only [fouterm] at h
  refine h.congr ?_
  intro i
  have hsplit :
      cexp (↑π * I * (↑(↑i + n₀) : ℂ) * z) =
        cexp (↑π * I * (i : ℂ) * z) * cexp (↑π * I * (n₀ : ℂ) * z) := by
    have harg :
        ↑π * I * (↑(↑i + n₀) : ℂ) * z =
          ↑π * I * (i : ℂ) * z + ↑π * I * (n₀ : ℂ) * z := by
      simp; ring
    simpa [harg.symm] using
      (Complex.exp_add (↑π * I * (i : ℂ) * z) (↑π * I * (n₀ : ℂ) * z))
  have hne : cexp (↑π * I * (n₀ : ℂ) * z) ≠ 0 :=
    Complex.exp_ne_zero (↑π * I * (n₀ : ℂ) * z)
  -- cancel the `n₀` shift in the exponential.
  grind only

include hcsum in
lemma aux_4 : Summable fun (i : ℕ) ↦ norm (c (i + n₀)) *
    norm (cexp (↑π * I * ↑i * z)) := by
  simpa [norm_mul] using aux_3 z c n₀ hcsum

lemma aux_5 (z : ℍ) : norm (∏' (n : ℕ+), (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24) =
  ∏' (n : ℕ+), norm (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 := by
  simpa [← norm_pow] using (Multipliable.norm_tprod (MultipliableDeltaProductExpansion_pnat z))

lemma aux_6 (z : ℍ) : 0 ≤ ∏' (n : ℕ+), norm (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 := by
  simp [← aux_5 z]

lemma aux_7 (a : ℤ) :
    norm (cexp (↑π * I * a * z)) ≤ rexp (-π * a * z.im) := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using le_of_eq (aux_1 (x := (↑π * (a * z))))

lemma aux_tprod_one_sub_rexp_pow_24_pos (c : ℝ) (hc : 0 < c) :
    0 < ∏' (n : ℕ+), (1 - rexp (-c * (n : ℝ))) ^ 24 := by
  rw [← Real.rexp_tsum_eq_tprod]
  · exact Real.exp_pos _
  · intro i
    simp_all
  · have hnat : Summable fun b : ℕ ↦ Real.exp (-c * (b : ℝ)) := by
      -- `Real.summable_exp_nat_mul_iff` is stated for `exp (n * a)`.
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (Real.summable_exp_nat_mul_iff (a := -c)).2 (by nlinarith)
    have hexp : Summable fun b : ℕ+ ↦ Real.exp (-c * (b : ℝ)) := by
      simpa using hnat.comp_injective PNat.coe_injective
    simpa [log_pow, Nat.cast_ofNat, sub_eq_add_neg, smul_eq_mul] using
      (Summable.const_smul (24 : ℝ) (Real.summable_log_one_add_of_summable hexp.neg))

lemma aux_8 : 0 < ∏' (n : ℕ+), (1 - rexp (-2 * π * ↑↑n * z.im)) ^ 24 := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    aux_tprod_one_sub_rexp_pow_24_pos (c := 2 * π * z.im) (by positivity)

lemma aux_ring (i : ℕ) : (I * ↑π * ↑i * z) = I * ((↑π * ↑i) * z) := by
  simp [mul_assoc]

lemma aux_9 (i : ℕ) :
    ‖c (i + n₀) * cexp (↑π * I * ↑i * z)‖ = ‖c (i + n₀)‖ * rexp (-π * ↑i * z.im) := by
  rw [norm_mul, mul_comm (↑π) I, aux_ring, aux_1]
  simp

include hcsum in
lemma aux_10 : Summable fun (n : ℕ) ↦ norm (c (n + n₀)) * rexp (-π * ↑n * z.im) := by
  simp only [← aux_9]
  exact aux_3 z c n₀ hcsum

lemma aux_11 : 0 < ∏' (n : ℕ+), (1 - rexp (-π * ↑↑n)) ^ 24 := by
  simpa using aux_tprod_one_sub_rexp_pow_24_pos (c := π) pi_pos

end calc_aux

section calc_steps

lemma multipliable_pow {ι : Type*} (f : ι → ℝ) (hf : Multipliable f) (n : ℕ) :
    Multipliable (fun i => f i ^ n) := by
  induction n with | zero => simp | succ n hn => simpa [pow_succ] using hn.mul hf

lemma step_7 :
    norm (cexp (π * I * (n₀ - 2) * z)) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    ∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24 ≤
    rexp (-π * (n₀ - 2) * z.im) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · exact_mod_cast aux_7 z (n₀ - 2)

include hcsum in
lemma step_8 :
    rexp (-π * (n₀ - 2) * z.im) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (π * I * n * z))) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · simpa [norm_mul] using norm_tsum_le_tsum_norm (aux_3 z c n₀ hcsum)

include hcsum in
lemma step_9 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (π * I * n * z))) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · exact aux_4 z c n₀ hcsum
  · exact aux_10 z c n₀ hcsum
  · simp [Complex.norm_exp, mul_assoc, mul_left_comm, mul_comm]

lemma step_10 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := by
  gcongr
  · exact aux_8 z
  · apply tprod_le_of_nonneg_of_multipliable
    · intro n
      positivity
    · intro n; simp only [neg_mul]; gcongr
      · simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff]; positivity
      · have hre : -(2 * π * n * z.im) = (2 * π * I * n * z).re := by simp
        rw [hre]; exact aux_2 (2 * π * I * n * z)
    · have h_base : Multipliable (fun b : ℕ+ => 1 - rexp (-2 * π * ↑↑b * z.im)) := by
        apply Real.multipliable_of_summable_log
        · intro i; simp [pi_pos, UpperHalfPlane.im_pos]
        · simp_rw [sub_eq_add_neg]
          apply Real.summable_log_one_add_of_summable
          apply Summable.neg
          conv => lhs; equals (fun (b : ℕ) => Real.exp (-2 * π * b * z.im)) ∘ (PNat.val) => rfl
          apply Summable.subtype
          simp_rw [mul_comm, mul_assoc, Real.summable_exp_nat_mul_iff]
          simp [pi_pos, UpperHalfPlane.im_pos]
      exact multipliable_pow _ h_base 24
    · exact multipliable_pow _ (MultipliableEtaProductExpansion_pnat z).norm 24

include hz hcsum hpoly in
lemma step_11 :
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
  (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) ≤
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := by
  have hg : Summable fun n : ℕ ↦ ‖c (n + n₀)‖ * rexp (-π * n / 2) :=
    summable_norm_mul_rexp_neg_pi_div_two (c := c) (n₀ := n₀) (k := k) hpoly
  have hsum :
      (∑' n : ℕ, ‖c (n + n₀)‖ * rexp (-π * n * z.im)) ≤
        ∑' n : ℕ, ‖c (n + n₀)‖ * rexp (-π * n / 2) := by
    refine Summable.tsum_le_tsum
      (f := fun n : ℕ ↦ ‖c (n + n₀)‖ * rexp (-π * n * z.im))
      (g := fun n : ℕ ↦ ‖c (n + n₀)‖ * rexp (-π * n / 2)) (fun n ↦ ?_)
      (by simpa using aux_10 z c n₀ hcsum) hg
    have hz' : (1 / 2 : ℝ) ≤ z.im := le_of_lt hz
    have hn : 0 ≤ (π : ℝ) * (n : ℝ) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine Real.exp_le_exp.2 ?_
    have := neg_le_neg (mul_le_mul_of_nonneg_left hz' hn)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, neg_mul] using this
  gcongr
  · exact (aux_8 z).le

lemma step_12a {r : ℝ} (hr : 0 < r) :
    Multipliable fun b : ℕ+ ↦ (1 - rexp (-r * (b : ℝ))) ^ 24 := by
  refine Real.multipliable_of_summable_log (fun i ↦ ?_) ?_
  · refine pow_pos (sub_pos.2 (Real.exp_lt_one_iff.2 ?_)) _
    have hi : (0 : ℝ) < (i : ℝ) := by exact_mod_cast i.pos
    nlinarith
  · have hnat : Summable fun b : ℕ ↦ Real.exp (-r * (b : ℝ)) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (Real.summable_exp_nat_mul_iff (a := -r)).2 (by nlinarith)
    have hexp : Summable fun b : ℕ+ ↦ Real.exp (-r * (b : ℝ)) := by
      simpa using hnat.comp_injective PNat.coe_injective
    simpa [log_pow, sub_eq_add_neg, smul_eq_mul] using
      (Summable.const_smul (24 : ℝ) (Real.summable_log_one_add_of_summable hexp.neg))

include hz in
lemma step_12 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
    (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
    (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := by
  gcongr
  · exact aux_11
  · have h0 (n : ℕ+) : 0 ≤ 1 - rexp (-π * (n : ℝ)) := by
      refine sub_nonneg.2 (Real.exp_le_one_iff.2 ?_)
      have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hπ : (-π : ℝ) ≤ 0 := by nlinarith [Real.pi_pos]
      simpa [mul_assoc, mul_comm, mul_left_comm] using mul_nonpos_of_nonpos_of_nonneg hπ hn
    apply tprod_le_of_nonneg_of_multipliable
    · intro n; exact pow_nonneg (h0 n) 24
    · intro n
      refine pow_le_pow_left₀ (h0 n) (sub_le_sub_left ?_ 1) 24
      refine Real.exp_le_exp.2 ?_
      have hz2 : (1 : ℝ) ≤ 2 * z.im := by nlinarith [hz]
      have hn : 0 ≤ (π : ℝ) * (n : ℝ) := by positivity
      have := neg_le_neg (mul_le_mul_of_nonneg_left hz2 hn)
      simpa [mul_assoc, mul_left_comm, mul_comm, mul_one] using this
    · exact step_12a pi_pos
    · simpa [mul_assoc, mul_left_comm, mul_comm] using
        (step_12a (r := 2 * π * z.im) (mul_pos two_pi_pos (UpperHalfPlane.im_pos z)))

end calc_steps

section main_theorem

/-
This section contains the proof of the main result of this file.
-/

include f hf z hz c n₀ hcsum k hpoly in
/-- A uniform bound on `‖(f z) / (Δ z)‖` for a function given by a Fourier series with polynomially
bounded coefficients.

The bound is stated in terms of `DivDiscBound` and an exponential factor depending on the shift
`n₀`.
-/
public theorem DivDiscBoundOfPolyFourierCoeff : norm ((f z) / (Δ z)) ≤
  (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := calc
  _ = norm ((∑' (n : ℕ), c (n + n₀) * cexp (π * I * (n + n₀) * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+),
      (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
        simp [DiscriminantProductFormula, hf, fouterm]
  _ = norm ((cexp (π * I * n₀ * z) * ∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
        congr
        rw [← tsum_mul_left]
        congr
        ext n; ring_nf
        rw [mul_assoc (c (n + n₀)) (cexp _), ← Complex.exp_add]
        congr 2
        ring
  _ = norm ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
        field_simp
  _ = norm ((cexp (π * I * (n₀ - 2) * z)) *
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
        rw [mul_sub, sub_mul, ← Complex.exp_sub]
        congr 6
        ac_rfl
  _ = norm (cexp (π * I * (n₀ - 2) * z)) *
      norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      norm (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) := by
        simp
  _ = norm (cexp (π * I * (n₀ - 2) * z)) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      ∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24 := by
        congr
        exact aux_5 z
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := step_7 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (π * I * n * z))) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := step_8 z c n₀ hcsum
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := step_9 z c n₀ hcsum
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := step_10 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := step_11 z hz c n₀ hcsum k hpoly
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := step_12 z hz c n₀
  _ = (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := by
      simp [DivDiscBound, mul_div_assoc, mul_comm, mul_assoc]

end main_theorem

section positivity

-- Note that this proof does NOT use our custom `summable_norm_pow_mul_geometric_of_norm_lt_one`
-- for functions with real inputs (see SpherePacking.ForMathlib.SpecificLimits).
include hpoly hcn₀ in
public theorem DivDiscBound_pos : 0 < DivDiscBound c n₀ := by
  rw [DivDiscBound]
  refine div_pos ?_ aux_11
  refine
    Summable.tsum_pos
      (summable_norm_mul_rexp_neg_pi_div_two (c := c) (n₀ := n₀) (k := k) hpoly)
      (fun _ => by positivity) 0 ?_
  simpa using (norm_pos_iff.2 hcn₀)

end positivity

end

end MagicFunction.PolyFourierCoeffBound
