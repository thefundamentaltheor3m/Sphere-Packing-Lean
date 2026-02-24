/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

module
public import SpherePacking.ForMathlib.SpecificLimits
public import SpherePacking.ForMathlib.tprod
public import SpherePacking.ModularForms.Eisenstein
public import Mathlib.Data.Finset.NatAntidiagonal


/-!
# Fourier expansion for `(E₂ * E₄ - E₆)^2`

We rewrite Bhavik's `ℕ+`-Fourier expansion of `E₂ * E₄ - E₆` into an `ℕ`-series, then square it
using the Cauchy product formula for `tsum` on `ℕ` (antidiagonal reindexing). Finally we convert
the resulting `2π i`-Fourier series into the `π i`-convention used by `fouterm` by forcing the odd
indices to vanish. This is Lemma 7.4 in the blueprint: an upper bound on the ratio between any
function whose Fourier coefficients are `O(n^k)` and its discriminant.

## Main definitions
* `MagicFunction.PolyFourierCoeffBound.fouterm`
* `MagicFunction.PolyFourierCoeffBound.DivDiscBound`

## Main statements
* `MagicFunction.PolyFourierCoeffBound.DivDiscBoundOfPolyFourierCoeff`
* `MagicFunction.PolyFourierCoeffBound.norm_φ₀_le`
-/

namespace MagicFunction.PolyFourierCoeffBound

noncomputable section

open scoped UpperHalfPlane ArithmeticFunction.sigma BigOperators

open Filter Complex Real Asymptotics ArithmeticFunction

/-- A single Fourier term in the `π i` convention.

This is the basic building block used to express `f : ℍ → ℂ` as a Fourier series in `cexp (π * I *
z)`.
-/
public def fouterm (coeff : ℤ → ℂ) (x : ℂ) (i : ℤ) : ℂ :=
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
  have h_shift : (fun n : ℕ => c (n + n₀)) =O[atTop] (fun n : ℕ => (n + n₀ : ℂ) ^ k) := by
    simp only [isBigO_iff, eventually_atTop] at hpoly ⊢
    obtain ⟨C, m, hCa⟩ := hpoly
    use C
    simp only [norm_pow, norm_eq_abs] at hCa ⊢
    refine ⟨(m - n₀).toNat, fun n hn ↦ ?_⟩
    exact_mod_cast hCa (n + n₀) (by grind)
  refine h_shift.trans ?_
  simp only [isBigO_iff, eventually_atTop]
  use 2 ^ k
  simp only [norm_pow, RCLike.norm_natCast]
  refine ⟨n₀.natAbs, fun n hn => ?_⟩
  rw [← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
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
      _ = rexp (-π * n / 2) := by
            congr 1
            ring
  simp [hpow]

end summable_aux

section calc_aux

-- These could even go in Mathlib... they look useful (if a bit random)

lemma aux_1 (x : ℂ) : norm (cexp (I * x)) = rexp (-x.im) := by
  simpa using (Complex.norm_exp (I * x))

-- Below was written by Bhavik
lemma aux_2 (x : ℂ) : 1 - Real.exp x.re ≤ norm (1 - cexp x) := calc
  norm (1 - cexp x) ≥ |‖(1 : ℂ)‖ - norm (cexp x)| := abs_norm_sub_norm_le 1 (cexp x)
  _ = |1 - rexp x.re| := by simp [Complex.norm_exp]
  _ ≥ _ := le_abs_self _

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
    -- rewrite the exponent as a sum, then apply `exp_add`.
    -- (`rw` is more reliable here than `simpa`.)
    rw [harg]
    simpa using
      (Complex.exp_add (↑π * I * (i : ℂ) * z) (↑π * I * (n₀ : ℂ) * z))
  have hne : cexp (↑π * I * (n₀ : ℂ) * z) ≠ 0 :=
    Complex.exp_ne_zero (↑π * I * (n₀ : ℂ) * z)
  -- cancel the `n₀` shift in the exponential.
  calc
    c (↑i + n₀) * cexp (↑π * I * (↑(↑i + n₀) : ℂ) * z) * (cexp (↑π * I * (n₀ : ℂ) * z))⁻¹ =
        c (↑i + n₀) * (cexp (↑π * I * (i : ℂ) * z) * cexp (↑π * I * (n₀ : ℂ) * z)) *
          (cexp (↑π * I * (n₀ : ℂ) * z))⁻¹ := by
        simpa [mul_assoc] using
          congrArg (fun w ↦ c (↑i + n₀) * w * (cexp (↑π * I * (n₀ : ℂ) * z))⁻¹) hsplit
    _ = c (↑i + n₀) * cexp (↑π * I * (i : ℂ) * z) := by
        simp [mul_assoc]

include hcsum in
lemma aux_4 : Summable fun (i : ℕ) ↦ norm (c (i + n₀)) *
    norm (cexp (↑π * I * ↑i * z)) := by
  simpa [norm_mul] using aux_3 z c n₀ hcsum

lemma aux_5 (z : ℍ) : norm (∏' (n : ℕ+), (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24) =
  ∏' (n : ℕ+), norm (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 := by
  simpa [← norm_pow] using
    (Multipliable.norm_tprod (MultipliableDeltaProductExpansion_pnat z))

lemma aux_6 (z : ℍ) : 0 ≤ ∏' (n : ℕ+), norm (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 := by
  rw [← aux_5 z]
  exact norm_nonneg _

lemma aux_7 (a : ℤ) :
    norm (cexp (↑π * I * a * z)) ≤ rexp (-π * a * z.im) := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (le_of_eq (aux_1 (x := (↑π * (a * z)))))

lemma aux_tprod_one_sub_rexp_pow_24_pos (c : ℝ) (hc : 0 < c) :
    0 < ∏' (n : ℕ+), (1 - rexp (-c * (n : ℝ))) ^ 24 := by
  rw [← Real.rexp_tsum_eq_tprod]
  · exact Real.exp_pos _
  · intro i
    refine pow_pos (sub_pos.2 ?_) _
    refine Real.exp_lt_one_iff.2 (by
      have : (0 : ℝ) < (i : ℝ) := by exact_mod_cast i.pos
      nlinarith)
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
    (aux_tprod_one_sub_rexp_pow_24_pos (c := 2 * π * z.im) (by positivity))

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
  · calc
      ‖∑' n : ℕ, c (n + n₀) * cexp (π * I * n * z)‖
          ≤ ∑' n : ℕ, ‖c (n + n₀) * cexp (π * I * n * z)‖ := by
            exact norm_tsum_le_tsum_norm (aux_3 z c n₀ hcsum)
      _ = ∑' n : ℕ, ‖c (n + n₀)‖ * ‖cexp (π * I * n * z)‖ := by
            simp

include hcsum in
lemma step_9 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (π * I * n * z))) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · exact (aux_4 z c n₀ hcsum)
  · exact aux_10 z c n₀ hcsum
  · next j =>
    simp [Complex.norm_exp, mul_assoc, mul_left_comm, mul_comm]

lemma step_10 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) :=
by
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
    refine
      Summable.tsum_le_tsum (f := fun n : ℕ ↦ ‖c (n + n₀)‖ * rexp (-π * n * z.im))
        (g := fun n : ℕ ↦ ‖c (n + n₀)‖ * rexp (-π * n / 2)) (fun n ↦ ?_)
        (by simpa using aux_10 z c n₀ hcsum) hg
    have hn0 : 0 ≤ ‖c (n + n₀)‖ := norm_nonneg _
    refine mul_le_mul_of_nonneg_left ?_ hn0
    refine Real.exp_le_exp.2 ?_
    have hz' : (1 / 2 : ℝ) ≤ z.im := le_of_lt hz
    have hn : 0 ≤ (π : ℝ) * (n : ℝ) := by positivity
    have hmul : (π : ℝ) * (n : ℝ) * 2⁻¹ ≤ (π : ℝ) * (n : ℝ) * z.im := by
      have := mul_le_mul_of_nonneg_left hz' hn
      simpa [mul_assoc, mul_left_comm, mul_comm, one_div] using this
    have := neg_le_neg hmul
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, neg_mul, one_div] using this
  have hD0 :
      0 ≤ (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24)⁻¹ := by
    exact inv_nonneg.2 (le_of_lt (aux_8 z))
  have hA0 : 0 ≤ rexp (-π * (n₀ - 2) * z.im) := by positivity
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hA0) hD0

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
  · apply tprod_le_of_nonneg_of_multipliable
    · intro n
      positivity
    · intro n
      have h0 : 0 ≤ 1 - rexp (-π * (n : ℝ)) := by
        refine sub_nonneg.2 (Real.exp_le_one_iff.2 ?_)
        have hn : (0 : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (Nat.zero_le (n : ℕ))
        have hπ : (-π : ℝ) ≤ 0 := by nlinarith [Real.pi_pos]
        exact mul_nonpos_of_nonpos_of_nonneg hπ hn
      refine pow_le_pow_left₀ h0 (sub_le_sub_left ?_ 1) 24
      refine Real.exp_le_exp.2 ?_
      have hz2 : (1 : ℝ) ≤ 2 * z.im := by nlinarith [hz]
      have hn : 0 ≤ (π : ℝ) * (n : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left hz2 hn
      simpa [mul_assoc, mul_left_comm, mul_comm, mul_one] using (neg_le_neg this)
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
theorem DivDiscBound_pos : 0 < DivDiscBound c n₀ := by
  rw [DivDiscBound]
  refine div_pos ?_ aux_11
  have hs :
      Summable (fun n : ℕ => ‖c (n + n₀)‖ * rexp (-π * n / 2)) :=
    summable_norm_mul_rexp_neg_pi_div_two (c := c) (n₀ := n₀) (k := k) hpoly
  refine Summable.tsum_pos hs ?_ 0 ?_
  · intro n; positivity
  · simpa using (norm_pos_iff.2 hcn₀)

end positivity

section Corollaries


def A_E_sq_coeff (m : ℕ) : ℂ :=
  ∑ p ∈ Finset.antidiagonal m, A_E_coeff p.1 * A_E_coeff p.2

lemma norm_A_E_coeff_le (n : ℕ) :
    ‖A_E_coeff n‖ ≤ (720 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 5 := by
  have hσ : (σ 3 (n + 1) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 4 := by
    exact_mod_cast (sigma_bound 3 (n + 1))
  calc
    ‖A_E_coeff n‖ = (720 : ℝ) * ((n + 1 : ℕ) : ℝ) * (σ 3 (n + 1) : ℝ) := by
      simpa using (norm_A_E_coeff (n := n))
    _ ≤ (720 : ℝ) * ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 4 := by
          gcongr
    _ = (720 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 5 := by
      simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

lemma norm_A_E_coeff_le_of_le {n m : ℕ} (hn : n ≤ m) :
    ‖A_E_coeff n‖ ≤ (720 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 5 := by
  refine (norm_A_E_coeff_le (n := n)).trans ?_
  have hnm : ((n + 1 : ℕ) : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ hn
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hnm 5) (by positivity)

lemma norm_A_E_sq_coeff_le (m : ℕ) :
    ‖A_E_sq_coeff m‖ ≤ (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 11 := by
  -- Crude bound: each factor is `≤ 720 * (m+1)^5`, there are `m+1` terms.
  have hterm (p : ℕ × ℕ) (hp : p ∈ Finset.antidiagonal m) :
      ‖A_E_coeff p.1 * A_E_coeff p.2‖ ≤ (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10 := by
    have hsum : p.1 + p.2 = m := by
      simpa [Finset.mem_antidiagonal] using hp
    have hp₁ : p.1 ≤ m := by
      have : p.1 ≤ p.1 + p.2 := Nat.le_add_right _ _
      simpa [hsum] using this
    have hp₂ : p.2 ≤ m := by
      have : p.2 ≤ p.1 + p.2 := Nat.le_add_left _ _
      simpa [hsum] using this
    have hA₁ : ‖A_E_coeff p.1‖ ≤ (720 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 5 :=
      norm_A_E_coeff_le_of_le hp₁
    have hA₂ : ‖A_E_coeff p.2‖ ≤ (720 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 5 :=
      norm_A_E_coeff_le_of_le hp₂
    calc
      ‖A_E_coeff p.1 * A_E_coeff p.2‖
          = ‖A_E_coeff p.1‖ * ‖A_E_coeff p.2‖ := by simp
      _ ≤ ((720 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 5) * ((720 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 5) := by
            gcongr
      _ = (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10 := by
            ring_nf
  -- Use triangle inequality to bound the sum by the sum of norms.
  calc
    ‖A_E_sq_coeff m‖
        = ‖∑ p ∈ Finset.antidiagonal m, A_E_coeff p.1 * A_E_coeff p.2‖ := by
            simp [A_E_sq_coeff]
    _ ≤ ∑ p ∈ Finset.antidiagonal m, ‖A_E_coeff p.1 * A_E_coeff p.2‖ := by
            simpa using (norm_sum_le (Finset.antidiagonal m)
              (fun p => A_E_coeff p.1 * A_E_coeff p.2))
    _ ≤ ∑ p ∈ Finset.antidiagonal m, (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10 := by
            refine Finset.sum_le_sum ?_
            intro p hp
            exact hterm p hp
    _ = ((Finset.antidiagonal m).card : ℝ) * ((720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10) := by
            -- `∑ _ ∈ s, c = card(s) * c`.
            simp [Finset.sum_const, nsmul_eq_mul]
    _ = ((m + 1 : ℕ) : ℝ) * ((720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10) := by
            simp [Finset.Nat.card_antidiagonal]
    _ = (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 11 := by
            simp [mul_assoc, mul_comm, pow_succ]

lemma A_E_sq_eq_tsum (z : ℍ) :
    (A_E z) ^ 2 =
      ∑' m : ℕ, A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
  -- Let `t n = a_n * exp(2πi (n+1) z)`.
  let t : ℕ → ℂ := fun n => A_E_term z n
  have hA : A_E z = ∑' n : ℕ, t n := by simpa [t] using A_E_eq_tsum (z := z)
  -- Summability of `‖t n‖` follows from polynomial growth of coefficients and exponential decay.
  have ht_norm : Summable (fun n : ℕ => ‖t n‖) := by
    -- Compare to `((n+1)^5) * r^(n+1)` with `r = exp(-2π z.im)`.
    let r : ℝ := Real.exp (-2 * Real.pi * z.im)
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr : ‖r‖ < 1 := by
      have hz : (-2 * Real.pi * z.im) < 0 := by
        have : 0 < z.im := UpperHalfPlane.im_pos z
        nlinarith [Real.pi_pos, this]
      simpa [r, Real.norm_of_nonneg hr0] using (Real.exp_lt_one_iff.2 hz)
    let g : ℕ → ℝ := fun n => (720 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 5 * r ^ (n + 1)
    have hg : Summable g := by
      have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * r ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5 hr
      have hs' :
          Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 5 * r ^ (n + 1)) := by
        simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff (f := fun n : ℕ =>
          ((n : ℝ) ^ 5 : ℝ) * r ^ n) 1).2 hs
      simpa [g, mul_assoc, mul_left_comm, mul_comm] using (hs'.mul_left (720 : ℝ))
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hg
    intro n
    have hexp :
        ‖cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))‖ ≤ r ^ (n + 1) := by
      -- Directly compute the norm of the exponential and rewrite as a geometric term.
      have hnorm :
          ‖cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))‖ =
            rexp (-2 * π * ((n + 1 : ℕ) : ℝ) * z.im) := by
        -- `‖exp(w)‖ = exp(re w)` and `re (2π i (n+1) z) = -2π (n+1) im z`.
        simp [Complex.norm_exp, mul_re, mul_im, mul_assoc, mul_left_comm, mul_comm]
      have hrpow :
          rexp (-2 * π * ((n + 1 : ℕ) : ℝ) * z.im) = r ^ (n + 1) := by
        -- `exp(-2π (n+1) im z) = (exp(-2π im z))^(n+1)`.
        have hrew :
            -2 * π * ((n + 1 : ℕ) : ℝ) * z.im = ((n + 1 : ℕ) : ℝ) * (-2 * π * z.im) := by
          ac_rfl
        calc
          rexp (-2 * π * ((n + 1 : ℕ) : ℝ) * z.im)
              = rexp (((n + 1 : ℕ) : ℝ) * (-2 * π * z.im)) := by
                    simpa using congrArg Real.exp hrew
          _ = rexp (-2 * π * z.im) ^ (n + 1) := by
                -- `exp ((n+1) * x) = exp x ^ (n+1)`.
                simpa using (Real.exp_nat_mul (-2 * π * z.im) (n + 1))
          _ = r ^ (n + 1) := by simp [r]
      exact le_of_eq (hnorm.trans hrpow)
    have hcoeff : ‖A_E_coeff n‖ ≤ (720 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 5 :=
      norm_A_E_coeff_le (n := n)
    calc
      ‖t n‖ = ‖A_E_coeff n * cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))‖ := by
        simp [t, A_E_term]
      _ = ‖A_E_coeff n‖ * ‖cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))‖ := by
        simp
      _ ≤ ((720 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 5) * (r ^ (n + 1)) := by
        exact mul_le_mul hcoeff hexp (norm_nonneg _) (by positivity)
      _ = g n := by
        simp [g, mul_assoc, mul_comm]
  -- Apply the Cauchy product formula.
  have hprod :
      (∑' n : ℕ, t n) * (∑' n : ℕ, t n) =
        ∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, t p.1 * t p.2 := by
    simpa using (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ht_norm ht_norm)
  -- Rewrite the antidiagonal terms.
  have hanti (m : ℕ) :
      (∑ p ∈ Finset.antidiagonal m, t p.1 * t p.2) =
        A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
    -- Expand `t` and use `p.1 + p.2 = m`.
    have hmul (p : ℕ × ℕ) (hp : p ∈ Finset.antidiagonal m) :
        t p.1 * t p.2 =
          (A_E_coeff p.1 * A_E_coeff p.2) *
            cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
      have hm : p.1 + p.2 = m := by
        simpa [Finset.mem_antidiagonal] using hp
      -- `exp(u) * exp(v) = exp(u+v)` and `p.1+p.2=m`.
      let e₁ : ℂ := cexp (2 * π * I * ((p.1 + 1 : ℕ) : ℂ) * (z : ℂ))
      let e₂ : ℂ := cexp (2 * π * I * ((p.2 + 1 : ℕ) : ℂ) * (z : ℂ))
      have hexp : e₁ * e₂ = cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
        have hadd : (p.1 + 1 : ℕ) + (p.2 + 1 : ℕ) = m + 2 := by omega
        have hcast :
            ((p.1 + 1 : ℕ) : ℂ) + ((p.2 + 1 : ℕ) : ℂ) = ((m + 2 : ℕ) : ℂ) := by
          simpa [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℂ)) hadd
        let u : ℂ := 2 * π * I * ((p.1 + 1 : ℕ) : ℂ) * (z : ℂ)
        let v : ℂ := 2 * π * I * ((p.2 + 1 : ℕ) : ℂ) * (z : ℂ)
        have huv : u + v = 2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ) := by
          dsimp [u, v]
          -- Combine coefficients using `hcast`.
          calc
            (2 * π * I * ((p.1 + 1 : ℕ) : ℂ) * (z : ℂ)) +
                (2 * π * I * ((p.2 + 1 : ℕ) : ℂ) * (z : ℂ))
                = 2 * π * I * ((((p.1 + 1 : ℕ) : ℂ) + ((p.2 + 1 : ℕ) : ℂ)) * (z : ℂ)) := by
                    simp [mul_assoc, mul_add, add_mul]
            _ = 2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ) := by
                    simpa [mul_assoc] using congrArg (fun x : ℂ => 2 * π * I * (x * (z : ℂ))) hcast
        have : cexp u * cexp v = cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
          calc
            cexp u * cexp v = cexp (u + v) := by
              exact (Complex.exp_add u v).symm
            _ = cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by simp [huv]
        simpa [e₁, e₂, u, v] using this
      -- Expand `t` and use `hexp`.
      dsimp [t, A_E_term, e₁, e₂]
      calc
        (A_E_coeff p.1 * cexp (2 * π * I * ((p.1 + 1 : ℕ) : ℂ) * (z : ℂ))) *
            (A_E_coeff p.2 * cexp (2 * π * I * ((p.2 + 1 : ℕ) : ℂ) * (z : ℂ)))
            = (A_E_coeff p.1 * A_E_coeff p.2) * (e₁ * e₂) := by
                simp [e₁, e₂, mul_assoc, mul_left_comm, mul_comm]
        _ = (A_E_coeff p.1 * A_E_coeff p.2) *
              cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
                simp [hexp]
    calc
      (∑ p ∈ Finset.antidiagonal m, t p.1 * t p.2)
          = ∑ p ∈ Finset.antidiagonal m,
              (A_E_coeff p.1 * A_E_coeff p.2) *
                cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
                refine Finset.sum_congr rfl ?_
                intro p hp
                exact hmul p hp
      _ = (∑ p ∈ Finset.antidiagonal m, A_E_coeff p.1 * A_E_coeff p.2) *
            cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
            simp [Finset.sum_mul, mul_assoc]
      _ = A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
            simp [A_E_sq_coeff, mul_assoc]
  -- Finish.
  calc
    (A_E z) ^ 2 = (∑' n : ℕ, t n) ^ 2 := by simp [hA]
    _ = (∑' n : ℕ, t n) * (∑' n : ℕ, t n) := by simp [pow_two]
    _ = ∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, t p.1 * t p.2 := by simp [hprod]
    _ = ∑' m : ℕ, A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) :=
          tsum_congr hanti

/-!
### Converting to `fouterm` coefficients

`DivDiscBoundOfPolyFourierCoeff` expects a `π i`-Fourier series with coefficients indexed by `ℤ`.
The expansion `A_E_sq_eq_tsum` is a `2π i`-series indexed by `ℕ`. We convert by forcing odd
indices to vanish and matching even indices.
-/

noncomputable def A_E_sq_fourierCoeff : ℤ → ℂ
  | (Int.ofNat j) =>
      if 4 ≤ j ∧ Even j then A_E_sq_coeff (j / 2 - 2) else 0
  | (Int.negSucc _) => 0

lemma A_E_sq_fourierCoeff_four_ne_zero : A_E_sq_fourierCoeff 4 ≠ 0 := by
  have hcond : 4 ≤ (4 : ℕ) ∧ Even (4 : ℕ) := by decide
  have hc4 : A_E_sq_fourierCoeff 4 = (720 : ℂ) ^ 2 := by
    -- Unfold the definition at `4` and compute `(4 / 2 - 2) = 0`.
    simp [A_E_sq_fourierCoeff, hcond, A_E_sq_coeff, A_E_coeff, pow_two]
  rw [hc4]
  exact pow_ne_zero 2 (by norm_num : (720 : ℂ) ≠ 0)

lemma norm_A_E_sq_fourierCoeff_ofNat_le (j : ℕ) (hj : 4 ≤ j) :
    ‖A_E_sq_fourierCoeff (Int.ofNat j)‖ ≤ (720 : ℝ) ^ 2 * (j : ℝ) ^ 11 := by
  by_cases hjEven : Even j
  · have hcond : 4 ≤ j ∧ Even j := ⟨hj, hjEven⟩
    have hmle : j / 2 - 2 + 1 ≤ j := by omega
    have hpow :
        ((j / 2 - 2 + 1 : ℕ) : ℝ) ^ 11 ≤ (j : ℝ) ^ 11 :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hmle) 11
    have h0 := norm_A_E_sq_coeff_le (m := (j / 2 - 2))
    calc
      ‖A_E_sq_fourierCoeff (Int.ofNat j)‖ = ‖A_E_sq_coeff (j / 2 - 2)‖ := by
        simp [A_E_sq_fourierCoeff, hcond]
      _ ≤ (720 : ℝ) ^ 2 * ((j / 2 - 2 + 1 : ℕ) : ℝ) ^ 11 := by
        simpa using h0
      _ ≤ (720 : ℝ) ^ 2 * (j : ℝ) ^ 11 := by
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (720 : ℝ) ^ 2 * (j : ℝ) ^ 11 := rfl
  · have hcond : ¬(4 ≤ j ∧ Even j) := by
      intro h
      exact hjEven h.2
    have hnonneg : 0 ≤ (720 : ℝ) ^ 2 * (j : ℝ) ^ 11 := by positivity
    simp [A_E_sq_fourierCoeff, hcond, hnonneg]

lemma A_E_sq_fourierCoeff_isBigO :
    A_E_sq_fourierCoeff =O[atTop] (fun n ↦ (n ^ 11 : ℝ)) := by
  simp only [isBigO_iff, eventually_atTop, ge_iff_le]
  refine ⟨(720 : ℝ) ^ 2, (4 : ℤ), ?_⟩
  intro n hn
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (by decide : (0 : ℤ) ≤ 4) hn)
  simpa using norm_A_E_sq_fourierCoeff_ofNat_le (j := j) (Int.ofNat_le.mp (by simpa using hn))

lemma A_E_sq_fourierCoeff_summable (z : ℍ) (hz : 1 / 2 < z.im) :
    Summable (fun i : ℕ ↦ fouterm A_E_sq_fourierCoeff z (i + 4)) := by
  -- Polynomially bounded coefficients times exponentially decaying terms.
  let r : ℝ := Real.exp (-Real.pi / 2)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr : ‖r‖ < 1 := by
    have : r < 1 := by
      have : (-Real.pi / 2) < 0 := by nlinarith [Real.pi_pos]
      simpa [r] using (Real.exp_lt_one_iff.2 this)
    simpa [Real.norm_of_nonneg hr0] using this
  let g : ℕ → ℝ := fun m => ((m : ℝ) ^ 11) * r ^ m
  have hg : Summable g := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 11 hr
  have hshift : Summable (fun n : ℕ => g (n + 4)) := by
    simpa [g] using (summable_nat_add_iff (f := g) 4).2 hg
  refine Summable.of_norm ?_
  refine
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((hshift.mul_left ((720 : ℝ) ^ 2))))
  have hz' : (1 / 2 : ℝ) ≤ z.im := le_of_lt hz
  have hcoeff :
      ‖A_E_sq_fourierCoeff (Int.ofNat (n + 4))‖ ≤
        (720 : ℝ) ^ 2 * ((n + 4 : ℕ) : ℝ) ^ 11 :=
    norm_A_E_sq_fourierCoeff_ofNat_le (j := n + 4) (by omega)
  have hexp :
      ‖cexp (↑π * I * (Int.ofNat (n + 4)) * z)‖ ≤ r ^ (n + 4) := by
    have hnorm :
        ‖cexp (↑π * I * (Int.ofNat (n + 4)) * z)‖ =
          Real.exp (-Real.pi * ((n + 4 : ℕ) : ℝ) * z.im) := by
      simp [Complex.norm_exp, mul_assoc, mul_left_comm, mul_comm]
    have hnonpos : -Real.pi * ((n + 4 : ℕ) : ℝ) ≤ 0 := by
      nlinarith [Real.pi_pos]
    have hle :
        (-Real.pi * ((n + 4 : ℕ) : ℝ)) * z.im ≤
          (-Real.pi * ((n + 4 : ℕ) : ℝ)) * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonpos_left hz' hnonpos
    have hmono :
        Real.exp ((-Real.pi * ((n + 4 : ℕ) : ℝ)) * z.im) ≤
          Real.exp ((-Real.pi * ((n + 4 : ℕ) : ℝ)) * (1 / 2 : ℝ)) :=
      Real.exp_le_exp.2 hle
    have hpow :
        Real.exp ((-Real.pi * ((n + 4 : ℕ) : ℝ)) * (1 / 2 : ℝ)) = r ^ (n + 4) := by
      have hrew :
          (-Real.pi * ((n + 4 : ℕ) : ℝ)) * (1 / 2 : ℝ) =
            (-Real.pi / 2 : ℝ) * ((n + 4 : ℕ) : ℝ) := by
        ring
      calc
        Real.exp ((-Real.pi * ((n + 4 : ℕ) : ℝ)) * (1 / 2 : ℝ)) =
            Real.exp ((-Real.pi / 2 : ℝ) * ((n + 4 : ℕ) : ℝ)) := by
              exact congrArg Real.exp hrew
        _ = Real.exp (((n + 4 : ℕ) : ℝ) * (-Real.pi / 2 : ℝ)) := by
              simp [mul_comm]
        _ = Real.exp (-Real.pi / 2) ^ (n + 4) := by
              simpa using Real.exp_nat_mul (-Real.pi / 2) (n + 4)
        _ = r ^ (n + 4) := by
              simp [r]
    have hnorm' :
        Real.exp (-Real.pi * ((n + 4 : ℕ) : ℝ) * z.im) =
          Real.exp ((-Real.pi * ((n + 4 : ℕ) : ℝ)) * z.im) := by
      ring
    exact (le_of_eq (hnorm.trans hnorm')).trans (hmono.trans_eq hpow)
  calc
    ‖fouterm A_E_sq_fourierCoeff z (n + 4)‖ =
        ‖A_E_sq_fourierCoeff (Int.ofNat (n + 4)) * cexp (↑π * I * (Int.ofNat (n + 4)) * z)‖ := by
          simp [fouterm]
    _ = ‖A_E_sq_fourierCoeff (Int.ofNat (n + 4))‖ *
          ‖cexp (↑π * I * (Int.ofNat (n + 4)) * z)‖ := by
          simp
    _ ≤ ((720 : ℝ) ^ 2 * ((n + 4 : ℕ) : ℝ) ^ 11) * (r ^ (n + 4)) := by
          gcongr
    _ = ((720 : ℝ) ^ 2) * g (n + 4) := by
          simp [g, mul_assoc, mul_left_comm, mul_comm]

lemma A_E_sq_series_summable (x : ℍ) :
    Summable (fun m : ℕ =>
      A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))) := by
  -- Compare to a polynomially weighted geometric series with ratio `r = exp(-2π * x.im)`.
  let r : ℝ := Real.exp (-2 * Real.pi * x.im)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr : ‖r‖ < 1 := by
    have hx : (-2 * Real.pi * x.im) < 0 := by
      have : 0 < x.im := UpperHalfPlane.im_pos x
      nlinarith [Real.pi_pos, this]
    simpa [r, Real.norm_of_nonneg hr0] using (Real.exp_lt_one_iff.2 hx)
  -- Summability of the comparison series.
  let g0 : ℕ → ℝ := fun m => ((m : ℝ) ^ 11) * r ^ m
  have hg0 : Summable g0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 11 hr
  have hg1 : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ 11 * r ^ (m + 1)) := by
    simpa [g0, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff (f := g0) 1).2 hg0
  have hg2 : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ 11 * r ^ (m + 2)) := by
    -- Multiply the summable series by the constant `r`, using `r^(m+2) = r^(m+1) * r`.
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hg1.mul_right r
  -- Now compare the norms termwise.
  refine Summable.of_norm ?_
  refine (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ (hg2.mul_left ((720 : ℝ) ^ 2)))
  intro m
  -- Coefficient bound.
  have hcoeff : ‖A_E_sq_coeff m‖ ≤ (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 11 :=
    norm_A_E_sq_coeff_le (m := m)
  -- Exponential norm.
  have hexp :
      ‖cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖ ≤ r ^ (m + 2) := by
    -- `‖exp(w)‖ = exp(re w)` and `re (2π i (m+2) x) = -2π (m+2) im x`.
    have hnorm :
        ‖cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖ =
          Real.exp (-2 * Real.pi * ((m + 2 : ℕ) : ℝ) * x.im) := by
      simp [Complex.norm_exp, mul_re, mul_im, mul_assoc, mul_left_comm, mul_comm]
    have hrpow :
        Real.exp (-2 * Real.pi * ((m + 2 : ℕ) : ℝ) * x.im) = r ^ (m + 2) := by
      -- `exp(-2π*(m+2)*im x) = exp(-2π*im x)^(m+2)`.
      calc
        Real.exp (-2 * Real.pi * ((m + 2 : ℕ) : ℝ) * x.im)
            = Real.exp (((m + 2 : ℕ) : ℝ) * (-2 * Real.pi * x.im)) := by
                  ring_nf
        _ = Real.exp (-2 * Real.pi * x.im) ^ (m + 2) := by
              simpa using (Real.exp_nat_mul (-2 * Real.pi * x.im) (m + 2))
        _ = r ^ (m + 2) := by simp [r]
    exact le_of_eq (hnorm.trans hrpow)
  calc
    ‖A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖
        = ‖A_E_sq_coeff m‖ * ‖cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖ := by
              simp
    _ ≤ ((720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 11) * (r ^ (m + 2)) := by
              exact mul_le_mul hcoeff hexp (norm_nonneg _) (by positivity)
    _ = ((720 : ℝ) ^ 2) * (((m + 1 : ℕ) : ℝ) ^ 11 * r ^ (m + 2)) := by
              ring_nf

lemma A_E_sq_fourierCoeff_hf :
    ∀ x : ℍ, (A_E x) ^ 2 = ∑' (n : ℕ), fouterm A_E_sq_fourierCoeff x (n + 4) := by
  intro x
  have hA2 := A_E_sq_eq_tsum (z := x)
  let f : ℕ → ℂ := fun n => fouterm A_E_sq_fourierCoeff x (n + 4)
  let g : ℕ → ℂ := fun m =>
    A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))
  have hodd_term (m : ℕ) : f (2 * m + 1) = 0 := by
    -- Rewrite the index `↑(2*m+1) + 4` as `↑(2*m+5)` and use the `else` branch.
    have hidxNat : (2 * m + 1) + 4 = 2 * m + 5 := by omega
    have hidx : ((2 * m + 1 : ℕ) : ℤ) + (4 : ℤ) = (Int.ofNat (2 * m + 5)) := by
      simpa [hidxNat] using (Int.ofNat_add_ofNat (2 * m + 1) 4)
    have hcond : ¬(4 ≤ (2 * m + 5) ∧ Even (2 * m + 5)) := by
      intro h
      have : ¬Even (2 * m + 5) := by simp [parity_simps]
      exact this h.2
    -- Unfold and simplify.
    dsimp [f, fouterm]
    -- Rewrite the index to an `ofNat` and use `hcond`.
    have : A_E_sq_fourierCoeff (((2 * m + 1 : ℕ) : ℤ) + 4) = 0 := by
      -- first, normalize the integer index
      rw [hidx]
      change
        (if 4 ≤ (2 * m + 5) ∧ Even (2 * m + 5) then A_E_sq_coeff ((2 * m + 5) / 2 - 2) else 0) =
          0
      rw [if_neg hcond]
    simpa [this]
  have heven_term (m : ℕ) : f (2 * m) = g m := by
    let i : ℤ := ((2 * m : ℕ) : ℤ) + 4
    have hiNat : (2 * m) + 4 = 2 * m + 4 := rfl
    have hi : i = Int.ofNat (2 * m + 4) := by
      dsimp [i]
    have hcond : 4 ≤ (2 * m + 4) ∧ Even (2 * m + 4) := by
      refine ⟨by omega, by simp [parity_simps]⟩
    have hc : A_E_sq_fourierCoeff i = A_E_sq_coeff m := by
      have hdiv : (2 * m + 4) / 2 - 2 = m := by
        have : 2 * m + 4 = 2 * (m + 2) := by ring
        simp [this]
      have hcNat : A_E_sq_fourierCoeff (Int.ofNat (2 * m + 4)) = A_E_sq_coeff m := by
        simp [A_E_sq_fourierCoeff, hcond, hdiv]
      simpa [hi] using hcNat
    have hexp :
        cexp (π * I * ((i : ℂ)) * (x : ℂ)) =
          cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ)) := by
      have hcast : ((2 * m + 4 : ℕ) : ℂ) = (2 : ℂ) * ((m + 2 : ℕ) : ℂ) := by
        have h : 2 * m + 4 = 2 * (m + 2) := by ring
        simp [h, Nat.cast_mul]
      have harg :
          (π * I * ((2 * m + 4 : ℕ) : ℂ) * (x : ℂ)) =
            (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ)) := by
        calc
          (π * I * ((2 * m + 4 : ℕ) : ℂ) * (x : ℂ))
              = π * I * ((2 : ℂ) * ((m + 2 : ℕ) : ℂ)) * (x : ℂ) := by
                    simp [hcast]
          _ = (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ)) := by ring_nf
      have hexpNat :
          cexp (π * I * ((2 * m + 4 : ℕ) : ℂ) * (x : ℂ)) =
            cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ)) := by
        simpa using congrArg Complex.exp harg
      simpa [hi] using hexpNat
    -- Finish.
    dsimp [f, g, fouterm]
    -- Keep the index as `i` to avoid unfolding coercions.
    have hidx : 2 * (m : ℤ) + 4 = i := by
      dsimp [i]
    -- Rewrite indices, then use the computed coefficient/exponent identities.
    -- `simp` here tends to unfold casts aggressively, so we do targeted rewrites.
    -- (The goal is in `ℂ`, so `rw` is safe.)
    rw [hidx]
    rw [hc]
    rw [hexp]
  have ho : Summable (fun m : ℕ => f (2 * m + 1)) := by
    have hzero : (fun m : ℕ => f (2 * m + 1)) = 0 := by
      funext m
      simpa using hodd_term m
    rw [hzero]
    exact (summable_zero : Summable (0 : ℕ → ℂ))
  have hs_g : Summable g := by
    simpa [g] using A_E_sq_series_summable (x := x)
  have he : Summable (fun m : ℕ => f (2 * m)) := by
    refine Summable.congr hs_g ?_
    intro m
    exact (heven_term m).symm
  have hsplit :
      (∑' m : ℕ, f (2 * m)) + (∑' m : ℕ, f (2 * m + 1)) = ∑' n : ℕ, f n :=
    tsum_even_add_odd (f := f) he ho
  have hodd_sum : (∑' m : ℕ, f (2 * m + 1)) = 0 := by
    -- since all odd terms are zero
    have : (∑' m : ℕ, f (2 * m + 1)) = ∑' m : ℕ, (0 : ℂ) := by
      refine tsum_congr ?_
      intro m
      simpa using hodd_term m
    simpa using this.trans (tsum_zero : (∑' m : ℕ, (0 : ℂ)) = 0)
  have heven_sum : (∑' m : ℕ, f (2 * m)) = ∑' m : ℕ, g m := by
    refine tsum_congr ?_
    intro m
    exact heven_term m
  have hsumf : (∑' n : ℕ, f n) = ∑' m : ℕ, g m := by
    calc
      (∑' n : ℕ, f n) = (∑' m : ℕ, f (2 * m)) + (∑' m : ℕ, f (2 * m + 1)) := by
        simpa [add_comm, add_left_comm, add_assoc] using hsplit.symm
      _ = (∑' m : ℕ, f (2 * m)) := by simp [hodd_sum]
      _ = ∑' m : ℕ, g m := heven_sum
  -- Now use Bhavik's `2π i`-series.
  have hA2' : (A_E x) ^ 2 = ∑' m : ℕ, g m := by
    simpa [g] using hA2
  simpa [f, hsumf] using hA2'

/-- Exponential decay for the magic function `φ₀` in the upper half-plane.

This produces a constant `C₀` such that `‖φ₀ z‖ ≤ C₀ * exp (-2 * π * Im z)` for `Im z > 1/2`.
-/
public theorem norm_φ₀_le : ∃ C₀ > 0, ∀ z : ℍ, 1 / 2 < z.im →
    norm (φ₀ z) ≤ C₀ * rexp (-2 * π * z.im) := by
  refine ⟨DivDiscBound A_E_sq_fourierCoeff 4, ?_, ?_⟩
  · simpa [gt_iff_lt] using
      (DivDiscBound_pos (c := A_E_sq_fourierCoeff) (n₀ := (4 : ℤ))
        (hcn₀ := A_E_sq_fourierCoeff_four_ne_zero) (k := 11) (hpoly := A_E_sq_fourierCoeff_isBigO))
  · intro z hz
    have hmain :
        norm (((A_E z) ^ 2) / (Δ z)) ≤
          (DivDiscBound A_E_sq_fourierCoeff 4) * rexp (-π * ((4 : ℤ) - 2) * z.im) := by
      exact
        DivDiscBoundOfPolyFourierCoeff (z := z) (hz := hz) (c := A_E_sq_fourierCoeff)
          (n₀ := (4 : ℤ)) (hcsum := by simpa using A_E_sq_fourierCoeff_summable (z := z) hz)
          (k := 11) (hpoly := A_E_sq_fourierCoeff_isBigO) (f := fun z ↦ (A_E z) ^ 2)
          (hf := fun x => by simpa using (A_E_sq_fourierCoeff_hf (x := x)))
    have hrexp : rexp (-(π * (4 - 2) * z.im)) = rexp (-(2 * π * z.im)) := by
      congr 1
      ring_nf
    -- Rewrite `φ₀` and the exponent.
    simpa [φ₀, A_E, hrexp] using hmain

/-- A derived uniform bound for `φ₀''` on the region `Im z > 1/2`.

This is the specialization of `norm_φ₀_le` to a fixed point `z` with `Im z > 1/2`, after bounding
`exp (-2 * π * Im z)` by `exp (-π)`.
-/
public lemma norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im {C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, 1 / 2 < z.im → ‖φ₀ z‖ ≤ C₀ * rexp (-2 * π * z.im)) (z : ℍ)
    (hz : 1 / 2 < z.im) : ‖φ₀'' (z : ℂ)‖ ≤ C₀ * rexp (-π) := by
  have hzpos : 0 < (z : ℂ).im := by
    have : (0 : ℝ) < z.im := lt_trans (by norm_num) hz
    simpa using this
  have hφ : ‖φ₀ z‖ ≤ C₀ * rexp (-2 * π * z.im) := hC₀ z hz
  have hexp : rexp (-2 * π * z.im) ≤ rexp (-π) := by
    have : (-2 * π * z.im : ℝ) ≤ -π := by
      have : (1 / 2 : ℝ) ≤ z.im := le_of_lt hz
      nlinarith [Real.pi_pos, this]
    simpa using (Real.exp_le_exp.2 this)
  have hmul : C₀ * rexp (-2 * π * z.im) ≤ C₀ * rexp (-π) :=
    mul_le_mul_of_nonneg_left hexp hC₀_pos.le
  calc
    ‖φ₀'' (z : ℂ)‖ = ‖φ₀ z‖ := by
      have hz' : (⟨(z : ℂ), hzpos⟩ : ℍ) = z := by
        ext
        rfl
      simp [φ₀''_def (z := (z : ℂ)) hzpos, hz']
    _ ≤ C₀ * rexp (-2 * π * z.im) := hφ
    _ ≤ C₀ * rexp (-π) := hmul

end Corollaries

end

end MagicFunction.PolyFourierCoeffBound
