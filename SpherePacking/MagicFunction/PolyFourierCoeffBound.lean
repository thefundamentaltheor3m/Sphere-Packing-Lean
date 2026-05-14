/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import SpherePacking.ModularForms.Eisenstein

/-!
# Polynomial Fourier Coefficient bounds

* Core lemma `DivDiscBoundOfPolyFourierCoeff` (Lemma 7.4 in the blueprint): explicit upper bound
  on `‖f / Δ‖` for `f : ℍ → ℂ` whose Fourier coefficients are polynomially bounded.
* Corollaries: Fourier coefficients of `(A_E)^2` via the Cauchy product, repackaged as `fouterm`,
  and concrete exponential decay estimates on `φ₀`.
-/

namespace MagicFunction.PolyFourierCoeffBound

noncomputable section

open scoped UpperHalfPlane ArithmeticFunction.sigma BigOperators

open Filter Complex Real Asymptotics ArithmeticFunction

/-! ## Core definitions and main bound (merged from `PolyFourierCoeffBound.Basic`) -/

/-- If `‖r‖ < 1` and `u n` grows at most polynomially, then `‖u n * r ^ n‖` is summable. -/
public theorem summable_real_norm_mul_geometric_of_norm_lt_one {k : ℕ} {r : ℂ}
    (hr : ‖r‖ < 1) {u : ℕ → ℂ} (hu : u =O[atTop] (fun n ↦ (↑(n ^ k) : ℝ))) :
    Summable fun n : ℕ ↦ ‖u n * r ^ n‖ := by
  refine summable_of_isBigO_nat (g := fun n ↦ ‖(↑(n ^ k) : ℂ) * r ^ n‖) ?_ ?_
  · simpa [Nat.cast_pow] using summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℂ) k (r := r) hr
  · simpa [norm_mul, Real.norm_eq_abs, Complex.norm_real, Nat.cast_pow] using
      (hu.norm_left.mul (Asymptotics.isBigO_refl (fun n : ℕ ↦ ‖r ^ n‖) atTop))

/-- Summability of `(n+s)^k * exp(-2π n)` on `ℕ`, used to justify `q`-series limits. -/
public theorem summable_pow_shift_mul_exp (k s : ℕ) :
    Summable (fun n : ℕ => ((n + s : ℝ) ^ k) * Real.exp (-2 * Real.pi * n)) := by
  have hs : Summable (fun n : ℕ => ((n + s : ℝ) ^ k) * Real.exp (-2 * Real.pi * (n + s : ℝ))) := by
    simpa [Nat.cast_add] using
      (summable_nat_add_iff s (f := fun n : ℕ =>
        ((n : ℝ) ^ k) * Real.exp (-2 * Real.pi * (n : ℝ)))).2 (by
          simpa [mul_assoc] using
            Real.summable_pow_mul_exp_neg_nat_mul k (r := 2 * Real.pi) (by positivity))
  refine (hs.mul_left (Real.exp (2 * Real.pi * (s : ℝ)))).congr fun n => ?_
  rw [show (-2 * Real.pi * (n : ℝ)) = 2 * Real.pi * (s : ℝ) + -2 * Real.pi * (n + s : ℝ) by ring,
    Real.exp_add]; ring

/-- Monotonicity of `∏'` under pointwise inequalities, for nonnegative and multipliable families. -/
private lemma tprod_le_of_nonneg_of_multipliable {β : Type*} {f g : β → ℝ} (hfnn : 0 ≤ f)
    (hfg : f ≤ g) (hf : Multipliable f) (hg : Multipliable g) : ∏' b, f b ≤ ∏' b, g b :=
  le_of_tendsto_of_tendsto' hf.hasProd hg.hasProd fun _ ↦
    Finset.prod_le_prod (fun i _ ↦ hfnn i) fun i _ ↦ hfg i

/-- A single Fourier term in the `π i` convention. -/
@[expose] public def fouterm (coeff : ℤ → ℂ) (x : ℂ) (i : ℤ) : ℂ :=
  (coeff i) * cexp (π * I * i * x)

variable (z : ℍ) (hz : 1 / 2 < z.im) (c : ℤ → ℂ) (n₀ : ℤ) (hcn₀ : c n₀ ≠ 0)
  (hcsum : Summable fun i : ℕ ↦ fouterm c z (i + n₀)) (k : ℕ)
  (hpoly : c =O[atTop] fun n ↦ (n ^ k : ℝ))
  (f : ℍ → ℂ) (hf : ∀ x : ℍ, f x = ∑' n : ℕ, fouterm c x (n + n₀))

/-- The explicit factor in `DivDiscBoundOfPolyFourierCoeff` bounding `f / Δ`. -/
public def DivDiscBound : ℝ :=
  (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24)

include hpoly in
lemma summable_norm_mul_rexp_neg_pi_div_two :
    Summable (fun n : ℕ => ‖c (n + n₀)‖ * rexp (-π * n / 2)) := by
  refine (summable_real_norm_mul_geometric_of_norm_lt_one (k := k) (r := cexp (-(π : ℂ) / 2))
    (by simp [Complex.norm_exp, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]) (by
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

private lemma summable_log_one_sub_rexp_pow_24 {c : ℝ} (hc : 0 < c) :
    Summable fun b : ℕ+ ↦ Real.log ((1 - rexp (-c * (b : ℝ))) ^ 24) := by
  simpa [log_pow, Nat.cast_ofNat, sub_eq_add_neg, smul_eq_mul] using Summable.const_smul (24 : ℝ)
    (Real.summable_log_one_add_of_summable ((by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        ((Real.summable_exp_nat_mul_iff (a := -c)).2 (by nlinarith)).comp_injective
          PNat.coe_injective :
      Summable fun b : ℕ+ ↦ Real.exp (-c * (b : ℝ))).neg))

lemma aux_tprod_one_sub_rexp_pow_24_pos (c : ℝ) (hc : 0 < c) :
    0 < ∏' (n : ℕ+), (1 - rexp (-c * (n : ℝ))) ^ 24 := by
  rw [← Real.rexp_tsum_eq_tprod (fun i ↦ by simp_all)]
  exacts [Real.exp_pos _, summable_log_one_sub_rexp_pow_24 hc]

lemma aux_8 : 0 < ∏' (n : ℕ+), (1 - rexp (-2 * π * ↑↑n * z.im)) ^ 24 := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    aux_tprod_one_sub_rexp_pow_24_pos (c := 2 * π * z.im) (by positivity)

include hcsum in
lemma aux_10 : Summable fun (n : ℕ) ↦ norm (c (n + n₀)) * rexp (-π * ↑n * z.im) := by
  refine (aux_3 z c n₀ hcsum).congr fun i => ?_
  rw [norm_mul, show (↑π * I * (i : ℂ) * z) = I * ((↑π * i) * z) by ring, Complex.norm_exp]; simp

lemma aux_11 : 0 < ∏' (n : ℕ+), (1 - rexp (-π * ↑↑n)) ^ 24 := by
  simpa using aux_tprod_one_sub_rexp_pow_24_pos (c := π) pi_pos

lemma step_12a {r : ℝ} (hr : 0 < r) :
    Multipliable fun b : ℕ+ ↦ (1 - rexp (-r * (b : ℝ))) ^ 24 := by
  refine Real.multipliable_of_summable_log (fun i ↦ ?_) ?_
  · refine pow_pos (sub_pos.2 (Real.exp_lt_one_iff.2 ?_)) _
    nlinarith [show (0 : ℝ) < (i : ℝ) from mod_cast i.pos]
  exact summable_log_one_sub_rexp_pow_24 hr

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
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := by
    have hpow : Multipliable fun b : ℕ+ ↦ ‖(1 - cexp (2 * ↑π * I * (b : ℂ) * z))‖ ^ 24 := by
      have h := (MultipliableEtaProductExpansion_pnat z).norm
      induction (24 : ℕ) with | zero => simp | succ n hn => simpa [pow_succ] using hn.mul h
    gcongr
    · exact aux_8 z
    refine tprod_le_of_nonneg_of_multipliable (fun n => by positivity) (fun n => ?_) ?_ hpow
    · simp only [neg_mul]; gcongr
      · simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff]; positivity
      · rw [show -(2 * π * n * z.im) = (2 * π * I * n * z).re by simp]
        exact (le_abs_self _).trans <| by
          simpa [Complex.norm_exp] using abs_norm_sub_norm_le (1 : ℂ) (cexp (2 * π * I * n * z))
    · simpa [mul_assoc, mul_left_comm, mul_comm] using
        step_12a (r := 2 * π * z.im) (mul_pos two_pi_pos (UpperHalfPlane.im_pos z))
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := by
    gcongr ?_ * ?_ / _
    · exact (aux_8 z).le
    refine Summable.tsum_le_tsum (fun n ↦ mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 ?_) (norm_nonneg _)) (aux_10 z c n₀ hcsum)
      (summable_norm_mul_rexp_neg_pi_div_two (c := c) (n₀ := n₀) (k := k) hpoly)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, neg_mul] using
      neg_le_neg (mul_le_mul_of_nonneg_left hz.le (by positivity : 0 ≤ (π : ℝ) * (n : ℝ)))
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
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
  _ = (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := by
      simp [DivDiscBound, mul_div_assoc, mul_comm, mul_assoc]

include hpoly hcn₀ in
public theorem DivDiscBound_pos : 0 < DivDiscBound c n₀ := by
  rw [DivDiscBound]
  refine div_pos (Summable.tsum_pos
    (summable_norm_mul_rexp_neg_pi_div_two (c := c) (n₀ := n₀) (k := k) hpoly)
    (fun _ => by positivity) 0 ?_) aux_11
  simpa using norm_pos_iff.2 hcn₀

/-! ## Corollaries: Fourier coefficients of `(A_E)^2` -/

public def A_E_sq_coeff (m : ℕ) : ℂ :=
  ∑ p ∈ Finset.antidiagonal m, A_E_coeff p.1 * A_E_coeff p.2

public lemma norm_A_E_coeff_le (n : ℕ) :
    ‖A_E_coeff n‖ ≤ (720 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 5 := by
  nlinarith [show ‖A_E_coeff n‖ = (720 : ℝ) * ((n + 1 : ℕ) : ℝ) * (σ 3 (n + 1) : ℝ) by
    simpa using norm_A_E_coeff n,
    show (σ 3 (n + 1) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 4 from mod_cast sigma_bound 3 (n + 1),
    Nat.zero_le n]

public lemma norm_A_E_sq_coeff_le (m : ℕ) :
    ‖A_E_sq_coeff m‖ ≤ (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 11 := by
  calc ‖A_E_sq_coeff m‖
      = ‖∑ p ∈ Finset.antidiagonal m, A_E_coeff p.1 * A_E_coeff p.2‖ := by simp [A_E_sq_coeff]
    _ ≤ ∑ p ∈ Finset.antidiagonal m, ‖A_E_coeff p.1 * A_E_coeff p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ Finset.antidiagonal m, (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10 :=
        Finset.sum_le_sum fun p hp => by
          rw [Finset.mem_antidiagonal] at hp
          rw [norm_mul, show (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10 =
            ((720 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 5) * ((720 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 5) by ring]
          gcongr <;> exact (norm_A_E_coeff_le _).trans (by gcongr; omega)
    _ = (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 11 := by simp [Finset.Nat.card_antidiagonal]; ring

public lemma A_E_sq_eq_tsum (z : ℍ) :
    (A_E z) ^ 2 =
      ∑' m : ℕ, A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
  have ht_norm : Summable (fun n : ℕ => ‖A_E_term z n‖) := by
    set r : ℝ := Real.exp (-2 * Real.pi * z.im)
    let g : ℕ → ℝ := fun n => (720 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 5 * r ^ (n + 1)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (show Summable g by
        simpa [g, mul_assoc, mul_left_comm, mul_comm, Nat.cast_add, Nat.cast_one] using
          ((summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * r ^ n) 1).2
            (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5 (by
              simpa [r, Real.norm_of_nonneg (Real.exp_pos _).le] using Real.exp_lt_one_iff.2 (by
                nlinarith [Real.pi_pos, UpperHalfPlane.im_pos z] :
                  (-2 * Real.pi * z.im) < 0)))).mul_left (720 : ℝ))
    calc ‖A_E_term z n‖
        = ‖A_E_coeff n‖ * ‖cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))‖ := by simp [A_E_term]
      _ ≤ g n := by
          simpa [g, mul_assoc, mul_comm] using mul_le_mul (norm_A_E_coeff_le n)
            (show ‖cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))‖ ≤ r ^ (n + 1) by
              rw [show ‖cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))‖ =
                  rexp (((n + 1 : ℕ) : ℝ) * (-2 * π * z.im)) by
                simp [Complex.norm_exp, mul_re, mul_im, mul_assoc, mul_left_comm, mul_comm],
                Real.exp_nat_mul]) (norm_nonneg _) (by positivity)
  have hanti (m : ℕ) :
      (∑ p ∈ Finset.antidiagonal m, A_E_term z p.1 * A_E_term z p.2) =
        A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
    rw [show (∑ p ∈ Finset.antidiagonal m, A_E_term z p.1 * A_E_term z p.2) =
        ∑ p ∈ Finset.antidiagonal m, (A_E_coeff p.1 * A_E_coeff p.2) *
            cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) from Finset.sum_congr rfl fun p hp => by
      rw [Finset.mem_antidiagonal] at hp
      have hexp : cexp (2 * π * I * ((p.1 + 1 : ℕ) : ℂ) * (z : ℂ)) *
          cexp (2 * π * I * ((p.2 + 1 : ℕ) : ℂ) * (z : ℂ)) =
            cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
        rw [← Complex.exp_add]; congr 1
        push_cast [← (show (p.1 + 1 : ℕ) + (p.2 + 1 : ℕ) = m + 2 by omega)]; ring
      dsimp [A_E_term]; exact CancelDenoms.mul_subst rfl hexp rfl]
    simp [Finset.sum_mul, A_E_sq_coeff, mul_assoc]
  rw [show (A_E z) ^ 2 = (∑' n : ℕ, A_E_term z n) * (∑' n : ℕ, A_E_term z n) by
    rw [← A_E_eq_tsum z]; ring,
    (by simpa using tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ht_norm ht_norm :
      (∑' n : ℕ, A_E_term z n) * (∑' n : ℕ, A_E_term z n) =
        ∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, A_E_term z p.1 * A_E_term z p.2)]
  exact tsum_congr hanti

/-! ### Converting to `fouterm` coefficients -/

public noncomputable def A_E_sq_fourierCoeff : ℤ → ℂ
  | (Int.ofNat j) => if 4 ≤ j ∧ Even j then A_E_sq_coeff (j / 2 - 2) else 0
  | (Int.negSucc _) => 0

public lemma A_E_sq_fourierCoeff_four_ne_zero : A_E_sq_fourierCoeff 4 ≠ 0 := by
  simp [A_E_sq_fourierCoeff, show 4 ≤ (4 : ℕ) ∧ Even (4 : ℕ) by decide, A_E_sq_coeff, A_E_coeff,
    show (720 : ℂ) ≠ 0 by norm_num]

public lemma norm_A_E_sq_fourierCoeff_ofNat_le (j : ℕ) (hj : 4 ≤ j) :
    ‖A_E_sq_fourierCoeff (Int.ofNat j)‖ ≤ (720 : ℝ) ^ 2 * (j : ℝ) ^ 11 := by
  by_cases hjEven : Even j
  · refine ((show ‖A_E_sq_fourierCoeff (Int.ofNat j)‖ = ‖A_E_sq_coeff (j / 2 - 2)‖ by
        simp [A_E_sq_fourierCoeff, hj, hjEven]).trans_le <| by
      simpa using norm_A_E_sq_coeff_le (j / 2 - 2)).trans ?_
    gcongr; exact_mod_cast (by omega : j / 2 - 2 + 1 ≤ j)
  · simp [A_E_sq_fourierCoeff, show ¬(4 ≤ j ∧ Even j) from fun h => hjEven h.2,
      show 0 ≤ (720 : ℝ) ^ 2 * (j : ℝ) ^ 11 by positivity]

public lemma A_E_sq_fourierCoeff_isBigO :
    A_E_sq_fourierCoeff =O[atTop] (fun n ↦ (n ^ 11 : ℝ)) := by
  simp only [isBigO_iff, eventually_atTop, ge_iff_le]
  refine ⟨(720 : ℝ) ^ 2, (4 : ℤ), fun n hn => ?_⟩
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ n)
  simpa using norm_A_E_sq_fourierCoeff_ofNat_le j (mod_cast hn)

public lemma A_E_sq_fourierCoeff_summable (z : ℍ) (hz : 1 / 2 < z.im) :
    Summable (fun i : ℕ ↦ fouterm A_E_sq_fourierCoeff z (i + 4)) := by
  set r : ℝ := Real.exp (-Real.pi / 2)
  let g : ℕ → ℝ := fun m => ((m : ℝ) ^ 11) * r ^ m
  refine Summable.of_norm <| Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((show Summable (fun n : ℕ => g (n + 4)) by
      simpa [g] using (summable_nat_add_iff (f := g) 4).2
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 11 (by
          simpa [r, Real.norm_of_nonneg (Real.exp_pos _).le] using
            Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos] :
              (-Real.pi / 2 : ℝ) < 0)))).mul_left ((720 : ℝ) ^ 2))
  have hexp : ‖cexp (↑π * I * (Int.ofNat (n + 4)) * z)‖ ≤ r ^ (n + 4) := by
    rw [show ‖cexp (↑π * I * (Int.ofNat (n + 4)) * z)‖ =
        Real.exp ((-Real.pi * ((n + 4 : ℕ) : ℝ)) * z.im) by
      simp [Complex.norm_exp, mul_assoc, mul_left_comm, mul_comm]]
    refine (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left hz.le
      (by nlinarith [Real.pi_pos]))).trans_eq ?_
    rw [show (-Real.pi * ((n + 4 : ℕ) : ℝ)) * (1 / 2 : ℝ) =
      ((n + 4 : ℕ) : ℝ) * (-Real.pi / 2 : ℝ) by ring, Real.exp_nat_mul]
  calc ‖fouterm A_E_sq_fourierCoeff z (n + 4)‖
      = ‖A_E_sq_fourierCoeff (Int.ofNat (n + 4))‖ *
          ‖cexp (↑π * I * (Int.ofNat (n + 4)) * z)‖ := by simp [fouterm]
    _ ≤ ((720 : ℝ) ^ 2 * ((n + 4 : ℕ) : ℝ) ^ 11) * (r ^ (n + 4)) := by
        gcongr; exact norm_A_E_sq_fourierCoeff_ofNat_le (j := n + 4) (by omega)
    _ = ((720 : ℝ) ^ 2) * g (n + 4) := by simp [g, mul_assoc, mul_left_comm, mul_comm]

public lemma A_E_sq_series_summable (x : ℍ) :
    Summable (fun m : ℕ => A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))) := by
  set r : ℝ := Real.exp (-2 * Real.pi * x.im)
  refine Summable.of_norm <| Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    ((show Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ 11 * r ^ (m + 2)) by
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm, Nat.cast_add, Nat.cast_one] using
        ((summable_nat_add_iff (f := fun m : ℕ => ((m : ℝ) ^ 11) * r ^ m) 1).2
          (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 11 (by
            simpa [r, Real.norm_of_nonneg (Real.exp_pos _).le] using Real.exp_lt_one_iff.2 (by
              nlinarith [Real.pi_pos, UpperHalfPlane.im_pos x] :
                (-2 * Real.pi * x.im) < 0)))).mul_right r).mul_left ((720 : ℝ) ^ 2))
  calc ‖A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖
      = ‖A_E_sq_coeff m‖ * ‖cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖ := by simp
    _ ≤ ((720 : ℝ) ^ 2) * (((m + 1 : ℕ) : ℝ) ^ 11 * r ^ (m + 2)) := by
        nlinarith [mul_le_mul (norm_A_E_sq_coeff_le m)
          (show ‖cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖ ≤ r ^ (m + 2) by
            rw [show ‖cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖ =
                Real.exp (((m + 2 : ℕ) : ℝ) * (-2 * Real.pi * x.im)) by
              simp [Complex.norm_exp, mul_re, mul_im, mul_assoc, mul_left_comm, mul_comm],
              Real.exp_nat_mul]) (norm_nonneg _) (by positivity)]

public lemma A_E_sq_fourierCoeff_hf (x : ℍ) :
    (A_E x) ^ 2 = ∑' (n : ℕ), fouterm A_E_sq_fourierCoeff x (n + 4) := by
  let f : ℕ → ℂ := fun n => fouterm A_E_sq_fourierCoeff x (n + 4)
  let g : ℕ → ℂ := fun m => A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))
  have hodd_term (m : ℕ) : f (2 * m + 1) = 0 := by
    simp only [f, fouterm, show ((2 * m + 1 : ℕ) : ℤ) + (4 : ℤ) = (Int.ofNat (2 * m + 5)) by
      simpa [show (2 * m + 1) + 4 = 2 * m + 5 by omega] using Int.ofNat_add_ofNat (2 * m + 1) 4,
      A_E_sq_fourierCoeff, if_neg (show ¬(4 ≤ (2 * m + 5) ∧ Even (2 * m + 5)) by
        grind only [= Nat.even_iff]), zero_mul]
  have heven_term (m : ℕ) : f (2 * m) = g m := by
    have hc : A_E_sq_fourierCoeff (Int.ofNat (2 * m + 4)) = A_E_sq_coeff m := by
      simp [A_E_sq_fourierCoeff,
        show 4 ≤ (2 * m + 4) ∧ Even (2 * m + 4) from ⟨by omega, by simp [parity_simps]⟩,
        show (2 * m + 4) / 2 - 2 = m by rw [show 2 * m + 4 = 2 * (m + 2) by ring]; simp]
    have hexp : cexp (π * I * ((Int.ofNat (2 * m + 4) : ℂ)) * (x : ℂ)) =
        cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ)) :=
      congrArg Complex.exp <| show (π * I * ((2 * m + 4 : ℕ) : ℂ) * (x : ℂ)) =
        (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ)) by push_cast; ring
    dsimp [f, g, fouterm]
    rw [show (2 * (m : ℤ) + 4 : ℤ) = Int.ofNat (2 * m + 4) by simp, hc, hexp]
  rw [show (∑' n : ℕ, f n) = (∑' m : ℕ, g m) by
    simpa [tsum_congr heven_term, tsum_congr hodd_term] using
      (tsum_even_add_odd (f := f)
        ((summable_congr heven_term).mpr (by simpa [g] using A_E_sq_series_summable x))
        (by simp [funext hodd_term] : Summable (fun m : ℕ => f (2 * m + 1)))).symm]
  exact A_E_sq_eq_tsum x

/-- Exponential decay for the magic function `φ₀` in the upper half-plane. -/
public theorem norm_φ₀_le : ∃ C₀ > 0, ∀ z : ℍ, 1 / 2 < z.im →
    norm (φ₀ z) ≤ C₀ * rexp (-2 * π * z.im) := by
  refine ⟨DivDiscBound A_E_sq_fourierCoeff 4, ?_, ?_⟩
  · simpa [gt_iff_lt] using
      DivDiscBound_pos (c := A_E_sq_fourierCoeff) (n₀ := (4 : ℤ))
        (hcn₀ := A_E_sq_fourierCoeff_four_ne_zero) (k := 11) (hpoly := A_E_sq_fourierCoeff_isBigO)
  · intro z hz
    have hmain :
        norm (((A_E z) ^ 2) / (Δ z)) ≤
          (DivDiscBound A_E_sq_fourierCoeff 4) * rexp (-π * ((4 : ℤ) - 2) * z.im) :=
      DivDiscBoundOfPolyFourierCoeff (z := z) (hz := hz) (c := A_E_sq_fourierCoeff)
        (n₀ := (4 : ℤ)) (hcsum := by simpa using A_E_sq_fourierCoeff_summable (z := z) hz)
        (k := 11) (hpoly := A_E_sq_fourierCoeff_isBigO) (f := fun z ↦ (A_E z) ^ 2)
        (hf := fun x => by simpa using A_E_sq_fourierCoeff_hf (x := x))
    have hrexp : rexp (-(π * (4 - 2) * z.im)) = rexp (-(2 * π * z.im)) := by congr 1; ring
    simpa [φ₀, A_E, hrexp] using hmain

/-- Uniform bound for `φ₀''` on `Im z > 1/2`, specialising `norm_φ₀_le`. -/
public lemma norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im {C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, 1 / 2 < z.im → ‖φ₀ z‖ ≤ C₀ * rexp (-2 * π * z.im)) (z : ℍ)
    (hz : 1 / 2 < z.im) : ‖φ₀'' (z : ℂ)‖ ≤ C₀ * rexp (-π) := by
  have hzpos : 0 < (z : ℂ).im := by simpa using lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hz
  have hexp : rexp (-2 * π * z.im) ≤ rexp (-π) :=
    Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, hz])
  calc
    ‖φ₀'' (z : ℂ)‖ = ‖φ₀ z‖ := by
      simp [φ₀''_def (z := (z : ℂ)) hzpos, show (⟨(z : ℂ), hzpos⟩ : ℍ) = z from by ext; rfl]
    _ ≤ C₀ * rexp (-2 * π * z.im) := hC₀ z hz
    _ ≤ C₀ * rexp (-π) := mul_le_mul_of_nonneg_left hexp hC₀_pos.le

end

end MagicFunction.PolyFourierCoeffBound
