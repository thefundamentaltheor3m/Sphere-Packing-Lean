/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.PolyFourierCoeffBound.Basic


/-!
# Fourier coefficients of `(A_E)^2`

This file specializes the general `DivDiscBound` framework from
`SpherePacking.MagicFunction.PolyFourierCoeffBound.Basic` to the function
`(A_E)^2` arising from the Eisenstein series expansion `E₂ * E₄ - E₆`.

We compute the `ℕ`-indexed Cauchy product of the `A_E` coefficients with itself
and repackage it as an `ℤ`-indexed `fouterm` Fourier series in the `π i`
convention, vanishing on odd indices. The main summability statements feed into
the bound `DivDiscBoundOfPolyFourierCoeff` in `Application.lean`.

## Main definitions
* `MagicFunction.PolyFourierCoeffBound.A_E_sq_coeff`
* `MagicFunction.PolyFourierCoeffBound.A_E_sq_fourierCoeff`
-/

namespace MagicFunction.PolyFourierCoeffBound

noncomputable section

open scoped UpperHalfPlane ArithmeticFunction.sigma BigOperators

open Filter Complex Real Asymptotics ArithmeticFunction

section Corollaries


public def A_E_sq_coeff (m : ℕ) : ℂ :=
  ∑ p ∈ Finset.antidiagonal m, A_E_coeff p.1 * A_E_coeff p.2

public lemma norm_A_E_coeff_le (n : ℕ) :
    ‖A_E_coeff n‖ ≤ (720 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 5 := by
  have hσ : (σ 3 (n + 1) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 4 := by
    exact_mod_cast (sigma_bound 3 (n + 1))
  calc
    ‖A_E_coeff n‖ = (720 : ℝ) * ((n + 1 : ℕ) : ℝ) * (σ 3 (n + 1) : ℝ) := by
      simpa using (norm_A_E_coeff (n := n))
    _ ≤ (720 : ℝ) * ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 4 := by gcongr
    _ = (720 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 5 := by ring

public lemma norm_A_E_coeff_le_of_le {n m : ℕ} (hn : n ≤ m) :
    ‖A_E_coeff n‖ ≤ (720 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 5 :=
  (norm_A_E_coeff_le (n := n)).trans (by gcongr)

public lemma norm_A_E_sq_coeff_le (m : ℕ) :
    ‖A_E_sq_coeff m‖ ≤ (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 11 := by
  have hterm (p : ℕ × ℕ) (hp : p ∈ Finset.antidiagonal m) :
      ‖A_E_coeff p.1 * A_E_coeff p.2‖ ≤ (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10 := by
    have hsum : p.1 + p.2 = m := by simpa [Finset.mem_antidiagonal] using hp
    have hp₁ : p.1 ≤ m := by omega
    have hp₂ : p.2 ≤ m := by omega
    calc
      ‖A_E_coeff p.1 * A_E_coeff p.2‖
          = ‖A_E_coeff p.1‖ * ‖A_E_coeff p.2‖ := by simp
      _ ≤ ((720 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 5) * ((720 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 5) := by
            gcongr <;> exact norm_A_E_coeff_le_of_le ‹_›
      _ = (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10 := by ring
  calc
    ‖A_E_sq_coeff m‖
        = ‖∑ p ∈ Finset.antidiagonal m, A_E_coeff p.1 * A_E_coeff p.2‖ := by
            simp [A_E_sq_coeff]
    _ ≤ ∑ p ∈ Finset.antidiagonal m, ‖A_E_coeff p.1 * A_E_coeff p.2‖ :=
          norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.antidiagonal m, (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10 :=
          Finset.sum_le_sum hterm
    _ = ((m + 1 : ℕ) : ℝ) * ((720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10) := by
            simp [Finset.sum_const, nsmul_eq_mul, Finset.Nat.card_antidiagonal]
    _ = (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 11 := by ring

public lemma A_E_sq_eq_tsum (z : ℍ) :
    (A_E z) ^ 2 =
      ∑' m : ℕ, A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
  let t : ℕ → ℂ := fun n => A_E_term z n
  have hA : A_E z = ∑' n : ℕ, t n := by simpa [t] using A_E_eq_tsum (z := z)
  have ht_norm : Summable (fun n : ℕ => ‖t n‖) := by
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
      have hnorm :
          ‖cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))‖ =
            rexp (-2 * π * ((n + 1 : ℕ) : ℝ) * z.im) := by
        simp [Complex.norm_exp, mul_re, mul_im, mul_assoc, mul_left_comm, mul_comm]
      have hrpow :
          rexp (-2 * π * ((n + 1 : ℕ) : ℝ) * z.im) = r ^ (n + 1) := by
        calc
          rexp (-2 * π * ((n + 1 : ℕ) : ℝ) * z.im)
              = rexp (((n + 1 : ℕ) : ℝ) * (-2 * π * z.im)) := by
                    ring_nf
          _ = rexp (-2 * π * z.im) ^ (n + 1) := by
                simpa using (Real.exp_nat_mul (-2 * π * z.im) (n + 1))
          _ = r ^ (n + 1) := by simp [r]
      exact le_of_eq (hnorm.trans hrpow)
    have hcoeff : ‖A_E_coeff n‖ ≤ (720 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 5 :=
      norm_A_E_coeff_le (n := n)
    calc
      ‖t n‖ = ‖A_E_coeff n‖ * ‖cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))‖ := by
        simp [t, A_E_term]
      _ ≤ ((720 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 5) * (r ^ (n + 1)) :=
        mul_le_mul hcoeff hexp (norm_nonneg _) (by positivity)
      _ = g n := by simp [g, mul_assoc, mul_comm]
  have hprod :
      (∑' n : ℕ, t n) * (∑' n : ℕ, t n) =
        ∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, t p.1 * t p.2 := by
    simpa using (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ht_norm ht_norm)
  have hanti (m : ℕ) :
      (∑ p ∈ Finset.antidiagonal m, t p.1 * t p.2) =
        A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
    have hmul (p : ℕ × ℕ) (hp : p ∈ Finset.antidiagonal m) :
        t p.1 * t p.2 =
          (A_E_coeff p.1 * A_E_coeff p.2) *
            cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
      have hm : p.1 + p.2 = m := by simpa [Finset.mem_antidiagonal] using hp
      have hadd : (p.1 + 1 : ℕ) + (p.2 + 1 : ℕ) = m + 2 := by omega
      have hcast :
          ((p.1 + 1 : ℕ) : ℂ) + ((p.2 + 1 : ℕ) : ℂ) = ((m + 2 : ℕ) : ℂ) := by
        simpa [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℂ)) hadd
      have huv :
          2 * π * I * ((p.1 + 1 : ℕ) : ℂ) * (z : ℂ) +
              2 * π * I * ((p.2 + 1 : ℕ) : ℂ) * (z : ℂ) =
            2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ) := by
        grind only
      have hexp :
          cexp (2 * π * I * ((p.1 + 1 : ℕ) : ℂ) * (z : ℂ)) *
              cexp (2 * π * I * ((p.2 + 1 : ℕ) : ℂ) * (z : ℂ)) =
            cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
        rw [← Complex.exp_add]; exact congrArg Complex.exp huv
      dsimp [t, A_E_term]
      exact CancelDenoms.mul_subst rfl hexp rfl
    calc
      (∑ p ∈ Finset.antidiagonal m, t p.1 * t p.2)
          = ∑ p ∈ Finset.antidiagonal m,
              (A_E_coeff p.1 * A_E_coeff p.2) *
                cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) :=
                Finset.sum_congr rfl hmul
      _ = A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
            simp [Finset.sum_mul, A_E_sq_coeff, mul_assoc]
  calc
    (A_E z) ^ 2 = (∑' n : ℕ, t n) * (∑' n : ℕ, t n) := by simp [hA, pow_two]
    _ = ∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, t p.1 * t p.2 := hprod
    _ = ∑' m : ℕ, A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) :=
          tsum_congr hanti

/-!
### Converting to `fouterm` coefficients

`DivDiscBoundOfPolyFourierCoeff` expects a `π i`-Fourier series with coefficients indexed by `ℤ`.
The expansion `A_E_sq_eq_tsum` is a `2π i`-series indexed by `ℕ`. We convert by forcing odd
indices to vanish and matching even indices.
-/

public noncomputable def A_E_sq_fourierCoeff : ℤ → ℂ
  | (Int.ofNat j) =>
      if 4 ≤ j ∧ Even j then A_E_sq_coeff (j / 2 - 2) else 0
  | (Int.negSucc _) => 0

public lemma A_E_sq_fourierCoeff_four_ne_zero : A_E_sq_fourierCoeff 4 ≠ 0 := by
  have hcond : 4 ≤ (4 : ℕ) ∧ Even (4 : ℕ) := by decide
  have h720 : (720 : ℂ) ≠ 0 := by norm_num
  simp [A_E_sq_fourierCoeff, hcond, A_E_sq_coeff, A_E_coeff, h720]

public lemma norm_A_E_sq_fourierCoeff_ofNat_le (j : ℕ) (hj : 4 ≤ j) :
    ‖A_E_sq_fourierCoeff (Int.ofNat j)‖ ≤ (720 : ℝ) ^ 2 * (j : ℝ) ^ 11 := by
  by_cases hjEven : Even j
  · have hcond : 4 ≤ j ∧ Even j := ⟨hj, hjEven⟩
    have hmle : j / 2 - 2 + 1 ≤ j := by omega
    have hpow : ((j / 2 - 2 + 1 : ℕ) : ℝ) ^ 11 ≤ (j : ℝ) ^ 11 :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hmle) 11
    calc
      ‖A_E_sq_fourierCoeff (Int.ofNat j)‖ = ‖A_E_sq_coeff (j / 2 - 2)‖ := by
        simp [A_E_sq_fourierCoeff, hcond]
      _ ≤ (720 : ℝ) ^ 2 * ((j / 2 - 2 + 1 : ℕ) : ℝ) ^ 11 := by
        simpa using norm_A_E_sq_coeff_le (m := (j / 2 - 2))
      _ ≤ (720 : ℝ) ^ 2 * (j : ℝ) ^ 11 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
  · have hcond : ¬(4 ≤ j ∧ Even j) := fun h => hjEven h.2
    have hnonneg : 0 ≤ (720 : ℝ) ^ 2 * (j : ℝ) ^ 11 := by positivity
    simp [A_E_sq_fourierCoeff, hcond, hnonneg]

public lemma A_E_sq_fourierCoeff_isBigO :
    A_E_sq_fourierCoeff =O[atTop] (fun n ↦ (n ^ 11 : ℝ)) := by
  simp only [isBigO_iff, eventually_atTop, ge_iff_le]
  refine ⟨(720 : ℝ) ^ 2, (4 : ℤ), fun n hn => ?_⟩
  rcases Int.eq_ofNat_of_zero_le (le_trans (by decide : (0 : ℤ) ≤ 4) hn) with ⟨j, rfl⟩
  simpa using norm_A_E_sq_fourierCoeff_ofNat_le (j := j) (Int.ofNat_le.mp (by simpa using hn))

public lemma A_E_sq_fourierCoeff_summable (z : ℍ) (hz : 1 / 2 < z.im) :
    Summable (fun i : ℕ ↦ fouterm A_E_sq_fourierCoeff z (i + 4)) := by
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
    have hnonpos : -Real.pi * ((n + 4 : ℕ) : ℝ) ≤ 0 := by nlinarith [Real.pi_pos]
    have hle :
        (-Real.pi * ((n + 4 : ℕ) : ℝ)) * z.im ≤
          (-Real.pi * ((n + 4 : ℕ) : ℝ)) * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonpos_left hz' hnonpos
    have hmono := Real.exp_le_exp.2 hle
    have hpow :
        Real.exp ((-Real.pi * ((n + 4 : ℕ) : ℝ)) * (1 / 2 : ℝ)) = r ^ (n + 4) := by
      calc
        Real.exp ((-Real.pi * ((n + 4 : ℕ) : ℝ)) * (1 / 2 : ℝ))
            = Real.exp (((n + 4 : ℕ) : ℝ) * (-Real.pi / 2 : ℝ)) := by
                  ring_nf
        _ = Real.exp (-Real.pi / 2) ^ (n + 4) := by
              simpa using Real.exp_nat_mul (-Real.pi / 2) (n + 4)
        _ = r ^ (n + 4) := by simp [r]
    have hnorm' :
        Real.exp (-Real.pi * ((n + 4 : ℕ) : ℝ) * z.im) =
          Real.exp ((-Real.pi * ((n + 4 : ℕ) : ℝ)) * z.im) := by ring_nf
    exact (le_of_eq (hnorm.trans hnorm')).trans (hmono.trans_eq hpow)
  calc
    ‖fouterm A_E_sq_fourierCoeff z (n + 4)‖
        = ‖A_E_sq_fourierCoeff (Int.ofNat (n + 4))‖ *
            ‖cexp (↑π * I * (Int.ofNat (n + 4)) * z)‖ := by
          simp [fouterm]
    _ ≤ ((720 : ℝ) ^ 2 * ((n + 4 : ℕ) : ℝ) ^ 11) * (r ^ (n + 4)) := by gcongr
    _ = ((720 : ℝ) ^ 2) * g (n + 4) := by
          simp [g, mul_assoc, mul_left_comm, mul_comm]

public lemma A_E_sq_series_summable (x : ℍ) :
    Summable (fun m : ℕ =>
      A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))) := by
  let r : ℝ := Real.exp (-2 * Real.pi * x.im)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr : ‖r‖ < 1 := by
    have hx : (-2 * Real.pi * x.im) < 0 := by
      have : 0 < x.im := UpperHalfPlane.im_pos x
      nlinarith [Real.pi_pos, this]
    simpa [r, Real.norm_of_nonneg hr0] using (Real.exp_lt_one_iff.2 hx)
  let g0 : ℕ → ℝ := fun m => ((m : ℝ) ^ 11) * r ^ m
  have hg0 : Summable g0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 11 hr
  have hg1 : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ 11 * r ^ (m + 1)) := by
    simpa [g0, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff (f := g0) 1).2 hg0
  have hg2 : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ 11 * r ^ (m + 2)) := by
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hg1.mul_right r
  refine Summable.of_norm ?_
  refine (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ (hg2.mul_left ((720 : ℝ) ^ 2)))
  intro m
  have hcoeff : ‖A_E_sq_coeff m‖ ≤ (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 11 :=
    norm_A_E_sq_coeff_le (m := m)
  have hexp :
      ‖cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖ ≤ r ^ (m + 2) := by
    have hnorm :
        ‖cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖ =
          Real.exp (-2 * Real.pi * ((m + 2 : ℕ) : ℝ) * x.im) := by
      simp [Complex.norm_exp, mul_re, mul_im, mul_assoc, mul_left_comm, mul_comm]
    have hrpow :
        Real.exp (-2 * Real.pi * ((m + 2 : ℕ) : ℝ) * x.im) = r ^ (m + 2) := by
      calc
        Real.exp (-2 * Real.pi * ((m + 2 : ℕ) : ℝ) * x.im)
            = Real.exp (((m + 2 : ℕ) : ℝ) * (-2 * Real.pi * x.im)) := by ring_nf
        _ = Real.exp (-2 * Real.pi * x.im) ^ (m + 2) := by
              simpa using (Real.exp_nat_mul (-2 * Real.pi * x.im) (m + 2))
        _ = r ^ (m + 2) := by simp [r]
    exact le_of_eq (hnorm.trans hrpow)
  calc
    ‖A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖
        = ‖A_E_sq_coeff m‖ * ‖cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖ := by simp
    _ ≤ ((720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 11) * (r ^ (m + 2)) :=
              mul_le_mul hcoeff hexp (norm_nonneg _) (by positivity)
    _ = ((720 : ℝ) ^ 2) * (((m + 1 : ℕ) : ℝ) ^ 11 * r ^ (m + 2)) := by ring_nf

public lemma A_E_sq_fourierCoeff_hf :
    ∀ x : ℍ, (A_E x) ^ 2 = ∑' (n : ℕ), fouterm A_E_sq_fourierCoeff x (n + 4) := by
  intro x
  have hA2 := A_E_sq_eq_tsum (z := x)
  let f : ℕ → ℂ := fun n => fouterm A_E_sq_fourierCoeff x (n + 4)
  let g : ℕ → ℂ := fun m =>
    A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))
  have hodd_term (m : ℕ) : f (2 * m + 1) = 0 := by
    have hidxNat : (2 * m + 1) + 4 = 2 * m + 5 := by omega
    have hidx : ((2 * m + 1 : ℕ) : ℤ) + (4 : ℤ) = (Int.ofNat (2 * m + 5)) := by
      simpa [hidxNat] using (Int.ofNat_add_ofNat (2 * m + 1) 4)
    have hcond : ¬(4 ≤ (2 * m + 5) ∧ Even (2 * m + 5)) := by
      grind only [= Nat.even_iff]
    dsimp [f, fouterm]
    have : A_E_sq_fourierCoeff (((2 * m + 1 : ℕ) : ℤ) + 4) = 0 := by
      rw [hidx]
      change
        (if 4 ≤ (2 * m + 5) ∧ Even (2 * m + 5) then A_E_sq_coeff ((2 * m + 5) / 2 - 2) else 0) = 0
      rw [if_neg hcond]
    simpa [this]
  have heven_term (m : ℕ) : f (2 * m) = g m := by
    let i : ℤ := ((2 * m : ℕ) : ℤ) + 4
    have hi : i = Int.ofNat (2 * m + 4) := by dsimp [i]
    have hcond : 4 ≤ (2 * m + 4) ∧ Even (2 * m + 4) :=
      ⟨by omega, by simp [parity_simps]⟩
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
        push_cast; ring
      have harg :
          (π * I * ((2 * m + 4 : ℕ) : ℂ) * (x : ℂ)) =
            (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ)) := by
        rw [hcast]; ring
      have hexpNat :
          cexp (π * I * ((2 * m + 4 : ℕ) : ℂ) * (x : ℂ)) =
            cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ)) := by
        simpa using congrArg Complex.exp harg
      simpa [hi] using hexpNat
    dsimp [f, g, fouterm]
    have hidx : 2 * (m : ℤ) + 4 = i := by dsimp [i]
    rw [hidx, hc, hexp]
  have ho : Summable (fun m : ℕ => f (2 * m + 1)) := by
    have hzero : (fun m : ℕ => f (2 * m + 1)) = 0 := by
      funext m; simpa using hodd_term m
    rw [hzero]; exact summable_zero
  have hs_g : Summable g := by simpa [g] using A_E_sq_series_summable (x := x)
  have he : Summable (fun m : ℕ => f (2 * m)) :=
    (summable_congr heven_term).mpr hs_g
  have hsplit :
      (∑' m : ℕ, f (2 * m)) + (∑' m : ℕ, f (2 * m + 1)) = ∑' n : ℕ, f n :=
    tsum_even_add_odd (f := f) he ho
  have hodd_sum : (∑' m : ℕ, f (2 * m + 1)) = 0 := by
    simp [tsum_congr hodd_term]
  have heven_sum : (∑' m : ℕ, f (2 * m)) = ∑' m : ℕ, g m := tsum_congr heven_term
  grind only

end Corollaries

end

end MagicFunction.PolyFourierCoeffBound
