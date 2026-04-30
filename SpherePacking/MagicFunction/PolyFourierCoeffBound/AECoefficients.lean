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
  nlinarith [show ‖A_E_coeff n‖ = (720 : ℝ) * ((n + 1 : ℕ) : ℝ) * (σ 3 (n + 1) : ℝ) by
    simpa using norm_A_E_coeff (n := n),
    show (σ 3 (n + 1) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 4 from mod_cast sigma_bound 3 (n + 1),
    Nat.zero_le n]

public lemma norm_A_E_coeff_le_of_le {n m : ℕ} (hn : n ≤ m) :
    ‖A_E_coeff n‖ ≤ (720 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 5 :=
  (norm_A_E_coeff_le (n := n)).trans (by gcongr)

public lemma norm_A_E_sq_coeff_le (m : ℕ) :
    ‖A_E_sq_coeff m‖ ≤ (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 11 := by
  have hterm (p : ℕ × ℕ) (hp : p ∈ Finset.antidiagonal m) :
      ‖A_E_coeff p.1 * A_E_coeff p.2‖ ≤ (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10 := by
    have hsum : p.1 + p.2 = m := by simpa [Finset.mem_antidiagonal] using hp
    rw [norm_mul, show (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10 =
      ((720 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 5) * ((720 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 5) from by ring]
    gcongr <;> exact norm_A_E_coeff_le_of_le (by omega)
  calc ‖A_E_sq_coeff m‖
      = ‖∑ p ∈ Finset.antidiagonal m, A_E_coeff p.1 * A_E_coeff p.2‖ := by simp [A_E_sq_coeff]
    _ ≤ ∑ p ∈ Finset.antidiagonal m, ‖A_E_coeff p.1 * A_E_coeff p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ Finset.antidiagonal m, (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10 :=
        Finset.sum_le_sum hterm
    _ = (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 11 := by simp [Finset.Nat.card_antidiagonal]; ring

public lemma A_E_sq_eq_tsum (z : ℍ) :
    (A_E z) ^ 2 =
      ∑' m : ℕ, A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
  have ht_norm : Summable (fun n : ℕ => ‖A_E_term z n‖) := by
    set r : ℝ := Real.exp (-2 * Real.pi * z.im)
    let g : ℕ → ℝ := fun n => (720 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 5 * r ^ (n + 1)
    have hg : Summable g := by
      simpa [g, mul_assoc, mul_left_comm, mul_comm, Nat.cast_add, Nat.cast_one] using
        ((summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * r ^ n) 1).2
          (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5 (by
            simpa [r, Real.norm_of_nonneg (Real.exp_pos _).le] using Real.exp_lt_one_iff.2 (by
              nlinarith [Real.pi_pos, UpperHalfPlane.im_pos z] :
                (-2 * Real.pi * z.im) < 0)))).mul_left (720 : ℝ)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hg
    have hexp : ‖cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))‖ ≤ r ^ (n + 1) := by
      rw [show ‖cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))‖ =
          rexp (((n + 1 : ℕ) : ℝ) * (-2 * π * z.im)) from by
        simp [Complex.norm_exp, mul_re, mul_im, mul_assoc, mul_left_comm, mul_comm],
        Real.exp_nat_mul]
    calc ‖A_E_term z n‖
        = ‖A_E_coeff n‖ * ‖cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))‖ := by simp [A_E_term]
      _ ≤ ((720 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 5) * (r ^ (n + 1)) :=
          mul_le_mul (norm_A_E_coeff_le n) hexp (norm_nonneg _) (by positivity)
      _ = g n := by simp [g, mul_assoc, mul_comm]
  have hanti (m : ℕ) :
      (∑ p ∈ Finset.antidiagonal m, A_E_term z p.1 * A_E_term z p.2) =
        A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
    rw [show (∑ p ∈ Finset.antidiagonal m, A_E_term z p.1 * A_E_term z p.2) =
        ∑ p ∈ Finset.antidiagonal m, (A_E_coeff p.1 * A_E_coeff p.2) *
            cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) from Finset.sum_congr rfl fun p hp => by
      have hsum : p.1 + p.2 = m := by simpa [Finset.mem_antidiagonal] using hp
      have hexp : cexp (2 * π * I * ((p.1 + 1 : ℕ) : ℂ) * (z : ℂ)) *
          cexp (2 * π * I * ((p.2 + 1 : ℕ) : ℂ) * (z : ℂ)) =
            cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1; push_cast [← (show (p.1 + 1 : ℕ) + (p.2 + 1 : ℕ) = m + 2 from by omega)]; ring
      dsimp [A_E_term]; exact CancelDenoms.mul_subst rfl hexp rfl]
    simp [Finset.sum_mul, A_E_sq_coeff, mul_assoc]
  rw [show (A_E z) ^ 2 = (∑' n : ℕ, A_E_term z n) * (∑' n : ℕ, A_E_term z n) from by
    rw [← A_E_eq_tsum (z := z)]; ring,
    (by simpa using tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ht_norm ht_norm :
      (∑' n : ℕ, A_E_term z n) * (∑' n : ℕ, A_E_term z n) =
        ∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, A_E_term z p.1 * A_E_term z p.2)]
  exact tsum_congr hanti

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
  simp [A_E_sq_fourierCoeff, show 4 ≤ (4 : ℕ) ∧ Even (4 : ℕ) by decide, A_E_sq_coeff, A_E_coeff,
    show (720 : ℂ) ≠ 0 by norm_num]

public lemma norm_A_E_sq_fourierCoeff_ofNat_le (j : ℕ) (hj : 4 ≤ j) :
    ‖A_E_sq_fourierCoeff (Int.ofNat j)‖ ≤ (720 : ℝ) ^ 2 * (j : ℝ) ^ 11 := by
  by_cases hjEven : Even j
  · calc ‖A_E_sq_fourierCoeff (Int.ofNat j)‖ = ‖A_E_sq_coeff (j / 2 - 2)‖ := by
          simp [A_E_sq_fourierCoeff, hj, hjEven]
      _ ≤ (720 : ℝ) ^ 2 * ((j / 2 - 2 + 1 : ℕ) : ℝ) ^ 11 := by
          simpa using norm_A_E_sq_coeff_le (m := (j / 2 - 2))
      _ ≤ (720 : ℝ) ^ 2 * (j : ℝ) ^ 11 := by
          gcongr; exact_mod_cast (by omega : j / 2 - 2 + 1 ≤ j)
  · simp [A_E_sq_fourierCoeff, show ¬(4 ≤ j ∧ Even j) from fun h => hjEven h.2,
      show 0 ≤ (720 : ℝ) ^ 2 * (j : ℝ) ^ 11 by positivity]

public lemma A_E_sq_fourierCoeff_isBigO :
    A_E_sq_fourierCoeff =O[atTop] (fun n ↦ (n ^ 11 : ℝ)) := by
  simp only [isBigO_iff, eventually_atTop, ge_iff_le]
  refine ⟨(720 : ℝ) ^ 2, (4 : ℤ), fun n hn => ?_⟩
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (by decide : (0 : ℤ) ≤ 4) hn)
  simpa using norm_A_E_sq_fourierCoeff_ofNat_le j (Int.ofNat_le.mp (by simpa using hn))

public lemma A_E_sq_fourierCoeff_summable (z : ℍ) (hz : 1 / 2 < z.im) :
    Summable (fun i : ℕ ↦ fouterm A_E_sq_fourierCoeff z (i + 4)) := by
  set r : ℝ := Real.exp (-Real.pi / 2)
  let g : ℕ → ℝ := fun m => ((m : ℝ) ^ 11) * r ^ m
  have hshift : Summable (fun n : ℕ => g (n + 4)) := by
    simpa [g] using (summable_nat_add_iff (f := g) 4).2
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 11 (by
        simpa [r, Real.norm_of_nonneg (Real.exp_pos _).le] using
          Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos] : (-Real.pi / 2 : ℝ) < 0)))
  refine Summable.of_norm <| Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (hshift.mul_left ((720 : ℝ) ^ 2))
  have hexp : ‖cexp (↑π * I * (Int.ofNat (n + 4)) * z)‖ ≤ r ^ (n + 4) := by
    rw [show ‖cexp (↑π * I * (Int.ofNat (n + 4)) * z)‖ =
        Real.exp ((-Real.pi * ((n + 4 : ℕ) : ℝ)) * z.im) from by
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
    Summable (fun m : ℕ =>
      A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))) := by
  set r : ℝ := Real.exp (-2 * Real.pi * x.im)
  have hg2 : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ 11 * r ^ (m + 2)) := by
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm, Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff (f := fun m : ℕ => ((m : ℝ) ^ 11) * r ^ m) 1).2
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 11 (by
          simpa [r, Real.norm_of_nonneg (Real.exp_pos _).le] using Real.exp_lt_one_iff.2 (by
            nlinarith [Real.pi_pos, UpperHalfPlane.im_pos x] :
              (-2 * Real.pi * x.im) < 0)))).mul_right r
  refine Summable.of_norm <| Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (hg2.mul_left ((720 : ℝ) ^ 2))
  have hexp : ‖cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖ ≤ r ^ (m + 2) := by
    rw [show ‖cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖ =
        Real.exp (((m + 2 : ℕ) : ℝ) * (-2 * Real.pi * x.im)) from by
      simp [Complex.norm_exp, mul_re, mul_im, mul_assoc, mul_left_comm, mul_comm], Real.exp_nat_mul]
  calc ‖A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖
      = ‖A_E_sq_coeff m‖ * ‖cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖ := by simp
    _ ≤ ((720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 11) * (r ^ (m + 2)) :=
        mul_le_mul (norm_A_E_sq_coeff_le m) hexp (norm_nonneg _) (by positivity)
    _ = ((720 : ℝ) ^ 2) * (((m + 1 : ℕ) : ℝ) ^ 11 * r ^ (m + 2)) := by ring_nf

public lemma A_E_sq_fourierCoeff_hf (x : ℍ) :
    (A_E x) ^ 2 = ∑' (n : ℕ), fouterm A_E_sq_fourierCoeff x (n + 4) := by
  have hA2 := A_E_sq_eq_tsum (z := x)
  let f : ℕ → ℂ := fun n => fouterm A_E_sq_fourierCoeff x (n + 4)
  let g : ℕ → ℂ := fun m =>
    A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))
  have hodd_term (m : ℕ) : f (2 * m + 1) = 0 := by
    simp only [f, fouterm, show ((2 * m + 1 : ℕ) : ℤ) + (4 : ℤ) = (Int.ofNat (2 * m + 5)) by
      simpa [show (2 * m + 1) + 4 = 2 * m + 5 by omega] using Int.ofNat_add_ofNat (2 * m + 1) 4,
      A_E_sq_fourierCoeff, if_neg (show ¬(4 ≤ (2 * m + 5) ∧ Even (2 * m + 5)) by
        grind only [= Nat.even_iff]), zero_mul]
  have heven_term (m : ℕ) : f (2 * m) = g m := by
    have hc : A_E_sq_fourierCoeff (Int.ofNat (2 * m + 4)) = A_E_sq_coeff m := by
      simp [A_E_sq_fourierCoeff,
        show 4 ≤ (2 * m + 4) ∧ Even (2 * m + 4) from ⟨by omega, by simp [parity_simps]⟩,
        show (2 * m + 4) / 2 - 2 = m by rw [show 2 * m + 4 = 2 * (m + 2) from by ring]; simp]
    have hexp : cexp (π * I * ((Int.ofNat (2 * m + 4) : ℂ)) * (x : ℂ)) =
        cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ)) :=
      congrArg Complex.exp
        (show (π * I * ((2 * m + 4 : ℕ) : ℂ) * (x : ℂ)) =
          (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ)) by push_cast; ring)
    dsimp [f, g, fouterm]
    rw [show (2 * (m : ℤ) + 4 : ℤ) = Int.ofNat (2 * m + 4) from by simp, hc, hexp]
  have ho : Summable (fun m : ℕ => f (2 * m + 1)) := by simp [funext hodd_term]
  have he : Summable (fun m : ℕ => f (2 * m)) :=
    (summable_congr heven_term).mpr (by simpa [g] using A_E_sq_series_summable (x := x))
  have hsplit : (∑' m : ℕ, f (2 * m)) + (∑' m : ℕ, f (2 * m + 1)) = ∑' n : ℕ, f n :=
    tsum_even_add_odd (f := f) he ho
  have hodd_sum : (∑' m : ℕ, f (2 * m + 1)) = 0 := by simp [tsum_congr hodd_term]
  have heven_sum : (∑' m : ℕ, f (2 * m)) = ∑' m : ℕ, g m := tsum_congr heven_term
  grind only

end Corollaries

end

end MagicFunction.PolyFourierCoeffBound
