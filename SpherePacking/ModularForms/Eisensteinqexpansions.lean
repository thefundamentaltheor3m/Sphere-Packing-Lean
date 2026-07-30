/-
Copyright (c) 2024 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

public import SpherePacking.ModularForms.Delta

/-!
# `q`-expansions of Eisenstein series

This file defines the normalised level-one Eisenstein series `E k` as a modular form for `Γ(1)`
(mathlib's `ModularForm.E` is typed over `𝒮ℒ`; the two coincide as functions on `ℍ`) and restates
its `q`-expansion `EisensteinSeries.q_expansion_riemannZeta` with the exponential written as
`exp (2πinz)`.
-/

@[expose] public section

open UpperHalfPlane Complex ModularForm

open scoped Real Nat ArithmeticFunction.sigma

noncomputable section

/-- The normalised Eisenstein series of weight `k` and level one, with constant term `1`.
The scaling by `1/2` matches the normalisation, since the sum is taken over coprime pairs. -/
def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma 1) k :=
  (1 / 2 : ℂ) • eisensteinSeriesMF hk 0

/-- The `q`-expansion of `E k` with `riemannZeta` coefficient; forwards to mathlib's
`EisensteinSeries.q_expansion_riemannZeta`. -/
lemma E_k_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (E k hk) z = 1 +
        (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, σ (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by
  have hq : (E k hk) z = 1 + (riemannZeta k)⁻¹ * (-2 * ↑π * Complex.I) ^ k / (k - 1)! *
      ∑' n : ℕ+, σ (k - 1) n * cexp (2 * ↑π * Complex.I * z) ^ (n : ℤ) :=
    EisensteinSeries.q_expansion_riemannZeta (by omega) hk2 z
  have ht : ∑' n : ℕ+, (σ (k - 1) n : ℂ) * cexp (2 * ↑π * Complex.I * z) ^ (n : ℤ) =
      ∑' n : ℕ+, σ (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) :=
    tsum_congr fun n => by rw [zpow_natCast, ← Complex.exp_nat_mul]; ring_nf
  rw [hq, ht]
  ring
