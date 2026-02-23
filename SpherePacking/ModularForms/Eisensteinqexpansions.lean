module
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Inv
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded

public import SpherePacking.ModularForms.Delta


/-!
# `q`-expansion for Eisenstein series

This file defines the normalized level-one Eisenstein series `E k` (for `k >= 3`) and proves a
`q`-expansion formula compatible with the conventions used in this repository.

## Main definitions
* `standardcongruencecondition`
* `E`

## Main statement
* `E_k_q_expansion`
-/
open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open scoped ArithmeticFunction.sigma

open EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

noncomputable section Definitions

/-- The standard congruence condition used to define Eisenstein series at level one. -/
@[expose] public def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0

/-- The (normalized) Eisenstein series of weight `k` as a modular form on `Γ(1)`. -/
@[expose] public def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma ↑1) k :=
  (1/2 : ℂ) • ModularForm.eisensteinSeriesMF hk standardcongruencecondition -- normalization

/-Forwards to `EisensteinSeries.q_expansion_riemannZeta` from mathlib. -/
lemma E_k_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (E k hk) z = 1 +
        (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, σ (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by
  rw [_root_.E]
  let F : ℍ → ℂ :=
    (1 / 2 : ℂ) • (ModularForm.eisensteinSeriesMF hk standardcongruencecondition : ℍ → ℂ)
  change F z = _
  calc
    F z =
        1 + (riemannZeta k)⁻¹ * (-2 * ↑π * Complex.I) ^ k / (k - 1)! *
          ∑' n : ℕ+, σ (k - 1) n * cexp (2 * ↑π * Complex.I * z) ^ (n : ℤ) := by
      have hq := EisensteinSeries.q_expansion_riemannZeta (k := k) (by omega) hk2 z
      rw [ModularForm.E] at hq
      change F z = _ at hq
      exact hq
    _ = 1 + (1 / riemannZeta k) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
          ∑' n : ℕ+, σ (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by
      rw [show ∑' n : ℕ+, σ (k - 1) n * cexp (2 * ↑π * Complex.I * z) ^ (n : ℤ) =
          ∑' n : ℕ+, σ (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) from by
            apply tsum_congr
            intro n
            rw [zpow_natCast, ← Complex.exp_nat_mul]
            ring_nf]
      simp [div_eq_mul_inv, mul_assoc]
