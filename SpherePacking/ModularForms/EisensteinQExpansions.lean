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

/-- `q`-expansion formula for `E k`, specialized to the conventions used in this repository. -/
public lemma E_k_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (E k hk) z = 1 +
        (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, σ (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by
  have h := EisensteinSeries.q_expansion_riemannZeta (show 3 ≤ k by exact_mod_cast hk) hk2 z
  show (ModularForm.E (k := k) (by exact_mod_cast hk)) z = _
  have h2 : ∀ n : ℕ+, Complex.exp (2 * (↑π : ℂ) * Complex.I * z) ^ ((n : ℕ) : ℤ) =
      Complex.exp (2 * (↑π : ℂ) * Complex.I * z * n) := fun n => by
    have hr : Complex.exp (2 * (↑π : ℂ) * Complex.I * z) ^ ((n : ℕ) : ℤ) =
        Complex.exp ((((n : ℕ) : ℤ) : ℂ) * (2 * (↑π : ℂ) * Complex.I * z)) := by
      rw [Complex.exp_int_mul]
    rw [hr, show ((((n : ℕ) : ℤ) : ℂ) * (2 * (↑π : ℂ) * Complex.I * z)) =
        (2 * (↑π : ℂ) * Complex.I * z * n) by push_cast; ring]
  rw [h, tsum_congr (fun n => by rw [h2 n])]
  ring

end Definitions
