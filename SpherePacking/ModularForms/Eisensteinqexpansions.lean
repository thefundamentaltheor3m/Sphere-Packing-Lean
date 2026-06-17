module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

public import SpherePacking.ModularForms.Delta

@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open scoped ArithmeticFunction.sigma

noncomputable section Definitions

def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0

def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma ↑1) k :=
  (1/2 : ℂ) • eisensteinSeriesMF hk standardcongruencecondition /-they need 1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/

/-Forwards to `EisensteinSeries.q_expansion_riemannZeta` from mathlib. -/
lemma E_k_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (E k hk) z = 1 +
        (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, σ (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by
  rw [_root_.E]
  change (1 / 2 : ℂ) • (ModularForm.eisensteinSeriesMF hk standardcongruencecondition z) = _
  calc
    (1 / 2 : ℂ) • (ModularForm.eisensteinSeriesMF hk standardcongruencecondition z) =
        1 + (riemannZeta k)⁻¹ * (-2 * ↑π * Complex.I) ^ k / (k - 1)! *
          ∑' n : ℕ+, σ (k - 1) n * cexp (2 * ↑π * Complex.I * z) ^ (n : ℤ) := by
      simpa [ModularForm.E, standardcongruencecondition, smul_eq_mul] using
        EisensteinSeries.q_expansion_riemannZeta (k := k) (by omega) hk2 z
    _ = 1 + (1 / riemannZeta k) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
          ∑' n : ℕ+, σ (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by
      rw [show ∑' n : ℕ+, σ (k - 1) n * cexp (2 * ↑π * Complex.I * z) ^ (n : ℤ) =
          ∑' n : ℕ+, σ (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) from by
            apply tsum_congr
            intro n
            rw [zpow_natCast, ← Complex.exp_nat_mul]
            ring_nf]
      simp [div_eq_mul_inv, mul_assoc]
