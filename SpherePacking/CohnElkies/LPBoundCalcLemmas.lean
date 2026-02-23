module
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import SpherePacking.CohnElkies.Prereqs


/-!
# LP Bound Calc Lemmas

This file collects small calculation lemmas used in the proof of the Cohn-Elkies LP bound.

We package the exponential sum over `P.centers ∩ D`, evaluate it at the zero frequency,
and record a basic nonnegativity statement for a dual-lattice `tsum` under the Fourier-side
condition `Re (𝓕 f) ≥ 0`.
-/

open scoped Real
open scoped SchwartzMap FourierTransform

namespace SpherePacking.CohnElkies

/--
The finite exponential sum over `P.centers ∩ D` at a dual lattice point `m`.

This quantity appears when applying Poisson summation to periodic packings.
-/
@[expose] public noncomputable def expSum {d : ℕ} (P : PeriodicSpherePacking d)
    (D : Set (EuclideanSpace ℝ (Fin d))) :
    ↥(SchwartzMap.dualLattice (d := d) P.lattice) → ℂ :=
  fun m =>
    ∑' x : ↑(P.centers ∩ D),
      Complex.exp (2 * π * Complex.I * ⟪(x : EuclideanSpace ℝ (Fin d)),
        (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])

/--
At frequency `0`, the exponential sum has value `P.numReps'`,
so its norm squared is `numReps'^2`.
-/
public lemma norm_tsum_exp_inner_zero_sq_eq_numReps_sq {d : ℕ} (P : PeriodicSpherePacking d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hd : 0 < d) (hD_isBounded : Bornology.IsBounded D) :
    norm (∑' x : ↑(P.centers ∩ D),
        Complex.exp (2 * π * Complex.I *
          ⟪(x : EuclideanSpace ℝ (Fin d)),
            (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2
      =
      (P.numReps' hd hD_isBounded : ℝ) ^ 2 := by
  letI := P.instFintypeNumReps' hd hD_isBounded
  simp [PeriodicSpherePacking.numReps']

/-- A small algebraic rearrangement used to normalize factors in the LP bound inequality. -/
public lemma one_div_mul_mul_eq_mul_mul_div {α : Type*} [DivisionCommMonoid α] (c a b : α) :
    (1 / c) * a * b = b * a / c := by
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/--
Nonnegativity of the dual-lattice series that appears in the LP bound:
each summand is nonnegative when `Re (𝓕 f) ≥ 0`.
-/
public lemma tsum_ite_fourier_re_mul_norm_tsum_exp_sq_nonneg {d : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (P : PeriodicSpherePacking d)
    (D : Set (EuclideanSpace ℝ (Fin d)))
    (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0) :
    0 ≤
      ∑' m : ↥(SchwartzMap.dualLattice (d := d) P.lattice),
        (if m = (0 : ↥(SchwartzMap.dualLattice (d := d) P.lattice)) then 0
        else
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              Complex.exp (2 * π * Complex.I *
                ⟪(x : EuclideanSpace ℝ (Fin d)),
                  (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) := by
  refine tsum_nonneg (fun m => ?_)
  by_cases hm : m = (0 : ↥(SchwartzMap.dualLattice (d := d) P.lattice))
  · simp [hm]
  · have hf : 0 ≤ (𝓕 ⇑f m).re := by
      simpa using hCohnElkies₂ (m : EuclideanSpace ℝ (Fin d))
    simpa [expSum, hm] using (mul_nonneg hf (sq_nonneg (norm (expSum P D m))))

end SpherePacking.CohnElkies
