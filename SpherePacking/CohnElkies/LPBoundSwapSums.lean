module
public import SpherePacking.CohnElkies.Prereqs

import SpherePacking.CohnElkies.LPBoundAux

/-!
# Swapping sums in the LP bound

In the Poisson summation part of the Cohn-Elkies argument, we obtain expressions involving
finite sums over `x, y ∈ P.centers ∩ D` and an infinite sum over the dual lattice.

This file proves a helper lemma commuting these sums (working in `ℂ` and then taking real parts),
using summability of the Fourier transform on the dual lattice.
-/

open scoped BigOperators FourierTransform SchwartzMap Real
open Complex MeasureTheory

namespace SpherePacking.CohnElkies

variable {d : ℕ}

/-- Commute the finite `x,y` sums with the dual-lattice `m` sum in the Poisson summation
expression. We assume `𝓕 f` is real-valued so the result lives in real parts. -/
public lemma calc_steps_swap_sums (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), (((𝓕 f) x).re : ℂ) = (𝓕 f) x)
    (P : PeriodicSpherePacking d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_isBounded : Bornology.IsBounded D) (hd : 0 < d) :
    (∑' x : ↑(P.centers ∩ D),
        ∑' y : ↑(P.centers ∩ D),
          (1 / ZLattice.covolume P.lattice volume) *
            ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
              (𝓕 f m) *
                exp (2 * π * I *
                  ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                    (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])).re
      =
      ((1 / ZLattice.covolume P.lattice volume) *
          ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
            (𝓕 f m).re *
              (∑' x : ↑(P.centers ∩ D),
                ∑' y : ↑(P.centers ∩ D),
                  exp (2 * π * I *
                    ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                      (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re := by
  have : Finite (↑(P.centers ∩ D)) := finite_centers_inter_of_isBounded P D hD_isBounded hd
  letI : Fintype (↑(P.centers ∩ D)) := Fintype.ofFinite (↑(P.centers ∩ D))
  refine congrArg Complex.re ?_
  let c : ℂ := (1 / ZLattice.covolume P.lattice volume : ℂ)
  let a : SchwartzMap.dualLattice (d := d) P.lattice → ℂ := fun m => ((𝓕 f m).re : ℂ)
  let e : ↑(P.centers ∩ D) → ↑(P.centers ∩ D) →
      SchwartzMap.dualLattice (d := d) P.lattice → ℂ := fun x y m =>
    exp (2 * π * I *
      ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
        (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])
  have hFourierReal : ∀ m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m) = a m := fun m => by
    simpa [a] using (hRealFourier (m : EuclideanSpace ℝ (Fin d))).symm
  have hSummableFourierNorm :
      Summable (fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
        ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖) := by
    simpa using
      (SpherePacking.CohnElkies.LPBoundAux.summable_norm_comp_add_zlattice
        (Λ := SchwartzMap.dualLattice (d := d) P.lattice) (f := 𝓕 f)
        (a := (0 : EuclideanSpace ℝ (Fin d))))
  have hSummable_c_mul_a_mul_e : ∀ x y : ↑(P.centers ∩ D),
      Summable fun m : SchwartzMap.dualLattice (d := d) P.lattice => c * a m * e x y m := by
    intro x y
    refine Summable.of_norm_bounded
      (g := fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
        ‖c‖ * ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖)
      (by simpa [mul_assoc] using hSummableFourierNorm.mul_left ‖c‖) fun m => by
        have hnexp : ‖e x y m‖ = (1 : ℝ) := by
          simpa [e, mul_assoc, mul_left_comm, mul_comm] using
            (Complex.norm_exp_I_mul_ofReal (x := 2 * π *
              ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))
        simp_all
  have hmain :
      (∑' x : ↑(P.centers ∩ D),
          ∑' y : ↑(P.centers ∩ D),
            c * ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, a m * e x y m)
        =
        c * ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
            a m * (∑' x : ↑(P.centers ∩ D), ∑' y : ↑(P.centers ∩ D), e x y m) := by
    simp only [tsum_fintype]
    simp_rw [← tsum_mul_left]
    simp_rw [show ∀ x : ↑(P.centers ∩ D),
        (∑ y : ↑(P.centers ∩ D),
            ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, c * (a m * e x y m))
          = ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
            ∑ y : ↑(P.centers ∩ D), c * (a m * e x y m) from fun x =>
      (Summable.tsum_finsetSum (fun y _ => by
        simpa [mul_assoc] using hSummable_c_mul_a_mul_e x y)).symm]
    rw [show (∑ x : ↑(P.centers ∩ D),
            ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
              ∑ y : ↑(P.centers ∩ D), c * (a m * e x y m))
          = ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
            ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), c * (a m * e x y m) from
      (Summable.tsum_finsetSum (fun x _ => by
        simpa using
          (summable_sum fun y _ => by simpa [mul_assoc] using hSummable_c_mul_a_mul_e x y :
            Summable fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
              ∑ y ∈ (Finset.univ : Finset ↑(P.centers ∩ D)),
                c * (a m * e x y m)))).symm]
    refine tsum_congr fun m => ?_
    calc
      (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), c * (a m * e x y m))
          = ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), (c * a m) * e x y m := by
              simp [mul_assoc]
      _ = (c * a m) * (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), e x y m) := by
              simp_rw [← Finset.mul_sum]
      _ = c * (a m * (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), e x y m)) := by ring
  simpa (config := { zeta := false }) [c, e, hFourierReal] using hmain

end SpherePacking.CohnElkies
