module
public import SpherePacking.CohnElkies.Prereqs

import SpherePacking.CohnElkies.DualSubmoduleDiscrete
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

/--
Commute the finite `x,y` sums with the dual-lattice `m` sum in the Poisson summation expression.

We assume `𝓕 f` is real-valued so that we can rewrite the result in terms of real parts.
-/
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
  have hfinite : Finite (↑(P.centers ∩ D)) :=
    finite_centers_inter_of_isBounded P D hD_isBounded hd
  letI : Fintype (↑(P.centers ∩ D)) := Fintype.ofFinite (↑(P.centers ∩ D))
  -- Work in `ℂ`, then take real parts.
  refine congrArg Complex.re ?_
  let c : ℂ := (1 / ZLattice.covolume P.lattice volume : ℂ)
  let a : SchwartzMap.dualLattice (d := d) P.lattice → ℂ := fun m => ((𝓕 f m).re : ℂ)
  let e :
      ↑(P.centers ∩ D) →
        ↑(P.centers ∩ D) →
          SchwartzMap.dualLattice (d := d) P.lattice → ℂ :=
    fun x y m =>
      exp (2 * π * I *
        ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
          (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])
  have hFourierReal :
      ∀ m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m) = a m := by
    intro m
    simpa [a] using (hRealFourier (m : EuclideanSpace ℝ (Fin d))).symm
  -- Summability of `‖𝓕 f‖` on the dual lattice.
  have hSummableFourierNorm :
      Summable (fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
        ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖) := by
    simpa using
      (SpherePacking.CohnElkies.LPBoundAux.summable_norm_comp_add_zlattice
        (Λ := SchwartzMap.dualLattice (d := d) P.lattice) (f := 𝓕 f)
        (a := (0 : EuclideanSpace ℝ (Fin d))))
  -- Each `m ↦ c * a m * e x y m` is summable.
  have hSummable_c_mul_a_mul_e :
      ∀ x y : ↑(P.centers ∩ D),
        Summable fun m : SchwartzMap.dualLattice (d := d) P.lattice => c * a m * e x y m := by
    intro x y
    refine Summable.of_norm_bounded
      (g := fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
        ‖c‖ * ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖) ?_ ?_
    · simpa [mul_assoc] using hSummableFourierNorm.mul_left ‖c‖
    · intro m
      have hnexp : ‖e x y m‖ = (1 : ℝ) := by
        simpa [e, mul_assoc, mul_left_comm, mul_comm] using
          (Complex.norm_exp_I_mul_ofReal (x := 2 * π *
            ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))
      have hbound : ‖c * a m * e x y m‖ ≤ ‖c‖ * ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖ := by
        have ha : ‖a m‖ = ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖ := by
          simpa using congrArg norm (hFourierReal m).symm
        have hEq : ‖c * a m * e x y m‖ = ‖c‖ * ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖ := by
          have h1 : ‖c * a m * e x y m‖ = ‖c * a m‖ * ‖e x y m‖ :=
            norm_mul (c * a m) (e x y m)
          have h2 : ‖c * a m‖ * ‖e x y m‖ = (‖c‖ * ‖a m‖) * ‖e x y m‖ :=
            congrArg (fun t : ℝ => t * ‖e x y m‖) (norm_mul c (a m))
          have h3 : (‖c‖ * ‖a m‖) * ‖e x y m‖ = ‖c‖ * ‖a m‖ * ‖e x y m‖ := rfl
          have h4 : ‖c‖ * ‖a m‖ * ‖e x y m‖ = ‖c‖ * ‖a m‖ := by
            rw [hnexp]
            exact mul_one (‖c‖ * ‖a m‖)
          have h5 : ‖c‖ * ‖a m‖ = ‖c‖ * ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖ :=
            congrArg (fun t : ℝ => ‖c‖ * t) ha
          exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
        exact hEq.le
      exact hbound
  -- Reduce the goal to the `c,a,e`-form, then commute the finite sums with the `m`-sum.
  have hmain :
      (∑' x : ↑(P.centers ∩ D),
          ∑' y : ↑(P.centers ∩ D),
            c * ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, a m * e x y m)
        =
        c *
          ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
            a m *
              (∑' x : ↑(P.centers ∩ D), ∑' y : ↑(P.centers ∩ D), e x y m) := by
    -- Expand the finite `tsum`s as finite sums.
    simp only [tsum_fintype]
    -- Rewrite `c * (∑' m, ...)` as `(∑' m, c * ...)` everywhere.
    simp_rw [← tsum_mul_left]
    -- Commute `y` with `m`.
    have hy_comm :
        ∀ x : ↑(P.centers ∩ D),
          (∑ y : ↑(P.centers ∩ D),
                ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, c * (a m * e x y m))
            =
            ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
              ∑ y : ↑(P.centers ∩ D), c * (a m * e x y m) := by
      intro x
      have hy' :
          ∀ y ∈ (Finset.univ : Finset ↑(P.centers ∩ D)),
            Summable fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
              c * (a m * e x y m) := by
        intro y _
        simpa [mul_assoc] using hSummable_c_mul_a_mul_e x y
      simpa using
        (Summable.tsum_finsetSum (s := (Finset.univ : Finset ↑(P.centers ∩ D)))
              (f := fun y m => c * (a m * e x y m)) hy').symm
    simp_rw [hy_comm]
    -- Commute `x` with `m`.
    have hx_comm :
        (∑ x : ↑(P.centers ∩ D),
              ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
                ∑ y : ↑(P.centers ∩ D), c * (a m * e x y m))
          =
          ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
            ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), c * (a m * e x y m) := by
      have hx' :
          ∀ x ∈ (Finset.univ : Finset ↑(P.centers ∩ D)),
            Summable fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
              ∑ y : ↑(P.centers ∩ D), c * (a m * e x y m) := by
        intro x _
        -- finite sum of summable functions
        have :
            Summable fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
              ∑ y ∈ (Finset.univ : Finset ↑(P.centers ∩ D)), c * (a m * e x y m) := by
          refine summable_sum ?_
          intro y _
          simpa [mul_assoc] using hSummable_c_mul_a_mul_e x y
        simpa using this
      simpa using
        (Summable.tsum_finsetSum (s := (Finset.univ : Finset ↑(P.centers ∩ D)))
              (f := fun x m => ∑ y : ↑(P.centers ∩ D), c * (a m * e x y m)) hx').symm
    simp_rw [hx_comm]
    -- Pull constants out of the finite sums pointwise in `m`.
    refine tsum_congr ?_
    intro m
    have hy_factor :
        ∀ x : ↑(P.centers ∩ D),
          (∑ y : ↑(P.centers ∩ D), (c * a m) * e x y m) =
            (c * a m) * (∑ y : ↑(P.centers ∩ D), e x y m) := by
      intro x
      simpa using
        (Finset.mul_sum (s := (Finset.univ : Finset ↑(P.centers ∩ D)))
              (a := c * a m) (f := fun y => e x y m)).symm
    have hx_factor :
        (∑ x : ↑(P.centers ∩ D),
              (c * a m) * (∑ y : ↑(P.centers ∩ D), e x y m)) =
            (c * a m) *
              (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), e x y m) := by
      simpa using
        (Finset.mul_sum (s := (Finset.univ : Finset ↑(P.centers ∩ D)))
              (a := c * a m)
              (f := fun x => ∑ y : ↑(P.centers ∩ D), e x y m)).symm
    calc
      (∑ x : ↑(P.centers ∩ D),
            ∑ y : ↑(P.centers ∩ D), c * (a m * e x y m))
          = ∑ x : ↑(P.centers ∩ D),
              ∑ y : ↑(P.centers ∩ D), (c * a m) * e x y m := by
              simp [mul_assoc]
      _ = ∑ x : ↑(P.centers ∩ D),
              (c * a m) * (∑ y : ↑(P.centers ∩ D), e x y m) := by
              simp_rw [hy_factor]
      _ = (c * a m) * (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), e x y m) := by
              simp [hx_factor]
      _ = c * (a m * (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), e x y m)) := by
              simp [mul_assoc]
  -- Rewrite the goal to the `c,a,e`-form, then close with `hmain`.
  simpa (config := { zeta := false }) [c, e, hFourierReal] using hmain

end SpherePacking.CohnElkies
