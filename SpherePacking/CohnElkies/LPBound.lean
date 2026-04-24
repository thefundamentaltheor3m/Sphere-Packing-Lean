/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Relator
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Trigonometric

public import SpherePacking.CohnElkies.Prereqs
public import SpherePacking.CohnElkies.DualSubmoduleDiscrete
public import SpherePacking.CohnElkies.LPBoundAux
public import SpherePacking.CohnElkies.LPBoundCalcLemmas
import SpherePacking.CohnElkies.LPBoundSwapSums
public import SpherePacking.CohnElkies.LPBoundReindex
public import SpherePacking.CohnElkies.LPBoundSummability
import SpherePacking.CohnElkies.LatticeSumBounds
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Cohn-Elkies linear programming bound

This file proves the Cohn-Elkies linear programming upper bound on `SpherePackingConstant d`.

Given a Schwartz function `f : 𝓢(R^d, ℂ)` with `f ≠ 0` satisfying the usual Cohn-Elkies sign
conditions

* `(f x).re ≤ 0` for `‖x‖ ≥ 1`, and
* `(𝓕 f x).re ≥ 0` for all `x`,

we obtain an explicit upper bound on the packing constant in terms of `(f 0).re`, `(𝓕 f 0).re`,
and the volume of the ball of radius `1/2`.

The main exported statements are `LinearProgrammingBound'` (for a single periodic packing) and
`LinearProgrammingBound` (for `SpherePackingConstant d`).
-/

open scoped FourierTransform ENNReal SchwartzMap BigOperators
open SpherePacking MeasureTheory Complex Real Bornology Module

variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)

local notation "conj" => starRingEnd ℂ
local notation "FT" => FourierTransform.fourierCLE ℝ (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)

section Nonnegativity

theorem hIntegrable : MeasureTheory.Integrable (𝓕 ⇑f) := (FT f).integrable

include hne_zero in
theorem fourier_ne_zero : 𝓕 f ≠ 0 := fun h => hne_zero <| by
  rw [← ContinuousLinearEquiv.map_eq_zero_iff (FourierTransform.fourierCLE ℝ _)]; exact h

include hCohnElkies₂ in
theorem f_nonneg_at_zero : 0 ≤ (f 0).re := by
  rw [← f.fourierInversion, fourierInv_eq]
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul]
  rw [← RCLike.re_eq_complex_re, ← integral_re hIntegrable]
  exact integral_nonneg fun v => by simpa using hCohnElkies₂ v

include hReal hRealFourier hCohnElkies₂ hne_zero in
theorem f_zero_pos : 0 < (f 0).re := by
  refine lt_of_le_of_ne (f_nonneg_at_zero (f := f) hCohnElkies₂) fun hf0re => ?_
  have hf0 : f 0 = 0 := by simpa [hf0re.symm] using (hReal 0).symm
  have hintRe : ∫ v : EuclideanSpace ℝ (Fin d), (𝓕 (⇑f) v).re = 0 := by
    rw [show (∫ v : EuclideanSpace ℝ (Fin d), (𝓕 (⇑f) v).re) =
        (∫ v : EuclideanSpace ℝ (Fin d), 𝓕 (⇑f) v).re from by
      simpa using integral_re (f := fun v : EuclideanSpace ℝ (Fin d) => 𝓕 (⇑f) v) hIntegrable]
    simpa using congrArg Complex.re <| show (∫ v : EuclideanSpace ℝ (Fin d), 𝓕 (⇑f) v) = 0 by
      simpa [fourierInv_eq, hf0] using (congrArg (fun g : EuclideanSpace ℝ (Fin d) → ℂ => g 0)
        f.fourierInversion : 𝓕⁻ (𝓕 ⇑f) 0 = f 0)
  have hfun : (fun x : EuclideanSpace ℝ (Fin d) => (𝓕 f x).re) = 0 := by
    refine (Continuous.integral_zero_iff_zero_of_nonneg (by fun_prop) ?_ hCohnElkies₂).1
      (by simpa using hintRe)
    exact hIntegrable.re
  refine fourier_ne_zero hne_zero ?_
  ext x; simpa [show (𝓕 f x).re = 0 from by simpa using congrArg (fun g => g x) hfun] using
    (hRealFourier x).symm

end Nonnegativity

section Fundamental_Domain_Dependent

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)

omit [Nonempty ↑P.centers] in
include hD_isBounded in
/-- Helper summability fact used in `calc_steps_part2`: the series
`∑ m, (𝓕 f m).re * ‖∑ x, exp (2 π I ⟪x, m⟫)‖²` indexed over the dual lattice
is summable, because `‖∑ x, ...‖ ≤ |P.centers ∩ D|` is uniform in `m`. -/
private lemma summable_fourier_mul_norm_exp_sq (hd : 0 < d) :
    Summable (fun m : ↥(SchwartzMap.dualLattice (d := d) P.lattice) =>
      (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) := by
  haveI : Finite (↑(P.centers ∩ D)) := finite_centers_inter_of_isBounded P D hD_isBounded hd
  letI : Fintype (↑(P.centers ∩ D)) := Fintype.ofFinite _
  let n : ℝ := (Fintype.card (↑(P.centers ∩ D)) : ℝ)
  have hFourierNorm : Summable (fun m : ↥(SchwartzMap.dualLattice (d := d) P.lattice) =>
      ‖(𝓕 ⇑f) (m : EuclideanSpace ℝ (Fin d))‖) := by
    simpa [SchwartzMap.fourier_coe] using
      SpherePacking.CohnElkies.LPBoundAux.summable_norm_comp_add_zlattice
        (Λ := SchwartzMap.dualLattice (d := d) P.lattice) (f := 𝓕 f)
        (a := (0 : EuclideanSpace ℝ (Fin d)))
  let g' : ↥(SchwartzMap.dualLattice (d := d) P.lattice) → ℝ := fun m =>
    ‖(𝓕 ⇑f) (m : EuclideanSpace ℝ (Fin d))‖ * (n ^ 2)
  refine Summable.of_norm_bounded (g := g') ?_ fun m => ?_
  · simpa [g'] using hFourierNorm.mul_right (n ^ 2)
  set A : ℂ := ∑' x : ↑(P.centers ∩ D),
    exp (2 * π * I * ⟪(x : EuclideanSpace ℝ (Fin d)),
      (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) with hAdef
  have hnexp : ∀ x : ↑(P.centers ∩ D),
      ‖exp (2 * π * I * ⟪(x : EuclideanSpace ℝ (Fin d)),
        (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])‖ = (1 : ℝ) := fun x => by
    simpa [show (2 * π * I * (⟪(x : EuclideanSpace ℝ (Fin d)),
        (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] : ℂ)) = ((2 * π * ⟪(x : EuclideanSpace ℝ (Fin d)),
        (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] : ℝ) : ℂ) * I from by simp [mul_assoc, mul_comm]]
      using Complex.norm_exp_ofReal_mul_I
        (2 * π * ⟪(x : EuclideanSpace ℝ (Fin d)), (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])
  have hA_le : ‖A‖ ≤ n := by
    simpa [hAdef, tsum_fintype, hnexp, n] using
      norm_sum_le (Finset.univ : Finset ↑(P.centers ∩ D)) fun x : ↑(P.centers ∩ D) =>
        exp (2 * π * I * ⟪(x : EuclideanSpace ℝ (Fin d)), (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])
  calc ‖(𝓕 ⇑f m).re * (‖A‖ ^ 2)‖
        = ‖((𝓕 ⇑f) (m : EuclideanSpace ℝ (Fin d))).re‖ * ‖A‖ ^ 2 := by
          simp [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    _ ≤ ‖((𝓕 ⇑f) (m : EuclideanSpace ℝ (Fin d))).re‖ * (n ^ 2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg A) hA_le 2) (norm_nonneg _)
    _ ≤ ‖(𝓕 ⇑f) (m : EuclideanSpace ℝ (Fin d))‖ * (n ^ 2) :=
        mul_le_mul_of_nonneg_right
          (by simpa [Real.norm_eq_abs] using abs_re_le_norm _) (by positivity)
    _ ≤ g' m := by simp [g']

include hP hCohnElkies₁ in
open Classical in
theorem calc_aux_1 (hd : 0 < d)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) :
    ∑' x : P.centers, ∑' y : ↑(P.centers ∩ D), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re
      ≤ ↑(P.numReps' hd hD_isBounded) * (f 0).re := by
  rw [SpherePacking.CohnElkies.tsum_centers_eq_tsum_centersInter_centersInter_lattice
    (f := f) (P := P) (D := D) hD_isBounded hD_unique_covers hd]
  letI : Fintype ↑(P.centers ∩ D) := P.instFintypeNumReps' hd hD_isBounded
  simp_rw [tsum_fintype]
  refine (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ =>
    CohnElkies.lattice_sum_re_le_ite hP hD_unique_covers hCohnElkies₁ x i).trans ?_
  simp [PeriodicSpherePacking.numReps']

omit [Nonempty ↑P.centers] in
include hD_isBounded in
lemma calc_steps' (hd : 0 < d) :
    ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : ↥P.lattice), (f (↑x - ↑y + ↑ℓ)).re =
    (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : ↥P.lattice), f (↑x - ↑y + ↑ℓ)).re := by
  haveI : Finite ↑(P.centers ∩ D) := finite_centers_inter_of_isBounded P D hD_isBounded hd
  rw [re_tsum Summable.of_finite]
  exact tsum_congr fun x => by
    rw [re_tsum Summable.of_finite]
    exact tsum_congr fun y => by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (re_tsum (SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_translate
        (Λ := P.lattice) (f := f) (a := (↑x - ↑y : EuclideanSpace ℝ (Fin d))))).symm

include d f hP hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hD_unique_covers in
omit hne_zero hReal hCohnElkies₂ in
theorem calc_steps_part1 (hd : 0 < d) :
    ↑(P.numReps' hd hD_isBounded) * (f 0).re ≥
      (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              exp (2 * π * I *
                ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2) := by
  calc ↑(P.numReps' hd hD_isBounded) * (f 0).re
  _ ≥ ∑' (x : P.centers) (y : ↑(P.centers ∩ D)), (f (x - ↑y)).re :=
        calc_aux_1 hCohnElkies₁ hP hD_isBounded hd hD_unique_covers
  _ = ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice), (f (↑x - ↑y + ↑ℓ)).re :=
        CohnElkies.tsum_centers_eq_tsum_centersInter_centersInter_lattice f P
          hD_isBounded hD_unique_covers hd
  _ = (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
      f (↑x - ↑y + ↑ℓ)).re := calc_steps' hD_isBounded hd
  _ = (∑' x : ↑(P.centers ∩ D),
      ∑' y : ↑(P.centers ∩ D), (1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m) *
      exp (2 * π * I * ⟪↑x - ↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])).re := by
        congr! 5 with x y; exact SchwartzMap.poissonSummation_lattice P.lattice f _
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
      (𝓕 f m).re * (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
      exp (2 * π * I * ⟪↑x - ↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re := by
        simpa using SpherePacking.CohnElkies.calc_steps_swap_sums (f := f)
          (hRealFourier := hRealFourier) (P := P) (D := D) hD_isBounded hd
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m).re * (
      ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) *
      exp (2 * π * I * ⟪-↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re := by
        congr! 9 with m x y
        simp only [sub_eq_neg_add, RCLike.wInner_neg_left, ofReal_neg, mul_neg, mul_comm]
        rw [RCLike.wInner_add_left]
        simp only [RCLike.wInner_neg_left, ofReal_add, ofReal_neg]
        rw [mul_add, Complex.exp_add, mul_comm]; simp
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
      (𝓕 f m).re * (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
      (∑' y : ↑(P.centers ∩ D),
      exp (-(2 * π * I * ⟪↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])))).re := by
        simp_rw [mul_assoc, ← tsum_mul_right, ← tsum_mul_left]
        congr! 9 with m x y
        simp only [RCLike.wInner_neg_left, ofReal_neg, mul_neg]
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m).re *
      (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
      conj (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re := by
        simp_rw [conj_tsum]
        congr! 7 with m x
        exact Complex.exp_neg_real_I_eq_conj (x : EuclideanSpace ℝ (Fin d)) m
  _ = (1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
        (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2) := by
        rw [← ofReal_re (1 / ZLattice.covolume P.lattice volume *
          ∑' (m : ↥(LinearMap.BilinForm.dualSubmodule (innerₗ _) P.lattice)),
            (𝓕 ⇑f ↑m).re * norm (∑' (x : ↑(P.centers ∩ D)),
            cexp (2 * ↑π * I * ↑⟪(x : EuclideanSpace ℝ (Fin d)), ↑m⟫_[ℝ])) ^ 2)]
        congr 1; push_cast; congr! 3 with m
        rw [mul_assoc, mul_conj, Complex.normSq_eq_norm_sq]; norm_cast

include d f hP hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ in
omit hne_zero hReal hRealFourier hCohnElkies₁ hP [Nonempty ↑P.centers] in
theorem calc_steps_part2 (hd : 0 < d) :
    (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              exp (2 * π * I *
                ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)
      ≥
      ↑(P.numReps' hd hD_isBounded) ^ 2 * (𝓕 f 0).re / ZLattice.covolume P.lattice volume := by
  calc (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              exp (2 * π * I *
                ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)
    _ = (1 / ZLattice.covolume P.lattice volume) * (
        (∑' (m : SchwartzMap.dualLattice (d := d) P.lattice),
          if m = (0 : ↥(SchwartzMap.dualLattice (d := d) P.lattice)) then 0
          else (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) +
        (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re *
        (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) := by
        refine congrArg (fun t => (1 / ZLattice.covolume P.lattice volume) * t) ?_
        refine (Summable.tsum_eq_add_tsum_ite
          (summable_fourier_mul_norm_exp_sq (f := f) (P := P) (D := D)
            (hD_isBounded := hD_isBounded) hd) 0).trans ?_
        ac_rfl
    _ ≥ (1 / ZLattice.covolume P.lattice volume) * (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re *
        (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2) := by
        rw [ge_iff_le, ← tsub_nonpos, mul_assoc,
          ← mul_sub (1 / ZLattice.covolume P.lattice volume) _ _]
        simp only [sub_add_cancel_right, mul_neg, Left.neg_nonpos_iff]
        exact mul_nonneg
          (one_div_nonneg.mpr (by rw [ZLattice.covolume]; exact ENNReal.toReal_nonneg))
          (SpherePacking.CohnElkies.tsum_ite_fourier_re_mul_norm_tsum_exp_sq_nonneg
            (f := f) (P := P) (D := D) (hCohnElkies₂ := hCohnElkies₂))
    _ = (1 / ZLattice.covolume P.lattice volume) * (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re *
        ↑(P.numReps' hd hD_isBounded) ^ 2 := by
        simp only [SpherePacking.CohnElkies.norm_tsum_exp_inner_zero_sq_eq_numReps_sq
          (P := P) (D := D) (hd := hd) (hD_isBounded := hD_isBounded)]
    _ = ↑(P.numReps' hd hD_isBounded) ^ 2 * (𝓕 f 0).re / ZLattice.covolume P.lattice volume :=
      SpherePacking.CohnElkies.one_div_mul_mul_eq_mul_mul_div
        (α := ℝ) (c := ZLattice.covolume P.lattice volume)
        (a := (𝓕 ⇑f 0).re) (b := (↑(P.numReps' hd hD_isBounded) : ℝ) ^ 2)

include d f hP hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hD_unique_covers in
omit hne_zero hReal in
theorem calc_steps (hd : 0 < d) :
    ↑(P.numReps' hd hD_isBounded) * (f 0).re ≥ ↑(P.numReps' hd hD_isBounded) ^ 2 *
      (𝓕 f 0).re / ZLattice.covolume P.lattice volume :=
  ge_trans (calc_steps_part1 (P := P) (D := D) hRealFourier hCohnElkies₁ hP hD_isBounded
    hD_unique_covers hd) (calc_steps_part2 (P := P) (D := D) (hCohnElkies₂ := hCohnElkies₂)
      hD_isBounded hd)

end Fundamental_Domain_Dependent

section Main_Theorem_For_One_Packing

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)

include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ P hP D hD_isBounded
  hD_unique_covers

/-- Linear programming bound for a single periodic packing of separation `1`; the key estimate
used to bound `SpherePackingConstant d` after reducing to periodic packings. -/
public theorem LinearProgrammingBound' (hd : 0 < d) :
    P.density ≤ (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  haveI : Fact (0 < d) := ⟨hd⟩
  rw [P.density_eq' hd]
  suffices hCalc : (P.numReps' hd hD_isBounded) * (f 0).re ≥
    (P.numReps' hd hD_isBounded)^2 * (𝓕 f 0).re / ZLattice.covolume P.lattice volume by
    rw [hP]
    rw [ge_iff_le] at hCalc
    have vol_ne_zero : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≠ 0 :=
      (Metric.measure_ball_pos (μ := volume) (0 : EuclideanSpace ℝ (Fin d)) one_half_pos).ne'
    have vol_ne_top : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≠ ∞ :=
      (MeasureTheory.measure_ball_lt_top (μ := volume)).ne
    rcases eq_or_ne (𝓕 f 0) 0 with h𝓕f | h𝓕f
    · rw [h𝓕f, zero_re, ENat.toENNReal_coe, toNNReal_zero, ENNReal.coe_zero,
        ENNReal.div_zero (ENNReal.coe_ne_zero.mpr (toNNReal_pos.mpr
          (f_zero_pos hne_zero hReal hRealFourier hCohnElkies₂)).ne'),
        ENNReal.top_mul vol_ne_zero]
      exact le_top
    rw [ENat.toENNReal_coe, mul_div_assoc, div_eq_mul_inv (volume _), mul_comm (volume _),
        ← mul_assoc, ENNReal.mul_le_mul_iff_left vol_ne_zero vol_ne_top]
    rw [← PeriodicSpherePacking.numReps_eq_numReps' (S := P) Fact.out hD_isBounded
      hD_unique_covers] at hCalc
    have hfouaux₁ : ((𝓕 f 0).re.toNNReal : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr <| by
      rw [ne_eq, Real.toNNReal_eq_zero, not_le]
      exact lt_of_le_of_ne (hCohnElkies₂ 0) fun heq => h𝓕f <|
        Complex.ext heq.symm (by simpa [eq_comm] using congrArg Complex.im (hRealFourier 0))
    rw [← ENNReal.mul_le_mul_iff_left hfouaux₁ ENNReal.coe_ne_top,
      div_eq_mul_inv ((f 0).re.toNNReal : ENNReal) _, mul_assoc ((f 0).re.toNNReal : ENNReal) _ _,
      ENNReal.inv_mul_cancel hfouaux₁ ENNReal.coe_ne_top, mul_one, mul_assoc,
      ← ENNReal.div_eq_inv_mul]
    have hnRaux₁ : ENat.toENNReal (P.numReps : ENat) ≠ 0 := by
      rw [ENat.toENNReal_coe, ne_eq, Nat.cast_eq_zero]
      haveI : Nonempty (Quotient (AddAction.orbitRel ↥P.lattice ↑P.centers)) :=
        nonempty_quotient_iff _ |>.2 ‹_›
      exact Fintype.card_ne_zero
    rw [← ENNReal.mul_le_mul_iff_right hnRaux₁ (Ne.symm (ne_of_beq_false rfl) :
        ENat.toENNReal (P.numReps : ENat) ≠ ⊤), ENat.toENNReal_coe, ← mul_assoc, ← pow_two,
      ← mul_div_assoc]
    have hcov_pos : 0 < ZLattice.covolume P.lattice volume := ZLattice.covolume_pos P.lattice volume
    have hRHSCast :
        (P.numReps : ENNReal) * ↑(f 0).re.toNNReal = (P.numReps * (f 0).re).toNNReal := by
      rw [show ((P.numReps : ℝ) * (f 0).re).toNNReal = (P.numReps : NNReal) * (f 0).re.toNNReal
        from by rw [Real.toNNReal_mul (Nat.cast_nonneg _)]; simp]
      push_cast; rfl
    have hLHSCast : (P.numReps : ENNReal) ^ 2 * ((𝓕 f 0).re.toNNReal : ENNReal) /
        ((ZLattice.covolume P.lattice volume).toNNReal : ENNReal) = ((P.numReps) ^ 2 *
        (𝓕 f 0).re / ZLattice.covolume P.lattice volume).toNNReal := by
      simp only [div_eq_mul_inv, ← ENNReal.coe_inv (Real.toNNReal_pos.mpr hcov_pos).ne',
        Real.toNNReal_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (hCohnElkies₂ 0))
          (inv_nonneg.mpr hcov_pos.le))]
      norm_cast
      rw [Real.toNNReal_of_nonneg (hCohnElkies₂ 0), Real.toNNReal_of_nonneg hcov_pos.le]; rfl
    rw [hRHSCast, hLHSCast, ENNReal.coe_le_coe]
    exact Real.toNNReal_le_toNNReal hCalc
  exact calc_steps hRealFourier hCohnElkies₁ hCohnElkies₂ hP hD_isBounded hD_unique_covers hd

end Main_Theorem_For_One_Packing

section Main_Theorem

include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂

/-- The Cohn-Elkies linear programming upper bound on `SpherePackingConstant d`. -/
public theorem LinearProgrammingBound (hd : 0 < d) : SpherePackingConstant d ≤
    (f 0).re.toNNReal / (𝓕 ⇑f 0).re.toNNReal *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  rw [← periodic_constant_eq_constant hd,
    periodic_constant_eq_periodic_constant_normalized (d := d)]
  refine iSup_le fun P => iSup_le fun hP => ?_
  cases isEmpty_or_nonempty ↑P.centers with
  | inl instEmpty => simp [P.density_of_centers_empty hd]
  | inr instNonempty =>
    let b : Basis (Fin d) ℤ ↥P.lattice :=
      ((ZLattice.module_free ℝ P.lattice).chooseBasis).reindex
        (PeriodicSpherePacking.basis_index_equiv P)
    exact LinearProgrammingBound' hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP
      (ZSpan.fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ P.lattice b))
      (PeriodicSpherePacking.fundamental_domain_unique_covers (S := P) b) hd

end Main_Theorem
