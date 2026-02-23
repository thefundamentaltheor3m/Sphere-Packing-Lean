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
public import SpherePacking.ForMathlib.VolumeOfBalls


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
-- `f` is real-valued (as a complex-valued function).
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
-- `𝓕 f` is real-valued (as a complex-valued function).
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
-- The Cohn-Elkies conditions:
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)

-- We (locally) denote the Complex Conjugate of some `z : ℂ` by `conj z`
local notation "conj" => starRingEnd ℂ

local notation "FT" => FourierTransform.fourierCLE ℝ (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)

section Complex_Function_Helpers

theorem helper (g : EuclideanSpace ℝ (Fin d) → ℂ) :
  (∀ x : EuclideanSpace ℝ (Fin d), ↑(g x).re = (g x)) →
  (∀ x : EuclideanSpace ℝ (Fin d), (g x).im = 0) := by
  intro hIsReal x
  simpa [eq_comm] using congrArg Complex.im (hIsReal x)

include hRealFourier in
@[simp]
theorem hFourierImZero : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).im = 0 :=
  helper (𝓕 ⇑f) hRealFourier

end Complex_Function_Helpers

section Nonnegativity

private theorem hIntegrable : MeasureTheory.Integrable (𝓕 ⇑f) :=
    (𝓕 f).integrable

include hne_zero in
theorem fourier_ne_zero : 𝓕 f ≠ 0 := by
  intro hFourierZero
  apply hne_zero
  simpa using congrArg (fun g => 𝓕⁻ g) hFourierZero

include hCohnElkies₂ in
theorem f_nonneg_at_zero : 0 ≤ (f 0).re := by
  -- Building off the previous one, f(0) is an integral of a nonneg function, and hence, also nonneg
  have hfourier : (f 0).re = (𝓕⁻ (𝓕 f) 0).re := by
    exact congrArg (fun g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) => (g 0).re)
      (FourierTransform.fourierInv_fourier_eq f).symm
  rw [hfourier, SchwartzMap.fourierInv_coe, fourierInv_eq]
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul]
  exact (integral_nonneg (f := fun v : EuclideanSpace ℝ (Fin d) => ((𝓕 f) v).re) hCohnElkies₂).trans
    (integral_re (μ := volume) (f := fun v : EuclideanSpace ℝ (Fin d) => (𝓕 f) v) hIntegrable).le

include hReal hRealFourier hCohnElkies₂ hne_zero in
theorem f_zero_pos : 0 < (f 0).re := by
  -- We know from previous that f(0) is nonneg. If zero, then the integral of 𝓕 f is zero, making
  -- 𝓕 f zero (it's continuous and nonneg: if it's pos anywhere, it's pos on a nbhd, and hence the
  -- integral must be pos too, but it's zero, contra). By Schwartz, f is identically zero iff 𝓕 f
  -- is (𝓕 is a linear iso). But 𝓕 f is zero while f is not, contra! So f(0) is positive.
  -- apply ne_of_gt
  have haux₁ : f 0 = 𝓕⁻ (𝓕 f) 0 := by
    exact congrArg (fun g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) => g 0)
      (FourierTransform.fourierInv_fourier_eq f).symm
  rw [SchwartzMap.fourierInv_coe, fourierInv_eq] at haux₁
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul] at haux₁
  -- We need to take real parts at haux₁
  rw [← re_add_im (f 0), hImZero hReal, ofReal_zero, zero_mul, add_zero] at haux₁
  -- We need to take real and imaginary parts inside the integral.
  have haux₂ : ∫ (v : EuclideanSpace ℝ (Fin d)), (𝓕 f) v =
    ((∫ (v : EuclideanSpace ℝ (Fin d)), ((𝓕 f) v).re : ℝ) : ℂ) := by
    calc ∫ (v : EuclideanSpace ℝ (Fin d)), (𝓕 f) v
    _ = ((∫ (v : EuclideanSpace ℝ (Fin d)), ((𝓕 f) v).re : ℝ) : ℂ) +
        (∫ (v : EuclideanSpace ℝ (Fin d)), ((𝓕 f) v).im : ℝ) * I := by
          symm
          exact integral_re_add_im (μ := volume)
            (f := fun v : EuclideanSpace ℝ (Fin d) => (𝓕 f) v) hIntegrable
    _ = ((∫ (v : EuclideanSpace ℝ (Fin d)), ((𝓕 f) v).re : ℝ) : ℂ) := by
          rw [add_eq_left]
          suffices hwhat : ∀ v : EuclideanSpace ℝ (Fin d), ((𝓕 f) v).im = 0 by
            simp only [hwhat, ofReal_zero, zero_mul, integral_zero]
          exact hFourierImZero hRealFourier
  rw [haux₂] at haux₁
  norm_cast at haux₁
  rw [haux₁, lt_iff_not_ge]
  by_contra hantisymm₁
  have hantisymm₂ : 0 ≤ ∫ (v : EuclideanSpace ℝ (Fin d)), ((𝓕 f) v).re := integral_nonneg
    hCohnElkies₂
  have hintzero : 0 = ∫ (v : EuclideanSpace ℝ (Fin d)), ((𝓕 f) v).re := by
    exact antisymm' hantisymm₁ hantisymm₂
  have h𝓕frezero : ∀ x, ((𝓕 f) x).re = 0 := by
    -- Integral of a nonneg continuous function is zero iff the function is zero
    suffices hfun : (fun x => ((𝓕 f) x).re) = 0 by
      -- (This is the function actually being integrated)
      intro x
      calc ((𝓕 f) x).re
      _ = (fun x => ((𝓕 f) x).re) x := rfl
      _ = (0 : (EuclideanSpace ℝ (Fin d)) → ℝ) x := by rw [hfun]
      _ = 0 := by rw [Pi.zero_apply]
    have hcont : Continuous (fun x ↦ (𝓕 f x).re) := by
      exact Continuous.comp' continuous_re (𝓕 f).continuous
    refine (Continuous.integral_zero_iff_zero_of_nonneg hcont ?_ hCohnElkies₂).mp hintzero.symm
    exact MeasureTheory.Integrable.re ((𝓕 f).integrable (μ := volume))
  have h𝓕fzero : 𝓕 f = 0 := by
    ext x
    rw [← re_add_im (𝓕 f x), hFourierImZero hRealFourier, ofReal_zero, zero_mul,
      add_zero, SchwartzMap.zero_apply, ofReal_eq_zero]
    exact h𝓕frezero x
  exact fourier_ne_zero hne_zero h𝓕fzero

end Nonnegativity

section Fundamental_Domain_Dependent

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)

/- In this section, we bound packing density by the Cohn-Elkies bound. -/

include hP hCohnElkies₁ in
open Classical in
private theorem calc_aux_1 (hd : 0 < d) (hf : Summable f) :
  ∑' x : P.centers, ∑' y : ↑(P.centers ∩ D), (f (x - ↑y)).re
  ≤ ↑(P.numReps' hd hD_isBounded) * (f 0).re := calc
  ∑' x : P.centers, ∑' y : ↑(P.centers ∩ D), (f (x - ↑y)).re
  _ = (∑' (x : P.centers) (y : ↑(P.centers ∩ D)),
      if h : x - (y : EuclideanSpace ℝ (Fin d)) = 0 then 0 else (f (x - ↑y)).re) +
      (∑' (x : ↑(P.centers ∩ D)), (f (0 : EuclideanSpace ℝ (Fin d))).re)
        := by
            have sum_finite := aux4 P D hD_isBounded hd
            have fintype_centers: Fintype ↑(P.centers ∩ D) := by apply Fintype.ofFinite
            conv =>
              rhs
              rhs
              equals ∑' (x : ↑(P.centers)), if x.val ∈ D then (f 0).re else 0 =>
                rw [tsum_subtype (f := fun x => (f 0).re)]
                rw [tsum_subtype (f := fun x => if ↑x ∈ D then (f 0).re else 0)]
                apply tsum_congr
                intro p
                simp [Set.indicator, ite_and]
            -- First, we need to un-distribute the tsums on the RHS.
            -- Then, we need to use some sort of `tsum_ite_eq`.
            -- Both of the above require some summability stuff.
            rw [← Summable.tsum_add]
            · apply tsum_congr
              intro x
              split_ifs with hx
              · let x_in: ↑(P.centers ∩ D) := ⟨x, by simp [hx]⟩
                simp only [dite_eq_ite]
                rw [← tsum_ite_eq (b := x_in) (a := fun _ ↦ (f 0).re)]
                simp_rw [← Subtype.val_inj]
                rw [← Summable.tsum_add]
                · apply tsum_congr
                  intro y
                  dsimp [x_in]
                  simp_rw [eq_comm (a := y.val), ← sub_eq_zero (a := x.val)]
                  split_ifs with x_eq_y <;> simp [x_eq_y]
                · apply Summable.of_finite
                · simp_rw [Subtype.val_inj]
                  apply (hasSum_ite_eq _ _).summable
              · simp only [dite_eq_ite, add_zero]
                apply tsum_congr
                intro b
                have x_neq_b: x.val ≠ b.val := by
                  by_contra!
                  rw [this] at hx
                  have b_in_d := b.property.right
                  contradiction
                dsimp [Ne] at x_neq_b
                rw [← sub_eq_zero] at x_neq_b
                simp [x_neq_b]
            · rw [← summable_abs_iff]
              apply Summable.of_nonneg_of_le (by simp) (?_) (f := fun x => ∑' (y : ↑(P.centers ∩
                D)), ‖if h : x.val - y.val = 0 then 0 else (f (x.val - y.val)).re‖) ?_
              · intro b
                rw [← Real.norm_eq_abs]
                apply norm_tsum_le_tsum_norm
                apply Summable.of_norm_bounded (g := fun x => |(f (b.val - x.val)).re|)
                · apply Summable.of_finite
                · intro a
                  split_ifs <;> simp
              · simp_rw [tsum_fintype]
                apply Summable.of_nonneg_of_le (f := fun x => ∑ (y: ↑(P.centers ∩ D)), |(f (x.val -
                  y.val)).re|)
                · intro b
                  refine Fintype.sum_nonneg ?_
                  rw [Pi.le_def]
                  simp
                · intro b
                  apply Finset.sum_le_sum
                  intro x hx
                  split_ifs <;> simp
                · apply summable_sum
                  intro y hy
                  have summable_f_re: Summable (fun x => (f x).re) := by
                    apply (Complex.hasSum_re (hf.choose_spec)).summable
                  rw [summable_abs_iff]
                  apply Summable.comp_injective summable_f_re
                  -- TODO - find a simpler injectivity proof
                  intro a b hab
                  field_simp at hab
                  aesop
            · apply summable_of_hasFiniteSupport
              -- TODO - is there a better way of writing (P.centers ∩ D) when dealing with subtypes?
              apply Set.Finite.subset (s := {x: ↑P.centers | x.val ∈ D})
              · rw [Set.finite_coe_iff] at sum_finite
                apply Set.Finite.of_finite_image (f := Subtype.val)
                · conv =>
                    arg 1
                    equals (P.centers ∩ D) =>
                      ext a
                      rw [Set.inter_comm]
                      simp
                  exact sum_finite
                · simp
              · intro x hx
                simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hx
                simp [hx.1]
  _ ≤ ∑' (x : ↑(P.centers ∩ D)), (f (0 : EuclideanSpace ℝ (Fin d))).re
        := by
            rw [← tsub_nonpos]
            rw [add_sub_cancel_right]
            apply tsum_nonpos
            intro x
            apply tsum_nonpos
            intro y
            cases eq_or_ne ((x : EuclideanSpace ℝ (Fin d)) - y) (0 : EuclideanSpace ℝ (Fin d))
            · case inl h =>
              simp only [h, ↓reduceDIte, le_refl]
            · case inr h =>
              simp only [h, ↓reduceDIte]
              apply hCohnElkies₁ (x - y)
              -- Both `x` and `y` are in `P.centers` and are distinct. `hP` then implies the result.
              rw [← hP]
              apply P.centers_dist'
              · exact Subtype.mem x
              · obtain ⟨hy₁, hy₂⟩ := Subtype.mem y
                exact hy₁
              · exact sub_ne_zero.mp h
    -- _ = ∑' (y : ↑(P.centers ∩ D)), (f (y - ↑y)).re
    -- := by simp only [sub_self]
    _ = ↑(P.numReps' hd hD_isBounded) * (f 0).re
        := by
            simp only [tsum_const, nsmul_eq_mul, mul_eq_mul_right_iff, Nat.cast_inj]
            cases eq_or_ne (f 0).re 0
            · case inl h =>
              right
              rw [h]
            · case inr h =>
              left
              let myInstFintype := P.instFintypeNumReps' hd hD_isBounded
              rw [PeriodicSpherePacking.numReps']
              exact Nat.card_eq_fintype_card

omit [Nonempty ↑P.centers] in
include hD_isBounded in
lemma calc_steps' (hd : 0 < d) :
    ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : ↥P.lattice), (f (↑x - ↑y + ↑ℓ)).re =
    (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : ↥P.lattice), f (↑x - ↑y + ↑ℓ)).re := by
  haveI : Finite ↑(P.centers ∩ D) := finite_centers_inter_of_isBounded P D hD_isBounded hd
  rw [re_tsum Summable.of_finite]
  refine tsum_congr fun x => ?_
  rw [re_tsum Summable.of_finite]
  refine tsum_congr fun y => ?_
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (re_tsum
        (SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_translate (Λ := P.lattice)
          (f := f) (a := (↑x - ↑y : EuclideanSpace ℝ (Fin d))))).symm

-- NOTE: intermediate summability facts should follow from `PSF_Conditions`
-- (add assumptions here if needed).
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
  calc
  ↑(P.numReps' hd hD_isBounded) * (f 0).re
  _ ≥ ∑' (x : P.centers) (y : ↑(P.centers ∩ D)),
      (f (x - ↑y)).re
        := by
            rw [ge_iff_le]
            exact calc_aux_1 hCohnElkies₁ hP hD_isBounded hd hD_unique_covers
  _ =
      ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
      (f (↑x - ↑y + ↑ℓ)).re
        := CohnElkies.tsum_centers_eq_tsum_centersInter_centersInter_lattice f P
              hD_isBounded hD_unique_covers hd
  -- Pull out real parts so we can apply PSF-L to the complex equality.
  _ = (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
      f (↑x - ↑y + ↑ℓ)).re
        := calc_steps' hD_isBounded hd
  _ = (∑' x : ↑(P.centers ∩ D),
      ∑' y : ↑(P.centers ∩ D), (1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m) *
      exp (2 * π * I * ⟪↑x - ↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])).re
        := by
            congr! 5 with x y
            exact SchwartzMap.poissonSummation_lattice P.lattice f _
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
      (𝓕 f m).re * (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
      exp (2 * π * I * ⟪↑x - ↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re
        := by
            simpa using
              (SpherePacking.CohnElkies.calc_steps_swap_sums (f := f)
                (hRealFourier := hRealFourier) (P := P) (D := D) hD_isBounded hd)
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m).re * (
      ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) *
      exp (2 * π * I * ⟪-↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re
        := by
            -- Use `congrArg`s to isolate the target expressions.
            congr! 9 with m x y
            simp only [sub_eq_neg_add, RCLike.wInner_neg_left, ofReal_neg, mul_neg, mul_comm]
            rw [RCLike.wInner_add_left]
            simp only [RCLike.wInner_neg_left, ofReal_add, ofReal_neg]
            rw [mul_add, Complex.exp_add, mul_comm]
            simp
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
      (𝓕 f m).re * (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
      (∑' y : ↑(P.centers ∩ D),
      exp (-(2 * π * I * ⟪↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])))).re
        := by
            simp_rw [mul_assoc, ← tsum_mul_right, ← tsum_mul_left]
            congr! 9 with m x y
            simp only [RCLike.wInner_neg_left, ofReal_neg, mul_neg]
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f
      m).re *
      (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
      conj (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) -- Need its complex conjugate
      ).re
        := by
            simp_rw [conj_tsum]
            congr! 7 with m x
            exact Complex.exp_neg_real_I_eq_conj (x : EuclideanSpace ℝ (Fin d)) m
    _ = (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
          (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)
          := by
            rw [← ofReal_re (1 / ZLattice.covolume P.lattice volume *
                ∑' (m : ↥(LinearMap.BilinForm.dualSubmodule (innerₗ _) P.lattice)),
                 (𝓕 ⇑f ↑m).re * norm (∑' (x : ↑(P.centers ∩ D)),
                 cexp (2 * ↑π * I * ↑⟪(x : EuclideanSpace ℝ (Fin d)), ↑m⟫_[ℝ])) ^ 2)]
            congr 1
            push_cast
            congr! 3 with m
            rw [mul_assoc]
            apply congrArg _ _
            rw [mul_conj, Complex.normSq_eq_norm_sq]
            norm_cast

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
  calc
    (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              exp (2 * π * I *
                ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)
    _ = (1 / ZLattice.covolume P.lattice volume) * (
        (∑' (m : SchwartzMap.dualLattice (d := d) P.lattice),
          if m = (0 : ↥(SchwartzMap.dualLattice (d := d) P.lattice)) then 0
          else (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2))
        +
        (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re *
        (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2))
          := by
              refine congrArg (fun t => (1 / ZLattice.covolume P.lattice volume) * t) ?_
              have hSummable :
                  Summable (fun m : ↥(SchwartzMap.dualLattice (d := d) P.lattice) =>
                    (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
                    exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) := by
                have hfinite : Finite (↑(P.centers ∩ D)) :=
                  finite_centers_inter_of_isBounded P D hD_isBounded hd
                letI : Fintype (↑(P.centers ∩ D)) := Fintype.ofFinite (↑(P.centers ∩ D))
                let n : ℝ := (Fintype.card (↑(P.centers ∩ D)) : ℝ)
                have hn_nonneg : 0 ≤ n := by
                  simp [n]
                have hFourierNorm :
                    Summable (fun m : ↥(SchwartzMap.dualLattice (d := d) P.lattice) =>
                      ‖(𝓕 ⇑f) (m : EuclideanSpace ℝ (Fin d))‖) := by
                  have h0 :
                      Summable (fun m : ↥(SchwartzMap.dualLattice (d := d) P.lattice) =>
                        ‖(𝓕 f) ((0 : EuclideanSpace ℝ (Fin d)) +
                          (m : EuclideanSpace ℝ (Fin d)))‖) :=
                    SpherePacking.CohnElkies.LPBoundAux.summable_norm_comp_add_zlattice
                      (Λ := SchwartzMap.dualLattice (d := d) P.lattice) (f := 𝓕 f)
                      (a := (0 : EuclideanSpace ℝ (Fin d)))
                  have h1 :
                      Summable (fun m : ↥(SchwartzMap.dualLattice (d := d) P.lattice) =>
                        ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖) := by
                    simpa using h0
                  simpa [SchwartzMap.fourier_coe] using h1
                let g' : ↥(SchwartzMap.dualLattice (d := d) P.lattice) → ℝ := fun m =>
                  ‖(𝓕 ⇑f) (m : EuclideanSpace ℝ (Fin d))‖ * (n ^ 2)
                refine Summable.of_norm_bounded
                  (g := g') ?_ ?_
                · simpa [g'] using hFourierNorm.mul_right (n ^ 2)
                · intro m
                  set A : ℂ :=
                      ∑' x : ↑(P.centers ∩ D),
                        exp (2 * π * I *
                          ⟪(x : EuclideanSpace ℝ (Fin d)),
                            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) with hAdef
                  have hnexp :
                      ∀ x : ↑(P.centers ∩ D),
                        ‖exp (2 * π * I *
                          ⟪(x : EuclideanSpace ℝ (Fin d)),
                            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])‖ = (1 : ℝ) := by
                    intro x
                    have hmul :
                        (2 * π * I *
                          (⟪(x : EuclideanSpace ℝ (Fin d)),
                            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] : ℂ))
                          =
                          ((2 * π *
                            ⟪(x : EuclideanSpace ℝ (Fin d)),
                              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] : ℝ) : ℂ) * I := by
                      simp [mul_assoc, mul_comm]
                    simpa [hmul] using
                      (Complex.norm_exp_ofReal_mul_I
                        (2 * π *
                          ⟪(x : EuclideanSpace ℝ (Fin d)),
                            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))
                  have hA_le : ‖A‖ ≤ n := by
                    rw [hAdef]
                    have htri :
                        ‖∑ x : ↑(P.centers ∩ D),
                            exp (2 * π * I *
                              ⟪(x : EuclideanSpace ℝ (Fin d)),
                                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])‖
                          ≤
                          ∑ x : ↑(P.centers ∩ D),
                            ‖exp (2 * π * I *
                              ⟪(x : EuclideanSpace ℝ (Fin d)),
                                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])‖ := by
                      simpa using
                        (norm_sum_le (s := Finset.univ)
                          (f := fun x : ↑(P.centers ∩ D) =>
                            exp (2 * π * I *
                              ⟪(x : EuclideanSpace ℝ (Fin d)),
                                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])))
                    simpa [tsum_fintype, hnexp, n] using htri
                  have hA_sq : ‖A‖ ^ 2 ≤ n ^ 2 := by
                    exact pow_le_pow_left₀ (norm_nonneg A) hA_le 2
                  have hRe_le :
                      ‖((𝓕 ⇑f) (m : EuclideanSpace ℝ (Fin d))).re‖
                        ≤ ‖(𝓕 ⇑f) (m : EuclideanSpace ℝ (Fin d))‖ := by
                    simpa [Real.norm_eq_abs] using
                      (abs_re_le_norm ((𝓕 ⇑f) (m : EuclideanSpace ℝ (Fin d))))
                  calc
                    ‖(𝓕 ⇑f m).re * (‖A‖ ^ 2)‖
                        = ‖((𝓕 ⇑f) (m : EuclideanSpace ℝ (Fin d))).re‖ * ‖‖A‖ ^ 2‖ := by
                          simp [norm_mul]
                    _ ≤ ‖((𝓕 ⇑f) (m : EuclideanSpace ℝ (Fin d))).re‖ * (n ^ 2) := by
                          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
                          simpa [Real.norm_of_nonneg (sq_nonneg _)] using hA_sq
                    _ ≤ ‖(𝓕 ⇑f) (m : EuclideanSpace ℝ (Fin d))‖ * (n ^ 2) := by
                          exact mul_le_mul_of_nonneg_right hRe_le (by positivity)
                    _ ≤ g' m := by
                          simp [g']
              have hsplit :=
                (Summable.tsum_eq_add_tsum_ite hSummable
                  (0 : ↥(SchwartzMap.dualLattice (d := d) P.lattice)))
              refine hsplit.trans ?_
              ac_rfl
    _ ≥ (1 / ZLattice.covolume P.lattice volume) * (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re *
        (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)
          := by
              rw [ge_iff_le, ← tsub_nonpos, mul_assoc,
                  ← mul_sub (1 / ZLattice.covolume P.lattice volume) _ _]
              simp only [sub_add_cancel_right, mul_neg, Left.neg_nonpos_iff]
              apply mul_nonneg
              · refine one_div_nonneg.mpr ?ha.a
                rw [ZLattice.covolume]
                exact ENNReal.toReal_nonneg
              · exact
                  SpherePacking.CohnElkies.tsum_ite_fourier_re_mul_norm_tsum_exp_sq_nonneg
                    (f := f) (P := P) (D := D) (hCohnElkies₂ := hCohnElkies₂)
    _ = (1 / ZLattice.covolume P.lattice volume) * (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re *
        ↑(P.numReps' hd hD_isBounded) ^ 2
          := by
              have hnorm0 :=
                SpherePacking.CohnElkies.norm_tsum_exp_inner_zero_sq_eq_numReps_sq
                  (P := P) (D := D) (hd := hd) (hD_isBounded := hD_isBounded)
              simp only [hnorm0]
    _ = ↑(P.numReps' hd hD_isBounded) ^ 2 * (𝓕 f 0).re / ZLattice.covolume P.lattice volume := by
              have hfou :
                  (𝓕 f) (0 : EuclideanSpace ℝ (Fin d)) = (𝓕 ⇑f) (0 : EuclideanSpace ℝ (Fin d)) := by
                simpa using congrArg (fun g : EuclideanSpace ℝ (Fin d) → ℂ => g 0)
                  (SchwartzMap.fourier_coe (f := f))
              have hfou_re : (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re = (𝓕 f 0).re := by
                simp [hfou]
              -- Commutative-monoid algebra + `hfou_re` (separate lemma avoids heartbeats).
              have hcomm :
                  (1 / ZLattice.covolume P.lattice volume) *
                      (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re *
                      (↑(P.numReps' hd hD_isBounded) : ℝ) ^ 2
                    =
                    (↑(P.numReps' hd hD_isBounded) : ℝ) ^ 2 *
                      (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re /
                        ZLattice.covolume P.lattice volume :=
                SpherePacking.CohnElkies.one_div_mul_mul_eq_mul_mul_div
                  (α := ℝ)
                  (c := ZLattice.covolume P.lattice volume)
                  (a := (𝓕 ⇑f 0).re)
                  (b := (↑(P.numReps' hd hD_isBounded) : ℝ) ^ 2)
              assumption

include d f hP hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hD_unique_covers in
omit hne_zero hReal in
theorem calc_steps (hd : 0 < d) :
    ↑(P.numReps' hd hD_isBounded) * (f 0).re ≥ ↑(P.numReps' hd hD_isBounded) ^ 2 *
      (𝓕 f 0).re / ZLattice.covolume P.lattice volume := by
  exact ge_trans
    (calc_steps_part1 (P := P) (D := D) (hRealFourier := hRealFourier)
      (hCohnElkies₁ := hCohnElkies₁) (hP := hP) (hD_isBounded := hD_isBounded)
      (hD_unique_covers := hD_unique_covers) hd)
    (calc_steps_part2 (P := P) (D := D) (hCohnElkies₂ := hCohnElkies₂)
      (hD_isBounded := hD_isBounded) hd)

end Fundamental_Domain_Dependent

section Main_Theorem_For_One_Packing

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)

include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ P hP D hD_isBounded
  hD_unique_covers

/--
Linear programming bound for a single periodic packing of separation `1`.

This is the key estimate used to bound `SpherePackingConstant d`
after reducing to periodic packings.
-/
public theorem LinearProgrammingBound' (hd : 0 < d) :
  P.density ≤ (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal *
  volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  haveI : Fact (0 < d) := ⟨hd⟩
  rw [P.density_eq' hd]
  suffices hCalc : (P.numReps' hd hD_isBounded) * (f 0).re ≥
    (P.numReps' hd hD_isBounded)^2 * (𝓕 f 0).re / ZLattice.covolume P.lattice volume by
    rw [hP]
    rw [ge_iff_le] at hCalc
    have vol_pos := EuclideanSpace.volume_ball_pos (0 : EuclideanSpace ℝ (Fin d)) one_half_pos
    have vol_ne_zero : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≠ 0 :=
      (ne_of_lt vol_pos).symm
    have vol_ne_top : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≠ ∞ :=
      ne_of_lt (EuclideanSpace.volume_ball_lt_top (0 : EuclideanSpace ℝ (Fin d)))
    cases eq_or_ne (𝓕 f 0) 0
    · case inl h𝓕f =>
      rw [h𝓕f, zero_re]
      -- For `ENNReal.div_zero`, need `f 0 ≠ 0` (from `𝓕 f ≥ 0` and `f ≠ 0`).
      have ne_zero_at_zero : ((f 0).re.toNNReal : ENNReal) ≠ 0 :=
        ENNReal.coe_ne_zero.mpr (Ne.symm (ne_of_lt (toNNReal_pos.mpr
        (f_zero_pos hne_zero hReal hRealFourier hCohnElkies₂))))
      -- Now we can safely divide by zero!
      rw [ENat.toENNReal_coe, toNNReal_zero, ENNReal.coe_zero, ENNReal.div_zero ne_zero_at_zero]
      -- Multiply by ⊤.
      rw [ENNReal.top_mul vol_ne_zero]
      exact le_top
    · case inr h𝓕f =>
      -- Shift and cancel volumes on the right.
      rw [ENat.toENNReal_coe, mul_div_assoc, div_eq_mul_inv (volume _), mul_comm (volume _),
          ← mul_assoc, ENNReal.mul_le_mul_iff_left vol_ne_zero vol_ne_top]
      -- Simplify `hCalc` by replacing `numReps'` with `numReps`.
      rw [← PeriodicSpherePacking.numReps_eq_numReps' (S := P) Fact.out hD_isBounded
        hD_unique_covers] at hCalc
      -- Multiply by `(𝓕 (⇑f) 0).re.toNNReal` and cancel.
      have hfouaux₁ : ((𝓕 f 0).re.toNNReal : ENNReal) ≠ 0 := by
        intro hContra
        apply h𝓕f
        simp only [ENNReal.coe_eq_zero, toNNReal_eq_zero] at hContra
        specialize hCohnElkies₂ 0
        rw [ge_iff_le] at hCohnElkies₂
        -- Can't use antisymm: equality is in ℂ, not ℝ.
        rw [← re_add_im (𝓕 f 0), le_antisymm hContra hCohnElkies₂,
            hFourierImZero hRealFourier 0, ofReal_zero, zero_mul, add_zero]
      have hfouaux₂ : ((𝓕 (⇑f) 0).re.toNNReal : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      rw [← ENNReal.mul_le_mul_iff_left hfouaux₁ hfouaux₂,
          div_eq_mul_inv ((f 0).re.toNNReal : ENNReal) _,
          mul_assoc ((f 0).re.toNNReal : ENNReal) _ _, ENNReal.inv_mul_cancel hfouaux₁ hfouaux₂]
      -- Put it in a more desirable form and consolidate.
      rw [mul_one, mul_assoc, ← ENNReal.div_eq_inv_mul]
      -- Multiply both sides by `↑P.numReps`.
      have hnRaux₁ : ENat.toENNReal (P.numReps : ENat) ≠ 0 := by
        rw [ENat.toENNReal_coe, ne_eq, Nat.cast_eq_zero, ← ne_eq]
        -- intro hContra
        -- rw [← P.card_centers_inter_isFundamentalDomain D hD_isBounded hD_unique_covers Fact.out]
        unfold PeriodicSpherePacking.numReps
        haveI : Nonempty (Quotient (AddAction.orbitRel ↥P.lattice ↑P.centers)) := by
          rw [nonempty_quotient_iff]
          assumption
        exact Fintype.card_ne_zero
      have hnRaux₂ : ENat.toENNReal (P.numReps : ENat) ≠ ⊤ := Ne.symm (ne_of_beq_false rfl)
      rw [← ENNReal.mul_le_mul_iff_right hnRaux₁ hnRaux₂]
      -- Put it in a more desirable form and consolidate.
      rw [ENat.toENNReal_coe, ← mul_assoc, ← pow_two, ← mul_div_assoc]
      -- Use nonnegativity to pull `toNNReal`s out.
      have hRHSCast : (P.numReps : ENNReal) * ↑(f 0).re.toNNReal = (P.numReps * (f 0).re).toNNReal
      := by
        -- rw [ENNReal.coe_mul, ENNReal.coe_natCast]
        norm_cast
        refine NNReal.eq ?_
        have haux₁ : 0 ≤ ↑P.numReps * (f 0).re := mul_nonneg (Nat.cast_nonneg' P.numReps)
          (f_nonneg_at_zero hCohnElkies₂)
        rw [Real.toNNReal_of_nonneg (f_nonneg_at_zero hCohnElkies₂),
            Real.toNNReal_of_nonneg haux₁]
        push_cast
        rfl
      have hLHSCast : (P.numReps : ENNReal) ^ 2 * ((𝓕 f 0).re.toNNReal : ENNReal) /
        ((ZLattice.covolume P.lattice volume).toNNReal : ENNReal) = ((P.numReps) ^ 2 *
        (𝓕 f 0).re / ZLattice.covolume P.lattice volume).toNNReal := by
        simp only [div_eq_mul_inv]
        have haux₁ : 0 ≤ ↑P.numReps ^ 2 * (𝓕 f 0).re * (ZLattice.covolume P.lattice volume)⁻¹
        := by
          refine mul_nonneg (mul_nonneg (sq_nonneg (P.numReps : ℝ)) (hCohnElkies₂ 0)) ?_
          rw [inv_nonneg]
          exact LT.lt.le (ZLattice.covolume_pos P.lattice volume)
        rw [Real.toNNReal_of_nonneg haux₁]
        have haux₂ : (ZLattice.covolume P.lattice volume).toNNReal ≠ 0 := by
          apply LT.lt.ne'
          rw [Real.toNNReal_pos]
          exact ZLattice.covolume_pos P.lattice volume
        rw [← ENNReal.coe_inv haux₂]
        norm_cast
        rw [Real.toNNReal_of_nonneg (hCohnElkies₂ 0),
            Real.toNNReal_of_nonneg (LT.lt.le (ZLattice.covolume_pos P.lattice volume))]
        rfl
      -- Drop `toNNReal`s and finish with `hCalc`.
      rw [hRHSCast, hLHSCast, ENNReal.coe_le_coe]
      exact Real.toNNReal_le_toNNReal hCalc
  exact calc_steps hRealFourier hCohnElkies₁ hCohnElkies₂ hP hD_isBounded hD_unique_covers hd

end Main_Theorem_For_One_Packing

section Main_Theorem

include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂

/-- The Cohn-Elkies linear programming upper bound on `SpherePackingConstant d`. -/
public theorem LinearProgrammingBound (hd : 0 < d) : SpherePackingConstant d ≤
  (f 0).re.toNNReal / (𝓕 ⇑f 0).re.toNNReal *
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
  := by
  rw [← periodic_constant_eq_constant hd,
    periodic_constant_eq_periodic_constant_normalized hd]
  apply iSup_le
  intro P
  rw [iSup_le_iff]
  intro hP
  cases isEmpty_or_nonempty ↑P.centers
  · case inl instEmpty =>
    rw [P.density_of_centers_empty hd]
    exact zero_le'
  · case inr instNonempty =>
    let b : Basis (Fin d) ℤ ↥P.lattice := ((ZLattice.module_free ℝ P.lattice).chooseBasis).reindex
      (P.basis_index_equiv)
    exact LinearProgrammingBound' hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP
      (fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ P.lattice b))
      (P.fundamental_domain_unique_covers b) hd hf

end Main_Theorem
