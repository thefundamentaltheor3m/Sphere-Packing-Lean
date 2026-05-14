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
public import SpherePacking.CohnElkies.LPBoundAux
public import SpherePacking.CohnElkies.LPBoundReindex
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Cohn-Elkies linear programming bound

Cohn-Elkies upper bound on `SpherePackingConstant d` via `LinearProgrammingBound`.
-/

open scoped FourierTransform ENNReal SchwartzMap BigOperators
open SpherePacking MeasureTheory Complex Real Bornology Module

namespace SpherePacking.CohnElkies

section SwapSums

/-- Commute the finite `x,y` sums with the dual-lattice `m` sum in the Poisson summation
expression. We assume `𝓕 f` is real-valued so the result lives in real parts. -/
public lemma calc_steps_swap_sums {d : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
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

end SwapSums

section LatticeSumBounds

variable {d : ℕ} {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}
variable {P : PeriodicSpherePacking d} {D : Set (EuclideanSpace ℝ (Fin d))}

/-- Pointwise bound on the lattice sum appearing in the Cohn-Elkies argument. -/
public lemma lattice_sum_re_le_ite (hP : P.separation = 1)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (x y : ↑(P.centers ∩ D)) :
    (∑' ℓ : P.lattice,
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
      ≤ ite (x = y) (f 0).re 0 := by
  -- If `x,y ∈ D` and `x + ℓ = y`, then `ℓ = 0` by uniqueness of the cover of `y`.
  have hℓ_eq_zero_of_vadd_eq {x y : ↑(P.centers ∩ D)} {ℓ : P.lattice}
      (hxy : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) =
          (y : EuclideanSpace ℝ (Fin d))) : ℓ = 0 := by
    obtain ⟨_, -, hg0_unique⟩ := hD_unique_covers (y : EuclideanSpace ℝ (Fin d))
    have hy0 : (0 : P.lattice) +ᵥ (y : EuclideanSpace ℝ (Fin d)) ∈ D := by
      simpa [Submodule.vadd_def] using y.property.2
    have hyℓ : (-ℓ : P.lattice) +ᵥ (y : EuclideanSpace ℝ (Fin d)) ∈ D := by
      have hEq : ((-ℓ : P.lattice) : EuclideanSpace ℝ (Fin d)) + (y : EuclideanSpace ℝ (Fin d)) =
          (x : EuclideanSpace ℝ (Fin d)) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (eq_sub_of_add_eq hxy).symm
      simpa [Submodule.vadd_def] using (hEq ▸ x.property.2 :
        ((-ℓ : P.lattice) : EuclideanSpace ℝ (Fin d)) + _ ∈ D)
    simpa using neg_eq_zero.mp ((hg0_unique (-ℓ) hyℓ).trans (hg0_unique 0 hy0).symm)
  by_cases hxy : x = y
  · subst hxy
    have hs : Summable fun ℓ : P.lattice => (f (ℓ : EuclideanSpace ℝ (Fin d))).re := by
      simpa [zero_add] using
        (SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_translate_re
          (Λ := P.lattice) (f := f) (a := (0 : EuclideanSpace ℝ (Fin d))))
    have htail : (∑' ℓ : P.lattice,
          ite (ℓ = (0 : P.lattice)) 0 (f (ℓ : EuclideanSpace ℝ (Fin d))).re) ≤ 0 := by
      refine tsum_nonpos fun ℓ => ?_
      by_cases hℓ : ℓ = 0
      · simp [hℓ]
      have hxℓ : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ∈ P.centers := by
        simpa [add_comm] using P.lattice_action ℓ.property x.property.1
      have hneq : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ≠
            (x : EuclideanSpace ℝ (Fin d)) := fun h => hℓ (hℓ_eq_zero_of_vadd_eq h)
      have hnorm : (1 : ℝ) ≤ ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ := by
        have : (1 : ℝ) ≤ dist
            ((x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)))
            (x : EuclideanSpace ℝ (Fin d)) := by
          simpa [hP] using P.centers_dist' _ _ hxℓ x.property.1 hneq
        simpa [dist_eq_norm, add_sub_cancel_left] using this
      simp [hℓ, hCohnElkies₁ (ℓ : EuclideanSpace ℝ (Fin d)) (by simpa [ge_iff_le] using hnorm)]
    have hsum_le : (∑' ℓ : P.lattice, (f (ℓ : EuclideanSpace ℝ (Fin d))).re) ≤ (f 0).re := by
      rw [hs.tsum_eq_add_tsum_ite (0 : P.lattice)]
      simpa using add_le_add_left htail (f 0).re
    simpa using hsum_le
  · have hnonpos : ∀ ℓ : P.lattice,
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re ≤ 0 := by
      intro ℓ
      have hxℓ : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ∈ P.centers := by
        simpa [add_comm] using P.lattice_action ℓ.property x.property.1
      have hneq : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ≠
            (y : EuclideanSpace ℝ (Fin d)) := by
        intro h
        have : ℓ = 0 := hℓ_eq_zero_of_vadd_eq (x := x) (y := y) (ℓ := ℓ) h
        subst this
        exact hxy (Subtype.ext (by simpa using h))
      have hdist := P.centers_dist' _ _ hxℓ y.property.1 hneq
      have hnorm : (1 : ℝ) ≤ ‖(x : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))‖ := by
        have : (1 : ℝ) ≤ dist
            ((x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)))
            (y : EuclideanSpace ℝ (Fin d)) := by simpa [hP] using hdist
        simpa [dist_eq_norm] using this
      have hle := hCohnElkies₁ _ (by simpa [ge_iff_le] using hnorm)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hle
    simpa [hxy] using tsum_nonpos hnonpos

end LatticeSumBounds

end SpherePacking.CohnElkies

variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)

local notation "conj" => starRingEnd ℂ

section Nonnegativity

theorem hIntegrable : MeasureTheory.Integrable (𝓕 ⇑f) :=
  (FourierTransform.fourierCLE ℝ (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) f).integrable

include hReal hRealFourier hCohnElkies₂ hne_zero in
theorem f_zero_pos : 0 < (f 0).re := by
  refine lt_of_le_of_ne (show 0 ≤ (f 0).re by
    rw [← f.fourierInversion, fourierInv_eq]
    simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul, ← RCLike.re_eq_complex_re,
      ← integral_re hIntegrable]
    exact integral_nonneg fun v ↦ by simpa using hCohnElkies₂ v) fun hf0re => hne_zero <|
    (ContinuousLinearEquiv.map_eq_zero_iff (FourierTransform.fourierCLE ℝ _)).1 ?_
  have hfun := (Continuous.integral_zero_iff_zero_of_nonneg
    (Complex.continuous_re.comp (𝓕 f).continuous) hIntegrable.re hCohnElkies₂).1 (by
    rw [show (∫ v : EuclideanSpace ℝ (Fin d), (re ∘ 𝓕 ⇑f) v) =
        (∫ v : EuclideanSpace ℝ (Fin d), 𝓕 (⇑f) v).re by
      simpa using integral_re (f := fun v : EuclideanSpace ℝ (Fin d) => 𝓕 (⇑f) v) hIntegrable]
    simpa [fourierInv_eq, show f 0 = 0 from by simpa [hf0re.symm] using (hReal 0).symm] using
      congrArg Complex.re (congrArg (· 0) f.fourierInversion))
  ext x; simpa [show (𝓕 f x).re = 0 from by simpa using congrFun hfun x] using (hRealFourier x).symm

end Nonnegativity

section Fundamental_Domain_Dependent

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)

omit [Nonempty ↑P.centers] in include hD_isBounded in
private lemma summable_fourier_mul_norm_exp_sq (hd : 0 < d) :
    Summable (fun m : ↥(SchwartzMap.dualLattice (d := d) P.lattice) =>
      (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) := by
  letI : Fintype (↑(P.centers ∩ D)) :=
    @Fintype.ofFinite _ <| finite_centers_inter_of_isBounded P D hD_isBounded hd
  refine Summable.of_norm_bounded (g := fun m => ‖(𝓕 ⇑f) (m : EuclideanSpace ℝ (Fin d))‖ *
    ((Fintype.card (↑(P.centers ∩ D)) : ℝ) ^ 2)) ?_ fun m => ?_
  · simpa [SchwartzMap.fourier_coe] using
      (SpherePacking.CohnElkies.LPBoundAux.summable_norm_comp_add_zlattice
        (Λ := SchwartzMap.dualLattice (d := d) P.lattice) (f := 𝓕 f)
        (a := (0 : EuclideanSpace ℝ (Fin d)))).mul_right _
  simp only [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]; gcongr
  · simpa [Real.norm_eq_abs] using abs_re_le_norm _
  · simpa [tsum_fintype, Complex.norm_exp, mul_re, mul_im, mul_assoc, mul_left_comm, mul_comm]
      using norm_sum_le (Finset.univ : Finset ↑(P.centers ∩ D)) fun x : ↑(P.centers ∩ D) =>
      exp (2 * π * I * ⟪(x : EuclideanSpace ℝ (Fin d)), (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])

include d f hP hRealFourier hCohnElkies₁ hD_unique_covers in
theorem calc_steps_part1 (hd : 0 < d) :
    ↑(P.numReps' hd hD_isBounded) * (f 0).re ≥
      (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              exp (2 * π * I *
                ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2) := by
  calc ↑(P.numReps' hd hD_isBounded) * (f 0).re
  _ ≥ ∑' (x : P.centers) (y : ↑(P.centers ∩ D)), (f (x - ↑y)).re := by
        letI : Fintype ↑(P.centers ∩ D) := P.instFintypeNumReps' hd hD_isBounded
        classical
        simp_rw [SpherePacking.CohnElkies.tsum_centers_eq_tsum_centersInter_centersInter_lattice
          (f := f) (P := P) (D := D) hD_isBounded hD_unique_covers hd, tsum_fintype]
        exact (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ =>
          CohnElkies.lattice_sum_re_le_ite hP hD_unique_covers hCohnElkies₁ x i).trans
          (by simp [PeriodicSpherePacking.numReps'])
  _ = ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice), (f (↑x - ↑y + ↑ℓ)).re :=
        CohnElkies.tsum_centers_eq_tsum_centersInter_centersInter_lattice f P
          hD_isBounded hD_unique_covers hd
  _ = (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
      f (↑x - ↑y + ↑ℓ)).re := by
        haveI : Finite ↑(P.centers ∩ D) := finite_centers_inter_of_isBounded P D hD_isBounded hd
        rw [re_tsum Summable.of_finite]
        exact tsum_congr fun x => by
          rw [re_tsum Summable.of_finite]; exact tsum_congr fun y => by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              (re_tsum (SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_translate
                (Λ := P.lattice) (f := f) (a := (↑x - ↑y : EuclideanSpace ℝ (Fin d))))).symm
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
        congr! 9 with m x y; simp [sub_eq_neg_add, RCLike.wInner_neg_left, ofReal_neg, mul_neg,
          mul_comm, RCLike.wInner_add_left, ofReal_add, mul_add, Complex.exp_add]
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
      (𝓕 f m).re * (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
      (∑' y : ↑(P.centers ∩ D),
      exp (-(2 * π * I * ⟪↑y, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])))).re := by
        simp_rw [mul_assoc, ← tsum_mul_right, ← tsum_mul_left]
        congr! 9 with m x y; simp only [RCLike.wInner_neg_left, ofReal_neg, mul_neg]
  _ = ((1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m).re *
      (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
      conj (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re := by
        simp_rw [conj_tsum]
        congr! 7 with m x
        calc Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
              (⟪(x : EuclideanSpace ℝ (Fin d)), m⟫_[ℝ] : ℂ)))
            = Circle.exp (-2 * Real.pi * ⟪(x : EuclideanSpace ℝ (Fin d)), m⟫_[ℝ]) := by
              rw [Circle.coe_exp]; push_cast; ring_nf
          _ = conj (Circle.exp (2 * Real.pi * ⟪(x : EuclideanSpace ℝ (Fin d)), m⟫_[ℝ])) := by
              rw [mul_assoc, neg_mul, ← mul_assoc, ← Circle.coe_inv_eq_conj, Circle.exp_neg]
          _ = conj (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                (⟪(x : EuclideanSpace ℝ (Fin d)), m⟫_[ℝ] : ℂ))) := by
              rw [Circle.coe_exp]; apply congrArg conj; push_cast; ring_nf
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

include d f hCohnElkies₂ in omit [Nonempty ↑P.centers] in
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
        exp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) :=
        congrArg ((1 / ZLattice.covolume P.lattice volume) * ·)
          ((Summable.tsum_eq_add_tsum_ite (summable_fourier_mul_norm_exp_sq (f := f) (P := P)
            (D := D) (hD_isBounded := hD_isBounded) hd) 0).trans (by ac_rfl))
    _ ≥ (1 / ZLattice.covolume P.lattice volume) * (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re *
        (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2) := by
        rw [ge_iff_le, ← tsub_nonpos, mul_assoc, ← mul_sub (1 / _) _ _]
        simpa using mul_nonneg (one_div_nonneg.mpr (ZLattice.covolume_pos P.lattice volume).le)
          (tsum_nonneg fun m => by
            by_cases hm : m = (0 : ↥(SchwartzMap.dualLattice (d := d) P.lattice))
            · simp [hm]
            · simpa [hm] using mul_nonneg
                (by simpa using hCohnElkies₂ (m : EuclideanSpace ℝ (Fin d)))
                (sq_nonneg (norm (∑' x : ↑(P.centers ∩ D),
                  exp (2 * π * I * ⟪(x : EuclideanSpace ℝ (Fin d)),
                    (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])))))
    _ = (1 / ZLattice.covolume P.lattice volume) * (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re *
        ↑(P.numReps' hd hD_isBounded) ^ 2 := by
        letI := P.instFintypeNumReps' hd hD_isBounded
        simp [PeriodicSpherePacking.numReps']
    _ = ↑(P.numReps' hd hD_isBounded) ^ 2 * (𝓕 f 0).re / ZLattice.covolume P.lattice volume := by
      simp [div_eq_mul_inv, mul_left_comm, mul_comm,
        show 𝓕 (⇑f) (0 : EuclideanSpace ℝ (Fin d)) = 𝓕 f 0 from rfl]

include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ P hP D hD_isBounded
  hD_unique_covers

/-- Linear programming bound for a single periodic packing of separation `1`. -/
public theorem LinearProgrammingBound' (hd : 0 < d) :
    P.density ≤ (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  haveI : Fact (0 < d) := ⟨hd⟩
  rw [P.density_eq' hd]
  suffices hCalc : (P.numReps' hd hD_isBounded) * (f 0).re ≥
    (P.numReps' hd hD_isBounded)^2 * (𝓕 f 0).re / ZLattice.covolume P.lattice volume by
    rw [hP]; rw [ge_iff_le] at hCalc
    have vol_ne_zero : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≠ 0 :=
      (Metric.measure_ball_pos (μ := volume) _ one_half_pos).ne'
    rcases eq_or_ne (𝓕 f 0) 0 with h𝓕f | h𝓕f
    · rw [h𝓕f, zero_re, ENat.toENNReal_coe, toNNReal_zero, ENNReal.coe_zero,
        ENNReal.div_zero (ENNReal.coe_ne_zero.mpr (toNNReal_pos.mpr
          (f_zero_pos hne_zero hReal hRealFourier hCohnElkies₂)).ne'),
        ENNReal.top_mul vol_ne_zero]; exact le_top
    rw [← PeriodicSpherePacking.numReps_eq_numReps' (S := P) Fact.out hD_isBounded
      hD_unique_covers] at hCalc
    have hfouaux₁ : ((𝓕 f 0).re.toNNReal : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr <| by
      rw [ne_eq, Real.toNNReal_eq_zero, not_le]
      exact lt_of_le_of_ne (hCohnElkies₂ 0) fun heq => h𝓕f <|
        Complex.ext heq.symm (by simpa [eq_comm] using congrArg Complex.im (hRealFourier 0))
    haveI : Nonempty (Quotient (AddAction.orbitRel ↥P.lattice ↑P.centers)) :=
      (nonempty_quotient_iff _).2 ‹_›
    have hcov_pos : 0 < ZLattice.covolume P.lattice volume := ZLattice.covolume_pos P.lattice volume
    rw [ENat.toENNReal_coe, mul_div_assoc, div_eq_mul_inv (volume _), mul_comm (volume _),
      ← mul_assoc, ENNReal.mul_le_mul_iff_left vol_ne_zero measure_ball_lt_top.ne,
      ← ENNReal.mul_le_mul_iff_left hfouaux₁ ENNReal.coe_ne_top,
      div_eq_mul_inv ((f 0).re.toNNReal : ENNReal) _, mul_assoc ((f 0).re.toNNReal : ENNReal) _ _,
      ENNReal.inv_mul_cancel hfouaux₁ ENNReal.coe_ne_top, mul_one, mul_assoc,
      ← ENNReal.div_eq_inv_mul, ← ENNReal.mul_le_mul_iff_right
        (by simpa [ENat.toENNReal_coe] using Fintype.card_ne_zero :
          ENat.toENNReal (P.numReps : ENat) ≠ 0)
        (Ne.symm (ne_of_beq_false rfl) : ENat.toENNReal (P.numReps : ENat) ≠ ⊤),
      ENat.toENNReal_coe, ← mul_assoc, ← pow_two, ← mul_div_assoc,
      show (P.numReps : ENNReal) * ↑(f 0).re.toNNReal = (P.numReps * (f 0).re).toNNReal by
        simp [Real.toNNReal_mul (Nat.cast_nonneg _)],
      show (P.numReps : ENNReal) ^ 2 * ((𝓕 f 0).re.toNNReal : ENNReal) /
          ((ZLattice.covolume P.lattice volume).toNNReal : ENNReal) =
          ((P.numReps) ^ 2 * (𝓕 f 0).re / ZLattice.covolume P.lattice volume).toNNReal by
        simp only [div_eq_mul_inv, ← ENNReal.coe_inv (Real.toNNReal_pos.mpr hcov_pos).ne',
          Real.toNNReal_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (hCohnElkies₂ 0))
            (inv_nonneg.mpr hcov_pos.le))]
        norm_cast
        rw [Real.toNNReal_of_nonneg (hCohnElkies₂ 0), Real.toNNReal_of_nonneg hcov_pos.le]; rfl,
      ENNReal.coe_le_coe]
    exact Real.toNNReal_le_toNNReal hCalc
  exact ge_trans (calc_steps_part1 (P := P) (D := D) hRealFourier hCohnElkies₁ hP hD_isBounded
    hD_unique_covers hd) (calc_steps_part2 (P := P) (D := D) (hCohnElkies₂ := hCohnElkies₂)
      hD_isBounded hd)

end Fundamental_Domain_Dependent

section Main_Theorem

include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂

/-- The Cohn-Elkies linear programming upper bound on `SpherePackingConstant d`. -/
public theorem LinearProgrammingBound (hd : 0 < d) : SpherePackingConstant d ≤
    (f 0).re.toNNReal / (𝓕 ⇑f 0).re.toNNReal *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  rw [← periodic_constant_eq_constant hd,
    periodic_constant_eq_periodic_constant_normalized (d := d)]
  refine iSup_le fun P => iSup_le fun hP => ?_
  rcases isEmpty_or_nonempty ↑P.centers with _ | _
  · simp [P.density_of_centers_empty hd]
  exact LinearProgrammingBound' hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP
    (ZSpan.fundamentalDomain_isBounded _) (PeriodicSpherePacking.fundamental_domain_unique_covers
      (S := P) (((ZLattice.module_free ℝ P.lattice).chooseBasis).reindex
        (PeriodicSpherePacking.basis_index_equiv P))) hd

end Main_Theorem
