/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.MetricSeparated

import SpherePacking.CohnElkies.Prereqs
import SpherePacking.Basic.PeriodicPacking

open scoped FourierTransform ENNReal SchwartzMap InnerProductSpace Pointwise BigOperators
open Metric Filter MeasureTheory Complex Real ZSpan Bornology LinearMap SchwartzMap Module
  Submodule

variable {d : ℕ}

/-
# Potential Design Complications:

* What we have in Mathlib on Fourier Transforms seems to deal with complex-valued functions. I've
  dealt with it for now by giving an assumption that the imaginary part of `f` is always zero and
  stating everything else in terms of the real part of `f`. The real-valuedness may not even be
  necessary, as we could simply apply the Cohn-Elkies theorem to the real part of any complex-valued
  function whose real part satisfies the Cohn-Elkies Conditions `hCohnElkies₁` and `hCohnElkies₂`.
  If the hypothesis does go unused (as I expect it will), I will remove it.

* As mentioned in `section theorem_2_2` of `SpherePacking/Basic/PeriodicPacking.lean`, we have to
  use a hack for fundamental domains by supplying the two necessary assumptions ourselves. One day,
  when it's a bit better developed in Mathlib, we can either modify our file or let people feed in
  those assumptions as inputs.

# TODOs:

* Everything in `Prereqs.lean` is either a TODO or has already been done (eg. in #25) (to reflect
  which the corresponding refs must be updated).
* Add some lemmas about when the set of centres of a sphere packing is empty. Then, do cases here
  and remove the `Nonempty` instance in the assumptions.
-/

--Let `f : ℝᵈ → ℂ` be a Schwartz function.
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)
-- let `f` to be real-valued:
variable (hReal : ∀ x, (f x).re = f x)
-- let `𝓕 f` be real-valued:
variable (hRealFourier : ∀ x, (𝓕 f x).re = 𝓕 f x)
-- moreover, impose the Cohn-Elkies conditions:
variable (hCohnElkies₁ : ∀ x, ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x, (𝓕 f x).re ≥ 0)

-- let `conj z` denote the complex conjugate of a complex number `z`:
local notation "conj" => starRingEnd ℂ

section Complex_Function_Helpers

/-- If the real part of a function is equal to the function itself,
    then its imaginary part is zero. -/
private theorem helper (g : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d))
  (hg : (g x).re = g x) : (g x).im = 0 := by rw [← hg, ofReal_im]

/-- The imaginary part of `f` is zero everywhere. -/
private theorem hImZero (hReal : ∀ x, (f x).re = f x) :
  ∀ x, (f x).im = 0 := fun x ↦ helper f x (hReal x)

/-- The imaginary part of `𝓕 f` is zero everywhere. -/
private theorem hFourierImZero (hRealFourier : ∀ x, (𝓕 f x).re = 𝓕 f x) :
  ∀ x, (𝓕 f x).im = 0 := fun x ↦ helper (𝓕 ⇑f) x (hRealFourier x)

end Complex_Function_Helpers


section Nonnegativity

/-- The Fourier transform of a Schwartz function is non-zero if the function is non-zero. -/
theorem fourier_ne_zero (hne_zero : f ≠ 0) : 𝓕 f ≠ 0 := by
  intro hfourier_zero
  apply hne_zero
  rw [← (FourierTransform.fourierCLE ℝ (𝓢(EuclideanSpace ℝ (Fin d), ℂ))).map_eq_zero_iff]
  exact hfourier_zero

/-- If the real part of the Fourier transform `𝓕 f` is nonnegative everywhere,
    then the real part of `f` at zero is nonnegative. -/
theorem f_nonneg_at_zero (hCohnElkies₂ : ∀ x, (𝓕 f x).re ≥ 0) : 0 ≤ (f 0).re := by
  rw [← f.fourierInversion ℝ, fourierInv_eq]
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul]
  rw [← RCLike.re_eq_complex_re, ← integral_re (𝓕 f).integrable]
  exact integral_nonneg hCohnElkies₂

include hReal hRealFourier hCohnElkies₂ hne_zero in
theorem f_zero_pos : 0 < (f 0).re := by
  -- We know from previous that f(0) is nonneg. If zero, then the integral of 𝓕 f is zero, making
  -- 𝓕 f zero (it's continuous and nonneg: if it's pos anywhere, it's pos on a nbhd, and hence the
  -- integral must be pos too, but it's zero, contra). By Schwartz, f is identically zero iff 𝓕 f
  -- is (𝓕 is a linear iso). But 𝓕 f is zero while f is not, contra! So f(0) is positive.
  -- apply ne_of_gt
  have haux₁ : f 0 = 𝓕⁻ (𝓕 ⇑f) 0 := by rw [f.fourierInversion ℝ]
  rw [fourierInv_eq] at haux₁
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul] at haux₁
  -- We need to take real parts at haux₁
  rw [← re_add_im <| f 0, hImZero hReal, ofReal_zero, zero_mul, add_zero] at haux₁
  -- We need to take real and imaginary parts inside the integral.
  have haux₂ : ∫ v, 𝓕 ⇑f v = ∫ v, (𝓕 ⇑f v).re :=
    calc ∫ v, 𝓕 ⇑f v
    _ = ↑(∫ v, (𝓕 ⇑f v).re) + (∫ v, (𝓕 ⇑f v).im) * I := by
      rw [← re_add_im <| ∫ v, 𝓕 ⇑f v, ← RCLike.re_eq_complex_re,
        ← integral_re (𝓕 f).integrable, RCLike.re_eq_complex_re,
        ← RCLike.im_eq_complex_im, ← integral_im (𝓕 f).integrable, RCLike.im_eq_complex_im]
    _ = ∫ v, (𝓕 ⇑f v).re := by
      rw [add_eq_left]
      suffices hwhat : ∀ v, (𝓕 ⇑f v).im = 0 by
        simp only [hwhat, ofReal_zero, zero_mul, integral_zero]
      exact hFourierImZero hRealFourier
  rw [haux₂] at haux₁
  norm_cast at haux₁
  rw [haux₁, lt_iff_not_ge]
  by_contra integral_nonpos
  refine fourier_ne_zero hne_zero ?_
  ext x
  rw [← re_add_im <| 𝓕 f x, hFourierImZero hRealFourier, ofReal_zero, zero_mul,
    add_zero, SchwartzMap.zero_apply, ofReal_eq_zero]
  have h𝓕frezero :=
    funext_iff.1 <| ((𝓕 f).continuous.re.integral_zero_iff_zero_of_nonneg
      (𝓕 f).integrable.re hCohnElkies₂).mp (le_antisymm
        integral_nonpos (integral_nonneg hCohnElkies₂))
  exact h𝓕frezero x

end Nonnegativity


section Fundamental_Domain_Dependent

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1)
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)

/- We start with auxiliary lemmata about summability of certain functions which will be
    used in the arguments below. -/

lemma hsummable₁ (y : EuclideanSpace ℝ (Fin d)) :
    Summable fun (b : P.centers) ↦ (f (b.val - y)).re := by
  have h_translated_summable : Summable (fun x : P.centers ↦ f (x - y)) := by
    have h_translated_summable :
      Summable (fun x : (P.centers - {y} : Set (EuclideanSpace ℝ (Fin d))) => f x) := by
      apply (f.summableOn (P.centers - {y}))
      use (ENNReal.ofReal P.separation) / 2
      refine ⟨by simp; exact P.separation_pos, ?_⟩
      have := P.toSpherePacking.centers_isSeparated
      generalize_proofs at *
      exact fun x hx y hy ↦ by aesop
    convert h_translated_summable.comp_injective
      (show Function.Injective (fun x : P.centers ↦
        ⟨x - y, by aesop⟩ : P.centers → (P.centers - {y} : Set (EuclideanSpace ℝ (Fin d))))
        from fun x y hxy ↦ by aesop) using 1
  convert h_translated_summable.re using 1

include hP hCohnElkies₁ in
open Classical in
private theorem calc_aux_1 (hd : 0 < d) :
    ∑' x : P.centers, ∑' y : ↑(P.centers ∩ D), (f (x - y)).re
    ≤ (P.numReps' hd hD_isBounded) * (f 0).re := by
  calc ∑' x : P.centers, ∑' y : ↑(P.centers ∩ D), (f (x - y)).re
  _ = (∑' (x : P.centers) (y : ↑(P.centers ∩ D)), if h : x - y.val = 0 then 0 else (f (x - y)).re) +
      ∑' x : ↑(P.centers ∩ D), (f 0).re := by
    let myInstFintype := P.instFintypeNumReps' hd hD_isBounded
    conv =>
      rhs
      rhs
      equals ∑' x : P.centers, if x.val ∈ D then (f 0).re else 0 =>
        rw [tsum_subtype (f := fun x ↦ (f 0).re),
          tsum_subtype (f := fun x => if ↑x ∈ D then (f 0).re else 0)]
        exact tsum_congr fun p ↦ by simp [Set.indicator, ite_and]
    -- First, we need to un-distribute the tsums on the RHS.
    -- Then, we need to use some sort of `tsum_ite_eq`.
    -- Both of the above require some summability stuff.
    rw [← Summable.tsum_add]
    · apply tsum_congr
      intro x
      split_ifs with hx
      · let x_in : ↑(P.centers ∩ D) := ⟨x, by simp [hx]⟩
        simp only [dite_eq_ite]
        rw [← tsum_ite_eq (b := x_in) (a := fun _ ↦ (f 0).re)]
        simp_rw [← Subtype.val_inj]
        rw [← Summable.tsum_add]
        · refine tsum_congr (fun y ↦ ?_)
          simp_rw [x_in, eq_comm (a := y.val), ← sub_eq_zero (a := x.val)]
          split_ifs with x_eq_y <;> simp [x_eq_y]
        · exact Summable.of_finite
        · simpa [Subtype.val_inj] using (hasSum_ite_eq _ _).summable
      · simp only [dite_eq_ite, add_zero]
        refine tsum_congr (fun b ↦ ?_)
        have x_neq_b : x.val ≠ b.val := by
          by_contra!
          rw [this] at hx
          have b_in_d := b.property.right
          contradiction
        dsimp [Ne] at x_neq_b
        rw [← sub_eq_zero] at x_neq_b
        simp [x_neq_b]
    · rw [← summable_abs_iff]
      refine Summable.of_nonneg_of_le (by simp) ?_
        (f := fun x => ∑' (y : ↑(P.centers ∩ D)),
          ‖if h : x.val - y.val = 0 then 0 else (f (x.val - y.val)).re‖) ?_
      · intro b
        rw [← Real.norm_eq_abs]
        apply norm_tsum_le_tsum_norm
        exact Summable.of_norm_bounded (g := fun x => |(f (b.val - x.val)).re|)
          Summable.of_finite (fun a ↦ by split_ifs <;> simp)
      · simp_rw [tsum_fintype]
        apply Summable.of_nonneg_of_le
          (f := fun x ↦ ∑ y : ↑(P.centers ∩ D), |(f (x.val - y.val)).re|)
        · exact fun b ↦ Fintype.sum_nonneg (by rw [Pi.le_def]; simp)
        · exact fun b ↦ Finset.sum_le_sum (fun x hx ↦ by split_ifs <;> simp)
        · exact summable_sum fun y hy ↦ (hsummable₁ y.val).abs
    · apply summable_of_finite_support
      apply Set.Finite.subset (s := { x : ↑P.centers | x.val ∈ D })
      · refine Set.Finite.of_finite_image (f := Subtype.val) ?_ (by simp)
        · conv =>
            arg 1
            equals (P.centers ∩ D) => ext a; rw [Set.inter_comm]; simp
          exact (P.centers ∩ D).toFinite
      · intro x hx
        simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hx
        simp [hx.1]
  _ ≤ ∑' (x : ↑(P.centers ∩ D)), (f 0).re := by
    rw [← tsub_nonpos, add_sub_cancel_right]
    refine tsum_nonpos <| fun x ↦ tsum_nonpos fun y ↦ ?_
    cases eq_or_ne (x.val - y.val) 0
    · case inl h =>
      simp only [h, ↓reduceDIte, le_refl]
    · case inr h =>
      simp only [h, ↓reduceDIte]
      apply hCohnElkies₁ (x - y)
      -- Both `x` and `y` are in `P.centers` and are distinct. `hP` then implies the result.
      rw [← hP]
      exact P.centers_dist' _ _ x.prop (Subtype.mem y).1 (sub_ne_zero.mp h)
  _ = (P.numReps' hd hD_isBounded) * (f 0).re := by
    simp only [tsum_const, nsmul_eq_mul, mul_eq_mul_right_iff, Nat.cast_inj]
    cases eq_or_ne (f 0).re 0
    · case inl h =>
        simp [h]
    · case inr h =>
        left
        let myInstFintype := P.instFintypeNumReps' hd hD_isBounded
        rw [PeriodicSpherePacking.numReps']
        exact Nat.card_eq_fintype_card

include hD_isBounded in
lemma calc_steps' (hd : 0 < d) :
    ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : ↥P.lattice), (f (↑x - ↑y + ↑ℓ)).re =
    (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : ↥P.lattice), f (↑x - ↑y + ↑ℓ)).re := by
  let myInstFintype := P.instFintypeNumReps' hd hD_isBounded
  simp_rw [re_tsum Summable.of_finite]
  refine tsum_congr <| fun x ↦ tsum_congr (fun y ↦ ?_)
  rw [re_tsum]
  have := f.summableOn (Set.range (fun ℓ : P.lattice ↦ ℓ.val + (x - y)))
    (by
      obtain ⟨ε, hε_pos, _⟩ := ZLattice.isSeparated P.lattice
      use ε, hε_pos
      exact fun x hx y hy hxy ↦ by aesop)
  convert this.comp_injective
    (show (fun ℓ : P.lattice => ⟨ℓ.val + (x - y), Set.mem_range_self ℓ⟩).Injective
    from fun a b h => by simpa using congr_arg Subtype.val h) using 1
  exact funext fun _ => by simp [add_comm]

lemma hunion_lemma_1
  (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
  (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ P.centers) :
    ∃ y ∈ P.centers ∩ D, ∃ ℓ ∈ P.lattice, x = y + ℓ := by
      obtain ⟨g, hg₁, hg₂⟩ := hD_unique_covers x
      refine ⟨g +ᵥ x, ?_, -g, ?_⟩ <;> simp_all
      · convert P.lattice_action g.2 hx using 1
      · ext; simp [add_comm]; exact eq_neg_add_of_add_eq rfl

lemma hunion_corrected (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    [Fintype ↑(P.centers ∩ D)] :
    P.centers = ⋃ x ∈ (P.centers ∩ D).toFinset, x +ᵥ SetLike.coe P.lattice := by
  refine Set.ext (fun x ↦ ?_)
  simp [Set.mem_iUnion, Set.mem_vadd_set]
  constructor
  · intro hx
    obtain ⟨y, hyD, hy⟩ := hunion_lemma_1 hD_unique_covers x hx
    use y
    aesop
  · rintro ⟨y, ⟨hy₁, hy₂⟩, z, hz₁, rfl⟩
    exact P.lattice_action hz₁ hy₁ |> fun h ↦ by simpa [add_comm] using h

include hD_unique_covers in
lemma pairwise_disj [Fintype ↑(P.centers ∩ D)] :
    (SetLike.coe (P.centers ∩ D).toFinset).Pairwise
    (Disjoint.onFun  fun x ↦ x +ᵥ SetLike.coe P.lattice) := by
  intro x hx y hy hxy
  simp_all [Set.disjoint_left]
  rintro z ⟨ g, hg, rfl ⟩ ⟨ h, hh, hz ⟩
  have h_diff : (⟨g - h, Submodule.sub_mem _ hg hh⟩ : P.lattice) +ᵥ x = y := by
    have hy_eq : y = x + g - h := eq_sub_of_add_eq hz
    simp_all [add_comm, add_left_comm, add_assoc, sub_eq_add_neg, vadd_eq_add]
    exact add_comm _ _
  have h_zero : (⟨g - h, Submodule.sub_mem _ hg hh⟩ : P.lattice) = 0 :=
    (hD_unique_covers x).unique (by aesop) (by aesop)
  generalize_proofs at *
  simp_all

variable (P) in
noncomputable def eq₁ (y : EuclideanSpace ℝ (Fin d)) :
    ↥P.lattice ≃ ↑(y +ᵥ (SetLike.coe P.lattice)) :=
  {
    toFun := fun x ↦ ⟨y + x, by simp [Set.mem_vadd_set]⟩,
    invFun := fun z ↦ ⟨z - y, by
        obtain ⟨ℓ, hℓ⟩ : ∃ ℓ ∈ P.lattice, z = y + ℓ := by
          obtain ⟨ℓ, hℓ⟩ := z.2
          use ℓ
          aesop
        rw [hℓ.right]
        simp [hℓ.left]⟩,
    left_inv := by simp [Function.LeftInverse]
    right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  }

lemma hsummable₈ [Fintype ↑(P.centers ∩ D)]
    (y i : EuclideanSpace ℝ (Fin d)) (hi : i ∈ (P.centers ∩ D).toFinset) :
    Summable (fun (x : ↑(i +ᵥ (SetLike.coe P.lattice))) ↦ (f (x.val - y)).re) := by
  have h_summable_shifted : Summable (fun (x_1 : P.lattice) ↦ (f (x_1 + i - y)).re) := by
    convert f.summableOn (Set.range (fun x_1 : P.lattice ↦ x_1.val + i - y)) using 1
    constructor <;> intro h
    · exact SchwartzMap.summableOn _ _
    · have h_summable_shifted :
        Summable fun (x_1 : P.lattice) ↦ f (x_1 + i - y) := by
        convert f.summableOn (Set.range (fun x_1 : P.lattice ↦ x_1.val + i - y)) using 1
        constructor <;> intro h
        · assumption
        · convert h _ |> Summable.comp_injective <| show
            (fun x_1 : P.lattice ↦ ⟨x_1.val + i - y, Set.mem_range_self x_1⟩ :
              P.lattice → Set.range (fun x_1 : P.lattice ↦
                x_1.val + i - y)).Injective from fun x y hxy => by aesop
          obtain ⟨ε, ε_pos, hε⟩ := ZLattice.isSeparated P.lattice
          use ε, ε_pos
          intro x hx y hy
          aesop
      convert h_summable_shifted.re using 1
  convert h_summable_shifted.comp_injective (show
    (fun x : { x : EuclideanSpace ℝ (Fin d) // x ∈ i +ᵥ (SetLike.coe P.lattice) } ↦
        ⟨ x.val - i, by
      obtain ⟨y, hy⟩ : ∃ y ∈ P.lattice, x.val = y + i := by
        rcases x with ⟨x, hx⟩; rcases hx with ⟨y, hy, rfl⟩
        exact ⟨y, hy, by simp [add_comm]⟩
      generalize_proofs at *; simp [hy.2, hy.1 ]⟩ :
        { x // x ∈ i +ᵥ (SetLike.coe P.lattice) } → P.lattice).Injective from ?_ ) using 1
  all_goals generalize_proofs at *
  · ext; simp
  · exact fun x y hxy => Subtype.ext <| by simpa using congr_arg Subtype.val hxy

include hD_isBounded hD_unique_covers in
private theorem calc_steps_aux_1 (hd : 0 < d) :
    ∑' (x : ↑P.centers) (y : ↑(P.centers ∩ D)), (f (↑x - ↑y)).re =
    ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : ↥P.lattice),
      (f (↑x - ↑y + ↑ℓ)).re := by
  let myInstFintype := P.instFintypeNumReps' hd hD_isBounded
  simp [tsum_fintype]
  rw [Summable.tsum_finsetSum (fun i hi ↦ hsummable₁ _), Finset.sum_comm]
  congr with x
  rw [tsum_congr_set_coe (fun b ↦ (f (b - x.val)).re) (hunion_corrected hD_unique_covers),
    Summable.tsum_finset_bUnion_disjoint (f := fun b ↦ (f (b - x.val)).re)
      (pairwise_disj hD_unique_covers) (fun i hi ↦ by
        simp [Function.comp_def]; exact hsummable₈ _ _ hi), ← Finset.sum_set_coe]
  congr with y
  rw [← (eq₁ P y.val).tsum_eq]
  simp [eq₁]
  congr! 4 with ℓ
  exact add_sub_right_comm _ _ _

/-- If a lattice has a bounded fundamental domain (or just a bounded set whose translates
    cover the space), then the lattice spans the whole space. -/
lemma lattice_span_eq_top {d : ℕ} {P : PeriodicSpherePacking d}
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : Bornology.IsBounded D)
    (hD_covers : ∀ x, ∃ g : P.lattice, g +ᵥ x ∈ D) :
    span ℝ (SetLike.coe P.lattice) = ⊤ := by
  by_contra h_not_span
  obtain ⟨y, hy⟩ : ∃ y : EuclideanSpace ℝ (Fin d),
    y ∉ span ℝ (SetLike.coe P.lattice) := by
    simpa [eq_top_iff'] using h_not_span
  set S := span ℝ (SetLike.coe P.lattice) with hS_def
  obtain ⟨R, hR_pos, hR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ x ∈ D, ‖x‖ ≤ R := by
    rcases hD_isBounded.exists_pos_norm_le with ⟨R, hR⟩; use Max.max R 1; aesop
  obtain ⟨z, hz⟩ : ∃ z : EuclideanSpace ℝ (Fin d), z ∈ S.orthogonal ∧ ‖z‖ > R := by
    obtain ⟨z, hz_perp, hz_norm⟩ :
      ∃ z : EuclideanSpace ℝ (Fin d), z ∈ S.orthogonal ∧ z ≠ 0 := by
      exact Submodule.ne_bot_iff _ |>.1 (show Sᗮ ≠ ⊥ from fun h => h_not_span <| by
        rw [orthogonal_eq_bot_iff] at h; aesop) |> fun ⟨z, hz⟩ ↦ ⟨z, hz.1, hz.2⟩
    exact ⟨(R / ‖z‖ + 1) • z, smul_mem _ _ hz_perp, by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      nlinarith [ norm_pos_iff.mpr hz_norm, div_mul_cancel₀ R
        (norm_ne_zero_iff.mpr hz_norm)]⟩
  obtain ⟨g, hg⟩ : ∃ g : EuclideanSpace ℝ (Fin d), g ∈ S ∧ g +ᵥ z ∈ D := by
    exact (hD_covers z).elim fun g hg ↦ ⟨g, subset_span g.2, hg⟩
  have h_norm_sq : ‖g +ᵥ z‖^2 = ‖g‖^2 + ‖z‖^2 := by
    simp_all [mem_orthogonal', norm_add_sq_real]
    simpa [real_inner_comm] using hz.1 g hg.1
  nlinarith [hR _ hg.2, norm_nonneg (g +ᵥ z), norm_nonneg g, norm_nonneg z]

lemma dual_eq_span_of_basis {d : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ b : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)),
      BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) L = span ℤ (Set.range b) := by
  have h_basis : ∃ (b : Basis (Fin d) ℤ L),
      span ℤ (Set.range (b.ofZLatticeBasis ℝ L)) = L := by
    have h_basis : ∃ (b : Basis (Fin d) ℤ L), True := by
      have h_basis : finrank ℤ L = d := by
        convert ZLattice.rank ℝ L; norm_num [finrank_pi]
      have h_basis : ∃ (b : Basis (Fin (finrank ℤ L)) ℤ L), True := by
        simp +zetaDelta at *; exact ⟨finBasis ℤ L⟩
      aesop
    exact ⟨h_basis.choose, h_basis.choose.ofZLatticeBasis_span ℝ L⟩
  obtain ⟨b, hb⟩ := h_basis
  convert BilinForm.dualSubmodule_span_of_basis (innerₗ (EuclideanSpace ℝ (Fin d))) _ _
  any_goals exact b.ofZLatticeBasis ℝ L
  any_goals try infer_instance
  · convert Iff.rfl
    rw [hb]
    constructor
    · exact fun h ↦ ⟨_, h⟩
    intro h
    convert BilinForm.dualSubmodule_span_of_basis (innerₗ (EuclideanSpace ℝ (Fin d))) ?_ ?_
    · exact hb.symm
    · infer_instance
  · exact fun x hx ↦ inner_self_eq_zero.mp (hx x)

lemma one : ∃ ε > 0, IsSeparated ε
    (SetLike.coe (BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) := by
  obtain ⟨b, hb⟩ : ∃ b : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)),
      (BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice) =
      span ℤ (Set.range b) := by
    convert dual_eq_span_of_basis P.lattice using 1
  have h_dual_separated : ∃ ε > 0,
      IsSeparated ε (SetLike.coe (span ℤ (Set.range b))) := by
    convert ZLattice.isSeparated (span ℤ (Set.range b)) using 1
  grind

lemma hsummable₆ (i : ↑(P.centers ∩ D)) [Fintype ↑(P.centers ∩ D)] :
    Summable fun (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) ↦
    ∑ x_1 : ↑(P.centers ∩ D), (𝓕 f m).re *
    cexp (2 * π * I * ⟪i.val.ofLp - x_1.val.ofLp, m.val.ofLp⟫_[ℝ]) := by
  simp_rw [← Finset.mul_sum]
  apply Summable.of_norm
  simp
  apply Summable.of_nonneg_of_le
  rotate_right
  · exact fun m ↦ |(𝓕 f m).re| * Nat.card ((P.centers ∩ D).toFinset)
  · exact fun b ↦ mul_nonneg (abs_nonneg _) (norm_nonneg _)
  · intro b
    gcongr
    simp
    convert norm_sum_le _ _ using 2
    norm_num [Complex.norm_exp]
    convert Nat.card_eq_fintype_card using 1
  · exact ((𝓕 f).summableOn _ one).re.norm.mul_right _

include hCohnElkies₂ hD_isBounded in
lemma hsummable₃ (hd : d > 0) :
    Summable (fun (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) ↦
    (𝓕 ⇑f m).re *
    (norm (∑' x : ↑(P.centers ∩ D), exp (2 * π * I * ⟪x.val, m.val.ofLp⟫_[ℝ])) ^ 2)) := by
  let myInstFintype := P.instFintypeNumReps' hd hD_isBounded
  apply Summable.of_norm
  simp
  apply Summable.of_nonneg_of_le
  rotate_right
  · exact fun m ↦ |(𝓕 f m.1).re| * (Nat.card ((P.centers ∩ D).toFinset)) ^ 2
  · exact fun b ↦ mul_nonneg (abs_nonneg _) (sq_nonneg _)
  · intro b
    gcongr
    · exact hCohnElkies₂ b
    · rw[Complex.le_def]; exact ⟨le_rfl, rfl⟩
    · refine le_trans (norm_sum_le _ _) ?_
      norm_num [Complex.norm_exp]
      rw [← Nat.card_eq_fintype_card]
      exact le_rfl
  · exact ((𝓕 f).summableOn _ one).re.norm.mul_right _

lemma hsummable₇ {i : ↑(P.centers ∩ D)} (x_1 : ↑(P.centers ∩ D)) : Summable fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) ↦
    (𝓕 f m).re *
    cexp (2 * π * I * ⟪i.val.ofLp - x_1.val.ofLp, m.val.ofLp⟫_[ℝ]) :=
  Summable.of_norm <| Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _)
    (fun m ↦ by simp [Complex.norm_exp]) (((𝓕 f).summableOn _ one).re.norm)

include hD_isBounded hCohnElkies₂ in
lemma hsummable₅ (hd : d > 0) : Summable
    fun (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) ↦
    (𝓕 f m).re * (normSq (∑' (x : ↑(P.centers ∩ D)),
    cexp (2 * (π * (I * ⟪x.val.ofLp, m.val.ofLp⟫_[ℝ])))) : ℂ) := by
  let myInstFintype := P.instFintypeNumReps' hd hD_isBounded
  convert Complex.ofRealCLM.summable <| hsummable₃ hCohnElkies₂ hD_isBounded hd using 2
  norm_num [Complex.normSq_eq_norm_sq]; ring_nf!

include hP hD_isBounded hD_unique_covers hRealFourier hCohnElkies₁ hCohnElkies₂ in
private theorem calc_steps (hd : 0 < d) :
    (P.numReps' hd hD_isBounded) * (f 0).re ≥ (P.numReps' hd hD_isBounded) ^ 2 *
    (𝓕 f 0).re / ZLattice.covolume P.lattice := by
  have : Fact (0 < d) := ⟨hd⟩
  calc (P.numReps' hd hD_isBounded) * (f 0).re
  _ ≥ ∑' (x : P.centers) (y : ↑(P.centers ∩ D)), (f (x - ↑y)).re := by
    simpa [ge_iff_le] using calc_aux_1 hCohnElkies₁ hP hD_isBounded hd
  _ = ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice), (f (↑x - ↑y + ↑ℓ)).re :=
    calc_steps_aux_1 hD_isBounded hD_unique_covers hd
  -- We now take the real part out so we can apply the PSF-L to the stuff inside.
  -- The idea would be to say, in subsequent lines, that "it suffices to show that the numbers
  -- whose real parts we're taking are equal as complex numbers" and then apply the PSF-L and
  -- other complex-valued stuff.
  _ = (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice), f (↑x - ↑y + ↑ℓ)).re :=
    calc_steps' hD_isBounded hd
  _ = (∑' x : ↑(P.centers ∩ D), ∑' y : ↑(P.centers ∩ D), (1 / ZLattice.covolume P.lattice) *
      ∑' m : BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice, (𝓕 f m) *
      exp (2 * π * I * ⟪↑x - ↑y, m.val⟫_[ℝ])).re := by
    congr! 5 with x y
    exact f.PoissonSummation_Lattices P.lattice _
  _ = ((1 / ZLattice.covolume P.lattice) *
      ∑' m : BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice,
      (𝓕 f m).re * ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
      exp (2 * π * I * ⟪x.val - y.val, m.val⟫_[ℝ])).re := by
    apply congrArg re
    simp only [tsum_mul_left]
    apply congrArg _ _
    simp only [← tsum_mul_left]
    let myInstFintype := P.instFintypeNumReps' hd hD_isBounded
    simp [tsum_fintype]
    rw [Summable.tsum_finsetSum (fun i hi ↦ hsummable₆ i)]
    simp_rw [Summable.tsum_finsetSum (fun x_1 hx_1 ↦ hsummable₇ x_1)]
    congr! 4 with x hx y hy m
    simp [hRealFourier m]
  _ = ((1 / ZLattice.covolume P.lattice) *
      ∑' m : BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice, (𝓕 f m).re * (
      ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
      exp (2 * π * I * ⟪x.val, (m.val).ofLp⟫_[ℝ]) *
      exp (2 * π * I * ⟪-y.val, (m.val).ofLp⟫_[ℝ]))).re := by
    congr! 9 with m x y
    simp [sub_eq_neg_add, RCLike.wInner_neg_left, ofReal_neg, mul_neg, mul_comm]
    rw [RCLike.wInner_add_left]
    simp only [RCLike.wInner_neg_left, ofReal_add, ofReal_neg]
    rw [mul_add, Complex.exp_add, mul_comm]
    simp
  _ = ((1 / ZLattice.covolume P.lattice) *
      ∑' m : BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice,
      (𝓕 f m).re * (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪x.val, (m.val).ofLp⟫_[ℝ])) *
      (∑' y : ↑(P.centers ∩ D),
      exp (-(2 * π * I * ⟪y.val, (m.val).ofLp⟫_[ℝ])))).re := by
    simp_rw [mul_assoc, ← tsum_mul_right, ← tsum_mul_left]
    congr! 9 with m x y
    simp [RCLike.wInner_neg_left, ofReal_neg, mul_neg]
  _ = ((1 / ZLattice.covolume P.lattice) *
      ∑' m : BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice, (𝓕 f
      m).re *
      (∑' x : ↑(P.centers ∩ D), exp (2 * π * I * ⟪x.val, (m.val).ofLp⟫_[ℝ])) *
      conj (∑' x : ↑(P.centers ∩ D), exp (2 * π * I * ⟪x.val, (m.val).ofLp⟫_[ℝ]))).re := by
    simp_rw [conj_tsum]
    congr! 7 with m x
    exact exp_neg_real_I_eq_conj x.val m
  _ = (1 / ZLattice.covolume P.lattice) *
      ∑' m : BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice,
      (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪x.val, (m.val).ofLp⟫_[ℝ])) ^ 2) := by
    simp_rw [← normSq_eq_norm_sq, mul_assoc, mul_conj, ← ofReal_one, ← ofReal_div,
      re_ofReal_mul]
    congr
    simp [re_tsum <| hsummable₅ hCohnElkies₂ hD_isBounded hd]
    congr with m
  -- We split the sum up into the `m = 0` and `m ≠ 0` parts.
  _ = (1 / ZLattice.covolume P.lattice) * (
      (∑' (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)),
        if hm : m = 0 then 0
        else (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) +
      (𝓕 ⇑f 0).re * (norm (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) := by
    let myInstFintype := P.instFintypeNumReps' hd hD_isBounded
    apply congrArg _ _
    rw [add_comm, (hsummable₃ hCohnElkies₂ hD_isBounded hd).tsum_eq_add_tsum_ite 0]
    simp only [ZeroMemClass.coe_zero, dite_eq_ite]
  _ ≥ (1 / ZLattice.covolume P.lattice) * (𝓕 ⇑f 0).re * (norm (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2) := by
    -- We need to show that the `m ≠ 0` part is nonpositive.
    -- We begin by subtracting both sides, and thereby, isolating the `m ≠ 0` part.
    rw [ge_iff_le, ← tsub_nonpos, mul_assoc,
      ← mul_sub (1 / ZLattice.covolume P.lattice volume) _ _]
    simp only [dite_eq_ite, sub_add_cancel_right, mul_neg, Left.neg_nonpos_iff]
    -- We now get rid of the `1 / ZLattice.covolume P.lattice volume` factor.
    apply mul_nonneg (one_div_nonneg.mpr (by simp [ZLattice.covolume]))
    refine tsum_nonneg <| fun m ↦ ?_
    cases eq_or_ne m 0
    · case inl h =>
        simp only [h, ↓reduceIte, le_refl]
    · case inr h =>
        simp only [h, ↓reduceIte]
        exact mul_nonneg (by rw [← ge_iff_le]; exact hCohnElkies₂ m) (sq_nonneg _)
  _ = (1 / ZLattice.covolume P.lattice) * (𝓕 ⇑f 0).re * ↑(P.numReps' hd hD_isBounded) ^ 2 := by
    apply congrArg _ _
    let myInstFintype := P.instFintypeNumReps' hd hD_isBounded
    simp [PeriodicSpherePacking.numReps', RCLike.wInner_zero_right, ofReal_zero,
      mul_zero, Complex.exp_zero, nsmul_eq_mul, mul_one]
  _ = ↑(P.numReps' hd hD_isBounded) ^ 2 * (𝓕 ⇑f 0).re / ZLattice.covolume P.lattice volume := by
    simp only [div_eq_mul_inv, mul_comm, one_mul, ← mul_assoc]

end Fundamental_Domain_Dependent


section Main_Theorem_For_One_Packing

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)

/-
In this section, we will prove that the density of every periodic sphere packing of separation 1 is
bounded above by the Cohn-Elkies bound.
-/

include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ P hP D hD_isBounded
  hD_unique_covers

theorem LinearProgrammingBound' (hd : 0 < d) :
    P.density ≤ (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal *
    volume (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  have : Fact (0 < d) := ⟨hd⟩
  rw [P.density_eq' hd]
  suffices hCalc : (P.numReps' hd hD_isBounded) * (f 0).re ≥
      (P.numReps' hd hD_isBounded)^2 * (𝓕 f 0).re / ZLattice.covolume P.lattice by
    rw [hP]
    rw [ge_iff_le] at hCalc
    have vol_pos := EuclideanSpace.volume_ball_pos (0 : EuclideanSpace ℝ (Fin d)) one_half_pos
    have vol_ne_top : volume (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≠ ∞ := by
      rw [← lt_top_iff_ne_top]
      exact EuclideanSpace.volume_ball_lt_top 0
    cases eq_or_ne (𝓕 f 0) 0
    · case inl h𝓕f =>
      rw [h𝓕f, zero_re]
      -- For `ENNReal.div_zero`, we need `f 0 ≠ 0`. This can be deduced from the fact that
      -- `𝓕 f ≥ 0` and `f ≠ 0`.
      have ne_zero_at_zero : ((f 0).re.toNNReal : ENNReal) ≠ 0 :=
        ENNReal.coe_ne_zero.mpr (ne_of_lt (toNNReal_pos.mpr
        (f_zero_pos hne_zero hReal hRealFourier hCohnElkies₂))).symm
      -- Now we can safely divide by zero!
      rw [ENat.toENNReal_coe, toNNReal_zero, ENNReal.coe_zero, ENNReal.div_zero ne_zero_at_zero]
      -- We now need to multiply by ⊤.
      rw [ENNReal.top_mul (ne_of_lt vol_pos).symm]
      exact le_top
    · case inr h𝓕f =>
      -- First, we shift things around and cancel volumes on the right
      rw [ENat.toENNReal_coe, mul_div_assoc, div_eq_mul_inv (volume _), mul_comm (volume _),
          ← mul_assoc, ENNReal.mul_le_mul_iff_left (ne_of_lt vol_pos).symm vol_ne_top]
      -- Next, we simplify `hCalc` by replacing `numReps'` with `numReps`
      rw [← P.numReps_eq_numReps' Fact.out hD_isBounded hD_unique_covers] at hCalc
      -- Next, we multiply both sides by `(𝓕 (⇑f) 0).re.toNNReal`, cancelling accordingly.
      have hfouaux₁ : ((𝓕 f 0).re.toNNReal : ENNReal) ≠ 0 := by
        intro hContra
        apply h𝓕f
        simp only [ENNReal.coe_eq_zero, toNNReal_eq_zero] at hContra
        specialize hCohnElkies₂ 0
        rw [ge_iff_le] at hCohnElkies₂
        -- We can't simply do antisymm because we have an equality in ℂ, not ℝ!
        rw [← re_add_im (𝓕 f 0), le_antisymm hContra hCohnElkies₂,
            hFourierImZero hRealFourier 0, ofReal_zero, zero_mul, add_zero]
      have hfouaux₂ : ((𝓕 f 0).re.toNNReal : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      rw [← ENNReal.mul_le_mul_iff_left hfouaux₁ hfouaux₂,
          div_eq_mul_inv ((f 0).re.toNNReal : ENNReal) _,
          mul_assoc ((f 0).re.toNNReal : ENNReal) _ _, ENNReal.inv_mul_cancel hfouaux₁ hfouaux₂]
      -- We put it in a more desirable form and consolidate.
      rw [mul_one, mul_assoc, ← ENNReal.div_eq_inv_mul]
      -- Next, we multiply both sides on the left by `↑P.numReps`.
      have hnRaux₁ : ENat.toENNReal (P.numReps : ENat) ≠ 0 := by
        rw [ENat.toENNReal_coe, ne_eq, Nat.cast_eq_zero, ← ne_eq]
        unfold PeriodicSpherePacking.numReps
        haveI : Nonempty (Quotient (AddAction.orbitRel ↥P.lattice ↑P.centers)) := by
          rw [nonempty_quotient_iff]
          assumption
        exact Fintype.card_ne_zero
      rw [← ENNReal.mul_le_mul_iff_right hnRaux₁ (ne_of_beq_false rfl).symm]
      -- We put it in a more desirable form and consolidate.
      rw [ENat.toENNReal_coe, ← mul_assoc, ← pow_two, ← mul_div_assoc]
      -- Now, we use the nonnegativity of... everything... to get the `toNNReal`s to the outside.
      have hRHSCast : (P.numReps : ENNReal) * (f 0).re.toNNReal =
          (P.numReps * (f 0).re).toNNReal := by
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
        have haux₁ : 0 ≤ P.numReps ^ 2 * (𝓕 f 0).re * (ZLattice.covolume P.lattice volume)⁻¹ := by
          refine mul_nonneg (mul_nonneg (sq_nonneg _) (hCohnElkies₂ 0)) ?_
          exact inv_nonneg.1 <| LT.lt.le (by simp [ZLattice.covolume_pos])
        rw [Real.toNNReal_of_nonneg haux₁,
          ← ENNReal.coe_inv <| LT.lt.ne' (by simp [ZLattice.covolume_pos])]
        norm_cast
        rw [Real.toNNReal_of_nonneg (hCohnElkies₂ 0),
            Real.toNNReal_of_nonneg (LT.lt.le (ZLattice.covolume_pos P.lattice volume))]
        exact NNReal.eq (by push_cast; rfl)
      -- We can now get rid of the `toNNReal`s and use `hCalc` to finish the proof!
      rw [hRHSCast, hLHSCast, ENNReal.coe_le_coe]
      exact Real.toNNReal_le_toNNReal hCalc
  exact calc_steps hRealFourier hCohnElkies₁ hCohnElkies₂ hP hD_isBounded hD_unique_covers hd

end Main_Theorem_For_One_Packing

section Main_Theorem

include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂

theorem LinearProgrammingBound (hd : 0 < d) :
  SpherePackingConstant d ≤ (f 0).re.toNNReal / (𝓕 ⇑f 0).re.toNNReal *
    volume (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  rw [← periodic_constant_eq_constant hd,
    periodic_constant_eq_periodic_constant_normalized hd]
  refine iSup_le (fun P ↦ ?_)
  rw [iSup_le_iff]
  intro hP
  cases isEmpty_or_nonempty P.centers
  · case inl instEmpty =>
      rw [P.density_of_centers_empty hd]
      exact zero_le _
  · case inr instNonempty =>
      let b := (ZLattice.module_free ℝ P.lattice).chooseBasis.reindex P.basis_index_equiv
      exact LinearProgrammingBound' hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP
        (fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ P.lattice))
        (P.fundamental_domain_unique_covers b) hd

end Main_Theorem
