/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
import Mathlib.Logic.IsEmpty
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Pointwise.Support
import Mathlib.Topology.MetricSpace.MetricSeparated

import SpherePacking.CohnElkies.Prereqs
import SpherePacking.ForMathlib.VolumeOfBalls
import SpherePacking.Basic.PeriodicPacking

open scoped FourierTransform ENNReal SchwartzMap InnerProductSpace Pointwise BigOperators
open SpherePacking Metric BigOperators Pointwise Filter MeasureTheory Complex Real ZSpan
  Bornology Summable Module LinearMap SchwartzMap

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
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
-- let `𝓕 f` be real-valued:
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
-- moreover, impose the Cohn-Elkies conditions:
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)

-- let `conj z` denote the complex conjugate of a complex number `z`:
local notation "conj" => starRingEnd ℂ

section Complex_Function_Helpers

/-- If the real part of a function is equal to the function itself,
    then its imaginary part is zero. -/
private theorem helper (g : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d))
    (hg : (g x).re = g x) : (g x).im = 0 := by
  rw [← hg, ofReal_im]

include hReal in
/-- The imaginary part of `f` is zero everywhere. -/
private theorem hImZero (x : EuclideanSpace ℝ (Fin d)) : (f x).im = 0 :=
  helper f x (hReal x)

include hRealFourier in
/-- The imaginary part of `𝓕 f` is zero everywhere. -/
private theorem hFourierImZero (x : EuclideanSpace ℝ (Fin d)) : (𝓕 f x).im = 0 :=
  helper (𝓕 ⇑f) x (hRealFourier x)

end Complex_Function_Helpers


section Nonnegativity

/-- The Fourier transform of a Schwartz function is non-zero if the function is non-zero. -/
theorem fourier_ne_zero (hne_zero : f ≠ 0) : 𝓕 f ≠ 0 := by
  intro hfourier_zero
  apply hne_zero
  rw [← ContinuousLinearEquiv.map_eq_zero_iff <|
    FourierTransform.fourierCLE ℝ (𝓢(EuclideanSpace ℝ (Fin d), ℂ))]
  exact hfourier_zero

include hCohnElkies₂ in
/-- If the real part of the Fourier transform `𝓕 f` is nonnegative everywhere,
    then the real part of `f` at zero is nonnegative. -/
theorem f_nonneg_at_zero : 0 ≤ (f 0).re := by
  rw [← f.fourierInversion ℝ, fourierInv_eq]
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul]
  have hcalc₁ :
    (∫ (v : EuclideanSpace ℝ (Fin d)), 𝓕 (⇑f) v).re =
    ∫ (v : EuclideanSpace ℝ (Fin d)), (𝓕 (⇑f) v).re := by
    rw [← RCLike.re_eq_complex_re, ← integral_re (𝓕 f).integrable]
  rw [hcalc₁]
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
  rw [← re_add_im (f 0), hImZero hReal, ofReal_zero, zero_mul, add_zero] at haux₁
  -- We need to take real and imaginary parts inside the integral.
  have haux₂ : ∫ (v : EuclideanSpace ℝ (Fin d)), 𝓕 (⇑f) v =
    ∫ (v : EuclideanSpace ℝ (Fin d)), (𝓕 (⇑f) v).re :=
    calc ∫ (v : EuclideanSpace ℝ (Fin d)), 𝓕 (⇑f) v
    _ = ↑(∫ (v : EuclideanSpace ℝ (Fin d)), (𝓕 (⇑f) v).re) +
    (∫ (v : EuclideanSpace ℝ (Fin d)), (𝓕 (⇑f) v).im) * I
      := by
         rw [← re_add_im (∫ (v : EuclideanSpace ℝ (Fin d)), 𝓕 (⇑f) v)]
         rw [← RCLike.re_eq_complex_re, ← integral_re (𝓕 f).integrable, RCLike.re_eq_complex_re]
         rw [← RCLike.im_eq_complex_im, ← integral_im (𝓕 f).integrable, RCLike.im_eq_complex_im]
    _ = ∫ (v : EuclideanSpace ℝ (Fin d)), (𝓕 (⇑f) v).re
      := by
         rw [add_eq_left]
         suffices hwhat : ∀ v : EuclideanSpace ℝ (Fin d), (𝓕 (⇑f) v).im = 0 by
           simp only [hwhat, ofReal_zero, zero_mul, integral_zero]
         exact hFourierImZero hRealFourier
  rw [haux₂] at haux₁
  norm_cast at haux₁
  rw [haux₁, lt_iff_not_ge]
  by_contra hantisymm₁
  have hantisymm₂ : 0 ≤ ∫ (v : EuclideanSpace ℝ (Fin d)), (𝓕 (⇑f) v).re := integral_nonneg
    hCohnElkies₂
  have hintzero : 0 = ∫ (v : EuclideanSpace ℝ (Fin d)), (𝓕 (⇑f) v).re := by
    --rw [ge_iff_le] at hantisymm₁
    exact antisymm' hantisymm₁ hantisymm₂
  have h𝓕frezero : ∀ x, (𝓕 ⇑f x).re = 0 := by
    -- Integral of a nonneg continuous function is zero iff the function is zero
    suffices hfun : (fun x => (𝓕 ⇑f x).re) = 0 by
      intro x
      calc (𝓕 (⇑f) x).re
      _ = (fun x => (𝓕 ⇑f x).re) x := rfl
      _ = (0 : (EuclideanSpace ℝ (Fin d)) → ℝ) x := by rw [hfun]
      _ = 0 := by rw [Pi.zero_apply]
    refine (Continuous.integral_zero_iff_zero_of_nonneg (𝓕 f).continuous.re
      ?_ hCohnElkies₂).mp hintzero.symm
    rw [← RCLike.re_eq_complex_re]
    refine MeasureTheory.Integrable.re (𝓕 f).integrable
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

/- We start with auxiliary lemmata about summability of certain functions which will be
    used in the arguments below. -/

lemma hsummable₁ (y : EuclideanSpace ℝ (Fin d)) :
    Summable fun (b : P.centers) ↦ (f (b.val - y)).re := by
  -- Since translation by y maps the centers of P to another set of points that are still
  -- separated by at least 1 (because the distance between any two points in P.centers - y
  -- is the same as the distance between the corresponding points in P.centers), the
  -- summability of the translated function should follow from the summability of f over
  -- the original set.
  have h_translated_summable : Summable (fun x : P.centers => f (x - y)) := by
    -- Since $P.centers$ is a separated set and $f$ is a Schwartz function, the series
    -- $\sum_{x \in P.centers} f(x - y)$ converges absolutely.
    have h_translated_summable : IsSeparated (ENNReal.ofReal P.separation) (P.centers - {y}) := by
      have h_translated_summable : IsSeparated (ENNReal.ofReal P.separation) P.centers := by
        exact SpherePacking.centers_isSeparated P.toSpherePacking
      generalize_proofs at *; (
      intro x hx y hy; aesop;);
    have h_translated_summable :
      Summable (fun x : (P.centers - {y} : Set (EuclideanSpace ℝ (Fin d))) => f x) := by
      -- Apply the SchwartzMap.summableOn_iff lemma with the separated set P.centers - {y}
      -- and the positive ε from h_translated_summable.
      apply (SchwartzMap.summableOn_iff f (P.centers - {y})).mpr;
      -- Since $P.separation$ is positive, we can take $\epsilon = P.separation$.
      use ENNReal.ofReal P.separation;
      exact ⟨ ENNReal.ofReal_pos.mpr P.separation_pos, h_translated_summable ⟩;
    convert h_translated_summable.comp_injective
      ( show Function.Injective ( fun x : P.centers =>
        ⟨ x - y, by aesop ⟩ : P.centers →
          ( P.centers - { y } : Set ( EuclideanSpace ℝ ( Fin d ) ) ) ) from
            fun x y hxy => by aesop ) using 1;
  convert h_translated_summable.re using 1

include hP hCohnElkies₁ in
open Classical in
private theorem calc_aux_1 (hd : 0 < d) :
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
                  rw [summable_abs_iff]
                  exact hsummable₁ y.val
            · apply summable_of_finite_support
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

lemma hsummable₄ (P : PeriodicSpherePacking d)
    (x y : EuclideanSpace ℝ (Fin d)) :
    Summable fun (ℓ : ↥P.lattice) ↦ f (x - y + ℓ.val) := by
  have := f.summableOn
    ( Set.range ( fun ℓ : P.lattice => ( ℓ : EuclideanSpace ℝ ( Fin d ) ) + ( x - y ) ) ) (by
  have h_separated : ∃ ε > 0, IsSeparated ε (P.lattice : Set (EuclideanSpace ℝ (Fin d))) := by
    exact ZLattice.isSeparated P.lattice;
  -- Since addition by a constant preserves the separation property, the range of the
  -- function ℓ ↦ ℓ + (x - y) is also separated.
  obtain ⟨ε, hε_pos, hε_sep⟩ := h_separated;
  use ε, hε_pos;
  intro x hx y hy hxy;
  aesop);
  convert this.comp_injective
    ( show Function.Injective ( fun ℓ : P.lattice =>
      ⟨ ( ℓ : EuclideanSpace ℝ ( Fin d ) ) + ( x - y ), Set.mem_range_self ℓ ⟩ )
        from fun a b h => by simpa using congr_arg Subtype.val h ) using 1;
  exact funext fun _ => by simp +decide [ add_comm ];

omit [Nonempty ↑P.centers] in
include hD_isBounded in
lemma calc_steps' (hd : 0 < d) :
    ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : ↥P.lattice), (f (↑x - ↑y + ↑ℓ)).re =
    (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : ↥P.lattice), f (↑x - ↑y + ↑ℓ)).re := by
  have sum_finite := aux4 P D hD_isBounded hd
  rw [re_tsum Summable.of_finite]
  apply tsum_congr
  intro x
  rw [re_tsum Summable.of_finite]
  apply tsum_congr
  intro y
  rw [re_tsum]
  exact hsummable₄ P x.val y.val

  /-
  apply Summable.comp_injective hf
  intro a b
  simp_all-/

-- # NOTE:
-- There are several summability results stated as intermediate `have`s in the following theorem.
-- I think their proofs should follow from whatever we define `PSF_Conditions` to be.
-- If there are assumptions needed beyond PSF, we should require them here, not in `PSF_Conditions`.

/-
Helper lemma: Any center point can be shifted by a lattice vector to land in the
fundamental domain D.
-/
lemma hunion_lemma_1
  (P : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))
  (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
  (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ P.centers) :
    ∃ y ∈ P.centers ∩ D, ∃ ℓ ∈ P.lattice, x = y + ℓ := by
      obtain ⟨ g, hg₁, hg₂ ⟩ := hD_unique_covers x;
      refine ⟨ g +ᵥ x, ?_, -g, ?_ ⟩ <;> simp_all +decide;
      · convert P.lattice_action g.2 hx using 1;
      · ext ; simp +decide [ add_comm ];
        exact eq_neg_add_of_add_eq rfl

/-
The corrected version of hunion, assuming D is a fundamental domain.
-/
lemma hunion_corrected (P : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    [Fintype ↑(P.centers ∩ D)] :
    P.centers = ⋃ (x ∈ (P.centers ∩ D).toFinset),
      (x +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))) := by
      -- Let's first show that the union of the lattice translates of the fundamental
      -- domain covers all centers.
      apply Set.ext
      intro x
      simp [Set.mem_iUnion, Set.mem_vadd_set];
      constructor;
      · intro hx
        obtain ⟨y, hyD, hy⟩ := hunion_lemma_1 P D hD_unique_covers x hx
        use y
        aesop;
      · rintro ⟨ y, ⟨ hy₁, hy₂ ⟩, z, hz₁, rfl ⟩;
        exact P.lattice_action hz₁ hy₁ |> fun h => by simpa [ add_comm ] using h;

lemma pairwise_disj [Fintype ↑(P.centers ∩ D)] :
  ((P.centers ∩ D).toFinset : Set (EuclideanSpace ℝ (Fin d))).Pairwise
  (Function.onFun Disjoint fun x ↦ x +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))) := by sorry

variable (P) in
noncomputable def eq₁ (y : EuclideanSpace ℝ (Fin d)) : ↥P.lattice ≃
    ↑(y +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))) :=
  {
    toFun := fun x ↦ ⟨y + x, by
      -- Since $x$ is in the lattice, adding $y$ to $x$ should still be in the lattice
      --shifted by $y$.
      simp [Set.mem_vadd_set]⟩,
    invFun := fun z ↦ ⟨z - y, by
      -- Since $z$ is in the set $y +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))$, there
      -- exists some $ℓ \in P.lattice$ such that $z = y + ℓ$.
      obtain ⟨ℓ, hℓ⟩ : ∃ ℓ ∈ P.lattice, z = y + ℓ := by
        -- By definition of $y +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))$, if $z \in
        -- y +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))$, then there exists some $ℓ
        -- \in P.lattice$ such that $z = y + ℓ$.
        obtain ⟨ℓ, hℓ⟩ := z.2;
        use ℓ;
        aesop;
      -- Substitute $z = y + ℓ$ into the expression $(z - y)$ and simplify.
      rw [hℓ.right]
      simp [hℓ.left]⟩,
    left_inv := by simp [Function.LeftInverse]
    right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  }

include d f hP hD_isBounded hD_unique_covers hne_zero hReal
  hRealFourier hCohnElkies₁ hCohnElkies₂ in
private theorem calc_steps_aux_1 (hd : 0 < d) :
    ∑' (x : ↑P.centers) (y : ↑(P.centers ∩ D)), (f (↑x - ↑y)).re =
    ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : ↥P.lattice),
      (f (↑x - ↑y + ↑ℓ)).re := by
  have sum_finite := aux4 P D hD_isBounded hd
  have fintype_centers: Fintype ↑(P.centers ∩ D) := by apply Fintype.ofFinite
  simp [tsum_fintype]
  rw [Summable.tsum_finsetSum (fun i hi ↦ hsummable₁ _), Finset.sum_comm]
  congr with x
  rw [tsum_congr_set_coe (fun b ↦ (f (b - x.val)).re) (hunion_corrected P D hD_unique_covers),
    @Summable.tsum_finset_bUnion_disjoint _ _ _ _ (fun b ↦ (f (b - x.val)).re) _
      _ _ _ _ pairwise_disj (fun i hi ↦ by simp [Function.comp_def]; sorry), ← Finset.sum_set_coe]
  congr with y
  rw [← Equiv.tsum_eq (eq₁ P y.val)]
  simp [eq₁]
  congr! 4 with ℓ
  exact add_sub_right_comm _ _ _

lemma hsummable₂ : Summable (Function.uncurry fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice))
    (x : ↑(P.centers ∩ D)) ↦
    ∑' (x_1 : ↑(P.centers ∩ D)), (𝓕 f m).re * exp (2 * π * I *
    ⟪(x.val).ofLp - (x_1.val).ofLp, (m.val).ofLp⟫_[ℝ])) := by
  simp [Function.uncurry_def]
  sorry

omit [Nonempty ↑P.centers] in
lemma hsummable₃ : Summable (fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) =>
      (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪x.val, (m.val).ofLp⟫_[ℝ])) ^ 2)) := by
  have := @SchwartzMap.summableOn_iff;
  contrapose! this;
  refine ⟨ ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_ ⟩;
  · exact 0;
  refine ⟨ Set.univ, Or.inl ⟨ ?_, ?_ ⟩ ⟩ <;> norm_num [ Metric.IsSeparated ];
  · exact summable_zero;
  · intro x hx; rw [ Set.Pairwise ] ; norm_num [ hx ] ;
    rcases x with ( _ | _ | x ) <;> norm_num at hx ⊢;
    · exact ⟨ 0, 1, by norm_num ⟩;
    · refine ⟨ 0, ?_, ?_, ?_ ⟩ <;> norm_num [ hx ];
      · exact { cauchy := Quot.mk ( ⇑CauSeq.equiv ) ‹_› };
      · exact ne_of_lt hx;
      · exact Subtype.mk_le_mk.mpr ( le_of_eq ( abs_of_nonneg <| by assumption ) )

omit [Nonempty ↑P.centers] in
lemma hsummable₅ : Summable
    fun (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) ↦
    (((𝓕 f) ↑m).re : ℂ) * ((normSq (∑' (x : ↑(P.centers ∩ D)),
    cexp (2 * (↑π * (I * ⟪x.val.ofLp, (m.val).ofLp⟫_[ℝ]))))) : ℂ) := by
  -- The series over the dual submodule is summable because it's a Fourier series with a
  --Schwartz function.
  have h_fourier_series : Summable
    (fun m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice) =>
      (𝓕 f m).re * (norm (∑' x : ↥(P.centers ∩ D),
        Complex.exp (2 * Real.pi * Complex.I * ⟪x.val, (m.val).ofLp⟫_[ℝ])) ^ 2)) := by
    -- Apply the hypothesis `hsummable₃` to conclude the proof.
    apply hsummable₃;
  convert Complex.ofRealCLM.summable h_fourier_series using 2 ;
  norm_num [ Complex.normSq_eq_norm_sq ] ; ring_nf!; aesop;

lemma hsummable₆ (i : ↑(P.centers ∩ D)) [Fintype ↑(P.centers ∩ D)] : Summable fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) ↦
    ∑ (x_1 : ↑(P.centers ∩ D)), ↑((𝓕 f) ↑m).re *
    cexp (2 * ↑π * I * ⟪(i.val).ofLp - (x_1.val).ofLp, (m.val).ofLp⟫_[ℝ]) := by
  convert hsummable₂.comp_injective
    ( show Function.Injective ( fun m : ↥ ( LinearMap.BilinForm.dualSubmodule
      ( innerₗ ( EuclideanSpace ℝ ( Fin d ) ) ) P.lattice ) => ( m, i ) ) from ?_ ) using 1;
  rotate_left;
  · exact f;
  · exact fun m n h => by injection h;
  · ext; simp +decide [ Function.comp, tsum_fintype ] ;

lemma hsummable₇ {i : ↑(P.centers ∩ D)} (x_1 : ↑(P.centers ∩ D))
    [Fintype ↑(P.centers ∩ D)] : Summable fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) ↦
    ↑((𝓕 f) ↑m).re *
    cexp (2 * ↑π * I * ⟪(i.val).ofLp - (x_1.val).ofLp, (m.val).ofLp⟫_[ℝ]) := by
  sorry

include d f hP hD_isBounded hD_unique_covers hne_zero hReal hRealFourier
  hCohnElkies₁ hCohnElkies₂ in
private theorem calc_steps (hd : 0 < d) :
    ↑(P.numReps' hd hD_isBounded) * (f 0).re ≥ ↑(P.numReps' hd hD_isBounded) ^ 2 *
    (𝓕 f 0).re / ZLattice.covolume P.lattice := by
  have : Fact (0 < d) := ⟨hd⟩
  calc
  ↑(P.numReps' hd hD_isBounded) * (f 0).re
  _ ≥ ∑' (x : P.centers) (y : ↑(P.centers ∩ D)),
      (f (x - ↑y)).re
        := by
            rw [ge_iff_le]
            exact calc_aux_1 hCohnElkies₁ hP hD_isBounded hd
  _ = ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
      (f (↑x - ↑y + ↑ℓ)).re
        :=
            calc_steps_aux_1 hne_zero hReal hRealFourier
              hCohnElkies₁ hCohnElkies₂ hP hD_isBounded hD_unique_covers hd
  -- We now take the real part out so we can apply the PSF-L to the stuff inside.
  -- The idea would be to say, in subsequent lines, that "it suffices to show that the numbers
  -- whose real parts we're taking are equal as complex numbers" and then apply the PSF-L and
  -- other complex-valued stuff.
  _ = (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
      f (↑x - ↑y + ↑ℓ)).re
        := calc_steps' hD_isBounded hd
  _ = (∑' x : ↑(P.centers ∩ D),
      ∑' y : ↑(P.centers ∩ D), (1 / ZLattice.covolume P.lattice) *
      ∑' m : BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice, (𝓕 f m) *
      exp (2 * π * I * ⟪↑x - ↑y, m.val⟫_[ℝ])).re
        := by
            congr! 5 with x y
            exact SchwartzMap.PoissonSummation_Lattices P.lattice f _
  _ = ((1 / ZLattice.covolume P.lattice) *
      ∑' m : BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice,
      (𝓕 f m).re * (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
      exp (2 * π * I * ⟪x.val - y.val, m.val⟫_[ℝ]))).re
        := by
            apply congrArg re
            simp only [tsum_mul_left]
            apply congrArg _ _
            simp only [← tsum_mul_left]
            have sum_finite := aux4 P D hD_isBounded hd
            have fintype_centers: Fintype ↑(P.centers ∩ D) := by apply Fintype.ofFinite
            simp [tsum_fintype]
            rw [Summable.tsum_finsetSum (fun i hi ↦ hsummable₆ i)]
            simp_rw [Summable.tsum_finsetSum (fun x_1 hx_1 ↦ hsummable₇ x_1)]
            congr! 4 with x hx y hy m
            simp [hRealFourier m]
  _ = ((1 / ZLattice.covolume P.lattice) *
      ∑' m : BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice, (𝓕 f m).re * (
      ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
      exp (2 * π * I * ⟪x.val, (m.val).ofLp⟫_[ℝ]) *
      exp (2 * π * I * ⟪-y.val, (m.val).ofLp⟫_[ℝ]))).re
        := by
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
      exp (-(2 * π * I * ⟪y.val, (m.val).ofLp⟫_[ℝ])))).re
        := by
            simp_rw [mul_assoc, ← tsum_mul_right, ← tsum_mul_left]
            congr! 9 with m x y
            simp [RCLike.wInner_neg_left, ofReal_neg, mul_neg]
  _ = ((1 / ZLattice.covolume P.lattice) *
      ∑' m : BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice, (𝓕 f
      m).re *
      (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪x.val, (m.val).ofLp⟫_[ℝ])) *
      conj (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪x.val, (m.val).ofLp⟫_[ℝ]))
      ).re
        := by
            simp_rw [conj_tsum]
            congr! 7 with m x
            exact Complex.exp_neg_real_I_eq_conj (x : EuclideanSpace ℝ (Fin d)) m
  _ = (1 / ZLattice.covolume P.lattice) *
      ∑' m : BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice,
      (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪x.val, (m.val).ofLp⟫_[ℝ])) ^ 2)
        := by
      simp_rw [← normSq_eq_norm_sq, mul_assoc, mul_conj, ← ofReal_one, ← ofReal_div, re_ofReal_mul]
      congr
      simp [Complex.re_tsum hsummable₅]
      congr with m
  -- We split the sum up into the `m = 0` and `m ≠ 0` parts.
  _ = (1 / ZLattice.covolume P.lattice) * (
      (∑' (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)),
        if hm : m = (0 : EuclideanSpace ℝ (Fin d)) then 0
        else (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2))
      +
      (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re *
      (norm (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2))
        := by
            apply congrArg _ _
            rw [add_comm]
            rw [Summable.tsum_eq_add_tsum_ite hsummable₃
              (0 : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice))]
            simp only [ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero, dite_eq_ite]
  _ ≥ (1 / ZLattice.covolume P.lattice) * (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re *
      (norm (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)
        := by
            -- We need to show that the `m ≠ 0` part is nonpositive.
            -- We begin by subtracting both sides, and thereby, isolating the `m ≠ 0` part.
            rw [ge_iff_le, ← tsub_nonpos, mul_assoc,
                ← mul_sub (1 / ZLattice.covolume P.lattice volume) _ _]
            simp only [ZeroMemClass.coe_eq_zero, dite_eq_ite, sub_add_cancel_right, mul_neg,
              Left.neg_nonpos_iff]
            -- We now get rid of the `1 / ZLattice.covolume P.lattice volume` factor.
            apply mul_nonneg
            · refine one_div_nonneg.mpr ?ha.a
              rw [ZLattice.covolume]
              exact ENNReal.toReal_nonneg
            · -- We now show that the `m ≠ 0` sum is nonpositive by showing that each term is.
              apply tsum_nonneg
              intro m
              cases eq_or_ne m 0
              · case inl h =>
                simp only [h, ↓reduceIte, le_refl]
              · case inr h =>
                simp only [h, ↓reduceIte]
                apply mul_nonneg
                · rw [← ge_iff_le]
                  exact hCohnElkies₂ m
                · -- Providing an explicit argument below gives a deterministic timeout...
                  exact sq_nonneg _
  _ = (1 / ZLattice.covolume P.lattice) * (𝓕 ⇑f (0 : EuclideanSpace ℝ (Fin d))).re *
      ↑(P.numReps' Fact.out hD_isBounded) ^ 2
        := by
            apply congrArg _ _
            let myInstFintype := P.instFintypeNumReps' hd hD_isBounded
            simp only [PeriodicSpherePacking.numReps']
            simp [RCLike.wInner_zero_right, ofReal_zero, mul_zero, Complex.exp_zero,
              nsmul_eq_mul, mul_one]
  _ = ↑(P.numReps' hd hD_isBounded) ^ 2 * (𝓕 ⇑f 0).re / ZLattice.covolume P.lattice volume
        := by simp only [div_eq_mul_inv, mul_comm, one_mul, ← mul_assoc]

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
    have vol_ne_zero : volume (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≠ 0 :=
      Ne.symm (ne_of_lt vol_pos)
    have vol_ne_top : volume (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≠ ∞ := by
      rw [← lt_top_iff_ne_top]
      exact EuclideanSpace.volume_ball_lt_top 0
    cases eq_or_ne (𝓕 f 0) 0
    · case inl h𝓕f =>
      rw [h𝓕f, zero_re]
      -- For `ENNReal.div_zero`, we need `f 0 ≠ 0`. This can be deduced from the fact that
      -- `𝓕 f ≥ 0` and `f ≠ 0`.
      have ne_zero_at_zero : ((f 0).re.toNNReal : ENNReal) ≠ 0 :=
        ENNReal.coe_ne_zero.mpr (Ne.symm (ne_of_lt (toNNReal_pos.mpr
        (f_zero_pos hne_zero hReal hRealFourier hCohnElkies₂))))
      -- Now we can safely divide by zero!
      rw [ENat.toENNReal_coe, toNNReal_zero, ENNReal.coe_zero, ENNReal.div_zero ne_zero_at_zero]
      -- We now need to multiply by ⊤.
      rw [ENNReal.top_mul vol_ne_zero]
      exact le_top
    · case inr h𝓕f =>
      -- First, we shift things around and cancel volumes on the right
      rw [ENat.toENNReal_coe, mul_div_assoc, div_eq_mul_inv (volume _), mul_comm (volume _),
          ← mul_assoc, ENNReal.mul_le_mul_iff_left vol_ne_zero vol_ne_top]
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
      have hfouaux₂ : ((𝓕 (⇑f) 0).re.toNNReal : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      rw [← ENNReal.mul_le_mul_iff_left hfouaux₁ hfouaux₂,
          div_eq_mul_inv ((f 0).re.toNNReal : ENNReal) _,
          mul_assoc ((f 0).re.toNNReal : ENNReal) _ _, ENNReal.inv_mul_cancel hfouaux₁ hfouaux₂]
      -- We put it in a more desirable form and consolidate.
      rw [mul_one, mul_assoc, ← ENNReal.div_eq_inv_mul]
      -- Next, we multiply both sides on the left by `↑P.numReps`.
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
      -- We put it in a more desirable form and consolidate.
      rw [ENat.toENNReal_coe, ← mul_assoc, ← pow_two, ← mul_div_assoc]
      -- Now, we use the nonnegativity of... everything... to get the `toNNReal`s to the outside.
      have hRHSCast : (P.numReps : ENNReal) * ↑(f 0).re.toNNReal = (P.numReps * (f 0).re).toNNReal
      := by
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
        refine NNReal.eq ?_
        push_cast
        rfl
      -- We can now get rid of the `toNNReal`s and use `hCalc` to finish the proof!
      rw [hRHSCast, hLHSCast, ENNReal.coe_le_coe]
      exact Real.toNNReal_le_toNNReal hCalc
  exact calc_steps hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP
    hD_isBounded hD_unique_covers hd

end Main_Theorem_For_One_Packing

section Main_Theorem

include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂

theorem LinearProgrammingBound (hd : 0 < d) : SpherePackingConstant d ≤
  (f 0).re.toNNReal / (𝓕 ⇑f 0).re.toNNReal * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
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
    exact zero_le _
  · case inr instNonempty =>
    let b : Basis (Fin d) ℤ ↥P.lattice := ((ZLattice.module_free ℝ P.lattice).chooseBasis).reindex
      (P.basis_index_equiv)
    exact LinearProgrammingBound' hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP
      (fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ P.lattice b))
      (P.fundamental_domain_unique_covers b) hd

end Main_Theorem
