/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
import SpherePacking.CohnElkies.Prereqs
import SpherePacking.ForMathlib.VolumeOfBalls
import SpherePacking.Basic.PeriodicPacking
import Mathlib.Logic.IsEmpty
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Analysis.Complex.Basic

open scoped FourierTransform ENNReal SchwartzMap
open SpherePacking Metric BigOperators Pointwise Filter MeasureTheory Complex Real Zspan Bornology

variable {d : ℕ} [instPosDim : Fact (0 < d)] -- Is `Fact` right here?

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

-- Once we sort out the whole 'including variables' thing, we should remove all the variables from
-- the various lemmas and leave these as they are. Else, we should remove these and keep those.
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)
-- We need `f` to be real-valued for Cohn-Elkies, but do we need that for the PSF-L as well?
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
-- I'm not sure if `hCohnElkies₂` can replace this, because of the 5th step in `calc_steps`.
-- (The blueprint says that 𝓕 f x ≥ 0, ie, 𝓕 f ∈ [0, ∞) ⊆ ℝ, for all x ∈ ℝᵈ)
-- We can't simply replace 𝓕 f with its real part everywhere because the PSF-L involves 𝓕 f.
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
-- The Cohn-Elkies conditions:
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)

-- We (locally) denote the Complex Conjugate of some `z : ℂ` by `conj z`
local notation "conj" => starRingEnd ℂ

section Complex_Function_Helpers

private theorem helper (g : EuclideanSpace ℝ (Fin d) → ℂ) :
  (∀ x : EuclideanSpace ℝ (Fin d), ↑(g x).re = (g x)) →
  (∀ x : EuclideanSpace ℝ (Fin d), (g x).im = 0) := by
  intro hIsReal x
  specialize hIsReal x
  rw [← hIsReal, ofReal_im]

include hReal in
private theorem hImZero : ∀ x : EuclideanSpace ℝ (Fin d), (f x).im = 0 :=
  helper f hReal

include hRealFourier in
private theorem hFourierImZero : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).im = 0 :=
  helper (𝓕 f) hRealFourier

end Complex_Function_Helpers

section Nonnegativity

private theorem hIntegrable : MeasureTheory.Integrable (𝓕 f) :=
    ((SchwartzMap.fourierTransformCLE ℝ) f).integrable

include hne_zero

theorem fourier_ne_zero : 𝓕 f ≠ 0 := by
  rw [← SchwartzMap.fourierTransformCLE_apply ℝ f]
  intro hFourierZero
  apply hne_zero
  rw [← ContinuousLinearEquiv.map_eq_zero_iff (SchwartzMap.fourierTransformCLE ℝ)]
  exact Eq.symm (SchwartzMap.ext (congrFun (id (Eq.symm hFourierZero))))

include hReal hRealFourier hCohnElkies₂

theorem f_nonneg_at_zero : 0 ≤ (f 0).re := by
  -- Building off the previous one, f(0) is an integral of a nonneg function, and hence, also nonneg
  rw [← f.fourierInversion ℝ, fourierIntegralInv_eq]
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul]
  have hcalc₁ :
    (∫ (v : EuclideanSpace ℝ (Fin d)), 𝓕 (⇑f) v).re =
    ∫ (v : EuclideanSpace ℝ (Fin d)), (𝓕 (⇑f) v).re := by
    rw [← RCLike.re_eq_complex_re, ← integral_re hIntegrable]
  rw [hcalc₁]
  exact integral_nonneg hCohnElkies₂

theorem f_zero_pos : 0 < (f 0).re := by
  -- We know from previous that f(0) is nonneg. If zero, then the integral of 𝓕 f is zero, making
  -- 𝓕 f zero (it's continuous and nonneg: if it's pos anywhere, it's pos on a nbhd, and hence the
  -- integral must be pos too, but it's zero, contra). By Schwartz, f is identically zero iff 𝓕 f
  -- is (𝓕 is a linear iso). But 𝓕 f is zero while f is not, contra! So f(0) is positive.
  -- apply ne_of_gt
  have haux₁ : f 0 = 𝓕⁻ (𝓕 f) 0 := by rw [f.fourierInversion ℝ]
  rw [fourierIntegralInv_eq] at haux₁
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
         rw [← RCLike.re_eq_complex_re, ← integral_re hIntegrable, RCLike.re_eq_complex_re]
         rw [← RCLike.im_eq_complex_im, ← integral_im hIntegrable, RCLike.im_eq_complex_im]
    _ = ∫ (v : EuclideanSpace ℝ (Fin d)), (𝓕 (⇑f) v).re
      := by
         rw [add_right_eq_self]
         suffices hwhat : ∀ v : EuclideanSpace ℝ (Fin d), (𝓕 (⇑f) v).im = 0
         · simp only [hwhat, ofReal_zero, zero_mul, integral_zero]
         exact hFourierImZero hRealFourier
  rw [haux₂] at haux₁
  norm_cast at haux₁
  rw [haux₁, lt_iff_not_ge]
  by_contra hantisymm₁
  have hantisymm₂ : 0 ≤ ∫ (v : EuclideanSpace ℝ (Fin d)), (𝓕 (⇑f) v).re := integral_nonneg hCohnElkies₂
  have hintzero : 0 = ∫ (v : EuclideanSpace ℝ (Fin d)), (𝓕 (⇑f) v).re := by
    rw [ge_iff_le] at hantisymm₁
    exact antisymm' hantisymm₁ hantisymm₂
  have h𝓕frezero : ∀ x, (𝓕 f x).re = 0 := by
    -- Integral of a nonneg continuous function is zero iff the function is zero
    suffices hfun : (fun x => (𝓕 f x).re) = 0
    -- (This is the function actually being integrated)
    · intro x
      calc (𝓕 (⇑f) x).re
      _ = (fun x => (𝓕 f x).re) x := rfl
      _ = (0 : (EuclideanSpace ℝ (Fin d)) → ℝ) x := by rw [hfun]
      _ = 0 := by rw [Pi.zero_apply]
    have hcont : Continuous (fun x ↦ (𝓕 (⇑f) x).re) := by
      rw [← SchwartzMap.fourierTransformCLE_apply ℝ f]
      exact Continuous.comp' continuous_re ((SchwartzMap.fourierTransformCLE ℝ) f).continuous
    refine (Continuous.integral_zero_iff_zero_of_nonneg hcont ?_ hCohnElkies₂).mp hintzero.symm
    rw [← RCLike.re_eq_complex_re]
    refine MeasureTheory.Integrable.re ?_
    rw [← SchwartzMap.fourierTransformCLE_apply ℝ f]
    exact ((SchwartzMap.fourierTransformCLE ℝ) f).integrable
  have h𝓕fzero : 𝓕 f = 0 := by
    ext x
    rw [← re_add_im (𝓕 f x), hFourierImZero hRealFourier, ofReal_zero, zero_mul,
        add_zero, Pi.zero_apply, ofReal_eq_zero]
    exact h𝓕frezero x
  exact fourier_ne_zero hne_zero h𝓕fzero

end Nonnegativity

section Fundamental_Domain_Dependent

include d instPosDim f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)

/-
In this section, we will prove that the density of every periodic sphere packing of separation 1 is
bounded above by the Cohn-Elkies bound.
-/

include hP
private theorem calc_aux_1 :
  ∑' x : P.centers, ∑' y : ↑(P.centers ∩ D), (f (x - ↑y)).re
  ≤ ↑(P.numReps' Fact.out hD_isBounded) * (f 0).re := calc
  ∑' x : P.centers, ∑' y : ↑(P.centers ∩ D), (f (x - ↑y)).re
  _ = (∑' (x : P.centers) (y : ↑(P.centers ∩ D)),
      if h : x - (y : EuclideanSpace ℝ (Fin d)) = 0 then 0 else (f (x - ↑y)).re) +
      (∑' (x : ↑(P.centers ∩ D)), (f (0 : EuclideanSpace ℝ (Fin d))).re)
        := by
            -- First, we need to un-distribute the tsums on the RHS.
            -- Then, we need to use some sort of `tsum_ite_eq`.
            -- Both of the above require some summability stuff.
            sorry
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
    --     := by simp only [sub_self]
    _ = ↑(P.numReps' Fact.out hD_isBounded) * (f 0).re
        := by
            simp only [tsum_const, nsmul_eq_mul, mul_eq_mul_right_iff, Nat.cast_inj]
            cases eq_or_ne (f 0).re 0
            · case inl h =>
              right
              rw [h]
            · case inr h =>
              left
              let myInstFintype := P.instFintypeNumReps' Fact.out hD_isBounded
              rw [PeriodicSpherePacking.numReps']
              exact Nat.card_eq_fintype_card

-- # NOTE:
-- There are several summability results stated as intermediate `have`s in the following theorem.
-- I think their proofs should follow from whatever we define `PSF_Conditions` to be.
-- If there are assumptions needed beyond PSF, we should require them here, not in `PSF_Conditions`.
set_option maxHeartbeats 200000
private theorem calc_steps :
  ↑(P.numReps' Fact.out hD_isBounded) * (f 0).re ≥ ↑(P.numReps' Fact.out hD_isBounded) ^ 2 *
  (𝓕 f 0).re / Zlattice.covolume P.lattice := calc
  ↑(P.numReps' Fact.out hD_isBounded) * (f 0).re
  _ ≥ ∑' (x : P.centers) (y : ↑(P.centers ∩ D)),
      (f (x - ↑y)).re
        := by
            rw [ge_iff_le]
            exact calc_aux_1 hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP
              hD_isBounded
  _ = ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
      (f (↑x - ↑y + ↑ℓ)).re
        :=  by
              -- We need to use `PeriodocSpherePacking.unique_covers_of_centers` to split up the
              -- `tsum` in `x` by writing `P.centers` as a union of translates of `P.centers ∩ D`.
              -- We'd need disjointedness so we can apply `tsum_finset_bUnion_disjoint`.
              -- Some summability stuff might be necessary as well...

              sorry
  -- We now take the real part out so we can apply the PSF-L to the stuff inside.
  -- The idea would be to say, in subsequent lines, that "it suffices to show that the numbers
  -- whose real parts we're taking are equal as complex numbers" and then apply the PSF-L and
  -- other complex-valued stuff.
  _ = (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
      f (↑x - ↑y + ↑ℓ)).re
        := by
            -- rw [re_tsum hPSF.1] -- Needs some sort of summability over subsets...?
            sorry
  _ = (∑' x : ↑(P.centers ∩ D),
      ∑' y : ↑(P.centers ∩ D), (1 / Zlattice.covolume P.lattice) *
      ∑' m : DualLattice P.lattice, (𝓕 f m) *
      exp (2 * π * I * ⟪↑x - ↑y, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ)).re
        := by
            -- First, we apply the fact that two sides are equal if they're equal in ℂ.
            apply congrArg re
            -- Next, we apply the fact that two sums are equal if their summands are.
            apply congrArg _ _
            ext x
            apply congrArg _ _
            ext y
            -- Now that we've isolated the innermost sum, we can use the PSF-L.
            exact SchwartzMap.PoissonSummation_Lattices P.lattice f (x - ↑y)
  _ = ((1 / Zlattice.covolume P.lattice) * ∑' m : DualLattice P.lattice, (𝓕 f m).re * (
      ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
      exp (2 * π * I * ⟪↑x - ↑y, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ))).re
        := by
            apply congrArg re
            simp only [tsum_mul_left]
            apply congrArg _ _
            simp only [← tsum_mul_left]
            -- We want to apply `tsum_comm`, which requires some summability conditions.
            have hSummable₁ : Summable (Function.uncurry fun
            (m : ↥(DualLattice P.lattice)) (x : ↑(P.centers ∩ D)) ↦
            ∑' (x_1 : ↑(P.centers ∩ D)), ↑(𝓕 f ↑m).re * exp (2 * ↑π * I *
            ↑⟪(x : EuclideanSpace ℝ (Fin d)) - ↑x_1, ↑m⟫_ℝ)) := by
              sorry
            rw [← tsum_comm hSummable₁]
            apply congrArg _ _
            ext x
            have hSummable₂ : Summable (Function.uncurry fun
            (m : ↥(DualLattice P.lattice)) (x_1 : ↑(P.centers ∩ D)) ↦
            ↑(𝓕 f ↑m).re * exp (2 * ↑π * I * ↑⟪(x : EuclideanSpace ℝ (Fin d)) - ↑x_1, ↑m⟫_ℝ)) := by
              sorry
            rw [← tsum_comm hSummable₂]
            apply congrArg _ _
            ext y
            apply congrArg _ _
            ext m
            refine (IsUnit.mul_left_inj ?h.h).mpr ?h.a
            · rw [isUnit_iff_ne_zero]
              exact Complex.exp_ne_zero _
            · exact (hRealFourier (m : EuclideanSpace ℝ (Fin d))).symm
  _ = ((1 / Zlattice.covolume P.lattice) * ∑' m : DualLattice P.lattice, (𝓕 f m).re * (
      ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ) *
      exp (2 * π * I * ⟪-↑y, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ))).re
        := by
            -- As before, we have to go through a bunch of `congrArg`s to isolate the expressions we
            -- are really trying to show are equal.
            apply congrArg re
            apply congrArg _ _
            apply congrArg _ _
            ext m
            apply congrArg _ _
            apply congrArg _ _
            ext x
            apply congrArg _ _
            ext y
            rw [sub_eq_neg_add, inner_add_left]
            push_cast  -- Can this be condensed into a rw so that there's just a bunch of rws?
            rw [mul_add, Complex.exp_add, mul_comm]
  _ = ((1 / Zlattice.covolume P.lattice) * ∑' m : DualLattice P.lattice, (𝓕 f m).re *
      (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ)) *
      (∑' y : ↑(P.centers ∩ D),
      exp (-(2 * π * I * ⟪↑y, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ)))).re
        := by
            apply congrArg re
            apply congrArg _ _
            apply congrArg _ _
            ext m
            simp only [mul_assoc]
            apply congrArg _ _
            rw [← tsum_mul_right]
            apply congrArg _ _
            ext x
            rw [← tsum_mul_left]
            apply congrArg _ _
            ext y
            simp only [inner_neg_left, ofReal_neg, mul_neg]
  _ = ((1 / Zlattice.covolume P.lattice) * ∑' m : DualLattice P.lattice, (𝓕 f m).re *
      (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ)) *
      conj (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ)) -- Need its complex conjugate
      ).re
        := by
            apply congrArg re
            apply congrArg _ _
            apply congrArg _ _
            ext m
            apply congrArg _ _
            rw [conj_tsum]
            apply congrArg _ _
            ext x
            exact Complex.exp_neg_real_I_eq_conj (x : EuclideanSpace ℝ (Fin d)) m
  _ = (1 / Zlattice.covolume P.lattice) * ∑' m : DualLattice P.lattice, (𝓕 f m).re *
      (Complex.abs (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ)) ^ 2)
        := by
            -- Need to turn the RHS into the real part of a complex number
            rw [← ofReal_re (1 / Zlattice.covolume P.lattice volume *
                               ∑' (m : ↥(DualLattice P.lattice)),
                               (𝓕 f ↑m).re * Complex.abs (∑' (x : ↑(P.centers ∩ D)),
                               cexp (2 * ↑π * I * ↑⟪(x : EuclideanSpace ℝ (Fin d)), ↑m⟫_ℝ)) ^ 2)]
            -- Now we can apply the fact that the real parts of both expressions are equal if they
            -- are equal in ℂ.
            apply congrArg re
            push_cast
            apply congrArg _ _
            apply congrArg _ _
            ext m
            rw [mul_assoc]
            apply congrArg _ _
            rw [mul_conj, normSq_eq_abs]
            norm_cast
  -- We split the sum up into the `m = 0` and `m ≠ 0` parts.
  _ = (1 / Zlattice.covolume P.lattice) * (
      (∑' (m : DualLattice P.lattice), if hm : m = (0 : EuclideanSpace ℝ (Fin d)) then 0 else
      (𝓕 f m).re * (Complex.abs (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ)) ^ 2))
      +
      (𝓕 f (0 : EuclideanSpace ℝ (Fin d))).re *
      (Complex.abs (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_ℝ)) ^ 2))
        := by
            apply congrArg _ _
            rw [add_comm]
            have hSummable : Summable (fun (m : ↥(DualLattice P.lattice)) =>
              (𝓕 f m).re * (Complex.abs (∑' x : ↑(P.centers ∩ D),
              exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ)) ^ 2)) := by
              sorry
            rw [tsum_eq_add_tsum_ite hSummable (0 : ↥(DualLattice P.lattice))]
            simp only [ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero, dite_eq_ite]
  _ ≥ (1 / Zlattice.covolume P.lattice) * (𝓕 f (0 : EuclideanSpace ℝ (Fin d))).re *
      (Complex.abs (∑' x : ↑(P.centers ∩ D),
      exp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_ℝ)) ^ 2)
        := by
            -- We need to show that the `m ≠ 0` part is nonpositive.
            -- We begin by subtracting both sides, and thereby, isolating the `m ≠ 0` part.
            rw [ge_iff_le, ← tsub_nonpos, mul_assoc,
                ← mul_sub (1 / Zlattice.covolume P.lattice volume) _ _]
            simp only [ZeroMemClass.coe_eq_zero, dite_eq_ite, sub_add_cancel_right, mul_neg,
              Left.neg_nonpos_iff]
            -- We now get rid of the `1 / Zlattice.covolume P.lattice volume` factor.
            apply mul_nonneg
            · refine one_div_nonneg.mpr ?ha.a
              rw [Zlattice.covolume]
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
  _ = (1 / Zlattice.covolume P.lattice) * (𝓕 f (0 : EuclideanSpace ℝ (Fin d))).re *
      ↑(P.numReps' Fact.out hD_isBounded) ^ 2
        := by
            apply congrArg _ _
            let myInstFintype := P.instFintypeNumReps' Fact.out hD_isBounded
            simp only [inner_zero_right, zero_mul, ofReal_zero, mul_zero, Complex.exp_zero,
                       tsum_const, nsmul_eq_mul, mul_one, abs_natCast, Nat.cast_nonneg, ne_eq,
                       not_false_eq_true, pow_left_inj, Nat.cast_inj,
                       PeriodicSpherePacking.numReps', Set.toFinset_card] -- ↑(P.centers ∩ D)]
            exact Nat.card_eq_fintype_card
  _ = ↑(P.numReps' Fact.out hD_isBounded) ^ 2 * (𝓕 f 0).re / Zlattice.covolume P.lattice volume
        := by simp only [div_eq_mul_inv, one_div, mul_comm, one_mul, ← mul_assoc]


-- And now, the main result of this section:
include hP hD_isBounded hD_unique_covers hD_measurable

-- Temporary hack, must be deleted
-- instance : HMul ℝ ℝ≥0∞ ℝ≥0∞ := sorry

/-
I think the only sustainable fix is to show that the volume of a sphere is finite and then turn
`SpherePacking.density` into an element of `ℝ` instead of `ℝ≥0∞`.
-/

end Fundamental_Domain_Dependent

section Main_Theorem_For_One_Packing

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)

include d instPosDim f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ P hP D hD_isBounded hD_unique_covers

theorem LinearProgrammingBound' :
  P.density ≤ (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal *
  volume (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  -- HUGE TODO: Get the periodic density formula in terms of some `D`.
  rw [P.density_eq' Fact.out]
  suffices hCalc : (P.numReps' Fact.out hD_isBounded) * (f 0).re ≥
    (P.numReps' Fact.out hD_isBounded)^2 * (𝓕 f 0).re / Zlattice.covolume P.lattice
  · rw [hP]
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
      -- `𝓕 f ≥ 0` and `f ≠ 0`.
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
          ← mul_assoc, ENNReal.mul_le_mul_right vol_ne_zero vol_ne_top]
      -- Next, we simplify `hCalc` by replacing `numReps'` with `numReps`
      rw [← P.numReps_eq_numReps' Fact.out hD_isBounded hD_unique_covers] at hCalc
      -- Next, we multiply both sides by `(𝓕 (⇑f) 0).re.toNNReal`, cancelling accordingly.
      have hfouaux₁ : ((𝓕 (⇑f) 0).re.toNNReal : ENNReal) ≠ 0 := by
        intro hContra
        apply h𝓕f
        simp only [ENNReal.coe_eq_zero, toNNReal_eq_zero] at hContra
        specialize hCohnElkies₂ 0
        rw [ge_iff_le] at hCohnElkies₂
        -- We can't simply do antisymm because we have an equality in ℂ, not ℝ!
        rw [← re_add_im (𝓕 (⇑f) 0), le_antisymm hContra hCohnElkies₂,
            hFourierImZero hRealFourier 0, ofReal_zero, zero_mul, add_zero]
      have hfouaux₂ : ((𝓕 (⇑f) 0).re.toNNReal : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      rw [← ENNReal.mul_le_mul_right hfouaux₁ hfouaux₂,
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
      rw [← ENNReal.mul_le_mul_left hnRaux₁ hnRaux₂]
      -- We put it in a more desirable form and consolidate.
      rw [ENat.toENNReal_coe, ← mul_assoc, ← pow_two, ← mul_div_assoc]
      -- Now, we use the nonnegativity of... everything... to get the `toNNReal`s to the outside.
      have hRHSCast : (P.numReps : ENNReal) * ↑(f 0).re.toNNReal = (P.numReps * (f 0).re).toNNReal
      := by
        -- rw [ENNReal.coe_mul, ENNReal.coe_natCast]
        norm_cast
        refine NNReal.eq ?_
        have haux₁ : 0 ≤ ↑P.numReps * (f 0).re := mul_nonneg (Nat.cast_nonneg' P.numReps)
          (f_nonneg_at_zero hne_zero hReal hRealFourier hCohnElkies₂)
        rw [Real.toNNReal_of_nonneg (f_nonneg_at_zero hne_zero hReal hRealFourier hCohnElkies₂),
            Real.toNNReal_of_nonneg haux₁]
        push_cast
        rfl
      have hLHSCast : (P.numReps : ENNReal) ^ 2 * ((𝓕 (⇑f) 0).re.toNNReal : ENNReal) / ((Zlattice.covolume P.lattice volume).toNNReal : ENNReal) = ((P.numReps) ^ 2 * (𝓕 (⇑f) 0).re / Zlattice.covolume P.lattice volume).toNNReal := by
        simp only [mul_div_assoc, div_eq_mul_inv]
        have haux₁ : 0 ≤ ↑P.numReps ^ 2 * (𝓕 (⇑f) 0).re * (Zlattice.covolume P.lattice volume)⁻¹ := by
          refine mul_nonneg (mul_nonneg (sq_nonneg (P.numReps : ℝ)) (hCohnElkies₂ 0)) ?_
          rw [inv_nonneg]
          exact LT.lt.le (Zlattice.covolume_pos P.lattice volume)
        rw [Real.toNNReal_of_nonneg haux₁]
        have haux₂ : (Zlattice.covolume P.lattice volume).toNNReal ≠ 0 := by
          apply LT.lt.ne'
          rw [Real.toNNReal_pos]
          exact Zlattice.covolume_pos P.lattice volume
        rw [← ENNReal.coe_inv haux₂]
        norm_cast
        rw [Real.toNNReal_of_nonneg (hCohnElkies₂ 0),
            Real.toNNReal_of_nonneg (LT.lt.le (Zlattice.covolume_pos P.lattice volume))]
        refine NNReal.eq ?_
        push_cast
        rfl
      -- We can now get rid of the `toNNReal`s and use `hCalc` to finish the proof!
      rw [hRHSCast, hLHSCast, ENNReal.coe_le_coe]
      exact Real.toNNReal_le_toNNReal hCalc
  exact calc_steps hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP hD_isBounded

end Main_Theorem_For_One_Packing

section Main_Theorem

include d instPosDim f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂

theorem LinearProgrammingBound : SpherePackingConstant d ≤
  (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  rw [← periodic_constant_eq_constant (Fact.out),
    periodic_constant_eq_periodic_constant_normalized (Fact.out)]
  apply iSup_le
  intro P
  rw [iSup_le_iff]
  intro hP
  cases isEmpty_or_nonempty ↑P.centers
  · case inl instEmpty =>
    rw [P.density_of_centers_empty Fact.out]
    exact zero_le _
  · case inr instNonempty =>
    let b : Basis (Fin d) ℤ ↥P.lattice := ((Zlattice.module_free ℝ P.lattice).chooseBasis).reindex
      (P.basis_index_equiv)
    exact LinearProgrammingBound' hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP
      (fundamentalDomain_isBounded (Basis.ofZlatticeBasis ℝ P.lattice b))
      (P.fundamental_domain_unique_covers b)

end Main_Theorem
