import SpherePacking.CohnElkies.Prereqs

open scoped FourierTransform ENNReal
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

* The summations do not seem to be allowing a ≠ type condition on the index variable. We need this
  in order to be able to split sums up and deem one of the parts nonpositive or something.
* Everything in `Prereqs.lean` is either a TODO or has already been done (eg. in #25) (to reflect
  which the corresponding refs must be updated).
-/

-- Once we sort out the whole 'including variables' thing, we should remove all the variables from
-- the various lemmas and leave these as they are. Else, we should remove these and keep those.
variable {f : EuclideanSpace ℝ (Fin d) → ℂ} (hPSF : PSF_Conditions f) (hne_zero : f ≠ 0)
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

section Fundamental_Domain_Dependent

include d instPosDim f hPSF hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1)
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)

/-
In this section, we will prove that the density of every periodic sphere packing of separation 1 is
bounded above by the Cohn-Elkies bound.
-/

include hP
private lemma calc_aux_1 :
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
              rw [PeriodicSpherePacking.numReps', Set.toFinset_card]
              -- Now we have to deal with annoying `Nat.card` and `Fintype.card` stuff...
              -- rw [Nat.card_eq_fintype_card]  -- Doesn't work
              sorry

-- # NOTE:
-- There are several summability results stated as intermediate `have`s in the following lemma.
-- I think their proofs should follow from whatever we define `PSF_Conditions` to be.
-- If there are assumptions needed beyond PSF, we should require them here, not in `PSF_Conditions`.
set_option maxHeartbeats 200000
private lemma calc_steps :
  ↑(P.numReps' Fact.out hD_isBounded) * (f 0).re ≥ ↑(P.numReps' Fact.out hD_isBounded) ^ 2 *
  (𝓕 f 0).re / Zlattice.covolume P.lattice := calc
  ↑(P.numReps' Fact.out hD_isBounded) * (f 0).re
  _ ≥ ∑' (x : P.centers) (y : ↑(P.centers ∩ D)),
      (f (x - ↑y)).re
        := by
            rw [ge_iff_le]
            exact calc_aux_1 hPSF hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP
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
            exact PSF_L P.lattice hPSF (x - ↑y)
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
              -- This should, I think, follow from however we define `PSF_Conditions`.
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
                · -- Providing an explicit argument gives a deterministic timeout for some reason
                  exact sq_nonneg _
  _ = (1 / Zlattice.covolume P.lattice) * (𝓕 f (0 : EuclideanSpace ℝ (Fin d))).re *
      ↑(P.numReps' Fact.out hD_isBounded) ^ 2
        := by
            apply congrArg _ _
            -- Why do I have to restate this to get `Set.toFinset_card ↑(P.centers ∩ D)` to work?
            -- It should already be able to synthesise a `Fintype` instance... right?
            haveI := P.instFintypeNumReps' Fact.out hD_isBounded
            simp only [inner_zero_right, zero_mul, ofReal_zero, mul_zero, Complex.exp_zero,
                       tsum_const, nsmul_eq_mul, mul_one, abs_natCast, Nat.cast_nonneg, ne_eq,
                       not_false_eq_true, pow_left_inj, Nat.cast_inj,
                       PeriodicSpherePacking.numReps', Set.toFinset_card] -- ↑(P.centers ∩ D)]
            -- Why doesn't `exact Nat.card_eq_fintype_card` work?
            -- exact Nat.card_eq_fintype_card
            rw [Nat.card_eq_fintype_card]
            -- Why doesn't `exact Fintype.card_congr' rfl` work?
            -- exact Fintype.card_congr' rfl
            sorry
  _ = ↑(P.numReps' Fact.out hD_isBounded) ^ 2 * (𝓕 f 0).re / Zlattice.covolume P.lattice volume
        := by simp only [div_eq_mul_inv, one_div, mul_comm, mul_assoc, one_mul]

-- And now, the main result of this section:
include hP hD_isBounded hD_unique_covers hD_measurable

theorem LinearProgrammingBound' :
  P.density ≤
  (f 0).re / (𝓕 f 0).re * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  -- HUGE TODO: Get the periodic density formula in terms of some `D`.
  rw [P.periodic_density_formula' Fact.out hD_isBounded hD_unique_covers hD_measurable]
  suffices hCalc : (P.numReps' Fact.out hD_isBounded) * (f 0).re ≥ (P.numReps' Fact.out hD_isBounded)^2 * (𝓕 f 0).re / Zlattice.covolume P.lattice
  · rw [hP]
    rw [ge_iff_le] at hCalc
    cases eq_or_ne (𝓕 f 0) 0
    · case inl h𝓕f =>
      rw [h𝓕f, zero_re]
      -- For `ENNReal.div_zero`, we need `f 0 ≠ 0`. This can be deduced from the fact that
      -- `𝓕 f ≥ 0` and `f ≠ 0` (if we assume `f` to be Schwartz).
      sorry
    · case inr h𝓕f =>

      sorry
  exact calc_steps hPSF hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP hD_isBounded

end Fundamental_Domain_Dependent

section Fundamental_Domain_Inependent

theorem LinearProgrammingBound : SpherePackingConstant d ≤
  (f 0).re / (𝓕 f 0).re * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  rw [← periodic_constant_eq_constant (Fact.out),
    periodic_constant_eq_periodic_constant_normalized (Fact.out)]
  apply iSup_le
  intro P
  rw [iSup_le_iff]
  intro hP
  -- We need to choose `D` to be a fundamental domain and cook up proofs of the necessary
  -- assumptions on `D` to feed into `LinearProgrammingBound'`.
  -- exact LinearProgrammingBound' hPSF hP (((Zlattice.module_free ℝ P.lattice).chooseBasis).reindex
  --   (PeriodicSpherePacking.basis_index_equiv P))
  sorry

end Fundamental_Domain_Inependent
