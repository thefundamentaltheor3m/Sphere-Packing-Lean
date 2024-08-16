import SpherePacking.CohnElkies.Prereqs

open scoped FourierTransform ENNReal
open SpherePacking Metric BigOperators Pointwise Filter MeasureTheory Complex Real Zspan Bornology

variable {d : ℕ} [Fact (0 < d)] -- Is `Fact` right here?

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

variable {f : EuclideanSpace ℝ (Fin d) → ℂ} (hPSF : PSF_Conditions f)
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), (f x).im = 0)
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)

-- We (locally) denote the Complex Conjugate of some `z : ℂ` by `conj z`
-- Idea taken from https://github.com/leanprover-community/mathlib4/blob/75cc36e80cb9fe76f894b7688be1e0c792ae55d9/Mathlib/Analysis/Complex/UnitDisc/Basic.lean#L21
local notation "conj" => starRingEnd ℂ

section Fundamental_Domain_Dependent

/-
In this section, we will prove that the density of every periodic sphere packing of separation 1 is
bounded above by the Cohn-Elkies bound.
-/

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) (b : Basis (Fin d) ℤ P.lattice)
variable {D : Set (EuclideanSpace ℝ (Fin d))}
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)

private lemma calc_aux_1 {f : EuclideanSpace ℝ (Fin d) → ℂ} (hPSF : PSF_Conditions f)
  (hReal : ∀ x : EuclideanSpace ℝ (Fin d), (f x).im = 0)
  (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
  (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
  {P : PeriodicSpherePacking d} (hP : P.separation = 1)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
  (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D) :
  ∑' x : P.centers, ∑' y : ↑(P.centers ∩ D), (f (x - ↑y)).re
  ≤ ↑(P.numReps' Fact.out hD_isBounded) * (f 0).re := sorry
  -- calc
  -- ∑' x : P.centers, ∑' y : ↑(P.centers ∩ D), (f (x - ↑y)).re
  -- _ = (∑' (x : P.centers) (y : ↑(P.centers ∩ D))
  --     (_ : (y : EuclideanSpace ℝ (Fin d)) ≠ ↑x),
  --     (f (x - ↑y)).re) +
  --     (∑' (x : P.centers) (y : ↑(P.centers ∩ D))
  --     (_ : (y : EuclideanSpace ℝ (Fin d)) = ↑x),
  --     (f (x - ↑y)).re)
  --       := sorry
  -- _ ≤ (∑' (x : P.centers) (y : ↑(P.centers ∩ D))
  --     (_ : (y : EuclideanSpace ℝ (Fin d)) = ↑x),
  --     (f (x - ↑y)).re)
  --       := sorry
  --   _ = ∑' (y : ↑(P.centers ∩ D)), (f (y - ↑y)).re
  --       := sorry
  --   _ = ↑(P.numReps' Fact.out hD_isBounded) * (f 0).re
  --       := sorry

set_option maxHeartbeats 2000000
private lemma calc_steps {f : EuclideanSpace ℝ (Fin d) → ℂ} (hPSF : PSF_Conditions f)
  (hReal : ∀ x : EuclideanSpace ℝ (Fin d), (f x).im = 0)
  (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
  (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
  {P : PeriodicSpherePacking d} (hP : P.separation = 1)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
  (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D) :
  ↑(P.numReps' Fact.out hD_isBounded) * (f 0).re ≥ ↑(P.numReps' Fact.out hD_isBounded) ^ 2 * (𝓕 f 0).re /
  Zlattice.covolume P.lattice := calc
  ↑(P.numReps' Fact.out hD_isBounded) * (f 0).re
  _ ≥ ∑' x : P.centers,
      ∑' y : ↑(P.centers ∩ D),
      (f (x - ↑y)).re
        := by
            rw [ge_iff_le]
            exact calc_aux_1 hPSF hReal hCohnElkies₁ hCohnElkies₂ hP hD_isBounded hD_unique_covers hD_measurable
  _ = ∑' x : ↑(P.centers ∩ D),
      ∑' y : ↑(P.centers ∩ D),
      ∑' ℓ : P.lattice, (f (↑x - ↑y + ↑ℓ)).re
        :=  by sorry
  -- We now take the real part out so we can apply the PSF-L to the stuff inside.
  -- The idea would be to say, in subsequent lines, that "it suffices to show that the numbers
  -- whose real parts we're taking are equal as complex numbers" and then apply the PSF-L and
  -- other complex-valued stuff.
  _ = (∑' x : ↑(P.centers ∩ D),
      ∑' y : ↑(P.centers ∩ D),
      ∑' ℓ : P.lattice, f (↑x - ↑y + ↑ℓ)).re
        := by sorry
  _ = (∑' x : ↑(P.centers ∩ D),
      ∑' y : ↑(P.centers ∩ D), (1 / Zlattice.covolume P.lattice) *
      ∑' m : DualLattice P.lattice, (𝓕 f m) *
      cexp (2 * π * I * ⟪↑x - ↑y, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ)).re
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
      ∑' x : ↑(P.centers ∩ D),
      ∑' y : ↑(P.centers ∩ D),
      cexp (2 * π * I * ⟪↑x - ↑y, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ))).re
        := by
            apply congrArg re
            sorry
  _ = ((1 / Zlattice.covolume P.lattice) * ∑' m : DualLattice P.lattice, (𝓕 f m).re * (
      ∑' x : ↑(P.centers ∩ D),
      ∑' y : ↑(P.centers ∩ D),
      cexp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ) *
      cexp (2 * π * I * ⟪-↑y, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ))).re
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

            sorry
  _ = ((1 / Zlattice.covolume P.lattice) * ∑' m : DualLattice P.lattice, (𝓕 f m).re *
      (∑' x : ↑(P.centers ∩ D),
      cexp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ)) *
      (∑' y : ↑(P.centers ∩ D),
      cexp (-(2 * π * I * ⟪↑y, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ)))).re
        := by sorry
  _ = ((1 / Zlattice.covolume P.lattice) * ∑' m : DualLattice P.lattice, (𝓕 f m).re *
      (∑' x : ↑(P.centers ∩ D),
      cexp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ)) *
      conj (∑' x : ↑(P.centers ∩ D),
      cexp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ)) -- Need its complex conjugate
      ).re
        := by sorry
  _ = (1 / Zlattice.covolume P.lattice) * ∑' m : DualLattice P.lattice, (𝓕 f m).re *
      (∑' x : ↑(P.centers ∩ D),
      Complex.abs (cexp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ)) ^ 2)
        := by sorry
  _ = (1 / Zlattice.covolume P.lattice) * (
      (∑' (m : DualLattice P.lattice) , (𝓕 f m).re * -- Need to add a `(hm : m ≠ 0)` into the sum
      (∑' x : ↑(P.centers ∩ D),
      Complex.abs (cexp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_ℝ)) ^ 2))
      +
      (𝓕 f (0 : EuclideanSpace ℝ (Fin d))).re *
      (∑' x : ↑(P.centers ∩ D),
      Complex.abs (cexp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_ℝ)) ^ 2))
        := by sorry
  _ ≥ (1 / Zlattice.covolume P.lattice) * (𝓕 f (0 : EuclideanSpace ℝ (Fin d))).re *
      (∑' x : ↑(P.centers ∩ D),
      Complex.abs (cexp (2 * π * I * ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_ℝ)) ^ 2)
        := sorry
  _ = (1 / Zlattice.covolume P.lattice) * (𝓕 f (0 : EuclideanSpace ℝ (Fin d))).re *
      ↑(P.numReps' Fact.out hD_isBounded) ^ 2
        := by sorry
  _ = ↑(P.numReps' Fact.out hD_isBounded) ^ 2 * (𝓕 f 0).re /
  Zlattice.covolume P.lattice volume
        := by sorry

theorem LinearProgrammingBound' {f : EuclideanSpace ℝ (Fin d) → ℂ} (hPSF : PSF_Conditions f)
  (hReal : ∀ x : EuclideanSpace ℝ (Fin d), (f x).im = 0)
  (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
  (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
  {P : PeriodicSpherePacking d} (hP : P.separation = 1)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
  (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D) :
  P.density ≤
  (f 0).re / (𝓕 f 0).re * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  rw [P.periodic_density_formula' Fact.out hD_isBounded hD_unique_covers hD_measurable]
  suffices hCalc : (P.numReps' Fact.out hD_isBounded) * (f 0).re ≥ (P.numReps' Fact.out hD_isBounded)^2 * (𝓕 f 0).re / Zlattice.covolume P.lattice
  · rw [hP]
    rw [ge_iff_le] at hCalc
    cases eq_or_ne (𝓕 f 0) 0
    · case inl h𝓕f =>
      rw [h𝓕f]
      -- simp only [zero_re, div_zero]
      -- Why does `div_zero` replace the value with `0` instead of `⊤`? I'd like `⊤`!
      have h : ∀ a : ENNReal, a / 0 = ⊤ := by

        sorry
      sorry
    · case inr h𝓕f =>
      sorry
  exact calc_steps hPSF hReal hCohnElkies₁ hCohnElkies₂ hP hD_isBounded hD_unique_covers hD_measurable

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
