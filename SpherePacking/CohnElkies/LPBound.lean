import SpherePacking.CohnElkies.Prereqs

open scoped FourierTransform ENNReal
open SpherePacking Metric BigOperators Pointwise Filter MeasureTheory Complex Real

variable {d : ℕ} [Fact (0 < d)]

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-
*Slight problem:*

What we have in Mathlib seems to deal with complex-valued functions. I've dealt with it for now by
giving an assumption that the imaginary part of `f` is always zero and stating everything else in
terms of the real part of `f`.
-/

variable {f : ℝᵈ → ℂ} (hPSF : PSF_Conditions f) (hReal : ∀ x : ℝᵈ, (f x).im = 0)
variable (hCohnElkies₁ : ∀ x : ℝᵈ, ‖x‖ ≥ 1 → (f x).re ≤ 0) (hCohnElkies₂ : ∀ x : ℝᵈ, (𝓕 f x).re ≥ 0)

private lemma calc_steps (P : PeriodicSpherePacking d) (hP : P.separation = 1) :
  ↑(Fintype.card (Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers))) * (f 0).re ≥
  ↑(Fintype.card (Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers))) ^ 2 * (𝓕 f 0).re /
  Zlattice.covolume P.Λ volume := calc
  _ ≥ ∑' x : P.centers, ∑' y : Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers), (f (x - ↑y)).re
        := sorry -- Might need some auxs or another calc, proving ≤ instead of ≥
  _ = ∑' x : Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers),
      ∑' y : Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers),
      ∑' ℓ : P.Λ, (f (↑x - ↑y + ↑ℓ)).re
        := sorry
  _ = ∑' x : Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers),
      ∑' y : Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers), (1 / Zlattice.covolume P.Λ) *
      ∑' m : DualLattice P.Λ, (𝓕 f m).re * cexp (2 * π * I * ⟪↑x - ↑y, (m : ℝᵈ)⟫_ℝ)
        := sorry  -- This is where the PSF-L is applied
  _ = (1 / Zlattice.covolume P.Λ) * ∑' m : DualLattice P.Λ, (𝓕 f m).re * (
      ∑' x : Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers),
      ∑' y : Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers),
      cexp (2 * π * I * ⟪↑x - ↑y, (m : ℝᵈ)⟫_ℝ))
        := sorry
  _ = (1 / Zlattice.covolume P.Λ) * ∑' m : DualLattice P.Λ, (𝓕 f m).re * (
      ∑' x : Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers),
      ∑' y : Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers),
      cexp (2 * π * I * ⟪↑x, (m : ℝᵈ)⟫_ℝ) * cexp (2 * π * I * ⟪-↑y, (m : ℝᵈ)⟫_ℝ))
        := sorry
  _ = (1 / Zlattice.covolume P.Λ) * ∑' m : DualLattice P.Λ, (𝓕 f m).re *
      (∑' x : Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers), cexp (2 * π * I * ⟪↑x, (m : ℝᵈ)⟫_ℝ)) *
      (∑' y : Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers), cexp (-(2 * π * I * ⟪↑y, (m : ℝᵈ)⟫_ℝ)))
        := sorry
  _ = (1 / Zlattice.covolume P.Λ) * ∑' m : DualLattice P.Λ, (𝓕 f m).re *
      (∑' x : Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers), cexp (2 * π * I * ⟪↑x, (m : ℝᵈ)⟫_ℝ)) *
      (∑' x : Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers), cexp (2 * π * I * ⟪↑x, (m : ℝᵈ)⟫_ℝ)).
      conj -- Have I done complex conjugation correctly?
        := sorry
  _ = (1 / Zlattice.covolume P.Λ) * ∑' m : DualLattice P.Λ, (𝓕 f m).re *
      (∑' x : Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers),
      |cexp (2 * π * I * ⟪↑x, (m : ℝᵈ)⟫_ℝ)| ^ 2)
        := sorry
  -- Why is the ≥ sign giving me an error below?
  -- _ ≥ (1 / Zlattice.covolume P.Λ) * (𝓕 f (0 : ℝᵈ)).re *
  --     (∑' x : Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers),
  --     |cexp (2 * π * I * ⟪↑x, (0 : ℝᵈ)⟫_ℝ)| ^ 2)
  --       := sorry -- Might need some auxs or another calc, proving ≤ instead of ≥
  _ = (1 / Zlattice.covolume P.Λ) * (𝓕 f (0 : ℝᵈ)).re *
      ↑(Fintype.card (Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers))) ^ 2
        := sorry
  _ = ↑(Fintype.card (Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers))) ^ 2 * (𝓕 f 0).re /
  Zlattice.covolume P.Λ volume
        := sorry

theorem LinearProgrammingBound :
  SpherePackingConstant d ≤ (f 0).re / (𝓕 f 0).re * volume (ball (0 : ℝᵈ) (1 / 2)) := by
  rw [← periodic_constant_eq_constant (Fact.out),
    periodic_constant_eq_periodic_constant_normalized (Fact.out)]
  apply iSup_le
  simp only [PeriodicSpherePacking.periodic_density_formula, iSup_le_iff]
  intro P hP
  suffices hCalc : (Fintype.card (Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers))) * (f 0).re ≥
    (Fintype.card (Quotient (AddAction.orbitRel ↥P.Λ ↑P.centers)))^2 * (𝓕 f 0).re /
    Zlattice.covolume P.Λ
  · rw [hP]
    sorry
  exact calc_steps P hP
