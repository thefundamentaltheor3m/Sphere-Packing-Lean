module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

public import SpherePacking.ForMathlib.ScalarOneForm

/-!
# Fourier permutation bookkeeping for `perm_J12`

Dimension-agnostic Fourier-permutation step deriving `FT (J₁ + J₂) = -(J₃ + J₄)` from a contour
deformation identity and curve-integral expressions for `(𝓕 J₁)`, `(𝓕 J₂)`, and `J₃ + J₄`.
-/

open scoped FourierTransform
open MeasureTheory MagicFunction

namespace SpherePacking.Contour

/-- Hypotheses for the `perm_J12` Fourier permutation: contour deformation identity and
curve-integral expressions for `(𝓕 J₁)`, `(𝓕 J₂)`, and `J₃ + J₄`. -/
public structure PermJ12FourierHypotheses
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (J₁ J₂ J₃ J₄ : SchwartzMap V ℂ) (Ψ₁_fourier Ψ₁' : ℝ → ℂ → ℂ) : Prop where
  perm_J12_contour : ∀ r : ℝ,
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I), scalarOneForm (Ψ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I, scalarOneForm (Ψ₁_fourier r) z =
      -((∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I), scalarOneForm (Ψ₁' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I, scalarOneForm (Ψ₁' r) z)
  fourier_J₁_eq_curveIntegral : ∀ w : V, (𝓕 J₁) w =
    ∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
      scalarOneForm (Ψ₁_fourier (‖w‖ ^ (2 : ℕ))) z
  fourier_J₂_eq_curveIntegral : ∀ w : V, (𝓕 J₂) w =
    ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
      scalarOneForm (Ψ₁_fourier (‖w‖ ^ (2 : ℕ))) z
  J₃_J₄_eq_curveIntegral : ∀ w : V,
    (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
        scalarOneForm (Ψ₁' (‖w‖ ^ (2 : ℕ))) z) +
      (∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (Ψ₁' (‖w‖ ^ (2 : ℕ))) z) = (J₃ : V → ℂ) w + (J₄ : V → ℂ) w

/-- Fourier permutation: `PermJ12FourierHypotheses` gives `FT (J₁ + J₂) = -(J₃ + J₄)`. -/
public theorem perm_J₁_J₂_of
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {J₁ J₂ J₃ J₄ : SchwartzMap V ℂ} {Ψ₁_fourier Ψ₁' : ℝ → ℂ → ℂ}
    (h : PermJ12FourierHypotheses (V := V) J₁ J₂ J₃ J₄ Ψ₁_fourier Ψ₁') :
    FourierTransform.fourierCLE ℂ (SchwartzMap V ℂ) (J₁ + J₂) = -(J₃ + J₄) := by
  ext w
  simp [FourierTransform.fourierCLE_apply, FourierAdd.fourier_add, h.fourier_J₁_eq_curveIntegral,
    h.fourier_J₂_eq_curveIntegral, h.perm_J12_contour (r := ‖w‖ ^ (2 : ℕ)),
    h.J₃_J₄_eq_curveIntegral, add_comm]

/-- Reverse Fourier permutation: if `J₃ + J₄` is Fourier-symmetric and `FT (J₁ + J₂) = -(J₃ + J₄)`,
then `FT (J₃ + J₄) = -(J₁ + J₂)`. -/
public theorem perm_J₃_J₄_of
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {J₁ J₂ J₃ J₄ : SchwartzMap V ℂ}
    (hsymm : (FourierTransform.fourierCLE ℂ (SchwartzMap V ℂ)).symm (J₃ + J₄) =
        FourierTransform.fourierCLE ℂ (SchwartzMap V ℂ) (J₃ + J₄))
    (perm_J₁_J₂ : FourierTransform.fourierCLE ℂ (SchwartzMap V ℂ) (J₁ + J₂) = -(J₃ + J₄)) :
    FourierTransform.fourierCLE ℂ (SchwartzMap V ℂ) (J₃ + J₄) = -(J₁ + J₂) := by
  let FT := FourierTransform.fourierCLE ℂ (SchwartzMap V ℂ)
  have h₁ : J₁ + J₂ = -FT.symm (J₃ + J₄) := by
    simpa [FT] using (FT.symm_apply_apply (J₁ + J₂)).symm.trans (congrArg FT.symm perm_J₁_J₂)
  have : -(J₁ + J₂) = FT.symm (J₃ + J₄) := by simpa using congrArg Neg.neg h₁
  lia

end SpherePacking.Contour
