module
import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12ContourDeformation
public import SpherePacking.MagicFunction.b.Schwartz.Basic
public import SpherePacking.MagicFunction.b.Eigenfunction.PermJ5Integrability
import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12CurveIntegrals
import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12FourierJ1
import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12FourierJ2
public import SpherePacking.ForMathlib.ScalarOneForm
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import SpherePacking.ForMathlib.GaussianFourierCommon


/-!
# Fourier permutations for `b`

This file combines contour permutation identities for the integrals defining `b` to show that `b`
is a `(-1)`-eigenfunction of the Fourier transform on `EuclideanSpace ℝ (Fin 8)`. The dimension-
agnostic abstract Fourier-permutation step (`perm_J₁_J₂_of`, `perm_J₃_J₄_of`) is bundled here.

## Main statement
* `eig_b`
-/

namespace SpherePacking.Contour

open scoped FourierTransform
open MeasureTheory MagicFunction

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

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology

open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral

theorem perm_J₁_J₂ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) ((J₁ : SchwartzMap ℝ⁸ ℂ) + J₂) =
      -((J₃ : SchwartzMap ℝ⁸ ℂ) + J₄) :=
  SpherePacking.Contour.perm_J₁_J₂_of
    (J₁ := (J₁ : SchwartzMap ℝ⁸ ℂ)) (J₂ := J₂)
    (J₃ := (J₃ : SchwartzMap ℝ⁸ ℂ)) (J₄ := J₄)
    (Ψ₁_fourier := Ψ₁_fourier) (Ψ₁' := Ψ₁')
    (h := ⟨perm_J12_contour,
      fun w => by simpa [SchwartzMap.fourier_coe] using fourier_J₁_eq_curveIntegral (w := w),
      fun w => by simpa [SchwartzMap.fourier_coe] using fourier_J₂_eq_curveIntegral (w := w),
      fun w => by
        simpa [J₃_apply, J₄_apply, add_assoc, add_left_comm, add_comm] using
          (J₃'_add_J₄'_eq_curveIntegral_segments (r := ‖w‖ ^ (2 : ℕ))).symm⟩)

/-- Rewrite `J₆'` as an integral over `Ici (1 : ℝ)`, using
`z₆' s = (Complex.I : ℂ) * (s : ℂ)`. -/
public lemma J₆'_eq (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₆' r =
      (-2 : ℂ) * ∫ s in Ici (1 : ℝ),
        (Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * r * s) := by
  simp only [MagicFunction.b.RealIntegrals.J₆', mul_assoc]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  refine
    (ae_restrict_iff' (measurableSet_Ici : MeasurableSet (Ici (1 : ℝ)))).2 <| .of_forall ?_
  intro s hs
  have hz6 : z₆' s = (Complex.I : ℂ) * (s : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (z₆'_eq_of_mem (t := s) hs)
  -- β-reduce, rewrite `z₆' s`, and then simplify the exponential using `I*I = -1`.
  dsimp
  rw [hz6]
  have hexp :
      cexp (↑π * ((Complex.I : ℂ) * ((r : ℂ) * ((Complex.I : ℂ) * (s : ℂ))))) =
        cexp (-↑π * ((r : ℂ) * (s : ℂ))) := by
    have :
        (↑π : ℂ) * ((Complex.I : ℂ) * ((r : ℂ) * ((Complex.I : ℂ) * (s : ℂ)))) =
          (-↑π : ℂ) * ((r : ℂ) * (s : ℂ)) := by
      ring_nf
      simp [Complex.I_sq]
    simpa using congrArg cexp this
  rw [hexp]

/-- Fourier permutation identity: `𝓕 J₅ = -J₆`. -/
public theorem perm_J₅ : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) J₅ = -J₆ := by
  ext w
  simp only [FourierTransform.fourierCLE_apply, neg_apply]
  change 𝓕 (J₅ : EuclideanSpace ℝ (Fin 8) → ℂ) w = -((J₆ : EuclideanSpace ℝ (Fin 8) → ℂ) w)
  rw [J₆_apply (x := w), fourier_eq' (J₅ : EuclideanSpace ℝ (Fin 8) → ℂ) w]
  simp only [smul_eq_mul, J₅_apply]
  have hJ5' (x : EuclideanSpace ℝ (Fin 8)) :
      MagicFunction.b.RealIntegrals.J₅' (‖x‖ ^ 2) =
        (-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s := by
    simpa using (J5Change.Complete_Change_of_Variables (r := (‖x‖ ^ 2)))
  simp only [hJ5', mul_assoc]
  let μs : Measure ℝ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))
  let f : (EuclideanSpace ℝ (Fin 8)) → ℝ → ℂ := fun x s ↦ PermJ5.kernel w (x, s)
  have hint : Integrable (Function.uncurry f)
      ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μs) := by
    simpa [μs, SpherePacking.Integration.μIciOne, f, Function.uncurry] using
      (PermJ5.integrable_kernel (w := w))
  have hinner (s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
      (∫ x : EuclideanSpace ℝ (Fin 8), f x s)
        =
      (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
    have hcancel : (s : ℂ) ^ (-4 : ℤ) * (s : ℂ) ^ (4 : ℕ) = 1 := by
      simpa [Complex.ofReal_zpow] using
        (PermJ5.zpow_neg_four_mul_pow_four (s := s) (ne_of_gt hs0))
    have hfactor :
        (fun x : EuclideanSpace ℝ (Fin 8) ↦ f x s) =
          fun x : EuclideanSpace ℝ (Fin 8) ↦
            ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * (s ^ (-4 : ℤ) : ℂ)) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) := by
      funext x
      dsimp [f, PermJ5.kernel, J5Change.g]
      simp
      ac_rfl
    rw [show (∫ x : EuclideanSpace ℝ (Fin 8), f x s) =
          ∫ x : EuclideanSpace ℝ (Fin 8),
            ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * (s ^ (-4 : ℤ) : ℂ)) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) from
      congrArg (fun F : EuclideanSpace ℝ (Fin 8) → ℂ => ∫ x, F x) hfactor]
    rw [MeasureTheory.integral_const_mul,
      SpherePacking.ForMathlib.integral_phase_gaussian_even (k := 4) (w := w) (s := s) hs0]
    linear_combination
      ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) * hcancel
  have hmain :
      (∫ x : EuclideanSpace ℝ (Fin 8),
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s))
        =
        (-2 : ℂ) *
          ∫ s in Ici (1 : ℝ),
            (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
    have hrew : (fun x : EuclideanSpace ℝ (Fin 8) ↦
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s)) =
        fun x : EuclideanSpace ℝ (Fin 8) ↦
          (-2 : ℂ) * ∫ s in Ici (1 : ℝ), f x s := by
      funext x
      rw [show (∫ s in Ici (1 : ℝ), f x s) =
          ∫ s in Ici (1 : ℝ), cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * J5Change.g (‖x‖ ^ 2) s
        from integral_congr_ae <| .of_forall fun _ ↦ by simp [f, PermJ5.kernel],
        MeasureTheory.integral_const_mul (μ := μs)]
      ring
    rw [show (∫ x : EuclideanSpace ℝ (Fin 8),
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s)) =
        ∫ x : EuclideanSpace ℝ (Fin 8), (-2 : ℂ) * ∫ s in Ici (1 : ℝ), f x s from
      congrArg (fun F : EuclideanSpace ℝ (Fin 8) → ℂ => ∫ x, F x) hrew,
      MeasureTheory.integral_const_mul,
      MeasureTheory.integral_integral_swap (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8))))
        (ν := μs) (f := f) hint]
    congr 1
    refine integral_congr_ae ((ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s hs ↦ ?_)
    simpa [f] using hinner s hs
  rw [hmain, J₆'_eq (r := ‖w‖ ^ 2),
    show (∫ s in Ici (1 : ℝ),
              (-I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) =
            -(∫ s in Ici (1 : ℝ),
              (Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) by
      rw [← MeasureTheory.integral_neg]
      exact integral_congr_ae <| .of_forall fun _ ↦ by ring]
  simp [mul_assoc]

/-- Fourier permutation identity: `𝓕 J₆ = -J₅`. -/
public theorem perm_J₆ : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) J₆ = -J₅ := by
  let FT := FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)
  have h : FT.symm J₆ = FT J₆ := by
    ext x
    simp only [FT, FourierTransform.fourierCLE_symm_apply, FourierTransform.fourierCLE_apply,
      fourier_coe, fourierInv_coe, fourierInv_eq_fourier_comp_neg]
    suffices (fun x ↦ J₆ (-x)) = ⇑J₆ by exact congr(𝓕 $this x)
    ext; simp [J₆, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]
  have h' : J₅ = -FT.symm J₆ := by
    simpa [map_neg] using congrArg FT.symm (show FT J₅ = -J₆ by simpa [FT] using perm_J₅)
  simpa [h] using (congrArg Neg.neg h').symm

theorem perm_₃_J₄ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) ((J₃ : SchwartzMap ℝ⁸ ℂ) + J₄) =
      -((J₁ : SchwartzMap ℝ⁸ ℂ) + J₂) := by
  let FT := FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)
  have hsymm : FT.symm ((J₃ : SchwartzMap ℝ⁸ ℂ) + J₄) = FT ((J₃ : SchwartzMap ℝ⁸ ℂ) + J₄) := by
    ext x
    simp only [FT, FourierTransform.fourierCLE_symm_apply, FourierTransform.fourierCLE_apply,
      fourier_coe, fourierInv_coe, fourierInv_eq_fourier_comp_neg]
    suffices (fun y : ℝ⁸ ↦ (J₃ + J₄) (-y)) = fun y ↦ (J₃ + J₄) y by
      simpa using congrArg (fun f : ℝ⁸ → ℂ => (𝓕 f) x) this
    funext y
    simp [J₃, J₄, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]
  simpa [FT] using
    SpherePacking.Contour.perm_J₃_J₄_of
      (J₁ := (J₁ : SchwartzMap ℝ⁸ ℂ)) (J₂ := J₂)
      (J₃ := (J₃ : SchwartzMap ℝ⁸ ℂ)) (J₄ := J₄)
      (hsymm := hsymm) (perm_J₁_J₂ := perm_J₁_J₂)

end Integral_Permutations

section Eigenfunction

/--
The Schwartz function `b` is a `(-1)`-eigenfunction of the Fourier transform on `ℝ⁸`.
-/
public theorem eig_b : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) b = -b := by
  rw [show b = J₁ + J₂ + J₃ + J₄ + J₅ + J₆ from rfl]
  have hrw : J₁ + J₂ + J₃ + J₄ + J₅ + J₆ = (J₁ + J₂) + (J₃ + J₄) + J₅ + J₆ := by ac_rfl
  rw [hrw, map_add, map_add, map_add, perm_J₁_J₂, perm_J₅, perm_₃_J₄, perm_J₆]
  abel

end Eigenfunction

end

end MagicFunction.b.Fourier
