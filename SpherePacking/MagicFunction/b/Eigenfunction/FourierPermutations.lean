module
public import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12Regularity
public import SpherePacking.Contour.MobiusInv.WedgeSetContour
public import SpherePacking.MagicFunction.b.Schwartz.Basic
public import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ5
public import SpherePacking.ModularForms.SlashActionAuxil
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.MeasureTheory.Integral.ExpDecay
import SpherePacking.Integration.InvChangeOfVariables
import SpherePacking.MagicFunction.b.PsiBounds
public import SpherePacking.Integration.Measure
import SpherePacking.ForMathlib.DerivHelpers
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

open SpherePacking SpherePacking.ForMathlib

/-- Unfold `Jⱼ` as the primed radial profile `Jⱼ'` evaluated at `‖x‖^2`. -/
public lemma J₃_apply (x : EuclideanSpace ℝ (Fin 8)) :
    (J₃ : EuclideanSpace ℝ (Fin 8) → ℂ) x = MagicFunction.b.RealIntegrals.J₃' (‖x‖ ^ 2) := by
  simp [J₃]
public lemma J₄_apply (x : EuclideanSpace ℝ (Fin 8)) :
    (J₄ : EuclideanSpace ℝ (Fin 8) → ℂ) x = MagicFunction.b.RealIntegrals.J₄' (‖x‖ ^ 2) := by
  simp [J₄]
public lemma J₅_apply (x : EuclideanSpace ℝ (Fin 8)) :
    (J₅ : EuclideanSpace ℝ (Fin 8) → ℂ) x = MagicFunction.b.RealIntegrals.J₅' (‖x‖ ^ 2) := by
  simp [J₅]
public lemma J₆_apply (x : EuclideanSpace ℝ (Fin 8)) :
    (J₆ : EuclideanSpace ℝ (Fin 8) → ℂ) x = MagicFunction.b.RealIntegrals.J₆' (‖x‖ ^ 2) := by
  simp [J₆]

namespace J5Change

open SpherePacking.Integration.InvChangeOfVariables

def f : ℝ → ℝ := fun t ↦ 1 / t
def f' : ℝ → ℝ := fun t ↦ -1 / t ^ 2

/-- The integrand appearing after the `t ↦ 1 / t` substitution in `J₅'`. -/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦ -I
  * ψS' ((Complex.I : ℂ) * (s : ℂ))
  * (s ^ (-4 : ℤ))
  * cexp (-π * r / s)

lemma Reconciling_Change_of_Variables (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₅' r =
      (-2 : ℂ) * ∫ (t : ℝ) in Ioc 0 1, |f' t| • (g r (f t)) := by
  rw [show MagicFunction.b.RealIntegrals.J₅' r =
      (-2 : ℂ) * ∫ (t : ℝ) in Ioc 0 1,
        (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * r * (z₅' t)) by
    simp [MagicFunction.b.RealIntegrals.J₅', intervalIntegral_eq_integral_uIoc, zero_le_one,
      uIoc_of_le, mul_assoc]]
  congr 1
  apply setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ fun t ht => ?_
  have hz5 : z₅' t = (Complex.I : ℂ) * (t : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using z₅'_eq_of_mem (t := t) (mem_Icc_of_Ioc ht)
  have hψS_inv : ψS' ((Complex.I : ℂ) * (t : ℂ)⁻¹) = ψS.resToImagAxis (t⁻¹) := by
    simpa [one_div] using
      (show ψS' ((Complex.I : ℂ) * ((1 / t : ℝ) : ℂ)) = ψS.resToImagAxis (1 / t) by
        simp [ψS', Function.resToImagAxis, ResToImagAxis, one_div, mul_comm])
  have hscalC : (1 / t ^ 2 : ℂ) * ((1 / t : ℝ) ^ (-4 : ℤ) : ℂ) = (t : ℂ) ^ (2 : ℕ) := by
    have : ((1 / t ^ 2) * ((1 / t : ℝ) ^ (-4 : ℤ)) : ℂ) = (t ^ 2 : ℂ) := by
      exact_mod_cast one_div_pow_two_mul_one_div_zpow
        (k := 4) (t := t) (hk := by decide) (ht := ne_of_gt ht.1)
    simpa [Complex.ofReal_mul] using this
  have hexp : cexp (π * (Complex.I : ℂ) * r * (z₅' t)) = cexp (-π * r * t) := by
    simpa [mul_assoc] using congrArg cexp
      (show (π : ℂ) * (Complex.I : ℂ) * (r : ℂ) * (z₅' t) = (-π : ℂ) * (r : ℂ) * (t : ℂ) by
        rw [hz5]; ring_nf; rw [Complex.I_sq]; ring)
  rw [show (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * r * (z₅' t)) =
        (-I : ℂ) * ψS.resToImagAxis (1 / t) * (t : ℂ) ^ (2 : ℕ) * cexp (-π * r * t) by
      rw [MagicFunction.b.Schwartz.J5Smooth.ψI'_z₅'_eq t ht, hexp,
        show ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) = (-1 : ℂ) * (t : ℂ) ^ (2 : ℕ) by
          rw [mul_pow]; simp [Complex.I_sq]]
      ring,
    show |f' t| • g r (f t) =
        (-I : ℂ) * ψS.resToImagAxis (1 / t) * (t : ℂ) ^ (2 : ℕ) * cexp (-π * r * t) by
      rw [show |f' t| = 1 / t ^ 2 by simp [f', neg_div, abs_neg]]
      calc (1 / t ^ 2) • g r (f t) = (1 / t ^ 2 : ℂ) * g r (f t) := by simp [real_smul]
        _ = (-I : ℂ) * ψS.resToImagAxis (1 / t) *
              ((1 / t ^ 2 : ℂ) * ((1 / t : ℝ) ^ (-4 : ℤ) : ℂ)) * cexp (-π * r * t) := by
            simp [g, f, hψS_inv, mul_assoc, mul_left_comm, mul_comm]
        _ = (-I : ℂ) * ψS.resToImagAxis (1 / t) * (t : ℂ) ^ (2 : ℕ) * cexp (-π * r * t) := by
            rw [hscalC]]

/-- Change-of-variables formula expressing `J₅'` as an integral over `Ici (1 : ℝ)`. -/
public theorem Complete_Change_of_Variables (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₅' r = (-2 : ℂ) * ∫ s in Ici (1 : ℝ), (g r s) := by
  rw [Reconciling_Change_of_Variables (r := r)]
  simpa [f, f'] using
    congrArg (fun z : ℂ => (-2 : ℂ) * z)
      (integral_Ici_one_eq_integral_abs_deriv_smul (g := g r)).symm

end J5Change

section PermJ12

open MeasureTheory Set Complex Real
open Filter
open scoped Interval ModularForm

/-- `Ψ₁' r` is `DiffContOnCl` on `wedgeSet`. -/
public lemma diffContOnCl_Ψ₁'_wedgeSet (r : ℝ) :
    DiffContOnCl ℝ (Ψ₁' r) wedgeSet := by
  refine ⟨((differentiableOn_Ψ₁'_upper (r := r)).restrictScalars ℝ).mono
    wedgeSet_subset_upperHalfPlaneSet, fun z hzcl => ?_⟩
  by_cases h1 : z = (1 : ℂ)
  · subst h1
    have hval : Ψ₁' r 1 = 0 := by simp [Ψ₁', ψT']
    simpa [ContinuousWithinAt, hval] using (tendsto_Ψ₁'_one_within_closure_wedgeSet (r := r))
  · exact ((differentiableOn_Ψ₁'_upper (r := r)).continuousOn.continuousAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
        (mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hzcl h1))).continuousWithinAt

/-- The scalar one-form `scalarOneForm (Ψ₁' r)` is `DiffContOnCl` on `wedgeSet`. -/
public lemma diffContOnCl_ω_wedgeSet (r : ℝ) :
    DiffContOnCl ℝ (scalarOneForm (Ψ₁' r)) wedgeSet :=
  diffContOnCl_scalarOneForm (s := wedgeSet) (diffContOnCl_Ψ₁'_wedgeSet (r := r))

/-- Symmetry of the within-derivative of the scalar one-form on `wedgeSet`, i.e. `dω = 0`. -/
public lemma fderivWithin_ω_wedgeSet_symm (r : ℝ) :
    ∀ x ∈ wedgeSet, ∀ u ∈ tangentConeAt ℝ wedgeSet x, ∀ v ∈ tangentConeAt ℝ wedgeSet x,
      fderivWithin ℝ (scalarOneForm (Ψ₁' r)) wedgeSet x u v =
        fderivWithin ℝ (scalarOneForm (Ψ₁' r)) wedgeSet x v u := by
  intro x hx u _ v _
  simpa using
    (SpherePacking.ForMathlib.fderivWithin_scalarOneForm_symm_of_isOpen (f := Ψ₁' r)
      (s := wedgeSet) isOpen_wedgeSet hx (u := u) (v := v)
      ((differentiableOn_Ψ₁'_upper (r := r)).differentiableAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
          (wedgeSet_subset_upperHalfPlaneSet hx))))

/-- Sum of the two `Ψ₁_fourier` curve integrals on the left boundary equals minus the corresponding
sum of `Ψ₁'` curve integrals on the right boundary. -/
public lemma perm_J12_contour (r : ℝ) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + I),
          scalarOneForm (Ψ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + I) I,
          scalarOneForm (Ψ₁_fourier r) z =
      -((∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
            scalarOneForm (Ψ₁' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Ψ₁' r) z) := by
  simpa using
    (SpherePacking.perm_J12_contour_mobiusInv_wedgeSet
      (Ψ₁_fourier := Ψ₁_fourier)
      (Ψ₁' := Ψ₁')
      (Ψ₁_fourier_eq_neg_deriv_mul := Ψ₁_fourier_eq_neg_deriv_mul)
      (closed_ω_wedgeSet := fun r =>
        ⟨diffContOnCl_ω_wedgeSet (r := r), fderivWithin_ω_wedgeSet_symm (r := r)⟩)
      (r := r))

end PermJ12

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

namespace PermJ5

open SpherePacking.Integration (μIciOne)

lemma continuousOn_J₅_g :
    ContinuousOn (fun p : ℝ⁸ × ℝ ↦ J5Change.g (‖p.1‖ ^ 2) p.2) (univ ×ˢ Ici (1 : ℝ)) := by
  have hpos : ∀ s ∈ Ici (1 : ℝ), 0 < s := fun _ hs => lt_of_lt_of_le (by norm_num) hs
  have hψ : ContinuousOn (fun s : ℝ ↦ ψS' ((Complex.I : ℂ) * (s : ℂ))) (Ici (1 : ℝ)) :=
    (Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS)
      MagicFunction.b.PsiBounds.continuous_ψS).congr fun s hs => by
      simp [ψS', Function.resToImagAxis, ResToImagAxis, hpos s hs, mul_comm]
  have hzpow : ContinuousOn (fun s : ℝ ↦ (s : ℂ) ^ (-4 : ℤ)) (Ici (1 : ℝ)) := fun s hs =>
    ((continuousAt_zpow₀ (s : ℂ) (-4 : ℤ) (Or.inl (by exact_mod_cast (hpos s hs).ne'))).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  refine (show ContinuousOn
      (fun p : ℝ⁸ × ℝ ↦ (-I : ℂ) * ψS' ((Complex.I : ℂ) * (p.2 : ℂ)) * ((p.2 : ℂ) ^ (-4 : ℤ)) *
        cexp ((-π : ℂ) * ((‖p.1‖ : ℂ) ^ 2) / (p.2 : ℂ))) (univ ×ˢ Ici (1 : ℝ)) from
    ((continuousOn_const.mul (hψ.comp continuousOn_snd
      fun _ hp => (Set.mem_prod.mp hp).2)).mul (hzpow.comp continuousOn_snd
      fun _ hp => (Set.mem_prod.mp hp).2)).mul
      (fun p hp ↦ by
        have hp2 : (p.2 : ℂ) ≠ 0 := mod_cast (zero_lt_one.trans_le (by simpa using hp)).ne'
        fun_prop (disch := exact hp2))).congr fun p _ => ?_
  simp [J5Change.g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The `(x,s)`-kernel used in the `J₅`/`J₆` Fourier permutation argument. -/
@[expose] public def kernel (w : ℝ⁸) : ℝ⁸ × ℝ → ℂ := fun p =>
  cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) * J5Change.g (‖p.1‖ ^ 2) p.2

lemma aestronglyMeasurable_kernel (w : ℝ⁸) :
    AEStronglyMeasurable (kernel w) ((volume : Measure ℝ⁸).prod μIciOne) := by
  have hker : ContinuousOn (kernel w) (univ ×ˢ Ici (1 : ℝ)) :=
    ((by fun_prop : Continuous fun p : ℝ⁸ × ℝ =>
      cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I)).continuousOn.mul continuousOn_J₅_g).congr fun p _ => by
      simp [kernel]
  simpa [show ((volume : Measure ℝ⁸).prod μIciOne) =
      (((volume : Measure ℝ⁸).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ici (1 : ℝ))) by
        simpa [μIciOne, Measure.restrict_univ] using
          Measure.prod_restrict (μ := (volume : Measure ℝ⁸)) (ν := (volume : Measure ℝ))
            (s := (univ : Set ℝ⁸)) (t := Ici (1 : ℝ))] using
    hker.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Ici)

/-- Cancellation identity `s^(-4) * s^4 = 1` (after coercions to `ℂ`). -/
public lemma zpow_neg_four_mul_pow_four (s : ℝ) (hs : s ≠ 0) :
    ((s ^ (-4 : ℤ) : ℝ) : ℂ) * (s ^ 4 : ℂ) = 1 := by
  simpa [Complex.ofReal_zpow] using (zpow_neg_mul_zpow_self (a := (s : ℂ)) (n := (4 : ℤ))
    (by exact_mod_cast hs))

lemma kernel_norm_eq (w x : ℝ⁸) (s : ℝ) :
    ‖kernel w (x, s)‖ =
      (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖) *
        rexp (-π * (‖x‖ ^ 2) / s) := by
  have hphase : ‖Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I)‖ = (1 : ℝ) := by
    simpa using Complex.norm_exp_ofReal_mul_I (-2 * (Real.pi * ⟪x, w⟫))
  rw [show ‖kernel w (x, s)‖ =
      ‖Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) *
          ((-Complex.I : ℂ) *
                ψS' ((Complex.I : ℂ) * (s : ℂ)) *
                (s ^ (-(4 : ℤ)) : ℂ) *
                Complex.exp ((-Real.pi * (‖x‖ ^ 2) / s : ℝ) : ℂ))‖ from by
    simp [kernel, J5Change.g]]
  simp only [norm_mul, hphase, Complex.norm_exp_ofReal, norm_neg, Complex.norm_I, one_mul]

/-- Integrability of `kernel w` for the product measure `volume × μIciOne`. -/
public lemma integrable_kernel (w : ℝ⁸) :
    Integrable (kernel w) ((volume : Measure ℝ⁸).prod μIciOne) := by
  haveI : MeasureTheory.SFinite μIciOne := by dsimp [μIciOne]; infer_instance
  refine (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure ℝ⁸)) (ν := μIciOne)
    (aestronglyMeasurable_kernel (w := w))).2
    ⟨(ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s hs => by
      have hg : Continuous fun x : ℝ⁸ => J5Change.g (‖x‖ ^ 2) s := by
        simpa [continuousOn_univ, Function.comp] using continuousOn_J₅_g.comp
          (by fun_prop : Continuous fun x : ℝ⁸ => (x, s)).continuousOn
          (show MapsTo (fun x : ℝ⁸ => (x, s)) (Set.univ : Set ℝ⁸) (univ ×ˢ Ici (1 : ℝ)) from
            fun _ _ => ⟨Set.mem_univ _, hs⟩)
      exact Integrable.mono' (by
          simpa [mul_assoc] using
            (SpherePacking.ForMathlib.integrable_gaussian_rexp (s := s)
              (lt_of_lt_of_le (by norm_num) hs)).const_mul
              (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖))
        ((by fun_prop : Continuous fun x : ℝ⁸ => cexp (↑(-2 * (π * ⟪x, w⟫)) * I)).mul
          hg).aestronglyMeasurable <| .of_forall fun x =>
        le_of_eq (kernel_norm_eq (w := w) (x := x) (s := s)), ?_⟩
  obtain ⟨C, hC⟩ :=
    MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one
  have hmajor : Integrable (fun s : ℝ ↦ C * rexp (-π * s)) μIciOne := by
    simpa [μIciOne, IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using
      ((show IntegrableOn (fun s : ℝ ↦ rexp (-(π : ℝ) * s)) (Ici (1 : ℝ)) volume by
        simpa [pow_zero, one_mul] using
          SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 0) (b := (π : ℝ))
            Real.pi_pos).const_mul C)
  have hmeas' : AEStronglyMeasurable (fun s : ℝ ↦ ∫ x : ℝ⁸, ‖kernel w (x, s)‖) μIciOne := by
    simpa using (aestronglyMeasurable_kernel (w := w)).norm.prod_swap.integral_prod_right'
      (μ := μIciOne) (ν := (volume : Measure ℝ⁸))
  refine Integrable.mono' hmajor hmeas' <| (ae_restrict_iff' measurableSet_Ici).2 <|
    .of_forall fun s hs => ?_
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hval : ∫ x : ℝ⁸, ‖kernel w (x, s)‖ ≤ ‖ψS.resToImagAxis s‖ := by
    have hs_zpow_pos : 0 < s ^ (-4 : ℤ) := zpow_pos hs0 _
    have habs : ‖(s ^ (-4 : ℤ) : ℂ)‖ = s ^ (-4 : ℤ) := by
      change ‖(s : ℂ) ^ (-4 : ℤ)‖ = s ^ (-4 : ℤ)
      rw [show (s : ℂ) ^ (-4 : ℤ) = ((s ^ (-4 : ℤ) : ℝ) : ℂ) from
        (Complex.ofReal_zpow s (-4 : ℤ)).symm]
      exact (RCLike.norm_ofReal _).trans (abs_of_pos hs_zpow_pos)
    have hscal : (‖(s ^ (-4 : ℤ) : ℂ)‖) * (s ^ 4) = (1 : ℝ) := by
      rw [habs, show (s ^ (-4 : ℤ)) = (s ^ 4)⁻¹ by simpa using zpow_negSucc s 3]
      exact inv_mul_cancel₀ (pow_ne_zero 4 hs0.ne')
    refine le_of_eq ?_
    calc (∫ x : ℝ⁸, ‖kernel w (x, s)‖)
        = (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖) *
            (∫ x : ℝ⁸, rexp (-π * (‖x‖ ^ 2) / s)) := by
          rw [funext fun x => kernel_norm_eq (w := w) (x := x) (s := s)]
          exact MeasureTheory.integral_const_mul _ _
      _ = ‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ := by
          rw [SpherePacking.ForMathlib.integral_gaussian_rexp (s := s) hs0, mul_assoc, hscal,
            mul_one]
      _ = ‖ψS.resToImagAxis s‖ :=
          congrArg norm (by simp [ψS', Function.resToImagAxis, ResToImagAxis, hs0, mul_comm])
  simpa [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ ∫ x : ℝ⁸, ‖kernel w (x, s)‖ from
    MeasureTheory.integral_nonneg fun _ => norm_nonneg _)] using hval.trans (hC s hs)

end PermJ5

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
