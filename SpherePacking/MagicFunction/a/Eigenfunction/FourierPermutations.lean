module
public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI12Prelude
public import SpherePacking.Basic.Domains.WedgeSet
public import SpherePacking.Contour.MobiusInv.WedgeSetContour
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import SpherePacking.MagicFunction.a.Eigenfunction.PermI12FourierMain
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import SpherePacking.ForMathlib.ScalarOneForm
import SpherePacking.MagicFunction.PolyFourierCoeffBound

/-!
# Fourier Permutations

We show that the Fourier transform permutes the integral pieces defining `a`, and deduce that `a`
is a Fourier eigenfunction.

## Main statements
* `eig_a`
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology Interval
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter
open Filter SpherePacking SpherePacking.ForMathlib MeasureTheory Set Complex Real

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

/-- `Φ₃' r` tends to `0` as `z → 1` within `closure wedgeSet`. -/
public lemma tendsto_Φ₃'_one_within_closure_wedgeSet (r : ℝ) :
    Tendsto (MagicFunction.a.ComplexIntegrands.Φ₃' r) (𝓝[closure wedgeSet] (1 : ℂ)) (𝓝 0) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  let expNorm : ℂ → ℝ := fun z ↦ ‖cexp (Real.pi * Complex.I * r * z)‖
  have hExp : ContinuousAt expNorm (1 : ℂ) := by fun_prop
  let M : ℝ := expNorm (1 : ℂ) + 1
  have hMpos : 0 < M := by positivity
  obtain ⟨δexp, hδexp_pos, hδexp⟩ := (Metric.continuousAt_iff.1 hExp) 1 (by norm_num)
  have hExpBound : ∀ {z : ℂ}, dist z (1 : ℂ) < δexp → expNorm z ≤ M := fun {z} hz ↦ by
    have habs : |expNorm z - expNorm (1 : ℂ)| < 1 := by simpa [Real.dist_eq] using hδexp hz
    simp only [M]
    linarith [le_abs_self (expNorm z - expNorm (1 : ℂ))]
  refine (Metric.tendsto_nhdsWithin_nhds).2 ?_
  intro ε hε
  have hub : Tendsto (fun z : ℂ => (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M) (𝓝 (1 : ℂ))
      (𝓝 (0 : ℝ)) := by
    simpa using (by fun_prop : Continuous (fun z : ℂ => (C₀ : ℝ) *
      (dist z (1 : ℂ)) ^ (2 : ℕ) * M)).tendsto (1 : ℂ)
  obtain ⟨δpow, hδpow_pos, hδpow⟩ :=
    Metric.mem_nhds_iff.1 <| Metric.tendsto_nhds.1 hub ε hε
  let δ : ℝ := min δexp (min 1 δpow)
  have hδ_pos : 0 < δ := lt_min hδexp_pos (lt_min (by norm_num) hδpow_pos)
  refine ⟨δ, hδ_pos, ?_⟩
  intro z hzcl hdistz
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    simpa [MagicFunction.a.ComplexIntegrands.Φ₃'] using hε
  have hdist_exp : dist z (1 : ℂ) < δexp := hdistz.trans_le (min_le_left _ _)
  have hdist_lt1 : dist z (1 : ℂ) < 1 :=
    hdistz.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdist_pow : dist z (1 : ℂ) < δpow :=
    hdistz.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hexpZ : expNorm z ≤ M := hExpBound hdist_exp
  have hz_im_pos : 0 < z.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using
      mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hzcl hz1
  have habs_re : |z.re - 1| ≤ z.im :=
    SpherePacking.closure_wedgeSet_subset_abs_re_sub_one_le_im hzcl
  have hnormSq_pos : 0 < Complex.normSq (z - 1) := Complex.normSq_pos.2 (sub_ne_zero.mpr hz1)
  have hz_im_lt1 : z.im < 1 :=
    (by simpa [abs_of_nonneg hz_im_pos.le] using Complex.abs_im_le_norm (z - 1) :
        z.im ≤ ‖z - 1‖).trans_lt (by simpa [dist_eq_norm] using hdist_lt1)
  have hnormSq_le : Complex.normSq (z - 1) ≤ 2 * z.im ^ 2 := by
    have hre_sq : (z.re - 1) ^ 2 ≤ z.im ^ 2 := by
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs_re 2
    have : Complex.normSq (z - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := by
      simp [Complex.normSq, sub_eq_add_neg, pow_two, add_comm]
    linarith
  have hw_half : (1 / 2 : ℝ) < (-1 / (z - 1)).im := by
    have him : (-1 / (z - 1)).im = z.im / Complex.normSq (z - 1) := by
      simp [div_eq_mul_inv, Complex.inv_im, sub_eq_add_neg]
    rw [him, lt_div_iff₀ hnormSq_pos]
    nlinarith [hnormSq_le, hz_im_pos, hz_im_lt1]
  have hw_pos : 0 < (-1 / (z - 1)).im := lt_trans (by norm_num) hw_half
  have hφ₀'' : ‖φ₀'' (-1 / (z - 1))‖ ≤ (C₀ : ℝ) := by
    let wH : UpperHalfPlane := ⟨-1 / (z - 1), hw_pos⟩
    have hφ₀_eq : φ₀ wH = φ₀'' (-1 / (z - 1)) := by
      simpa [wH] using (φ₀''_def (z := (-1 / (z - 1))) hw_pos).symm
    have hexp : Real.exp (-2 * Real.pi * wH.im) ≤ 1 := Real.exp_le_one_iff.2 <| by
      have : 0 ≤ Real.pi * wH.im := mul_nonneg Real.pi_pos.le wH.2.le; linarith
    calc ‖φ₀'' (-1 / (z - 1))‖
        = ‖φ₀ wH‖ := by rw [hφ₀_eq]
      _ ≤ (C₀ : ℝ) * Real.exp (-2 * Real.pi * wH.im) := hC₀ wH hw_half
      _ ≤ (C₀ : ℝ) * 1 := by gcongr
      _ = (C₀ : ℝ) := mul_one _
  have hmain :
      ‖MagicFunction.a.ComplexIntegrands.Φ₃' r z‖ ≤ (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M := by
    have heq : ‖MagicFunction.a.ComplexIntegrands.Φ₃' r z‖
        = ‖φ₀'' (-1 / (z - 1))‖ * (dist z (1 : ℂ)) ^ (2 : ℕ) * expNorm z := by
      simp [MagicFunction.a.ComplexIntegrands.Φ₃', expNorm, dist_eq_norm, mul_left_comm, mul_comm]
    rw [heq]; gcongr
  have hpow_small : (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M < ε := by
    have h : dist ((C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M) (0 : ℝ) < ε :=
      hδpow (show z ∈ Metric.ball (1 : ℂ) δpow from hdist_pow)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h
  simpa [dist_eq_norm] using hmain.trans_lt hpow_small

section Integral_Permutations

/-- The `1`-form built from `Φ₃'` is differentiable on `wedgeSet` with continuous extension. -/
public lemma diffContOnCl_ω_wedgeSet (r : ℝ) :
    DiffContOnCl ℝ (scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r)) wedgeSet :=
  ForMathlib.diffContOnCl_scalarOneForm (s := wedgeSet) <| by
    refine ⟨((MagicFunction.a.ComplexIntegrands.Φ₃'_contDiffOn (r := r)).differentiableOn
        (by simp)).mono wedgeSet_subset_upperHalfPlaneSet, fun z hz => ?_⟩
    by_cases h1 : z = (1 : ℂ)
    · subst h1
      have hval : MagicFunction.a.ComplexIntegrands.Φ₃' r (1 : ℂ) = 0 := by
        simp [MagicFunction.a.ComplexIntegrands.Φ₃']
      simpa [ContinuousWithinAt, hval] using tendsto_Φ₃'_one_within_closure_wedgeSet (r := r)
    · have hzU : z ∈ UpperHalfPlane.upperHalfPlaneSet :=
        mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hz h1
      exact ((MagicFunction.a.ComplexIntegrands.Φ₃'_contDiffOn (r := r)).continuousOn.continuousAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hzU)).continuousWithinAt

/-- Symmetry of the derivative of `scalarOneForm (Φ₃' r)` on `wedgeSet`.

This is the key hypothesis needed to apply the Poincare lemma. -/
public lemma fderivWithin_ω_wedgeSet_symm (r : ℝ) :
    ∀ x ∈ wedgeSet, ∀ u ∈ tangentConeAt ℝ wedgeSet x, ∀ v ∈ tangentConeAt ℝ wedgeSet x,
      fderivWithin ℝ (scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r)) wedgeSet x u v =
        fderivWithin ℝ (scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r))
          wedgeSet x v u := by
  intro x hx _ _ _ _
  have hxU : x ∈ UpperHalfPlane.upperHalfPlaneSet := wedgeSet_subset_upperHalfPlaneSet hx
  have hfdiff : DifferentiableAt ℂ (MagicFunction.a.ComplexIntegrands.Φ₃' r) x :=
    (MagicFunction.a.ComplexIntegrands.Φ₃'_holo (r := r)).differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hxU)
  exact SpherePacking.ForMathlib.fderivWithin_scalarOneForm_symm_of_isOpen
    (s := wedgeSet) isOpen_wedgeSet hx (hfdiff := hfdiff)

open MeasureTheory Set Complex Real

/-- The contour permutation identity underlying the Fourier invariance of the `I₁`/`I₂` part. -/
private lemma perm_I12_contour (r : ℝ) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
          scalarOneForm (Φ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Φ₁_fourier r) z =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
            scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z :=
  SpherePacking.perm_I12_contour_mobiusInv_wedgeSet
    (Ψ₁_fourier := Φ₁_fourier)
    (Ψ₁' := MagicFunction.a.ComplexIntegrands.Φ₃')
    (Ψ₁_fourier_eq_deriv_mul := Φ₁_fourier_eq_deriv_mobiusInv_mul_Φ₃')
    (closed_ω_wedgeSet := fun r =>
      ⟨diffContOnCl_ω_wedgeSet (r := r), fderivWithin_ω_wedgeSet_symm (r := r)⟩)
    (r := r)

theorem perm_I₁_I₂ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) (I₁ + I₂ : SchwartzMap ℝ⁸ ℂ) =
      (I₃ + I₄ : SchwartzMap ℝ⁸ ℂ) := by
  ext w
  simp only [FourierTransform.fourierCLE_apply, FourierAdd.fourier_add, add_apply, I₃_apply,
    I₄_apply, fourier_coe]
  rw [fourier_I₁_eq_curveIntegral (w := w), fourier_I₂_eq_curveIntegral (w := w),
    I₃'_add_I₄'_eq_curveIntegral_segments (r := ‖w‖ ^ 2)]
  simpa using perm_I12_contour (r := ‖w‖ ^ 2)

theorem perm_I₃_I₄ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) (I₃ + I₄ : SchwartzMap ℝ⁸ ℂ) =
      (I₁ + I₂ : SchwartzMap ℝ⁸ ℂ) := by
  rw [← perm_I₁_I₂]
  simpa using radial_inversion (I₁ + I₂) fun _ => by simp [I₁, I₂]

theorem perm_I₆ : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) I₆ = I₅ := by
  simpa [← perm_I₅] using radial_inversion I₅ fun _ => by
    simp [I₅, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]

end Integral_Permutations

section Eigenfunction

/-- The magic function `a` is invariant under the Fourier transform. -/
public theorem eig_a : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) a = a := by
  rw [show a = I₁ + I₂ + I₃ + I₄ + I₅ + I₆ from rfl,
    show I₁ + I₂ + I₃ + I₄ + I₅ + I₆ = (I₁ + I₂) + (I₃ + I₄) + I₅ + I₆ by ac_rfl,
    map_add, map_add, map_add, perm_I₁_I₂, perm_I₅, perm_I₃_I₄, perm_I₆]
  ac_rfl

end Eigenfunction
end
end MagicFunction.a.Fourier
