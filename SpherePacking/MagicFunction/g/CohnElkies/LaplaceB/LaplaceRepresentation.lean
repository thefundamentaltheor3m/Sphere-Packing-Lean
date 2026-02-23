module
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceB.Basic
public import SpherePacking.MagicFunction.g.CohnElkies.IntegralReductions
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceB.ContourIdentities
import SpherePacking.MagicFunction.g.CohnElkies.IntegralPieces

/-!
# Laplace representation for `b'`

This file proves the main Laplace representation for the radial profile `b'`, used in the
blueprint proposition `prop:b-double-zeros`.

## Main statements
* `MagicFunction.g.CohnElkies.IntegralReps.bRadial_eq_laplace_psiI_main`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Topology UpperHalfPlane intervalIntegral
open MeasureTheory Real Complex Filter
open MagicFunction.FourierEigenfunctions

private lemma setIntegral_Ioi0_eq_add_Ioc_Ioi {f : ℝ → ℂ}
    (hf : IntegrableOn f (Set.Ioi (0 : ℝ)) (μ := (volume : Measure ℝ))) :
    (∫ t in Set.Ioi (0 : ℝ), f t) =
      (∫ t in Set.Ioc (0 : ℝ) 1, f t) + (∫ t in Set.Ioi (1 : ℝ), f t) := by
  have hIoc : IntegrableOn f (Set.Ioc (0 : ℝ) 1) (μ := (volume : Measure ℝ)) :=
    hf.mono_set (by intro t ht; exact ht.1)
  have hIoi : IntegrableOn f (Set.Ioi (1 : ℝ)) (μ := (volume : Measure ℝ)) :=
    hf.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  simpa [Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)] using
    (MeasureTheory.setIntegral_union (μ := (volume : Measure ℝ)) (f := f)
      (s := Set.Ioc (0 : ℝ) 1) (t := Set.Ioi (1 : ℝ)) Set.Ioc_disjoint_Ioi_same
      measurableSet_Ioi hIoc hIoi)

/-- Main lemma for blueprint proposition `prop:b-double-zeros`. -/
public theorem bRadial_eq_laplace_psiI_main {u : ℝ} (hu : 2 < u) :
    b' u =
      (-4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ),
              ψI' ((Complex.I : ℂ) * (t : ℂ)) *
                Real.exp (-π * u * t)) := by
  have hu0 : 0 ≤ u := by linarith
  rw [MagicFunction.g.CohnElkies.b'_eq_realIntegrals_b' (u := u) hu0]
  have hLap :
      (∫ t in Set.Ioi (0 : ℝ),
          ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)) =
        -(∫ t in Set.Ioi (0 : ℝ), bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ))) := by
    calc
      (∫ t in Set.Ioi (0 : ℝ),
            ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)) =
          ∫ t in Set.Ioi (0 : ℝ), -bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ)) := by
            refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi ?_
            intro t ht
            simp [bContourIntegrandI, bContourWeight_mul_I, mul_assoc]
      _ = -(∫ t in Set.Ioi (0 : ℝ), bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ))) := by
            simp [MeasureTheory.integral_neg]
  let VI : ℂ := ∫ t in Set.Ioi (0 : ℝ), bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ))
  have hcoef :
      (2 : ℂ) - Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) -
            Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) =
        ((4 * (Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
    simpa using
      (MagicFunction.g.CohnElkies.Trig.two_sub_exp_pi_mul_I_sub_exp_neg_pi_mul_I u).trans
        (congrArg (fun r : ℝ => (r : ℂ))
          (MagicFunction.g.CohnElkies.Trig.two_sub_two_cos_eq_four_sin_sq u))
  rw [MagicFunction.b.RealIntegrals.b']
  have hRHS :
      (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
            (∫ t in Set.Ioi (0 : ℝ),
              ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)) =
        (Complex.I : ℂ) *
            (((2 : ℂ) - Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) -
                  Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I))) * VI) := by
    rw [hLap]
    dsimp [VI]
    rw [hcoef]
    simp [mul_assoc, mul_comm]
  rw [hRHS]
  clear hRHS hLap
  -- Deform the vertical lines onto the rectangle boundary pieces for `J₁', ..., J₄'`.
  have hStrip0 :
      (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    have : (1 : ℝ) ≤ z.im := by simpa [Set.mem_Ici] using hz.2
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) this
  have hcontT :
      ContinuousOn (bContourIntegrandT u) (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) := by
    simpa using (continuousOn_bContourIntegrandT (u := u)).mono hStrip0
  have hdiffT :
      ∀ z ∈ (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioi (1 : ℝ)),
        DifferentiableAt ℂ (bContourIntegrandT u) z := by
    intro z hz
    have hzIm : (1 : ℝ) < z.im := by
      simpa [Set.mem_Ioi] using hz.2
    have hzpos : 0 < z.im := lt_trans (by norm_num) hzIm
    -- Use differentiability on the open upper half-plane.
    exact
      (differentiableOn_bContourIntegrandT (u := u) z hzpos).differentiableAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hzpos)
  have hintI :
      IntegrableOn (fun t : ℝ => bContourIntegrandI u (I * (t : ℂ)))
        (Set.Ioi (0 : ℝ)) := by
    -- This is exactly `bLaplaceIntegral_convergent`, after rewriting the exponential.
    have hneg :
        IntegrableOn (fun t : ℝ => -bLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) :=
      (bLaplaceIntegral_convergent (u := u) hu).neg
    simpa [bContourIntegrandI_mul_I_eq_bLaplaceIntegrand] using hneg
  have hintT_center :
      IntegrableOn (fun t : ℝ => bContourIntegrandT u (I * (t : ℂ)))
        (Set.Ioi (1 : ℝ)) := by
    rcases exists_ψI_bound_exp with ⟨Cψ, Aψ, hCψ, hψbd⟩
    let A : ℝ := max 1 Aψ
    have hA1 : (1 : ℝ) ≤ A := le_max_left _ _
    have hAψ : Aψ ≤ A := le_max_right _ _
    let f : ℝ → ℂ := fun t : ℝ => bContourIntegrandT u (I * (t : ℂ))
    -- Integrability on the compact interval `[1,A]`.
    have hcontIcc : ContinuousOn f (Set.Icc (1 : ℝ) A) := by
      have hmul : ContinuousOn (fun t : ℝ => I * (t : ℂ)) (Set.Icc (1 : ℝ) A) := by
        simpa using (by
          have : Continuous (fun t : ℝ => I * (t : ℂ)) := by fun_prop
          exact this.continuousOn)
      have hmaps :
          Set.MapsTo (fun t : ℝ => I * (t : ℂ)) (Set.Icc (1 : ℝ) A)
            {z : ℂ | 0 < z.im} := by
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
        simpa using ht0
      simpa [f] using (continuousOn_bContourIntegrandT (u := u)).comp hmul hmaps
    have hInt_finite : IntegrableOn f (Set.Ioc (1 : ℝ) A) := by
      have hIntIcc : IntegrableOn f (Set.Icc (1 : ℝ) A) :=
        hcontIcc.integrableOn_compact isCompact_Icc
      exact hIntIcc.mono_set Set.Ioc_subset_Icc_self
    -- Tail integrability on `(A,∞)` by domination.
    have hdom :
        ∀ t : ℝ, t ∈ Set.Ioi A →
          ‖f t‖ ≤ Cψ * Real.exp (-(π * (u - 2)) * t) := by
      intro t ht
      have ht1 : 1 ≤ t := le_trans hA1 (le_of_lt ht)
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
      have hzI : 0 < (((I * (t : ℂ) + (1 : ℂ) : ℂ)).im) := by
        simpa [add_assoc, mul_assoc] using ht0
      let z : ℍ := ⟨I * (t : ℂ) + (1 : ℂ), hzI⟩
      have hzIm : Aψ ≤ z.im := by
        have : Aψ ≤ t := le_trans hAψ (le_of_lt ht)
        simpa [z, UpperHalfPlane.im, add_assoc, mul_assoc] using this
      have hψI :
          ‖ψI z‖ ≤ Cψ * Real.exp (2 * π * t) := by
        simpa [z, UpperHalfPlane.im, add_assoc, mul_assoc] using hψbd z hzIm
      have hψT : ψT' (I * (t : ℂ)) = ψI z := by
        calc
          ψT' (I * (t : ℂ)) = ψI' (I * (t : ℂ) + (1 : ℂ)) := ψT'_I_mul (t := t) ht0
          _ = ψI z := by simp [ψI', z, ht0]
      have hψT_norm :
          ‖ψT' (I * (t : ℂ))‖ ≤ Cψ * Real.exp (2 * π * t) := by
        simpa [hψT] using hψI
      have hnorm :
          ‖f t‖ = ‖ψT' (I * (t : ℂ))‖ * Real.exp (-π * u * t) := by
        simp [f, bContourIntegrandT_mul_I, -Complex.ofReal_exp, Complex.norm_real,
          abs_of_nonneg (le_of_lt (Real.exp_pos _))]
      rw [hnorm]
      have hmul :
          ‖ψT' ((Complex.I : ℂ) * (t : ℂ))‖ * Real.exp (-π * u * t) ≤
            (Cψ * Real.exp (2 * π * t)) * Real.exp (-π * u * t) :=
        mul_le_mul_of_nonneg_right hψT_norm (le_of_lt (Real.exp_pos _))
      refine le_trans hmul (le_of_eq ?_)
      calc
        (Cψ * Real.exp (2 * π * t)) * Real.exp (-π * u * t) =
            Cψ * (Real.exp (2 * π * t) * Real.exp (-π * u * t)) := by ring_nf
        _ = Cψ * Real.exp (2 * π * t + (-π * u * t)) := by
            simp [Real.exp_add, mul_assoc]
        _ = Cψ * Real.exp (-(π * (u - 2)) * t) := by ring_nf
    have hpos : 0 < π * (u - 2) := by
      have : 0 < u - 2 := sub_pos.2 hu
      exact mul_pos Real.pi_pos this
    have hg :
        Integrable (fun t : ℝ => Cψ * Real.exp (-(π * (u - 2)) * t))
          (volume.restrict (Set.Ioi A)) := by
      have hI : IntegrableOn (fun t : ℝ => Real.exp (-(π * (u - 2)) * t)) (Set.Ioi A) := by
        simpa [mul_assoc] using
          exp_neg_integrableOn_Ioi (a := A) (b := π * (u - 2)) hpos
      simpa [MeasureTheory.IntegrableOn, mul_assoc] using (hI.const_mul Cψ)
    have hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioi A)) := by
      have hmul : ContinuousOn (fun t : ℝ => I * (t : ℂ)) (Set.Ioi A) := by
        fun_prop
      have hmaps :
          Set.MapsTo (fun t : ℝ => I * (t : ℂ)) (Set.Ioi A) {z : ℂ | 0 < z.im} := by
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le (by linarith [hA1]) (le_of_lt ht)
        simpa using ht0
      have hcont : ContinuousOn f (Set.Ioi A) := by
        simpa [f] using (continuousOn_bContourIntegrandT (u := u)).comp hmul hmaps
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    have hInt_tail : IntegrableOn f (Set.Ioi A) := by
      have hInt : Integrable f (volume.restrict (Set.Ioi A)) := by
        refine MeasureTheory.Integrable.mono' hg hmeas ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
        intro t ht
        simpa using hdom t ht
      simpa [MeasureTheory.IntegrableOn] using hInt
    -- Combine `(1,A]` and `(A,∞)`.
    have hUnion : Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) A ∪ Set.Ioi A := by
      simpa using (Set.Ioc_union_Ioi_eq_Ioi (a := (1 : ℝ)) (b := A) hA1).symm
    rw [hUnion]
    exact hInt_finite.union hInt_tail
  -- The left/right vertical lines `Re z = ±1` reduce to `ψI(it)` using the `ψT'` identities.
  have hintT_shift (a : ℂ)
      (hψ : ∀ t : ℝ, 0 < t → ψT' (a + I * (t : ℂ)) = ψI' (I * (t : ℂ))) :
      IntegrableOn (fun t : ℝ => bContourIntegrandT u (a + I * (t : ℂ)))
        (Set.Ioi (1 : ℝ)) := by
    have hI1 :
        IntegrableOn (fun t : ℝ => bContourIntegrandI u (I * (t : ℂ)))
          (Set.Ioi (1 : ℝ)) := by
      simpa using hintI.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
    have hConst :
        IntegrableOn
            (fun t : ℝ =>
              (-bContourIntegrandI u (I * (t : ℂ))) * bContourWeight u a)
            (Set.Ioi (1 : ℝ)) := by
      simpa [mul_assoc] using (hI1.neg.mul_const (bContourWeight u a))
    refine hConst.congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := lt_trans (by norm_num) ht
    have hψ' := hψ t ht0
    simp [bContourIntegrandT, bContourIntegrandI, hψ', bContourWeight_add, mul_comm, mul_left_comm]
  have hintT_left :
      IntegrableOn (fun t : ℝ => bContourIntegrandT u ((-1 : ℂ) + I * (t : ℂ)))
        (Set.Ioi (1 : ℝ)) :=
    hintT_shift (-1 : ℂ) (fun t ht0 => by
      simpa [add_assoc] using ψT'_neg_one_add_I_mul (t := t) ht0)
  have hintT_right :
      IntegrableOn (fun t : ℝ => bContourIntegrandT u ((1 : ℂ) + I * (t : ℂ)))
        (Set.Ioi (1 : ℝ)) :=
    hintT_shift (1 : ℂ) (fun t ht0 => by
      simpa [add_assoc] using ψT'_one_add_I_mul (t := t) ht0)
  -- Decay of the contour integrand as `im z → ∞`, needed for the open-rectangle lemma.
  have htendstoT :
      ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖bContourIntegrandT u z‖ < ε := by
    rcases exists_ψI_bound_exp with ⟨Cψ, Aψ, hCψ, hψbd⟩
    have hc : 0 < π * (u - 2) := by
      have : 0 < u - 2 := sub_pos.2 hu
      exact mul_pos Real.pi_pos this
    -- The dominating exponential term tends to `0` as `y → ∞`.
    have htdec :
        Tendsto (fun y : ℝ => Cψ * Real.exp (-((π * (u - 2)) * y))) atTop (𝓝 (0 : ℝ)) := by
      have hmul : Tendsto (fun y : ℝ => (π * (u - 2)) * y) atTop atTop := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using (tendsto_id.const_mul_atTop hc)
      have hexp :
          Tendsto (fun y : ℝ => Real.exp (-((π * (u - 2)) * y))) atTop (𝓝 (0 : ℝ)) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
      have hconst : Tendsto (fun _ : ℝ => Cψ) atTop (𝓝 Cψ) := tendsto_const_nhds
      simpa [mul_assoc] using hconst.mul hexp
    intro ε hε
    have hEv :
        ∀ᶠ y in atTop, Cψ * Real.exp (-((π * (u - 2)) * y)) < ε := by
      simpa using htdec.eventually (Iio_mem_nhds hε)
    rcases (Filter.eventually_atTop.1 hEv) with ⟨Mε, hMε⟩
    let M : ℝ := max (max 1 Aψ) Mε
    refine ⟨M, ?_⟩
    intro z hzM
    have hzpos : 0 < z.im := by
      have hM1 : (1 : ℝ) ≤ M := le_trans (le_max_left 1 Aψ) (le_max_left (max 1 Aψ) Mε)
      exact lt_of_lt_of_le (by norm_num) (le_trans hM1 hzM)
    have hAψM : Aψ ≤ M := le_trans (le_max_right 1 Aψ) (le_max_left (max 1 Aψ) Mε)
    have hzAψ : Aψ ≤ z.im := le_trans hAψM hzM
    -- Control `ψT' z` by the exponential bound for `ψI`.
    have hψT : ψT' z = ψI' (z + (1 : ℂ)) := ψT'_eq_ψI'_add_one z hzpos
    have hzI : 0 < (z + (1 : ℂ)).im := by simpa [add_assoc] using hzpos
    have htIm :
        Aψ ≤ UpperHalfPlane.im (⟨z + (1 : ℂ), hzI⟩ : ℍ) := by
      simpa [UpperHalfPlane.im, add_assoc] using hzAψ
    have hψI :
        ‖ψI (⟨z + (1 : ℂ), hzI⟩ : ℍ)‖ ≤ Cψ * Real.exp (2 * π * z.im) := by
      simpa [UpperHalfPlane.im, add_assoc] using (hψbd (⟨z + (1 : ℂ), hzI⟩ : ℍ) htIm)
    have hψI' : ψI' (z + (1 : ℂ)) = ψI (⟨z + (1 : ℂ), hzI⟩ : ℍ) := by
      simp [ψI', hzpos]
    -- Norm of the exponential weight.
    have hweight : ‖bContourWeight u z‖ = Real.exp (-π * u * z.im) := by
      dsimp [bContourWeight]
      -- `‖exp w‖ = exp (Re w)`.
      rw [Complex.norm_exp]
      -- Compute the real part of `π * I * u * z`.
      have h1 :
          (π : ℂ) * (Complex.I : ℂ) * (u : ℂ) * z =
            ((π : ℂ) * (u : ℂ) * z) * (Complex.I : ℂ) := by
        ring_nf
      -- `Re (a * I) = -Im a`.
      simp [h1]
    -- Combine the estimates.
    have hnorm :
        ‖bContourIntegrandT u z‖ =
          ‖ψT' z‖ * ‖bContourWeight u z‖ := by
      simp [bContourIntegrandT]
    rw [hnorm, hψT, hψI', hweight]
    have hpos : 0 ≤ Real.exp (-π * u * z.im) := le_of_lt (Real.exp_pos _)
    have hmul :
        ‖ψI (⟨z + (1 : ℂ), hzI⟩ : ℍ)‖ * Real.exp (-π * u * z.im) ≤
          (Cψ * Real.exp (2 * π * z.im)) * Real.exp (-π * u * z.im) :=
      mul_le_mul_of_nonneg_right hψI hpos
    have hcomb : 2 * π * z.im + (-π * u * z.im) = -((π * (u - 2)) * z.im) := by ring_nf
    have hbound :
        ‖ψI (⟨z + (1 : ℂ), hzI⟩ : ℍ)‖ * Real.exp (-π * u * z.im) ≤
          Cψ * Real.exp (-((π * (u - 2)) * z.im)) := by
      calc
        ‖ψI (⟨z + (1 : ℂ), hzI⟩ : ℍ)‖ * Real.exp (-π * u * z.im) ≤
            (Cψ * Real.exp (2 * π * z.im)) * Real.exp (-π * u * z.im) := hmul
        _ = Cψ * Real.exp (-((π * (u - 2)) * z.im)) := by
            calc
              (Cψ * Real.exp (2 * π * z.im)) * Real.exp (-π * u * z.im) =
                  Cψ * (Real.exp (2 * π * z.im) * Real.exp (-π * u * z.im)) := by ring_nf
              _ = Cψ * Real.exp (2 * π * z.im + (-π * u * z.im)) := by
                  simp [Real.exp_add, mul_assoc]
              _ = Cψ * Real.exp (-((π * (u - 2)) * z.im)) := by
                  rw [hcomb]
    -- Apply the tail estimate from `Mε`.
    have hzMε : Mε ≤ z.im := le_trans (le_max_right (max 1 Aψ) Mε) hzM
    have htail : Cψ * Real.exp (-((π * (u - 2)) * z.im)) < ε := hMε z.im hzMε
    exact lt_of_le_of_lt hbound htail
  -- Apply the open-rectangle deformation for the left and right vertical lines.
  have hRectLeft :
      (∫ (x : ℝ) in (0 : ℝ)..1,
            bContourIntegrandT u ((x : ℂ) + (1 : ℂ) * Complex.I - 1)) +
          (I •
              ∫ (t : ℝ) in Set.Ioi (1 : ℝ), bContourIntegrandT u (I * (t : ℂ))) -
        (I •
            ∫ (t : ℝ) in Set.Ioi (1 : ℝ),
              bContourIntegrandT u ((-1 : ℂ) + I * (t : ℂ))) =
        0 := by
    -- Apply the general lemma with `f(z) = bContourIntegrandT u (z-1)`.
    -- Work on the strip `[[0,1]]×Ici 1`.
    let f : ℂ → ℂ := fun z : ℂ => bContourIntegrandT u (z - 1)
    have hcont' : ContinuousOn f (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) := by
      -- Compose `bContourIntegrandT` (continuous on the upper half-plane) with translation by `-1`.
      simpa [f] using
        (continuousOn_bContourIntegrandT (u := u)).comp (continuousOn_id.sub continuousOn_const) (by
          intro z hz
          have hz_uIcc : z ∈ Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ) := by
            simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hz
          have hz' : 0 < z.im := hStrip0 hz_uIcc
          simpa [sub_eq_add_neg] using hz')
    have hdiff' :
        ∀ z ∈
            ((Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1) ×ℂ Set.Ioi (1 : ℝ)) \
              (∅ : Set ℂ)),
          DifferentiableAt ℂ f z := by
      intro z hz
      have hzIm : (1 : ℝ) < z.im := by
        simpa [Set.mem_Ioi] using hz.1.2
      have hzpos : 0 < z.im := lt_trans (by norm_num) hzIm
      have hzpos' : 0 < (z - 1).im := by simpa [sub_eq_add_neg] using hzpos
      have hAt : DifferentiableAt ℂ (bContourIntegrandT u) (z - 1) :=
        (differentiableOn_bContourIntegrandT (u := u) (z - 1) hzpos').differentiableAt
          (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hzpos')
      have htrans : DifferentiableAt ℂ (fun z : ℂ => z - 1) z := by fun_prop
      simpa [f] using hAt.comp z htrans
    -- Integrability along the two vertical lines after translation.
    have hint₁ :
        IntegrableOn (fun t : ℝ => f ((0 : ℂ) + t * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
      simpa
          [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
            mul_assoc, mul_comm, mul_left_comm]
        using hintT_left
    have hint₂ :
        IntegrableOn (fun t : ℝ => f ((1 : ℂ) + t * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
      -- this is the center line `Re z = 0`.
      simpa
          [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
            mul_assoc, mul_comm, mul_left_comm]
        using hintT_center
    have htendsto' :
        ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε := by
      intro ε hε
      rcases htendstoT ε hε with ⟨M, hM⟩
      refine ⟨M, ?_⟩
      intro z hz
      have hz' : M ≤ (z - 1).im := by simpa [sub_eq_add_neg] using hz
      simpa [f] using hM (z - 1) hz'
    have hrect :=
      integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
        (y := (1 : ℝ)) (f := f) (x₁ := (0 : ℝ)) (x₂ := (1 : ℝ))
        hcont' (s := (∅ : Set ℂ)) (by simp) hdiff' hint₁ hint₂ htendsto'
    simpa
        [min_eq_left (zero_le_one : (0 : ℝ) ≤ 1),
          max_eq_right (zero_le_one : (0 : ℝ) ≤ 1),
          f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
          mul_assoc, mul_comm, mul_left_comm]
      using hrect
  have hRectRight :
      (∫ (x : ℝ) in (1 : ℝ)..0, bContourIntegrandT u ((x : ℂ) + (1 : ℂ) * Complex.I)) +
          (I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ), bContourIntegrandT u (I * (t : ℂ))) -
            (I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ),
              bContourIntegrandT u ((1 : ℂ) + I * (t : ℂ))) = 0 := by
    -- Direct application on `[[0,1]]×Ici 1` with reversed orientation `1..0`.
    -- Use `x₁ = 1`, `x₂ = 0`.
    have hcont1 :
        ContinuousOn (bContourIntegrandT u) (Set.uIcc (1 : ℝ) 0 ×ℂ Set.Ici (1 : ℝ)) := by
      simpa [Set.uIcc_comm] using hcontT
    have hdiff1 :
        ∀ z ∈
            ((Set.Ioo (min (1 : ℝ) 0) (max (1 : ℝ) 0) ×ℂ Set.Ioi (1 : ℝ)) \
              (∅ : Set ℂ)),
          DifferentiableAt ℂ (bContourIntegrandT u) z := by
      intro z hz
      exact hdiffT z (by
        simpa
            [min_eq_right (zero_le_one : (0 : ℝ) ≤ 1),
              max_eq_left (zero_le_one : (0 : ℝ) ≤ 1)]
          using hz.1)
    have hint₁ :
        IntegrableOn
          (fun t : ℝ => bContourIntegrandT u ((1 : ℂ) + (t : ℂ) * Complex.I))
          (Set.Ioi (1 : ℝ)) volume := by
      simpa [mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm] using
        hintT_right
    have hint₂ :
        IntegrableOn
          (fun t : ℝ => bContourIntegrandT u ((0 : ℂ) + (t : ℂ) * Complex.I))
          (Set.Ioi (1 : ℝ)) volume := by
      simpa [mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm] using
        hintT_center
    have hrect :=
      integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
        (y := (1 : ℝ)) (f := bContourIntegrandT u) (x₁ := (1 : ℝ)) (x₂ := (0 : ℝ))
        hcont1 (s := (∅ : Set ℂ)) (by simp) hdiff1 hint₁ hint₂ htendstoT
    simpa
        [min_eq_right (zero_le_one : (0 : ℝ) ≤ 1),
          max_eq_left (zero_le_one : (0 : ℝ) ≤ 1),
          mul_assoc, mul_comm, mul_left_comm, add_assoc, add_left_comm, add_comm]
      using hrect
  -- Use the rectangle identities to rewrite `J₁'+J₂'` and `J₃'+J₄'`
  -- as shifted ray integrals.
  -- We now expand the defining integrals of `b'` and simplify.
  -- The left and right shifted rays are converted to the central Laplace ray `VI` by translation.
  -- First express `J₂'` and `J₄'` as the top-edge integrals appearing in
  -- `hRectLeft/hRectRight`.
  have hJ2_top :
      MagicFunction.b.RealIntegrals.J₂' u =
        ∫ (x : ℝ) in (0 : ℝ)..1,
          bContourIntegrandT u ((x : ℂ) + (1 : ℂ) * Complex.I - 1) := by
    dsimp [MagicFunction.b.RealIntegrals.J₂']
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
    have hz : MagicFunction.Parametrisations.z₂' x = (-1 : ℂ) + (x : ℂ) + (I : ℂ) := by
      simpa using (MagicFunction.Parametrisations.z₂'_eq_of_mem (t := x) hx')
    have hz' : (x : ℂ) + (1 : ℂ) * Complex.I - 1 = (-1 : ℂ) + (x : ℂ) + (I : ℂ) := by
      ring_nf
    have hz_g : MagicFunction.Parametrisations.z₂' x = (x : ℂ) + (1 : ℂ) * Complex.I - 1 := by
      calc
        MagicFunction.Parametrisations.z₂' x = (-1 : ℂ) + (x : ℂ) + (I : ℂ) := hz
        _ = (x : ℂ) + (1 : ℂ) * Complex.I - 1 := by
          simpa using hz'.symm
    simp [bContourIntegrandT, bContourWeight, hz_g, sub_eq_add_neg, mul_assoc]
  have hJ4_top :
      MagicFunction.b.RealIntegrals.J₄' u =
        ∫ (x : ℝ) in (1 : ℝ)..0,
          bContourIntegrandT u ((x : ℂ) + (1 : ℂ) * Complex.I) := by
    -- Rewrite the parametrization `z₄'(t) = 1 - t + I` and switch orientation.
    dsimp [MagicFunction.b.RealIntegrals.J₄']
    let g : ℝ → ℂ := fun x : ℝ => bContourIntegrandT u ((x : ℂ) + (1 : ℂ) * Complex.I)
    have hrew :
        (∫ t in (0 : ℝ)..1,
            (-1 : ℂ) * ψT' (MagicFunction.Parametrisations.z₄' t) *
              cexp (π * (Complex.I : ℂ) * (u : ℂ) * MagicFunction.Parametrisations.z₄' t)) =
          ∫ t in (0 : ℝ)..1, (-1 : ℂ) * g (1 - t) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
      have hz : MagicFunction.Parametrisations.z₄' t = (1 : ℂ) - (t : ℂ) + (I : ℂ) := by
        -- `z₄'_eq_of_mem` gives `1 - t + I` with the real coercion.
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (MagicFunction.Parametrisations.z₄'_eq_of_mem (t := t) ht')
      have hz' :
          ((1 - t : ℝ) : ℂ) + (1 : ℂ) * Complex.I = (1 : ℂ) - (t : ℂ) + (I : ℂ) := by
        have hcast : ((1 - t : ℝ) : ℂ) = (1 : ℂ) - (t : ℂ) := by
          norm_cast
        -- Reduce to `1 * I = I`.
        simp [hcast]
      have hz_g :
          MagicFunction.Parametrisations.z₄' t =
            ((1 - t : ℝ) : ℂ) + (1 : ℂ) * Complex.I := by
        calc
          MagicFunction.Parametrisations.z₄' t = (1 : ℂ) - (t : ℂ) + (I : ℂ) := hz
          _ = ((1 - t : ℝ) : ℂ) + (1 : ℂ) * Complex.I := by
            exact hz'.symm
      simp [g, bContourIntegrandT, bContourWeight, hz_g, sub_eq_add_neg, mul_assoc]
    rw [hrew]
    have hcomp : (∫ t in (0 : ℝ)..1, g (1 - t)) = ∫ t in (0 : ℝ)..1, g t := by
      have h :=
        intervalIntegral.integral_comp_sub_left
          (f := g) (a := (0 : ℝ)) (b := (1 : ℝ)) (d := (1 : ℝ))
      calc
        (∫ t in (0 : ℝ)..1, g (1 - t)) = ∫ t in (1 : ℝ) - 1..(1 : ℝ) - 0, g t := h
        _ = ∫ t in (0 : ℝ)..1, g t := by simp
    -- `(-1) * ∫ g = ∫_{1..0} g` by orientation reversal.
    calc
      ∫ t in (0 : ℝ)..1, (-1 : ℂ) * g (1 - t)
          = (-1 : ℂ) * ∫ t in (0 : ℝ)..1, g (1 - t) := by
              simp
      _ = (-1 : ℂ) * ∫ t in (0 : ℝ)..1, g t := by rw [hcomp]
      _ = -∫ t in (0 : ℝ)..1, g t := by simp
      _ = ∫ t in (1 : ℝ)..0, g t := by
            simpa using
              (intervalIntegral.integral_symm (a := (0 : ℝ)) (b := (1 : ℝ)) (f := g)).symm
  -- Solve for `J₂'` and `J₄'` using the rectangle identities.
  have hJ2_ray :
      MagicFunction.b.RealIntegrals.J₂' u =
        (I •
              ∫ (t : ℝ) in Set.Ioi (1 : ℝ),
                bContourIntegrandT u ((-1 : ℂ) + I * (t : ℂ))) -
          (I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ), bContourIntegrandT u (I * (t : ℂ))) := by
    have htop := eq_sub_of_add_eq (sub_eq_zero.mp hRectLeft)
    simpa [hJ2_top] using htop
  have hJ4_ray :
      MagicFunction.b.RealIntegrals.J₄' u =
        (I •
              ∫ (t : ℝ) in Set.Ioi (1 : ℝ),
                bContourIntegrandT u ((1 : ℂ) + I * (t : ℂ))) -
          (I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ), bContourIntegrandT u (I * (t : ℂ))) := by
    have htop := eq_sub_of_add_eq (sub_eq_zero.mp hRectRight)
    simpa [hJ4_top] using htop
  -- Rewrite the remaining `J`-pieces as set integrals over `Ioc 0 1` and `Ioi 1`.
  have hJ1_set :
      MagicFunction.b.RealIntegrals.J₁' u =
        (I : ℂ) *
          (∫ t in Set.Ioc (0 : ℝ) 1,
            bContourIntegrandT u ((-1 : ℂ) + I * (t : ℂ))) := by
    dsimp [MagicFunction.b.RealIntegrals.J₁']
    -- Rewrite `z₁'(t) = -1 + I*t` on `[[0,1]]`.
    have hrew :
        (∫ t in (0 : ℝ)..1,
            (I : ℂ) * ψT' (MagicFunction.Parametrisations.z₁' t) *
              cexp (π * (I : ℂ) * (u : ℂ) * MagicFunction.Parametrisations.z₁' t)) =
          ∫ t in (0 : ℝ)..1,
            (I : ℂ) * bContourIntegrandT u ((-1 : ℂ) + I * (t : ℂ)) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
      have hz : MagicFunction.Parametrisations.z₁' t = (-1 : ℂ) + I * (t : ℂ) := by
        simpa using (MagicFunction.Parametrisations.z₁'_eq_of_mem (t := t) ht')
      simp [bContourIntegrandT, bContourWeight, hz, mul_assoc]
    rw [hrew]
    -- Pull out the constant `I` and convert the interval integral to a set integral.
    simp only [intervalIntegral.integral_const_mul, mul_eq_mul_left_iff, I_ne_zero, or_false]
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have hJ3_set :
      MagicFunction.b.RealIntegrals.J₃' u =
        (I : ℂ) *
          (∫ t in Set.Ioc (0 : ℝ) 1,
            bContourIntegrandT u ((1 : ℂ) + I * (t : ℂ))) := by
    dsimp [MagicFunction.b.RealIntegrals.J₃']
    have hrew :
        (∫ t in (0 : ℝ)..1,
            (I : ℂ) * ψT' (MagicFunction.Parametrisations.z₃' t) *
              cexp (π * (I : ℂ) * (u : ℂ) * MagicFunction.Parametrisations.z₃' t)) =
          ∫ t in (0 : ℝ)..1,
            (I : ℂ) * bContourIntegrandT u ((1 : ℂ) + I * (t : ℂ)) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
      have hz : MagicFunction.Parametrisations.z₃' t = (1 : ℂ) + I * (t : ℂ) := by
        simpa using (MagicFunction.Parametrisations.z₃'_eq_of_mem (t := t) ht')
      simp [bContourIntegrandT, bContourWeight, hz, mul_assoc]
    rw [hrew]
    simp only [intervalIntegral.integral_const_mul, mul_eq_mul_left_iff, I_ne_zero, or_false]
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have hJ5_set :
      MagicFunction.b.RealIntegrals.J₅' u =
        (2 : ℂ) * (I : ℂ) *
          (∫ t in Set.Ioc (0 : ℝ) 1, bContourIntegrandI u (I * (t : ℂ))) := by
    dsimp [MagicFunction.b.RealIntegrals.J₅']
    -- Rewrite `z₅'(t) = I*t` on `[[0,1]]` and pull out constants.
    have hrew :
        (∫ t in (0 : ℝ)..1,
              (I : ℂ) * ψI' (MagicFunction.Parametrisations.z₅' t) *
                cexp (π * (I : ℂ) * (u : ℂ) * MagicFunction.Parametrisations.z₅' t)) =
          ∫ t in (0 : ℝ)..1,
            -(I : ℂ) * bContourIntegrandI u (I * (t : ℂ)) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
      have hz : MagicFunction.Parametrisations.z₅' t = I * (t : ℂ) := by
        simpa using (MagicFunction.Parametrisations.z₅'_eq_of_mem (t := t) ht')
      simp [bContourIntegrandI, bContourWeight, hz, mul_assoc, mul_left_comm, mul_comm]
    rw [hrew]
    -- Convert the interval integral to a set integral and pull out the constants `-2` and `I`.
    simp only
      [neg_mul, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
        mul_neg, neg_neg]
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    ring
  have hJ6_set :
      MagicFunction.b.RealIntegrals.J₆' u =
        (-2 : ℂ) * (I : ℂ) *
          (∫ t in Set.Ioi (1 : ℝ), bContourIntegrandS u (I * (t : ℂ))) := by
    -- Rewrite `z₆'(t) = I*t` and remove the endpoint `t = 1`.
    dsimp [MagicFunction.b.RealIntegrals.J₆']
    have hcongr :
        (∫ t in Set.Ici (1 : ℝ),
              (I : ℂ) * ψS' (MagicFunction.Parametrisations.z₆' t) *
                cexp (π * (I : ℂ) * (u : ℂ) * MagicFunction.Parametrisations.z₆' t)) =
          ∫ t in Set.Ici (1 : ℝ),
            (I : ℂ) * bContourIntegrandS u (I * (t : ℂ)) := by
      refine MeasureTheory.setIntegral_congr_fun (s := Set.Ici (1 : ℝ)) measurableSet_Ici ?_
      intro t ht
      have hz : MagicFunction.Parametrisations.z₆' t = I * (t : ℂ) := by
        simpa using (MagicFunction.Parametrisations.z₆'_eq_of_mem (t := t) ht)
      simp [bContourIntegrandS, bContourWeight, hz, mul_assoc, mul_left_comm, mul_comm]
    rw [hcongr]
    -- Pull out `I` and replace `Ici 1` by `Ioi 1`.
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    simp [MeasureTheory.integral_const_mul, mul_assoc]
  -- Pointwise translation identities on the shifted rays.
  have hLeft_point :
      ∀ t : ℝ, 0 < t →
        bContourIntegrandT u ((-1 : ℂ) + I * (t : ℂ)) =
          bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u (-1 : ℂ)) := by
    intro t ht
    have hψ :
        ψT' ((-1 : ℂ) + I * (t : ℂ)) = ψI' (I * (t : ℂ)) :=
      ψT'_neg_one_add_I_mul (t := t) ht
    have hw :
        bContourWeight u ((-1 : ℂ) + I * (t : ℂ)) =
          bContourWeight u (I * (t : ℂ)) * bContourWeight u (-1 : ℂ) := by
      -- Use multiplicativity and commutativity of addition.
      simpa [add_assoc, add_left_comm, add_comm] using
        (bContourWeight_add (u := u) (I * (t : ℂ)) (-1 : ℂ))
    -- Expand the integrands and rewrite the exponential weight.
    simp [bContourIntegrandT, bContourIntegrandI, hψ, hw, mul_assoc]
  have hRight_point :
      ∀ t : ℝ, 0 < t →
        bContourIntegrandT u ((1 : ℂ) + I * (t : ℂ)) =
          bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u (1 : ℂ)) := by
    intro t ht
    have hψ :
        ψT' ((1 : ℂ) + I * (t : ℂ)) = ψI' (I * (t : ℂ)) :=
      ψT'_one_add_I_mul (t := t) ht
    have hw :
        bContourWeight u ((1 : ℂ) + I * (t : ℂ)) =
          bContourWeight u (I * (t : ℂ)) * bContourWeight u (1 : ℂ) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        (bContourWeight_add (u := u) (I * (t : ℂ)) (1 : ℂ))
    simp [bContourIntegrandT, bContourIntegrandI, hψ, hw, mul_assoc]
  have hITS :
      ∀ z : ℂ, 0 < z.im →
        bContourIntegrandT u z + bContourIntegrandS u z = -bContourIntegrandI u z := by
    intro z hz
    have hψ :
        ψI' z = ψT' z + ψS' z := by
      have h := congrArg (fun F : ℍ → ℂ => F ⟨z, hz⟩) ψI_eq_add_ψT_ψS
      simpa [ψI', ψT', ψS', hz] using h
    simp [bContourIntegrandI, bContourIntegrandT, bContourIntegrandS, hψ, add_mul]
  -- Convert the full left/right rays and the central correction term to `VI`.
  have hLeft_ray :
      (∫ t in Set.Ioi (0 : ℝ),
            bContourIntegrandT u ((-1 : ℂ) + I * (t : ℂ))) =
        (-VI) * bContourWeight u (-1 : ℂ) := by
    have hcongr :
        (∫ t in Set.Ioi (0 : ℝ),
              bContourIntegrandT u ((-1 : ℂ) + I * (t : ℂ))) =
            ∫ t in Set.Ioi (0 : ℝ),
              bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u (-1 : ℂ)) := by
      refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi ?_
      intro t ht
      exact hLeft_point t ht
    rw [hcongr]
    -- Pull out the constant exponential weight.
    dsimp [VI]
    have hmul :
        (∫ t in Set.Ioi (0 : ℝ),
              bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u (-1 : ℂ))) =
            (∫ t in Set.Ioi (0 : ℝ),
              bContourIntegrandI u (I * (t : ℂ))) * (-bContourWeight u (-1 : ℂ)) :=
      (MeasureTheory.integral_mul_const (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (r := -bContourWeight u (-1 : ℂ))
        (f := fun t : ℝ => bContourIntegrandI u (I * (t : ℂ))))
    -- Normalize `* (-w)` into `(-·) * w`.
    -- (We keep this algebraic step explicit to avoid simp rewriting the integrand to `-(·)`.)
    calc
      (∫ t in Set.Ioi (0 : ℝ),
            bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u (-1 : ℂ))) =
          (∫ t in Set.Ioi (0 : ℝ),
            bContourIntegrandI u (I * (t : ℂ))) * (-bContourWeight u (-1 : ℂ)) := hmul
      _ = (-((∫ t in Set.Ioi (0 : ℝ),
            bContourIntegrandI u (I * (t : ℂ))) * bContourWeight u (-1 : ℂ))) := by
          ring
      _ = (- (∫ t in Set.Ioi (0 : ℝ),
            bContourIntegrandI u (I * (t : ℂ)))) * bContourWeight u (-1 : ℂ) := by
          ring
  have hRight_ray :
      (∫ t in Set.Ioi (0 : ℝ),
            bContourIntegrandT u ((1 : ℂ) + I * (t : ℂ))) =
        (-VI) * bContourWeight u (1 : ℂ) := by
    have hcongr :
        (∫ t in Set.Ioi (0 : ℝ),
              bContourIntegrandT u ((1 : ℂ) + I * (t : ℂ))) =
            ∫ t in Set.Ioi (0 : ℝ),
              bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u (1 : ℂ)) := by
      refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi ?_
      intro t ht
      exact hRight_point t ht
    rw [hcongr]
    dsimp [VI]
    have hmul :
        (∫ t in Set.Ioi (0 : ℝ),
              bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u (1 : ℂ))) =
            (∫ t in Set.Ioi (0 : ℝ),
              bContourIntegrandI u (I * (t : ℂ))) * (-bContourWeight u (1 : ℂ)) :=
      (MeasureTheory.integral_mul_const (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (r := -bContourWeight u (1 : ℂ))
        (f := fun t : ℝ => bContourIntegrandI u (I * (t : ℂ))))
    calc
      (∫ t in Set.Ioi (0 : ℝ),
            bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u (1 : ℂ))) =
          (∫ t in Set.Ioi (0 : ℝ),
            bContourIntegrandI u (I * (t : ℂ))) * (-bContourWeight u (1 : ℂ)) := hmul
      _ = (-((∫ t in Set.Ioi (0 : ℝ),
            bContourIntegrandI u (I * (t : ℂ))) * bContourWeight u (1 : ℂ))) := by
          ring
      _ = (- (∫ t in Set.Ioi (0 : ℝ),
            bContourIntegrandI u (I * (t : ℂ)))) * bContourWeight u (1 : ℂ) := by
          ring
  have hCenter_split :
      (∫ t in Set.Ioi (1 : ℝ), bContourIntegrandS u (I * (t : ℂ))) =
        -(∫ t in Set.Ioi (1 : ℝ), bContourIntegrandI u (I * (t : ℂ))) -
          (∫ t in Set.Ioi (1 : ℝ), bContourIntegrandT u (I * (t : ℂ))) := by
    -- Use `ψI = ψT + ψS` to rewrite `S` as `-I - T`.
    have hcongr :
        (∫ t in Set.Ioi (1 : ℝ), bContourIntegrandS u ((Complex.I : ℂ) * (t : ℂ))) =
            ∫ t in Set.Ioi (1 : ℝ),
              ((-bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ))) -
                bContourIntegrandT u ((Complex.I : ℂ) * (t : ℂ))) := by
      refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (1 : ℝ)) measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := lt_trans (by norm_num) ht
      have hz : 0 < (((Complex.I : ℂ) * (t : ℂ) : ℂ)).im := by simpa using ht0
      have hsum := hITS (((Complex.I : ℂ) * (t : ℂ) : ℂ)) hz
      -- Rearrange `T + S = -I` into `S = -I - T`.
      have : bContourIntegrandS u ((Complex.I : ℂ) * (t : ℂ)) =
          (-bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ))) -
            bContourIntegrandT u ((Complex.I : ℂ) * (t : ℂ)) := by
        have hsum' :
            bContourIntegrandS u ((Complex.I : ℂ) * (t : ℂ)) +
                bContourIntegrandT u ((Complex.I : ℂ) * (t : ℂ)) =
              -bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ)) := by
          simpa [add_comm, add_left_comm, add_assoc] using hsum
        simpa [sub_eq_add_neg, add_assoc] using (eq_sub_of_add_eq hsum')
      simp [this]
    rw [hcongr]
    -- Apply linearity of the integral on `Ioi 1`.
    have hI1 :
        IntegrableOn
          (fun t : ℝ => bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ)))
          (Set.Ioi (1 : ℝ)) := by
      exact hintI.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
    have hT1 :
        IntegrableOn
          (fun t : ℝ => bContourIntegrandT u ((Complex.I : ℂ) * (t : ℂ)))
          (Set.Ioi (1 : ℝ)) :=
      hintT_center
    -- Coerce to integrable functions over the restricted measure.
    have hI1' :
        Integrable (fun t : ℝ => bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ)))
          (volume.restrict (Set.Ioi (1 : ℝ))) := by
      simpa [IntegrableOn] using hI1
    have hT1' :
        Integrable (fun t : ℝ => bContourIntegrandT u ((Complex.I : ℂ) * (t : ℂ)))
          (volume.restrict (Set.Ioi (1 : ℝ))) := by
      simpa [IntegrableOn] using hT1
    have hSub :=
      (MeasureTheory.integral_sub (μ := volume.restrict (Set.Ioi (1 : ℝ))) hI1'.neg hT1')
    -- `∫ (-I - T) = -∫ I - ∫ T`.
    simpa
        [MeasureTheory.integral_neg, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hSub
  -- Split `VI` at height `1`.
  have hVI_split :
      VI =
        (∫ t in Set.Ioc (0 : ℝ) 1, bContourIntegrandI u (I * (t : ℂ))) +
          (∫ t in Set.Ioi (1 : ℝ), bContourIntegrandI u (I * (t : ℂ))) := by
    have hUnion :
        (∫ t in Set.Ioi (0 : ℝ),
              bContourIntegrandI u (I * (t : ℂ))) =
            (∫ t in Set.Ioc (0 : ℝ) 1, bContourIntegrandI u (I * (t : ℂ))) +
              (∫ t in Set.Ioi (1 : ℝ), bContourIntegrandI u (I * (t : ℂ))) :=
      setIntegral_Ioi0_eq_add_Ioc_Ioi (f := fun t : ℝ => bContourIntegrandI u (I * (t : ℂ)))
        hintI
    dsimp [VI]
    simp [hUnion]
  -- Now put everything together.
  have hsum :
      MagicFunction.b.RealIntegrals.J₁' u +
          MagicFunction.b.RealIntegrals.J₂' u +
            MagicFunction.b.RealIntegrals.J₃' u +
              MagicFunction.b.RealIntegrals.J₄' u +
                MagicFunction.b.RealIntegrals.J₅' u +
                  MagicFunction.b.RealIntegrals.J₆' u =
        (Complex.I : ℂ) *
          (((2 : ℂ) - bContourWeight u (1 : ℂ) - bContourWeight u (-1 : ℂ)) * VI) := by
    -- Rewrite `J₂'` and `J₄'` using the rectangle identities.
    rw [hJ2_ray, hJ4_ray]
    -- Replace `J₁',J₃',J₅',J₆'` by their set-integral forms.
    rw [hJ1_set, hJ3_set, hJ5_set, hJ6_set]
    -- Convert the shifted-ray integrals on `Ioi 1` into full rays on `Ioi 0`.
    -- Left ray: `Ioc 0 1` + `Ioi 1` equals `Ioi 0`.
    have hIocI :
        IntegrableOn
          (fun t : ℝ => bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ)))
          (Set.Ioc (0 : ℝ) 1) := by
      refine hintI.mono_set ?_
      intro t ht
      exact ht.1
    have hIoiI :
        IntegrableOn
          (fun t : ℝ => bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ)))
          (Set.Ioi (1 : ℝ)) :=
      hintI.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
    have hsplitW (w : ℂ) :
        (∫ t in Set.Ioc (0 : ℝ) 1,
              bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ)) * w) +
            (∫ t in Set.Ioi (1 : ℝ),
              bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ)) * w) =
          (∫ t in Set.Ioi (0 : ℝ),
            bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ)) * w) := by
      have hIoi0W :
          IntegrableOn
            (fun t : ℝ => bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ)) * w)
            (Set.Ioi (0 : ℝ)) :=
        by
          simpa [mul_assoc] using (hintI.mul_const w)
      simpa [add_comm, add_left_comm, add_assoc] using
        (setIntegral_Ioi0_eq_add_Ioc_Ioi (f := fun t : ℝ =>
            bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ)) * w) hIoi0W).symm
    -- Rewrite shifted rays using the pointwise translation lemmas.
    have hJ1_shift :
        (∫ t in Set.Ioc (0 : ℝ) 1,
              bContourIntegrandT u ((-1 : ℂ) + I * (t : ℂ))) =
            ∫ t in Set.Ioc (0 : ℝ) 1,
              bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u (-1 : ℂ)) := by
      refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioc (0 : ℝ) 1) measurableSet_Ioc ?_
      intro t ht
      exact hLeft_point t ht.1
    have hJ2_shift :
        (∫ t in Set.Ioi (1 : ℝ),
              bContourIntegrandT u ((-1 : ℂ) + I * (t : ℂ))) =
            ∫ t in Set.Ioi (1 : ℝ),
              bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u (-1 : ℂ)) := by
      refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (1 : ℝ)) measurableSet_Ioi ?_
      intro t ht
      exact hLeft_point t (lt_trans (by norm_num) ht)
    have hJ3_shift :
        (∫ t in Set.Ioc (0 : ℝ) 1,
              bContourIntegrandT u ((1 : ℂ) + I * (t : ℂ))) =
            ∫ t in Set.Ioc (0 : ℝ) 1,
              bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u (1 : ℂ)) := by
      refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioc (0 : ℝ) 1) measurableSet_Ioc ?_
      intro t ht
      exact hRight_point t ht.1
    have hJ4_shift :
        (∫ t in Set.Ioi (1 : ℝ),
              bContourIntegrandT u ((1 : ℂ) + I * (t : ℂ))) =
            ∫ t in Set.Ioi (1 : ℝ),
              bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u (1 : ℂ)) := by
      refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (1 : ℝ)) measurableSet_Ioi ?_
      intro t ht
      exact hRight_point t (lt_trans (by norm_num) ht)
    -- Replace the shifted integrals by `VI` times constants.
    have hLeft_full :
        (∫ t in Set.Ioc (0 : ℝ) 1,
              bContourIntegrandT u ((-1 : ℂ) + I * (t : ℂ))) +
            (∫ t in Set.Ioi (1 : ℝ),
              bContourIntegrandT u ((-1 : ℂ) + I * (t : ℂ))) =
          (-VI) * bContourWeight u (-1 : ℂ) := by
      rw [hJ1_shift, hJ2_shift]
      have hsplit := hsplitW (-bContourWeight u (-1 : ℂ))
      have hmul :
          (∫ t in Set.Ioi (0 : ℝ),
              bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u (-1 : ℂ))) =
            VI * (-bContourWeight u (-1 : ℂ)) := by
        dsimp [VI]
        simpa using
          (MeasureTheory.integral_mul_const (μ := volume.restrict (Set.Ioi (0 : ℝ)))
            (r := -bContourWeight u (-1 : ℂ))
            (f := fun t : ℝ => bContourIntegrandI u (I * (t : ℂ))))
      have := hsplit.trans hmul
      -- Normalize the constant `-bContourWeight u (-1)` to match the statement.
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hRight_full :
        (∫ t in Set.Ioc (0 : ℝ) 1,
              bContourIntegrandT u ((1 : ℂ) + I * (t : ℂ))) +
            (∫ t in Set.Ioi (1 : ℝ),
              bContourIntegrandT u ((1 : ℂ) + I * (t : ℂ))) =
          (-VI) * bContourWeight u (1 : ℂ) := by
      rw [hJ3_shift, hJ4_shift]
      have hsplit := hsplitW (-bContourWeight u (1 : ℂ))
      have hmul :
          (∫ t in Set.Ioi (0 : ℝ),
              bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u (1 : ℂ))) =
            VI * (-bContourWeight u (1 : ℂ)) := by
        dsimp [VI]
        simpa using
          (MeasureTheory.integral_mul_const (μ := volume.restrict (Set.Ioi (0 : ℝ)))
            (r := -bContourWeight u (1 : ℂ))
            (f := fun t : ℝ => bContourIntegrandI u (I * (t : ℂ))))
      have := hsplit.trans hmul
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    -- Center correction: express the `S`-tail as `-I - T`.
    have hCenter :
        (∫ t in Set.Ioi (1 : ℝ),
              bContourIntegrandT u ((Complex.I : ℂ) * (t : ℂ))) +
            (∫ t in Set.Ioi (1 : ℝ),
              bContourIntegrandS u ((Complex.I : ℂ) * (t : ℂ))) =
          -(∫ t in Set.Ioi (1 : ℝ),
              bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ))) := by
      -- From `∫ S = -∫ I - ∫ T`.
      have hS := hCenter_split
      -- Add `∫ T` to both sides.
      -- `T + S = -I`.
      simpa [add_assoc, add_left_comm, add_comm] using
        congrArg
          (fun x =>
            x + (∫ t in Set.Ioi (1 : ℝ), bContourIntegrandT u ((Complex.I : ℂ) * (t : ℂ))))
          hS
    -- Replace the central `I` integral using `VI`.
    have hCenterVI :
        (∫ t in Set.Ioc (0 : ℝ) 1,
              bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ))) +
            (∫ t in Set.Ioi (1 : ℝ),
              bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ))) = VI := by
      -- This is exactly `hVI_split`, rearranged.
      simpa [add_comm, add_left_comm, add_assoc] using hVI_split.symm
    -- Final algebra step (avoid expensive normalization on large integrals).
    simp only [smul_eq_mul, neg_mul]
    -- Abbreviate the remaining integrals on the four rays and the two central pieces.
    set L0 : ℂ :=
        ∫ t in Set.Ioc (0 : ℝ) 1,
          bContourIntegrandT u ((-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) with hL0
    set L1 : ℂ :=
        ∫ t in Set.Ioi (1 : ℝ),
          bContourIntegrandT u ((-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) with hL1
    set R0 : ℂ :=
        ∫ t in Set.Ioc (0 : ℝ) 1,
          bContourIntegrandT u ((1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) with hR0
    set R1 : ℂ :=
        ∫ t in Set.Ioi (1 : ℝ),
          bContourIntegrandT u ((1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) with hR1
    set C : ℂ :=
        ∫ t in Set.Ioi (1 : ℝ),
          bContourIntegrandT u ((Complex.I : ℂ) * (t : ℂ)) with hC
    set S : ℂ :=
        ∫ t in Set.Ioi (1 : ℝ),
          bContourIntegrandS u ((Complex.I : ℂ) * (t : ℂ)) with hS
    set I0 : ℂ :=
        ∫ t in Set.Ioc (0 : ℝ) 1,
          bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ)) with hI0
    set I1 : ℂ :=
        ∫ t in Set.Ioi (1 : ℝ),
          bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ)) with hI1
    -- The `set` commands above already rewrite the goal into this abbreviated form.
    -- Rewrite the helper equalities in the abbreviated language.
    have hLeft_full' : L0 + L1 = (-VI) * bContourWeight u (-1 : ℂ) := by
      simpa [hL0, hL1] using hLeft_full
    have hRight_full' : R0 + R1 = (-VI) * bContourWeight u (1 : ℂ) := by
      simpa [hR0, hR1] using hRight_full
    have hCenter' : C + S = -I1 := by
      have h := hCenter
      -- Replace integrals by abbreviations.
      simpa [hC, hS, hI1] using h
    have hCenterVI' : I0 + I1 = VI := by
      simpa [hI0, hI1] using hCenterVI
    -- Center contribution equals `2*I*VI`.
    have hCenterTerm :
        (2 : ℂ) * (Complex.I : ℂ) * I0 + (-2 : ℂ) * (Complex.I : ℂ) * S -
              (Complex.I : ℂ) * C - (Complex.I : ℂ) * C =
          (2 : ℂ) * (Complex.I : ℂ) * VI := by
      calc
        (2 : ℂ) * (Complex.I : ℂ) * I0 + (-2 : ℂ) * (Complex.I : ℂ) * S -
              (Complex.I : ℂ) * C - (Complex.I : ℂ) * C
            =
              (2 : ℂ) * (Complex.I : ℂ) * I0 + (-2 : ℂ) * (Complex.I : ℂ) * (C + S) := by
                ring
        _ =
              (2 : ℂ) * (Complex.I : ℂ) * I0 + (2 : ℂ) * (Complex.I : ℂ) * I1 := by
                simp [hCenter']
        _ = (2 : ℂ) * (Complex.I : ℂ) * (I0 + I1) := by
              ring
        _ = (2 : ℂ) * (Complex.I : ℂ) * VI := by
              simp [hCenterVI']
    have hCenterTerm' :
        (2 * Complex.I * I0 : ℂ) + (-(2 * Complex.I * S) : ℂ) -
              (Complex.I : ℂ) * C - (Complex.I : ℂ) * C =
          (2 : ℂ) * (Complex.I : ℂ) * VI := by
      convert hCenterTerm using 1
      ring
    -- Combine the left and right contributions and finish.
    calc
      (Complex.I : ℂ) * L0 + ((Complex.I : ℂ) * L1 - (Complex.I : ℂ) * C) +
          (Complex.I : ℂ) * R0 + ((Complex.I : ℂ) * R1 - (Complex.I : ℂ) * C) +
          (2 * Complex.I * I0 : ℂ) + (-(2 * Complex.I * S) : ℂ)
          =
            (Complex.I : ℂ) * (L0 + L1) +
              (Complex.I : ℂ) * (R0 + R1) +
                ((2 : ℂ) * (Complex.I : ℂ) * I0 + (-2 : ℂ) * (Complex.I : ℂ) * S -
                  (Complex.I : ℂ) * C - (Complex.I : ℂ) * C) := by
            ring
      _ =
            (Complex.I : ℂ) * ((-VI) * bContourWeight u (-1 : ℂ)) +
              (Complex.I : ℂ) * ((-VI) * bContourWeight u (1 : ℂ)) +
              (2 : ℂ) * (Complex.I : ℂ) * VI := by
            simp [hLeft_full', hRight_full', hCenterTerm']
      _ =
          (Complex.I : ℂ) *
            (((2 : ℂ) - bContourWeight u (1 : ℂ) - bContourWeight u (-1 : ℂ)) * VI) := by
          ring
  -- Identify the exponential weights at `±1`.
  have hW1 : bContourWeight u (1 : ℂ) = Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) := by
    simp [bContourWeight, mul_left_comm, mul_comm]
  have hWm1 :
      bContourWeight u (-1 : ℂ) = Complex.exp (-(((π * u : ℝ) : ℂ) * I)) := by
    simp [bContourWeight, mul_left_comm, mul_comm]
  -- Finish by rewriting the coefficient.
  calc
    MagicFunction.b.RealIntegrals.J₁' u +
        MagicFunction.b.RealIntegrals.J₂' u +
          MagicFunction.b.RealIntegrals.J₃' u +
            MagicFunction.b.RealIntegrals.J₄' u +
              MagicFunction.b.RealIntegrals.J₅' u +
                MagicFunction.b.RealIntegrals.J₆' u =
        (Complex.I : ℂ) *
          (((2 : ℂ) - bContourWeight u (1 : ℂ) - bContourWeight u (-1 : ℂ)) * VI) :=
          hsum
    _ =
        (Complex.I : ℂ) *
          (((2 : ℂ) -
                Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) -
                Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I))) * VI) := by
          simp [hW1, hWm1, sub_eq_add_neg, add_left_comm, add_comm, mul_assoc]

end MagicFunction.g.CohnElkies.IntegralReps
