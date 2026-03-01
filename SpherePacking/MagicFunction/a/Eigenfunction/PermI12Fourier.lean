module
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI12Prelude
public import SpherePacking.Contour.Segments
public import SpherePacking.Integration.Measure
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import Mathlib.Tactic.Ring.RingNF


/-!
# Fourier kernels for `I₁` and `I₂`

We introduce the product-measure kernels used to express the Fourier transforms of `I₁` and `I₂`
as iterated integrals, and record their measurability.

## Main definitions
* `permI1Kernel`
* `permI2Kernel`

## Main statements
* `permI1Kernel_measurable`
* `permI2Kernel_measurable`
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section PermI12Fourier

open MeasureTheory Set Complex Real
open SpherePacking.Integration
open SpherePacking.Contour
open scoped Interval

/-- The kernel used to rewrite `𝓕 I₁` as an integral over `x` and the segment parameter `t`. -/
@[expose] public def permI1Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    (EuclideanSpace ℝ (Fin 8)) × ℝ → ℂ := fun p =>
  let x : EuclideanSpace ℝ (Fin 8) := p.1
  let t : ℝ := p.2
  cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
    ((I : ℂ) * MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₁line t))

/-- The kernel used to rewrite `𝓕 I₂` as an integral over `x` and the segment parameter `t`. -/
@[expose] public def permI2Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    (EuclideanSpace ℝ (Fin 8)) × ℝ → ℂ := fun p =>
  let x : EuclideanSpace ℝ (Fin 8) := p.1
  let t : ℝ := p.2
  cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
    MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₂line t)

/-- Measurability of `permI1Kernel` with respect to the product measure `volume × μIoc01`. -/
public lemma permI1Kernel_measurable (w : EuclideanSpace ℝ (Fin 8)) :
    AEStronglyMeasurable (permI1Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod (μIoc01)) := by
  -- Work with the restricted product measure on `univ ×ˢ Ioc 0 1`.
  have hμ :
      ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) =
        (((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod (volume : Measure ℝ)).restrict
          (univ ×ˢ Ioc (0 : ℝ) 1)) := by
    simpa using
      (SpherePacking.Integration.prod_muIoc01_eq_restrict
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8)))))
  have hcont_z₁line : Continuous z₁line := by
    simpa using SpherePacking.Contour.continuous_z₁line
  have hcont : ContinuousOn (permI1Kernel w) (univ ×ˢ Ioc (0 : ℝ) 1) := by
    intro p hp
    have ht : p.2 ∈ Ioc (0 : ℝ) 1 := (Set.mem_prod.mp hp).2
    have htpos : 0 < p.2 := ht.1
    have hz_add1 (t : ℝ) : z₁line t + 1 = (I : ℂ) * (t : ℂ) := by
      simp
    have hden : (z₁line p.2 + 1) ≠ 0 := by
      have htne : (p.2 : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt htpos)
      have hI : (I : ℂ) ≠ 0 := by simp
      simpa [hz_add1] using mul_ne_zero hI htne
    have him_pos : 0 < (z₁line p.2 + 1).im := by
      -- `z₁line t + 1 = I*t`, so the imaginary part is `t`.
      simpa [hz_add1] using htpos
    have harg_pos : 0 < (-1 / (z₁line p.2 + 1)).im :=
      neg_one_div_im_pos (z₁line p.2 + 1) him_pos
    have hφ :
        ContinuousAt (fun z : ℂ => φ₀'' z) (-1 / (z₁line p.2 + 1)) := by
      have hzmem : (-1 / (z₁line p.2 + 1)) ∈ UpperHalfPlane.upperHalfPlaneSet := by
        simpa [UpperHalfPlane.upperHalfPlaneSet] using harg_pos
      have hdiff :
          DifferentiableAt ℂ φ₀'' (-1 / (z₁line p.2 + 1)) := by
        have hdiffOn := MagicFunction.a.ComplexIntegrands.φ₀''_holo
        exact hdiffOn.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hzmem)
      exact hdiff.continuousAt
    have hmap :
        ContinuousAt (fun t : ℝ => (-1 : ℂ) / (z₁line t + 1)) p.2 := by
      have hnum : ContinuousAt (fun _ : ℝ => (-1 : ℂ)) p.2 := continuousAt_const
      have hdenom : ContinuousAt (fun t : ℝ => z₁line t + 1) p.2 :=
        (hcont_z₁line.continuousAt (x := p.2)).add continuousAt_const
      exact ContinuousAt.div hnum hdenom (by simpa using hden)
    have hφcomp :
        ContinuousAt (fun t : ℝ => φ₀'' ((-1 : ℂ) / (z₁line t + 1))) p.2 := by
      simpa [Function.comp] using
        (ContinuousAt.comp (f := fun t : ℝ => (-1 : ℂ) / (z₁line t + 1)) (x := p.2) hφ hmap)
    have hkernel : ContinuousAt (permI1Kernel w) p := by
      dsimp [permI1Kernel]
      have hphase :
          ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
              cexp (↑(-2 * (π * ⟪q.1, w⟫)) * I)) p := by
        fun_prop
      have hrest :
          ContinuousAt
            (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
              (I : ℂ) * MagicFunction.a.ComplexIntegrands.Φ₁' (‖q.1‖ ^ 2) (z₁line q.2))
            p := by
        have hI : ContinuousAt (fun _ : (EuclideanSpace ℝ (Fin 8)) × ℝ => (I : ℂ)) p :=
          continuousAt_const
        have hz₁ : ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => z₁line q.2) p := by
          simpa [Function.comp] using
            ((hcont_z₁line.continuousAt (x := p.2)).comp continuousAt_snd)
        have hz₁_add1 :
            ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => z₁line q.2 + 1) p :=
          hz₁.add continuousAt_const
        have hpow :
            ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => (z₁line q.2 + 1) ^ (2 : ℕ)) p :=
          hz₁_add1.pow 2
        have hφterm' :
            ContinuousAt
              (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
                φ₀'' ((-1 : ℂ) / (z₁line q.2 + 1)))
              p := by
          simpa [Function.comp] using
            (ContinuousAt.comp (f := fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => q.2) (x := p)
              (g := fun t : ℝ => φ₀'' ((-1 : ℂ) / (z₁line t + 1))) hφcomp continuousAt_snd)
        have hnormSqR :
            ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => (‖q.1‖ ^ 2 : ℝ)) p := by
          fun_prop
        have hnormSqC :
            ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => ((‖q.1‖ ^ 2 : ℝ) : ℂ)) p :=
          (Complex.continuous_ofReal.continuousAt.comp hnormSqR)
        have hmul :
            ContinuousAt
              (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
                (π : ℂ) * I * ((‖q.1‖ ^ 2 : ℝ) : ℂ) * (z₁line q.2 : ℂ))
              p :=
          ((continuousAt_const.mul continuousAt_const).mul hnormSqC).mul hz₁
        have hexp :
            ContinuousAt
              (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
                cexp ((π : ℂ) * I * ((‖q.1‖ ^ 2 : ℝ) : ℂ) * (z₁line q.2 : ℂ)))
              p :=
          hmul.cexp
        -- Assemble `Φ₁'` from continuous factors.
        have hΦ :
            ContinuousAt
              (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
                MagicFunction.a.ComplexIntegrands.Φ₁' (‖q.1‖ ^ 2) (z₁line q.2))
              p := by
          dsimp [MagicFunction.a.ComplexIntegrands.Φ₁']
          exact (hφterm'.mul hpow).mul hexp
        exact hI.mul hΦ
      exact hphase.mul hrest
    exact hkernel.continuousWithinAt
  have hs : MeasurableSet (Set.univ : Set (EuclideanSpace ℝ (Fin 8))) := MeasurableSet.univ
  have ht : MeasurableSet (Ioc (0 : ℝ) 1) := measurableSet_Ioc
  have hmeas :
      AEStronglyMeasurable (permI1Kernel w)
        (((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod (volume : Measure ℝ)).restrict
          (univ ×ˢ Ioc (0 : ℝ) 1)) := by
    exact ContinuousOn.aestronglyMeasurable hcont (hs.prod ht)
  -- Rewrite the measure to `volume.prod μIoc01`.
  simpa [hμ] using hmeas

/-- Measurability of `permI2Kernel` with respect to the product measure `volume × μIoc01`. -/
public lemma permI2Kernel_measurable (w : EuclideanSpace ℝ (Fin 8)) :
    AEStronglyMeasurable (permI2Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod (μIoc01)) := by
  -- Work with the restricted product measure on `univ ×ˢ Ioc 0 1`.
  have hμ :
      ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) =
        (((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod (volume : Measure ℝ)).restrict
          (univ ×ˢ Ioc (0 : ℝ) 1)) := by
    simpa using
      (SpherePacking.Integration.prod_muIoc01_eq_restrict
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8)))))
  have hcont_z₂line : Continuous z₂line := by
    simpa using SpherePacking.Contour.continuous_z₂line
  have hcont : ContinuousOn (permI2Kernel w) (univ ×ˢ Ioc (0 : ℝ) 1) := by
    intro p hp
    have hp2 : p.2 ∈ Ioc (0 : ℝ) 1 := (Set.mem_prod.mp hp).2
    have hden : ((p.2 : ℂ) + I) ≠ 0 := by
      intro h
      have him1 : (((p.2 : ℂ) + I).im) = (1 : ℝ) := by simp
      have him0 : (((p.2 : ℂ) + I).im) = (0 : ℝ) := by
        simpa using congrArg Complex.im h
      have : (1 : ℝ) = 0 := him1.symm.trans him0
      exact one_ne_zero this
    have him_pos : 0 < ((p.2 : ℂ) + I).im := by simp
    have harg_pos : 0 < (-1 / ((p.2 : ℂ) + I)).im := neg_one_div_im_pos ((p.2 : ℂ) + I) him_pos
    have hφ :
        ContinuousAt (fun z : ℂ => φ₀'' z) (-1 / ((p.2 : ℂ) + I)) := by
      -- `φ₀''` is holomorphic on the upper half-plane, hence continuous there.
      have hzmem : (-1 / ((p.2 : ℂ) + I)) ∈ UpperHalfPlane.upperHalfPlaneSet := by
        simpa [UpperHalfPlane.upperHalfPlaneSet] using harg_pos
      have hdiff :
          DifferentiableAt ℂ φ₀'' (-1 / ((p.2 : ℂ) + I)) := by
        have hdiffOn := MagicFunction.a.ComplexIntegrands.φ₀''_holo
        -- `φ₀''_holo` is `DifferentiableOn`, so use openness of the upper half-plane.
        exact hdiffOn.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hzmem)
      exact hdiff.continuousAt
    have hmap :
        ContinuousAt (fun t : ℝ => (-1 : ℂ) / ((t : ℂ) + I)) p.2 := by
      have hden' : ((p.2 : ℂ) + I) ≠ 0 := hden
      -- `t ↦ (t : ℂ) + I` is continuous, and the denominator never vanishes at `p.2`.
      have hnum : ContinuousAt (fun _ : ℝ => (-1 : ℂ)) p.2 := continuousAt_const
      have hdenom : ContinuousAt (fun t : ℝ => ((t : ℂ) + I)) p.2 := by fun_prop
      exact ContinuousAt.div hnum hdenom (by simpa using hden')
    have hφcomp :
        ContinuousAt (fun t : ℝ => φ₀'' ((-1 : ℂ) / ((t : ℂ) + I))) p.2 :=
      by
        simpa [Function.comp] using
          (ContinuousAt.comp (f := fun t : ℝ => (-1 : ℂ) / ((t : ℂ) + I)) (x := p.2) hφ hmap)
    -- Assemble continuity of the whole kernel.
    have hkernel : ContinuousAt (permI2Kernel w) p := by
      -- Expand the definition so `fun_prop` can use the continuity facts above.
      dsimp [permI2Kernel]
      have hphase :
          ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
              cexp (↑(-2 * (π * ⟪q.1, w⟫)) * I)) p := by
        fun_prop
      have hrest :
          ContinuousAt
            (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
              MagicFunction.a.ComplexIntegrands.Φ₁' (‖q.1‖ ^ 2) (z₂line q.2))
            p := by
              have hz_add' (t : ℝ) : z₂line t + 1 = (t : ℂ) + I := by
                simpa using (SpherePacking.Contour.z₂line_add_one (t := t))
              have hφterm' :
                  ContinuousAt
                    (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
                      φ₀'' ((-1 : ℂ) / ((q.2 : ℂ) + I)))
                    p := by
                -- this depends only on `q.2`
                simpa [Function.comp] using
                  (ContinuousAt.comp (f := fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => q.2) (x := p)
                    (g := fun t : ℝ => φ₀'' ((-1 : ℂ) / ((t : ℂ) + I))) hφcomp
                    continuousAt_snd)
              have hφterm :
                  ContinuousAt
                    (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => φ₀'' (-1 / (z₂line q.2 + 1)))
                    p := by
                have hfun :
                    (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
                        φ₀'' ((-1 : ℂ) / ((q.2 : ℂ) + I))) =
                      fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => φ₀'' (-1 / (z₂line q.2 + 1)) := by
                  funext q
                  have hden : (-1 : ℂ) + ((↑q.2 : ℂ) + (I + 1)) = (↑q.2 : ℂ) + I := by
                    ring
                  simp [SpherePacking.Contour.z₂line, add_assoc, hden]
                simpa [hfun] using hφterm'
              -- Now prove continuity of the remaining factors directly.
              have hz₂ : ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => z₂line q.2) p := by
                simpa [Function.comp] using
                  ((hcont_z₂line.continuousAt (x := p.2)).comp continuousAt_snd)
              have hz₂_add1 :
                  ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => z₂line q.2 + 1) p :=
                hz₂.add continuousAt_const
              have hpow :
                  ContinuousAt
                    (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => (z₂line q.2 + 1) ^ (2 : ℕ)) p :=
                hz₂_add1.pow 2
              have hnormSqR :
                  ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => (‖q.1‖ ^ 2 : ℝ)) p := by
                fun_prop
              have hnormSqC :
                  ContinuousAt
                    (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => ((‖q.1‖ ^ 2 : ℝ) : ℂ)) p :=
                (Complex.continuous_ofReal.continuousAt.comp hnormSqR)
              have hmul :
                  ContinuousAt
                    (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
                      (π : ℂ) * I * ((‖q.1‖ ^ 2 : ℝ) : ℂ) * (z₂line q.2 : ℂ))
                    p := by
                exact ((continuousAt_const.mul continuousAt_const).mul hnormSqC).mul hz₂
              have hexp :
                  ContinuousAt
                    (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
                      cexp ((π : ℂ) * I * ((‖q.1‖ ^ 2 : ℝ) : ℂ) * (z₂line q.2 : ℂ)))
                    p :=
                hmul.cexp
              -- Assemble `Φ₁'` from continuous factors.
              dsimp [MagicFunction.a.ComplexIntegrands.Φ₁']
              exact (hφterm.mul hpow).mul hexp
      exact hphase.mul hrest
    exact hkernel.continuousWithinAt
  have hs : MeasurableSet (Set.univ : Set (EuclideanSpace ℝ (Fin 8))) := MeasurableSet.univ
  have ht : MeasurableSet (Ioc (0 : ℝ) 1) := measurableSet_Ioc
  have hmeas :
      AEStronglyMeasurable (permI2Kernel w)
        (((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod (volume : Measure ℝ)).restrict
          (univ ×ˢ Ioc (0 : ℝ) 1)) := by
    exact ContinuousOn.aestronglyMeasurable hcont (hs.prod ht)
  -- Rewrite the measure to `volume.prod μIoc01`.
  simpa [hμ] using hmeas

end Integral_Permutations.PermI12Fourier
end
end MagicFunction.a.Fourier
