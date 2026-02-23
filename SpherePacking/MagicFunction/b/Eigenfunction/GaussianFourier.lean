module
public import SpherePacking.MagicFunction.b.Eigenfunction.Prelude
/-!
# Gaussian Fourier

This file contains Gaussian/Fourier lemmas used by the `b`-side permutation arguments that are
*not* already provided by the shared development in
`SpherePacking/ForMathlib/GaussianFourierCommon.lean`.
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology

open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral

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

end Integral_Permutations

end

end MagicFunction.b.Fourier
