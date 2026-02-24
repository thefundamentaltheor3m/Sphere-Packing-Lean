module
public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import SpherePacking.MagicFunction.a.Eigenfunction.PermI5Integrability

/-!
# Fourier permutation for `I₅` and `I₆`

We compute the Fourier transform of `I₅` by rewriting it as an iterated integral with
`permI5Kernel` and evaluating the inner Gaussian integral. The result is the identity
`𝓕 I₅ = I₆` at the level of Schwartz maps.

## Main statements
* `perm_I₅`
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter
open SpherePacking.Integration (μIciOne)

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section PermI5

open MeasureTheory Set Complex Real

/-- Fourier transform of `I₅` is `I₆`. -/
public theorem perm_I₅ : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) I₅ = I₆ := by
  ext w
  -- Reduce to the underlying function equality `𝓕 I₅ = I₆`.
  simp only [FourierTransform.fourierCLE_apply, I₆_apply]
  -- Expand the Fourier transform as an integral and rewrite `I₅` using the change of variables.
  change 𝓕 (I₅ : ℝ⁸ → ℂ) w = _
  rw [fourier_eq' (I₅ : ℝ⁸ → ℂ) w]
  simp only [smul_eq_mul, I₅_apply]
  have hI5' (x : ℝ⁸) :
      MagicFunction.a.RealIntegrals.I₅' (‖x‖ ^ 2) =
        -2 * ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s := by
    simpa using (MagicFunction.a.IntegralEstimates.I₅.Complete_Change_of_Variables (r := ‖x‖ ^ 2))
  simp only [hI5', mul_assoc]
  -- Move the `x`-dependent phase factor inside the `s`-integral so we can use Fubini.
  let μs : Measure ℝ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))
  have hmul :
      (fun x : ℝ⁸ ↦
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s) =
        fun x : ℝ⁸ ↦
          ∫ s in Ici (1 : ℝ),
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s := by
    ext x
    -- Pull out the scalar factor (as a constant with respect to `s`).
    simpa [μs] using
      (MeasureTheory.integral_const_mul (μ := μs)
        (r := cexp (↑(-2 * (π * ⟪x, w⟫)) * I))
        (f := fun s ↦ MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s)).symm
  -- Apply Fubini to swap the order of integration.
  let f : ℝ⁸ → ℝ → ℂ := fun x s => permI5Kernel w (x, s)
  have hint : Integrable (Function.uncurry f) ((volume : Measure ℝ⁸).prod μs) := by
    simpa [f, Function.uncurry, μs, μIciOne] using (integrable_perm_I₅_kernel (w := w))
  have hswap :=
    (MeasureTheory.integral_integral_swap (μ := (volume : Measure ℝ⁸)) (ν := μs)
      (f := f) hint)
  -- Compute the inner integral using the Gaussian Fourier transform.
  have hinner (s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
      (∫ x : ℝ⁸,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s)
        =
      (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
    have hs_ne0 : (s : ℝ) ≠ 0 := ne_of_gt hs0
    have hcancel : ((s : ℂ) ^ (-4 : ℤ)) * (s ^ 4 : ℂ) = 1 :=
      zpow_neg_four_mul_pow_four (s := s) hs_ne0
    -- Factor constants from the integral, evaluate the Gaussian Fourier transform, then cancel.
    have hfactor :
        (fun x : ℝ⁸ ↦
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s) =
          fun x : ℝ⁸ ↦
            ((-I) * φ₀'' (I * s) * ((s : ℂ) ^ (-4 : ℤ))) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) := by
      funext x
      -- Unfold `g`, turn `s ^ (-4 : ℤ)` into `((s : ℂ) ^ (-4 : ℤ))`, then reassociate/commute.
      simp [MagicFunction.a.IntegralEstimates.I₅.g]
      ac_rfl
    -- Evaluate the inner integral using the Gaussian Fourier transform, then cancel `s^(-4) * s^4`.
    calc
      (∫ x : ℝ⁸,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s)
          =
          ∫ x : ℝ⁸,
            ((-I) * φ₀'' (I * s) * ((s : ℂ) ^ (-4 : ℤ))) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) := by
            exact congrArg (fun F : ℝ⁸ → ℂ => ∫ x : ℝ⁸, F x) hfactor
      _ =
          ((-I) * φ₀'' (I * s) * ((s : ℂ) ^ (-4 : ℤ))) *
            ∫ x : ℝ⁸,
              cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s) := by
            exact
              (MeasureTheory.integral_const_mul
                (μ := (volume : Measure ℝ⁸))
                (r := ((-I) * φ₀'' (I * s) * ((s : ℂ) ^ (-4 : ℤ))))
                (f := fun x : ℝ⁸ ↦
                  cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)))
      _ =
          ((-I) * φ₀'' (I * s) * ((s : ℂ) ^ (-4 : ℤ))) *
            ((s ^ 4 : ℂ) * cexp (-π * (‖w‖ ^ 2) * s)) := by
            rw [integral_phase_gaussian (w := w) (s := s) hs0]
      _ = (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
            calc
              ((-I) * φ₀'' (I * s) * ((s : ℂ) ^ (-4 : ℤ))) *
                  ((s ^ 4 : ℂ) * cexp (-π * (‖w‖ ^ 2) * s))
                  =
                  (-I) * φ₀'' (I * s) *
                    (((s : ℂ) ^ (-4 : ℤ)) * (s ^ 4 : ℂ)) *
                      cexp (-π * (‖w‖ ^ 2) * s) := by
                        ac_rfl
              _ = (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
                    rw [hcancel]
                    simp [mul_assoc]
  -- Put everything together and match the definition of `I₆'`.
  have hpull2 :
      (∫ x : ℝ⁸,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              (-2 * ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s)) =
        (-2 : ℂ) *
          ∫ x : ℝ⁸,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s := by
    calc
      (∫ x : ℝ⁸,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              (-2 * ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s))
          =
          ∫ x : ℝ⁸,
            (-2 : ℂ) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s) := by
            refine MeasureTheory.integral_congr_ae ?_
            refine ae_of_all _ ?_
            intro x
            ring_nf
      _ =
          (-2 : ℂ) *
            ∫ x : ℝ⁸,
              cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s :=
            integral_const_mul (-2) _
  have htoIter :
      (∫ x : ℝ⁸,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s) =
        ∫ x : ℝ⁸,
          ∫ s in Ici (1 : ℝ),
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s :=
    congrArg (fun F : ℝ⁸ → ℂ => ∫ x : ℝ⁸, F x) hmul
  have hswap' :
      (∫ x : ℝ⁸, ∫ s in Ici (1 : ℝ), f x s) =
        ∫ s in Ici (1 : ℝ), ∫ x : ℝ⁸, f x s := by
    simpa [μs] using hswap
  have hAE :
      (fun s : ℝ ↦ ∫ x : ℝ⁸, f x s) =ᵐ[μs]
        fun s : ℝ ↦ (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
    intro s hs
    simpa [f, permI5Kernel, permI5Phase] using hinner s hs
  have hintEq :
      (∫ s in Ici (1 : ℝ), ∫ x : ℝ⁸, f x s) =
        ∫ s in Ici (1 : ℝ), (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
    simpa [μs] using (MeasureTheory.integral_congr_ae hAE)
  have hconst_mul (c : ℂ) :
      (∫ s in Ici (1 : ℝ), c * (φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s))) =
        c * ∫ s in Ici (1 : ℝ), φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
    have hexp (s : ℝ) :
        cexp (-((π : ℂ) * (((‖w‖ : ℂ) ^ (2 : ℕ)) * (s : ℂ)))) =
          cexp (-(π : ℂ) * ((‖w‖ : ℂ) ^ (2 : ℕ)) * (s : ℂ)) := by
      refine congrArg cexp ?_
      calc
        -((π : ℂ) * (((‖w‖ : ℂ) ^ (2 : ℕ)) * (s : ℂ))) =
            (-(π : ℂ)) * (((‖w‖ : ℂ) ^ (2 : ℕ)) * (s : ℂ)) := by
              simp
        _ = (-(π : ℂ)) * ((‖w‖ : ℂ) ^ (2 : ℕ)) * (s : ℂ) := by
            simp [mul_assoc]
    simpa [μs, mul_assoc, neg_mul, hexp] using
      (MeasureTheory.integral_const_mul (μ := μs)
        (r := c)
        (f := fun s : ℝ ↦ φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s)))
  have hpull :
      (∫ s in Ici (1 : ℝ), (-I) * (φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s))) =
        (-I) *
          ∫ s in Ici (1 : ℝ), φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
    simpa using (hconst_mul (-I))
  have hpush :
      (∫ s in Ici (1 : ℝ), I * (φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s))) =
        I * ∫ s in Ici (1 : ℝ), φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
    simpa using (hconst_mul I)
  calc
    (∫ x : ℝ⁸,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            (-2 * ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s))
        =
        (-2 : ℂ) *
          ∫ x : ℝ⁸,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s := hpull2
    _ =
        (-2 : ℂ) *
          ∫ x : ℝ⁸,
            ∫ s in Ici (1 : ℝ),
              cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s := by
          exact congrArg (fun z : ℂ => (-2 : ℂ) * z) htoIter
    _ =
        (-2 : ℂ) *
          ∫ x : ℝ⁸, ∫ s in Ici (1 : ℝ), f x s := by
          simp [f, permI5Kernel, permI5Phase]
    _ =
        (-2 : ℂ) *
          ∫ s in Ici (1 : ℝ), ∫ x : ℝ⁸, f x s := by
          exact congrArg (fun z : ℂ => (-2 : ℂ) * z) hswap'
    _ =
        (-2 : ℂ) *
          ∫ s in Ici (1 : ℝ), (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
          exact congrArg (fun z : ℂ => (-2 : ℂ) * z) hintEq
    _ = 2 * ∫ s in Ici (1 : ℝ), I * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
          have hconst : ((-2 : ℂ) * (-I : ℂ)) = (2 : ℂ) * (I : ℂ) := by
            ring_nf
          calc
            (-2 : ℂ) * ∫ s in Ici (1 : ℝ), (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s)
                =
                (-2 : ℂ) *
                  ((-I : ℂ) *
                    ∫ s in Ici (1 : ℝ),
                      φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s)) := by
                  -- pull `(-I)` out of the integral, without rewriting the exponential argument
                  have hrew :
                      (∫ s in Ici (1 : ℝ), (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s)) =
                        ∫ s in Ici (1 : ℝ), (-I) * (φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s)) := by
                        simp [mul_assoc]
                  rw [hrew, hconst_mul]
            _ =
                (2 : ℂ) *
                  ((I : ℂ) *
                    ∫ s in Ici (1 : ℝ),
                      φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s)) := by
                  calc
                    (-2 : ℂ) *
                        ((-I : ℂ) *
                          ∫ s in Ici (1 : ℝ),
                            φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s))
                        =
                        ((-2 : ℂ) * (-I : ℂ)) *
                          ∫ s in Ici (1 : ℝ), φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
                          ac_rfl
                    _ =
                        ((2 : ℂ) * (I : ℂ)) *
                          ∫ s in Ici (1 : ℝ), φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
                          simp [hconst]
                    _ =
                        (2 : ℂ) * ((I : ℂ) *
                          ∫ s in Ici (1 : ℝ), φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s)) := by
                          ac_rfl
            _ = 2 * ∫ s in Ici (1 : ℝ), I * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
                  -- push `I` back into the integral
                  rw [hpush.symm]
                  simp [mul_assoc]
    _ = MagicFunction.a.RealIntegrals.I₆' (‖w‖ ^ 2) := by
          simp [MagicFunction.a.RadialFunctions.I₆'_eq, mul_assoc, mul_comm]

end Integral_Permutations.PermI5
end
end MagicFunction.a.Fourier
