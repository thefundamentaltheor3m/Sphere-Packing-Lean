module

public import SpherePacking.MagicFunction.b.Eigenfunction.GaussianFourier
import SpherePacking.MagicFunction.b.Eigenfunction.PermJ5Integrability
import SpherePacking.ForMathlib.GaussianFourierCommon

/-!
# Perm J5

This file proves the `J₅`/`J₆` Fourier-permutation identities used in the `b`-eigenfunction
argument.
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology

open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral

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
    calc
      ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * (s ^ (-4 : ℤ) : ℂ)) *
            ((s ^ 4 : ℂ) * cexp (-π * (‖w‖ ^ 2) * s))
          = (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) *
              (((s ^ (-4 : ℤ) : ℂ) * (s ^ 4 : ℂ))) *
                cexp (-π * (‖w‖ ^ 2) * s) := by ac_rfl
      _ = (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
            rw [hcancel]; simp [mul_assoc]
  have hswap :=
    MeasureTheory.integral_integral_swap
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8)))) (ν := μs) (f := f) hint
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
      MeasureTheory.integral_const_mul, hswap]
    congr 1
    refine integral_congr_ae ((ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s hs ↦ ?_)
    simpa [f] using hinner s hs
  rw [hmain, J₆'_eq (r := ‖w‖ ^ 2),
    show (∫ s in Ici (1 : ℝ),
              (-I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) =
            -(∫ s in Ici (1 : ℝ),
              (Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s))
    from by
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
    ext
    simp [J₆, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]
  have h₅ : FT J₅ = -J₆ := by simpa [FT] using perm_J₅
  have h' : J₅ = -FT.symm J₆ := by simpa [map_neg] using congrArg FT.symm h₅
  simpa [h] using (congrArg Neg.neg h').symm

end Integral_Permutations

end

end MagicFunction.b.Fourier
