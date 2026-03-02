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
  -- Rewrite `J₅'` using the `t ↦ 1/t` substitution.
  have hJ5' (x : EuclideanSpace ℝ (Fin 8)) :
      MagicFunction.b.RealIntegrals.J₅' (‖x‖ ^ 2) =
        (-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s := by
    simpa using (J5Change.Complete_Change_of_Variables (r := (‖x‖ ^ 2)))
  simp only [hJ5', mul_assoc]
  -- Move the `x`-dependent phase factor inside the `s`-integral so we can use Fubini.
  let μs : Measure ℝ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))
  have hmul :
      (fun x : EuclideanSpace ℝ (Fin 8) ↦
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) =
        fun x : EuclideanSpace ℝ (Fin 8) ↦
          ∫ s in Ici (1 : ℝ),
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              J5Change.g (‖x‖ ^ 2) s := by
    ext x
    simpa [μs] using
      (MeasureTheory.integral_const_mul (μ := μs)
        (r := cexp (↑(-2 * (π * ⟪x, w⟫)) * I))
        (f := fun s ↦ J5Change.g (‖x‖ ^ 2) s)).symm
  -- Apply Fubini to swap the order of integration.
  let f : (EuclideanSpace ℝ (Fin 8)) → ℝ → ℂ := fun x s ↦ PermJ5.kernel w (x, s)
  have hint : Integrable (Function.uncurry f)
      ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μs) := by
    have hint' :
        Integrable (PermJ5.kernel w) ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μs) := by
      simpa [μs, SpherePacking.Integration.μIciOne] using (PermJ5.integrable_kernel (w := w))
    simpa [f, Function.uncurry] using hint'
  have hswap :=
    MeasureTheory.integral_integral_swap
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8)))) (ν := μs) (f := f) hint
  -- Compute the inner integral using the Gaussian Fourier transform.
  have hinner (s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
      (∫ x : EuclideanSpace ℝ (Fin 8), f x s)
        =
      (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
    have hs_ne0 : s ≠ 0 := ne_of_gt hs0
    have hcancel : (s : ℂ) ^ (-4 : ℤ) * (s : ℂ) ^ (4 : ℕ) = 1 := by
      simpa [Complex.ofReal_zpow] using
        (PermJ5.zpow_neg_four_mul_pow_four (s := s) hs_ne0)
    have hfactor :
        (fun x : EuclideanSpace ℝ (Fin 8) ↦ f x s) =
          fun x : EuclideanSpace ℝ (Fin 8) ↦
            ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * (s ^ (-4 : ℤ) : ℂ)) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) := by
      funext x
      dsimp [f, PermJ5.kernel, J5Change.g]
      simp
      ac_rfl
    calc
      (∫ x : EuclideanSpace ℝ (Fin 8), f x s) =
          ∫ x : EuclideanSpace ℝ (Fin 8),
            ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * (s ^ (-4 : ℤ) : ℂ)) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) :=
            congrArg (fun F : EuclideanSpace ℝ (Fin 8) → ℂ => ∫ x, F x) hfactor
      _ =
          ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * (s ^ (-4 : ℤ) : ℂ)) *
            ∫ x : EuclideanSpace ℝ (Fin 8),
              cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s) := by
            exact MeasureTheory.integral_const_mul (-I * ψS' (I * ↑s) * ↑s ^ (-4)) fun a =>
              cexp (↑(-2 * (π * ⟪a, w⟫)) * I) * cexp (-↑π * ↑‖a‖ ^ 2 / ↑s)
      _ =
          ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * (s ^ (-4 : ℤ) : ℂ)) *
            ((s ^ 4 : ℂ) * cexp (-π * (‖w‖ ^ 2) * s)) := by
            rw [SpherePacking.ForMathlib.integral_phase_gaussian_even
              (k := 4) (w := w) (s := s) hs0]
      _ = (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
            calc
              ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * (s ^ (-4 : ℤ) : ℂ)) *
                    ((s ^ 4 : ℂ) * cexp (-π * (‖w‖ ^ 2) * s))
                  =
                  (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) *
                    (((s ^ (-4 : ℤ) : ℂ) * (s ^ 4 : ℂ))) *
                      cexp (-π * (‖w‖ ^ 2) * s) := by
                        ac_rfl
              _ = (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
                    rw [hcancel]
                    simp [mul_assoc]
  have htoIter :
      (∫ x : EuclideanSpace ℝ (Fin 8),
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) =
        ∫ x : EuclideanSpace ℝ (Fin 8),
          ∫ s in Ici (1 : ℝ), f x s := by
    simpa [f, PermJ5.kernel] using
      congrArg (fun F : EuclideanSpace ℝ (Fin 8) → ℂ => ∫ x, F x) hmul
  have hswap' :
      (∫ x : EuclideanSpace ℝ (Fin 8), ∫ s in Ici (1 : ℝ), f x s) =
        ∫ s in Ici (1 : ℝ), ∫ x : EuclideanSpace ℝ (Fin 8), f x s := by
    simpa [μs] using hswap
  have hAE :
      (fun s : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 8), f x s) =ᵐ[μs]
        fun s : ℝ ↦ (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
    intro s hs
    simpa [f] using hinner s hs
  have hintEq :
      (∫ s in Ici (1 : ℝ), ∫ x : EuclideanSpace ℝ (Fin 8), f x s) =
        ∫ s in Ici (1 : ℝ), (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
    simpa [μs] using (MeasureTheory.integral_congr_ae hAE)
  -- Finish: match `-J₆`.
  have hmain :
      (∫ x : EuclideanSpace ℝ (Fin 8),
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s))
        =
        (-2 : ℂ) *
          ∫ s in Ici (1 : ℝ),
            (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
    -- Pull out the scalar `(-2)` and then apply Fubini + the computed inner integral.
    have hpull :
        (∫ x : EuclideanSpace ℝ (Fin 8),
              cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s)) =
          (-2 : ℂ) *
            (∫ x : EuclideanSpace ℝ (Fin 8),
                cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                  ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) := by
      -- Rewrite the integrand as `(-2) * (phase * inner)` and use linearity.
      have hfun :
          (fun x : EuclideanSpace ℝ (Fin 8) ↦
              cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s)) =
            fun x : EuclideanSpace ℝ (Fin 8) ↦
              (-2 : ℂ) *
                (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                  ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) := by
        funext x
        ac_rfl
      calc
        (∫ x : EuclideanSpace ℝ (Fin 8),
              cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s))
            = ∫ x : EuclideanSpace ℝ (Fin 8),
                (-2 : ℂ) *
                  (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                    ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) :=
          congrArg (fun F : EuclideanSpace ℝ (Fin 8) → ℂ => ∫ x, F x) hfun
        _ = (-2 : ℂ) *
              (∫ x : EuclideanSpace ℝ (Fin 8),
                cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                  ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) :=
          MeasureTheory.integral_const_mul (-2) fun a =>
            cexp (↑(-2 * (π * ⟪a, w⟫)) * I) * ∫ (s : ℝ) in Ici 1, J5Change.g (‖a‖ ^ 2) s
    calc
      (∫ x : EuclideanSpace ℝ (Fin 8),
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s))
          = (-2 : ℂ) *
              (∫ x : EuclideanSpace ℝ (Fin 8),
                cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                  ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) := hpull
      _ = (-2 : ℂ) * (∫ x : EuclideanSpace ℝ (Fin 8), ∫ s in Ici (1 : ℝ), f x s) := by
            rw [htoIter]
      _ = (-2 : ℂ) * (∫ s in Ici (1 : ℝ), ∫ x : EuclideanSpace ℝ (Fin 8), f x s) := by
            rw [hswap']
      _ = (-2 : ℂ) *
            ∫ s in Ici (1 : ℝ), (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) *
              cexp (-π * (‖w‖ ^ 2) * s) := by
            rw [hintEq]
  -- Compare the computed `s`-integral with the explicit representation of `J₆'`.
  rw [hmain, J₆'_eq (r := ‖w‖ ^ 2)]
  have h :
      (∫ s in Ici (1 : ℝ),
            (-I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) =
        -(∫ s in Ici (1 : ℝ),
              (Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) := by
    have hneg :
        (fun s : ℝ ↦
            (-I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) =
          fun s : ℝ ↦
            -((Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) := by
      funext s; ring
    calc
      (∫ s in Ici (1 : ℝ),
            (-I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) =
          ∫ s in Ici (1 : ℝ),
            -((Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) := by
            exact congrArg (fun F : ℝ → ℂ => ∫ s in Ici (1 : ℝ), F s) hneg
      _ = -(∫ s in Ici (1 : ℝ),
              (Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) :=
            (MeasureTheory.integral_neg (μ := (volume : Measure ℝ).restrict (Ici (1 : ℝ)))
                (f := fun s : ℝ ↦
                  (Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) *
                    cexp (-π * (‖w‖ ^ 2) * s)))
  rw [h]
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
