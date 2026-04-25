module
import SpherePacking.MagicFunction.g.CohnElkies.Defs
import SpherePacking.MagicFunction.g.CohnElkies.IntegralPieces
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceLemmas
import SpherePacking.MagicFunction.g.CohnElkies.IntegralReductions
import SpherePacking.MagicFunction.g.CohnElkies.DeltaBounds
public import SpherePacking.MagicFunction.b.Psi
import SpherePacking.MagicFunction.b.PsiBounds
import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay
import Mathlib.MeasureTheory.Integral.ExpDecay


/-!
# Laplace integral for `b'`

This file defines the Laplace integrand `bLaplaceIntegrand` and proves its convergence on
`(0, ∞)` for `u > 2`.

These lemmas are used in the blueprint proposition `prop:b-double-zeros` (the main statement is
`bRadial_eq_laplace_psiI_main`).

## Main definitions
* `MagicFunction.g.CohnElkies.IntegralReps.bLaplaceIntegrand`

## Main statements
* `MagicFunction.g.CohnElkies.IntegralReps.bLaplaceIntegral_convergent`
-/


namespace MagicFunction.g.CohnElkies.IntegralReps

noncomputable section

open scoped BigOperators Topology UpperHalfPlane
open MeasureTheory Real Complex Filter
open UpperHalfPlane
open MagicFunction.FourierEigenfunctions

/-- The Laplace integrand appearing in the representation of the radial profile `b'`. -/
@[expose] public def bLaplaceIntegrand (u t : ℝ) : ℂ :=
  ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)

lemma ψI_apply_eq_factor (z : ℍ) :
    ψI z =
      (1 / 2 : ℂ) *
        (H₄ z ^ (3 : ℕ) *
          (2 * H₄ z ^ (2 : ℕ) + 5 * H₄ z * H₂ z + 5 * H₂ z ^ (2 : ℕ))) / (Δ z) := by
  have hJ : H₃ z = H₂ z + H₄ z := by
    simpa using congrArg (fun f : ℍ → ℂ => f z) jacobi_identity.symm
  have hψI0 :
      ψI z =
        (128 : ℂ) * ((H₃ z + H₄ z) / (H₂ z) ^ (2 : ℕ)) +
          (128 : ℂ) * ((H₄ z - H₂ z) / (H₃ z) ^ (2 : ℕ)) := by
    simpa [Pi.smul_apply, nsmul_eq_mul] using congrArg (fun f : ℍ → ℂ => f z) ψI_eq
  have hΔ : (Δ z : ℂ) = ((H₂ z) * (H₃ z) * (H₄ z)) ^ 2 / (256 : ℂ) := by
    simpa [Delta_apply] using Delta_eq_H₂_H₃_H₄ z
  refine eq_div_of_mul_eq (by simpa [Delta_apply] using Δ_ne_zero z) ?_
  rw [hψI0, hΔ]
  field_simp [H₂_ne_zero z, H₃_ne_zero z, H₄_ne_zero z]
  simp [hJ]; ring

/-- Exponential growth bound for `ψI` on vertical rays in the upper half-plane. -/
public lemma exists_ψI_bound_exp :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖ψI z‖ ≤ C * Real.exp (2 * π * z.im) := by
  let num : ℍ → ℂ :=
    fun z : ℍ =>
      (1 / 2 : ℂ) *
        (H₄ z ^ (3 : ℕ) *
          (2 * H₄ z ^ (2 : ℕ) + 5 * H₄ z * H₂ z + 5 * H₂ z ^ (2 : ℕ)))
  have hH2 : Tendsto H₂ atImInfty (𝓝 (0 : ℂ)) := H₂_tendsto_atImInfty
  have hH4 : Tendsto H₄ atImInfty (𝓝 (1 : ℂ)) := H₄_tendsto_atImInfty
  have hpoly :
      Tendsto
        (fun z : ℍ =>
          (2 : ℂ) * H₄ z ^ (2 : ℕ) + (5 : ℂ) * (H₄ z * H₂ z) + (5 : ℂ) * H₂ z ^ (2 : ℕ))
        atImInfty (𝓝 (2 : ℂ)) := by
    simpa [mul_add, add_assoc, add_left_comm, add_comm] using
      (tendsto_const_nhds.mul (hH4.pow 2)).add
        ((tendsto_const_nhds.mul (hH4.mul hH2)).add (tendsto_const_nhds.mul (hH2.pow 2)))
  have hnum : Tendsto num atImInfty (𝓝 (1 : ℂ)) := by
    have hprod : Tendsto
            (fun z : ℍ =>
              H₄ z ^ (3 : ℕ) *
                (2 * H₄ z ^ (2 : ℕ) + 5 * H₄ z * H₂ z + 5 * H₂ z ^ (2 : ℕ)))
            atImInfty (𝓝 ((1 : ℂ) ^ (3 : ℕ) * (2 : ℂ))) := by
      simpa [mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
        (hH4.pow 3).mul hpoly
    simpa [num, show ((1 / 2 : ℂ) * ((1 : ℂ) ^ (3 : ℕ) * (2 : ℂ))) = (1 : ℂ) from by norm_num] using
      (tendsto_const_nhds (x := (1 / 2 : ℂ)) (f := atImInfty)).mul hprod
  have hEvNum : ∀ᶠ z in atImInfty, ‖num z‖ ≤ (2 : ℝ) := by
    filter_upwards [hnum.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1))]
      with z hz
    have hdist : ‖num z - (1 : ℂ)‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have htriangle : ‖num z‖ ≤ ‖num z - (1 : ℂ)‖ + ‖(1 : ℂ)‖ := by
      simpa [sub_add_cancel] using norm_add_le (num z - (1 : ℂ)) (1 : ℂ)
    nlinarith [show ‖(1 : ℂ)‖ = (1 : ℝ) by simp]
  rcases (UpperHalfPlane.atImInfty_mem _).1 (by simpa using hEvNum) with ⟨A0, hA0⟩
  rcases exists_inv_Delta_bound_exp with ⟨CΔ, AΔ, hCΔ, hΔ⟩
  refine ⟨2 * CΔ, max A0 AΔ, by positivity, fun z hz => ?_⟩
  calc ‖ψI z‖ = ‖num z‖ * ‖(Δ z)⁻¹‖ := by simp [num, ψI_apply_eq_factor, div_eq_mul_inv]
    _ ≤ (2 : ℝ) * (CΔ * Real.exp (2 * π * z.im)) :=
          mul_le_mul (hA0 z (le_trans (le_max_left _ _) hz))
            (hΔ z (le_trans (le_max_right _ _) hz)) (by positivity) (by positivity)
    _ = (2 * CΔ) * Real.exp (2 * π * z.im) := by ring

/-- Convergence of the Laplace integral defining `b'` (integrability on `(0, ∞)` for `u > 2`). -/
public lemma bLaplaceIntegral_convergent {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) := by
  have hu0 : 0 ≤ u := by linarith
  have hψI' (t : ℝ) (ht : 0 < t) :
      ψI' ((Complex.I : ℂ) * (t : ℂ)) = ψI.resToImagAxis t := by
    simp [ψI', Function.resToImagAxis, ResToImagAxis, ht]
  have hSlashS (t : ℝ) (ht : 0 < t) :
      ψI.resToImagAxis t = (-(t ^ (2 : ℕ)) : ℂ) * ψS.resToImagAxis (1 / t) := by
    simpa [zpow_two, pow_two, ψS_slash_S] using
      ResToImagAxis.SlashActionS (F := ψS) (k := (-2 : ℤ)) (t := t) ht
  rcases
      MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
    ⟨Cψ, hCψ⟩
  let Cψ0 : ℝ := max Cψ 0
  have hCψ0 : 0 ≤ Cψ0 := le_max_right _ _
  have hψS_bound (s : ℝ) (hs : 1 ≤ s) :
      ‖ψS.resToImagAxis s‖ ≤ Cψ0 * Real.exp (-π * s) :=
    (hCψ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hcontIoi : ContinuousOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) := by
    intro t ht0
    have hIm : 0 < (((Complex.I : ℂ) * (t : ℂ) : ℂ)).im := by simpa using ht0
    have hEq :
        (fun s : ℝ => bLaplaceIntegrand u s) =ᶠ[𝓝 t]
          fun s : ℝ =>
            (ψI (UpperHalfPlane.ofComplex ((Complex.I : ℂ) * (s : ℂ)))) *
              (Real.exp (-π * u * s) : ℂ) := by
      filter_upwards [lt_mem_nhds ht0] with s hs
      have hsIm : 0 < (((Complex.I : ℂ) * (s : ℂ) : ℂ)).im := by simpa using hs
      simp [bLaplaceIntegrand, ψI', UpperHalfPlane.ofComplex_apply_of_im_pos hsIm, hs]
    have hmulI : ContinuousAt (fun s : ℝ => (Complex.I : ℂ) * (s : ℂ)) t := by fun_prop
    have hof : ContinuousAt UpperHalfPlane.ofComplex ((Complex.I : ℂ) * (t : ℂ)) :=
      (UpperHalfPlane.contMDiffAt_ofComplex (n := ⊤) hIm).continuousAt
    have hof' :
        ContinuousAt (fun s : ℝ => UpperHalfPlane.ofComplex ((Complex.I : ℂ) * (s : ℂ))) t :=
      ContinuousAt.comp hof hmulI
    have hψIcomp :
        ContinuousAt
          (fun s : ℝ => ψI (UpperHalfPlane.ofComplex ((Complex.I : ℂ) * (s : ℂ)))) t :=
      ContinuousAt.comp MagicFunction.b.PsiBounds.continuous_ψI.continuousAt hof'
    have hmul : ContinuousAt
        (fun s : ℝ =>
          (ψI (UpperHalfPlane.ofComplex ((Complex.I : ℂ) * (s : ℂ)))) *
            (Real.exp (-π * u * s) : ℂ)) t := by
      simpa [mul_assoc] using hψIcomp.mul (by fun_prop :
        ContinuousAt (fun s : ℝ => (Real.exp (-π * u * s) : ℂ)) t)
    exact (hmul.congr_of_eventuallyEq hEq).continuousWithinAt
  have hint_small :
      IntegrableOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioc (0 : ℝ) 1) := by
    have hmeas : AEStronglyMeasurable (fun t : ℝ => bLaplaceIntegrand u t)
          (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      (hcontIoi.mono fun t ht => ht.1).aestronglyMeasurable measurableSet_Ioc
    have hbound :
        ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ‖bLaplaceIntegrand u t‖ ≤ Cψ0 := by
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have ht' : 1 ≤ (1 / t : ℝ) := by simpa [one_div] using (one_le_div ht0).2 ht1
      have hψS' : ‖ψS.resToImagAxis (1 / t : ℝ)‖ ≤ Cψ0 := by
        have hexp_le : Real.exp (-π * (1 / t : ℝ)) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, le_of_lt (one_div_pos.2 ht0)])
        simpa using (hψS_bound (1 / t : ℝ) ht').trans (mul_le_mul_of_nonneg_left hexp_le hCψ0)
      have ht2le : t ^ (2 : ℕ) ≤ 1 := by simpa using pow_le_one₀ (n := 2) ht0.le ht1
      have hψI : ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ ≤ Cψ0 := by
        rw [hψI' t ht0, hSlashS t ht0]
        calc ‖(-(t ^ (2 : ℕ)) : ℂ) * ψS.resToImagAxis (1 / t)‖
              = (t ^ (2 : ℕ)) * ‖ψS.resToImagAxis (1 / t)‖ := by simp
          _ ≤ 1 * Cψ0 := mul_le_mul ht2le hψS' (norm_nonneg _) zero_le_one
          _ = Cψ0 := one_mul _
      have hexp_norm : ‖(Real.exp (-π * u * t) : ℂ)‖ ≤ 1 := by
        rw [show ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) by
          simpa [Complex.ofReal_exp] using Complex.norm_exp_ofReal (-π * u * t)]
        exact Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, mul_nonneg hu0 ht0.le])
      calc ‖bLaplaceIntegrand u t‖
            = ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ * ‖(Real.exp (-π * u * t) : ℂ)‖ := by
              simp [bLaplaceIntegrand]
        _ ≤ ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ * 1 :=
              mul_le_mul_of_nonneg_left hexp_norm (norm_nonneg _)
        _ ≤ Cψ0 := by simpa using hψI
    exact IntegrableOn.of_bound measure_Ioc_lt_top hmeas Cψ0 hbound
  rcases exists_ψI_bound_exp with ⟨CI, AI, hCI, hI⟩
  let A : ℝ := max AI 1
  have hint_mid :
      IntegrableOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioc (1 : ℝ) A) :=
    ((hcontIoi.mono fun t ht => lt_of_lt_of_le (by norm_num) ht.1).integrableOn_Icc
      (μ := (volume : Measure ℝ))).mono_set Set.Ioc_subset_Icc_self
  have hint_tail :
      IntegrableOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioi A) := by
    have hmeas : AEStronglyMeasurable (fun t : ℝ => bLaplaceIntegrand u t)
          (volume.restrict (Set.Ioi A)) :=
      (hcontIoi.mono fun t ht =>
        lt_trans (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _))
          ht).aestronglyMeasurable measurableSet_Ioi
    have hdom :
        ∀ᵐ t ∂(volume.restrict (Set.Ioi A)),
          ‖bLaplaceIntegrand u t‖ ≤ ‖(CI : ℂ) * (Real.exp (-(π * (u - 2)) * t) : ℂ)‖ := by
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have htA : A ≤ t := ht.le
      have htAI : AI ≤ t := (le_max_left _ _).trans htA
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans htA)
      have htIm : 0 < (((Complex.I : ℂ) * (t : ℂ) : ℂ)).im := by simpa using ht0
      let z : ℍ := ⟨(Complex.I : ℂ) * (t : ℂ), htIm⟩
      have hψI' : ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ ≤ CI * Real.exp (2 * π * t) := by
        have hval : ψI' ((Complex.I : ℂ) * (t : ℂ)) = ψI z := by simp [ψI', ht0, z]
        simpa [hval, z, UpperHalfPlane.im] using hI z
          (by simpa [z, UpperHalfPlane.im] using htAI)
      have hcomb := MagicFunction.g.CohnElkies.exp_two_pi_mul_mul_exp_neg_pi_mul u t
      have hexp_norm : ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) := by
        simpa [Complex.ofReal_exp] using Complex.norm_exp_ofReal (-π * u * t)
      have hnormExp : ‖(Real.exp (-(π * (u - 2)) * t) : ℂ)‖ = Real.exp (-(π * (u - 2)) * t) := by
        simpa [Complex.ofReal_exp] using Complex.norm_exp_ofReal (-(π * (u - 2)) * t)
      calc ‖bLaplaceIntegrand u t‖
            = ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ * ‖(Real.exp (-π * u * t) : ℂ)‖ := by
              simp [bLaplaceIntegrand]
        _ = ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ * Real.exp (-π * u * t) := by rw [hexp_norm]
        _ ≤ (CI * Real.exp (2 * π * t)) * Real.exp (-π * u * t) :=
              mul_le_mul_of_nonneg_right hψI' (Real.exp_pos _).le
        _ = CI * Real.exp (-(π * (u - 2)) * t) := by
              simpa [mul_assoc] using congrArg (fun x : ℝ => CI * x) hcomb
        _ = ‖(CI : ℂ) * (Real.exp (-(π * (u - 2)) * t) : ℂ)‖ := by
              rw [norm_mul, show ‖(CI : ℂ)‖ = CI from by simp [abs_of_nonneg hCI.le], hnormExp]
    have hpos : 0 < π * (u - 2) := mul_pos Real.pi_pos (sub_pos.2 hu)
    have hExp : IntegrableOn (fun t : ℝ => Real.exp (-(π * (u - 2)) * t)) (Set.Ioi A) := by
      simpa [mul_assoc] using exp_neg_integrableOn_Ioi (a := A) (b := π * (u - 2)) hpos
    have hExpC :
        IntegrableOn (fun t : ℝ => (CI : ℂ) * (Real.exp (-(π * (u - 2)) * t) : ℂ)) (Set.Ioi A) := by
      simpa [IntegrableOn] using
        (show Integrable _ (volume.restrict (Set.Ioi A)) from hExp).ofReal.const_mul (CI : ℂ)
    exact MeasureTheory.Integrable.mono (μ := volume.restrict (Set.Ioi A))
      (by simpa [IntegrableOn] using hExpC) hmeas hdom
  have hUnion1 : Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) A ∪ Set.Ioi A := by
    simpa using (Set.Ioc_union_Ioi_eq_Ioi (a := (1 : ℝ)) (b := A) (le_max_right _ _)).symm
  have hint_large : IntegrableOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioi (1 : ℝ)) := by
    simpa [hUnion1] using hint_mid.union hint_tail
  rw [show Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) from by norm_num]
  exact hint_small.union hint_large

end

end MagicFunction.g.CohnElkies.IntegralReps
