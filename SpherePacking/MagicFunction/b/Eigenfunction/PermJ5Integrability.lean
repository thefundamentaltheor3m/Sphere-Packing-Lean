module
public import SpherePacking.MagicFunction.b.Eigenfunction.GaussianFourier
public import SpherePacking.MagicFunction.b.Eigenfunction.Prelude
import SpherePacking.MagicFunction.b.PsiBounds
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ6.Bounds
public import SpherePacking.ForMathlib.ExpNormSqDiv
public import SpherePacking.ForMathlib.GaussianRexpIntegral
public import SpherePacking.ForMathlib.GaussianRexpIntegrable
public import SpherePacking.Integration.Measure
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.Contour.PermJ5Kernel


/-!
# Perm J5 Integrability

This file proves integrability / measurability results for the `PermJ5` kernel, such as
`aestronglyMeasurable_kernel` and `zpow_neg_four_mul_pow_four`.
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology

open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral

namespace PermJ5

open MeasureTheory Set Complex Real
open SpherePacking.Contour

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open SpherePacking.Integration (μIciOne)

lemma continuousOn_J₅_g :
      ContinuousOn (fun p : ℝ⁸ × ℝ ↦ J5Change.g (‖p.1‖ ^ 2) p.2) (univ ×ˢ Ici (1 : ℝ)) := by
    have hψ : ContinuousOn (fun s : ℝ ↦ ψS' ((Complex.I : ℂ) * (s : ℂ))) (Ici (1 : ℝ)) := by
      refine (Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS)
        MagicFunction.b.PsiBounds.continuous_ψS).congr fun s hs => ?_
      simp [ψS', Function.resToImagAxis, ResToImagAxis, lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hs,
        mul_comm]
    have hzpow : ContinuousOn (fun s : ℝ ↦ (s : ℂ) ^ (-4 : ℤ)) (Ici (1 : ℝ)) := fun s hs => by
      have hsC : (s : ℂ) ≠ 0 := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hs).ne'
      exact ((continuousAt_zpow₀ (s : ℂ) (-4 : ℤ) (Or.inl hsC)).comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt
    have hψ' : ContinuousOn (fun p : ℝ⁸ × ℝ ↦ ψS' ((Complex.I : ℂ) * (p.2 : ℂ)))
        (univ ×ˢ Ici (1 : ℝ)) :=
      hψ.comp continuousOn_snd fun _ hp => (Set.mem_prod.mp hp).2
    have hzpow' : ContinuousOn (fun p : ℝ⁸ × ℝ ↦ (p.2 : ℂ) ^ (-4 : ℤ)) (univ ×ˢ Ici (1 : ℝ)) :=
      hzpow.comp continuousOn_snd fun _ hp => (Set.mem_prod.mp hp).2
    have hprod3 : ContinuousOn
        (fun p : ℝ⁸ × ℝ ↦ (-I : ℂ) * ψS' ((Complex.I : ℂ) * (p.2 : ℂ)) * ((p.2 : ℂ) ^ (-4 : ℤ)) *
          cexp ((-π : ℂ) * ((‖p.1‖ : ℂ) ^ 2) / (p.2 : ℂ)))
        (univ ×ˢ Ici (1 : ℝ)) :=
      ((continuousOn_const.mul hψ').mul hzpow').mul
        (SpherePacking.ForMathlib.continuousOn_exp_norm_sq_div (E := ℝ⁸))
    refine hprod3.congr fun p _ => ?_
    simp [J5Change.g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The `(x,s)`-kernel used in the `J₅`/`J₆` Fourier permutation argument. -/
@[expose] public def kernel (w : ℝ⁸) : ℝ⁸ × ℝ → ℂ :=
  fun p =>
    cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) * J5Change.g (‖p.1‖ ^ 2) p.2

lemma aestronglyMeasurable_kernel (w : ℝ⁸) :
    AEStronglyMeasurable (kernel w) ((volume : Measure ℝ⁸).prod μIciOne) := by
  have hphase : Continuous fun p : ℝ⁸ × ℝ => cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) := by fun_prop
  have hker : ContinuousOn (kernel w) (univ ×ˢ Ici (1 : ℝ)) :=
    (hphase.continuousOn.mul continuousOn_J₅_g).congr fun p _ => by simp [kernel]
  have hμ :
      ((volume : Measure ℝ⁸).prod μIciOne) =
        (((volume : Measure ℝ⁸).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ici (1 : ℝ))) := by
    simpa [μIciOne, Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ⁸)) (ν := (volume : Measure ℝ))
        (s := (univ : Set ℝ⁸)) (t := Ici (1 : ℝ)))
  simpa [hμ] using hker.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Ici)

/-- Cancellation identity `s^(-4) * s^4 = 1` (after coercions to `ℂ`). -/
public lemma zpow_neg_four_mul_pow_four (s : ℝ) (hs : s ≠ 0) :
    ((s ^ (-4 : ℤ) : ℝ) : ℂ) * (s ^ 4 : ℂ) = 1 := by
  simpa [Complex.ofReal_zpow] using (zpow_neg_mul_zpow_self (a := (s : ℂ)) (n := (4 : ℤ))
    (by exact_mod_cast hs))

lemma kernel_norm_eq (w x : ℝ⁸) (s : ℝ) :
    ‖kernel w (x, s)‖ =
      (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖) *
        rexp (-π * (‖x‖ ^ 2) / s) := by
  simpa [kernel, J5Change.g] using (permJ5_kernel_norm_eq_of (ψS' := ψS') (k := 4) w x s)

lemma integrable_kernel_slice (w : ℝ⁸) (s : ℝ) (hs : 1 ≤ s) :
    Integrable (fun x : ℝ⁸ ↦ kernel w (x, s)) (volume : Measure ℝ⁸) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hmajor :
      Integrable (fun x : ℝ⁸ ↦ (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖) *
        rexp (-π * (‖x‖ ^ 2) / s)) (volume : Measure ℝ⁸) := by
    simpa [mul_assoc] using
      (SpherePacking.ForMathlib.integrable_gaussian_rexp (s := s) hs0).const_mul
        (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖)
  have hg : Continuous fun x : ℝ⁸ => J5Change.g (‖x‖ ^ 2) s := by
    simpa [continuousOn_univ, Function.comp] using continuousOn_J₅_g.comp
      (by fun_prop : Continuous fun x : ℝ⁸ => (x, s)).continuousOn
      (show MapsTo (fun x : ℝ⁸ => (x, s)) (Set.univ : Set ℝ⁸) (univ ×ˢ Ici (1 : ℝ)) from
        fun _ _ => ⟨Set.mem_univ _, hs⟩)
  exact Integrable.mono' hmajor
    ((by fun_prop : Continuous fun x : ℝ⁸ => cexp (↑(-2 * (π * ⟪x, w⟫)) * I)).mul
      hg).aestronglyMeasurable <| .of_forall fun x =>
    le_of_eq (kernel_norm_eq (w := w) (x := x) (s := s))

/-- Integrability of `kernel w` for the product measure `volume × μIciOne`. -/
public lemma integrable_kernel (w : ℝ⁸) :
    Integrable (kernel w) ((volume : Measure ℝ⁸).prod μIciOne) := by
  haveI : MeasureTheory.SFinite μIciOne := by dsimp [μIciOne]; infer_instance
  have hmeas : AEStronglyMeasurable (kernel w) ((volume : Measure ℝ⁸).prod μIciOne) :=
    aestronglyMeasurable_kernel (w := w)
  refine (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure ℝ⁸)) (ν := μIciOne) hmeas).2
    ⟨(ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s hs =>
      integrable_kernel_slice (w := w) (s := s) hs, ?_⟩
  rcases
    MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
    ⟨C, hC⟩
  have hmajor : Integrable (fun s : ℝ ↦ C * rexp (-π * s)) μIciOne := by
    have hIci : IntegrableOn (fun s : ℝ ↦ rexp (-(π : ℝ) * s)) (Ici (1 : ℝ)) volume := by
      simpa [pow_zero, one_mul] using
        (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 0) (b := (π : ℝ))
          Real.pi_pos)
    simpa [μIciOne, IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using hIci.const_mul C
  have hmeas' : AEStronglyMeasurable (fun s : ℝ ↦ ∫ x : ℝ⁸, ‖kernel w (x, s)‖) μIciOne := by
    simpa using (hmeas.norm.prod_swap.integral_prod_right'
      (μ := μIciOne) (ν := (volume : Measure ℝ⁸)))
  refine Integrable.mono' hmajor hmeas' <| (ae_restrict_iff' measurableSet_Ici).2 <|
    .of_forall fun s hs => ?_
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hnorm : (fun x : ℝ⁸ ↦ ‖kernel w (x, s)‖) =
      fun x : ℝ⁸ ↦ (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖) *
        rexp (-π * (‖x‖ ^ 2) / s) :=
    funext fun x => kernel_norm_eq (w := w) (x := x) (s := s)
  have hval : ∫ x : ℝ⁸, ‖kernel w (x, s)‖ ≤ ‖ψS.resToImagAxis s‖ := by
    have hs_zpow_pos : 0 < s ^ (-4 : ℤ) := zpow_pos hs0 _
    have habs : ‖(s ^ (-4 : ℤ) : ℂ)‖ = s ^ (-4 : ℤ) := by
      change ‖(s : ℂ) ^ (-4 : ℤ)‖ = s ^ (-4 : ℤ)
      rw [show (s : ℂ) ^ (-4 : ℤ) = ((s ^ (-4 : ℤ) : ℝ) : ℂ) from
        (Complex.ofReal_zpow s (-4 : ℤ)).symm]
      exact (RCLike.norm_ofReal _).trans (abs_of_pos hs_zpow_pos)
    have hscal : (‖(s ^ (-4 : ℤ) : ℂ)‖) * (s ^ 4) = (1 : ℝ) := by
      rw [habs, show (s ^ (-4 : ℤ)) = (s ^ 4)⁻¹ by simpa using (zpow_negSucc s 3)]
      exact inv_mul_cancel₀ (pow_ne_zero 4 hs0.ne')
    refine le_of_eq ?_
    calc
      (∫ x : ℝ⁸, ‖kernel w (x, s)‖)
          = (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖) *
              (∫ x : ℝ⁸, rexp (-π * (‖x‖ ^ 2) / s)) := by
            rw [hnorm]; exact MeasureTheory.integral_const_mul _ _
      _ = ‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ := by
            rw [SpherePacking.ForMathlib.integral_gaussian_rexp (s := s) hs0, mul_assoc, hscal,
              mul_one]
      _ = ‖ψS.resToImagAxis s‖ :=
            congrArg norm (by simp [ψS', Function.resToImagAxis, ResToImagAxis, hs0, mul_comm])
  simpa [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ ∫ x : ℝ⁸, ‖kernel w (x, s)‖ from
    MeasureTheory.integral_nonneg fun _ => norm_nonneg _)] using hval.trans (hC s hs)

end Integral_Permutations.PermJ5
end

end MagicFunction.b.Fourier
