module
public import SpherePacking.MagicFunction.b.Eigenfunction.GaussianFourier
public import SpherePacking.MagicFunction.b.Eigenfunction.Prelude
import SpherePacking.MagicFunction.b.PsiBounds
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ6.Bounds
public import SpherePacking.ForMathlib.ExpNormSqDiv
public import SpherePacking.ForMathlib.GaussianRexpIntegral
public import SpherePacking.ForMathlib.GaussianRexpIntegrable
import SpherePacking.ForMathlib.IntegralProd
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
      have hres : ContinuousOn ψS.resToImagAxis (Ici (1 : ℝ)) := by
        have hψS : Continuous ψS := MagicFunction.b.PsiBounds.continuous_ψS
        exact
          Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS) hψS
      refine hres.congr ?_
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
      simp [ψS', Function.resToImagAxis, ResToImagAxis, hs0, mul_comm]
    have hzpow : ContinuousOn (fun s : ℝ ↦ (s : ℂ) ^ (-4 : ℤ)) (Ici (1 : ℝ)) := by
      intro s hs
      have hs0 : s ≠ 0 := by
        have : (0 : ℝ) < s := lt_of_lt_of_le (by norm_num) hs
        exact ne_of_gt this
      have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
      have hzC : ContinuousAt (fun z : ℂ => z ^ (-4 : ℤ)) (s : ℂ) :=
        continuousAt_zpow₀ (s : ℂ) (-4 : ℤ) (Or.inl hsC)
      have hof : ContinuousAt (fun t : ℝ => (t : ℂ)) s := Complex.continuous_ofReal.continuousAt
      exact (hzC.comp hof).continuousWithinAt
    have hψ' :
        ContinuousOn (fun p : ℝ⁸ × ℝ ↦ ψS' ((Complex.I : ℂ) * (p.2 : ℂ)))
          (univ ×ˢ Ici (1 : ℝ)) := by
      refine hψ.comp continuousOn_snd ?_
      intro p hp
      exact (Set.mem_prod.mp hp).2
    have hzpow' :
        ContinuousOn (fun p : ℝ⁸ × ℝ ↦ (p.2 : ℂ) ^ (-4 : ℤ))
          (univ ×ˢ Ici (1 : ℝ)) := by
      refine hzpow.comp continuousOn_snd ?_
      intro p hp
      exact (Set.mem_prod.mp hp).2
    have hconst :
        ContinuousOn (fun _ : ℝ⁸ × ℝ ↦ (-I : ℂ)) (univ ×ˢ Ici (1 : ℝ)) :=
      continuousOn_const
    have hprod1 :
        ContinuousOn (fun p : ℝ⁸ × ℝ ↦ (-I : ℂ) * ψS' ((Complex.I : ℂ) * (p.2 : ℂ)))
          (univ ×ˢ Ici (1 : ℝ)) :=
      hconst.mul hψ'
    have hprod2 :
        ContinuousOn
          (fun p : ℝ⁸ × ℝ ↦ (-I : ℂ) * ψS' ((Complex.I : ℂ) * (p.2 : ℂ)) * ((p.2 : ℂ) ^ (-4 : ℤ)))
          (univ ×ˢ Ici (1 : ℝ)) := by
      exact hprod1.mul hzpow'
    have hprod3 :
        ContinuousOn
          (fun p : ℝ⁸ × ℝ ↦
            (-I : ℂ) * ψS' ((Complex.I : ℂ) * (p.2 : ℂ)) * ((p.2 : ℂ) ^ (-4 : ℤ)) *
              cexp ((-π : ℂ) * ((‖p.1‖ : ℂ) ^ 2) / (p.2 : ℂ)))
          (univ ×ˢ Ici (1 : ℝ)) := by
      exact hprod2.mul (SpherePacking.ForMathlib.continuousOn_exp_norm_sq_div (E := ℝ⁸))
    refine hprod3.congr ?_
    intro p hp
    simp [J5Change.g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The `(x,s)`-kernel used in the `J₅`/`J₆` Fourier permutation argument. -/
@[expose] public def kernel (w : ℝ⁸) : ℝ⁸ × ℝ → ℂ :=
  fun p =>
    cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) * J5Change.g (‖p.1‖ ^ 2) p.2

lemma aestronglyMeasurable_kernel (w : ℝ⁸) :
    AEStronglyMeasurable (kernel w) ((volume : Measure ℝ⁸).prod μIciOne) := by
  have hphase : Continuous fun p : ℝ⁸ × ℝ => cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) := by fun_prop
  have hker : ContinuousOn (kernel w) (univ ×ˢ Ici (1 : ℝ)) := by
    refine (hphase.continuousOn.mul continuousOn_J₅_g).congr ?_
    intro p hp
    simp [kernel]
  have hmeas :
      AEStronglyMeasurable (kernel w)
        (((volume : Measure ℝ⁸).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ici (1 : ℝ))) := by
    exact ContinuousOn.aestronglyMeasurable hker (MeasurableSet.univ.prod measurableSet_Ici)
  have hμ :
      ((volume : Measure ℝ⁸).prod μIciOne) =
        (((volume : Measure ℝ⁸).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ici (1 : ℝ))) := by
    simpa [μIciOne, Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ⁸)) (ν := (volume : Measure ℝ))
        (s := (univ : Set ℝ⁸)) (t := Ici (1 : ℝ)))
  simpa [hμ] using hmeas

/-- Cancellation identity `s^(-4) * s^4 = 1` (after coercions to `ℂ`). -/
public lemma zpow_neg_four_mul_pow_four (s : ℝ) (hs : s ≠ 0) :
    ((s ^ (-4 : ℤ) : ℝ) : ℂ) * (s ^ 4 : ℂ) = 1 := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  simpa [Complex.ofReal_zpow] using (zpow_neg_mul_zpow_self (a := (s : ℂ)) (n := (4 : ℤ)) hsC)

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
  have hmeas : AEStronglyMeasurable (fun x : ℝ⁸ ↦ kernel w (x, s)) (volume : Measure ℝ⁸) := by
    have hs_mem : s ∈ Ici (1 : ℝ) := by simpa [Set.mem_Ici] using hs
    have hphase : Continuous fun x : ℝ⁸ => cexp (↑(-2 * (π * ⟪x, w⟫)) * I) := by fun_prop
    have hg : Continuous fun x : ℝ⁸ => J5Change.g (‖x‖ ^ 2) s := by
      have hg_on : ContinuousOn (fun x : ℝ⁸ => J5Change.g (‖x‖ ^ 2) s) (Set.univ : Set ℝ⁸) := by
        have hf : ContinuousOn (fun x : ℝ⁸ => (x, s)) (Set.univ : Set ℝ⁸) :=
          (by fun_prop : Continuous fun x : ℝ⁸ => (x, s)).continuousOn
        have hmaps :
            MapsTo (fun x : ℝ⁸ => (x, s)) (Set.univ : Set ℝ⁸) (univ ×ˢ Ici (1 : ℝ)) := by
          intro x hx
          exact ⟨Set.mem_univ _, hs_mem⟩
        simpa [Function.comp] using (continuousOn_J₅_g.comp hf hmaps)
      simpa [continuousOn_univ] using hg_on
    have hkernel : Continuous fun x : ℝ⁸ => kernel w (x, s) := by
      simpa [kernel] using hphase.mul hg
    exact hkernel.aestronglyMeasurable
  refine Integrable.mono' hmajor hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  exact le_of_eq (kernel_norm_eq (w := w) (x := x) (s := s))

/-- Integrability of `kernel w` for the product measure `volume × μIciOne`. -/
public lemma integrable_kernel (w : ℝ⁸) :
    Integrable (kernel w) ((volume : Measure ℝ⁸).prod μIciOne) := by
  haveI : MeasureTheory.SFinite μIciOne := by
    dsimp [μIciOne]
    infer_instance
  have hmeas : AEStronglyMeasurable (kernel w) ((volume : Measure ℝ⁸).prod μIciOne) :=
    aestronglyMeasurable_kernel (w := w)
  refine (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure ℝ⁸)) (ν := μIciOne) hmeas).2 ?_
  refine ⟨?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
    intro s hs
    exact integrable_kernel_slice (w := w) (s := s) hs
  · -- Integrability in `s` follows from exponential decay of `ψS` on the imaginary axis.
    rcases
      MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
      ⟨C, hC⟩
    have hmajor :
        Integrable (fun s : ℝ ↦ C * rexp (-π * s)) μIciOne := by
      have hIci : IntegrableOn (fun s : ℝ ↦ rexp (-(π : ℝ) * s)) (Ici (1 : ℝ)) volume := by
        -- `t^0 * exp(-π*t)` is integrable on `[1, ∞)`.
        simpa [pow_zero, one_mul] using
          (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 0) (b := (π : ℝ))
            Real.pi_pos)
      have hIci' : IntegrableOn (fun s : ℝ ↦ C * rexp (-(π : ℝ) * s)) (Ici (1 : ℝ)) volume := by
        simpa [IntegrableOn, mul_assoc] using hIci.const_mul C
      simpa [μIciOne, IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using hIci'
    have hmeas' :
        AEStronglyMeasurable (fun s : ℝ ↦ ∫ x : ℝ⁸, ‖kernel w (x, s)‖) μIciOne := by
      simpa using
        (SpherePacking.ForMathlib.aestronglyMeasurable_integral_norm_prod_right'
          (μ := μIciOne) (ν := (volume : Measure ℝ⁸)) (f := kernel w) hmeas)
    refine Integrable.mono' hmajor hmeas' ?_
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
    have hs_ne0 : s ≠ 0 := hs0.ne'
    have hgauss : (∫ x : ℝ⁸, rexp (-π * (‖x‖ ^ 2) / s)) = s ^ 4 :=
      SpherePacking.ForMathlib.integral_gaussian_rexp (s := s) hs0
    have hcancel : ((s ^ (-4 : ℤ) : ℝ) : ℂ) * (s ^ 4 : ℂ) = 1 :=
      zpow_neg_four_mul_pow_four (s := s) hs_ne0
    -- Evaluate the `x`-integral of `‖kernel‖` and compare to `‖ψS.resToImagAxis s‖`.
    have hnorm :
        (fun x : ℝ⁸ ↦ ‖kernel w (x, s)‖) =
          fun x : ℝ⁸ ↦ (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖) *
            rexp (-π * (‖x‖ ^ 2) / s) := by
      funext x
      exact kernel_norm_eq (w := w) (x := x) (s := s)
    have hval :
        ∫ x : ℝ⁸, ‖kernel w (x, s)‖ ≤ ‖ψS.resToImagAxis s‖ := by
      have hs_zpow_pos : 0 < s ^ (-4 : ℤ) := zpow_pos hs0 _
      have habs : ‖(s ^ (-4 : ℤ) : ℂ)‖ = s ^ (-4 : ℤ) := by
        -- The type ascription forces the `zpow` to live in `ℂ`.
        change ‖(s : ℂ) ^ (-4 : ℤ)‖ = s ^ (-4 : ℤ)
        have hzpow : (s : ℂ) ^ (-4 : ℤ) = (↑(s ^ (-4 : ℤ)) : ℂ) := by
          exact (Complex.ofReal_zpow s (-4 : ℤ)).symm
        -- Rewrite the `zpow` into an `ofReal` so we can use `RCLike.norm_ofReal`.
        rw [hzpow]
        calc
          ‖(↑(s ^ (-4 : ℤ)) : ℂ)‖ = |s ^ (-4 : ℤ)| := by
            exact
              (RCLike.norm_ofReal (s ^ (-4 : ℤ)) :
                ‖((s ^ (-4 : ℤ) : ℝ) : ℂ)‖ = |s ^ (-4 : ℤ)|)
          _ = s ^ (-4 : ℤ) := by
            exact abs_of_pos hs_zpow_pos
      have hs_pow : s ^ 4 ≠ 0 := pow_ne_zero 4 hs_ne0
      have hz : (s ^ (-4 : ℤ)) = (s ^ 4)⁻¹ := by simpa using (zpow_negSucc s 3)
      have hscal : (‖(s ^ (-4 : ℤ) : ℂ)‖) * (s ^ 4) = (1 : ℝ) := by
        rw [habs]
        rw [hz]
        exact inv_mul_cancel₀ hs_pow
      have hψS' : ‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ = ‖ψS.resToImagAxis s‖ := by
        have h :
            ψS' ((Complex.I : ℂ) * (s : ℂ)) = ψS.resToImagAxis s := by
          simp [ψS', Function.resToImagAxis, ResToImagAxis, hs0, mul_comm]
        simpa using congrArg norm h
      have hEq : (∫ x : ℝ⁸, ‖kernel w (x, s)‖) = ‖ψS.resToImagAxis s‖ := by
        have hEq0 :
            (∫ x : ℝ⁸, ‖kernel w (x, s)‖) =
              ∫ x : ℝ⁸,
                (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖) *
                  rexp (-π * (‖x‖ ^ 2) / s) := by
          exact congrArg (fun f : ℝ⁸ → ℝ => ∫ x : ℝ⁸, f x) hnorm
        have hEq1 :
            (∫ x : ℝ⁸,
                  (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖) *
                    rexp (-π * (‖x‖ ^ 2) / s)) =
              (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖) *
                (∫ x : ℝ⁸, rexp (-π * (‖x‖ ^ 2) / s)) := by
          exact
            (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ⁸))
              (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖)
              (fun x : ℝ⁸ ↦ rexp (-π * (‖x‖ ^ 2) / s)))
        calc
          (∫ x : ℝ⁸, ‖kernel w (x, s)‖)
              = ∫ x : ℝ⁸,
                  (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖) *
                    rexp (-π * (‖x‖ ^ 2) / s) := hEq0
          _ = (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖) *
                (∫ x : ℝ⁸, rexp (-π * (‖x‖ ^ 2) / s)) := hEq1
          _ = (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-4 : ℤ) : ℂ)‖) * (s ^ 4) := by
                rw [hgauss]
          _ = ‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ := by
                rw [mul_assoc]
                rw [hscal]
                simp
          _ = ‖ψS.resToImagAxis s‖ := by simp [hψS']
      exact le_of_eq hEq
    have hbound :
        ‖(∫ x : ℝ⁸, ‖kernel w (x, s)‖)‖ ≤ C * rexp (-π * s) := by
      have hn0 : 0 ≤ ∫ x : ℝ⁸, ‖kernel w (x, s)‖ :=
        MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
      have habs : ‖∫ x : ℝ⁸, ‖kernel w (x, s)‖‖ = ∫ x : ℝ⁸, ‖kernel w (x, s)‖ := by
        simp [Real.norm_eq_abs, abs_of_nonneg hn0]
      have : ∫ x : ℝ⁸, ‖kernel w (x, s)‖ ≤ C * rexp (-π * s) := hval.trans (hC s hs)
      simpa [habs] using this
    simpa using hbound

end Integral_Permutations.PermJ5
end

end MagicFunction.b.Fourier
