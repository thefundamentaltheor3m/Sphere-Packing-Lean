module
public import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12FourierJ2
public import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12Defs
public import SpherePacking.Basic.Domains.WedgeSet
import SpherePacking.MagicFunction.b.PsiBounds
import SpherePacking.Contour.PermJ12Tendsto


/-!
# Regularity and contour deformation for `perm_J₁_J₂`

This file packages the analytic input for the Poincare-lemma based contour deformation used in
the `b`-side permutation argument: holomorphicity of `ψT'` and `Ψ₁'`, and vanishing of `Ψ₁'` at the
cusp `1` within `closure wedgeSet`.

## Main statements
* `differentiableOn_ψT'_upper`
* `differentiableOn_Ψ₁'_upper`
* `tendsto_Ψ₁'_one_within_closure_wedgeSet`
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology

open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

open SpherePacking

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral


section PermJ12

open MeasureTheory Set Complex Real
open Filter
open scoped Interval

open scoped ModularForm


/-- Holomorphicity of `ψT` when viewed as a complex function on the upper half-plane. -/
public lemma differentiableOn_ψT_ofComplex :
    DifferentiableOn ℂ (fun z : ℂ => ψT (UpperHalfPlane.ofComplex z))
      UpperHalfPlane.upperHalfPlaneSet := by
  -- Get differentiability of `H₂,H₃,H₄` from their manifold differentiability.
  have hH2 :
      DifferentiableOn ℂ (fun z : ℂ => H₂ (UpperHalfPlane.ofComplex z))
        UpperHalfPlane.upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff (f := H₂)).1 mdifferentiable_H₂
  have hH3 :
      DifferentiableOn ℂ (fun z : ℂ => H₃ (UpperHalfPlane.ofComplex z))
        UpperHalfPlane.upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff (f := H₃)).1 mdifferentiable_H₃
  have hH4 :
      DifferentiableOn ℂ (fun z : ℂ => H₄ (UpperHalfPlane.ofComplex z))
        UpperHalfPlane.upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff (f := H₄)).1 mdifferentiable_H₄
  have hterm1 :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          (H₃ (UpperHalfPlane.ofComplex z) + H₄ (UpperHalfPlane.ofComplex z)) /
            (H₂ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ))
        UpperHalfPlane.upperHalfPlaneSet :=
    (hH3.add hH4).div (hH2.pow 2) fun z _ => pow_ne_zero 2 (H₂_ne_zero (UpperHalfPlane.ofComplex z))
  have hterm2 :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          (H₂ (UpperHalfPlane.ofComplex z) + H₃ (UpperHalfPlane.ofComplex z)) /
            (H₄ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ))
        UpperHalfPlane.upperHalfPlaneSet :=
    (hH2.add hH3).div (hH4.pow 2) fun z _ => pow_ne_zero 2 (H₄_ne_zero (UpperHalfPlane.ofComplex z))
  have hExpr :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          (128 : ℂ) *
            (((H₃ (UpperHalfPlane.ofComplex z) + H₄ (UpperHalfPlane.ofComplex z)) /
                    (H₂ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ)) +
              ((H₂ (UpperHalfPlane.ofComplex z) + H₃ (UpperHalfPlane.ofComplex z)) /
                    (H₄ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ))))
        UpperHalfPlane.upperHalfPlaneSet := by
    simpa [mul_assoc] using (DifferentiableOn.const_mul (hterm1.add hterm2) (128 : ℂ))
  refine hExpr.congr ?_
  intro z hz
  have hψ :=
    congrArg (fun f : UpperHalfPlane → ℂ => f (UpperHalfPlane.ofComplex z)) ψT_eq
  assumption

/-- Holomorphicity of `ψT'` on the upper half-plane. -/
public lemma differentiableOn_ψT'_upper :
    DifferentiableOn ℂ ψT' UpperHalfPlane.upperHalfPlaneSet := by
  refine (differentiableOn_ψT_ofComplex).congr fun z hz => ?_
  have hz' : 0 < z.im := by simpa [UpperHalfPlane.upperHalfPlaneSet] using hz
  simp [ψT', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']

/-- Holomorphicity of `Ψ₁' r` on the upper half-plane. -/
public lemma differentiableOn_Ψ₁'_upper (r : ℝ) :
    DifferentiableOn ℂ (Ψ₁' r) UpperHalfPlane.upperHalfPlaneSet := by
  unfold Ψ₁'
  exact differentiableOn_ψT'_upper.mul
    ((differentiable_id.const_mul
      ((Real.pi : ℂ) * Complex.I * (r : ℂ))).cexp.differentiableOn)

open UpperHalfPlane Complex ModularGroup MatrixGroups ModularForm SlashAction Matrix
open scoped Real ModularForm MatrixGroups

/-- `Ψ₁' r` tends to `0` at the cusp `1` when restricted to `closure wedgeSet`. -/
public lemma tendsto_Ψ₁'_one_within_closure_wedgeSet (r : ℝ) :
    Tendsto (Ψ₁' r) (𝓝[closure wedgeSet] (1 : ℂ)) (𝓝 0) := by
  let g : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ModularGroup.S * ModularGroup.T * ModularGroup.S
  let gAct : UpperHalfPlane → UpperHalfPlane :=
    fun zH =>
      HSMul.hSMul (α := Matrix.SpecialLinearGroup (Fin 2) ℤ) (β := UpperHalfPlane)
        (γ := UpperHalfPlane) g zH
  have hg :
      g =
        ⟨!![-1, 0; 1, -1], by
          norm_num [Matrix.det_fin_two_of]⟩ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [g, ModularGroup.S, ModularGroup.T]
  have hgAct_im :
      ∀ {z : ℂ} (hz : 0 < z.im),
        (gAct (⟨z, hz⟩ : UpperHalfPlane)).im = z.im / Complex.normSq (z - 1) := by
    intro z hz
    let zH : UpperHalfPlane := ⟨z, hz⟩
    have him :
        (gAct zH).im = z.im / Complex.normSq (UpperHalfPlane.denom g zH) := by
      simpa [gAct, zH] using (ModularGroup.im_smul_eq_div_normSq (g := g) (z := zH))
    have hdenom : UpperHalfPlane.denom g zH = (z : ℂ) - 1 := by
      have hcalc : UpperHalfPlane.denom g zH = (z : ℂ) + (-1 : ℂ) := by
        simp [UpperHalfPlane.denom, hg, zH]
      simpa [sub_eq_add_neg] using hcalc
    simpa [hdenom] using him
  have hψT' :
      ∀ {z : ℂ} (hz : 0 < z.im),
        ψT' z = -ψS (gAct (⟨z, hz⟩ : UpperHalfPlane)) * (z - 1) ^ (2 : ℕ) := by
    intro z hz
    let zH : UpperHalfPlane := ⟨z, hz⟩
    have hrel0 := congrArg (fun F : UpperHalfPlane → ℂ => F zH) ψS_slash_STS
    have hrel : (ψS ∣[(-2 : ℤ)] g) zH = -ψT zH := by
      simpa [g] using hrel0
    have hdenom : UpperHalfPlane.denom g zH = (z : ℂ) - 1 := by
      have hcalc : UpperHalfPlane.denom g zH = (z : ℂ) + (-1 : ℂ) := by
        simp [UpperHalfPlane.denom, hg, zH]
      simpa [sub_eq_add_neg] using hcalc
    have h1 :
        ψS (gAct zH) * UpperHalfPlane.denom g zH ^ (2 : ℤ) = -ψT zH := by
      simpa [ModularForm.SL_slash_apply, gAct] using hrel
    have h2 : ψT zH = -ψS (gAct zH) * UpperHalfPlane.denom g zH ^ (2 : ℤ) := by
      simpa [neg_mul, mul_assoc] using (congrArg Neg.neg h1).symm
    calc
      ψT' z = ψT zH := by simp [ψT', hz, zH]
      _ = -ψS (gAct zH) * UpperHalfPlane.denom g zH ^ (2 : ℤ) := h2
      _ = -ψS (gAct zH) * ((z : ℂ) - 1) ^ (2 : ℤ) := by
            simp [hdenom]
      _ = -ψS (gAct zH) * (z - 1) ^ (2 : ℕ) := by
            simpa using
              congrArg (fun t : ℂ => -ψS (gAct zH) * t) (zpow_ofNat (z - 1) 2)
  simpa using
    (SpherePacking.Contour.tendsto_Ψ₁'_one_within_closure_wedgeSet_of
      (h := ({
        hk := by decide
        Ψ₁'_eq := by intro r z; rfl
        ψT'_one := by simp [ψT']
        tendsto_ψS_atImInfty := MagicFunction.b.PsiBounds.tendsto_ψS_atImInfty
        gAct_im := hgAct_im
        ψT'_eq_neg_ψS_mul := hψT'
        mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one :=
          mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one
        closure_wedgeSet_subset_abs_re_sub_one_le_im := by
          intro z hz
          simpa using (closure_wedgeSet_subset_abs_re_sub_one_le_im (a := z) hz)
      } : SpherePacking.Contour.TendstoPsiOneHypotheses wedgeSet ψS ψT' Ψ₁' gAct 2))
      (r := r))

end Integral_Permutations.PermJ12
end

end MagicFunction.b.Fourier
