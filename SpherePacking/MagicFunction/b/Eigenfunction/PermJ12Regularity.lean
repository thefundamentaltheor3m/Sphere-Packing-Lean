module
public import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12FourierJ2
public import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12Defs
public import SpherePacking.Basic.Domains.WedgeSet
import SpherePacking.MagicFunction.b.PsiBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Regularity and contour deformation for `perm_J₁_J₂`

Holomorphicity of `ψT'`, `Ψ₁'` and vanishing of `Ψ₁'` at the cusp `1` within `closure wedgeSet`.
-/

namespace SpherePacking.Contour

noncomputable section

open Set Filter
open scoped Topology Complex

/-- Bundles the hypotheses for `tendsto_Ψ₁'_one_within_closure_wedgeSet_of`. -/
public structure TendstoPsiOneHypotheses (wedgeSet : Set ℂ) (ψS : UpperHalfPlane → ℂ)
    (ψT' : ℂ → ℂ) (Ψ₁' : ℝ → ℂ → ℂ) (gAct : UpperHalfPlane → UpperHalfPlane) (k : ℕ) : Prop where
  hk : (1 : ℕ) ≤ k
  Ψ₁'_eq : ∀ r : ℝ, ∀ z : ℂ,
    Ψ₁' r z = ψT' z * cexp ((Real.pi : ℂ) * Complex.I * (r : ℂ) * z)
  ψT'_one : ψT' (1 : ℂ) = 0
  tendsto_ψS_atImInfty : Tendsto ψS UpperHalfPlane.atImInfty (𝓝 (0 : ℂ))
  gAct_im : ∀ {z : ℂ} (hz : 0 < z.im),
    (gAct (⟨z, hz⟩ : UpperHalfPlane)).im = z.im / Complex.normSq (z - 1)
  ψT'_eq_neg_ψS_mul : ∀ {z : ℂ} (hz : 0 < z.im),
    ψT' z = -ψS (gAct (⟨z, hz⟩ : UpperHalfPlane)) * (z - 1) ^ k
  mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one :
    ∀ {z : ℂ}, z ∈ closure wedgeSet → z ≠ (1 : ℂ) → z ∈ UpperHalfPlane.upperHalfPlaneSet
  closure_wedgeSet_subset_abs_re_sub_one_le_im :
    ∀ {z : ℂ}, z ∈ closure wedgeSet → |z.re - 1| ≤ z.im

private def expNorm (r : ℝ) (z : ℂ) : ℝ := ‖cexp (z * (Complex.I * ((r : ℂ) * (Real.pi : ℂ))))‖

/-- Under `TendstoPsiOneHypotheses`, `Ψ₁' r` tends to `0` as `z → 1` within `closure wedgeSet`. -/
public lemma tendsto_Ψ₁'_one_within_closure_wedgeSet_of {wedgeSet : Set ℂ}
    {ψS : UpperHalfPlane → ℂ} {ψT' : ℂ → ℂ} {Ψ₁' : ℝ → ℂ → ℂ}
    {gAct : UpperHalfPlane → UpperHalfPlane} {k : ℕ}
    (h : TendstoPsiOneHypotheses wedgeSet ψS ψT' Ψ₁' gAct k) (r : ℝ) :
    Tendsto (Ψ₁' r) (𝓝[closure wedgeSet] (1 : ℂ)) (𝓝 0) := by
  let M : ℝ := expNorm r (1 : ℂ) + 1
  have hMpos : 0 < M := by linarith [show 0 ≤ expNorm r 1 from norm_nonneg _]
  obtain ⟨δexp, hδexp_pos, hExpBound⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ {z : ℂ}, dist z (1 : ℂ) < δ → expNorm r z ≤ expNorm r (1 : ℂ) + 1 := by
    rcases (Metric.continuousAt_iff.1 (by
      simpa [expNorm] using (continuousAt_id.mul continuousAt_const).cexp.norm :
      ContinuousAt (expNorm r) (1 : ℂ))) 1 (by norm_num) with ⟨δ, hδ_pos, hδ⟩
    exact ⟨δ, hδ_pos, fun {z} hz => le_of_lt (sub_lt_iff_lt_add'.1
      (abs_sub_lt_iff.1 (by simpa [Real.dist_eq] using hδ hz)).1)⟩
  obtain ⟨A, hApos, hA⟩ : ∃ A : ℝ, 0 < A ∧ ∀ τ : UpperHalfPlane, A ≤ τ.im → ‖ψS τ‖ ≤ (1 : ℝ) := by
    rcases (UpperHalfPlane.atImInfty_mem (S := {τ : UpperHalfPlane | ‖ψS τ‖ < (1 : ℝ)})).1
      (((tendsto_zero_iff_norm_tendsto_zero).1 h.tendsto_ψS_atImInfty).eventually
        (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))) with ⟨A0, hA0⟩
    exact ⟨max A0 1, zero_lt_one.trans_le (le_max_right _ _),
      fun τ hτ => (hA0 τ ((le_max_left _ _).trans hτ)).le⟩
  refine (Metric.tendsto_nhdsWithin_nhds).2 fun ε hε => ?_
  refine ⟨min δexp (min (min 1 (ε / M)) (1 / (2 * A))),
    lt_min hδexp_pos (lt_min (lt_min (by norm_num) (div_pos hε hMpos)) (by positivity)),
    fun z hzcl hdistz => ?_⟩
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1; simpa [h.Ψ₁'_eq, h.ψT'_one] using hε
  have hz_im_pos : 0 < z.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using
      h.mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hzcl hz1
  let zH : UpperHalfPlane := ⟨z, hz_im_pos⟩
  have hexpZ : expNorm r z ≤ M := hExpBound (lt_of_lt_of_le hdistz (min_le_left _ _))
  have hdist_min := lt_of_lt_of_le hdistz (min_le_right _ _)
  have hdist_lt := lt_of_lt_of_le hdist_min (min_le_left _ _)
  have hdist_lt_one : dist z (1 : ℂ) < 1 := lt_of_lt_of_le hdist_lt (min_le_left _ _)
  have hdist_pow : (dist z (1 : ℂ)) ^ k < ε / M :=
    ((by simpa [pow_one] using pow_le_pow_of_le_one dist_nonneg hdist_lt_one.le h.hk
      : (dist z (1 : ℂ)) ^ k ≤ dist z (1 : ℂ))).trans_lt
        (lt_of_lt_of_le hdist_lt (min_le_right _ _))
  have hdist_im : dist z (1 : ℂ) < 1 / (2 * A) := lt_of_lt_of_le hdist_min (min_le_right _ _)
  have hA_le_im : A ≤ (gAct zH).im := by
    have hz_im_lt : z.im < 1 / (2 * A) := lt_of_le_of_lt
      (by simpa [abs_of_nonneg hz_im_pos.le] using Complex.abs_im_le_norm (z - 1))
      (by simpa [dist_eq_norm] using hdist_im)
    have habs_re : |z.re - 1| ≤ z.im :=
      h.closure_wedgeSet_subset_abs_re_sub_one_le_im hzcl
    have hbound : (1 : ℝ) / (2 * z.im) ≤ z.im / Complex.normSq (z - 1) := by
      have hnormSq_pos : 0 < Complex.normSq (z - 1) :=
        Complex.normSq_pos.2 (sub_ne_zero.mpr hz1)
      have hnormSq_le : Complex.normSq (z - 1) ≤ 2 * z.im ^ 2 := by
        have hre_sq : (z.re - 1) ^ 2 ≤ z.im ^ 2 := by
          simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs_re 2
        nlinarith [show Complex.normSq (z - 1) = (z.re - 1) ^ 2 + z.im ^ 2 by
          simp [Complex.normSq, sub_eq_add_neg, pow_two, add_comm], hre_sq]
      calc (1 : ℝ) / (2 * z.im) = z.im * ((1 : ℝ) / (2 * z.im ^ 2)) := by field_simp
        _ ≤ z.im * ((1 : ℝ) / Complex.normSq (z - 1)) := mul_le_mul_of_nonneg_left
              (one_div_le_one_div_of_le hnormSq_pos hnormSq_le) hz_im_pos.le
        _ = z.im / Complex.normSq (z - 1) := by simp [div_eq_mul_inv]
    simpa [zH, h.gAct_im (z := z) (hz := hz_im_pos)] using ((lt_div_iff₀
      (by positivity : (0:ℝ) < 2 * z.im)).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using
        (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * A)).1 hz_im_lt)).trans_le hbound |>.le
  have hψT_norm : ‖ψT' z‖ ≤ ‖(z - 1) ^ k‖ :=
    calc ‖ψT' z‖ = ‖ψS (gAct zH)‖ * ‖(z - 1) ^ k‖ := by
            simp [show ψT' z = -ψS (gAct zH) * (z - 1) ^ k by
              simpa [zH] using h.ψT'_eq_neg_ψS_mul (z := z) (hz := hz_im_pos), norm_neg]
      _ ≤ 1 * ‖(z - 1) ^ k‖ := mul_le_mul_of_nonneg_right (hA _ hA_le_im) (norm_nonneg _)
      _ = _ := by simp
  have hmain : ‖Ψ₁' r z‖ ≤ (dist z (1 : ℂ)) ^ k * M :=
    calc ‖Ψ₁' r z‖ = ‖ψT' z‖ * expNorm r z := by
            simp [h.Ψ₁'_eq, expNorm, show ((Real.pi : ℂ) * Complex.I * (r : ℂ) * z) =
              z * (Complex.I * ((r : ℂ) * (Real.pi : ℂ))) by ac_rfl]
      _ ≤ ‖(z - 1) ^ k‖ * expNorm r z :=
          mul_le_mul_of_nonneg_right hψT_norm (by simp [expNorm])
      _ ≤ ‖(z - 1) ^ k‖ * M := mul_le_mul_of_nonneg_left hexpZ (norm_nonneg _)
      _ = (dist z (1 : ℂ)) ^ k * M := by simp [dist_eq_norm, norm_pow]
  simpa [dist_eq_norm] using hmain.trans_lt ((lt_div_iff₀ hMpos).mp hdist_pow)

end

end SpherePacking.Contour

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap
open SpherePacking

section Integral_Permutations

open scoped Real
open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral

section PermJ12

open MeasureTheory Set Complex Real Filter
open scoped Interval ModularForm

/-- Holomorphicity of `ψT` when viewed as a complex function on the upper half-plane. -/
public lemma differentiableOn_ψT_ofComplex :
    DifferentiableOn ℂ (fun z : ℂ => ψT (UpperHalfPlane.ofComplex z))
      UpperHalfPlane.upperHalfPlaneSet := by
  have hH2 := (UpperHalfPlane.mdifferentiable_iff (f := H₂)).1 mdifferentiable_H₂
  have hH3 := (UpperHalfPlane.mdifferentiable_iff (f := H₃)).1 mdifferentiable_H₃
  have hH4 := (UpperHalfPlane.mdifferentiable_iff (f := H₄)).1 mdifferentiable_H₄
  have hterm1 := (hH3.add hH4).div (hH2.pow 2)
    fun z _ => pow_ne_zero 2 (H₂_ne_zero (UpperHalfPlane.ofComplex z))
  have hterm2 := (hH2.add hH3).div (hH4.pow 2)
    fun z _ => pow_ne_zero 2 (H₄_ne_zero (UpperHalfPlane.ofComplex z))
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
  exact hExpr.congr fun z _ =>
    congrArg (fun f : UpperHalfPlane → ℂ => f (UpperHalfPlane.ofComplex z)) ψT_eq

/-- Holomorphicity of `Ψ₁' r` on the upper half-plane. -/
public lemma differentiableOn_Ψ₁'_upper (r : ℝ) :
    DifferentiableOn ℂ (Ψ₁' r) UpperHalfPlane.upperHalfPlaneSet :=
  (differentiableOn_ψT_ofComplex.congr fun z hz => by
    have hz' : 0 < z.im := by simpa [UpperHalfPlane.upperHalfPlaneSet] using hz
    simp [ψT', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']).mul
    ((differentiable_id.const_mul
      ((Real.pi : ℂ) * Complex.I * (r : ℂ))).cexp.differentiableOn)

open UpperHalfPlane Complex ModularGroup MatrixGroups ModularForm SlashAction Matrix
open scoped Real ModularForm MatrixGroups

/-- `Ψ₁' r` tends to `0` at the cusp `1` when restricted to `closure wedgeSet`. -/
public lemma tendsto_Ψ₁'_one_within_closure_wedgeSet (r : ℝ) :
    Tendsto (Ψ₁' r) (𝓝[closure wedgeSet] (1 : ℂ)) (𝓝 0) := by
  let g : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ModularGroup.S * ModularGroup.T * ModularGroup.S
  let gAct : UpperHalfPlane → UpperHalfPlane := fun zH =>
    HSMul.hSMul (α := Matrix.SpecialLinearGroup (Fin 2) ℤ) (β := UpperHalfPlane)
      (γ := UpperHalfPlane) g zH
  have hg : g = ⟨!![-1, 0; 1, -1], by norm_num [Matrix.det_fin_two_of]⟩ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [g, ModularGroup.S, ModularGroup.T]
  have hdenom : ∀ {z : ℂ} (hz : 0 < z.im),
      UpperHalfPlane.denom g (⟨z, hz⟩ : UpperHalfPlane) = (z : ℂ) - 1 := fun {z} hz => by
    simp [UpperHalfPlane.denom, hg, sub_eq_add_neg]
  have hgAct_im :
      ∀ {z : ℂ} (hz : 0 < z.im),
        (gAct (⟨z, hz⟩ : UpperHalfPlane)).im = z.im / Complex.normSq (z - 1) := fun {z} hz => by
    simpa [hdenom hz, gAct] using
      (ModularGroup.im_smul_eq_div_normSq (g := g) (z := (⟨z, hz⟩ : UpperHalfPlane)))
  have hψT' :
      ∀ {z : ℂ} (hz : 0 < z.im),
        ψT' z = -ψS (gAct (⟨z, hz⟩ : UpperHalfPlane)) * (z - 1) ^ (2 : ℕ) := fun {z} hz => by
    let zH : UpperHalfPlane := ⟨z, hz⟩
    have h1 : ψS (gAct zH) * UpperHalfPlane.denom g zH ^ (2 : ℤ) = -ψT zH := by
      simpa [ModularForm.SL_slash_apply, gAct, g] using
        congrArg (fun F : UpperHalfPlane → ℂ => F zH) ψS_slash_STS
    calc ψT' z = ψT zH := by simp [ψT', hz, zH]
      _ = -ψS (gAct zH) * UpperHalfPlane.denom g zH ^ (2 : ℤ) := by
            simpa [neg_mul, mul_assoc] using (congrArg Neg.neg h1).symm
      _ = -ψS (gAct zH) * ((z : ℂ) - 1) ^ (2 : ℤ) := by rw [hdenom hz]
      _ = -ψS (gAct zH) * (z - 1) ^ (2 : ℕ) := by
            simpa using congrArg (fun t : ℂ => -ψS (gAct zH) * t) (zpow_ofNat (z - 1) 2)
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
        closure_wedgeSet_subset_abs_re_sub_one_le_im := fun {z} hz => by
          simpa using (closure_wedgeSet_subset_abs_re_sub_one_le_im (a := z) hz)
      } : SpherePacking.Contour.TendstoPsiOneHypotheses wedgeSet ψS ψT' Ψ₁' gAct 2))
      (r := r))

end Integral_Permutations.PermJ12
end

end MagicFunction.b.Fourier
