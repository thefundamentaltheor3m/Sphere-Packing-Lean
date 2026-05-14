module
import SpherePacking.MagicFunction.g.CohnElkies.Defs
public import SpherePacking.MagicFunction.b.Schwartz.Basic
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceLemmas
import SpherePacking.MagicFunction.g.CohnElkies.DeltaBounds
public import SpherePacking.MagicFunction.b.Psi
import SpherePacking.MagicFunction.b.PsiBounds
import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay
import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular

/-!
# Laplace representation for `b'` (blueprint `prop:b-double-zeros`)

Defines the Laplace integrand `bLaplaceIntegrand` and proves its convergence on `(0, ∞)` for
`u > 2`. Used in the blueprint proposition `prop:b-double-zeros` (main statement
`bRadial_eq_laplace_psiI_main`). Also includes the contour-integrand definitions
(`bContourWeight`, `bContourIntegrand{I,T,S}`) and the supporting `ψT' = ψI' (· + 1)` identities
used in the rectangle deformation argument.
-/

namespace MagicFunction.g.CohnElkies

/--
For `u ≥ 0`, the radial profile `b'` from `MagicFunction.FourierEigenfunctions` agrees with the
real-integral definition `MagicFunction.b.RealIntegrals.b'`.

The prime `'` is part of the standard notation for this radial profile (it is not a derivative).
-/
public lemma b'_eq_realIntegrals_b' {u : ℝ} (hu : 0 ≤ u) :
    (MagicFunction.FourierEigenfunctions.b' : ℝ → ℂ) u = MagicFunction.b.RealIntegrals.b' u := by
  simp [MagicFunction.FourierEigenfunctions.b', MagicFunction.b.RealIntegrals.b',
    MagicFunction.b.SchwartzIntegrals.J₁'_apply_of_nonneg,
    MagicFunction.b.SchwartzIntegrals.J₂'_apply_of_nonneg,
    MagicFunction.b.SchwartzIntegrals.J₃'_apply_of_nonneg,
    MagicFunction.b.SchwartzIntegrals.J₄'_apply_of_nonneg,
    MagicFunction.b.SchwartzIntegrals.J₅'_apply_of_nonneg,
    MagicFunction.b.SchwartzIntegrals.J₆'_apply_of_nonneg, hu]

end MagicFunction.g.CohnElkies

namespace MagicFunction.g.CohnElkies.IntegralReps

noncomputable section

open scoped BigOperators Topology UpperHalfPlane intervalIntegral
open MeasureTheory Real Complex Filter
open MagicFunction.FourierEigenfunctions MagicFunction.Parametrisations
  MagicFunction.g.CohnElkies.Trig

/-- The Laplace integrand appearing in the representation of the radial profile `b'`. -/
@[expose] public def bLaplaceIntegrand (u t : ℝ) : ℂ :=
  ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)

lemma ψI_apply_eq_factor (z : ℍ) :
    ψI z = (1 / 2 : ℂ) * (H₄ z ^ (3 : ℕ) *
      (2 * H₄ z ^ (2 : ℕ) + 5 * H₄ z * H₂ z + 5 * H₂ z ^ (2 : ℕ))) / (Δ z) := by
  refine eq_div_of_mul_eq (by simpa [Delta_apply] using Δ_ne_zero z) ?_
  rw [show ψI z = (128 : ℂ) * ((H₃ z + H₄ z) / (H₂ z) ^ (2 : ℕ)) +
        (128 : ℂ) * ((H₄ z - H₂ z) / (H₃ z) ^ (2 : ℕ)) by
      simpa [Pi.smul_apply, nsmul_eq_mul] using congrArg (fun f : ℍ → ℂ => f z) ψI_eq,
    show (Δ z : ℂ) = ((H₂ z) * (H₃ z) * (H₄ z)) ^ 2 / (256 : ℂ) by
      simpa [Delta_apply] using Delta_eq_H₂_H₃_H₄ z]
  field_simp [H₂_ne_zero z, H₃_ne_zero z, H₄_ne_zero z]
  simp [show H₃ z = H₂ z + H₄ z by
    simpa using congrArg (fun f : ℍ → ℂ => f z) jacobi_identity.symm]; ring

/-- Exponential growth bound for `ψI` on vertical rays in the upper half-plane. -/
public lemma exists_ψI_bound_exp :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖ψI z‖ ≤ C * Real.exp (2 * π * z.im) := by
  let num : ℍ → ℂ := fun z : ℍ =>
    (1 / 2 : ℂ) * (H₄ z ^ (3 : ℕ) *
      (2 * H₄ z ^ (2 : ℕ) + 5 * H₄ z * H₂ z + 5 * H₂ z ^ (2 : ℕ)))
  have hH2 : Tendsto H₂ UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) := H₂_tendsto_atImInfty
  have hH4 : Tendsto H₄ UpperHalfPlane.atImInfty (𝓝 (1 : ℂ)) := H₄_tendsto_atImInfty
  have hnum : Tendsto num UpperHalfPlane.atImInfty (𝓝 (1 : ℂ)) := by
    simpa [num, show ((1 / 2 : ℂ) * ((1 : ℂ) ^ (3 : ℕ) * (2 : ℂ))) = (1 : ℂ) from by norm_num] using
      (tendsto_const_nhds (x := (1 / 2 : ℂ)) (f := UpperHalfPlane.atImInfty)).mul (show Tendsto
            (fun z : ℍ => H₄ z ^ (3 : ℕ) *
              (2 * H₄ z ^ (2 : ℕ) + 5 * H₄ z * H₂ z + 5 * H₂ z ^ (2 : ℕ)))
            UpperHalfPlane.atImInfty (𝓝 ((1 : ℂ) ^ (3 : ℕ) * (2 : ℂ))) by
        simpa [mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
          using (hH4.pow 3).mul (show Tendsto
              (fun z : ℍ => (2 : ℂ) * H₄ z ^ (2 : ℕ) + (5 : ℂ) * (H₄ z * H₂ z) +
                (5 : ℂ) * H₂ z ^ (2 : ℕ)) UpperHalfPlane.atImInfty (𝓝 (2 : ℂ)) by
            simpa [mul_add, add_assoc, add_left_comm, add_comm] using
              (tendsto_const_nhds.mul (hH4.pow 2)).add
                ((tendsto_const_nhds.mul (hH4.mul hH2)).add (tendsto_const_nhds.mul (hH2.pow 2)))))
  have hEvNum : ∀ᶠ z in UpperHalfPlane.atImInfty, ‖num z‖ ≤ (2 : ℝ) := by
    filter_upwards [hnum.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1))]
      with z hz
    nlinarith [show ‖(1 : ℂ)‖ = (1 : ℝ) by simp,
      (by simpa [Metric.mem_ball, dist_eq_norm] using hz : ‖num z - (1 : ℂ)‖ < 1),
      (by simpa [sub_add_cancel] using norm_add_le (num z - (1 : ℂ)) (1 : ℂ) :
        ‖num z‖ ≤ ‖num z - (1 : ℂ)‖ + ‖(1 : ℂ)‖)]
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
  obtain ⟨Cψ, hCψ⟩ :=
    MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one
  let Cψ0 : ℝ := max Cψ 0
  have hψS_bound (s : ℝ) (hs : 1 ≤ s) :
      ‖ψS.resToImagAxis s‖ ≤ Cψ0 * Real.exp (-π * s) :=
    (hCψ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hcontIoi : ContinuousOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) := by
    intro t ht0
    have hψIcomp :
        ContinuousAt
          (fun s : ℝ => ψI (UpperHalfPlane.ofComplex ((Complex.I : ℂ) * (s : ℂ)))) t :=
      ContinuousAt.comp MagicFunction.b.PsiBounds.continuous_ψI.continuousAt
        (ContinuousAt.comp (UpperHalfPlane.contMDiffAt_ofComplex (n := ⊤) (by simpa using ht0 :
          0 < (((Complex.I : ℂ) * (t : ℂ) : ℂ)).im)).continuousAt
          (by fun_prop : ContinuousAt (fun s : ℝ => (Complex.I : ℂ) * (s : ℂ)) t))
    refine ((show ContinuousAt
        (fun s : ℝ => (ψI (UpperHalfPlane.ofComplex ((Complex.I : ℂ) * (s : ℂ)))) *
            (Real.exp (-π * u * s) : ℂ)) t by
      simpa [mul_assoc] using hψIcomp.mul (by fun_prop :
        ContinuousAt (fun s : ℝ => (Real.exp (-π * u * s) : ℂ)) t)).congr_of_eventuallyEq ?_
      ).continuousWithinAt
    filter_upwards [lt_mem_nhds ht0] with s hs
    have hsIm : 0 < (((Complex.I : ℂ) * (s : ℂ) : ℂ)).im := by simpa using hs
    simp [bLaplaceIntegrand, ψI', UpperHalfPlane.ofComplex_apply_of_im_pos hsIm, hs]
  have hint_small : IntegrableOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioc (0 : ℝ) 1) :=
    IntegrableOn.of_bound measure_Ioc_lt_top
      ((hcontIoi.mono fun t ht => ht.1).aestronglyMeasurable measurableSet_Ioc) Cψ0 <| by
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
      have ht0 : 0 < t := ht.1
      have ht' : 1 ≤ (1 / t : ℝ) := by simpa [one_div] using (one_le_div ht0).2 ht.2
      have hψS' : ‖ψS.resToImagAxis (1 / t : ℝ)‖ ≤ Cψ0 := by
        simpa using (hψS_bound (1 / t : ℝ) ht').trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, le_of_lt (one_div_pos.2 ht0)])
            : Real.exp (-π * (1 / t : ℝ)) ≤ 1) (le_max_right _ _))
      have hψI : ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ ≤ Cψ0 := by
        rw [show ψI' ((Complex.I : ℂ) * (t : ℂ)) = ψI.resToImagAxis t by
            simp [ψI', Function.resToImagAxis, ResToImagAxis, ht0],
          show ψI.resToImagAxis t = (-(t ^ (2 : ℕ)) : ℂ) * ψS.resToImagAxis (1 / t) by
            simpa [zpow_two, pow_two, ψS_slash_S] using
              ResToImagAxis.SlashActionS (F := ψS) (k := (-2 : ℤ)) (t := t) ht0]
        calc ‖(-(t ^ (2 : ℕ)) : ℂ) * ψS.resToImagAxis (1 / t)‖
              = (t ^ (2 : ℕ)) * ‖ψS.resToImagAxis (1 / t)‖ := by simp
          _ ≤ 1 * Cψ0 := mul_le_mul (by simpa using pow_le_one₀ (n := 2) ht0.le ht.2) hψS'
            (norm_nonneg _) zero_le_one
          _ = Cψ0 := one_mul _
      calc ‖bLaplaceIntegrand u t‖
            = ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ * ‖(Real.exp (-π * u * t) : ℂ)‖ := by
              simp [bLaplaceIntegrand]
        _ ≤ ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ * 1 := mul_le_mul_of_nonneg_left (by
              rw [show ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) by
                simpa [Complex.ofReal_exp] using Complex.norm_exp_ofReal (-π * u * t)]
              exact Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, mul_nonneg hu0 ht0.le]))
              (norm_nonneg _)
        _ ≤ Cψ0 := by simpa using hψI
  rcases exists_ψI_bound_exp with ⟨CI, AI, hCI, hI⟩
  let A : ℝ := max AI 1
  have hint_mid : IntegrableOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioc (1 : ℝ) A) :=
    ((hcontIoi.mono fun t ht => lt_of_lt_of_le (by norm_num) ht.1).integrableOn_Icc
      (μ := (volume : Measure ℝ))).mono_set Set.Ioc_subset_Icc_self
  have hint_tail : IntegrableOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioi A) := by
    have hmeas : AEStronglyMeasurable (fun t : ℝ => bLaplaceIntegrand u t)
          (volume.restrict (Set.Ioi A)) :=
      (hcontIoi.mono fun t ht =>
        lt_trans (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _))
          ht).aestronglyMeasurable measurableSet_Ioi
    have hdom :
        ∀ᵐ t ∂(volume.restrict (Set.Ioi A)),
          ‖bLaplaceIntegrand u t‖ ≤ ‖(CI : ℂ) * (Real.exp (-(π * (u - 2)) * t) : ℂ)‖ := by
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans ht.le)
      have htIm : 0 < (((Complex.I : ℂ) * (t : ℂ) : ℂ)).im := by simpa using ht0
      calc ‖bLaplaceIntegrand u t‖
            = ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ * ‖(Real.exp (-π * u * t) : ℂ)‖ := by
              simp [bLaplaceIntegrand]
        _ = ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ * Real.exp (-π * u * t) := by
              rw [show ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) by
                simpa [Complex.ofReal_exp] using Complex.norm_exp_ofReal (-π * u * t)]
        _ ≤ (CI * Real.exp (2 * π * t)) * Real.exp (-π * u * t) :=
              mul_le_mul_of_nonneg_right (by
                simpa [show ψI' ((Complex.I : ℂ) * (t : ℂ)) =
                    ψI (⟨(Complex.I : ℂ) * (t : ℂ), htIm⟩ : ℍ) from by simp [ψI', ht0],
                  UpperHalfPlane.im] using
                  hI (⟨(Complex.I : ℂ) * (t : ℂ), htIm⟩ : ℍ)
                    (by simpa [UpperHalfPlane.im] using (le_max_left _ _).trans ht.le))
                (Real.exp_pos _).le
        _ = CI * Real.exp (-(π * (u - 2)) * t) := by
              simpa [mul_assoc] using congrArg (fun x : ℝ => CI * x)
                (MagicFunction.g.CohnElkies.exp_two_pi_mul_mul_exp_neg_pi_mul u t)
        _ = ‖(CI : ℂ) * (Real.exp (-(π * (u - 2)) * t) : ℂ)‖ := by
              rw [norm_mul, show ‖(CI : ℂ)‖ = CI from by simp [abs_of_nonneg hCI.le],
                show ‖(Real.exp (-(π * (u - 2)) * t) : ℂ)‖ = Real.exp (-(π * (u - 2)) * t) from by
                  simpa [Complex.ofReal_exp] using Complex.norm_exp_ofReal (-(π * (u - 2)) * t)]
    exact MeasureTheory.Integrable.mono (μ := volume.restrict (Set.Ioi A))
      (by simpa [IntegrableOn] using
        (show IntegrableOn (fun t : ℝ => Real.exp (-(π * (u - 2)) * t)) (Set.Ioi A) by
          simpa [mul_assoc] using exp_neg_integrableOn_Ioi (a := A) (b := π * (u - 2))
            (mul_pos Real.pi_pos (sub_pos.2 hu))).ofReal.const_mul (CI : ℂ))
      hmeas hdom
  rw [show Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) from by norm_num]
  exact hint_small.union <| by
    simpa [show Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) A ∪ Set.Ioi A by
      simpa using (Set.Ioc_union_Ioi_eq_Ioi (a := (1 : ℝ)) (b := A) (le_max_right _ _)).symm]
      using hint_mid.union hint_tail

/-! ## Contour integrands -/

/-- Exponential weight `exp(π i u z)` used in the contour integrands for `b'`. -/
@[expose] public def bContourWeight (u : ℝ) (z : ℂ) : ℂ :=
  cexp (π * (Complex.I : ℂ) * (u : ℂ) * z)

/-- Multiplicativity of `bContourWeight` with respect to addition. -/
public lemma bContourWeight_add (u : ℝ) (z w : ℂ) :
    bContourWeight u (z + w) = bContourWeight u z * bContourWeight u w := by
  simp [bContourWeight, mul_add, Complex.exp_add, mul_assoc]

/-- Contour integrand for the `ψI'` term (with a minus sign). -/
@[expose] public def bContourIntegrandI (u : ℝ) (z : ℂ) : ℂ :=
  -(ψI' z * bContourWeight u z)

/-- Contour integrand for the `ψT'` term. -/
@[expose] public def bContourIntegrandT (u : ℝ) (z : ℂ) : ℂ :=
  ψT' z * bContourWeight u z

/-- Contour integrand for the `ψS'` term. -/
@[expose] public def bContourIntegrandS (u : ℝ) (z : ℂ) : ℂ :=
  ψS' z * bContourWeight u z

/-- Evaluate `bContourWeight` on the imaginary axis: `bContourWeight u (I * t) = exp(-π u t)`. -/
public lemma bContourWeight_mul_I (u t : ℝ) :
    bContourWeight u ((Complex.I : ℂ) * (t : ℂ)) = (Real.exp (-π * u * t) : ℂ) := by
  simp [bContourWeight, show (π : ℂ) * (Complex.I : ℂ) * (u : ℂ) * ((Complex.I : ℂ) * (t : ℂ)) =
    (-(π : ℂ) * (u : ℂ) * (t : ℂ)) by ring_nf; simp [pow_two, Complex.I_mul_I]]

/-- Translate `ψT'` into `ψI'` by adding `1` in the upper half-plane. -/
public lemma ψT'_eq_ψI'_add_one (z : ℂ) (hz : 0 < z.im) :
    ψT' z = ψI' (z + (1 : ℂ)) := by
  simp [ψT', ψI', hz, ψT, modular_slash_T_apply,
    show ((1 : ℝ) +ᵥ ⟨z, hz⟩ : ℍ) = ⟨z + (1 : ℂ), by simpa using hz⟩ by ext1; simp; ring_nf]

/-- Specialize `ψT'_eq_ψI'_add_one` at `z = -1 + I * t`. -/
public lemma ψT'_neg_one_add_I_mul (t : ℝ) (ht : 0 < t) :
    ψT' ((-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) = ψI' ((Complex.I : ℂ) * (t : ℂ)) := by
  simpa [add_assoc, mul_assoc] using
    (ψT'_eq_ψI'_add_one (z := (-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) (by simpa [mul_assoc] using ht))

/-- Specialize `ψT'_eq_ψI'_add_one` at `z = 1 + I * t`. -/
public lemma ψT'_one_add_I_mul (t : ℝ) (ht : 0 < t) :
    ψT' ((1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) = ψI' ((Complex.I : ℂ) * (t : ℂ)) := by
  have hz0 : 0 < (((Complex.I : ℂ) * (t : ℂ)) : ℂ).im := by simpa using ht
  have hz1 : 0 < (((1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) : ℂ).im := by simpa [mul_assoc] using ht
  have htrans :
      ((1 : ℝ) +ᵥ ⟨(Complex.I : ℂ) * (t : ℂ), hz0⟩ : ℍ) =
        ⟨(1 : ℂ) + (Complex.I : ℂ) * (t : ℂ), hz1⟩ := by ext1; simp
  simpa [ψT', ψI', ht, modular_slash_T_apply, htrans] using
    congrArg (fun F : ℍ → ℂ => F ⟨(Complex.I : ℂ) * (t : ℂ), hz0⟩) ψT_slash_T

/-- Holomorphy of `bContourIntegrandT` on the open upper half-plane. -/
public lemma differentiableOn_bContourIntegrandT (u : ℝ) :
    DifferentiableOn ℂ (bContourIntegrandT u) {z : ℂ | 0 < z.im} := by
  have hExp : DifferentiableOn ℂ (bContourWeight u) {z : ℂ | 0 < z.im} := by
    simpa [bContourWeight] using (by fun_prop :
      Differentiable ℂ fun z : ℂ => cexp (π * (Complex.I : ℂ) * (u : ℂ) * z)).differentiableOn
  have hψT : DifferentiableOn ℂ (fun z : ℂ => ψT (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im} := by
    have hH2 := (UpperHalfPlane.mdifferentiable_iff (f := H₂)).1 mdifferentiable_H₂
    have hH3 := (UpperHalfPlane.mdifferentiable_iff (f := H₃)).1 mdifferentiable_H₃
    have hH4 := (UpperHalfPlane.mdifferentiable_iff (f := H₄)).1 mdifferentiable_H₄
    have hleft := (hH3.add hH4).div (hH2.pow 2) fun _ _ => pow_ne_zero 2 (H₂_ne_zero _)
    have hright := (hH2.add hH3).div (hH4.pow 2) fun _ _ => pow_ne_zero 2 (H₄_ne_zero _)
    refine (DifferentiableOn.const_mul (hleft.add hright) (128 : ℂ)).congr fun z _ => ?_
    simpa [mul_assoc] using congrArg (fun f : ℍ → ℂ => f (UpperHalfPlane.ofComplex z)) ψT_eq
  refine (hψT.mul hExp).congr fun z hz => ?_
  have hz' : 0 < z.im := hz
  simp [bContourIntegrandT, ψT', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']

/-- Continuity of `bContourIntegrandT` on the open upper half-plane. -/
public lemma continuousOn_bContourIntegrandT (u : ℝ) :
    ContinuousOn (bContourIntegrandT u) {z : ℂ | 0 < z.im} :=
  (differentiableOn_bContourIntegrandT (u := u)).continuousOn

/-! ## Laplace representation -/

private lemma setIntegral_Ioi0_eq_add_Ioc_Ioi {f : ℝ → ℂ}
    (hf : IntegrableOn f (Set.Ioi (0 : ℝ)) (μ := (volume : Measure ℝ))) :
    (∫ t in Set.Ioi (0 : ℝ), f t) =
      (∫ t in Set.Ioc (0 : ℝ) 1, f t) + (∫ t in Set.Ioi (1 : ℝ), f t) := by
  simpa [Set.Ioc_union_Ioi_eq_Ioi zero_le_one] using MeasureTheory.setIntegral_union
    (μ := (volume : Measure ℝ)) (f := f) Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hf.mono_set fun _ ht ↦ ht.1) (hf.mono_set (Set.Ioi_subset_Ioi zero_le_one))

/-- Blueprint `prop:b-double-zeros`. -/
public theorem bRadial_eq_laplace_psiI_main {u : ℝ} (hu : 2 < u) :
    b' u =
      (-4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ),
              ψI' ((Complex.I : ℂ) * (t : ℂ)) *
                Real.exp (-π * u * t)) := by
  open MagicFunction.b.RealIntegrals in
  rw [MagicFunction.g.CohnElkies.b'_eq_realIntegrals_b' (u := u) (by linarith : 0 ≤ u)]
  let VI : ℂ := ∫ t in Set.Ioi (0 : ℝ), bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ))
  rw [MagicFunction.b.RealIntegrals.b', show (-4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) * (∫ t in Set.Ioi (0 : ℝ),
          ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)) =
      (Complex.I : ℂ) * (((2 : ℂ) - Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) -
        Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I))) * VI) by
      rw [show (∫ t in Set.Ioi (0 : ℝ),
            ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)) = -VI by
        rw [← MeasureTheory.integral_neg]
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun _ _ => by
          simp [bContourIntegrandI, bContourWeight_mul_I, mul_assoc],
        show (2 : ℂ) - Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) -
            Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) =
            ((4 * (Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) by
        simpa using (two_sub_exp_pi_mul_I_sub_exp_neg_pi_mul_I u).trans
          (congrArg (fun r : ℝ => (r : ℂ)) (two_sub_two_cos_eq_four_sin_sq u))]
      simp [mul_assoc, mul_comm]]
  have hStrip0 : (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) ⊆ {z : ℂ | 0 < z.im} :=
    fun _ hz => lt_of_lt_of_le zero_lt_one (by simpa using hz.2)
  have hintI : IntegrableOn (fun t : ℝ => bContourIntegrandI u (I * (t : ℂ)))
      (Set.Ioi (0 : ℝ)) := by
    have hneg : IntegrableOn (fun t : ℝ => -bLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) :=
      (bLaplaceIntegral_convergent (u := u) hu).neg
    simpa [bContourIntegrandI, bContourWeight_mul_I, bLaplaceIntegrand, mul_assoc] using hneg
  rcases exists_ψI_bound_exp with ⟨Cψ, Aψ, _, hψbd⟩
  have hintT_center : IntegrableOn (fun t : ℝ => bContourIntegrandT u (I * (t : ℂ)))
      (Set.Ioi (1 : ℝ)) := by
    let A : ℝ := max 1 Aψ
    let f : ℝ → ℂ := fun t : ℝ => bContourIntegrandT u (I * (t : ℂ))
    have hmaps_Ioi (S : Set ℝ) (hS : ∀ t ∈ S, 0 < t) :
        Set.MapsTo (fun t : ℝ => I * (t : ℂ)) S {z : ℂ | 0 < z.im} :=
      fun t ht => by simpa using hS t ht
    have hdom : ∀ t : ℝ, t ∈ Set.Ioi A →
        ‖f t‖ ≤ Cψ * Real.exp (-(π * (u - 2)) * t) := fun t ht => by
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ((le_max_left 1 Aψ).trans ht.le)
      have hzI : 0 < ((I * (t : ℂ) + (1 : ℂ)).im) := by simpa [add_assoc, mul_assoc] using ht0
      rw [show ‖f t‖ = ‖ψT' (I * (t : ℂ))‖ * Real.exp (-π * u * t) by
            simp [f, bContourIntegrandT, bContourWeight_mul_I, mul_assoc,
              -Complex.ofReal_exp, Complex.norm_real, abs_of_nonneg (Real.exp_pos _).le],
        ← MagicFunction.g.CohnElkies.exp_two_pi_mul_mul_exp_neg_pi_mul, ← mul_assoc,
        show ψT' (I * (t : ℂ)) = ψI ⟨I * (t : ℂ) + (1 : ℂ), hzI⟩ by
          rw [show ψT' ((Complex.I : ℂ) * (t : ℂ)) =
              ψI' (((Complex.I : ℂ) * (t : ℂ)) + (1 : ℂ)) by
            simpa [add_assoc] using
              (ψT'_eq_ψI'_add_one (z := (Complex.I : ℂ) * (t : ℂ)) (by simpa using ht0))]
          simp [ψI', ht0]]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      simpa [UpperHalfPlane.im, add_assoc, mul_assoc] using hψbd _ (by
        simpa [UpperHalfPlane.im, add_assoc, mul_assoc] using
          (le_max_right 1 Aψ).trans ht.le :
        Aψ ≤ UpperHalfPlane.im ⟨I * (t : ℂ) + (1 : ℂ), hzI⟩)
    rw [show Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) A ∪ Set.Ioi A from
      (Set.Ioc_union_Ioi_eq_Ioi (a := (1 : ℝ)) (b := A) (le_max_left 1 Aψ)).symm]
    refine (((continuousOn_bContourIntegrandT (u := u)).comp (by fun_prop)
        (hmaps_Ioi _ fun _ ht => lt_of_lt_of_le (by norm_num) ht.1)).integrableOn_compact
          isCompact_Icc |>.mono_set Set.Ioc_subset_Icc_self).union (by
      simpa [MeasureTheory.IntegrableOn] using
        (show Integrable (fun t : ℝ => Cψ * Real.exp (-(π * (u - 2)) * t))
          (volume.restrict (Set.Ioi A)) by
          simpa [MeasureTheory.IntegrableOn, mul_assoc] using
            (exp_neg_integrableOn_Ioi (a := A) (b := π * (u - 2))
              (mul_pos Real.pi_pos (sub_pos.2 hu))).const_mul Cψ).mono'
          (((continuousOn_bContourIntegrandT (u := u)).comp (by fun_prop)
            (hmaps_Ioi _ fun _ ht => lt_of_lt_of_le (by positivity) ht.le)).aestronglyMeasurable
            measurableSet_Ioi)
          (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by simpa using hdom t ht))
  have hintT_shift (a : ℂ) (hψ : ∀ t : ℝ, 0 < t → ψT' (a + I * (t : ℂ)) = ψI' (I * (t : ℂ))) :
      IntegrableOn (fun t : ℝ => bContourIntegrandT u (a + I * (t : ℂ))) (Set.Ioi (1 : ℝ)) := by
    refine (show IntegrableOn (fun t : ℝ =>
        (-bContourIntegrandI u (I * (t : ℂ))) * bContourWeight u a) (Set.Ioi (1 : ℝ)) by
      simpa [mul_assoc] using
        ((hintI.mono_set (Set.Ioi_subset_Ioi zero_le_one)).neg.mul_const
          (bContourWeight u a))).congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp [bContourIntegrandT, bContourIntegrandI, hψ t (lt_trans (by norm_num) ht),
      bContourWeight_add, mul_comm, mul_left_comm]
  have htendstoT : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖bContourIntegrandT u z‖ < ε := by
    intro ε hε
    have htend : Tendsto (fun y : ℝ => Cψ * Real.exp (-((π * (u - 2)) * y))) atTop (𝓝 (0 : ℝ)) := by
      simpa [mul_assoc] using tendsto_const_nhds.mul
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (by simpa [mul_assoc, mul_comm, mul_left_comm] using
            tendsto_id.const_mul_atTop (mul_pos Real.pi_pos (sub_pos.2 hu))))
    rcases Filter.eventually_atTop.1 (htend.eventually (Iio_mem_nhds hε)) with ⟨Mε, hMε⟩
    refine ⟨max (max 1 Aψ) Mε, fun z hzM => ?_⟩
    have hzpos : 0 < z.im := lt_of_lt_of_le zero_lt_one
      (((le_max_left 1 Aψ).trans (le_max_left _ _) : (1 : ℝ) ≤ _).trans hzM)
    have hzI : 0 < (z + (1 : ℂ)).im := by simpa using hzpos
    rw [show ‖bContourIntegrandT u z‖ = ‖ψT' z‖ * ‖bContourWeight u z‖ by
          simp [bContourIntegrandT], ψT'_eq_ψI'_add_one z hzpos,
        show ψI' (z + (1 : ℂ)) = ψI ⟨z + (1 : ℂ), hzI⟩ by simp [ψI', hzpos],
        show ‖bContourWeight u z‖ = Real.exp (-π * u * z.im) by
          simp [bContourWeight, Complex.norm_exp]]
    refine lt_of_le_of_lt ?_ (hMε z.im ((le_max_right _ _).trans hzM))
    refine (mul_le_mul_of_nonneg_right (show
      ‖ψI (⟨z + (1 : ℂ), hzI⟩ : ℍ)‖ ≤ Cψ * Real.exp (2 * π * z.im) by
      simpa [UpperHalfPlane.im, add_assoc] using hψbd _ (by
        simpa [UpperHalfPlane.im, add_assoc] using
          (((le_max_right 1 Aψ).trans (le_max_left _ _)).trans hzM : Aψ ≤ z.im) :
        Aψ ≤ UpperHalfPlane.im (⟨z + (1 : ℂ), hzI⟩ : ℍ))) (Real.exp_pos _).le).trans
      (le_of_eq (by rw [mul_assoc, ← Real.exp_add]; ring_nf))
  have hRectLeft :
      (∫ (x : ℝ) in (0 : ℝ)..1,
            bContourIntegrandT u ((x : ℂ) + (1 : ℂ) * Complex.I - 1)) +
          (I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ), bContourIntegrandT u (I * (t : ℂ))) -
        (I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ),
              bContourIntegrandT u ((-1 : ℂ) + I * (t : ℂ))) = 0 := by
    let f : ℂ → ℂ := fun z : ℂ => bContourIntegrandT u (z - 1)
    simpa [min_eq_left zero_le_one, max_eq_right zero_le_one, f, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm, mul_assoc, mul_comm, mul_left_comm] using
      integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
        (y := (1 : ℝ)) (f := f) (x₁ := (0 : ℝ)) (x₂ := (1 : ℝ))
        ((continuousOn_bContourIntegrandT (u := u)).comp
          (continuousOn_id.sub continuousOn_const) fun z hz => by
            simpa [sub_eq_add_neg] using hStrip0 (by simpa [Set.uIcc_of_le zero_le_one] using hz))
        (s := (∅ : Set ℂ)) (by simp) (fun z hz => by
          have hzpos' : 0 < (z - 1).im := by
            simpa [sub_eq_add_neg] using lt_trans zero_lt_one ((Set.mem_Ioi).1 hz.1.2)
          simpa [f] using ((differentiableOn_bContourIntegrandT (u := u) (z - 1)
            hzpos').differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hzpos')).comp
            z (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z - 1) z))
        (by simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_comm,
            mul_left_comm] using hintT_shift (-1 : ℂ) fun t ht0 ↦
              by simpa [add_assoc] using ψT'_neg_one_add_I_mul (t := t) ht0)
        (by simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_comm,
            mul_left_comm] using hintT_center)
        (fun ε hε => let ⟨M, hM⟩ := htendstoT ε hε
          ⟨M, fun z hz => by simpa [f] using hM (z - 1) (by simpa [sub_eq_add_neg] using hz)⟩)
  have hRectRight :
      (∫ (x : ℝ) in (1 : ℝ)..0, bContourIntegrandT u ((x : ℂ) + (1 : ℂ) * Complex.I)) +
          (I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ), bContourIntegrandT u (I * (t : ℂ))) -
            (I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ),
              bContourIntegrandT u ((1 : ℂ) + I * (t : ℂ))) = 0 := by
    simpa [min_eq_right zero_le_one, max_eq_left zero_le_one, mul_assoc, mul_comm, mul_left_comm,
      add_assoc, add_left_comm, add_comm] using
      integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
        (y := (1 : ℝ)) (f := bContourIntegrandT u) (x₁ := (1 : ℝ)) (x₂ := (0 : ℝ))
        (by simpa [Set.uIcc_comm] using
          (continuousOn_bContourIntegrandT (u := u)).mono hStrip0) (s := (∅ : Set ℂ)) (by simp)
        (fun z hz ↦ have hzpos : 0 < z.im := lt_trans zero_lt_one (by
          simpa [min_eq_right zero_le_one, max_eq_left zero_le_one, Set.mem_Ioi] using hz.1.2)
          (differentiableOn_bContourIntegrandT (u := u) z hzpos).differentiableAt
            (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hzpos))
        (by simpa [mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm] using
          hintT_shift (1 : ℂ) fun t ht0 ↦
            by simpa [add_assoc] using ψT'_one_add_I_mul (t := t) ht0)
        (by simpa [mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm]
          using hintT_center) htendstoT
  have hmem_Icc : ∀ {x : ℝ}, x ∈ Set.uIcc (0 : ℝ) 1 → x ∈ Set.Icc (0 : ℝ) 1 :=
    fun hx => by simpa [Set.uIcc_of_le zero_le_one] using hx
  have hJ2_top : J₂' u =
      ∫ (x : ℝ) in (0 : ℝ)..1,
        bContourIntegrandT u ((x : ℂ) + (1 : ℂ) * Complex.I - 1) := by
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    simp [bContourIntegrandT, bContourWeight, sub_eq_add_neg, mul_assoc,
      show z₂' x = (x : ℂ) + (1 : ℂ) * Complex.I - 1 by
        have h := z₂'_eq_of_mem (t := x) (hmem_Icc hx); push_cast at h; linear_combination h]
  have hJ4_top : J₄' u =
      ∫ (x : ℝ) in (1 : ℝ)..0,
        bContourIntegrandT u ((x : ℂ) + (1 : ℂ) * Complex.I) := by
    dsimp [J₄']
    let g : ℝ → ℂ := fun x : ℝ => bContourIntegrandT u ((x : ℂ) + (1 : ℂ) * Complex.I)
    rw [intervalIntegral.integral_congr fun t ht => show _ = (-1 : ℂ) * g (1 - t) by
        simp [g, bContourIntegrandT, bContourWeight, sub_eq_add_neg, mul_assoc,
          show z₄' t = ((1 - t : ℝ) : ℂ) + (1 : ℂ) * Complex.I by
            have h := z₄'_eq_of_mem (t := t) (hmem_Icc ht)
            push_cast at h ⊢; linear_combination h],
      show (∫ t in (0 : ℝ)..1, (-1 : ℂ) * g (1 - t)) = ∫ t in (1 : ℝ)..0, g t by
        simp [show (∫ t in (0 : ℝ)..1, g (1 - t)) = ∫ t in (0 : ℝ)..1, g t by norm_num,
          (intervalIntegral.integral_symm (a := (0 : ℝ)) (b := (1 : ℝ)) (f := g)).symm]]
  have hJ2_ray : J₂' u =
      (I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ), bContourIntegrandT u ((-1 : ℂ) + I * (t : ℂ))) -
        (I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ), bContourIntegrandT u (I * (t : ℂ))) := by
    simpa [hJ2_top] using eq_sub_of_add_eq (sub_eq_zero.mp hRectLeft)
  have hJ4_ray : J₄' u =
      (I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ), bContourIntegrandT u ((1 : ℂ) + I * (t : ℂ))) -
        (I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ), bContourIntegrandT u (I * (t : ℂ))) := by
    simpa [hJ4_top] using eq_sub_of_add_eq (sub_eq_zero.mp hRectRight)
  have hJ_vert_aux (a : ℂ) (zp : ℝ → ℂ)
      (hzp : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → zp t = a + I * (t : ℂ)) :
      (∫ t in (0 : ℝ)..1, (I : ℂ) * ψT' (zp t) * cexp (π * (I : ℂ) * (u : ℂ) * zp t)) =
        (I : ℂ) * (∫ t in Set.Ioc (0 : ℝ) 1, bContourIntegrandT u (a + I * (t : ℂ))) := by
    rw [intervalIntegral.integral_congr fun t ht =>
        show _ = (I : ℂ) * bContourIntegrandT u (a + I * (t : ℂ)) by
          simp [bContourIntegrandT, bContourWeight, hzp (hmem_Icc ht), mul_assoc],
      intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le zero_le_one]
  have hJ1_set : J₁' u =
      (I : ℂ) * (∫ t in Set.Ioc (0 : ℝ) 1, bContourIntegrandT u ((-1 : ℂ) + I * (t : ℂ))) :=
    hJ_vert_aux (-1 : ℂ) z₁' fun ht => by simpa using z₁'_eq_of_mem ht
  have hJ3_set : J₃' u =
      (I : ℂ) * (∫ t in Set.Ioc (0 : ℝ) 1, bContourIntegrandT u ((1 : ℂ) + I * (t : ℂ))) :=
    hJ_vert_aux (1 : ℂ) z₃' fun ht => by simpa using z₃'_eq_of_mem ht
  have hJ5_set : J₅' u =
      (2 : ℂ) * (I : ℂ) *
        (∫ t in Set.Ioc (0 : ℝ) 1, bContourIntegrandI u (I * (t : ℂ))) := by
    dsimp [J₅']
    rw [intervalIntegral.integral_congr fun t ht =>
        show _ = -(I : ℂ) * bContourIntegrandI u (I * (t : ℂ)) by
          simp [bContourIntegrandI, bContourWeight, mul_assoc, mul_left_comm, mul_comm,
            show z₅' t = I * (t : ℂ) by simpa using z₅'_eq_of_mem (t := t) (hmem_Icc ht)]]
    simp only [neg_mul, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      mul_neg, neg_neg]; rw [intervalIntegral.integral_of_le zero_le_one]; ring
  have hJ6_set : J₆' u =
      (-2 : ℂ) * (I : ℂ) *
        (∫ t in Set.Ioi (1 : ℝ), bContourIntegrandS u (I * (t : ℂ))) := by
    dsimp [J₆']
    rw [MeasureTheory.setIntegral_congr_fun (s := Set.Ici (1 : ℝ)) measurableSet_Ici
        fun t ht => show _ = (I : ℂ) * bContourIntegrandS u (I * (t : ℂ)) by
          simp [bContourIntegrandS, bContourWeight, mul_assoc, mul_left_comm, mul_comm,
            show z₆' t = I * (t : ℂ) by simpa using z₆'_eq_of_mem (t := t) ht],
      MeasureTheory.integral_Ici_eq_integral_Ioi, MeasureTheory.integral_const_mul, mul_assoc]
  have hShift_point (a : ℂ) (hψa : ∀ t : ℝ, 0 < t → ψT' (a + I * (t : ℂ)) = ψI' (I * (t : ℂ)))
      (t : ℝ) (ht : 0 < t) : bContourIntegrandT u (a + I * (t : ℂ)) =
        bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u a) := by
    simp [bContourIntegrandT, bContourIntegrandI, hψa t ht, mul_assoc,
      show bContourWeight u (a + I * (t : ℂ)) =
        bContourWeight u (I * (t : ℂ)) * bContourWeight u a by
        simpa [add_assoc, add_left_comm, add_comm] using
          bContourWeight_add (u := u) (I * (t : ℂ)) a]
  have hITS (z : ℂ) (hz : 0 < z.im) :
      bContourIntegrandT u z + bContourIntegrandS u z = -bContourIntegrandI u z := by
    simp [bContourIntegrandI, bContourIntegrandT, bContourIntegrandS, add_mul,
      show ψI' z = ψT' z + ψS' z by
        simpa [ψI', ψT', ψS', hz] using congrArg (fun F : ℍ → ℂ ↦ F ⟨z, hz⟩) ψI_eq_add_ψT_ψS]
  have hCenter_split : (∫ t in Set.Ioi (1 : ℝ), bContourIntegrandS u (I * (t : ℂ))) =
      -(∫ t in Set.Ioi (1 : ℝ), bContourIntegrandI u (I * (t : ℂ))) -
        (∫ t in Set.Ioi (1 : ℝ), bContourIntegrandT u (I * (t : ℂ))) := by
    rw [show (∫ t in Set.Ioi (1 : ℝ), bContourIntegrandS u ((Complex.I : ℂ) * (t : ℂ))) =
        ∫ t in Set.Ioi (1 : ℝ),
          ((-bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ))) -
            bContourIntegrandT u ((Complex.I : ℂ) * (t : ℂ))) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => by
        have hz : 0 < (((Complex.I : ℂ) * (t : ℂ) : ℂ)).im := by
          simpa using lt_trans zero_lt_one ht
        with_reducible exact eq_sub_iff_add_eq'.mpr (hITS (I * ↑t) hz)]
    simpa [MeasureTheory.integral_neg, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      MeasureTheory.integral_sub (μ := volume.restrict (Set.Ioi (1 : ℝ)))
        (hintI.mono_set (Set.Ioi_subset_Ioi zero_le_one)).neg hintT_center
  have hsum : J₁' u + J₂' u + J₃' u + J₄' u + J₅' u + J₆' u =
      (Complex.I : ℂ) *
        (((2 : ℂ) - bContourWeight u (1 : ℂ) - bContourWeight u (-1 : ℂ)) * VI) := by
    rw [hJ2_ray, hJ4_ray, hJ1_set, hJ3_set, hJ5_set, hJ6_set]
    have hfull (a : ℂ) (hpt : ∀ t : ℝ, 0 < t →
        bContourIntegrandT u (a + I * (t : ℂ)) =
          bContourIntegrandI u (I * (t : ℂ)) * (-bContourWeight u a)) :
        (∫ t in Set.Ioc (0 : ℝ) 1, bContourIntegrandT u (a + I * (t : ℂ))) +
            (∫ t in Set.Ioi (1 : ℝ), bContourIntegrandT u (a + I * (t : ℂ))) =
          (-VI) * bContourWeight u a := by
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => hpt t ht.1,
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht =>
          hpt t (lt_trans (by norm_num) ht)]
      simpa [mul_assoc, mul_left_comm, mul_comm, VI] using
        (Eq.symm (setIntegral_Ioi0_eq_add_Ioc_Ioi
          (by simpa [mul_assoc] using hintI.mul_const (-bContourWeight u a)))).trans
          (MeasureTheory.integral_mul_const (μ := volume.restrict (Set.Ioi (0 : ℝ)))
            (r := -bContourWeight u a) (f := fun t : ℝ => bContourIntegrandI u (I * (t : ℂ))))
    have hLeft_full := hfull (-1 : ℂ) (hShift_point (-1 : ℂ) ψT'_neg_one_add_I_mul)
    have hRight_full := hfull (1 : ℂ) (hShift_point (1 : ℂ) ψT'_one_add_I_mul)
    have hCenterVI := (setIntegral_Ioi0_eq_add_Ioc_Ioi (f := fun t : ℝ =>
      bContourIntegrandI u (I * (t : ℂ))) hintI).symm
    simp only [smul_eq_mul, neg_mul]; grind only
  simpa [bContourWeight, sub_eq_add_neg, add_left_comm, add_comm, mul_assoc, mul_left_comm,
    mul_comm] using hsum

end

end MagicFunction.g.CohnElkies.IntegralReps
