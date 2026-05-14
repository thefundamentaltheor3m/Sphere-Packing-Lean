module
public import SpherePacking.Basic.SpherePacking
public import SpherePacking.Basic.PeriodicPacking.Aux
public import SpherePacking.MagicFunction.b.Schwartz.Basic
public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.IntegralLemmas
public import SpherePacking.ModularForms.FG.Basic
public import SpherePacking.ModularForms.EisensteinBase
public import SpherePacking.MagicFunction.b.Psi
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import SpherePacking.ModularForms.SlashActionAuxil
import SpherePacking.ForMathlib.DerivHelpers
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import SpherePacking.CohnElkies.LPBound
import SpherePacking.MagicFunction.a.SpecialValues
import SpherePacking.MagicFunction.a.Eigenfunction.FourierPermutations
import SpherePacking.MagicFunction.b.Eigenfunction.FourierPermutations
import SpherePacking.Integration.Measure
import SpherePacking.ModularForms.Delta
import SpherePacking.MagicFunction.b.PsiBounds
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.Cancellation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay
import SpherePacking.ModularForms.FG.Inequalities
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Upper bound for sphere packing in dimension 8

Defines `scaledMagic`, obtained from Viazovska's magic function `g` by precomposing with scaling
by `Real.sqrt 2`, transfers the Cohn-Elkies sign conditions from `g` to the scaled function
`scaledMagic`, and uses the Cohn-Elkies linear programming bound to obtain an upper bound for
`SpherePackingConstant 8`. Includes `g_real` / `g_real_fourier` (blueprint `thm:g1`/`thm:g`)
showing that `g` and its Fourier transform are real-valued, and packages the final main theorem.

Also contains basic properties of the E₈ lattice (merged from `E8.Packing`): the E₈ lattice as
the parity submodule of `Fin 8 → R` and as the ℤ-span of `E8Matrix`, integrality of squared
norms, and the periodic sphere packing `E8Packing` of density `π^4 / 384`.

## Main statements
* `SpherePacking.SpherePackingConstant_le_E8Packing_density`
* `SpherePacking.MainTheorem`
* `E8Packing_density`
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

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Interval Topology
open MeasureTheory Real Complex Filter Set
open SpherePacking.Integration (μIciOne)
open SpherePacking intervalIntegral

noncomputable section BPrimeExtension

open MagicFunction.b.RealIntegrals MagicFunction.Parametrisations

/-- Complexifications `J₁'C` … `J₆'C` of the real integrals `J₁'` … `J₆'`. -/
def J₁'C (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1,
  (Complex.I : ℂ) * ψT' (z₁' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₁' t))

def J₂'C (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1,
  ψT' (z₂' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₂' t))

def J₃'C (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1,
  (Complex.I : ℂ) * ψT' (z₃' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₃' t))

def J₄'C (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1,
  (-1 : ℂ) * ψT' (z₄' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₄' t))

def J₅'C (u : ℂ) : ℂ := -2 * ∫ t in (0 : ℝ)..1,
  (Complex.I : ℂ) * ψI' (z₅' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₅' t))

def J₆'C (u : ℂ) : ℂ := -2 * ∫ t in Set.Ici (1 : ℝ),
  (Complex.I : ℂ) * ψS' (z₆' t) * Complex.exp (π * (Complex.I : ℂ) * u * (z₆' t))

/-- Analytic extension of `b'` defined as the sum `J₁'C + … + J₆'C`. -/
public def bPrimeC (u : ℂ) : ℂ :=
  J₁'C u + J₂'C u + J₃'C u + J₄'C u + J₅'C u + J₆'C u

/-- On real parameters, `bPrimeC` agrees with the real function `b'`. -/
public lemma bPrimeC_ofReal (u : ℝ) : bPrimeC (u : ℂ) = MagicFunction.b.RealIntegrals.b' u := by
  simp [bPrimeC, MagicFunction.b.RealIntegrals.b', J₁'C, J₂'C, J₃'C, J₄'C, J₅'C, J₆'C,
    J₁', J₂', J₃', J₄', J₅', J₆']

open ModularForm ModularGroup UpperHalfPlane

lemma mem_Ioc_of_mem_uIoc {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht

private lemma continuousOn_ψT'_comp (z : ℝ → ℂ) (hz : Continuous z)
    (hIm : ∀ t ∈ Ι (0 : ℝ) 1, 0 < (z t).im) :
    ContinuousOn (fun t : ℝ => ψT' (z t)) (Ι (0 : ℝ) 1) :=
  continuousOn_iff_continuous_restrict.2 <| by
    simpa [Set.restrict] using SpherePacking.Integration.continuous_comp_upperHalfPlane_mk
      (α := Ι (0 : ℝ) 1) (ψT := ψT) (ψT' := ψT') MagicFunction.b.PsiBounds.continuous_ψT
      (z := fun t : Ι (0 : ℝ) 1 => z (t : ℝ)) (hz.comp continuous_subtype_val)
      (fun t => hIm (t : ℝ) t.2) (fun t => by simp [ψT', hIm (t : ℝ) t.2])

private lemma exists_bound_norm_ψT'_comp_of_im_pos_all (z : ℝ → ℂ) (hz : Continuous z)
    (hIm : ∀ t : ℝ, 0 < (z t).im) :
    ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z t)‖ ≤ M :=
  Integration.exists_bound_norm_uIoc_zero_one_of_continuous (fun t => ψT' (z t))
    (SpherePacking.Integration.continuous_comp_upperHalfPlane_mk (ψT := ψT) (ψT' := ψT')
      MagicFunction.b.PsiBounds.continuous_ψT (z := z) hz hIm fun t => by simp [ψT', hIm t])

lemma exists_bound_norm_ψI'_z₅' :
    ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψI' (z₅' t)‖ ≤ M := by
  obtain ⟨M, hM⟩ := MagicFunction.b.PsiBounds.exists_bound_norm_ψS_resToImagAxis_Ici_one
  refine ⟨M, fun t ht => ?_⟩
  have htIoc : t ∈ Ioc (0 : ℝ) 1 := mem_Ioc_of_mem_uIoc ht
  refine (norm_modular_rewrite_Ioc_bound 2 ψS ψI' z₅' b.Schwartz.J5Smooth.ψI'_z₅'_eq htIoc
    (hM (1 / t) (by simpa using (one_le_div htIoc.1).2 htIoc.2))).trans ?_
  simpa [mul_one] using mul_le_mul_of_nonneg_left
    (by simpa using pow_le_pow_left₀ htIoc.1.le htIoc.2 2 : t ^ 2 ≤ (1 : ℝ))
    ((norm_nonneg (ψS.resToImagAxis 1)).trans (hM 1 (by norm_num)))

lemma norm_z₃'_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖z₃' t‖ ≤ 2 := by
  have hz : z₃' t = (1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) := by simp [z₃'_eq_of_mem (t := t) ht]
  have h := norm_add_le (1 : ℂ) ((Complex.I : ℂ) * (t : ℂ))
  rw [hz]; simp [Complex.norm_real, abs_of_nonneg ht.1] at h; linarith [ht.2]

private lemma norm_add_I_le_three (a : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ha : ‖a‖ ≤ 1 + t) : ‖a + (Complex.I : ℂ)‖ ≤ 3 := by
  have h := norm_add_le a (Complex.I : ℂ); simp at h; linarith [ht.2]

/-- Shared differentiability wrapper for `J₁'C`–`J₅'C`. -/
private lemma integral_ψ_exp_differentiable
    {ψ : ℂ → ℂ} {z : ℝ → ℂ} {Mψ Cz : ℝ}
    (hψz_cont : ContinuousOn (fun t : ℝ => ψ (z t)) (Ι (0 : ℝ) 1))
    (hz_cont : Continuous z)
    (hψz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖ψ (z t)‖ ≤ Mψ)
    (hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ Cz) :
    Differentiable ℂ
      (fun u : ℂ => ∫ t in (0 : ℝ)..1,
        ψ (z t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z t)) := fun u0 => by
  have hEq : (fun u : ℂ => ∫ t in (0 : ℝ)..1,
        ψ (z t) * Complex.exp (u * ((π : ℂ) * (Complex.I : ℂ) * z t))) =
      fun u : ℂ => ∫ t in (0 : ℝ)..1,
        ψ (z t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z t) := by
    funext u; congr 1; funext t; congr 2; ring
  exact hEq ▸ differentiableAt_intervalIntegral_mul_exp (u0 := u0) (Cbase := Mψ) (K := Cz * π)
    hψz_cont (continuous_const.mul hz_cont).continuousOn hψz_bound
    (fun t ht => by
      rw [norm_mul, show ‖(π : ℂ) * (Complex.I : ℂ)‖ = (π : ℝ) by
        simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le], mul_comm]
      gcongr; exact hz_bound t ht)

lemma J₁'C_differentiable : Differentiable ℂ J₁'C :=
  let ⟨_, hMψ⟩ : ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z₁' t)‖ ≤ M :=
    exists_bound_norm_ψI'_z₅'.imp fun _ hM t ht => by
      simpa [MagicFunction.b.PsiParamRelations.ψT'_z₁'_eq_ψI'_z₅' (t := t)
        (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht))] using hM t ht
  (show J₁'C = fun u : ℂ => (Complex.I : ℂ) * ∫ t in (0 : ℝ)..1,
      ψT' (z₁' t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z₁' t) from
    funext fun u => by simp [J₁'C, ← intervalIntegral.integral_const_mul, mul_assoc]) ▸
    (differentiable_const (Complex.I : ℂ)).mul (integral_ψ_exp_differentiable (Cz := 2)
      (continuousOn_ψT'_comp z₁' continuous_z₁' fun t ht => im_z₁'_pos (mem_Ioc_of_mem_uIoc ht))
      continuous_z₁' hMψ (fun t _ => norm_z₁'_le_two t))

lemma J₂'C_differentiable : Differentiable ℂ J₂'C :=
  let ⟨_, hMψ⟩ := exists_bound_norm_ψT'_comp_of_im_pos_all z₂' continuous_z₂' im_z₂'_pos_all
  integral_ψ_exp_differentiable (Cz := 3)
    (continuousOn_ψT'_comp z₂' continuous_z₂'
      fun _ ht => im_z₂'_pos (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)))
    continuous_z₂' hMψ (fun t ht => by
      have htic := mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)
      exact (show z₂' t = ((-1 : ℂ) + (t : ℂ)) + (Complex.I : ℂ) by
          simp [z₂'_eq_of_mem (t := t) htic, add_comm]) ▸ norm_add_I_le_three _ htic
            (by simpa [Complex.norm_real, abs_of_nonneg htic.1] using norm_add_le (-1 : ℂ) (t : ℂ)))

lemma J₃'C_differentiable : Differentiable ℂ J₃'C :=
  let ⟨_, hMψ⟩ : ∃ M, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z₃' t)‖ ≤ M :=
    exists_bound_norm_ψI'_z₅'.imp fun _ hM t ht => by
      simpa [MagicFunction.b.PsiParamRelations.ψT'_z₃'_eq_ψI'_z₅' (t := t)
        (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht))] using hM t ht
  (show J₃'C = fun u : ℂ => (Complex.I : ℂ) * ∫ t in (0 : ℝ)..1,
      ψT' (z₃' t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z₃' t) from
    funext fun u => by simp [J₃'C, ← intervalIntegral.integral_const_mul, mul_assoc]) ▸
    (differentiable_const (Complex.I : ℂ)).mul (integral_ψ_exp_differentiable (Cz := 2)
      (continuousOn_ψT'_comp z₃' continuous_z₃' fun t ht => im_z₃'_pos (mem_Ioc_of_mem_uIoc ht))
      continuous_z₃' hMψ (fun t ht => norm_z₃'_le t (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht))))

lemma J₄'C_differentiable : Differentiable ℂ J₄'C :=
  let ⟨_, hMψ⟩ := exists_bound_norm_ψT'_comp_of_im_pos_all z₄' continuous_z₄' im_z₄'_pos_all
  (show J₄'C = fun u : ℂ => (-1 : ℂ) * ∫ t in (0 : ℝ)..1,
      ψT' (z₄' t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z₄' t) from
    funext fun u => by simp [J₄'C, ← intervalIntegral.integral_const_mul, mul_assoc]) ▸
    (differentiable_const (-1 : ℂ)).mul (integral_ψ_exp_differentiable (Cz := 3)
      (continuousOn_ψT'_comp z₄' continuous_z₄'
        fun t ht => im_z₄'_pos (mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)))
      continuous_z₄' hMψ (fun t ht => by
        have htic := mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)
        exact (show z₄' t = ((1 : ℂ) + (-(t : ℂ))) + (Complex.I : ℂ) by
            simp [z₄'_eq_of_mem (t := t) htic, sub_eq_add_neg, add_comm]) ▸ norm_add_I_le_three _ htic
              ((norm_add_le _ _).trans (by simp [Complex.norm_real, abs_of_nonneg htic.1]))))

private lemma continuousOn_ψI'_z₅' :
    ContinuousOn (fun t : ℝ => ψI' (z₅' t)) (Ι (0 : ℝ) 1) := by
  have hcont : Continuous fun t : Ioc (0 : ℝ) 1 => ψI' (z₅' (t : ℝ)) := by
    let zH : Ioc (0 : ℝ) 1 → ℍ := fun t => ⟨z₅' (t : ℝ), im_z₅'_pos (t := (t : ℝ)) t.2⟩
    have hzH : Continuous zH := by
      simpa [zH] using Continuous.upperHalfPlaneMk
        (continuous_z₅'.comp continuous_subtype_val : Continuous fun t : Ioc (0:ℝ) 1 => z₅' (t:ℝ))
        (fun t => im_z₅'_pos (t := (t : ℝ)) t.2)
    have hEq : (fun t : Ioc (0 : ℝ) 1 => ψI' (z₅' (t : ℝ))) = fun t => ψI (zH t) := by
      funext t; simp [ψI', zH, im_z₅'_pos (t := (t : ℝ)) t.2]
    simpa [hEq] using b.PsiBounds.continuous_ψI.comp hzH
  simpa using (continuousOn_iff_continuous_restrict).2 (by simpa [Set.restrict] using hcont)

lemma J₅'C_differentiable : Differentiable ℂ J₅'C :=
  let ⟨_, hMψ⟩ := exists_bound_norm_ψI'_z₅'
  (show J₅'C = fun u : ℂ => (-2 * Complex.I : ℂ) * ∫ t in (0 : ℝ)..1,
      ψI' (z₅' t) * Complex.exp ((π : ℂ) * (Complex.I : ℂ) * u * z₅' t) from
    funext fun u => by simp [J₅'C, ← intervalIntegral.integral_const_mul, mul_assoc,
      mul_left_comm, mul_comm]) ▸
    (differentiable_const (-2 * Complex.I : ℂ)).mul (integral_ψ_exp_differentiable (Cz := 1)
      continuousOn_ψI'_z₅' continuous_z₅' hMψ
      (fun t ht => by
        have htic := mem_Icc_of_Ioc (mem_Ioc_of_mem_uIoc ht)
        simpa [z₅'_eq_of_mem (t := t) htic, Complex.norm_real, abs_of_nonneg htic.1] using htic.2))

set_option maxHeartbeats 1000000 in
lemma J₆'C_differentiableOn : DifferentiableOn ℂ J₆'C rightHalfPlane := by
  intro u0 hu0
  have hu0re : 0 < u0.re := by simpa [rightHalfPlane] using hu0
  let μ : Measure ℝ := μIciOne
  have hψS'_eq : ∀ t : ℝ, t ∈ Set.Ici (1 : ℝ) → ψS' (z₆' t) = ψS.resToImagAxis t := fun t ht => by
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    simp [show z₆' t = (Complex.I : ℂ) * (t : ℂ) by simpa using (z₆'_eq_of_mem (t := t) ht),
      ψS', Function.resToImagAxis, ResToImagAxis, ht0, mul_comm]
  let base : ℝ → ℂ := fun t => (Complex.I : ℂ) * ψS.resToImagAxis t
  let k : ℝ → ℂ := fun t => (-(π : ℂ)) * (t : ℂ)
  let F : ℂ → ℝ → ℂ := fun u t => base t * Complex.exp (u * k t)
  let F' : ℂ → ℝ → ℂ := fun u t => base t * k t * Complex.exp (u * k t)
  have hcont_base : ContinuousOn base (Set.Ici (1 : ℝ)) := by
    simpa [base] using continuousOn_const.mul (Function.continuousOn_resToImagAxis_Ici_one_of
      (F := ψS) MagicFunction.b.PsiBounds.continuous_ψS)
  have hk_cont : ContinuousOn k (Set.Ici (1 : ℝ)) := by fun_prop
  have hExp : ∀ u : ℂ, ContinuousOn (fun t : ℝ => Complex.exp (u * k t)) (Set.Ici (1 : ℝ)) :=
    fun u => ContinuousOn.cexp (continuousOn_const.mul hk_cont)
  have hF_meas : ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (F u) μ := .of_forall fun u => by
    simpa [μ] using ((hcont_base.mul (hExp u)).aestronglyMeasurable (μ := volume) measurableSet_Ici)
  have hF'_meas : AEStronglyMeasurable (F' u0) μ := by simpa [F', μ, mul_assoc] using
    ((hcont_base.mul hk_cont).mul (hExp u0)).aestronglyMeasurable (μ := volume) measurableSet_Ici
  obtain ⟨Mψ, hMψ⟩ := MagicFunction.b.PsiBounds.exists_bound_norm_ψS_resToImagAxis_Ici_one
  have hbase_bound : ∀ t : ℝ, 1 ≤ t → ‖base t‖ ≤ Mψ := fun t ht => by
    simpa [base, norm_mul] using mul_le_mul_of_nonneg_left (hMψ t ht) (norm_nonneg (Complex.I : ℂ))
  have hF_int : Integrable (F u0) μ := by
    let b : ℝ := Real.pi * u0.re
    have hb : 0 < b := by positivity
    refine Integrable.mono' (by
      simpa [μ, MeasureTheory.IntegrableOn, pow_zero, one_mul] using
        ((SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 0) (b := b)
          hb) : IntegrableOn _ _ (volume : Measure ℝ)).const_mul Mψ :
      Integrable (fun t : ℝ => Mψ * Real.exp (-b * t)) μ) hF_meas.self_of_nhds
      ((ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht => ?_)
    have hexp : ‖Complex.exp (u0 * k t)‖ = Real.exp (-b * t) := by
      simp [Complex.norm_exp, mul_re, show (k t).re = -Real.pi * t by simp [k],
        show (k t).im = 0 by simp [k], b, mul_left_comm, mul_comm]
    rw [show ‖F u0 t‖ = ‖base t‖ * ‖Complex.exp (u0 * k t)‖ by simp [F], hexp]
    exact mul_le_mul_of_nonneg_right (hbase_bound t ht) (Real.exp_pos _).le
  let ε : ℝ := u0.re / 2
  have ε_pos : 0 < ε := div_pos hu0re (by norm_num)
  let b : ℝ := Real.pi * ε
  have hb : 0 < b := by positivity
  let bound : ℝ → ℝ := fun t => (Mψ * Real.pi) * t * Real.exp (-b * t)
  have bound_int : Integrable bound μ := by
    simpa [μ, MeasureTheory.IntegrableOn, bound, mul_assoc, mul_left_comm, mul_comm] using
      (by simpa [pow_one] using
          (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 1) (b := b) hb) :
        IntegrableOn (fun t : ℝ => t * Real.exp (-b * t)) (Set.Ici (1 : ℝ))
          (volume : Measure ℝ)).const_mul (Mψ * Real.pi)
  have hre_lower : ∀ u : ℂ, u ∈ Metric.ball u0 ε → (u0.re / 2) ≤ u.re := fun u hu => by
    have hu' : ‖u - u0‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hu
    have hre : |u.re - u0.re| ≤ ‖u - u0‖ := by simpa using abs_re_le_norm (u - u0)
    grind only [= abs.eq_1, = max_def]
  have h_bound : ∀ᵐ t ∂μ, ∀ u ∈ Metric.ball u0 ε, ‖F' u t‖ ≤ bound t :=
    (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht u hu => by
      have ht0 : 0 ≤ t := le_trans (by norm_num) ht
      have hexp_le : ‖Complex.exp (u * k t)‖ ≤ Real.exp (-b * t) := by
        simpa [Complex.norm_exp, mul_re, show (k t).re = -Real.pi * t by simp [k],
          show (k t).im = 0 by simp [k], b, ε, mul_assoc, mul_left_comm, mul_comm] using
          Real.exp_le_exp.2 (show -Real.pi * u.re * t ≤ -Real.pi * (u0.re / 2) * t by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonpos_left (hre_lower u hu)
                (by nlinarith [mul_nonneg Real.pi_pos.le ht0] : (-Real.pi * t) ≤ 0))
      have hk_norm : ‖k t‖ = Real.pi * t := by
        simp [k, Complex.norm_real, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg ht0, mul_comm]
      calc ‖F' u t‖
          = ‖base t‖ * (‖k t‖ * ‖Complex.exp (u * k t)‖) := by simp [F', mul_assoc]
        _ ≤ Mψ * ((Real.pi * t) * Real.exp (-b * t)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (mul_le_mul_of_nonneg_left (mul_le_mul (le_of_eq hk_norm) hexp_le (norm_nonneg _)
                (mul_nonneg Real.pi_pos.le ht0)) (norm_nonneg (base t))).trans
                (mul_le_mul_of_nonneg_right (hbase_bound t ht) (by positivity))
        _ = bound t := by simp [bound, mul_assoc, mul_left_comm, mul_comm]
  have h_diff : ∀ᵐ t ∂μ, ∀ u ∈ Metric.ball u0 ε,
      HasDerivAt (fun u : ℂ => F u t) (F' u t) u :=
    .of_forall fun t u _ => by simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using
      (HasDerivAt.comp u (Complex.hasDerivAt_exp (u * k t))
        (hasDerivAt_mul_const (k t) (x := u))).const_mul (base t)
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := F) (x₀ := u0) (s := Metric.ball u0 ε) (hs := Metric.ball_mem_nhds u0 ε_pos)
      (bound := bound) (hF_meas := hF_meas) (hF_int := hF_int) (hF'_meas := hF'_meas)
      (h_bound := h_bound) (bound_integrable := bound_int) (h_diff := h_diff)
  have hEq : (fun u : ℂ => (-2 : ℂ) * ∫ t, F u t ∂μ) = J₆'C := by
    funext u
    simp only [J₆'C, μ]
    have hμ : (∫ t, F u t ∂μIciOne) = ∫ t in Set.Ici (1 : ℝ), F u t := by simp [μIciOne]
    rw [hμ]
    refine congrArg ((-2 : ℂ) * ·) (MeasureTheory.integral_congr_ae <|
      (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht => ?_)
    have hz : z₆' t = (Complex.I : ℂ) * (t : ℂ) := by simpa using (z₆'_eq_of_mem (t := t) ht)
    have hψ' : ψS' ((Complex.I : ℂ) * (t : ℂ)) = ψS.resToImagAxis t := by
      simpa [hz] using hψS'_eq t ht
    have hIexp' : u * ((Complex.I : ℂ) * (Complex.I * ((t : ℂ) * (π : ℂ)))) =
          -(u * ((t : ℂ) * (π : ℂ))) := by ring_nf; simp [Complex.I_sq]
    simp [F, base, k, hz, hψ', hIexp', mul_left_comm, mul_comm]
  exact (hEq ▸ (h.2.differentiableAt.const_mul (-2 : ℂ)) : DifferentiableAt ℂ J₆'C u0)
    |>.differentiableWithinAt

/-- `bPrimeC` is analytic on the right half-plane. -/
public lemma bPrimeC_analyticOnNhd : AnalyticOnNhd ℂ bPrimeC rightHalfPlane := by
  simpa [bPrimeC] using
    ((((J₁'C_differentiable.add J₂'C_differentiable).add J₃'C_differentiable).add
      J₄'C_differentiable).add J₅'C_differentiable).differentiableOn.add
      J₆'C_differentiableOn |>.analyticOnNhd rightHalfPlane_isOpen

end BPrimeExtension

/-! ## "Another integral" representation for `b'` -/

noncomputable section

open MagicFunction.FourierEigenfunctions

/-- Complex-parameter integrand for the "another integral" representation of `b'`. -/
@[expose] public def bAnotherIntegrandC (u : ℂ) (t : ℝ) : ℂ :=
  bAnotherBase t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

/-- Complex-parameter "another integral" associated to `b'`. -/
@[expose] public def bAnotherIntegralC (u : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrandC u t

/-- Restriction of `bAnotherIntegralC` to real parameters. -/
public lemma bAnotherIntegralC_ofReal (u : ℝ) :
    bAnotherIntegralC (u : ℂ) =
      ∫ t in Set.Ioi (0 : ℝ), bAnotherBase t * (Real.exp (-π * u * t) : ℂ) :=
  MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun t _ ↦ by simp [bAnotherIntegrandC, mul_assoc])

def bAnotherRHS (u : ℂ) : ℂ :=
  (-4 * (Complex.I : ℂ)) *
    (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) *
      ((144 : ℂ) / ((π : ℂ) * u) + (1 : ℂ) / ((π : ℂ) * (u - 2)) + bAnotherIntegralC u)

lemma bAnotherRHS_analyticOnNhd :
    AnalyticOnNhd ℂ bAnotherRHS ACDomain := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hterm1 :
      AnalyticOnNhd ℂ (fun u : ℂ => (144 : ℂ) / ((π : ℂ) * u)) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul analyticOnNhd_id) fun u hu =>
      mul_ne_zero hπ fun h0 =>
        (ne_of_gt (by simpa [rightHalfPlane] using hu.1)) (by simp [h0])
  have hterm2 :
      AnalyticOnNhd ℂ (fun u : ℂ => (1 : ℂ) / ((π : ℂ) * (u - 2))) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const))
      fun u hu => mul_ne_zero hπ (sub_ne_zero.2 (by simpa [Set.mem_singleton_iff] using hu.2))
  unfold bAnotherRHS
  exact analyticOnNhd_sinSq_prefactor_mul (sign := (-4 * (Complex.I : ℂ))) <| by
    simpa [add_assoc] using
      (hterm1.add hterm2).add ((show AnalyticOnNhd ℂ bAnotherIntegralC rightHalfPlane by
        convert analyticOnNhd_integral_base_exp (base := bAnotherBase) continuousOn_bAnotherBase
          (fun u hu ↦ bAnotherBase_integrable_exp (u := u) hu) using 1).mono fun u hu => hu.1)

/--
Analytic-continuation step: extend the "another integral" identity for `b'` from `u > 2` to all
real `0 < u` with `u ≠ 2`.
-/
public theorem bRadial_eq_another_integral_analytic_continuation_of_gt2
    (h_gt2 :
      ∀ r : ℝ, 2 < r →
        b' r =
          (-4 * (Complex.I : ℂ)) *
            (Real.sin (π * r / 2)) ^ (2 : ℕ) *
              ((144 : ℂ) / (π * r) + (1 : ℂ) / (π * (r - 2)) +
                ∫ t in Set.Ioi (0 : ℝ),
                  bAnotherBase t * (Real.exp (-π * r * t) : ℂ)))
    {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    b' u =
      (-4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) +
            ∫ t in Set.Ioi (0 : ℝ),
              bAnotherBase t * (Real.exp (-π * u * t) : ℂ)) :=
  analytic_continuation_of_gt2
    ⟨bPrimeC, bPrimeC_analyticOnNhd.mono (fun u hu => hu.1), fun u hu _ => by
      simpa [show MagicFunction.b.RealIntegrals.b' u = b' u by
        simpa using (MagicFunction.g.CohnElkies.b'_eq_realIntegrals_b' (u := u) hu.le).symm]
        using bPrimeC_ofReal u⟩
    bAnotherRHS_analyticOnNhd
    (fun u => by
      simp [bAnotherRHS, bAnotherIntegralC_ofReal, sub_eq_add_neg, add_assoc, add_comm,
        add_left_comm, mul_assoc])
    h_gt2 hu hu2

/-- The integrand used in the "another integral" representation of `b'`. -/
@[expose] public def bAnotherIntegrand (u t : ℝ) : ℂ :=
  bAnotherBase t * (Real.exp (-π * u * t) : ℂ)

lemma bRadial_eq_another_integral_of_gt2 {u : ℝ} (hu : 2 < u) : b' u =
    (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
      ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) +
        ∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrand u t) := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hpoint (t : ℝ) : bLaplaceIntegrand u t = bAnotherIntegrand u t +
      ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t) := by
    simp [bLaplaceIntegrand, bAnotherIntegrand, bAnotherBase, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm, mul_left_comm, mul_comm, mul_add]
  have hExpInt : IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_neg_pi_mul_Ioi_complex (u := u) hu0
  have h2ExpInt : IntegrableOn (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ))
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu
  have hCorrInt : IntegrableOn
      (fun t : ℝ => ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t))
      (Set.Ioi (0 : ℝ)) :=
    ((hExpInt.const_mul (144 : ℂ)).add h2ExpInt).congr <|
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => by
        simp [-Complex.ofReal_exp, add_mul, mul_assoc]
  have hAnotherInt : IntegrableOn (fun t : ℝ => bAnotherIntegrand u t) (Set.Ioi (0 : ℝ)) := by
    simpa [show (fun t : ℝ => bAnotherIntegrand u t) =
        fun t : ℝ => bLaplaceIntegrand u t -
          ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t) from
      funext fun t => by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (eq_sub_of_add_eq (hpoint t).symm)] using
      (bLaplaceIntegral_convergent (u := u) hu).sub hCorrInt
  have hLapInt_decomp : (∫ t in Set.Ioi (0 : ℝ), bLaplaceIntegrand u t) =
      (∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrand u t) + (∫ t in Set.Ioi (0 : ℝ),
        ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t)) := by
    rw [show (∫ t in Set.Ioi (0 : ℝ), bLaplaceIntegrand u t) =
          ∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrand u t +
            ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t) from
      MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi (fun t _ => by simp [hpoint t])]
    exact integral_add hAnotherInt hCorrInt
  have hCorr_eval : (∫ t in Set.Ioi (0 : ℝ),
      ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t)) =
      (144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) := by
    rw [show (fun t : ℝ => ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t)) =
          fun t => (144 : ℂ) * (Real.exp (-π * u * t) : ℂ) +
            (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) from
        funext fun t => by simp [-Complex.ofReal_exp, add_mul, mul_assoc],
      MeasureTheory.integral_add (hExpInt.const_mul (144 : ℂ)) h2ExpInt,
      MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))
        (144 : ℂ) (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)),
      integral_exp_neg_pi_mul_Ioi_complex (u := u) hu0,
      integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu]
    push_cast; ring
  rw [show b' u = (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
        (∫ t in Set.Ioi (0 : ℝ), bLaplaceIntegrand u t) from by
      simpa [bLaplaceIntegrand] using bRadial_eq_laplace_psiI_main (u := u) hu,
    hLapInt_decomp, hCorr_eval]
  ring_nf

/-- Main lemma for blueprint proposition `prop:b-another-integral`. -/
public theorem bRadial_eq_another_integral_main {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    b' u = (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
      ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + ∫ t in Set.Ioi (0 : ℝ),
        (ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) - ((Real.exp (2 * π * t)) : ℂ)) *
          Real.exp (-π * u * t)) := by
  simpa [bAnotherIntegrand] using bRadial_eq_another_integral_analytic_continuation_of_gt2
    (h_gt2 := fun r hr => by
      simpa [bAnotherIntegrand] using bRadial_eq_another_integral_of_gt2 (u := r) hr)
    (u := u) hu hu2

end

end MagicFunction.g.CohnElkies.IntegralReps

namespace MagicFunction.g.CohnElkies.IntegralReps

section AnotherIntegralA

open MeasureTheory Real Complex
open SpherePacking.Integration (μIoi0)
open MagicFunction.FourierEigenfunctions

lemma corrIntegral_eval {u : ℝ} (hu0 : 0 < u) (hu : 2 < u)
    {c36 c8640 c18144 : ℂ}
    (hc36 : c36 = ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ))
    (hc8640 : c8640 = ((8640 / π : ℝ) : ℂ))
    (hc18144 : c18144 = ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))
    {corr : ℝ → ℂ}
    (hcorr : corr =
      fun t : ℝ => (c36 * Real.exp (2 * π * t) - c8640 * t + c18144) * Real.exp (-π * u * t))
    (hIexp :
        (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) = ((1 / (π * u) : ℝ) : ℂ))
    (hItexp : (∫ t in Set.Ioi (0 : ℝ), (t * Real.exp (-π * u * t) : ℂ)) =
        ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ))
    (hI2exp : (∫ t in Set.Ioi (0 : ℝ), (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) =
        ((1 / (π * (u - 2)) : ℝ) : ℂ))
    (hExpInt : IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)))
    (hTExpInt : IntegrableOn (fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)))
    (h2ExpInt : IntegrableOn
        (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ))) :
    (∫ t in Set.Ioi (0 : ℝ), corr t) =
      (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
        (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * u) := by
  rw [hcorr]
  let f0 : ℝ → ℂ := fun t : ℝ => (Real.exp (-π * u * t) : ℂ)
  let f1 : ℝ → ℂ := fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)
  let f2 : ℝ → ℂ := fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)
  rw [show (∫ t in Set.Ioi (0 : ℝ),
      (c36 * Real.exp (2 * π * t) - c8640 * t + c18144) * Real.exp (-π * u * t)) =
      ∫ t in Set.Ioi (0 : ℝ), ((c36 * f2 t + (-c8640) * f1 t) + c18144 * f0 t) from
    congrArg (integral (volume.restrict (Set.Ioi 0))) <| by funext t; dsimp [f0, f1, f2]; ring]
  change (∫ t, ((c36 * f2 t + (-c8640) * f1 t) + c18144 * f0 t) ∂ μIoi0) =
    (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
      (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) + (18144 : ℂ) / (π ^ (3 : ℕ) * u)
  have hI (f : ℝ → ℂ) (hf : IntegrableOn f (Set.Ioi (0 : ℝ))) : Integrable f μIoi0 := by
    simpa [MeasureTheory.IntegrableOn, μIoi0] using hf
  rw [integral_add_add (μ := μIoi0) ((hI f2 h2ExpInt).const_mul c36)
      ((hI f1 hTExpInt).const_mul (-c8640)) ((hI f0 hExpInt).const_mul c18144),
    integral_const_mul (μ := μIoi0) c36 f2, integral_const_mul (μ := μIoi0) (-c8640) f1,
    integral_const_mul (μ := μIoi0) c18144 f0,
    show (∫ t, f2 t ∂μIoi0) = ((1 / (π * (u - 2)) : ℝ) : ℂ) by simpa [f2, μIoi0] using hI2exp,
    show (∫ t, f1 t ∂μIoi0) = ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) by simpa [f1, μIoi0] using hItexp,
    show (∫ t, f0 t ∂μIoi0) = ((1 / (π * u) : ℝ) : ℂ) by simpa [f0, μIoi0] using hIexp,
    hc36, hc8640, hc18144]
  have hu2ne : (u - 2 : ℝ) ≠ 0 := (sub_pos.mpr hu).ne'
  have hune : (u : ℝ) ≠ 0 := hu0.ne'
  push_cast [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp
  ring

lemma aRadial_eq_another_integral_of_gt2 {u : ℝ} (hu : 2 < u) :
    a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
            (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / (π ^ (3 : ℕ) * u) +
              aAnotherIntegral u) := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hLap' : a' u = (4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
      (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) := by
    simpa [aLaplaceIntegrand, mul_assoc] using aRadial_eq_laplace_phi0_main hu
  set c36 : ℂ := ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) with hc36
  set c8640 : ℂ := ((8640 / π : ℝ) : ℂ) with hc8640
  set c18144 : ℂ := ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ) with hc18144
  let corr : ℝ → ℂ :=
    fun t : ℝ => (c36 * Real.exp (2 * π * t) - c8640 * t + c18144) * Real.exp (-π * u * t)
  have hIexp : (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) = ((1 / (π * u) : ℝ) : ℂ) :=
    integral_exp_neg_pi_mul_Ioi_complex hu0
  have hItexp : (∫ t in Set.Ioi (0 : ℝ), (t * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := integral_mul_exp_neg_pi_mul_Ioi_complex hu0
  have hI2exp : (∫ t in Set.Ioi (0 : ℝ), (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * (u - 2)) : ℝ) : ℂ) := integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex hu
  have hExpInt : IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_neg_pi_mul_Ioi_complex hu0
  have hTExpInt : IntegrableOn (fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_mul_exp_neg_pi_mul_Ioi_complex hu0
  have h2ExpInt : IntegrableOn
      (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex hu
  have hCorrInt : IntegrableOn corr (Set.Ioi (0 : ℝ)) := by
    refine ((((h2ExpInt.const_mul c36).sub (hTExpInt.const_mul c8640)).add
      (hExpInt.const_mul c18144)).congr <|
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t _ ↦ ?_)
    dsimp [corr]; ring
  have hLapInt_decomp : (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) =
      (∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) + (∫ t in Set.Ioi (0 : ℝ), corr t) := by
    rw [show (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) =
        ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t + corr t from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ by
        simp [-Complex.ofReal_exp, aLaplaceIntegrand, aAnotherIntegrand, c36, c8640, c18144,
          sub_eq_add_neg, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm, corr]
        ring]
    exact integral_add (by simpa [MeasureTheory.IntegrableOn] using
      aAnotherIntegrand_integrable_of_pos hu0)
      (by simpa [MeasureTheory.IntegrableOn] using hCorrInt)
  simpa [aAnotherIntegral, hLapInt_decomp, show (∫ t in Set.Ioi (0 : ℝ), corr t) =
      (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
        (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) + (18144 : ℂ) / (π ^ (3 : ℕ) * u) from
    corrIntegral_eval hu0 hu hc36 hc8640 hc18144 rfl hIexp hItexp hI2exp hExpInt hTExpInt h2ExpInt,
    add_assoc, add_left_comm, add_comm] using hLap'

/-- Main lemma for blueprint proposition `prop:a-another-integral`. -/
public theorem aRadial_eq_another_integral_main {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
            (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / (π ^ (3 : ℕ) * u) +
              ∫ t in Set.Ioi (0 : ℝ),
                ((((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                        ((8640 / π : ℝ) : ℂ) * t -
                        ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) *
                    Real.exp (-π * u * t))) := by
  simpa [aAnotherIntegrand] using
    aRadial_eq_another_integral_analytic_continuation_of_gt2 (u := u) (hu := hu) (hu2 := hu2)
      fun r hr => by simpa [aAnotherIntegral] using aRadial_eq_another_integral_of_gt2 (u := r) hr

end AnotherIntegralA

end MagicFunction.g.CohnElkies.IntegralReps

namespace MagicFunction.g.CohnElkies

open scoped BigOperators FourierTransform SchwartzMap Topology UpperHalfPlane
open MeasureTheory Real Complex
open MagicFunction.FourierEigenfunctions MagicFunction.g.CohnElkies.IntegralReps

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

noncomputable local instance : FourierTransform (𝓢(ℝ⁸, ℂ)) (𝓢(ℝ⁸, ℂ)) :=
  ⟨FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)⟩

/-! ## Real-valuedness on the positive imaginary axis (merged from `ImagAxisReal`) -/

private lemma imagAxis_im_eq_zero (F : ℍ → ℂ) (t : ℝ) (ht : 0 < t) (hF : ResToImagAxis.Real F) :
    (F ⟨Complex.I * t, by simp [ht]⟩).im = 0 := by
  simpa [Function.resToImagAxis, ResToImagAxis, ht] using hF t ht

/-- The value `φ₀'' (it)` is real for `t > 0`. -/
public lemma φ₀''_imag_axis_im (t : ℝ) (ht : 0 < t) :
    (φ₀'' ((Complex.I : ℂ) * (t : ℂ))).im = 0 := by
  simpa [φ₀'', ht] using show (φ₀ ⟨Complex.I * t, by simp [ht]⟩).im = 0 by
    set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
    have hE2 : (E₂ z).im = 0 := by simpa [z] using imagAxis_im_eq_zero E₂ t ht E₂_imag_axis_real
    have hE4 : (E₄ z).im = 0 := by simpa [z] using imagAxis_im_eq_zero E₄ t ht E₄_imag_axis_real
    have hE6 : (E₆ z).im = 0 := by simpa [z] using imagAxis_im_eq_zero E₆ t ht E₆_imag_axis_real
    have hΔ : (Δ z).im = 0 := by simpa [z] using imagAxis_im_eq_zero Δ t ht Delta_imag_axis_pos.1
    simp [-E4_apply, -E6_apply, φ₀, z, Complex.div_im, hΔ,
      Complex.im_pow_eq_zero_of_im_eq_zero (show ((E₂ z) * (E₄ z) - (E₆ z)).im = 0 by
        simp [-E4_apply, -E6_apply, Complex.sub_im, Complex.mul_im, hE2, hE4, hE6]) 2]

/-- The value `φ₀'' (i / t)` is real for `t > 0`. -/
public lemma φ₀''_imag_axis_div_im (t : ℝ) (ht : 0 < t) :
    (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).im = 0 := by
  simpa [div_eq_mul_inv] using (φ₀''_imag_axis_im (t := (1 / t)) (by positivity))

/-- The value `ψI' (it)` is real for `t > 0`. -/
public lemma ψI'_imag_axis_im (t : ℝ) (ht : 0 < t) :
    (ψI' ((Complex.I : ℂ) * (t : ℂ))).im = 0 := by
  set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hH2 : (H₂_MF z).im = 0 := by simpa [z] using imagAxis_im_eq_zero H₂ t ht H₂_imag_axis_real
  have hH3 : (H₃_MF z).im = 0 := by
    simpa [z] using imagAxis_im_eq_zero H₃ t ht (by
      simpa [jacobi_identity] using H₂_imag_axis_real.add H₄_imag_axis_real)
  have hH4 : (H₄_MF z).im = 0 := by simpa [z] using imagAxis_im_eq_zero H₄ t ht H₄_imag_axis_real
  simpa [ψI', Function.resToImagAxis, ResToImagAxis, ht, z] using show (ψI z).im = 0 by
    rw [ψI_eq]
    simp [z, Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.div_im, hH2, hH3, hH4,
      Complex.im_pow_eq_zero_of_im_eq_zero hH2 2, Complex.im_pow_eq_zero_of_im_eq_zero hH3 2]

/-! ## Integral representation for `𝓕 g` (merged from `IntegralB`) -/

namespace IntegralB

lemma B_mul_exp_eq_decomp {u t : ℝ} (ht : 0 < t) : (B t : ℂ) * Real.exp (-π * u * t) =
    -(aAnotherIntegrand u t) + ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * bAnotherIntegrand u t +
      ((8640 / π : ℝ) : ℂ) * ((t : ℂ) * (Real.exp (-π * u * t) : ℂ)) -
        ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (Real.exp (-π * u * t) : ℂ) := by
  have hB : (B t : ℂ) = (-(t ^ (2 : ℕ)) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) +
      ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * ψI' ((Complex.I : ℂ) * (t : ℂ)) := by
    apply Complex.ext <;> simp [B, φ₀''_imag_axis_div_im (t := t) ht, ψI'_imag_axis_im (t := t) ht]
  simp [hB, aAnotherIntegrand, bAnotherIntegrand, mul_assoc, mul_left_comm, mul_comm]; ring_nf

private lemma integrable_bAnother {u : ℝ} (hu : 0 < u) :
    Integrable (fun t : ℝ => bAnotherIntegrand u t)
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
  simpa [MeasureTheory.IntegrableOn, bAnotherIntegrand, bAnotherBase, mul_assoc] using
    bAnotherBase_integrable_exp hu

lemma integrableOn_B_mul_exp_neg_pi_mul {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (B t : ℂ) * Real.exp (-π * u * t)) (Set.Ioi (0 : ℝ)) :=
  ((((aAnotherIntegrand_integrable_of_pos hu).neg.add ((integrable_bAnother hu).const_mul _)).add
    ((integrableOn_mul_exp_neg_pi_mul_Ioi_complex hu).const_mul _)).sub
    ((integrableOn_exp_neg_pi_mul_Ioi_complex hu).const_mul _)).congr <|
  MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (IntegralB.B_mul_exp_eq_decomp (t := t) ht).symm

lemma integral_B_mul_exp_decomp {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) =
      -(∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) +
        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrand u t) +
        ((8640 / π : ℝ) : ℂ) * (∫ t in Set.Ioi (0 : ℝ), (t : ℂ) * (Real.exp (-π * u * t) : ℂ)) -
        ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
          (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
  let f1 : ℝ → ℂ := fun t => -(aAnotherIntegrand u t)
  let f2 : ℝ → ℂ := fun t => ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * bAnotherIntegrand u t
  let f3 : ℝ → ℂ := fun t => ((8640 / π : ℝ) : ℂ) * ((t : ℂ) * (Real.exp (-π * u * t) : ℂ))
  let f4 : ℝ → ℂ := fun t => -((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (Real.exp (-π * u * t) : ℂ)
  have hf1 : Integrable f1 μ := (aAnotherIntegrand_integrable_of_pos hu).neg
  have hf2 : Integrable f2 μ := (integrable_bAnother hu).const_mul _
  have hf3 : Integrable f3 μ := (integrableOn_mul_exp_neg_pi_mul_Ioi_complex hu).const_mul _
  have hf4 : Integrable f4 μ := by simpa [f4, mul_assoc] using
    (integrableOn_exp_neg_pi_mul_Ioi_complex hu).const_mul (-((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ))
  have hf23 : Integrable (fun t => f2 t + f3 t) μ := hf2.add hf3
  have hf234 : Integrable (fun t => (f2 t + f3 t) + f4 t) μ := hf23.add hf4
  rw [show (∫ t : ℝ, (B t : ℂ) * Real.exp (-π * u * t) ∂μ) =
        ∫ t : ℝ, (f1 t + ((f2 t + f3 t) + f4 t)) ∂μ from
      MeasureTheory.integral_congr_ae <|
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
          simpa [f1, f2, f3, f4, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
            mul_assoc] using IntegralB.B_mul_exp_eq_decomp (t := t) ht,
    MeasureTheory.integral_add hf1 hf234, MeasureTheory.integral_add hf23 hf4,
    MeasureTheory.integral_add hf2 hf3]
  simp [f1, f2, f3, f4, MeasureTheory.integral_neg, MeasureTheory.integral_const_mul, μ,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc]

end IntegralB

theorem fourier_g_eq_integral_B_of_ne_two {x : ℝ⁸} (hx : 0 < ‖x‖ ^ 2) (hx2 : ‖x‖ ^ 2 ≠ 2) :
    ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) = (π / 2160 : ℂ) * (Real.sin (π * (‖x‖ ^ 2) / 2)) ^ (2 : ℕ) *
      (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (‖x‖ ^ 2) * t)) := by
  set u : ℝ := ‖x‖ ^ 2
  have hFourier : ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
      ((↑π * I) / 8640 : ℂ) * a' u + (I / (240 * (↑π)) : ℂ) * b' u := by
    change (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) g) x = _
    simp [u, show FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) g =
        ((↑π * I) / 8640) • a + (I / (240 * (↑π))) • b from by
      simp [g, map_sub, map_smul, MagicFunction.a.Fourier.eig_a, MagicFunction.b.Fourier.eig_b,
        -FourierTransform.fourierCLE_apply], SchwartzMap.add_apply, SchwartzMap.smul_apply,
      smul_eq_mul, MagicFunction.FourierEigenfunctions.a, MagicFunction.FourierEigenfunctions.b,
      schwartzMap_multidimensional_of_schwartzMap_real, SchwartzMap.compCLM_apply]
  set IA : ℂ := ∫ t in Set.Ioi (0 : ℝ),
    ((((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
        ((8640 / π : ℝ) : ℂ) * t - ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) * Real.exp (-π * u * t))
  set IB : ℂ := ∫ t in Set.Ioi (0 : ℝ),
    (ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) - ((Real.exp (2 * π * t)) : ℂ)) *
      Real.exp (-π * u * t)
  have hAterm : ((↑π * I) / 8640 : ℂ) * a' u =
      (Real.sin (π * u / 2)) ^ (2 : ℕ) * (-(π / 2160 : ℂ)) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) - (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) := by
    rw [show a' u = (4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) - (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) from by
      simpa [IA] using aRadial_eq_another_integral_main hx hx2]
    linear_combination ((Real.sin (π * u / 2)) ^ (2 : ℕ) *
      ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) - (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
        (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA)) * (by field_simp; rw [Complex.I_sq]; ring :
        (((↑π * I) / 8640 : ℂ) * (4 * (Complex.I : ℂ))) = -(π / 2160 : ℂ))
  have hBterm : (I / (240 * (↑π)) : ℂ) * b' u =
      (Real.sin (π * u / 2)) ^ (2 : ℕ) * (1 / (60 * π) : ℂ) *
        ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) := by
    rw [show b' u = (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
        ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) from by
      simpa [IB] using bRadial_eq_another_integral_main hx hx2]
    linear_combination ((Real.sin (π * u / 2)) ^ (2 : ℕ) *
      ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB)) *
      (by field_simp; rw [Complex.I_sq]; ring :
        (((I / (240 * (↑π)) : ℂ)) * (-4 * (Complex.I : ℂ))) = (1 / (60 * π) : ℂ))
  have hBracket : (-(π / 2160 : ℂ)) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) - (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) +
      (1 / (60 * π) : ℂ) * ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) =
      (π / 2160 : ℂ) * (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) := by
    rw [show (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) =
        -IA + ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * IB +
          ((8640 / π : ℝ) : ℂ) * (∫ t in Set.Ioi (0 : ℝ), (t : ℂ) * (Real.exp (-π * u * t) : ℂ)) -
          ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
            (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) from by
        simpa [IA, IB, aAnotherIntegrand, bAnotherIntegrand]
          using IntegralB.integral_B_mul_exp_decomp hx,
      integral_mul_exp_neg_pi_mul_Ioi_complex hx, integral_exp_neg_pi_mul_Ioi_complex hx]
    push_cast; field_simp; ring
  simpa [u, mul_assoc] using show ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
      (π / 2160 : ℂ) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
        (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) by
    rw [hFourier, hAterm, hBterm]; grind only

/-- Integral representation of `𝓕 g` in terms of `B(t)` (for `0 < ‖x‖ ^ 2`). -/
public theorem fourier_g_eq_integral_B {x : ℝ⁸} (hx : 0 < ‖x‖ ^ 2) :
    ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) = (π / 2160 : ℂ) * (Real.sin (π * (‖x‖ ^ 2) / 2)) ^ (2 : ℕ) *
      (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (‖x‖ ^ 2) * t)) := by
  by_cases hx2 : ‖x‖ ^ 2 = 2
  · let c : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
    let xseq : ℕ → ℝ⁸ := fun n => (c n) • x
    have hxseq : Filter.Tendsto xseq Filter.atTop (𝓝 x) := by
      simpa [xseq] using (show Filter.Tendsto c Filter.atTop (𝓝 (1 : ℝ)) by
        simpa [c] using tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).smul_const x
    let useq : ℕ → ℝ := fun n => ‖xseq n‖ ^ 2
    have huseq_gt2 (n : ℕ) : 2 < useq n := by
      rw [show useq n = (c n) ^ (2 : ℕ) * (‖x‖ ^ 2) by
        simp [useq, xseq, norm_smul, abs_of_pos (by positivity : (0 : ℝ) < c n), pow_two,
          mul_assoc, mul_left_comm, mul_comm], hx2]
      nlinarith [sq_nonneg (c n - 1), (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))]
    let M : ℝ := ∫ t in Set.Ioi (0 : ℝ), ‖(B t : ℂ) * Real.exp (-π * (2 : ℝ) * t)‖
    have hInt_bound (n : ℕ) :
        ‖∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (useq n) * t)‖ ≤ M :=
      norm_integral_le_of_norm_le
        (by simpa using (IntegralB.integrableOn_B_mul_exp_neg_pi_mul (u := 2) (by positivity)).norm)
        <| MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
          rw [norm_mul, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
            Complex.norm_of_nonneg (Real.exp_pos _).le]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
          nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right (le_of_lt (huseq_gt2 n)) ht.le]
    have hRHSseq0 : Filter.Tendsto (fun n : ℕ => (π / 2160 : ℂ) *
        (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (useq n) * t)))
        Filter.atTop (𝓝 (0 : ℂ)) := by
      refine (tendsto_zero_iff_norm_tendsto_zero).2 <|
        squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
          ((tendsto_const_nhds.mul (show Filter.Tendsto (fun n : ℕ =>
              (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ)) Filter.atTop (𝓝 (0 : ℝ)) by
            simpa using (show ContinuousAt (fun u : ℝ => (Real.sin (π * u / 2)) ^ (2 : ℕ)) (2 : ℝ)
              by fun_prop).tendsto.comp (show Filter.Tendsto useq Filter.atTop (𝓝 (2 : ℝ)) by
                simpa [useq, hx2] using
                  ((by continuity : Continuous (fun y : ℝ⁸ => ‖y‖ ^ 2)).tendsto x).comp
                    hxseq))).trans (by simp) :
            Filter.Tendsto (fun n : ℕ => (‖(π / 2160 : ℂ)‖ * M) *
              (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ)) Filter.atTop (𝓝 (0 : ℝ)))
      rw [norm_mul, norm_mul,
        show ‖((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ)‖ =
            (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) by
          simpa [pow_two] using Complex.norm_of_nonneg (sq_nonneg (Real.sin (π * (useq n) / 2))),
        mul_right_comm]
      gcongr; exact hInt_bound n
    rw [tendsto_nhds_unique (((SchwartzMap.continuous (𝓕 g : 𝓢(ℝ⁸, ℂ))).tendsto x).comp hxseq)
      ((Filter.tendsto_congr fun n => fourier_g_eq_integral_B_of_ne_two (x := xseq n)
        ((by norm_num : (0:ℝ) < 2).trans (huseq_gt2 n)) (huseq_gt2 n).ne').mpr hRHSseq0)]
    simp [hx2]
  · exact fourier_g_eq_integral_B_of_ne_two (x := x) hx hx2

/-! ## Cohn-Elkies sign conditions -/

noncomputable section

private lemma complex_eq_ofReal_of_im_eq_zero (z : ℂ) (hz : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext rfl (by simp [hz])

/-- The constant `c = 18 / π^2` appearing in the definitions of `A` and `B`. -/
public abbrev c : ℝ := 18 * (π ^ (-2 : ℤ))

/-- Real part of `φ₀'' (I / t)` in terms of `FReal` and the imaginary-axis restriction of `Δ`. -/
public lemma phi0''_re_I_div (t : ℝ) (ht : 0 < t) :
    (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re =
      (FReal (1 / t)) / (Δ.resToImagAxis (1 / t)).re := by
  set s : ℝ := 1 / t
  have hs : 0 < s := one_div_pos.2 ht
  let z : ℍ := ⟨Complex.I * s, by simp [hs]⟩
  have hz : (z : ℂ) = (Complex.I : ℂ) / (t : ℂ) := by simp [z, s, div_eq_mul_inv]
  calc (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re
      = (φ₀ z).re := by simpa [hz] using congrArg Complex.re (φ₀''_coe_upperHalfPlane z)
    _ = ((F z) / (Δ z)).re := by simp [φ₀, F]
    _ = ((FReal s : ℂ) / (Δ.resToImagAxis s)).re := by
        simp [show F z = (FReal s : ℂ) by
          simpa [Function.resToImagAxis, ResToImagAxis, hs, z] using F_eq_FReal (t := s) hs,
          show Δ z = Δ.resToImagAxis s by simp [Function.resToImagAxis, ResToImagAxis, hs, z]]
    _ = ((FReal s : ℂ) / ((Δ.resToImagAxis s).re : ℂ)).re := by
        rw [complex_eq_ofReal_of_im_eq_zero _ (Delta_imag_axis_pos.1 s hs)]; rfl
    _ = (FReal s) / (Δ.resToImagAxis s).re := by rw [← Complex.ofReal_div]; simp
    _ = (FReal (1 / t)) / (Δ.resToImagAxis (1 / t)).re := by simp [s]

/-- Real part of `ψS` on the imaginary axis, written using `GReal` and `Δ`. -/
public lemma ψS_resToImagAxis_re (s : ℝ) (hs : 0 < s) :
    (ψS.resToImagAxis s).re = -(2⁻¹ * GReal s) / (Δ.resToImagAxis s).re := by
  let z : ℍ := ⟨Complex.I * s, by simp [hs]⟩
  calc (ψS.resToImagAxis s).re
      = ((-(1 / 2 : ℂ)) * (G.resToImagAxis s) / (Δ.resToImagAxis s)).re := by
        simpa using congrArg Complex.re (show ψS.resToImagAxis s =
            (-(1 / 2 : ℂ)) * (G.resToImagAxis s) / (Δ.resToImagAxis s) by
          simpa [Function.resToImagAxis, ResToImagAxis, hs, z] using show
              ψS z = (-(1 / 2 : ℂ)) * (G z) / (Δ z) by
            rw [MagicFunction.b.PsiBounds.ψS_apply_eq_factor z]
            simp [G, show Δ z = (H₂ z * H₃ z * H₄ z) ^ 2 / (256 : ℂ) by
              simpa [Delta_apply, mul_assoc] using Delta_eq_H₂_H₃_H₄ z]
            field_simp [H₂_ne_zero z, H₃_ne_zero z, H₄_ne_zero z]; ring_nf)
    _ = ((-(1 / 2 : ℂ)) * (GReal s : ℂ) / (Δ.resToImagAxis s)).re := by
        simp [show ResToImagAxis G s = (GReal s : ℂ) by
          simpa [Function.resToImagAxis_apply, GReal] using G_eq_GReal (t := s) hs]
    _ = ((-(1 / 2 : ℂ)) * (GReal s : ℂ) / ((Δ.resToImagAxis s).re : ℂ)).re := by
        rw [complex_eq_ofReal_of_im_eq_zero _ (Delta_imag_axis_pos.1 s hs)]; rfl
    _ = (-(1 / 2 : ℝ)) * (GReal s) / (Δ.resToImagAxis s).re := by simp
    _ = -(2⁻¹ * GReal s) / (Δ.resToImagAxis s).re := by simp [div_eq_mul_inv, mul_assoc]

/-- Relate `ψI' (I * t)` to `ψS` at `1 / t` via the slash-action symmetry. -/
public lemma ψI'_re_mul_I (t : ℝ) (ht : 0 < t) :
    (ψI' ((Complex.I : ℂ) * (t : ℂ))).re =
      -(t ^ (2 : ℕ)) * (ψS.resToImagAxis (1 / t)).re := by
  set s : ℝ := 1 / t
  have hs : 0 < s := one_div_pos.2 ht
  have hψS' : ψS.resToImagAxis s = ((-(s ^ (2 : ℕ)) : ℝ) : ℂ) * ψI.resToImagAxis t := by
    simpa [show (1 / s) = t by simp [s], zpow_ofNat, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using
      ResToImagAxis.SlashActionS (F := ψI) (k := (-2 : ℤ)) (t := s) hs
  have hts : (t ^ (2 : ℕ)) * (s ^ (2 : ℕ)) = (1 : ℝ) := by
    simp [s, ht.ne', pow_two, div_eq_mul_inv, mul_assoc, mul_comm]
  have hψIaxis : ψI.resToImagAxis t = ((-(t ^ (2 : ℕ)) : ℝ) : ℂ) * ψS.resToImagAxis s :=
    calc ψI.resToImagAxis t
        = ((t ^ (2 : ℕ) * s ^ (2 : ℕ) : ℝ) : ℂ) * ψI.resToImagAxis t := by simp [hts]
      _ = ((-(t ^ (2 : ℕ)) : ℝ) : ℂ) * ψS.resToImagAxis s := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (congrArg (fun w : ℂ => ((-(t ^ (2 : ℕ)) : ℝ) : ℂ) * w) hψS').symm
  calc (ψI' ((Complex.I : ℂ) * (t : ℂ))).re
      = (ψI.resToImagAxis t).re := by simp [ψI', ResToImagAxis, ht]
    _ = (-(t ^ (2 : ℕ)) : ℝ) * (ψS.resToImagAxis s).re := by
      rw [hψIaxis]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    _ = -(t ^ (2 : ℕ)) * (ψS.resToImagAxis (1 / t)).re := by simp [s]

/-- Rewrite `A t` as a quotient involving `FReal`, `GReal`, and `Δ` on the imaginary axis. -/
public lemma A_eq_neg_mul_FG_div_Delta (t : ℝ) (ht : 0 < t) :
    A t = (-(t ^ (2 : ℕ))) *
      ((FReal (1 / t) + c * GReal (1 / t)) / (Δ.resToImagAxis (1 / t)).re) := by
  set s : ℝ := 1 / t
  have hs : 0 < s := one_div_pos.2 ht
  have hΔr : (Δ.resToImagAxis s).re ≠ 0 := ne_of_gt (Delta_imag_axis_pos.2 s hs)
  rw [show A t = (-(t ^ (2 : ℕ))) * (FReal s / (Δ.resToImagAxis s).re) -
        (36 / (π ^ (2 : ℕ)) : ℝ) * (-(t ^ (2 : ℕ)) * (ψS.resToImagAxis s).re) by
      simp [A, show (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re = FReal s / (Δ.resToImagAxis s).re by
        simpa [s] using phi0''_re_I_div (t := t) ht,
        show (ψI' ((Complex.I : ℂ) * (t : ℂ))).re = -(t ^ (2 : ℕ)) * (ResToImagAxis ψS s).re by
          simpa [s, Function.resToImagAxis_apply] using ψI'_re_mul_I (t := t) ht],
    ψS_resToImagAxis_re (s := s) hs]
  field_simp [hΔr]; ring

/-- Rewrite `B t` as a quotient involving `FReal`, `GReal`, and `Δ` on the imaginary axis. -/
public lemma B_eq_neg_mul_FG_div_Delta (t : ℝ) (ht : 0 < t) :
    B t = (-(t ^ (2 : ℕ))) *
      ((FReal (1 / t) - c * GReal (1 / t)) / (Δ.resToImagAxis (1 / t)).re) := by
  set s : ℝ := 1 / t
  have hs : 0 < s := one_div_pos.2 ht
  have hΔr : (Δ.resToImagAxis s).re ≠ 0 := ne_of_gt (Delta_imag_axis_pos.2 s hs)
  rw [show B t = (-(t ^ (2 : ℕ))) * (FReal s / (Δ.resToImagAxis s).re) +
        (36 / (π ^ (2 : ℕ)) : ℝ) * (-(t ^ (2 : ℕ)) * (ψS.resToImagAxis s).re) by
      simp [B, show (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re = FReal s / (Δ.resToImagAxis s).re by
        simpa [s] using phi0''_re_I_div (t := t) ht,
        show (ψI' ((Complex.I : ℂ) * (t : ℂ))).re = -(t ^ (2 : ℕ)) * (ResToImagAxis ψS s).re by
          simpa [s, Function.resToImagAxis_apply] using ψI'_re_mul_I (t := t) ht],
    ψS_resToImagAxis_re (s := s) hs]
  field_simp [hΔr]; ring

end

/-- Laplace-type integral formula for `gRadial` in terms of the kernel `A(t)` (for `u > 2`). -/
public theorem gRadial_eq_integral_A {u : ℝ} (hu : 2 < u) : gRadial u =
    (π / 2160 : ℂ) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
    (∫ t in Set.Ioi (0 : ℝ), (A t : ℂ) * Real.exp (-π * u * t)) := by
  set IA : ℂ := ∫ t in Set.Ioi (0 : ℝ),
    ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) * Real.exp (-π * u * t)
  set IB : ℂ := ∫ t in Set.Ioi (0 : ℝ),
    ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)
  have ha' : a' u = (4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IA := by
    simpa [IA, mul_assoc] using
      MagicFunction.g.CohnElkies.IntegralReps.aRadial_eq_laplace_phi0_main (u := u) hu
  have hb' : b' u = (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IB := by
    simpa [IB, mul_assoc] using
      MagicFunction.g.CohnElkies.IntegralReps.bRadial_eq_laplace_psiI_main (u := u) hu
  have hg : gRadial u =
      ((↑π * Complex.I) / 8640 : ℂ) * a' u - (Complex.I / (240 * (↑π)) : ℂ) * b' u := by
    simp [gRadial, sub_eq_add_neg, SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul]
  have hcoefA :
      ((↑π * Complex.I) / 8640 : ℂ) * (4 * (Complex.I : ℂ)) = -(π / 2160 : ℂ) := by
    ring_nf; simp; ring
  have hcoefB :
      (-(Complex.I / (240 * (↑π)) : ℂ)) * (-4 * (Complex.I : ℂ)) = -(1 / (60 * π) : ℂ) := by
    field_simp [show (π : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero]; ring_nf; simp
  have hA_integral : (∫ t in Set.Ioi (0 : ℝ), (A t : ℂ) * Real.exp (-π * u * t)) =
      -IA + (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * IB := by
    have hset : (∫ t in Set.Ioi (0 : ℝ), (A t : ℂ) * Real.exp (-π * u * t)) =
        ∫ t in Set.Ioi (0 : ℝ), (((-(t ^ (2 : ℕ)) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) +
          (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * ψI' ((Complex.I : ℂ) * (t : ℂ))) *
          Real.exp (-π * u * t)) :=
      MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi (fun t ht => by
          simp [show (A t : ℂ) = (-(t ^ (2 : ℕ)) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) +
              (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * ψI' ((Complex.I : ℂ) * (t : ℂ)) by
            apply Complex.ext <;> simp [A, sub_eq_add_neg, φ₀''_imag_axis_div_im t ht,
              ψI'_imag_axis_im t ht]])
    rw [hset]
    have hIntA : IntegrableOn (fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ) *
        φ₀'' ((Complex.I : ℂ) / (t : ℂ)) * Real.exp (-π * u * t)) (Set.Ioi (0 : ℝ)) := by
      simpa [MagicFunction.g.CohnElkies.IntegralReps.aLaplaceIntegrand, mul_assoc] using
        (MagicFunction.g.CohnElkies.IntegralReps.aLaplaceIntegral_convergent (u := u) hu)
    have hIntB : IntegrableOn (fun t : ℝ => ψI' ((Complex.I : ℂ) * (t : ℂ)) *
        Real.exp (-π * u * t)) (Set.Ioi (0 : ℝ)) := by
      simpa [MagicFunction.g.CohnElkies.IntegralReps.bLaplaceIntegrand] using
        (MagicFunction.g.CohnElkies.IntegralReps.bLaplaceIntegral_convergent (u := u) hu)
    set c : ℂ := (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)
    have hsplit : (fun t : ℝ => (((-(t ^ (2 : ℕ)) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) +
        c * ψI' ((Complex.I : ℂ) * (t : ℂ))) * Real.exp (-π * u * t))) =
        fun t : ℝ => -(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
          Real.exp (-π * u * t)) +
          c * (ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)) := by
      funext t; grind only [Complex.ofReal_pow]
    rw [hsplit]
    have hIntA'' : Integrable (fun t : ℝ =>
        -(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) * Real.exp (-π * u * t)))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := hIntA.neg
    have hIntB'' : Integrable (fun t : ℝ =>
        c * (ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := hIntB.const_mul c
    change (∫ t : ℝ, -(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
        Real.exp (-π * u * t)) + c * (ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)) ∂
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) = -IA + c * IB
    rw [MeasureTheory.integral_add hIntA'' hIntB'']
    simp [IA, IB, c, mul_assoc, MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]
  have hmain : ((↑π * Complex.I) / 8640 : ℂ) *
        ((4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IA) +
        (-(Complex.I / (240 * (↑π)) : ℂ)) *
        ((-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IB) =
        (π / 2160 : ℂ) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
        (-IA + (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * IB) := by
    have h36 : (π / 2160 : ℂ) * (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) = (-(1 / (60 * π)) : ℂ) := by
      exact_mod_cast show (π / 2160 : ℝ) * (-(36 / (π ^ (2 : ℕ)) : ℝ)) = -(1 / (60 * π)) by
        field_simp [Real.pi_ne_zero]; norm_num
    grind only
  simp_all

private lemma integral_Ioi_ofReal_mul_exp (u : ℝ) (f : ℝ → ℝ) :
    (∫ t in Set.Ioi (0 : ℝ), (f t : ℂ) * Real.exp (-π * u * t)) =
      ((∫ t in Set.Ioi (0 : ℝ), f t * Real.exp (-π * u * t) : ℝ) : ℂ) := by
  simpa [Complex.ofReal_mul, mul_left_comm, mul_comm, mul_assoc] using
    (integral_ofReal (μ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) (𝕜 := ℂ)
      (f := fun t : ℝ => f t * Real.exp (-π * u * t)))

/-- If `‖x‖ ^ 2 ≥ 2`, then the real part of `g x` is nonpositive. -/
public theorem g_nonpos_of_norm_sq_ge_two (x : ℝ⁸) (hx : 2 ≤ ‖x‖ ^ 2) : (g x).re ≤ 0 := by
  rw [g_apply_eq_gRadial_norm_sq]
  refine (isClosed_Iic.preimage
      (Complex.continuous_re.comp (SchwartzMap.continuous gRadial))).closure_subset_iff.2
    (fun u' hu' => ?_) (by simpa [closure_Ioi] using hx : ‖x‖ ^ 2 ∈ closure (Set.Ioi (2 : ℝ)))
  have hEqReal : gRadial u' = (((π / 2160 : ℝ) * (Real.sin (π * u' / 2)) ^ (2 : ℕ) *
      ∫ t in Set.Ioi (0 : ℝ), A t * Real.exp (-π * u' * t) : ℝ) : ℂ) := by
    rw [gRadial_eq_integral_A (u := u') hu', integral_Ioi_ofReal_mul_exp u' A]; push_cast; ring
  have hA_neg : ∀ {t : ℝ}, 0 < t → A t < 0 := fun {t} ht => by
    set s : ℝ := 1 / t
    have hs : 0 < s := one_div_pos.2 ht
    have hA : A t = (-(t ^ (2 : ℕ))) *
        ((FReal s + c * GReal s) / (Δ.resToImagAxis s).re) := by
      simpa [s] using A_eq_neg_mul_FG_div_Delta (t := t) ht
    simpa [hA] using mul_neg_of_neg_of_pos (neg_lt_zero.2 (pow_pos ht 2))
      (div_pos (by simpa [c] using FG_inequality_1 (t := s) hs) (Delta_imag_axis_pos.2 s hs))
  exact (congrArg Complex.re hEqReal).le.trans (mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (MeasureTheory.setIntegral_nonpos (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
      measurableSet_Ioi fun t ht =>
        mul_nonpos_of_nonpos_of_nonneg (hA_neg ht).le (Real.exp_pos _).le))

/-- The real part of the Fourier transform `𝓕 g` is nonnegative. -/
public theorem fourier_g_nonneg : ∀ x : ℝ⁸, (𝓕 g x).re ≥ 0 := by
  intro x
  by_cases hx : x = 0
  · subst hx
    have h0 : (𝓕 g (0 : ℝ⁸)) = (1 : ℂ) := by
      simpa [FourierTransform.fourierCLE_apply, SchwartzMap.fourier_coe] using
        (fourier_g_zero : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) g 0 = 1)
    simp [h0]
  · have hx' : 0 < ‖x‖ ^ 2 := by positivity
    set u : ℝ := ‖x‖ ^ 2 with hu
    set IB : ℝ := ∫ t in Set.Ioi (0 : ℝ), B t * Real.exp (-π * u * t)
    set s : ℝ := (π / 2160 : ℝ) * (Real.sin (π * u / 2)) ^ (2 : ℕ)
    have hEqReal : (𝓕 g x) = ((s * IB : ℝ) : ℂ) := by
      rw [show 𝓕 g x = _ from fourier_g_eq_integral_B (x := x) hx', ← hu,
        integral_Ioi_ofReal_mul_exp u B]
      push_cast [s]; ring
    have hB_pos : ∀ {t : ℝ}, 0 < t → 0 < B t := fun {t} ht => by
      set sB : ℝ := 1 / t
      have hsB : 0 < sB := one_div_pos.2 ht
      have hΔpos : 0 < (Δ.resToImagAxis sB).re := (Delta_imag_axis_pos).2 sB hsB
      have hB :
          B t = (-(t ^ (2 : ℕ))) * ((FReal sB - c * GReal sB) / (Δ.resToImagAxis sB).re) := by
        simpa [sB] using (B_eq_neg_mul_FG_div_Delta (t := t) ht)
      simpa [hB] using mul_pos_of_neg_of_neg (neg_lt_zero.2 (pow_pos ht _))
        (div_neg_of_neg_of_pos (by simpa [c] using (FG_inequality_2 (t := sB) hsB)) hΔpos)
    have hIntegral : 0 ≤ IB :=
      MeasureTheory.setIntegral_nonneg (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi fun t ht =>
          mul_nonneg (hB_pos ht).le (Real.exp_pos _).le
    rw [ge_iff_le, congrArg Complex.re hEqReal]
    exact mul_nonneg (by change 0 ≤ (π / 2160 : ℝ) * _; positivity) hIntegral

end MagicFunction.g.CohnElkies

section E8LatticeAndPacking

variable {R : Type*}

open Module InnerProductSpace RCLike

/-! ## Basic E₈ lattice -/

lemma AddCommGroup.ModEq.zsmul' {α : Type*} [AddCommGroup α] {p a b : α} {n : ℤ}
    (h : a ≡ b [PMOD p]) : n • a ≡ n • b [PMOD p] := (h.zsmul (z := n)).of_zsmul

/-- The coefficientwise cast map `(ι → ℤ) → (ι → R)` as a `ℤ`-linear map. -/
@[expose, simps]
public def LinearMap.intCast {ι : Type*} (R : Type*) [Ring R] : (ι → ℤ) →ₗ[ℤ] (ι → R) where
  toFun f i := Int.cast (f i)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Integer vectors in `Fin n → ℤ` with even coordinate sum. -/
public def Submodule.evenLatticeInt (n : ℕ) : Submodule ℤ (Fin n → ℤ) where
  carrier := {v | ∑ i, v i ≡ 0 [PMOD 2]}
  add_mem' {a b} ha hb := by
    simpa [AddCommGroup.modEq_iff_intModEq, Pi.add_apply, Finset.sum_add_distrib] using ha.add hb
  zero_mem' := by simp
  smul_mem' c a ha := by simpa [Finset.mul_sum] using ha.zsmul' (n := c)

/-- `evenLatticeInt n` cast into `Fin n → R`. -/
public def Submodule.evenLattice (R : Type*) (n : ℕ) [Ring R] : Submodule ℤ (Fin n → R) :=
  (evenLatticeInt n).map (LinearMap.intCast R)

/-- Coordinatewise characterization of `evenLattice`: integer entries with even sum. -/
public lemma Submodule.coe_evenLattice (R : Type*) (n : ℕ) [Ring R] [CharZero R] :
    (Submodule.evenLattice R n : Set (Fin n → R)) =
    {v | (∀ i, ∃ n : ℤ, (n : R) = v i) ∧ ∑ i, v i ≡ 0 [PMOD 2]} := by
  ext v
  simp only [evenLattice, map_coe, Set.mem_image, SetLike.mem_coe, Set.mem_setOf_eq]
  refine ⟨fun ⟨f, hf, hfv⟩ => hfv ▸ ⟨fun i ↦ ⟨f i, by simp⟩, ?_⟩, fun ⟨hv, hv'⟩ => ?_⟩
  · simpa [Int.cast_sum] using
      (by simpa [evenLatticeInt] using hf : (∑ i, f i : ℤ) ≡ 0 [PMOD 2]).intCast (G := R)
  choose w hw using hv
  refine ⟨w, ?_, by ext i; simpa using hw i⟩
  simpa [evenLatticeInt] using (AddCommGroup.intCast_modEq_intCast' (G := R)
    (a := ∑ i, w i) (b := 0) (n := 2)).1 (by simpa [← hw, Int.cast_sum] using hv')

public lemma Submodule.mem_evenLattice {R : Type*} [Ring R] [CharZero R] (n : ℕ) {v : Fin n → R} :
    v ∈ Submodule.evenLattice R n ↔
      (∀ i, ∃ n : ℤ, (n : R) = v i) ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  simp [← SetLike.mem_coe, Submodule.coe_evenLattice]

/-- The `E8` lattice as a `ℤ`-submodule of `Fin 8 → R`, defined by parity conditions. -/
public noncomputable def Submodule.E8 (R : Type*) [Field R] [NeZero (2 : R)] :
    Submodule ℤ (Fin 8 → R) where
  carrier :=
    {v | ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i)) ∧ ∑ i, v i ≡ 0 [PMOD 2]}
  add_mem' := by
    simp only [Set.mem_setOf_eq, and_imp, nsmul_eq_mul, Nat.cast_ofNat, Pi.add_apply]
    rintro a b ha has hb hbs
    refine ⟨?_, by simpa [Finset.sum_add_distrib] using
      ((has.add_right _).trans (hbs.add_left _)).trans (by simp)⟩
    obtain ha | ha := ha
    · refine hb.imp (fun hb i => ?_) (fun hb i => ?_) <;> obtain ⟨a', ha⟩ := ha i
      · exact let ⟨b', hb⟩ := hb i; ⟨a' + b', by simp [ha, hb]⟩
      exact let ⟨b', hb', hb⟩ := hb i
        ⟨2 * a' + b', Even.add_odd (by simp) hb', by simp [← ha, ← hb, mul_add]⟩
    refine hb.symm.imp (fun hb i => ?_) (fun hb i => ?_) <;> obtain ⟨a', ha', ha⟩ := ha i
    · obtain ⟨b', hb', hb⟩ := hb i
      exact ⟨(a' + b') / 2, by
        rw [Int.cast_div ((even_iff_two_dvd ..).1 (ha'.add_odd hb')) (by simpa using NeZero.ne 2),
          Int.cast_add, add_div (K := R), ha, hb, Int.cast_ofNat,
          mul_div_cancel_left₀ _ (NeZero.ne 2), mul_div_cancel_left₀ _ (NeZero.ne _)]⟩
    exact let ⟨b', hb⟩ := hb i
      ⟨a' + 2 * b', ha'.add_even (by simp), by simp [ha, hb, mul_add]⟩
  zero_mem' := ⟨.inl fun _ => ⟨0, by simp⟩, by simp⟩
  smul_mem' := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Set.mem_setOf_eq, zsmul_eq_mul, Pi.mul_apply,
      Pi.intCast_apply, and_imp]
    refine fun c a ha has => ⟨?_, by simpa [zsmul_eq_mul, Finset.mul_sum] using has.zsmul' (n := c)⟩
    rcases ha with ha | ha
    · exact .inl fun i ↦ let ⟨a, ha⟩ := ha i; ⟨c * a, by simp [← ha, Int.cast_mul]⟩
    rcases c.even_or_odd with ⟨c, rfl⟩ | hc
    · exact .inl fun i ↦ let ⟨j, hj, hj'⟩ := ha i
        ⟨c * j, by rw [Int.cast_mul, hj', Int.cast_add]; ring⟩
    exact .inr fun i ↦ let ⟨j, hj, hj'⟩ := ha i
      ⟨c * j, by simp [hc, hj, hj', mul_left_comm]⟩

lemma Submodule.mem_E8 {R : Type*} [Field R] [NeZero (2 : R)] {v : Fin 8 → R} :
    v ∈ E8 R ↔ ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i))
      ∧ ∑ i, v i ≡ 0 [PMOD 2] := Iff.rfl

lemma Submodule.mem_E8'' {R : Type*} [Field R] [NeZero (2 : R)] {v : Fin 8 → R} :
    v ∈ E8 R ↔ ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, n + 2⁻¹ = v i))
      ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  rw [mem_E8]
  suffices ∀ i, (∃ n : ℤ, Odd n ∧ n = 2 • v i) ↔ (∃ n : ℤ, n + 2⁻¹ = v i) by simp_rw [this]
  exact fun i => ⟨fun ⟨_, ⟨k, rfl⟩, hn'⟩ => ⟨k, by
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, nsmul_eq_mul,
      Nat.cast_ofNat] at hn'
    linear_combination 2⁻¹ * hn' - (k - v i) * inv_mul_cancel₀ (NeZero.ne (2 : R))⟩,
    fun ⟨k, hk⟩ => ⟨2 * k + 1, by simp, by rw [← hk]; simp [NeZero.ne]⟩⟩

theorem Submodule.E8_eq_sup (R : Type*) [Field R] [CharZero R] :
    E8 R = (evenLattice R 8 ⊔ Submodule.span ℤ {fun _ ↦ (2⁻¹ : R)}) := by
  refine le_antisymm (fun x => ?_) (sup_le
    (fun v hv ↦ by simp [mem_E8, (mem_evenLattice (R := R) (n := 8)).1 hv])
    (Submodule.span_le.2 <| by
      simpa [mem_E8, show (8 * 2⁻¹ : R) = (2 : ℤ) • 2 by norm_num] using
        AddCommGroup.zsmul_modEq_zero (p := (2 : R)) 2))
  rw [mem_E8]
  rintro ⟨hx | hx, hx'⟩
  · exact Submodule.mem_sup_left ((mem_evenLattice (R := R) (n := 8)).2 ⟨hx, hx'⟩)
  simp only [Odd] at hx
  choose y hy hy' using hx
  choose z hz using hy
  simp only [hz, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_ofNat] at *
  rw [show (evenLattice R 8 : Submodule ℤ (Fin 8 → R)) = span ℤ (evenLattice R 8) by simp,
    sup_comm, ← Submodule.span_insert, Submodule.mem_span_insert, span_eq]
  refine ⟨1, LinearMap.intCast R z, ?_, by
    ext i; rw [Pi.add_apply, LinearMap.intCast_apply, Pi.smul_apply, one_smul]
    linear_combination - 2⁻¹ * hy' i⟩
  rw [← SetLike.mem_coe, coe_evenLattice]
  simp_rw [show ∀ i, x i = z i + 2⁻¹ from fun i => by linear_combination - 2⁻¹ * hy' i,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, show (8 : R) * 2⁻¹ = 2 • 2 by norm_num] at hx'
  exact ⟨by simp, by simpa using (AddCommGroup.add_nsmul_modEq _).symm.trans hx'⟩

/-- Concrete matrix whose rows form a basis for the `E8` lattice. -/
@[expose] public def E8Matrix (R : Type*) [Field R] : Matrix (Fin 8) (Fin 8) R :=
  !![2, 0, 0, 0, 0, 0, 0, 0; -1, 1, 0, 0, 0, 0, 0, 0;
     0, -1, 1, 0, 0, 0, 0, 0; 0, 0, -1, 1, 0, 0, 0, 0;
     0, 0, 0, -1, 1, 0, 0, 0; 0, 0, 0, 0, -1, 1, 0, 0;
     0, 0, 0, 0, 0, -1, 1, 0; 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹]

public lemma E8Matrix_row_mem_E8 [Field R] [CharZero R] :
    ∀ i, (E8Matrix R).row i ∈ Submodule.E8 R := by
  rw [Submodule.E8_eq_sup, Fin.forall_fin_succ']
  refine ⟨fun i => Submodule.mem_sup_left ?_, Submodule.mem_sup_right <| Submodule.subset_span <| by
    simp [E8Matrix, Fin.reduceLast, Matrix.of_row, Matrix.cons_val, funext_iff,
      Fin.forall_fin_succ]⟩
  revert i
  simp [Fin.forall_fin_succ, E8Matrix, Submodule.mem_evenLattice, Fin.sum_univ_eight,
    show ∃ n : ℤ, (n : R) = 2 from ⟨2, by simp⟩, show ∃ n : ℤ, (n : R) = -1 from ⟨-1, by simp⟩]

lemma E8Matrix_eq_cast (R : Type*) [Field R] [CharZero R] :
    E8Matrix R = (E8Matrix ℚ).map (Rat.castHom R) := by
  rw [← Matrix.ext_iff]; norm_num [Fin.forall_fin_succ, E8Matrix]

public theorem E8Matrix_unimodular (R : Type*) [Field R] [NeZero (2 : R)] :
    (E8Matrix R).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (by simp [Matrix.BlockTriangular, E8Matrix,
    Fin.forall_fin_succ] : (E8Matrix R).BlockTriangular OrderDual.toDual)]
  simp [E8Matrix, Fin.prod_univ_eight, NeZero.ne (2 : R)]

private lemma E8Matrix_is_basis (R : Type*) [Field R] [NeZero (2 : R)] :
    LinearIndependent R (E8Matrix R).row ∧
    Submodule.span R (Set.range (E8Matrix R).row) = ⊤ := by
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det, ← Matrix.det, Matrix.row,
    E8Matrix_unimodular]; simp

public lemma linearIndependent_E8Matrix (R : Type*) [Field R] [NeZero (2 : R)] :
    LinearIndependent R (E8Matrix R).row := (E8Matrix_is_basis _).1

public lemma span_E8Matrix_eq_top (R : Type*) [Field R] [NeZero (2 : R)] :
    Submodule.span R (Set.range (E8Matrix R).row) = ⊤ := (E8Matrix_is_basis _).2

/-- Basis of `Fin 8 → R` given by the rows of `E8Matrix`. -/
@[expose] public noncomputable def E8Basis (R : Type*) [Field R] [NeZero (2 : R)] :
    Basis (Fin 8) R (Fin 8 → R) :=
  Basis.mk (linearIndependent_E8Matrix R) (span_E8Matrix_eq_top R).ge

public lemma E8Basis_apply [Field R] [NeZero (2 : R)] (i : Fin 8) :
    E8Basis R i = (E8Matrix R).row i := by simp [E8Basis, Matrix.row]

public lemma of_basis_eq_matrix [Field R] [CharZero R] : Matrix.of (E8Basis R) = E8Matrix R := by
  ext; simp [E8Basis_apply]

public theorem range_E8Matrix_row_subset (R : Type*) [Field R] [CharZero R] :
    Set.range (E8Matrix R).row ⊆ Submodule.E8 R :=
  Set.range_subset_iff.2 (E8Matrix_row_mem_E8 (R := R))

def E8Inverse (R : Type*) [Field R] [NeZero (2 : R)] : Matrix (Fin 8) (Fin 8) R :=
  !![2⁻¹, 0, 0, 0, 0, 0, 0, 0; 2⁻¹, 1, 0, 0, 0, 0, 0, 0;
     2⁻¹, 1, 1, 0, 0, 0, 0, 0; 2⁻¹, 1, 1, 1, 0, 0, 0, 0;
     2⁻¹, 1, 1, 1, 1, 0, 0, 0; 2⁻¹, 1, 1, 1, 1, 1, 0, 0;
     2⁻¹, 1, 1, 1, 1, 1, 1, 0; -7 * 2⁻¹, -6, -5, -4, -3, -2, -1, 2]

lemma exists_cast_eq_vecMul_E8Inverse {R : Type*} [Field R] [CharZero R]
    (v : Fin 8 → R) (hv : v ∈ Submodule.E8 R) :
    ∃ c : Fin 8 → ℤ, LinearMap.intCast R c = Matrix.vecMul v (E8Inverse R) := by
  set c' := Matrix.vecMul v (E8Inverse R)
  have aux (w : Fin 8 → ℤ) (hw : ∑ i, w i = 0) (k : Fin 8)
      (hk : c' k = ∑ i, v i * w i := by
        simp [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse]) :
      ∃ n : ℤ, (n : R) = c' k := by
    obtain ⟨hv' | hv', _⟩ := Submodule.mem_E8''.1 hv <;> choose v' hv' using hv'
    exacts [⟨∑ i, v' i * w i, by simp [hk, ← hv', Int.cast_sum, Int.cast_mul]⟩,
      ⟨∑ i, v' i * w i, by simp [hk, ← hv', add_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
        Int.cast_sum, Int.cast_mul, show (∑ i, (w i : R)) = 0 from by exact_mod_cast hw]⟩]
  obtain ⟨c0, hc0⟩ : ∃ n : ℤ, (n : R) = c' 0 := by
    have h0' : c' 0 = (∑ i, v i) * 2⁻¹ - 4 * v 7 := by
      simp [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse]; ring
    obtain ⟨h0, h1⟩ := Submodule.mem_E8.1 hv
    obtain ⟨a, ha⟩ := AddCommGroup.modEq_iff_zsmul'.1 h1.symm
    rw [(by simpa [sub_zero, zsmul_eq_mul] using ha : ∑ i, v i = a * 2),
      mul_inv_cancel_right₀ (NeZero.ne 2)] at h0'
    obtain h0 | h0 := h0 <;> obtain ⟨n, hn⟩ := h0 7
    exacts [⟨a - 4 * n, by simp [hn, h0']⟩,
      ⟨a - 2 * n, by norm_num [hn, h0', mul_add, add_comm, ← mul_assoc]⟩]
  obtain ⟨c7, hc7⟩ : ∃ n : ℤ, (n : R) = c' 7 := by
    have hc7' : c' 7 = 2 * v 7 := by
      simp [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse, mul_comm]
    obtain ⟨h0 | h0, _⟩ := Submodule.mem_E8''.1 hv <;> obtain ⟨n, hn⟩ := h0 7
    exacts [⟨2 * n, by simp [hn, hc7']⟩, ⟨2 * n + 1, by simp [← hn, hc7', mul_add]⟩]
  obtain ⟨c1, hc1⟩ := aux ![0, 1, 1, 1, 1, 1, 1, -6] rfl 1
  obtain ⟨c2, hc2⟩ := aux ![0, 0, 1, 1, 1, 1, 1, -5] rfl 2
  obtain ⟨c3, hc3⟩ := aux ![0, 0, 0, 1, 1, 1, 1, -4] rfl 3
  obtain ⟨c4, hc4⟩ := aux ![0, 0, 0, 0, 1, 1, 1, -3] rfl 4
  obtain ⟨c5, hc5⟩ := aux ![0, 0, 0, 0, 0, 1, 1, -2] rfl 5
  obtain ⟨c6, hc6⟩ := aux ![0, 0, 0, 0, 0, 0, 1, -1] rfl 6
  exact ⟨![c0, c1, c2, c3, c4, c5, c6, c7], by rw [funext_iff]; simp [Fin.forall_fin_succ, *]⟩

/-- The `E8` lattice is the `ℤ`-span of the rows of `E8Matrix`. -/
public theorem span_E8Matrix (R : Type*) [Field R] [CharZero R] :
    Submodule.span ℤ (Set.range (E8Matrix R).row) = Submodule.E8 R := by
  refine Submodule.span_eq_of_le _ (range_E8Matrix_row_subset R) fun v hv ↦ ?_
  rw [Submodule.mem_span_range_iff_exists_fun]
  obtain ⟨c, hc⟩ := exists_cast_eq_vecMul_E8Inverse v hv
  exact ⟨c, by
    simpa [Matrix.vecMul_eq_sum, Matrix.row, LinearMap.intCast_apply, zsmul_eq_mul] using
      show Matrix.vecMul (LinearMap.intCast R c) (E8Matrix R) = v by
        rw [hc, Matrix.vecMul_vecMul, show E8Inverse R * E8Matrix R = 1 by
          rw [E8Matrix_eq_cast, show E8Inverse R = (E8Inverse ℚ).map (Rat.castHom R) by
              rw [← Matrix.ext_iff]; norm_num [Fin.forall_fin_succ, E8Inverse],
            ← Matrix.map_mul, show E8Inverse ℚ * E8Matrix ℚ = 1 by decide +kernel]; simp]
        simp⟩

def E8.inn : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, -2, 0, 0, 0, 0, 0, 1; -2, 2, -1, 0, 0, 0, 0, 0;
     0, -1, 2, -1, 0, 0, 0, 0; 0, 0, -1, 2, -1, 0, 0, 0;
     0, 0, 0, -1, 2, -1, 0, 0; 0, 0, 0, 0, -1, 2, -1, 0;
     0, 0, 0, 0, 0, -1, 2, 0; 1, 0, 0, 0, 0, 0, 0, 2]

lemma dotProduct_eq_inn {R : Type*} [Field R] [CharZero R] (i j : Fin 8) :
    (E8Matrix R).row i ⬝ᵥ (E8Matrix R).row j = E8.inn i j := by
  simpa [Matrix.mul_apply', Matrix.col_transpose] using congrArg (· i j)
    (show E8Matrix R * (E8Matrix R).transpose = E8.inn.map (↑) by
      rw [E8Matrix_eq_cast, ← Matrix.transpose_map, ← Matrix.map_mul,
        show E8Matrix ℚ * (E8Matrix ℚ).transpose = E8.inn.map (↑) by decide +kernel,
        Matrix.map_map]; ext; simp)

/-- The squared norm of a vector in `E8` is an even integer. -/
public theorem E8_integral_self {R : Type*} [Field R] [CharZero R] (v : Fin 8 → R)
    (hv : v ∈ Submodule.E8 R) : ∃ z : ℤ, Even z ∧ z = v ⬝ᵥ v := by
  rw [← span_E8Matrix, Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, rfl⟩ := hv
  simp_rw [sum_dotProduct, dotProduct_sum, dotProduct_smul, smul_dotProduct, dotProduct_eq_inn,
    zsmul_eq_mul]
  norm_cast
  simp only [exists_eq_right, E8.inn, Fin.sum_univ_eight, Matrix.of_apply, Matrix.cons_val, mul_neg,
    mul_zero, add_zero, mul_one, zero_add]
  ring_nf; simp [show Even (4 : ℤ) from ⟨2, rfl⟩, parity_simps]

/-! ## E₈ packing -/

lemma E8_norm_lower_bound (v : Fin 8 → ℝ) (hv : v ∈ Submodule.E8 ℝ) :
    v = 0 ∨ √2 ≤ ‖WithLp.toLp 2 v‖ := by
  rw [or_iff_not_imp_left, ← ne_eq]
  intro hv'
  obtain ⟨n, hn, hn'⟩ : ∃ n : ℤ, Even n ∧ n = ‖WithLp.toLp 2 v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]
    exact E8_integral_self _ hv
  have hn_ne : n ≠ 0 := by contrapose! hv'; simpa [hv'] using hn'.symm
  have hn2 : 2 ≤ n := by
    have : 0 ≤ n := by exact_mod_cast (by simp [hn'] : (0 : ℝ) ≤ (n : ℝ))
    obtain ⟨k, rfl⟩ := hn; omega
  exact le_of_sq_le_sq
    (by simpa [hn', Real.sq_sqrt zero_le_two] using (show (2 : ℝ) ≤ n from mod_cast hn2)) (by simp)

/-- The `E8` lattice as a `ℤ`-submodule of `EuclideanSpace ℝ (Fin 8)`. -/
public noncomputable def E8Lattice : Submodule ℤ (EuclideanSpace ℝ (Fin 8)) :=
  (Submodule.E8 ℝ).map (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm.toLinearMap

/-- The `E8` lattice is a discrete subgroup of `EuclideanSpace ℝ (Fin 8)`. -/
public instance instDiscreteE8Lattice : DiscreteTopology E8Lattice := by
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
  refine ⟨1, by norm_num, ?_⟩
  rintro ⟨_, ⟨v, hv, rfl⟩⟩ hx'
  suffices v = 0 by simpa using congrArg (WithLp.toLp 2) this
  exact (E8_norm_lower_bound v hv).resolve_right (not_le_of_gt (lt_trans
    (by simpa [dist_zero_right, AddSubgroupClass.coe_norm] using hx') Real.one_lt_sqrt_two))

/-- `E8Lattice` spans the ambient space over `ℝ`. -/
public instance instIsZLatticeE8Lattice : IsZLattice ℝ E8Lattice where
  span_top := by
    have hE8 : Submodule.span ℝ (Submodule.E8 ℝ : Set (Fin 8 → ℝ)) = ⊤ :=
      eq_top_iff.2 (by simpa [span_E8Matrix_eq_top ℝ] using
        Submodule.span_mono (R := ℝ) (range_E8Matrix_row_subset ℝ))
    change Submodule.span ℝ
      ((WithLp.linearEquiv 2 ℝ (Fin 8 → ℝ)).symm.toLinearMap '' (Submodule.E8 ℝ : Set _)) = ⊤
    rw [Submodule.span_image, hE8]; simp

noncomputable def E8_ℤBasis : Basis (Fin 8) ℤ E8Lattice := by
  refine Basis.mk
      (v := fun i ↦ ⟨(WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i), ?_⟩) ?_ ?_
  · exact Submodule.mem_map_of_mem (E8Matrix_row_mem_E8 i)
  · exact LinearIndependent.of_comp (Submodule.subtype _) <|
      LinearIndependent.of_comp (M' := (Fin 8 → ℝ)) (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ))
        ((linearIndependent_E8Matrix ℝ).restrict_scalars' ℤ)
  · rw [← Submodule.map_le_map_iff_of_injective (f := E8Lattice.subtype) (by simp),
      Submodule.map_top, Submodule.range_subtype, Submodule.map_span, ← Set.range_comp]
    refine (?_ : Submodule.span ℤ
        (Set.range fun i ↦ (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i)) =
        E8Lattice).ge
    rw [show Set.range (fun i ↦ (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i)) =
          ((WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm :
              (Fin 8 → ℝ) →ₗ[ℤ] EuclideanSpace ℝ (Fin 8)) '' Set.range (E8Matrix ℝ).row by
        simpa [Function.comp] using
          Set.range_comp (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm (E8Matrix ℝ).row,
      ← Submodule.map_span, span_E8Matrix ℝ]
    simp [E8Lattice]

open scoped Real

/-- The periodic sphere packing in `ℝ^8` coming from the `E8` lattice. -/
@[expose] public noncomputable def E8Packing : PeriodicSpherePacking 8 where
  separation := √2
  lattice := E8Lattice
  centers := E8Lattice
  centers_dist := by
    simp only [Pairwise, E8Lattice, ne_eq, Subtype.forall, Subtype.mk.injEq]
    rintro _ ⟨a', ha', rfl⟩ _ ⟨b', hb', rfl⟩ hab
    simp only [dist_eq_norm, AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub]
    convert (E8_norm_lower_bound _ (Submodule.sub_mem _ ha' hb')).resolve_left
      (sub_ne_zero.mpr (by contrapose! hab; simp [hab])) using 2
  lattice_action x y := add_mem

private lemma E8_ℤBasis_apply_norm : ∀ i : Fin 8, ‖E8_ℤBasis i‖ ≤ 2 := by
  have hbase : ∀ i : Fin 8, ‖WithLp.toLp 2 (E8Basis ℝ i)‖ ≤ 2 := by
    simp [E8Basis, E8Matrix, EuclideanSpace.norm_eq, Fin.forall_fin_succ, Fin.sum_univ_eight]
    norm_num [show (√2 : ℝ) ≤ 2 by rw [Real.sqrt_le_iff]; norm_num]
  simpa [E8_ℤBasis, Basis.coe_mk, E8Basis_apply] using hbase

open MeasureTheory ZSpan in
/-- The density of the `E8` packing. -/
public theorem E8Packing_density : E8Packing.density = ENNReal.ofReal π ^ 4 / 384 := by
  rw [PeriodicSpherePacking.density_eq E8_ℤBasis ?_ (by omega) (L := 16)]
  · rw [PeriodicSpherePacking.numReps_eq_one _ rfl, Nat.cast_one, one_mul, volume_ball,
      finrank_euclideanSpace,
      Fintype.card_fin, Nat.cast_ofNat]
    simp only [E8Packing]
    have {x : ℝ} (hx : 0 ≤ x := by positivity) : √x ^ 8 = x ^ 4 := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt hx]
    rw [← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, div_pow, this, this, ← mul_div_assoc,
      div_mul_eq_mul_div, mul_comm, mul_div_assoc, mul_div_assoc]
    · norm_num [Nat.factorial, mul_one_div]
      convert div_one _
      · have hpreim : (WithLp.linearEquiv 2 ℝ _).symm ⁻¹' fundamentalDomain
            (E8_ℤBasis.ofZLatticeBasis ℝ E8Lattice) = fundamentalDomain (E8Basis ℝ) := by
          rw [← LinearEquiv.image_eq_preimage_symm, ZSpan.map_fundamentalDomain]
          congr! 1; ext i : 1; simp [E8_ℤBasis, E8Basis_apply]
        rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
          _).symm.measure_preimage_equiv]
        erw [hpreim, show volume (fundamentalDomain (E8Basis ℝ)) = 1 by
          simp [volume_fundamentalDomain (b := E8Basis ℝ), of_basis_eq_matrix,
            E8Matrix_unimodular (R := ℝ)]]
      · rw [← ENNReal.ofReal_pow, ENNReal.ofReal_div_of_pos, ENNReal.ofReal_ofNat] <;> positivity
    · positivity
    · positivity
  · intro x hx
    trans ∑ i, ‖E8_ℤBasis i‖
    · rw [← fract_eq_self.mpr hx]; convert norm_fract_le (K := ℝ) _ _; simp; rfl
    · exact (Finset.sum_le_sum (fun i _ ↦ E8_ℤBasis_apply_norm i)).trans (by norm_num)

end E8LatticeAndPacking

namespace SpherePacking

open scoped FourierTransform ENNReal SchwartzMap
open SchwartzMap SpherePacking.ForMathlib.Fourier
open MeasureTheory Real SpherePacking Metric

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)

/-- Non-vanishing of `Real.sqrt 2`. -/
public lemma sqrt2_ne_zero : (Real.sqrt (2 : ℝ)) ≠ 0 :=
  Real.sqrt_ne_zero'.2 (by positivity)

/-- The scaled Schwartz function used for the dimension-8 Cohn-Elkies LP bound. -/
@[expose] public noncomputable def scaledMagic : 𝓢(ℝ⁸, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ⁸) (Real.sqrt 2) sqrt2_ne_zero).toContinuousLinearEquiv
    g

/-- The value of `scaledMagic` at `0` is `1`. -/
public theorem scaledMagic_zero : scaledMagic 0 = 1 := by
  simp [scaledMagic, g_zero]

/-- The value of the Fourier transform of `scaledMagic` at `0` is `1 / 16`. -/
public theorem fourier_scaledMagic_zero : FT scaledMagic 0 = (1 / 16 : ℂ) := by
  let c : ℝ := Real.sqrt 2
  let A : ℝ⁸ ≃ₗ[ℝ] ℝ⁸ := LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ⁸) c sqrt2_ne_zero
  have hdet : abs (LinearMap.det (A : ℝ⁸ →ₗ[ℝ] ℝ⁸)) = (16 : ℝ) := by
    have hA : (A : ℝ⁸ →ₗ[ℝ] ℝ⁸) = c • (LinearMap.id : ℝ⁸ →ₗ[ℝ] ℝ⁸) := by ext x; simp [A]
    have hc_pow : c ^ 8 = (16 : ℝ) := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul,
        show c ^ 2 = 2 from Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hA]; simp [LinearMap.det_smul, LinearMap.det_id, hc_pow]
  have hg0 : (𝓕 (g : ℝ⁸ → ℂ)) 0 = (1 : ℂ) := by
    simpa [FourierTransform.fourierCLE_apply, SchwartzMap.fourier_coe] using
      (fourier_g_zero : FT g 0 = 1)
  have hscaled :
      FT scaledMagic 0 =
        (abs (LinearMap.det (A : ℝ⁸ →ₗ[ℝ] ℝ⁸)))⁻¹ • (𝓕 (g : ℝ⁸ → ℂ)) 0 := by
    simpa [FourierTransform.fourierCLE_apply, SchwartzMap.fourier_coe, scaledMagic, c, A,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      (SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv
        (A := A) (f := (g : ℝ⁸ → ℂ)) (w := (0 : ℝ⁸)))
  simp_all

/-- Convenience form of `fourier_scaledMagic_zero` for the coerced function `⇑scaledMagic`. -/
public theorem fourier_scaledMagic_zero_fun : 𝓕 (⇑scaledMagic) 0 = (1 / 16 : ℂ) := by
  simpa [FourierTransform.fourierCLE_apply, SchwartzMap.fourier_coe] using fourier_scaledMagic_zero

end SpherePacking

namespace MagicFunction.g.CohnElkies

open scoped FourierTransform SchwartzMap
open Real Complex MagicFunction.FourierEigenfunctions
open MeasureTheory

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)

namespace PureImaginary

private lemma setIntegral_im_ofReal (f : ℝ → ℝ) :
    (∫ t in Set.Ioi (0 : ℝ), ((f t : ℝ) : ℂ)).im = 0 := by
  simpa using congrArg Complex.im
    (integral_ofReal (μ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) (𝕜 := ℂ) (f := f))

lemma a'_re_eq_zero_of_pos_ne_two {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) : (a' u).re = 0 := by
  have hEq := IntegralReps.aRadial_eq_another_integral_main (u := u) hu hu2
  set Iterm : ℂ :=
      ∫ t in Set.Ioi (0 : ℝ),
        ((((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                ((8640 / π : ℝ) : ℂ) * t -
                ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) *
            Real.exp (-π * u * t))
  set E : ℂ := (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
    (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) + (18144 : ℂ) / (π ^ (3 : ℕ) * u) + Iterm
  have hEq' : a' u = (4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * E := by
    simpa [E, Iterm, IntegralReps.aAnotherIntegrand, mul_assoc] using hEq
  have hIterm : Iterm.im = 0 := by
    let innerR : ℝ → ℝ := fun t => (t ^ (2 : ℕ)) * (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re -
      (36 / (π ^ (2 : ℕ)) : ℝ) * Real.exp (2 * π * t) +
      (8640 / π : ℝ) * t - (18144 / (π ^ (2 : ℕ)) : ℝ)
    rw [show Iterm = ∫ t in Set.Ioi (0 : ℝ), ((innerR t * Real.exp (-π * u * t) : ℝ) : ℂ) from
      MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi fun t (ht : 0 < t) => by
          rw [show φ₀'' ((Complex.I : ℂ) / (t : ℂ)) =
            ((φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re : ℂ) from by
              apply Complex.ext <;> simp [φ₀''_imag_axis_div_im t ht]]
          push_cast [innerR]; ring]
    exact setIntegral_im_ofReal (f := fun t => innerR t * Real.exp (-π * u * t))
  have hEim : E.im = 0 := by
    simp [E, Complex.add_im, Complex.sub_im, hIterm, Complex.div_im, Complex.mul_im,
      Complex.im_pow_eq_zero_of_im_eq_zero (show ((π : ℂ)).im = 0 by simp) 3,
      Complex.im_pow_eq_zero_of_im_eq_zero (show ((u : ℂ)).im = 0 by simp) 2]
  rw [hEq', show ((Real.sin (π * u / 2) : ℂ) ^ (2 : ℕ)) =
      (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) by simp [Complex.ofReal_pow]]
  have : (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ).im = 0 := Complex.ofReal_im _
  simp_all

lemma b'_re_eq_zero_of_pos_ne_two {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) : (b' u).re = 0 := by
  have hEq := IntegralReps.bRadial_eq_another_integral_main (u := u) hu hu2
  set Iterm : ℂ :=
      ∫ t in Set.Ioi (0 : ℝ),
        (ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) - Real.exp (2 * π * t)) *
          Real.exp (-π * u * t)
  set E : ℂ := (144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + Iterm
  have hEq' : b' u = (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * E := by
    simpa [E, Iterm, IntegralReps.bAnotherIntegrand, mul_assoc] using hEq
  have hIterm : Iterm.im = 0 := by
    let innerR : ℝ → ℝ := fun t =>
      (ψI' ((Complex.I : ℂ) * (t : ℂ))).re - (144 : ℝ) - Real.exp (2 * π * t)
    rw [show Iterm = ∫ t in Set.Ioi (0 : ℝ), ((innerR t * Real.exp (-π * u * t) : ℝ) : ℂ) from
      MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi fun t (ht : 0 < t) => by
          rw [show ψI' ((Complex.I : ℂ) * (t : ℂ)) =
            ((ψI' ((Complex.I : ℂ) * (t : ℂ))).re : ℂ) from by
              apply Complex.ext <;> simp [ψI'_imag_axis_im t ht]]
          push_cast [innerR]; ring]
    exact setIntegral_im_ofReal (f := fun t => innerR t * Real.exp (-π * u * t))
  have hEim : E.im = 0 := by
    simp [E, Complex.add_im, hIterm, Complex.div_im, Complex.mul_im]
  rw [hEq', show ((Real.sin (π * u / 2) : ℂ) ^ (2 : ℕ)) =
      (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) by simp [Complex.ofReal_pow]]
  have : (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ).im = 0 := Complex.ofReal_im _
  simp_all

/-- Extend `re = 0` from `(0,∞) \ {2}` to all of `(0,∞)` using continuity. -/
private lemma re_eq_zero_of_pos_from_ne_two (f : ℝ → ℂ) (hcont : Continuous f)
    (h : ∀ {u : ℝ}, 0 < u → u ≠ 2 → (f u).re = 0) {u : ℝ} (hu : 0 < u) : (f u).re = 0 := by
  by_cases hu2 : u = 2
  · subst hu2
    refine (IsClosed.closure_subset_iff
        (isClosed_eq (Complex.continuous_re.comp hcont) continuous_const)).2
      (fun r (hr : r ∈ Set.Ioi (0 : ℝ) \ ({2} : Set ℝ)) =>
        h hr.1 fun h' => hr.2 (by simp [h']))
      (Metric.mem_closure_iff.2 fun ε hε => ⟨2 + ε / 2,
        ⟨show (0 : ℝ) < 2 + ε / 2 by positivity,
          fun h => by linarith [show (2 + ε / 2 : ℝ) = 2 by simpa using h]⟩, ?_⟩)
    rw [Real.dist_eq, show (2 : ℝ) - (2 + ε / 2) = -(ε/2) by ring, abs_neg,
      abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith
  · exact h hu hu2

end PureImaginary

/-- The eigenfunction `a` is purely imaginary-valued (its real part vanishes). -/
public theorem a_pureImag (x : ℝ⁸) : (a x).re = 0 := by
  by_cases hx : x = 0
  · subst hx; simp [MagicFunction.a.SpecialValues.a_zero]
  · simpa [MagicFunction.FourierEigenfunctions.a, schwartzMap_multidimensional_of_schwartzMap_real,
      SchwartzMap.compCLM_apply] using PureImaginary.re_eq_zero_of_pos_from_ne_two a'
        (SchwartzMap.continuous a') PureImaginary.a'_re_eq_zero_of_pos_ne_two
        (u := ‖x‖ ^ 2) (by simpa using pow_pos (norm_pos_iff.2 hx) 2)

/-- The eigenfunction `b` is purely imaginary-valued (its real part vanishes). -/
public theorem b_pureImag (x : ℝ⁸) : (b x).re = 0 := by
  by_cases hx : x = 0
  · subst hx; simp [MagicFunction.b.SpecialValues.b_zero]
  · simpa [MagicFunction.FourierEigenfunctions.b, schwartzMap_multidimensional_of_schwartzMap_real,
      SchwartzMap.compCLM_apply] using PureImaginary.re_eq_zero_of_pos_from_ne_two b'
        (SchwartzMap.continuous b') PureImaginary.b'_re_eq_zero_of_pos_ne_two
        (u := ‖x‖ ^ 2) (by simpa using pow_pos (norm_pos_iff.2 hx) 2)

private theorem ofReal_re_eq (z : ℂ) (hz : z.im = 0) : (↑z.re : ℂ) = z :=
  Complex.ext (by simp) (by simp [hz])

/-- The magic function `g` is real-valued. -/
public theorem g_real (x : ℝ⁸) : (↑(g x).re : ℂ) = g x :=
  ofReal_re_eq (g x) <| by
    simp [g, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, Complex.sub_im,
      Complex.mul_im, a_pureImag (x := x), b_pureImag (x := x), div_eq_mul_inv, Complex.mul_re]

/-- The Fourier transform `𝓕 g` is real-valued. -/
public theorem g_real_fourier (x : ℝ⁸) : (↑((𝓕 g x).re : ℂ)) = (𝓕 g x) := by
  refine ofReal_re_eq (𝓕 g x) ?_
  have hFg : FT g = ((↑π * I) / 8640) • a + (I / (240 * (↑π))) • b := by
    simp [g, map_sub, map_smul, MagicFunction.a.Fourier.eig_a, MagicFunction.b.Fourier.eig_b,
      -FourierTransform.fourierCLE_apply]
  change ((𝓕 g) x).im = 0
  rw [show (𝓕 g) = FT g from by simp, hFg]
  simp [SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul, Complex.add_im, Complex.mul_im,
    a_pureImag (x := x), b_pureImag (x := x), div_eq_mul_inv, Complex.mul_re]

end MagicFunction.g.CohnElkies

namespace SpherePacking

open scoped FourierTransform ENNReal SchwartzMap
open Real Complex SpherePacking MeasureTheory Metric

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open MagicFunction.g.CohnElkies

private noncomputable def scaleEquiv : ℝ⁸ ≃ₗ[ℝ] ℝ⁸ :=
  LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ⁸) (Real.sqrt 2) sqrt2_ne_zero

/-- `scaledMagic` is real-valued (scaled variant of `g_real`). -/
public theorem scaledMagic_real' : ∀ x : ℝ⁸, (↑(scaledMagic x).re : ℂ) = scaledMagic x := by
  simpa [SpherePacking.scaledMagic] using fun x => g_real (x := (Real.sqrt 2) • x)

private lemma fourier_scaledMagic_eq (x : ℝ⁸) :
    (𝓕 scaledMagic x) =
      |LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹ •
        𝓕 g ((LinearMap.adjoint ((scaleEquiv.symm : ℝ⁸ ≃ₗ[ℝ] ℝ⁸) : ℝ⁸ →ₗ[ℝ] ℝ⁸)) x) := by
  simpa [SpherePacking.scaledMagic, scaleEquiv, SchwartzMap.fourier_coe] using
    SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv (A := scaleEquiv) (f := g) (w := x)

/-- The Fourier transform `𝓕 scaledMagic` is real-valued (scaled variant of `g_real_fourier`). -/
public theorem scaledMagic_real_fourier' :
    ∀ x : ℝ⁸, (↑((𝓕 scaledMagic x).re : ℂ)) = (𝓕 scaledMagic x) := by
  intro x
  let y0 : ℝ⁸ := (LinearMap.adjoint ((scaleEquiv.symm : ℝ⁸ ≃ₗ[ℝ] ℝ⁸) : ℝ⁸ →ₗ[ℝ] ℝ⁸)) x
  have hImG : (𝓕 g y0).im = 0 := by
    simpa using (congrArg Complex.im (g_real_fourier (x := y0))).symm
  have hImScaled : (𝓕 scaledMagic x).im = 0 := by
    simpa [y0, Complex.smul_im, hImG] using congrArg Complex.im (fourier_scaledMagic_eq (x := x))
  exact Complex.ext (by simp) (by simp [hImScaled])

/-- Cohn-Elkies sign condition for `scaledMagic` outside the unit ball (scaled variant). -/
public theorem scaledMagic_cohnElkies₁' : ∀ x : ℝ⁸, ‖x‖ ≥ 1 → (scaledMagic x).re ≤ 0 := by
  intro x hx
  have h2 : (2 : ℝ) ≤ ‖(Real.sqrt 2) • x‖ ^ (2 : ℕ) := by
    rw [norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
    nlinarith [mul_le_mul hx hx (by positivity) (norm_nonneg x), sq_nonneg ‖x‖]
  simpa [SpherePacking.scaledMagic] using
    g_nonpos_of_norm_sq_ge_two (x := (Real.sqrt 2) • x) h2

/-- Cohn-Elkies nonnegativity for `𝓕 scaledMagic` (scaled variant). -/
public theorem scaledMagic_cohnElkies₂' : ∀ x : ℝ⁸, (𝓕 scaledMagic x).re ≥ 0 := by
  intro x
  let y0 : ℝ⁸ := (LinearMap.adjoint ((scaleEquiv.symm : ℝ⁸ ≃ₗ[ℝ] ℝ⁸) : ℝ⁸ →ₗ[ℝ] ℝ⁸)) x
  have hre : (𝓕 scaledMagic x).re =
      |LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹ • (𝓕 g y0).re := by
    have hre' : (𝓕 scaledMagic x).re =
        (|LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹ • 𝓕 g y0).re := by
      simpa [y0] using congrArg Complex.re (fourier_scaledMagic_eq (x := x))
    exact hre'.trans (by
      simpa using
        Complex.smul_re (r := |LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹) (z := 𝓕 g y0))
  simpa [hre] using
    smul_nonneg (inv_nonneg.2 (abs_nonneg (LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸))))
      (by simpa using fourier_g_nonneg (x := y0))

/-- Upper bound on `SpherePackingConstant 8` given by the density of the `E8` lattice packing. -/
public theorem SpherePackingConstant_le_E8Packing_density :
    SpherePackingConstant 8 ≤ E8Packing.density := by
  have hne : (scaledMagic : 𝓢(ℝ⁸, ℂ)) ≠ 0 := fun h => by
    simpa [scaledMagic_zero] using congrArg (fun f : 𝓢(ℝ⁸, ℂ) => f 0) h
  have hLP :
      SpherePackingConstant 8 ≤ (scaledMagic 0).re.toNNReal / (𝓕 (⇑scaledMagic) 0).re.toNNReal *
        volume (ball (0 : ℝ⁸) (1 / 2 : ℝ)) := by
    simpa using
      (LinearProgrammingBound (d := 8) (f := (scaledMagic : 𝓢(ℝ⁸, ℂ))) hne
        scaledMagic_real' scaledMagic_real_fourier' scaledMagic_cohnElkies₁'
        scaledMagic_cohnElkies₂' (Nat.succ_pos 7))
  have hratio : (scaledMagic 0).re.toNNReal / (𝓕 (⇑scaledMagic) 0).re.toNNReal = (16 : ℝ≥0∞) := by
    simp [ENNReal.ofNNReal_toNNReal, scaledMagic_zero, fourier_scaledMagic_zero_fun]
  calc
    SpherePackingConstant 8 ≤ (16 : ℝ≥0∞) * volume (ball (0 : ℝ⁸) (1 / 2 : ℝ)) := by
      simpa [mul_assoc, hratio] using hLP
    _ = ENNReal.ofReal π ^ 4 / 384 := by
      calc (16 : ℝ≥0∞) * volume (ball (0 : ℝ⁸) (1 / 2 : ℝ))
          = (16 : ℝ≥0∞) *
            (ENNReal.ofReal (1 / 2 : ℝ) ^ 8 * ENNReal.ofReal (π ^ 4 / 24)) := by
            simp [InnerProductSpace.volume_ball_of_dim_even (E := ℝ⁸) (k := 4) (hk := by simp),
              finrank_euclideanSpace, Nat.factorial]
        _ = ENNReal.ofReal ((16 : ℝ) * (((1 / 2 : ℝ) ^ 8) * (π ^ 4 / 24))) := by
            have hinv : (2⁻¹ : ℝ≥0∞) ^ 8 = (2 ^ 8 : ℝ≥0∞)⁻¹ := by
              simpa using (ENNReal.inv_pow (a := (2 : ℝ≥0∞)) (n := 8)).symm
            simp [mul_left_comm, ENNReal.ofReal_mul, (by norm_num : (0 : ℝ) ≤ (16 : ℝ)), hinv]
        _ = ENNReal.ofReal (π ^ 4 / 384 : ℝ) := by congr 1; ring
        _ = ENNReal.ofReal π ^ 4 / 384 := by
            simp [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 384),
              ENNReal.ofReal_pow Real.pi_pos.le]
    _ = E8Packing.density := by simpa using E8Packing_density.symm

open SpherePacking E8

/-- Main theorem (dimension 8): the optimal packing density equals `E8Packing.density`. -/
public theorem MainTheorem : SpherePackingConstant 8 = E8Packing.density :=
  le_antisymm SpherePackingConstant_le_E8Packing_density <| by
    simpa [SpherePackingConstant] using
      le_iSup (fun S : SpherePacking 8 => S.density) E8Packing.toSpherePacking

end SpherePacking
