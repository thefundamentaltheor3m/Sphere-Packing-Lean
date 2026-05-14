module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.StripBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import SpherePacking.MagicFunction.a.Schwartz.Basic
import SpherePacking.Integration.Measure
public import
  SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.Integrability
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.APrimeExtension
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
import Mathlib.Tactic


/-!
# Laplace-type integrals and analytic continuation for `AnotherIntegral.A`

Explicit evaluations and integrability facts for basic Laplace-type integrals on `t > 0`,
in the complex-valued form used by the "another integral" representation of `a'`. Also includes
the analytic-continuation step that extends the "another integral" identity for `a'` from `u > 2`
to all real `0 < u` with `u ≠ 2`.

This file also provides the generic analytic-continuation wrapper used by both the `a'` and `b'`
representations: the punctured right half-plane `ACDomain = {u : ℂ | 0 < re u} \ {2}` and the
theorem `analytic_continuation_of_gt2`.

Also contains the Laplace representation for `a'` (merged from `LaplaceA/LaplaceRepresentation`):
the tail-deformation lemma `I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail` and the main theorem
`aRadial_eq_laplace_phi0_main`.

## Main definitions
* `ACDomain`, `aAnotherBase`, `aAnotherIntegrandC`, `aAnotherIntegralC`, `aAnotherRHS`

## Main statements
* `analytic_continuation_of_gt2`
* `aRadial_eq_another_integral_analytic_continuation_of_gt2`
* `I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail`, `aRadial_eq_laplace_phi0_main`
-/

namespace MagicFunction.g.CohnElkies

/--
For `u ≥ 0`, the radial profile `a'` from `MagicFunction.FourierEigenfunctions` agrees with the
real-integral definition `MagicFunction.a.RealIntegrals.a'`.

The prime `'` is part of the standard notation for this radial profile (it is not a derivative).
-/
public lemma a'_eq_realIntegrals_a' {u : ℝ} (hu : 0 ≤ u) :
    (MagicFunction.FourierEigenfunctions.a' : ℝ → ℂ) u = MagicFunction.a.RealIntegrals.a' u := by
  simp [MagicFunction.FourierEigenfunctions.a', MagicFunction.a.RealIntegrals.a',
    MagicFunction.a.SchwartzIntegrals.I₁'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₂'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₃'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₄'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₅'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₆'_apply_of_nonneg, hu]

end MagicFunction.g.CohnElkies

namespace MagicFunction.g.CohnElkies.IntegralReps

section LaplaceRepresentation

open scoped BigOperators UpperHalfPlane Topology intervalIntegral
open MeasureTheory Real Complex Filter
open UpperHalfPlane
open MagicFunction.FourierEigenfunctions
open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrals MagicFunction.a.RealIntegrands
  MagicFunction.Parametrisations

local notation "c12π" => ‖(12 * (Complex.I : ℂ)) / (π : ℂ)‖
local notation "c36π2" => ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖

/-! ## Tail deformation -/

/-- Strip-bound core: bound `‖F (x + tI)‖` by the standard envelope when
`F (x + tI) = (φ₀''(-1/w) * w²) * exp(πIu(x + tI))` with `w = s + tI`, `|s| ≤ 1`. -/
private lemma norm_strip_le_of_hdef {u s t x : ℝ} {F : ℂ → ℂ} {Cφ Aφ C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
      ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (hs : |s| ≤ (1 : ℝ)) (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t)
    (hdef : F ((x : ℂ) + (t : ℂ) * Complex.I) =
      (φ₀'' ((-1 : ℂ) / (((s : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
        ((((s : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ (2 : ℕ))) *
          cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I))) :
    ‖F ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
  set K : ℝ := 4 * C₀ + (2 * c12π + c36π2) * Cφ
  let wH : ℍ := ⟨((s : ℝ) : ℂ) + (t : ℂ) * Complex.I, by simpa using by linarith⟩
  have hw_im : (wH : ℂ).im = t := by simp [wH]
  calc ‖F ((x : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ * Real.exp (-π * u * t) := by
          rw [hdef, show φ₀'' ((-1 : ℂ) / (wH : ℂ)) * ((wH : ℂ) ^ 2) =
              φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ)) by
            rw [show φ₀ (ModularGroup.S • wH) = φ₀'' ((ModularGroup.S • wH : ℍ) : ℂ) by simp,
              show ((ModularGroup.S • wH : ℍ) : ℂ) = (-1 : ℂ) / (wH : ℂ) by
                simpa using ModularGroup.coe_S_smul (z := wH)], norm_mul,
            show ‖cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I))‖ =
                Real.exp (-π * u * t) by
              rw [show ((π : ℂ) * Complex.I * (u : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I)) =
                  ((π * u * x : ℝ) : ℂ) * Complex.I - ((π * u * t : ℝ) : ℂ) by
                push_cast; ring_nf; simp [mul_left_comm, mul_comm, sub_eq_add_neg],
                Complex.norm_exp]
              simp [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]]
    _ ≤ (K * (t ^ (2 : ℕ) * Real.exp (2 * π * t))) * Real.exp (-π * u * t) :=
          mul_le_mul_of_nonneg_right (norm_phi0S_mul_sq_le wH hw_im hC₀_pos hC₀ hφbd ht1 htAφ <| by
            simp only [wH]
            linarith [norm_add_le ((s : ℝ) : ℂ) ((t : ℂ) * Complex.I),
              (by simpa [Complex.norm_real] using hs : ‖((s : ℝ) : ℂ)‖ ≤ (1 : ℝ)),
              (by simp [abs_of_nonneg (by linarith : (0:ℝ) ≤ t)] :
                ‖(t : ℂ) * Complex.I‖ = t)]) (Real.exp_pos _).le
    _ = K * (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
          rw [mul_assoc, mul_assoc, ← MagicFunction.g.CohnElkies.exp_two_pi_mul_mul_exp_neg_pi_mul]

/-- Top-edge decay: reduce `tendsto` of an interval integral to a pointwise strip bound. -/
private lemma tendsto_intervalIntegral_top_of_strip_bound {u : ℝ} (hu : 2 < u) {F : ℂ → ℂ}
    {x₁ x₂ : ℝ} (hlen : |x₂ - x₁| ≤ 1)
    (hF : ∀ Cφ Aφ C₀ x t : ℝ, 0 < C₀ →
      (∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im)) →
      (∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
        ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im)) →
      x ∈ Set.uIoc x₁ x₂ → (1 : ℝ) ≤ t → Aφ ≤ t →
      ‖F ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
          (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t))) :
    Tendsto (fun m : ℝ => ∫ x in x₁..x₂, F ((x : ℂ) + (m : ℂ) * Complex.I)) atTop (𝓝 0) := by
  obtain ⟨Cφ, Aφ, _, hφbd⟩ := exists_phi2'_phi4'_bound_exp
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  set K : ℝ := 4 * C₀ + (2 * c12π + c36π2) * Cφ
  set a : ℝ := π * (u - 2)
  have ha : 0 < a := mul_pos Real.pi_pos (sub_pos.2 hu)
  refine squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨max 1 Aφ, fun m hm => ?_⟩) (by
    simpa [mul_zero] using tendsto_const_nhds.mul
      (by simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (2 : ℝ)) (b := a) ha :
        Tendsto (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t)) atTop (𝓝 0)) :
      Tendsto (fun m : ℝ => K * (m ^ (2 : ℕ) * Real.exp (-a * m))) atTop (𝓝 0))
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (a := x₁) (b := x₂)
    (C := K * (m ^ (2 : ℕ) * Real.exp (-a * m)))
    (fun x hx => hF Cφ Aφ C₀ x m hC₀_pos hC₀ hφbd hx ((le_max_left _ _).trans hm)
      ((le_max_right _ _).trans hm))).trans ?_
  nlinarith [hlen, show 0 ≤ K * (m ^ (2 : ℕ) * Real.exp (-a * m)) by positivity]

private lemma tendsto_intervalIntegral_Φ₂'_top {u : ℝ} (hu : 2 < u) :
    Tendsto (fun m : ℝ => ∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + (m : ℂ) * Complex.I))
      atTop (𝓝 0) :=
  tendsto_intervalIntegral_top_of_strip_bound hu (x₁ := -1) (x₂ := 0) (by norm_num)
    fun _ _ _ x t h1 h2 h3 hx h4 h5 =>
      have hx' : x ∈ Set.Ioc (-1 : ℝ) 0 := Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 0) ▸ hx
      norm_strip_le_of_hdef (s := x + 1) (F := Φ₂' u) h1 h2 h3
        (by rw [abs_of_nonneg (by linarith [hx'.1.le] : (0:ℝ) ≤ x + 1)]; linarith [hx'.2])
        h4 h5 <| by
        simp [MagicFunction.a.ComplexIntegrands.Φ₂', MagicFunction.a.ComplexIntegrands.Φ₁',
          show (x : ℂ) + (t : ℂ) * Complex.I + 1 = ((x + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I by
            push_cast; ring, mul_assoc]

private lemma tendsto_intervalIntegral_Φ₄'_top {u : ℝ} (hu : 2 < u) :
    Tendsto (fun m : ℝ => ∫ x in (1 : ℝ)..0, Φ₄' u ((x : ℂ) + (m : ℂ) * Complex.I))
      atTop (𝓝 0) :=
  tendsto_intervalIntegral_top_of_strip_bound hu (x₁ := 1) (x₂ := 0) (by norm_num)
    fun _ _ _ x t h1 h2 h3 hx h4 h5 =>
      have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := Set.uIoc_of_ge (by norm_num : (0:ℝ) ≤ 1) ▸ hx
      norm_strip_le_of_hdef (s := x - 1) (F := Φ₄' u) h1 h2 h3
        (by rw [abs_sub_comm, abs_of_nonneg (by linarith [hx'.2] : (0:ℝ) ≤ 1 - x)]
            linarith [hx'.1.le]) h4 h5 <| by
        simp [MagicFunction.a.ComplexIntegrands.Φ₄', MagicFunction.a.ComplexIntegrands.Φ₃',
          show (x : ℂ) + (t : ℂ) * Complex.I - 1 = ((x - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I by
            push_cast; ring, mul_assoc]

private lemma bottom_eq_I_smul_sub_of_rect_deform {f : ℂ → ℂ} {x₁ x₂ : ℝ}
    (hcontU : ContinuousOn f {z : ℂ | 0 < z.im})
    (hdiffU : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hint₁ : IntegrableOn (fun t : ℝ => f ((x₁ : ℂ) + (t : ℂ) * Complex.I))
      (Set.Ioi (1 : ℝ)) volume)
    (hint₂ : IntegrableOn (fun t : ℝ => f ((x₂ : ℂ) + (t : ℂ) * Complex.I))
      (Set.Ioi (1 : ℝ)) volume)
    (htop : Tendsto (fun m : ℝ => ∫ x in x₁..x₂, f ((x : ℂ) + (m : ℂ) * Complex.I))
      atTop (𝓝 0)) :
    (∫ x in x₁..x₂, f ((x : ℂ) + Complex.I)) =
      (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), f ((x₁ : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), f ((x₂ : ℂ) + (t : ℂ) * Complex.I)) := by
  simpa [smul_eq_mul, mul_sub, one_mul] using eq_sub_of_add_eq (by
    simpa [one_mul] using sub_eq_zero.mp <| Complex.rect_deform_of_tendsto_top (f := f)
      (x₁ := x₁) (x₂ := x₂) (y := (1 : ℝ))
      (hcontU.mono fun z hz => show 0 < z.im from lt_of_lt_of_le zero_lt_one
        (by simpa [mem_reProdIm] using hz : _ ∧ z.im ∈ Set.Ici (1 : ℝ)).2)
      (fun z hz =>
        have hz0 : 0 < z.im :=
          lt_trans zero_lt_one (by simpa [mem_reProdIm] using hz : _ ∧ z.im ∈ Set.Ioi (1 : ℝ)).2
        (hdiffU z hz0).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hz0))
      hint₁ hint₂ htop)

lemma I₂'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    I₂' u = (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((t : ℂ) * Complex.I)) := by
  let g : ℝ → ℂ := fun x : ℝ => Φ₂' u ((x : ℂ) + Complex.I)
  have hΦ₁' := Φ₁'_contDiffOn_ℂ (r := u)
  rw [show I₂' u = ∫ x in (-1 : ℝ)..0, g x by
    dsimp [I₂', Φ₂]
    rw [show (∫ t in (0 : ℝ)..1, Φ₂' u (z₂' t)) =
        ∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ)) from intervalIntegral.integral_congr fun t ht => by
          simp [g, show z₂' t = (-1 : ℂ) + (t : ℂ) + (Complex.I : ℂ) by
            simpa using z₂'_eq_of_mem (by simpa [Set.uIcc_of_le zero_le_one] using ht), add_comm],
      show (∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ))) = ∫ x in (-1 : ℝ)..0, g x by norm_num]]
  simpa [zero_add] using bottom_eq_I_smul_sub_of_rect_deform (f := Φ₂' u)
    (x₁ := (-1 : ℝ)) (x₂ := (0 : ℝ)) hΦ₁'.continuousOn (hΦ₁'.differentiableOn (by simp))
    (by simpa [show (fun t : ℝ => Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) =
        fun t : ℝ => Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) * Φ₅' u ((t : ℂ) * Complex.I)
        from funext fun t => Φ₁'_shift_left (u := u) (t := t)]
      using (integrableOn_Φ₅'_imag_axis hu).const_mul _)
    (by simpa using integrableOn_Φ₂'_imag_axis hu) (tendsto_intervalIntegral_Φ₂'_top hu)

lemma I₄'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    I₄' u = (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((t : ℂ) * Complex.I)) := by
  let g : ℝ → ℂ := fun x : ℝ => Φ₄' u ((x : ℂ) + Complex.I)
  have hΦ₃' := Φ₃'_contDiffOn_ℂ (r := u)
  rw [show I₄' u = ∫ x in (1 : ℝ)..0, g x by
    dsimp [I₄', Φ₄]
    rw [show (∫ t in (0 : ℝ)..1, (-1 : ℂ) * Φ₄' u (z₄' t)) =
        ∫ t in (0 : ℝ)..1, (-1 : ℂ) * g (1 - t) from
      intervalIntegral.integral_congr fun t ht => by
        simp [g, sub_eq_add_neg, show z₄' t = (1 : ℂ) - (t : ℂ) + (Complex.I : ℂ) by
          simpa using z₄'_eq_of_mem (t := t) (by simpa [Set.uIcc_of_le zero_le_one] using ht)],
      intervalIntegral.integral_const_mul,
      show (∫ t in (0 : ℝ)..1, g (1 - t)) = ∫ t in (0 : ℝ)..1, g t by norm_num]
    simpa using (intervalIntegral.integral_symm (a := (0 : ℝ)) (b := (1 : ℝ)) (f := g)).symm]
  simpa [zero_add] using bottom_eq_I_smul_sub_of_rect_deform (f := Φ₄' u)
    (x₁ := (1 : ℝ)) (x₂ := (0 : ℝ)) hΦ₃'.continuousOn (hΦ₃'.differentiableOn (by simp))
    (by simpa [show (fun t : ℝ => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) =
        fun t : ℝ => Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) * Φ₅' u ((t : ℂ) * Complex.I)
        from funext fun t => Φ₃'_shift_right (u := u) (t := t)]
      using (integrableOn_Φ₅'_imag_axis hu).const_mul _)
    (by simpa using integrableOn_Φ₄'_imag_axis hu) (tendsto_intervalIntegral_Φ₄'_top hu)

lemma I₆'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    I₆' u = (Complex.I : ℂ) *
        ((∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((t : ℂ) * Complex.I)) -
            2 * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) +
              ∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((t : ℂ) * Complex.I)) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  let f2 : ℝ → ℂ := fun t => Φ₂' u ((t : ℂ) * Complex.I)
  let f5 : ℝ → ℂ := fun t => Φ₅' u ((t : ℂ) * Complex.I)
  let f4 : ℝ → ℂ := fun t => Φ₄' u ((t : ℂ) * Complex.I)
  have hf2 : Integrable f2 μ := integrableOn_Φ₂'_imag_axis hu
  have hf5 : Integrable f5 μ := integrableOn_Φ₅'_imag_axis hu
  have hf4 : Integrable f4 μ := integrableOn_Φ₄'_imag_axis hu
  dsimp [I₆', Φ₆]
  rw [show (∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * Φ₆' u (z₆' t))
        = ∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I) from
      setIntegral_congr_fun measurableSet_Ici fun t ht => by
        simp [show z₆' t = (Complex.I : ℂ) * (t : ℂ) by
          simpa [mul_assoc, mul_comm, mul_left_comm] using z₆'_eq_of_mem ht, mul_comm],
    integral_Ici_eq_integral_Ioi,
    (integral_const_mul (μ := μ) (r := (2 : ℂ))
      (f := fun t : ℝ => (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I))).symm,
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
      simpa [f2, f5, f4, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]
        using (congrArg (fun z : ℂ => (Complex.I : ℂ) * z)
        (Φ_finite_difference_imag_axis (lt_trans zero_lt_one ht))).symm :
      ∀ t ∈ Set.Ioi (1 : ℝ), (2 : ℂ) * ((Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I)) =
        (Complex.I : ℂ) * (f2 t - 2 * f5 t + f4 t)),
    integral_const_mul (μ := μ) (r := (Complex.I : ℂ)) (f := fun t => f2 t - 2 * f5 t + f4 t)]
  calc (Complex.I : ℂ) * (∫ t, (f2 t - 2 * f5 t + f4 t) ∂μ)
      = (Complex.I : ℂ) * ((∫ t, f2 t - 2 * f5 t ∂μ) + ∫ t, f4 t ∂μ) := by
        simpa using congrArg ((Complex.I : ℂ) * ·)
          (integral_add (μ := μ) (hf2.sub (hf5.const_mul 2)) hf4)
    _ = (Complex.I : ℂ) * ((∫ t, f2 t ∂μ) - 2 * (∫ t, f5 t ∂μ) + ∫ t, f4 t ∂μ) := by
        rw [integral_sub (μ := μ) hf2 (hf5.const_mul 2),
          integral_const_mul (μ := μ) (r := (2 : ℂ)) (f := f5)]

/-- If `G t = E * Φ₅' u (tI)` for `t > 1`, then `∫ G = E * ∫ central` over `Ioi 1`. -/
private lemma ray_integral_eq_const_mul_central {u : ℝ} {G : ℝ → ℂ} {E : ℂ}
    (hG : ∀ t, 1 < t → G t = E * Φ₅' u ((t : ℂ) * Complex.I)) :
    (∫ t in Set.Ioi (1 : ℝ), G t) = E * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) := by
  rw [setIntegral_congr_fun measurableSet_Ioi hG, integral_const_mul]

/-- Rewrite `I₂' + I₄' + I₆'` as an imaginary-axis integral of `Φ₅'` over `t ≥ 1`. -/
public lemma I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail {u : ℝ} (hu : 2 < u) :
    I₂' u + I₄' u + I₆' u =
      (Complex.I : ℂ) *
        ((Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) +
              Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) *
          (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) := by
  rw [I₂'_eq_deform_imag_axis hu, I₄'_eq_deform_imag_axis hu, I₆'_eq_deform_imag_axis hu,
    ray_integral_eq_const_mul_central (G := fun t => Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I))
      (E := Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)))
      (fun t _ => by simpa [mul_assoc] using Φ₁'_shift_left (u := u) (t := t)),
    ray_integral_eq_const_mul_central (G := fun t => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I))
      (E := Complex.exp (((π * u : ℝ) : ℂ) * Complex.I))
      (fun t _ => by simpa [mul_assoc] using Φ₃'_shift_right (u := u) (t := t))]
  simp [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm]; ring

/-! ## Main Laplace representation -/

/-- Main lemma for blueprint proposition `prop:a-double-zeros`. -/
public theorem aRadial_eq_laplace_phi0_main {u : ℝ} (hu : 2 < u) :
    MagicFunction.FourierEigenfunctions.a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ),
            ((t ^ (2 : ℕ) : ℝ) : ℂ) *
              φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
                Real.exp (-π * u * t)) := by
  have hu0 : 0 ≤ u := (lt_trans (by norm_num : (0 : ℝ) < 2) hu).le
  have ha : MagicFunction.FourierEigenfunctions.a' u = MagicFunction.a.RealIntegrals.a' u := by
    simpa using (MagicFunction.g.CohnElkies.a'_eq_realIntegrals_a' (u := u) hu0)
  rw [ha]
  dsimp [MagicFunction.a.RealIntegrals.a']
  have hsplit :
      MagicFunction.a.RealIntegrals.I₁' u + MagicFunction.a.RealIntegrals.I₂' u +
            MagicFunction.a.RealIntegrals.I₃' u + MagicFunction.a.RealIntegrals.I₄' u +
              MagicFunction.a.RealIntegrals.I₅' u + MagicFunction.a.RealIntegrals.I₆' u =
          (MagicFunction.a.RealIntegrals.I₁' u + MagicFunction.a.RealIntegrals.I₃' u +
              MagicFunction.a.RealIntegrals.I₅' u) +
            (MagicFunction.a.RealIntegrals.I₂' u + MagicFunction.a.RealIntegrals.I₄' u +
              MagicFunction.a.RealIntegrals.I₆' u) := by ring
  rw [hsplit, I₁'_add_I₃'_add_I₅'_eq_imag_axis (u := u),
    I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail (u := u) hu]
  have hseg : (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)) =
      ∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I) := by
    simp [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  rw [hseg]
  have hIoi :
      (∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I)) +
          (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) =
        ∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I) := by
    have h5Ioi0 : IntegrableOn (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (Set.Ioi (0 : ℝ)) volume :=
      by simpa [IntegrableOn, Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand] using
        (aLaplaceIntegral_convergent hu).neg'
    have h5Ioc := h5Ioi0.mono_set (fun t (ht : t ∈ Set.Ioc (0 : ℝ) 1) => ht.1)
    rw [show (Set.Ioi (0 : ℝ)) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) by
      simp [Set.Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one]]
    simpa [add_comm, add_left_comm, add_assoc] using
      (MeasureTheory.setIntegral_union (μ := volume)
        (f := fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I))
        (s := Set.Ioc (0 : ℝ) 1) (t := Set.Ioi (1 : ℝ))
        (hst := Set.Ioc_disjoint_Ioi_same)
        (ht := measurableSet_Ioi) h5Ioc (integrableOn_Φ₅'_imag_axis (u := u) hu)).symm
  set coeff : ℂ :=
    (Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) +
        Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ))
  have hcomb :
      (Complex.I : ℂ) * (coeff * (∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I))) +
          (Complex.I : ℂ) * (coeff * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) =
        (Complex.I : ℂ) * (coeff * (∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) := by
    rw [← hIoi]; ring
  rw [hcomb]
  have hcoeff : coeff = -((4 * (Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
    have hrew : coeff = -((2 : ℂ) - Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) -
        Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I))) := by simp [coeff]; ring
    have htrig := MagicFunction.g.CohnElkies.Trig.two_sub_exp_pi_mul_I_sub_exp_neg_pi_mul_I u
    have hhalf := MagicFunction.g.CohnElkies.Trig.two_sub_two_cos_eq_four_sin_sq u
    grind only
  have hΦ5 : (∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) =
      - (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) := by
    rw [MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
      (g := fun t => -aLaplaceIntegrand u t)
      (fun t _ => by simpa using (Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand (u := u) (t := t)))]
    simp [integral_neg]
  rw [hcoeff, hΦ5]
  simp [aLaplaceIntegrand, mul_assoc, mul_left_comm, mul_comm]

end LaplaceRepresentation

open scoped BigOperators Topology UpperHalfPlane

open MeasureTheory Real Complex UpperHalfPlane Filter
open SpherePacking
open SpherePacking.Integration (μIoi0)
open MagicFunction.FourierEigenfunctions

/-- The analytic continuation domain `U = {u : ℂ | 0 < re u} \ {2}`. -/
@[expose] public def ACDomain : Set ℂ := rightHalfPlane \ {2}

/-- The analytic continuation domain `ACDomain` is preconnected. -/
public lemma ACDomain_isPreconnected : IsPreconnected ACDomain := by
  -- We use a homeomorphism `ℂ ≃ₜ {u : ℂ // 0 < u.re}` to reduce to connectedness of the
  -- complement of a singleton in `ℂ`.
  let z2 : {u : ℂ // 0 < u.re} := ⟨(2 : ℂ), by simp⟩
  let h₃ : (Set.Ioi (0 : ℝ) × ℝ) ≃ₜ {u : ℂ // 0 < u.re} :=
    { toEquiv :=
        { toFun := fun p =>
            ⟨(p.1 : ℝ) + p.2 * Complex.I, by
              have hp : (0 : ℝ) < (p.1 : ℝ) := p.1.2
              simpa using hp⟩
          invFun := fun z => (⟨z.1.re, z.2⟩, z.1.im)
          left_inv := by
            rintro ⟨x, y⟩
            ext <;> simp
          right_inv := by
            rintro ⟨z, hz⟩
            apply Subtype.ext
            simp [Complex.re_add_im] }
      continuous_toFun := by
        refine
            (show Continuous (fun p : Set.Ioi (0 : ℝ) × ℝ => (p.1 : ℝ) + p.2 * Complex.I) by
              fun_prop).subtype_mk fun p => by
            have hp : (0 : ℝ) < (p.1 : ℝ) := p.1.2
            simpa using hp
      continuous_invFun := by
        fun_prop }
  let h : ℂ ≃ₜ {u : ℂ // 0 < u.re} :=
    (Complex.equivRealProdCLM.toHomeomorph.trans
          ((Real.expOrderIso.toHomeomorph).prodCongr (Homeomorph.refl ℝ))).trans h₃
  have hpre : IsPreconnected ({z2}ᶜ : Set {u : ℂ // 0 < u.re}) := by
    have hconn : IsConnected ({h.symm z2}ᶜ : Set ℂ) :=
      isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) (h.symm z2)
    have himage :
        h '' ({h.symm z2}ᶜ : Set ℂ) = ({z2}ᶜ : Set {u : ℂ // 0 < u.re}) := by
      ext z
      refine ⟨?_, fun hz => ⟨h.symm z, by simpa, by simp⟩⟩
      rintro ⟨x, hx, rfl⟩
      have hx' : x ≠ h.symm z2 := by simpa using hx
      simpa using fun hz => hx' (by simpa using congrArg h.symm hz)
    simpa [himage] using hconn.isPreconnected.image h h.continuous.continuousOn
  have hval :
      ((Subtype.val : {u : ℂ // 0 < u.re} → ℂ) '' ({z2}ᶜ :
          Set {u : ℂ // 0 < u.re})) = ACDomain := by
    ext u
    refine ⟨?_, ?_⟩
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ≠ z2 := by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
      exact ⟨z.2, by simpa using fun hEq => hz' (Subtype.ext hEq)⟩
    · rintro hu
      have hu_re : 0 < u.re := by simpa [rightHalfPlane] using hu.1
      refine ⟨⟨u, hu_re⟩, ?_, rfl⟩
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using fun hEq =>
        (by simpa using hu.2 : u ≠ (2 : ℂ)) (congrArg Subtype.val hEq)
  simpa [hval] using
    hpre.image (Subtype.val : {u : ℂ // 0 < u.re} → ℂ) continuous_subtype_val.continuousOn

/-- Generic analytic continuation on `ACDomain = {Re u > 0} \ {2}`. -/
public theorem analytic_continuation_of_gt2
    {value : ℝ → ℂ} {rhsC : ℂ → ℂ} {rhsR : ℝ → ℂ}
    (h_extension : ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f ACDomain ∧
      ∀ u : ℝ, 0 < u → u ≠ 2 → f (u : ℂ) = value u)
    (h_rhs_analytic : AnalyticOnNhd ℂ rhsC ACDomain)
    (h_rhs_ofReal : ∀ u : ℝ, rhsC (u : ℂ) = rhsR u)
    (h_gt2 : ∀ r : ℝ, 2 < r → value r = rhsR r)
    {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    value u = rhsR u := by
  rcases h_extension with ⟨f, hf_analytic, hf_ofReal⟩
  have hf_gt2 : ∀ r : ℝ, 2 < r → f (r : ℂ) = rhsC (r : ℂ) := fun r hr =>
    (hf_ofReal r (lt_trans (by norm_num) hr) (by linarith)).trans
      ((h_gt2 r hr).trans (h_rhs_ofReal r).symm)
  have hFreq : (∃ᶠ z in 𝓝[≠] (3 : ℂ), f z = rhsC z) := Filter.frequently_iff.2 <| by
    intro U hU
    obtain ⟨V, hVnhds, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hU
    obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.1 hVnhds
    refine ⟨((3 + ε / 2 : ℝ) : ℂ), hVsub ⟨hball ?_, ?_⟩, by
      simpa using hf_gt2 (3 + ε / 2) (by nlinarith [hεpos])⟩
    · simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε / 2),
        abs_of_nonneg hεpos.le] using half_lt_self hεpos
    · simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (show ((3 + ε / 2 : ℝ) : ℂ) ≠ 3 by exact_mod_cast
          (by nlinarith [hεpos.ne'] : (3 + ε / 2 : ℝ) ≠ 3))
  have hEqOn : Set.EqOn f rhsC ACDomain :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf_analytic h_rhs_analytic
      ACDomain_isPreconnected (by simp [ACDomain, rightHalfPlane]) hFreq
  have hu_mem : (u : ℂ) ∈ ACDomain :=
    ⟨by simpa [rightHalfPlane] using hu,
      by simpa [ACDomain, Set.mem_singleton_iff] using (show (u : ℂ) ≠ 2 by exact_mod_cast hu2)⟩
  exact (hf_ofReal u hu hu2).symm.trans ((hEqOn hu_mem).trans (h_rhs_ofReal u))

/-- If `inner` is analytic on `ACDomain`, then so is
`u ↦ sign * (sin (π u / 2))^2 * inner u` for any constant `sign : ℂ`. -/
public lemma analyticOnNhd_sinSq_prefactor_mul
    (sign : ℂ) {inner : ℂ → ℂ} (hinner : AnalyticOnNhd ℂ inner ACDomain) :
    AnalyticOnNhd ℂ
      (fun u : ℂ => sign * (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) * inner u) ACDomain :=
  (analyticOnNhd_const.mul (by
    have hsin : AnalyticOnNhd ℂ (fun u : ℂ => Complex.sin ((π : ℂ) * u / 2)) ACDomain := by
      simpa [Function.comp] using ((by simpa using (analyticOnNhd_sin (s := (Set.univ : Set ℂ)))) :
          AnalyticOnNhd ℂ (fun z : ℂ => Complex.sin z) (Set.univ : Set ℂ)).comp
        (AnalyticOnNhd.div_const (analyticOnNhd_const.mul analyticOnNhd_id) :
          AnalyticOnNhd ℂ (fun u : ℂ => (π : ℂ) * u / 2) ACDomain) (by intro _ _; simp)
    exact hsin.pow 2)).mul hinner

noncomputable section

/-- The `u`-independent bracket in the "another integral" integrand for `a'`. -/
@[expose] public def aAnotherBase (t : ℝ) : ℂ :=
  (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
    ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
    ((8640 / π : ℝ) : ℂ) * t - ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))

/-- Complex-parameter integrand for the "another integral" representation of `a'`. -/
@[expose] public def aAnotherIntegrandC (u : ℂ) (t : ℝ) : ℂ :=
  aAnotherBase t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

/-- Complex-parameter "another integral" for `a'`. -/
@[expose] public def aAnotherIntegralC (u : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrandC u t

private lemma norm_exp_le_of_re_ge {z : ℂ} {t c : ℝ} (ht0 : 0 ≤ t) (hcz : c ≤ z.re) :
    ‖Complex.exp (-(π : ℂ) * z * (t : ℂ))‖ ≤ Real.exp (-π * c * t) := by
  simpa [Complex.norm_exp, show (-(π : ℂ) * z * (t : ℂ)).re = -π * z.re * t by
    simp [mul_assoc, Complex.mul_re, sub_eq_add_neg, add_comm]] using
    Real.exp_le_exp.mpr <| by simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonpos_left hcz (by nlinarith [Real.pi_pos, ht0] : (-π * t : ℝ) ≤ 0)

/-- Analyticity of `u ↦ ∫ t ∈ (0, ∞), base(t) * Complex.exp(-π u t)` on the right half-plane. -/
public theorem analyticOnNhd_integral_base_exp
    {base : ℝ → ℂ}
    (hbase_cont : ContinuousOn base (Set.Ioi (0 : ℝ)))
    (hbase_int : ∀ u : ℝ, 0 < u →
      IntegrableOn (fun t : ℝ => base t * (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ))) :
    AnalyticOnNhd ℂ
      (fun u : ℂ => ∫ t in Set.Ioi (0 : ℝ), base t * Complex.exp (-(π : ℂ) * u * (t : ℂ)))
      rightHalfPlane := by
  have hDiff :
      DifferentiableOn ℂ
        (fun u : ℂ => ∫ t in Set.Ioi (0 : ℝ), base t * Complex.exp (-(π : ℂ) * u * (t : ℂ)))
        rightHalfPlane := by
    intro u hu
    have hu0 : 0 < u.re := by simpa [rightHalfPlane] using hu
    set ε : ℝ := u.re / 2
    have hε : 0 < ε := by positivity
    let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
    let F : ℂ → ℝ → ℂ := fun z t => base t * Complex.exp (-(π : ℂ) * z * (t : ℂ))
    let F' : ℂ → ℝ → ℂ := fun z t => (-(π : ℂ) * (t : ℂ)) * F z t
    have hF_meas : ∀ z : ℂ, AEStronglyMeasurable (F z) μ := fun z =>
      (hbase_cont.aestronglyMeasurable measurableSet_Ioi).mul
        ((by fun_prop : Continuous fun t : ℝ =>
          Complex.exp (-(π : ℂ) * z * (t : ℂ))).aestronglyMeasurable)
    have hBase_ε2 :
        Integrable (fun t : ℝ => base t * (Real.exp (-π * (ε / 2) * t) : ℂ)) μ := by
      simpa [μ, IntegrableOn] using (hbase_int (ε / 2) (by positivity))
    have hmem_Ioi : ∀ᵐ t ∂μ, t ∈ Set.Ioi (0 : ℝ) := by
      simpa [μ] using ae_restrict_mem (μ := (volume : Measure ℝ))
        (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
    have hF_int : Integrable (F u) μ := by
      refine Integrable.mono' (g := fun t : ℝ => ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖)
        hBase_ε2.norm (hF_meas u) ?_
      filter_upwards [hmem_Ioi] with t ht
      calc ‖F u t‖ = ‖base t‖ * ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ := by simp [F]
        _ ≤ ‖base t‖ * Real.exp (-π * (ε / 2) * t) := mul_le_mul_of_nonneg_left
            (norm_exp_le_of_re_ge ht.le (by dsimp [ε]; linarith : (ε / 2 : ℝ) ≤ u.re))
            (norm_nonneg _)
        _ = ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖ := by
          rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
    let bound : ℝ → ℝ := fun t => (2 / ε) * ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖
    have hbound_int : Integrable bound μ := by
      simpa [bound] using hBase_ε2.norm.const_mul (2 / ε)
    have hbound : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball u ε, ‖F' z t‖ ≤ bound t := by
      filter_upwards [hmem_Ioi] with t ht z hz
      have htpos : (0 : ℝ) < t := ht
      have hzre : ε ≤ z.re := by
        have hlt : |z.re - u.re| < ε := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            lt_of_le_of_lt (abs_re_le_norm (z - u))
              (by simpa [Metric.mem_ball] using hz : ‖z - u‖ < ε)
        dsimp [ε] at hlt ⊢; nlinarith [(abs_lt.mp hlt).1]
      have hExpTrade :
          (π * t) * Real.exp (-π * ε * t) ≤ (2 / ε) * Real.exp (-π * (ε / 2) * t) := by
        have hπε : (0 : ℝ) < π * ε := by positivity
        have hc2 : (0 : ℝ) ≤ 2 / (π * ε) := (div_pos (by norm_num) hπε).le
        have ht_le : t ≤ (2 / (π * ε)) * Real.exp ((π * ε / 2) * t) := by
          simpa [mul_assoc, show (2 / (π * ε)) * ((π * ε / 2) * t) = t by field_simp [hπε.ne']]
            using mul_le_mul_of_nonneg_left
              (by linarith [Real.add_one_le_exp ((π * ε / 2) * t)] :
                (π * ε / 2) * t ≤ Real.exp ((π * ε / 2) * t)) hc2
        have hbase : t * Real.exp (-(π * ε) * t) ≤ (2 / (π * ε)) * Real.exp (-(π * ε / 2) * t) := by
          refine (mul_le_mul_of_nonneg_right ht_le (Real.exp_nonneg (-(π * ε) * t))).trans_eq ?_
          rw [mul_assoc, ← Real.exp_add]; ring_nf
        simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv, Real.pi_ne_zero,
          ne_of_gt hε] using mul_le_mul_of_nonneg_left hbase Real.pi_pos.le
      have hnorm_integ : ‖F z t‖ ≤ ‖base t‖ * Real.exp (-π * ε * t) := by
        simpa [F, norm_mul, mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left (norm_exp_le_of_re_ge htpos.le hzre) (norm_nonneg _)
      have hnorm_base_exp : ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖ =
          ‖base t‖ * Real.exp (-π * (ε / 2) * t) := by
        rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
      calc ‖F' z t‖ = ‖(-(π : ℂ) * (t : ℂ))‖ * ‖F z t‖ := by simp [F']
        _ ≤ (π * t) * ‖F z t‖ := by rw [show ‖(-(π : ℂ) * (t : ℂ))‖ = π * t from by
              simp [abs_of_pos htpos, Real.pi_pos.le]]
        _ ≤ (π * t) * (‖base t‖ * Real.exp (-π * ε * t)) :=
          mul_le_mul_of_nonneg_left hnorm_integ (by nlinarith [Real.pi_pos, htpos.le])
        _ ≤ (2 / ε) * (‖base t‖ * Real.exp (-π * (ε / 2) * t)) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_left hExpTrade (norm_nonneg (base t))
        _ = bound t := by rw [← hnorm_base_exp]
    have hdiff : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball u ε,
        HasDerivAt (fun w : ℂ => F w t) (F' z t) z :=
      Filter.Eventually.of_forall fun t z _hz => by
        simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using
          (show HasDerivAt (fun w : ℂ => Complex.exp (-(π : ℂ) * w * (t : ℂ)))
              (Complex.exp (-(π : ℂ) * z * (t : ℂ)) * (-(π : ℂ) * (t : ℂ))) z from
            (show HasDerivAt (fun w : ℂ => (-(π : ℂ) * w * (t : ℂ))) (-(π : ℂ) * (t : ℂ)) z by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                ((hasDerivAt_id z).const_mul (-(π : ℂ) * (t : ℂ)))).cexp).const_mul (base t)
    have hDeriv : HasDerivAt (fun z : ℂ => ∫ t, F z t ∂μ) (∫ t, F' u t ∂μ) u :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
        (s := Metric.ball u ε) (Metric.ball_mem_nhds u hε) (x₀ := u)
        (F := F) (F' := F') (bound := bound)
        (hF_meas := Filter.Eventually.of_forall hF_meas) (hF_int := hF_int)
        (hF'_meas := ((by fun_prop : Continuous fun t : ℝ =>
            (-(π : ℂ) * (t : ℂ))).aestronglyMeasurable).mul (hF_meas u))
        (h_bound := hbound) (bound_integrable := hbound_int) (h_diff := hdiff)).2
    exact hDeriv.differentiableAt.differentiableWithinAt
  exact hDiff.analyticOnNhd rightHalfPlane_isOpen

/-- `aAnotherIntegralC` is analytic on the right half-plane. -/
public lemma aAnotherIntegralC_analyticOnNhd :
    AnalyticOnNhd ℂ aAnotherIntegralC rightHalfPlane := by
  have hcontIdiv : ContinuousOn (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Ioi (0 : ℝ)) :=
    continuous_const.continuousOn.div continuous_ofReal.continuousOn fun t ht => by
      exact_mod_cast ne_of_gt ht
  have hφcomp : ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) (Set.Ioi (0 : ℝ)) :=
    (by simpa using MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn :
      ContinuousOn (fun z : ℂ => φ₀'' z) upperHalfPlaneSet).comp hcontIdiv fun t ht => by
        change 0 < (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im
        rw [imag_I_div t]; exact inv_pos.2 (by simpa using ht)
  have hbase : ContinuousOn aAnotherBase (Set.Ioi (0 : ℝ)) :=
    ((((by fun_prop : Continuous fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ)).continuousOn.mul
      hφcomp).sub (continuousOn_const.mul (by fun_prop : Continuous fun t : ℝ =>
      ((Real.exp (2 * π * t)) : ℂ)).continuousOn)).add
      (continuousOn_const.mul continuous_ofReal.continuousOn)).sub continuousOn_const
  convert analyticOnNhd_integral_base_exp (base := aAnotherBase)
    hbase (fun u hu => (aAnotherIntegrand_integrable_of_pos hu).congr <|
      Filter.Eventually.of_forall fun t => by
        simp [aAnotherIntegrand, aAnotherBase, mul_assoc]) using 1

/-!
## Analytic RHS function on `ℂ`

This is the complex-analytic function whose restriction to the real axis is the blueprint RHS.
-/

def aAnotherRHS (u : ℂ) : ℂ :=
  (4 * Complex.I) * (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) *
    ((36 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * (u - 2)) -
      (8640 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u ^ (2 : ℕ)) +
      (18144 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u) + aAnotherIntegralC u)

lemma aAnotherRHS_analyticOnNhd :
    AnalyticOnNhd ℂ aAnotherRHS ACDomain := by
  have hπ : (π : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
  have hu_ne0 : ∀ u ∈ ACDomain, u ≠ 0 := fun u hu h0 =>
    absurd (by simpa [rightHalfPlane] using hu.1) (by simp [h0])
  have hterm1 :
      AnalyticOnNhd ℂ (fun u : ℂ => (36 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * (u - 2))) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const))
      fun u hu => mul_ne_zero (pow_ne_zero _ hπ) (sub_ne_zero.2 (by simpa using hu.2))
  have hterm2 :
      AnalyticOnNhd ℂ (fun u : ℂ => (8640 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u ^ (2 : ℕ))) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul (analyticOnNhd_id.pow 2))
      fun u hu => mul_ne_zero (pow_ne_zero _ hπ) (pow_ne_zero _ (hu_ne0 u hu))
  have hterm3 :
      AnalyticOnNhd ℂ (fun u : ℂ => (18144 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u)) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul analyticOnNhd_id)
      fun u hu => mul_ne_zero (pow_ne_zero _ hπ) (hu_ne0 u hu)
  have hinner :
      AnalyticOnNhd ℂ
        (fun u : ℂ =>
          (36 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * (u - 2)) -
              (8640 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u) + aAnotherIntegralC u)
        ACDomain := by
    simpa [sub_eq_add_neg, add_assoc] using (hterm1.sub hterm2).add
      (hterm3.add (aAnotherIntegralC_analyticOnNhd.mono fun u hu => hu.1))
  simpa [aAnotherRHS] using
    analyticOnNhd_sinSq_prefactor_mul (sign := 4 * Complex.I) hinner

/-- Analytic-continuation step: extend the "another integral" identity for `a'` from `u > 2`
to all real `0 < u` with `u ≠ 2`. -/
public theorem aRadial_eq_another_integral_analytic_continuation_of_gt2
  (h_gt2 :
      ∀ r : ℝ, 2 < r →
        a' r =
          (4 * Complex.I) * (Real.sin (π * r / 2)) ^ (2 : ℕ) *
            ((36 : ℂ) / (π ^ (3 : ℕ) * (r - 2)) -
              (8640 : ℂ) / (π ^ (3 : ℕ) * r ^ (2 : ℕ)) +
              (18144 : ℂ) / (π ^ (3 : ℕ) * r) +
                ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand r t))
    {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    a' u =
      (4 * Complex.I) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
          (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * u) +
            ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) := by
  refine analytic_continuation_of_gt2
    ⟨aPrimeC, aPrimeC_analyticOnNhd.mono (fun u hu => hu.1), fun u hu _ => by
      simpa [show MagicFunction.a.RealIntegrals.a' u = a' u by
        simpa using (MagicFunction.g.CohnElkies.a'_eq_realIntegrals_a' (u := u) (hu := hu.le)).symm]
        using aPrimeC_ofReal u⟩
    aAnotherRHS_analyticOnNhd
    (rhsR := fun r : ℝ =>
      (4 * Complex.I) * (Real.sin (π * r / 2)) ^ (2 : ℕ) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (r - 2)) -
          (8640 : ℂ) / (π ^ (3 : ℕ) * r ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * r) +
            ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand r t))
    (fun r => by
      simp only [aAnotherRHS, show (Complex.sin ((π : ℂ) * (r : ℂ) / 2)) ^ (2 : ℕ) =
        ((Real.sin (π * r / 2)) ^ (2 : ℕ) : ℂ) by simp,
        show aAnotherIntegralC (r : ℂ) = ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand r t from
          MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
            measurableSet_Ioi (fun t _ => by
              simp [aAnotherIntegrandC, aAnotherBase, aAnotherIntegrand])])
    h_gt2 hu hu2

/-- Integral of a triple sum is the sum of the integrals, under integrability assumptions. -/
public lemma integral_add_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, ((f x + g x) + h x) ∂ μ) =
      (∫ x, f x ∂ μ) + (∫ x, g x ∂ μ) + (∫ x, h x ∂ μ) := by
  simpa [add_assoc, MeasureTheory.integral_add (μ := μ) hf hg] using
    MeasureTheory.integral_add (μ := μ) (hf.add hg) hh

/-- `∫_{t > 0} exp (-π u t) dt = 1 / (π u)` as a complex-valued integral, for `u > 0`. -/
public lemma integral_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * u) : ℝ) : ℂ) := by
  change (∫ t : ℝ, (Real.exp (-π * u * t) : ℂ) ∂μIoi0) = ((1 / (π * u) : ℝ) : ℂ)
  rw [← MagicFunction.g.CohnElkies.integral_exp_neg_pi_mul_Ioi (u := u) hu]
  exact integral_ofReal (μ := μIoi0) (𝕜 := ℂ)

/-- `∫_{t > 0} t * exp (-π u t) dt = 1 / (π u)^2` as a complex-valued integral, for `u > 0`. -/
public lemma integral_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (t * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := by
  change (∫ t : ℝ, (t * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
      ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ)
  rw [← MagicFunction.g.CohnElkies.integral_mul_exp_neg_pi_mul_Ioi (u := u) hu]
  simpa [Complex.ofReal_mul] using
    integral_ofReal (μ := μIoi0) (𝕜 := ℂ) (f := fun t : ℝ => t * Real.exp (-π * u * t))

/-- `∫_{t > 0} exp (2π t) * exp (-π u t) dt = 1 / (π (u - 2))` as a complex-valued integral,
for `u > 2`. -/
public lemma integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 2 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * (u - 2)) : ℝ) : ℂ) := by
  change (∫ t : ℝ, (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
      ((1 / (π * (u - 2)) : ℝ) : ℂ)
  rw [← MagicFunction.g.CohnElkies.integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi (u := u) hu]
  simpa [Complex.ofReal_mul] using integral_ofReal (μ := μIoi0) (𝕜 := ℂ)
    (f := fun t : ℝ => Real.exp (2 * π * t) * Real.exp (-π * u * t))

/-- Integrability of `t ↦ exp (-π u t)` on `t > 0` as a complex-valued function, for `u > 0`. -/
public lemma integrableOn_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
  have hne : (∫ t : ℝ, (Real.exp (-π * u * t) : ℂ) ∂μIoi0) ≠ 0 := by
    rw [show (∫ t : ℝ, (Real.exp (-π * u * t) : ℂ) ∂μIoi0) = ((1 / (π * u) : ℝ) : ℂ) from by
      simpa [μIoi0] using integral_exp_neg_pi_mul_Ioi_complex (u := u) hu]
    exact_mod_cast one_div_ne_zero (mul_ne_zero Real.pi_ne_zero hu.ne')
  simpa [MeasureTheory.IntegrableOn, μIoi0] using
    MeasureTheory.Integrable.of_integral_ne_zero (μ := μIoi0) hne

/-- Integrability of `t ↦ t * exp (-π u t)` on `t > 0` as a complex-valued function, for
`u > 0`. -/
public lemma integrableOn_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
  have hne : (∫ t : ℝ, (t * Real.exp (-π * u * t) : ℂ) ∂μIoi0) ≠ 0 := by
    rw [show (∫ t : ℝ, (t * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
        ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) from by
      simpa [μIoi0] using integral_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu]
    exact_mod_cast one_div_ne_zero (pow_ne_zero 2 (mul_ne_zero Real.pi_ne_zero hu.ne'))
  simpa [MeasureTheory.IntegrableOn, μIoi0] using
    MeasureTheory.Integrable.of_integral_ne_zero (μ := μIoi0) hne

/-- Integrability of `t ↦ exp (2π t) * exp (-π u t)` on `t > 0` as a complex-valued function, for
`u > 2`. -/
public lemma integrableOn_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  have hne :
      (∫ t : ℝ, (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) ∂μIoi0) ≠ 0 := by
    rw [show (∫ t : ℝ, (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
        ((1 / (π * (u - 2)) : ℝ) : ℂ) from by
      simpa [μIoi0] using integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu]
    exact_mod_cast one_div_ne_zero (mul_ne_zero Real.pi_ne_zero (sub_pos.2 hu).ne')
  simpa [MeasureTheory.IntegrableOn, μIoi0] using
    MeasureTheory.Integrable.of_integral_ne_zero (μ := μIoi0) hne

end

end MagicFunction.g.CohnElkies.IntegralReps
