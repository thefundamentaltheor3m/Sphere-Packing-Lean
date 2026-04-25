module
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.StripBounds
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.FiniteDifference
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular


/-!
# Tail deformation for `a'`

This file proves the tail contour deformation for the pieces `I₂' + I₄' + I₆'` in the
definition of `a'`. The deformation is carried out on the rectangle strip `t ≥ 1`, using
`rect_deform_of_tendsto_top` together with explicit exponential bounds.

## Main statements
* `MagicFunction.g.CohnElkies.IntegralReps.integrableOn_Φ₅'_imag_axis_Ioi0`
* `MagicFunction.g.CohnElkies.IntegralReps.I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators UpperHalfPlane Topology intervalIntegral
open MeasureTheory Real Complex Filter
open UpperHalfPlane
open MagicFunction.FourierEigenfunctions
open MagicFunction.a.ComplexIntegrands

local notation "c12π" => ‖(12 * (Complex.I : ℂ)) / (π : ℂ)‖
local notation "c36π2" => ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖


/-- Integrability of `Φ₅'` on the full ray `t > 0` (via `aLaplaceIntegrand`). -/
public lemma integrableOn_Φ₅'_imag_axis_Ioi0 {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (Set.Ioi (0 : ℝ)) volume := by
  simpa [IntegrableOn, Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand] using
    (show Integrable (fun t : ℝ => aLaplaceIntegrand u t) (volume.restrict (Set.Ioi (0 : ℝ))) from
      by simpa [IntegrableOn] using aLaplaceIntegral_convergent (u := u) hu).neg'

private lemma norm_real_add_mul_I_le_two_mul {a t : ℝ} (ha : ‖((a : ℝ) : ℂ)‖ ≤ (1 : ℝ))
    (ht : (1 : ℝ) ≤ t) :
    ‖((a : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ≤ 2 * t := by
  have : ‖(t : ℂ) * Complex.I‖ = t := by simp [abs_of_nonneg (by linarith : (0:ℝ) ≤ t)]
  linarith [norm_add_le ((a : ℝ) : ℂ) ((t : ℂ) * Complex.I)]

/-- Generic strip-bound core: given `x ∈ [-1,1]`, `t ≥ 1`, and a function `F` satisfying
`F (x + t*I) = (φ₀''(-1/w) * w^2) * exp(π*I*u*(x + t*I))` where `w = s + t*I` with `|s| ≤ 1`,
bound `‖F (x + t*I)‖` by the standard envelope. -/
private lemma norm_strip_le_of_hdef {u s t x : ℝ} {F : ℂ → ℂ}
    {Cφ Aφ C₀ : ℝ}
    (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im →
      ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
        ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (hs : |s| ≤ (1 : ℝ))
    (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t)
    (hdef : F ((x : ℂ) + (t : ℂ) * Complex.I) =
      (φ₀'' ((-1 : ℂ) / (((s : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
        ((((s : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ (2 : ℕ))) *
          cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I))) :
    ‖F ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
  set K : ℝ := 4 * C₀ + (2 * c12π + c36π2) * Cφ
  let w : ℂ := ((s : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hw_im : w.im = t := by simp [w]
  let wH : ℍ := ⟨w, by simpa [hw_im] using lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) ht1⟩
  calc ‖F ((x : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ * Real.exp (-π * u * t) := by
          rw [hdef]; show ‖_ * _‖ = _
          rw [show φ₀'' ((-1 : ℂ) / w) * (w ^ 2) =
              φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ)) by
            rw [show φ₀ (ModularGroup.S • wH) = φ₀'' ((ModularGroup.S • wH : ℍ) : ℂ) by simp,
              show ((ModularGroup.S • wH : ℍ) : ℂ) = (-1 : ℂ) / (wH : ℂ) by
                simpa using ModularGroup.coe_S_smul (z := wH)], norm_mul,
            show ‖cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I))‖ =
                Real.exp (-π * u * t) by
              rw [show ((π : ℂ) * Complex.I * (u : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I)) =
                  ((π * u * x : ℝ) : ℂ) * Complex.I - ((π * u * t : ℝ) : ℂ) from by
                push_cast; ring_nf; simp [mul_left_comm, mul_comm, sub_eq_add_neg],
                Complex.norm_exp]
              simp [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]]
    _ ≤ (K * (t ^ (2 : ℕ) * Real.exp (2 * π * t))) * Real.exp (-π * u * t) :=
          mul_le_mul_of_nonneg_right (norm_phi0S_mul_sq_le wH hw_im hC₀_pos hC₀ hφbd ht1 htAφ
            (norm_real_add_mul_I_le_two_mul (a := s) (t := t)
              (by simpa [Complex.norm_real] using hs) ht1)) (Real.exp_pos _).le
    _ = K * (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
          rw [mul_assoc, mul_assoc, ← MagicFunction.g.CohnElkies.exp_two_pi_mul_mul_exp_neg_pi_mul]

/-- Uniform strip bound for `Φ₂' u (x + tI)` with `x ∈ [-1,0]` and `t ≥ 1`. -/
lemma norm_Φ₂'_strip_le {u x t : ℝ} {Cφ Aφ C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im →
      ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
        ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (hx0 : -1 ≤ x) (hx1 : x ≤ 0) (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t) :
    ‖Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
  refine norm_strip_le_of_hdef (s := x + 1) (F := Φ₂' u) hC₀_pos hC₀ hφbd
    (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x + 1)]; linarith) ht1 htAφ ?_
  simp [MagicFunction.a.ComplexIntegrands.Φ₂', MagicFunction.a.ComplexIntegrands.Φ₁',
    show (x : ℂ) + (t : ℂ) * Complex.I + 1 =
      ((x + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I from by push_cast; ring, mul_assoc]

/-- Uniform strip bound for `Φ₄' u (x + tI)` with `x ∈ [0,1]` and `t ≥ 1`. -/
lemma norm_Φ₄'_strip_le {u x t : ℝ} {Cφ Aφ C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im →
      ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
        ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t) :
    ‖Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
  refine norm_strip_le_of_hdef (s := x - 1) (F := Φ₄' u) hC₀_pos hC₀ hφbd
    (by rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - x)]; linarith) ht1 htAφ ?_
  simp [MagicFunction.a.ComplexIntegrands.Φ₄', MagicFunction.a.ComplexIntegrands.Φ₃',
    show (x : ℂ) + (t : ℂ) * Complex.I - 1 =
      ((x - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I from by push_cast; ring, mul_assoc]

/-- Generic top-edge decay: reduces a `tendsto` statement on an interval integral to a pointwise
strip bound. -/
private lemma tendsto_intervalIntegral_top_of_strip_bound {u : ℝ} (hu : 2 < u) {F : ℂ → ℂ}
    {x₁ x₂ : ℝ} (hlen : |x₂ - x₁| ≤ 1)
    (hF : ∀ Cφ Aφ C₀ x t : ℝ, 0 < C₀ →
      (∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im)) →
      (∀ z : ℍ, Aφ ≤ z.im →
        ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
          ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im)) →
      x ∈ Set.uIoc x₁ x₂ → (1 : ℝ) ≤ t → Aφ ≤ t →
      ‖F ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
          (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t))) :
    Tendsto (fun m : ℝ => ∫ x in x₁..x₂, F ((x : ℂ) + (m : ℂ) * Complex.I))
      atTop (𝓝 0) := by
  obtain ⟨Cφ, Aφ, _, hφbd⟩ := exists_phi2'_phi4'_bound_exp
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  set K : ℝ := 4 * C₀ + (2 * c12π + c36π2) * Cφ
  set a : ℝ := π * (u - 2)
  have ha : 0 < a := mul_pos Real.pi_pos (sub_pos.2 hu)
  have htend : Tendsto (fun m : ℝ => K * (m ^ (2 : ℕ) * Real.exp (-a * m))) atTop (𝓝 0) := by
    simpa [mul_zero] using tendsto_const_nhds.mul
      (by simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (2 : ℝ)) (b := a) ha :
        Tendsto (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t)) atTop (𝓝 0))
  refine squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨max 1 Aφ, fun m hm => ?_⟩) htend
  have hm1 : (1 : ℝ) ≤ m := (le_max_left _ _).trans hm
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (a := x₁) (b := x₂)
    (f := fun x : ℝ => F ((x : ℂ) + (m : ℂ) * Complex.I))
    (C := K * (m ^ (2 : ℕ) * Real.exp (-a * m)))
    (fun x hx => hF Cφ Aφ C₀ x m hC₀_pos hC₀ hφbd hx hm1 ((le_max_right _ _).trans hm))).trans ?_
  nlinarith [hlen, show 0 ≤ K * (m ^ (2 : ℕ) * Real.exp (-a * m)) by positivity]

/-- Top-edge decay needed for the left rectangle deformation (`Φ₂'`). -/
lemma tendsto_intervalIntegral_Φ₂'_top {u : ℝ} (hu : 2 < u) :
    Tendsto (fun m : ℝ => ∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + (m : ℂ) * Complex.I))
      atTop (𝓝 0) :=
  tendsto_intervalIntegral_top_of_strip_bound hu (x₁ := -1) (x₂ := 0) (by norm_num)
    fun _ _ _ x _ h1 h2 h3 hx h4 h5 =>
      have hx' : x ∈ Set.Ioc (-1 : ℝ) 0 := by
        simpa [Set.uIoc_of_le (show (-1:ℝ) ≤ 0 by norm_num)] using hx
      norm_Φ₂'_strip_le h1 h2 h3 hx'.1.le hx'.2 h4 h5

/-- Top-edge decay needed for the right rectangle deformation (`Φ₄'`). -/
lemma tendsto_intervalIntegral_Φ₄'_top {u : ℝ} (hu : 2 < u) :
    Tendsto (fun m : ℝ => ∫ x in (1 : ℝ)..0, Φ₄' u ((x : ℂ) + (m : ℂ) * Complex.I))
      atTop (𝓝 0) :=
  tendsto_intervalIntegral_top_of_strip_bound hu (x₁ := 1) (x₂ := 0) (by norm_num)
    fun _ _ _ x _ h1 h2 h3 hx h4 h5 =>
      have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_ge (show (0:ℝ) ≤ 1 by norm_num)] using hx
      norm_Φ₄'_strip_le h1 h2 h3 hx'.1.le hx'.2 h4 h5

lemma I₂'_eq_intervalIntegral_bottom (u : ℝ) :
    MagicFunction.a.RealIntegrals.I₂' u =
      ∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + Complex.I) := by
  dsimp [MagicFunction.a.RealIntegrals.I₂', MagicFunction.a.RealIntegrands.Φ₂]
  let g : ℝ → ℂ := fun x : ℝ => Φ₂' u ((x : ℂ) + Complex.I)
  rw [show (∫ t in (0 : ℝ)..1, Φ₂' u (MagicFunction.Parametrisations.z₂' t)) =
      ∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ)) from
    intervalIntegral.integral_congr fun t ht => by
      simp [g, show MagicFunction.Parametrisations.z₂' t =
        (-1 : ℂ) + (t : ℂ) + (Complex.I : ℂ) from by
          simpa using MagicFunction.Parametrisations.z₂'_eq_of_mem (t := t)
            (by simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht), add_comm],
    show (∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ))) = ∫ x in (-1 : ℝ)..0, g x from by norm_num]

lemma I₄'_eq_intervalIntegral_bottom (u : ℝ) :
    MagicFunction.a.RealIntegrals.I₄' u =
      ∫ x in (1 : ℝ)..0, Φ₄' u ((x : ℂ) + Complex.I) := by
  dsimp [MagicFunction.a.RealIntegrals.I₄', MagicFunction.a.RealIntegrands.Φ₄]
  let g : ℝ → ℂ := fun x : ℝ => Φ₄' u ((x : ℂ) + Complex.I)
  calc ∫ t in (0 : ℝ)..1, (-1 : ℂ) * Φ₄' u (MagicFunction.Parametrisations.z₄' t)
      = ∫ t in (0 : ℝ)..1, (-1 : ℂ) * g (1 - t) :=
        intervalIntegral.integral_congr fun t ht => by
          simp [g, show MagicFunction.Parametrisations.z₄' t =
            (1 : ℂ) - (t : ℂ) + (Complex.I : ℂ) from by
              simpa using MagicFunction.Parametrisations.z₄'_eq_of_mem (t := t)
                (by simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht),
            sub_eq_add_neg]
    _ = -∫ t in (0 : ℝ)..1, g t := by simp [show (∫ t in (0 : ℝ)..1, g (1 - t)) =
          ∫ t in (0 : ℝ)..1, g t by norm_num]
    _ = ∫ t in (1 : ℝ)..0, g t := by
        simpa using (intervalIntegral.integral_symm (a := (0 : ℝ)) (b := (1 : ℝ)) (f := g)).symm

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
  have hcont : ContinuousOn f (Set.uIcc x₁ x₂ ×ℂ Set.Ici (1 : ℝ)) :=
    hcontU.mono fun z hz => show 0 < z.im from
      lt_of_lt_of_le zero_lt_one (by simpa [mem_reProdIm] using hz : _ ∧ z.im ∈ Set.Ici (1 : ℝ)).2
  have hdiff : ∀ z ∈ (Set.Ioo (min x₁ x₂) (max x₁ x₂) ×ℂ Set.Ioi (1 : ℝ)),
      DifferentiableAt ℂ f z := fun z hz =>
    have hz0 : 0 < z.im := lt_trans zero_lt_one
      (by simpa [mem_reProdIm] using hz : _ ∧ z.im ∈ Set.Ioi (1 : ℝ)).2
    (hdiffU z hz0).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hz0)
  simpa [smul_eq_mul, mul_sub, one_mul] using eq_sub_of_add_eq (by
    simpa [one_mul] using sub_eq_zero.mp <| Complex.rect_deform_of_tendsto_top (f := f)
      (x₁ := x₁) (x₂ := x₂) (y := (1 : ℝ)) hcont hdiff hint₁ hint₂ htop)

lemma I₂'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    MagicFunction.a.RealIntegrals.I₂' u =
      (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((t : ℂ) * Complex.I)) := by
  rw [I₂'_eq_intervalIntegral_bottom (u := u)]
  simpa [zero_add] using bottom_eq_I_smul_sub_of_rect_deform (f := Φ₂' u)
    (x₁ := (-1 : ℝ)) (x₂ := (0 : ℝ))
    (MagicFunction.a.ComplexIntegrands.Φ₁'_contDiffOn_ℂ (r := u)).continuousOn
    ((MagicFunction.a.ComplexIntegrands.Φ₁'_contDiffOn_ℂ (r := u)).differentiableOn (by simp))
    (by simpa [show (fun t : ℝ => Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) =
        fun t : ℝ => Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) *
          Φ₅' u ((t : ℂ) * Complex.I) from funext fun t => Φ₁'_shift_left (u := u) (t := t)]
      using (integrableOn_Φ₅'_imag_axis (u := u) hu).const_mul _)
    (by simpa using integrableOn_Φ₂'_imag_axis (u := u) hu)
    (tendsto_intervalIntegral_Φ₂'_top (u := u) hu)

lemma I₄'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    MagicFunction.a.RealIntegrals.I₄' u =
      (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((t : ℂ) * Complex.I)) := by
  rw [I₄'_eq_intervalIntegral_bottom (u := u)]
  simpa [zero_add] using bottom_eq_I_smul_sub_of_rect_deform (f := Φ₄' u)
    (x₁ := (1 : ℝ)) (x₂ := (0 : ℝ))
    (MagicFunction.a.ComplexIntegrands.Φ₃'_contDiffOn_ℂ (r := u)).continuousOn
    ((MagicFunction.a.ComplexIntegrands.Φ₃'_contDiffOn_ℂ (r := u)).differentiableOn (by simp))
    (by simpa [show (fun t : ℝ => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) =
        fun t : ℝ => Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) *
          Φ₅' u ((t : ℂ) * Complex.I) from funext fun t => Φ₃'_shift_right (u := u) (t := t)]
      using (integrableOn_Φ₅'_imag_axis (u := u) hu).const_mul _)
    (by simpa using integrableOn_Φ₄'_imag_axis (u := u) hu)
    (tendsto_intervalIntegral_Φ₄'_top (u := u) hu)

lemma I₆'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    MagicFunction.a.RealIntegrals.I₆' u =
      (Complex.I : ℂ) *
        ((∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((t : ℂ) * Complex.I)) -
            2 * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) +
              ∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((t : ℂ) * Complex.I)) := by
  have hI6 : MagicFunction.a.RealIntegrals.I₆' u =
      (2 : ℂ) *
        ∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I) := by
    dsimp [MagicFunction.a.RealIntegrals.I₆', MagicFunction.a.RealIntegrands.Φ₆]
    rw [show (∫ t in Set.Ici (1 : ℝ),
              (Complex.I : ℂ) * Φ₆' u (MagicFunction.Parametrisations.z₆' t)) =
          ∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun t ht => by
        simp [show MagicFunction.Parametrisations.z₆' t = (Complex.I : ℂ) * (t : ℂ) from by
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            MagicFunction.Parametrisations.z₆'_eq_of_mem (t := t) ht, mul_comm],
      MeasureTheory.integral_Ici_eq_integral_Ioi]
  let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  let f2 : ℝ → ℂ := fun t => Φ₂' u ((t : ℂ) * Complex.I)
  let f5 : ℝ → ℂ := fun t => Φ₅' u ((t : ℂ) * Complex.I)
  let f4 : ℝ → ℂ := fun t => Φ₄' u ((t : ℂ) * Complex.I)
  have hf2 : Integrable f2 μ := integrableOn_Φ₂'_imag_axis (u := u) hu
  have hf5 : Integrable f5 μ := integrableOn_Φ₅'_imag_axis (u := u) hu
  have hf4 : Integrable f4 μ := integrableOn_Φ₄'_imag_axis (u := u) hu
  have hfdI : ∀ t ∈ Set.Ioi (1 : ℝ),
      (2 : ℂ) * ((Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I)) =
        (Complex.I : ℂ) * (f2 t - 2 * f5 t + f4 t) := fun t ht => by
    simpa [f2, f5, f4, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm,
      sub_eq_add_neg] using (congrArg (fun z : ℂ => (Complex.I : ℂ) * z)
      (Φ_finite_difference_imag_axis (u := u) (t := t) (lt_trans zero_lt_one ht))).symm
  rw [hI6,
    (MeasureTheory.integral_const_mul (μ := μ) (r := (2 : ℂ))
      (f := fun t : ℝ => (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I))).symm,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hfdI,
    MeasureTheory.integral_const_mul (μ := μ) (r := (Complex.I : ℂ))
      (f := fun t => f2 t - 2 * f5 t + f4 t)]
  have h1 := MeasureTheory.integral_add (μ := μ) (hf2.sub (hf5.const_mul 2)) hf4
  calc (Complex.I : ℂ) * (∫ t, (f2 t - 2 * f5 t + f4 t) ∂μ)
      = (Complex.I : ℂ) * ((∫ t, f2 t - 2 * f5 t ∂μ) + ∫ t, f4 t ∂μ) := by
        simpa using congrArg ((Complex.I : ℂ) * ·) h1
    _ = (Complex.I : ℂ) * ((∫ t, f2 t ∂μ) - 2 * (∫ t, f5 t ∂μ) + ∫ t, f4 t ∂μ) := by
        rw [MeasureTheory.integral_sub (μ := μ) hf2 (hf5.const_mul 2),
          MeasureTheory.integral_const_mul (μ := μ) (r := (2 : ℂ)) (f := f5)]

/-- Generic helper: if `G t = E * Φ₅' u (t*I)` for `t > 1`, then the ray integral of `G` over
`Ioi 1` equals `E` times the central ray integral. -/
private lemma ray_integral_eq_const_mul_central {u : ℝ} {G : ℝ → ℂ} {E : ℂ}
    (hG : ∀ t, 1 < t → G t = E * Φ₅' u ((t : ℂ) * Complex.I)) :
    (∫ t in Set.Ioi (1 : ℝ), G t) =
      E * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hG, MeasureTheory.integral_const_mul]

/--
Rewrite the tail part `I₂' + I₄' + I₆'` as an imaginary-axis integral of `Φ₅'` over `t ≥ 1`.
-/
public lemma I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail {u : ℝ} (hu : 2 < u) :
    MagicFunction.a.RealIntegrals.I₂' u + MagicFunction.a.RealIntegrals.I₄' u +
        MagicFunction.a.RealIntegrals.I₆' u =
      (Complex.I : ℂ) *
        ((Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) +
              Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) *
          (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) := by
  have hLeft_ray := ray_integral_eq_const_mul_central
    (G := fun t => Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I))
    (E := Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)))
    fun t _ => by simpa [mul_assoc] using Φ₁'_shift_left (u := u) (t := t)
  have hRight_ray := ray_integral_eq_const_mul_central
    (G := fun t => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I))
    (E := Complex.exp (((π * u : ℝ) : ℂ) * Complex.I))
    fun t _ => by simpa [mul_assoc] using Φ₃'_shift_right (u := u) (t := t)
  rw [I₂'_eq_deform_imag_axis (u := u) hu, I₄'_eq_deform_imag_axis (u := u) hu,
    I₆'_eq_deform_imag_axis (u := u) hu, hLeft_ray, hRight_ray]
  simp [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm]
  ring

end MagicFunction.g.CohnElkies.IntegralReps
