module
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.StripBounds
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.FiniteDifference
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular

/-! # Tail deformation for `a'`: rewrite `I₂' + I₄' + I₆'` via `rect_deform_of_tendsto_top`. -/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators UpperHalfPlane Topology intervalIntegral
open MeasureTheory Real Complex Filter UpperHalfPlane
  MagicFunction.FourierEigenfunctions MagicFunction.a.ComplexIntegrands

local notation "c12π" => ‖(12 * (Complex.I : ℂ)) / (π : ℂ)‖
local notation "c36π2" => ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖

/-- Integrability of `Φ₅'` on the full ray `t > 0` (via `aLaplaceIntegrand`). -/
public lemma integrableOn_Φ₅'_imag_axis_Ioi0 {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (Set.Ioi (0 : ℝ)) volume := by
  simpa [IntegrableOn, Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand] using
    (aLaplaceIntegral_convergent hu).neg'

/-- Strip-bound core: given `F (x + tI) = (φ₀''(-1/w) * w^2) * exp(πIu(x + tI))` with
`w = s + tI`, `|s| ≤ 1`, bound `‖F (x + tI)‖` by the standard envelope. -/
private lemma norm_strip_le_of_hdef {u s t x : ℝ} {F : ℂ → ℂ}
    {Cφ Aφ C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
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
  let wH : ℍ := ⟨((s : ℝ) : ℂ) + (t : ℂ) * Complex.I, by
    simpa using lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) ht1⟩
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
    Tendsto (fun m : ℝ => ∫ x in x₁..x₂, F ((x : ℂ) + (m : ℂ) * Complex.I))
      atTop (𝓝 0) := by
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
    (f := fun x : ℝ => F ((x : ℂ) + (m : ℂ) * Complex.I))
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
    MagicFunction.a.RealIntegrals.I₂' u =
      (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((t : ℂ) * Complex.I)) := by
  let g : ℝ → ℂ := fun x : ℝ => Φ₂' u ((x : ℂ) + Complex.I)
  rw [show MagicFunction.a.RealIntegrals.I₂' u = ∫ x in (-1 : ℝ)..0, g x by
    dsimp [MagicFunction.a.RealIntegrals.I₂', MagicFunction.a.RealIntegrands.Φ₂]
    rw [show (∫ t in (0 : ℝ)..1, Φ₂' u (MagicFunction.Parametrisations.z₂' t)) =
        ∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ)) from intervalIntegral.integral_congr fun t ht => by
          simp [g, show MagicFunction.Parametrisations.z₂' t =
              (-1 : ℂ) + (t : ℂ) + (Complex.I : ℂ) by
            simpa using MagicFunction.Parametrisations.z₂'_eq_of_mem
              (by simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht), add_comm],
      show (∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ))) = ∫ x in (-1 : ℝ)..0, g x by norm_num]]
  simpa [zero_add] using bottom_eq_I_smul_sub_of_rect_deform (f := Φ₂' u)
    (x₁ := (-1 : ℝ)) (x₂ := (0 : ℝ))
    (MagicFunction.a.ComplexIntegrands.Φ₁'_contDiffOn_ℂ (r := u)).continuousOn
    ((MagicFunction.a.ComplexIntegrands.Φ₁'_contDiffOn_ℂ (r := u)).differentiableOn (by simp))
    (by simpa [show (fun t : ℝ => Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) =
        fun t : ℝ => Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) *
          Φ₅' u ((t : ℂ) * Complex.I) from funext fun t => Φ₁'_shift_left (u := u) (t := t)]
      using (integrableOn_Φ₅'_imag_axis hu).const_mul _)
    (by simpa using integrableOn_Φ₂'_imag_axis hu)
    (tendsto_intervalIntegral_Φ₂'_top hu)

lemma I₄'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    MagicFunction.a.RealIntegrals.I₄' u =
      (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((t : ℂ) * Complex.I)) := by
  let g : ℝ → ℂ := fun x : ℝ => Φ₄' u ((x : ℂ) + Complex.I)
  rw [show MagicFunction.a.RealIntegrals.I₄' u = ∫ x in (1 : ℝ)..0, g x by
    dsimp [MagicFunction.a.RealIntegrals.I₄', MagicFunction.a.RealIntegrands.Φ₄]
    rw [show (∫ t in (0 : ℝ)..1, (-1 : ℂ) * Φ₄' u (MagicFunction.Parametrisations.z₄' t)) =
        ∫ t in (0 : ℝ)..1, (-1 : ℂ) * g (1 - t) from
      intervalIntegral.integral_congr fun t ht => by
        simp [g, sub_eq_add_neg,
          show MagicFunction.Parametrisations.z₄' t = (1 : ℂ) - (t : ℂ) + (Complex.I : ℂ) by
            simpa using MagicFunction.Parametrisations.z₄'_eq_of_mem (t := t)
              (by simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)],
      intervalIntegral.integral_const_mul,
      show (∫ t in (0 : ℝ)..1, g (1 - t)) = ∫ t in (0 : ℝ)..1, g t by norm_num]
    simpa using (intervalIntegral.integral_symm (a := (0 : ℝ)) (b := (1 : ℝ)) (f := g)).symm]
  simpa [zero_add] using bottom_eq_I_smul_sub_of_rect_deform (f := Φ₄' u)
    (x₁ := (1 : ℝ)) (x₂ := (0 : ℝ))
    (MagicFunction.a.ComplexIntegrands.Φ₃'_contDiffOn_ℂ (r := u)).continuousOn
    ((MagicFunction.a.ComplexIntegrands.Φ₃'_contDiffOn_ℂ (r := u)).differentiableOn (by simp))
    (by simpa [show (fun t : ℝ => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) =
        fun t : ℝ => Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) *
          Φ₅' u ((t : ℂ) * Complex.I) from funext fun t => Φ₃'_shift_right (u := u) (t := t)]
      using (integrableOn_Φ₅'_imag_axis hu).const_mul _)
    (by simpa using integrableOn_Φ₄'_imag_axis hu)
    (tendsto_intervalIntegral_Φ₄'_top hu)

lemma I₆'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    MagicFunction.a.RealIntegrals.I₆' u =
      (Complex.I : ℂ) *
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
  dsimp [MagicFunction.a.RealIntegrals.I₆', MagicFunction.a.RealIntegrands.Φ₆]
  rw [show (∫ t in Set.Ici (1 : ℝ),
            (Complex.I : ℂ) * Φ₆' u (MagicFunction.Parametrisations.z₆' t)) =
        ∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I) from
      setIntegral_congr_fun measurableSet_Ici fun t ht => by
        simp [show MagicFunction.Parametrisations.z₆' t = (Complex.I : ℂ) * (t : ℂ) from by
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            MagicFunction.Parametrisations.z₆'_eq_of_mem ht, mul_comm],
    integral_Ici_eq_integral_Ioi,
    (integral_const_mul (μ := μ) (r := (2 : ℂ))
      (f := fun t : ℝ => (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I))).symm,
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
      simpa [f2, f5, f4, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm,
        sub_eq_add_neg] using (congrArg (fun z : ℂ => (Complex.I : ℂ) * z)
        (Φ_finite_difference_imag_axis (lt_trans zero_lt_one ht))).symm :
      ∀ t ∈ Set.Ioi (1 : ℝ),
      (2 : ℂ) * ((Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I)) =
        (Complex.I : ℂ) * (f2 t - 2 * f5 t + f4 t)),
    integral_const_mul (μ := μ) (r := (Complex.I : ℂ))
      (f := fun t => f2 t - 2 * f5 t + f4 t)]
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
    (∫ t in Set.Ioi (1 : ℝ), G t) =
      E * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) := by
  rw [setIntegral_congr_fun measurableSet_Ioi hG, integral_const_mul]

/-- Rewrite `I₂' + I₄' + I₆'` as an imaginary-axis integral of `Φ₅'` over `t ≥ 1`. -/
public lemma I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail {u : ℝ} (hu : 2 < u) :
    MagicFunction.a.RealIntegrals.I₂' u + MagicFunction.a.RealIntegrals.I₄' u +
        MagicFunction.a.RealIntegrals.I₆' u =
      (Complex.I : ℂ) *
        ((Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) +
              Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) *
          (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) := by
  rw [I₂'_eq_deform_imag_axis hu, I₄'_eq_deform_imag_axis hu, I₆'_eq_deform_imag_axis hu,
    ray_integral_eq_const_mul_central
      (G := fun t => Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I))
      (E := Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)))
      (fun t _ => by simpa [mul_assoc] using Φ₁'_shift_left (u := u) (t := t)),
    ray_integral_eq_const_mul_central
      (G := fun t => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I))
      (E := Complex.exp (((π * u : ℝ) : ℂ) * Complex.I))
      (fun t _ => by simpa [mul_assoc] using Φ₃'_shift_right (u := u) (t := t))]
  simp [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm]; ring

end MagicFunction.g.CohnElkies.IntegralReps
