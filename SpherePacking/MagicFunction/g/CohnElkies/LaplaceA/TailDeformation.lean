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

lemma tendsto_sq_mul_exp_neg_mul_atTop_nhds_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t)) atTop (𝓝 0) := by
  simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (2 : ℝ)) (b := a) ha

private lemma norm_real_add_mul_I_le_two_mul {a t : ℝ} (ha : ‖((a : ℝ) : ℂ)‖ ≤ (1 : ℝ))
    (ht : (1 : ℝ) ≤ t) :
    ‖((a : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ≤ 2 * t := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have hIt : ‖(t : ℂ) * Complex.I‖ = t := by
    simp [Complex.norm_real, abs_of_nonneg ht0]
  calc
    ‖((a : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖((a : ℝ) : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ :=
        norm_add_le _ _
    _ ≤ (1 : ℝ) + t := add_le_add ha (le_of_eq hIt)
    _ ≤ 2 * t := by linarith

/-- Uniform strip bound for `Φ₂' u (x + tI)` with `x ∈ [-1,0]` and `t ≥ 1`. -/
lemma norm_Φ₂'_strip_le {u x t : ℝ} {Cφ Aφ C₀ : ℝ}
    (hC₀_pos : 0 < C₀)
    (hC₀ :
      ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd :
      ∀ z : ℍ, Aφ ≤ z.im →
        ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
          ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (hx0 : -1 ≤ x) (hx1 : x ≤ 0) (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t) :
    ‖Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
  let a : ℝ := π * (u - 2)
  let K : ℝ :=
    (4 * C₀ + (2 * c12π + c36π2) * Cφ)
  -- Work with `w = (x+1) + i*t`.
  let w : ℂ := ((x + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hwpos : 0 < w.im := by simpa [w] using ht0
  have hw_im : w.im = t := by simp [w]
  have hxa : ‖((x + 1 : ℝ) : ℂ)‖ ≤ (1 : ℝ) := by
    have hx01 : 0 ≤ x + 1 ∧ x + 1 ≤ (1 : ℝ) := by
      constructor <;> linarith
    have habs : |x + 1| ≤ (1 : ℝ) := by
      simpa [abs_of_nonneg hx01.1] using hx01.2
    simpa only [Complex.norm_real] using habs
  have hw_norm : ‖w‖ ≤ 2 * t := by
    simpa [w] using norm_real_add_mul_I_le_two_mul (a := x + 1) (t := t) hxa ht1
  let wH : ℍ := ⟨w, by simpa [hw_im] using ht0⟩
  have hwH_im : wH.im = t := by
    simpa [wH] using hw_im
  have hmod :
      ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
        K * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
    have hw' : ‖(wH : ℂ)‖ ≤ 2 * t := by simpa [wH] using hw_norm
    have h :=
      norm_phi0S_mul_sq_le (t := t) wH hwH_im (Cφ := Cφ) (Aφ := Aφ) (C₀ := C₀)
        hC₀_pos hC₀ hφbd ht1 htAφ hw'
    simpa [K] using h
  let zExp : ℂ :=
    (π : ℂ) * Complex.I * (u : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I)
  have hExpNorm :
      ‖cexp zExp‖ = Real.exp (-π * u * t) := by
    have harg :
        zExp =
          ((π * u * x : ℝ) : ℂ) * Complex.I - ((π * u * t : ℝ) : ℂ) := by
      dsimp [zExp]
      ring_nf
      simp [mul_left_comm, mul_comm, sub_eq_add_neg]
    have hnorm := Complex.norm_exp zExp
    -- `‖exp z‖ = exp(re z)` and `re(z) = -π*u*t`.
    simpa [harg, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] using
      hnorm
  have hExpRew :
      Real.exp (2 * π * t) * Real.exp (-π * u * t) = Real.exp (-a * t) := by
    simpa [a, mul_assoc, mul_left_comm, mul_comm] using
      (MagicFunction.g.CohnElkies.IntegralReps.exp_two_pi_mul_mul_exp_neg_pi_mul (u := u) (t := t))
  have hdef :
      Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I) =
        (φ₀'' ((-1 : ℂ) / (w)) * (w ^ (2 : ℕ))) *
          cexp zExp := by
    have : (x : ℂ) + (t : ℂ) * Complex.I + 1 = w := by
      simp [w, add_assoc, add_left_comm, add_comm]
    simp [MagicFunction.a.ComplexIntegrands.Φ₂', MagicFunction.a.ComplexIntegrands.Φ₁', this,
      zExp, mul_assoc]
  have hphi0S :
      φ₀'' ((-1 : ℂ) / w) * (w ^ (2 : ℕ)) =
        φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ)) := by
    have hwS : φ₀ (ModularGroup.S • wH) = φ₀'' ((ModularGroup.S • wH : ℍ) : ℂ) := by
      simp
    have harg : ((ModularGroup.S • wH : ℍ) : ℂ) = (-1 : ℂ) / (wH : ℂ) := by
      simpa using (ModularGroup.coe_S_smul (z := wH))
    have hw : (wH : ℂ) = w := by
      simp [wH]
    -- Rewrite RHS into the common `φ₀'' (-1 / w) * w^2` form.
    rw [hwS, harg, hw]
  have hΦ :
      ‖Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        K * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
    calc
      ‖Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)‖ =
          ‖(φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))) *
                cexp zExp‖ := by
            simp [hdef, hphi0S, mul_assoc]
      _ ≤ ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ *
            ‖cexp zExp‖ := by
            exact norm_mul_le _ _
      _ =
          ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ *
            Real.exp (-π * u * t) := by
            simp [hExpNorm]
      _ ≤ (K * (t ^ (2 : ℕ) * Real.exp (2 * π * t))) * Real.exp (-π * u * t) := by
            exact mul_le_mul_of_nonneg_right hmod (Real.exp_pos _).le
      _ = K * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
            -- Use the exponential identity `exp(2πt) * exp(-πut) = exp(-a t)`.
            calc
              (K * (t ^ (2 : ℕ) * Real.exp (2 * π * t))) * Real.exp (-π * u * t) =
                  K * (t ^ (2 : ℕ) * (Real.exp (2 * π * t) * Real.exp (-π * u * t))) := by
                    ring
              _ = K * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
                    simpa using congrArg (fun x => K * (t ^ (2 : ℕ) * x)) hExpRew
  simpa [K, a] using hΦ

/-- Uniform strip bound for `Φ₄' u (x + tI)` with `x ∈ [0,1]` and `t ≥ 1`. -/
lemma norm_Φ₄'_strip_le {u x t : ℝ} {Cφ Aφ C₀ : ℝ}
    (hC₀_pos : 0 < C₀)
    (hC₀ :
      ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd :
      ∀ z : ℍ, Aφ ≤ z.im →
        ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
          ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t) :
    ‖Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
  -- Reduce to the previous bound by working with `w = (x-1) + i*t`.
  have hx0' : -1 ≤ x - 1 := by linarith
  have hx1' : x - 1 ≤ 0 := by linarith
  -- The proof mirrors `norm_Φ₂'_strip_le` with `z-1` in place of `z+1`.
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
  let a : ℝ := π * (u - 2)
  let K : ℝ :=
    (4 * C₀ + (2 * c12π + c36π2) * Cφ)
  let w : ℂ := ((x - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hwpos : 0 < w.im := by simpa [w] using ht0
  have hw_im : w.im = t := by simp [w]
  have hxa : ‖((x - 1 : ℝ) : ℂ)‖ ≤ (1 : ℝ) := by
    have hx01 : 0 ≤ 1 - x ∧ 1 - x ≤ (1 : ℝ) := by
      constructor <;> linarith
    have habs : |x - 1| ≤ (1 : ℝ) := by
      have habs' : |x - 1| = |1 - x| := by simpa using (abs_sub_comm x 1)
      simpa [habs', abs_of_nonneg hx01.1] using hx01.2
    simpa only [Complex.norm_real] using habs
  have hw_norm : ‖w‖ ≤ 2 * t := by
    simpa [w] using norm_real_add_mul_I_le_two_mul (a := x - 1) (t := t) hxa ht1
  let wH : ℍ := ⟨w, by simpa [hw_im] using ht0⟩
  have hwH_im : wH.im = t := by
    simpa [wH] using hw_im
  have hmod :
      ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
        K * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
    have hw' : ‖(wH : ℂ)‖ ≤ 2 * t := by simpa [wH] using hw_norm
    have h :=
      norm_phi0S_mul_sq_le (t := t) wH hwH_im (Cφ := Cφ) (Aφ := Aφ) (C₀ := C₀)
        hC₀_pos hC₀ hφbd ht1 htAφ hw'
    simpa [K] using h
  let zExp : ℂ :=
    (π : ℂ) * Complex.I * (u : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I)
  have hExpNorm :
      ‖cexp zExp‖ = Real.exp (-π * u * t) := by
    -- Same computation as in `norm_Φ₂'_strip_le`.
    have harg :
        zExp =
          ((π * u * x : ℝ) : ℂ) * Complex.I - ((π * u * t : ℝ) : ℂ) := by
      dsimp [zExp]
      ring_nf
      simp [mul_left_comm, mul_comm, sub_eq_add_neg]
    have hnorm := Complex.norm_exp zExp
    simpa [harg, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] using
      hnorm
  have hExpRew :
      Real.exp (2 * π * t) * Real.exp (-π * u * t) = Real.exp (-a * t) := by
    simpa [a, mul_assoc, mul_left_comm, mul_comm] using
      (MagicFunction.g.CohnElkies.IntegralReps.exp_two_pi_mul_mul_exp_neg_pi_mul (u := u) (t := t))
  have hdef :
      Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I) =
        (φ₀'' ((-1 : ℂ) / (w)) * (w ^ (2 : ℕ))) *
          cexp zExp := by
    have : (x : ℂ) + (t : ℂ) * Complex.I - 1 = w := by
      simp [w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    simp [MagicFunction.a.ComplexIntegrands.Φ₄', MagicFunction.a.ComplexIntegrands.Φ₃', this,
      zExp, mul_assoc]
  have hphi0S :
      φ₀'' ((-1 : ℂ) / w) * (w ^ (2 : ℕ)) =
        φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ)) := by
    have hwS : φ₀ (ModularGroup.S • wH) = φ₀'' ((ModularGroup.S • wH : ℍ) : ℂ) := by
      simp
    have harg : ((ModularGroup.S • wH : ℍ) : ℂ) = (-1 : ℂ) / (wH : ℂ) := by
      simpa using (ModularGroup.coe_S_smul (z := wH))
    have hw : (wH : ℂ) = w := by
      simp [wH]
    rw [hwS, harg, hw]
  have hΦ :
      ‖Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        K * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
    calc
      ‖Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)‖ =
          ‖(φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))) *
                cexp zExp‖ := by
            simp [hdef, hphi0S, mul_assoc]
      _ ≤ ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ *
            ‖cexp zExp‖ := by
            exact norm_mul_le _ _
      _ =
          ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ *
            Real.exp (-π * u * t) := by
            simp [hExpNorm]
      _ ≤ (K * (t ^ (2 : ℕ) * Real.exp (2 * π * t))) * Real.exp (-π * u * t) := by
            exact mul_le_mul_of_nonneg_right hmod (Real.exp_pos _).le
      _ = K * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
            calc
              (K * (t ^ (2 : ℕ) * Real.exp (2 * π * t))) * Real.exp (-π * u * t) =
                  K * (t ^ (2 : ℕ) * (Real.exp (2 * π * t) * Real.exp (-π * u * t))) := by
                    ring
              _ = K * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
                    simpa using congrArg (fun x => K * (t ^ (2 : ℕ) * x)) hExpRew
  simpa [K, a] using hΦ

/-- Top-edge decay needed for the left rectangle deformation (`Φ₂'`). -/
lemma tendsto_intervalIntegral_Φ₂'_top {u : ℝ} (hu : 2 < u) :
    Tendsto
      (fun m : ℝ => ∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + (m : ℂ) * Complex.I))
      atTop (𝓝 0) := by
  rcases exists_phi2'_phi4'_bound_exp with ⟨Cφ, Aφ, hCφ, hφbd⟩
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  let K : ℝ :=
    (4 * C₀ + (2 * c12π + c36π2) * Cφ)
  let a : ℝ := π * (u - 2)
  have ha : 0 < a := mul_pos Real.pi_pos (sub_pos.2 hu)
  have htendBase : Tendsto (fun m : ℝ => m ^ (2 : ℕ) * Real.exp (-a * m)) atTop (𝓝 0) :=
    tendsto_sq_mul_exp_neg_mul_atTop_nhds_zero a ha
  have htend : Tendsto (fun m : ℝ => K * (m ^ (2 : ℕ) * Real.exp (-a * m))) atTop (𝓝 0) :=
    by simpa [mul_zero] using (tendsto_const_nhds.mul htendBase)
  have hbound :
      ∀ᶠ m : ℝ in atTop,
        ‖∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + (m : ℂ) * Complex.I)‖ ≤
          K * (m ^ (2 : ℕ) * Real.exp (-a * m)) := by
    refine (Filter.eventually_atTop.2 ⟨max 1 Aφ, ?_⟩)
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := le_trans (le_max_left _ _) hm
    have hmA : Aφ ≤ m := le_trans (le_max_right _ _) hm
    have hnorm :
        ∀ x ∈ Set.uIoc (-1 : ℝ) 0,
          ‖Φ₂' u ((x : ℂ) + (m : ℂ) * Complex.I)‖ ≤
            K * (m ^ (2 : ℕ) * Real.exp (-a * m)) := by
      intro x hx
      have hle : (-1 : ℝ) ≤ 0 := by norm_num
      have hx' : x ∈ Set.Ioc (-1 : ℝ) 0 := by
        simpa [Set.uIoc_of_le hle] using hx
      have hx0 : -1 ≤ x := le_of_lt hx'.1
      have hx1 : x ≤ 0 := hx'.2
      simpa [K, a, mul_assoc] using
        (norm_Φ₂'_strip_le (u := u) (x := x) (t := m) (Cφ := Cφ) (Aφ := Aφ) (C₀ := C₀)
          hC₀_pos hC₀ hφbd hx0 hx1 hm1 hmA)
    -- Apply the uniform bound on `Ι (-1) 0`.
    simpa using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := (0 : ℝ))
        (f := fun x : ℝ => Φ₂' u ((x : ℂ) + (m : ℂ) * Complex.I))
        (C := K * (m ^ (2 : ℕ) * Real.exp (-a * m))) hnorm
  -- Convert the norm estimate to a `Tendsto` statement.
  refine (tendsto_zero_iff_norm_tendsto_zero).2 ?_
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
      htend (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound

/-- Top-edge decay needed for the right rectangle deformation (`Φ₄'`). -/
lemma tendsto_intervalIntegral_Φ₄'_top {u : ℝ} (hu : 2 < u) :
    Tendsto
      (fun m : ℝ => ∫ x in (1 : ℝ)..0, Φ₄' u ((x : ℂ) + (m : ℂ) * Complex.I))
      atTop (𝓝 0) := by
  rcases exists_phi2'_phi4'_bound_exp with ⟨Cφ, Aφ, hCφ, hφbd⟩
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  let K : ℝ :=
    (4 * C₀ + (2 * c12π + c36π2) * Cφ)
  let a : ℝ := π * (u - 2)
  have ha : 0 < a := mul_pos Real.pi_pos (sub_pos.2 hu)
  have htendBase : Tendsto (fun m : ℝ => m ^ (2 : ℕ) * Real.exp (-a * m)) atTop (𝓝 0) :=
    tendsto_sq_mul_exp_neg_mul_atTop_nhds_zero a ha
  have htend : Tendsto (fun m : ℝ => K * (m ^ (2 : ℕ) * Real.exp (-a * m))) atTop (𝓝 0) :=
    by simpa [mul_zero] using (tendsto_const_nhds.mul htendBase)
  have hbound :
      ∀ᶠ m : ℝ in atTop,
        ‖∫ x in (1 : ℝ)..0, Φ₄' u ((x : ℂ) + (m : ℂ) * Complex.I)‖ ≤
          K * (m ^ (2 : ℕ) * Real.exp (-a * m)) := by
    refine (Filter.eventually_atTop.2 ⟨max 1 Aφ, ?_⟩)
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := le_trans (le_max_left _ _) hm
    have hmA : Aφ ≤ m := le_trans (le_max_right _ _) hm
    have hnorm :
        ∀ x ∈ Set.uIoc (1 : ℝ) 0,
          ‖Φ₄' u ((x : ℂ) + (m : ℂ) * Complex.I)‖ ≤
            K * (m ^ (2 : ℕ) * Real.exp (-a * m)) := by
      intro x hx
      have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
        -- `uIoc 1 0 = Ioc 0 1`.
        simpa [Set.uIoc_of_ge (show (0 : ℝ) ≤ 1 by norm_num)] using hx
      have hx0 : 0 ≤ x := le_of_lt hx'.1
      have hx1 : x ≤ 1 := hx'.2
      simpa [K, a, mul_assoc] using
        (norm_Φ₄'_strip_le (u := u) (x := x) (t := m) (Cφ := Cφ) (Aφ := Aφ) (C₀ := C₀)
          hC₀_pos hC₀ hφbd hx0 hx1 hm1 hmA)
    simpa using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 : ℝ)) (b := (0 : ℝ))
        (f := fun x : ℝ => Φ₄' u ((x : ℂ) + (m : ℂ) * Complex.I))
        (C := K * (m ^ (2 : ℕ) * Real.exp (-a * m))) hnorm
  refine (tendsto_zero_iff_norm_tendsto_zero).2 ?_
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
      htend (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound

lemma I₂'_eq_intervalIntegral_bottom (u : ℝ) :
    MagicFunction.a.RealIntegrals.I₂' u =
      ∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + Complex.I) := by
  -- Unfold `I₂'`/`Φ₂` and change variables `x = t - 1`.
  dsimp [MagicFunction.a.RealIntegrals.I₂', MagicFunction.a.RealIntegrands.Φ₂]
  let g : ℝ → ℂ := fun x : ℝ => Φ₂' u ((x : ℂ) + Complex.I)
  have hcongr :
      (∫ t in (0 : ℝ)..1, Φ₂' u (MagicFunction.Parametrisations.z₂' t)) =
        ∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ)) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
    have hz :
        MagicFunction.Parametrisations.z₂' t =
          (-1 : ℂ) + (t : ℂ) + (Complex.I : ℂ) := by
      simpa using (MagicFunction.Parametrisations.z₂'_eq_of_mem (t := t) ht')
    have hcast : ((t + (-1 : ℝ) : ℝ) : ℂ) = (t : ℂ) + (-1 : ℂ) := by
      norm_cast
    dsimp [g]
    simp [hz, hcast, add_comm]
  have hshift :
      (∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ))) = ∫ x in (-1 : ℝ)..0, g x := by
    simp
      (config := { zeta := false })
      [intervalIntegral.integral_comp_add_right
        (f := g) (a := (0 : ℝ)) (b := (1 : ℝ)) (-1 : ℝ)]
  calc
    (∫ t in (0 : ℝ)..1, Φ₂' u (MagicFunction.Parametrisations.z₂' t)) =
        ∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ)) := hcongr
    _ = ∫ x in (-1 : ℝ)..0, g x := hshift
    _ = ∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + Complex.I) := by
        simp [g]

lemma I₄'_eq_intervalIntegral_bottom (u : ℝ) :
    MagicFunction.a.RealIntegrals.I₄' u =
      ∫ x in (1 : ℝ)..0, Φ₄' u ((x : ℂ) + Complex.I) := by
  -- Unfold `I₄'`/`Φ₄` and change variables `x = 1 - t`, then reverse orientation.
  dsimp [MagicFunction.a.RealIntegrals.I₄', MagicFunction.a.RealIntegrands.Φ₄]
  let g : ℝ → ℂ := fun x : ℝ => Φ₄' u ((x : ℂ) + Complex.I)
  have hrew :
      (∫ t in (0 : ℝ)..1, (-1 : ℂ) * Φ₄' u (MagicFunction.Parametrisations.z₄' t)) =
        ∫ t in (0 : ℝ)..1, (-1 : ℂ) * g (1 - t) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
    have hz :
        MagicFunction.Parametrisations.z₄' t =
          (1 : ℂ) - (t : ℂ) + (Complex.I : ℂ) := by
      simpa using (MagicFunction.Parametrisations.z₄'_eq_of_mem (t := t) ht')
    dsimp [g]
    simp [hz, sub_eq_add_neg]
  rw [hrew]
  have hcomp : (∫ t in (0 : ℝ)..1, g (1 - t)) = ∫ t in (0 : ℝ)..1, g t := by
    have h :=
      intervalIntegral.integral_comp_sub_left
        (f := g) (a := (0 : ℝ)) (b := (1 : ℝ)) (d := (1 : ℝ))
    calc
      (∫ t in (0 : ℝ)..1, g (1 - t)) = ∫ t in (1 : ℝ) - 1..(1 : ℝ) - 0, g t := h
      _ = ∫ t in (0 : ℝ)..1, g t := by simp
  calc
    ∫ t in (0 : ℝ)..1, (-1 : ℂ) * g (1 - t)
        = (-1 : ℂ) * ∫ t in (0 : ℝ)..1, g (1 - t) := by simp
    _ = (-1 : ℂ) * ∫ t in (0 : ℝ)..1, g t := by rw [hcomp]
    _ = -∫ t in (0 : ℝ)..1, g t := by simp
    _ = ∫ t in (1 : ℝ)..0, g t := by
          simpa using
            (intervalIntegral.integral_symm (a := (0 : ℝ)) (b := (1 : ℝ)) (f := g)).symm

private lemma bottom_eq_I_smul_sub_of_rect_deform {f : ℂ → ℂ} {x₁ x₂ : ℝ}
    (hcontU : ContinuousOn f {z : ℂ | 0 < z.im})
    (hdiffU : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hint₁ :
      IntegrableOn
        (fun t : ℝ => f ((x₁ : ℂ) + (t : ℂ) * Complex.I))
        (Set.Ioi (1 : ℝ)) volume)
    (hint₂ :
      IntegrableOn
        (fun t : ℝ => f ((x₂ : ℂ) + (t : ℂ) * Complex.I))
        (Set.Ioi (1 : ℝ)) volume)
    (htop :
      Tendsto
        (fun m : ℝ => ∫ x in x₁..x₂, f ((x : ℂ) + (m : ℂ) * Complex.I))
        atTop (𝓝 0)) :
    (∫ x in x₁..x₂, f ((x : ℂ) + Complex.I)) =
      (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), f ((x₁ : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), f ((x₂ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hStrip : (Set.uIcc x₁ x₂ ×ℂ Set.Ici (1 : ℝ)) ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    rcases (by simpa [mem_reProdIm] using hz :
        z.re ∈ Set.uIcc x₁ x₂ ∧ z.im ∈ Set.Ici (1 : ℝ)) with ⟨-, hz⟩
    exact lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) (by simpa [Set.mem_Ici] using hz)
  have hcont : ContinuousOn f (Set.uIcc x₁ x₂ ×ℂ Set.Ici (1 : ℝ)) := hcontU.mono hStrip
  have hdiff :
      ∀ z ∈ (Set.Ioo (min x₁ x₂) (max x₁ x₂) ×ℂ Set.Ioi (1 : ℝ)),
        DifferentiableAt ℂ f z := by
    intro z hz
    have hz' :
        z.re ∈ Set.Ioo (min x₁ x₂) (max x₁ x₂) ∧ z.im ∈ Set.Ioi (1 : ℝ) := by
      simpa [mem_reProdIm] using hz
    have hz0 : 0 < z.im :=
      lt_trans (by norm_num : (0 : ℝ) < 1) (by simpa [Set.mem_Ioi] using hz'.2)
    exact (hdiffU z hz0).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hz0)
  have hrect :=
    Complex.rect_deform_of_tendsto_top (f := f) (x₁ := x₁) (x₂ := x₂) (y := (1 : ℝ))
      hcont hdiff hint₁ hint₂ htop
  simpa [smul_eq_mul, mul_sub, one_mul] using
    eq_sub_of_add_eq (by simpa [one_mul] using (sub_eq_zero.mp hrect))

lemma I₂'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    MagicFunction.a.RealIntegrals.I₂' u =
      (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((t : ℂ) * Complex.I)) := by
  have hcontΦ2 : ContinuousOn (Φ₂' u) {z : ℂ | 0 < z.im} :=
    (MagicFunction.a.ComplexIntegrands.Φ₁'_contDiffOn_ℂ (r := u)).continuousOn
  have hdiffΦ2 : DifferentiableOn ℂ (Φ₂' u) {z : ℂ | 0 < z.im} :=
    (MagicFunction.a.ComplexIntegrands.Φ₁'_contDiffOn_ℂ (r := u)).differentiableOn (by simp)
  have hint₁ :
      IntegrableOn
        (fun t : ℝ => Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I))
        (Set.Ioi (1 : ℝ)) volume := by
    -- Shift to the `Φ₅'`-ray.
    let E : ℂ := Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I))
    have hcongr :
        (fun t : ℝ => Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) =
          fun t : ℝ => E * Φ₅' u ((t : ℂ) * Complex.I) := by
      funext t
      simpa [E, mul_assoc, add_assoc, add_comm, add_left_comm] using
        (Φ₁'_shift_left (u := u) (t := t))
    simpa [hcongr, mul_assoc] using (integrableOn_Φ₅'_imag_axis (u := u) hu).const_mul E
  have hint₂ :
      IntegrableOn
        (fun t : ℝ => Φ₂' u ((0 : ℂ) + (t : ℂ) * Complex.I))
        (Set.Ioi (1 : ℝ)) volume := by
    simpa [mul_assoc] using integrableOn_Φ₂'_imag_axis (u := u) hu
  have htop :
      Tendsto
        (fun m : ℝ => ∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + (m : ℂ) * Complex.I))
        atTop (𝓝 0) :=
    tendsto_intervalIntegral_Φ₂'_top (u := u) hu
  have hbottom :
      (∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + (1 : ℂ) * Complex.I)) =
        (Complex.I : ℂ) •
          ((∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) -
            ∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((0 : ℂ) + (t : ℂ) * Complex.I)) := by
    simpa using
      (bottom_eq_I_smul_sub_of_rect_deform (f := Φ₂' u) (x₁ := (-1 : ℝ)) (x₂ := (0 : ℝ))
        hcontΦ2 hdiffΦ2 (by simpa using hint₁) (by simpa using hint₂) htop)
  -- Replace `I₂'` by the bottom-edge integral and simplify the `x = 0` ray.
  rw [I₂'_eq_intervalIntegral_bottom (u := u)]
  simpa [zero_add] using hbottom

lemma I₄'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    MagicFunction.a.RealIntegrals.I₄' u =
      (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((t : ℂ) * Complex.I)) := by
  have hcontΦ4 : ContinuousOn (Φ₄' u) {z : ℂ | 0 < z.im} :=
    (MagicFunction.a.ComplexIntegrands.Φ₃'_contDiffOn_ℂ (r := u)).continuousOn
  have hdiffΦ4 : DifferentiableOn ℂ (Φ₄' u) {z : ℂ | 0 < z.im} :=
    (MagicFunction.a.ComplexIntegrands.Φ₃'_contDiffOn_ℂ (r := u)).differentiableOn (by simp)
  have hint₁ :
      IntegrableOn
        (fun t : ℝ => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I))
        (Set.Ioi (1 : ℝ)) volume := by
    let E : ℂ := Complex.exp (((π * u : ℝ) : ℂ) * Complex.I)
    have hcongr :
        (fun t : ℝ => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) =
          fun t : ℝ => E * Φ₅' u ((t : ℂ) * Complex.I) := by
      funext t
      simpa [E, mul_assoc, add_assoc, add_comm, add_left_comm] using
        (Φ₃'_shift_right (u := u) (t := t))
    simpa [hcongr, mul_assoc] using (integrableOn_Φ₅'_imag_axis (u := u) hu).const_mul E
  have hint₂ :
      IntegrableOn
        (fun t : ℝ => Φ₄' u ((0 : ℂ) + (t : ℂ) * Complex.I))
        (Set.Ioi (1 : ℝ)) volume := by
    simpa [mul_assoc] using integrableOn_Φ₄'_imag_axis (u := u) hu
  have htop :
      Tendsto
        (fun m : ℝ => ∫ x in (1 : ℝ)..0, Φ₄' u ((x : ℂ) + (m : ℂ) * Complex.I))
        atTop (𝓝 0) :=
    tendsto_intervalIntegral_Φ₄'_top (u := u) hu
  have hbottom :
      (∫ x in (1 : ℝ)..0, Φ₄' u ((x : ℂ) + (1 : ℂ) * Complex.I)) =
        (Complex.I : ℂ) •
          ((∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) -
            ∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((0 : ℂ) + (t : ℂ) * Complex.I)) := by
    simpa using
      (bottom_eq_I_smul_sub_of_rect_deform (f := Φ₄' u) (x₁ := (1 : ℝ)) (x₂ := (0 : ℝ))
        hcontΦ4 hdiffΦ4 (by simpa using hint₁) (by simpa using hint₂) htop)
  rw [I₄'_eq_intervalIntegral_bottom (u := u)]
  simpa [zero_add] using hbottom

lemma I₆'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    MagicFunction.a.RealIntegrals.I₆' u =
      (Complex.I : ℂ) *
        ((∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((t : ℂ) * Complex.I)) -
            2 * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) +
              ∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((t : ℂ) * Complex.I)) := by
  -- Start from the definition of `I₆'` and rewrite the parametrization.
  have hI6 :
      MagicFunction.a.RealIntegrals.I₆' u =
        (2 : ℂ) *
          ∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I) := by
    dsimp [MagicFunction.a.RealIntegrals.I₆', MagicFunction.a.RealIntegrands.Φ₆]
    have hcongr :
        (∫ t in Set.Ici (1 : ℝ),
              (Complex.I : ℂ) * Φ₆' u (MagicFunction.Parametrisations.z₆' t)) =
          ∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I) := by
      refine MeasureTheory.setIntegral_congr_fun (s := Set.Ici (1 : ℝ)) measurableSet_Ici ?_
      intro t ht
      have hz : MagicFunction.Parametrisations.z₆' t = (Complex.I : ℂ) * (t : ℂ) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          (MagicFunction.Parametrisations.z₆'_eq_of_mem (t := t) ht)
      simp [hz, mul_comm]
    -- Replace `z₆' t` with `t * I` and remove the endpoint `t = 1`.
    rw [hcongr]
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  -- Move `2` inside the integrand.
  have hI6' :
      (2 : ℂ) * ∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I) =
        ∫ t in Set.Ioi (1 : ℝ),
          (2 : ℂ) * ((Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I)) := by
    -- Use `integral_const_mul` on the restricted measure.
    simpa using
      (MeasureTheory.integral_const_mul (μ := volume.restrict (Set.Ioi (1 : ℝ))) (r := (2 : ℂ))
        (f := fun t : ℝ => (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I))).symm
  -- Use the finite-difference identity on the imaginary axis.
  have hfd_int :
      (∫ t in Set.Ioi (1 : ℝ),
            (2 : ℂ) * ((Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I))) =
        ∫ t in Set.Ioi (1 : ℝ),
          (Complex.I : ℂ) *
            (Φ₂' u ((t : ℂ) * Complex.I) - 2 * Φ₅' u ((t : ℂ) * Complex.I) +
              Φ₄' u ((t : ℂ) * Complex.I)) := by
    refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (1 : ℝ)) measurableSet_Ioi ?_
    intro t ht
    have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1) ht
    have hfd := Φ_finite_difference_imag_axis (u := u) (t := t) ht0
    -- Multiply `Φ₂' - 2Φ₅' + Φ₄' = 2Φ₆'` by `I`.
    have hfdI :=
      congrArg (fun z : ℂ => (Complex.I : ℂ) * z) hfd
    simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using hfdI.symm
  -- Split the integral and pull out the outer factor `I`.
  have hlin :
      (∫ t in Set.Ioi (1 : ℝ),
            (Complex.I : ℂ) *
              (Φ₂' u ((t : ℂ) * Complex.I) - 2 * Φ₅' u ((t : ℂ) * Complex.I) +
                Φ₄' u ((t : ℂ) * Complex.I))) =
        (Complex.I : ℂ) *
          ((∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((t : ℂ) * Complex.I)) -
              2 * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) +
                ∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((t : ℂ) * Complex.I)) := by
    -- Work on the restricted measure `μ = volume.restrict (Ioi 1)`.
    let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
    let f2 : ℝ → ℂ := fun t : ℝ => Φ₂' u ((t : ℂ) * Complex.I)
    let f5 : ℝ → ℂ := fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)
    let f4 : ℝ → ℂ := fun t : ℝ => Φ₄' u ((t : ℂ) * Complex.I)
    have hf2 : Integrable f2 μ := by
      simpa [IntegrableOn, μ, f2] using (integrableOn_Φ₂'_imag_axis (u := u) hu)
    have hf5 : Integrable f5 μ := by
      simpa [IntegrableOn, μ, f5] using (integrableOn_Φ₅'_imag_axis (u := u) hu)
    have hf4 : Integrable f4 μ := by
      simpa [IntegrableOn, μ, f4] using (integrableOn_Φ₄'_imag_axis (u := u) hu)
    have hf5' : Integrable (fun t : ℝ => (2 : ℂ) * f5 t) μ := hf5.const_mul (2 : ℂ)
    have hsub : Integrable (fun t : ℝ => f2 t - (2 : ℂ) * f5 t) μ := hf2.sub hf5'
    have hadd : Integrable (fun t : ℝ => (f2 t - (2 : ℂ) * f5 t) + f4 t) μ := hsub.add hf4
    have hinter :
        (∫ t, (f2 t - (2 : ℂ) * f5 t) + f4 t ∂μ) =
          (∫ t, f2 t ∂μ) - (2 : ℂ) * (∫ t, f5 t ∂μ) + ∫ t, f4 t ∂μ := by
      calc
        (∫ t, (f2 t - (2 : ℂ) * f5 t) + f4 t ∂μ) =
            (∫ t, (f2 t - (2 : ℂ) * f5 t) ∂μ) + ∫ t, f4 t ∂μ := by
              simpa using (MeasureTheory.integral_add hsub hf4)
        _ = ((∫ t, f2 t ∂μ) - ∫ t, (2 : ℂ) * f5 t ∂μ) + ∫ t, f4 t ∂μ := by
              simpa using congrArg (fun z : ℂ => z + ∫ t, f4 t ∂μ)
                (MeasureTheory.integral_sub hf2 hf5')
        _ = ((∫ t, f2 t ∂μ) - ((2 : ℂ) * ∫ t, f5 t ∂μ)) + ∫ t, f4 t ∂μ := by
              rw [MeasureTheory.integral_const_mul (μ := μ) (r := (2 : ℂ)) (f := f5)]
        _ = (∫ t, f2 t ∂μ) - (2 : ℂ) * (∫ t, f5 t ∂μ) + ∫ t, f4 t ∂μ := by ring
    -- Put everything back into `setIntegral` notation and pull out the leading `I`.
    have hinner :
        (∫ t in Set.Ioi (1 : ℝ), f2 t - (2 : ℂ) * f5 t + f4 t) =
          (∫ t in Set.Ioi (1 : ℝ), f2 t) - (2 : ℂ) * (∫ t in Set.Ioi (1 : ℝ), f5 t) +
            ∫ t in Set.Ioi (1 : ℝ), f4 t := by
      -- This is exactly `hinter`, rewritten through `μ`.
      simpa [μ, sub_eq_add_neg, add_assoc, f2, f5, f4] using hinter
    -- Now pull out `I` and rewrite the integrand to match `f2 - 2*f5 + f4`.
    have hI :
        (∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * (f2 t - (2 : ℂ) * f5 t + f4 t)) =
          (Complex.I : ℂ) * (∫ t in Set.Ioi (1 : ℝ), f2 t - (2 : ℂ) * f5 t + f4 t) := by
      simpa [μ] using (MeasureTheory.integral_const_mul (μ := μ) (r := (Complex.I : ℂ))
        (f := fun t : ℝ => f2 t - (2 : ℂ) * f5 t + f4 t))
    -- Finish.
    calc
      (∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * (f2 t - (2 : ℂ) * f5 t + f4 t)) =
          (Complex.I : ℂ) * (∫ t in Set.Ioi (1 : ℝ), f2 t - (2 : ℂ) * f5 t + f4 t) := hI
      _ =
          (Complex.I : ℂ) *
            ((∫ t in Set.Ioi (1 : ℝ), f2 t) - (2 : ℂ) * (∫ t in Set.Ioi (1 : ℝ), f5 t) +
              ∫ t in Set.Ioi (1 : ℝ), f4 t) := by
            simpa using congrArg (fun z : ℂ => (Complex.I : ℂ) * z) hinner
  -- Combine everything.
  calc
    MagicFunction.a.RealIntegrals.I₆' u
        = (2 : ℂ) *
            ∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I) := hI6
    _ = ∫ t in Set.Ioi (1 : ℝ),
          (2 : ℂ) * ((Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I)) := hI6'
    _ = ∫ t in Set.Ioi (1 : ℝ),
          (Complex.I : ℂ) *
            (Φ₂' u ((t : ℂ) * Complex.I) - 2 * Φ₅' u ((t : ℂ) * Complex.I) +
              Φ₄' u ((t : ℂ) * Complex.I)) := hfd_int
    _ = (Complex.I : ℂ) *
          ((∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((t : ℂ) * Complex.I)) -
              2 * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) +
                ∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((t : ℂ) * Complex.I)) := hlin

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
  -- Rewrite `I₂'` and `I₄'` via rectangle deformation.
  -- Convert the shifted rays to the central ray using the shift identities.
  have hLeft_ray :
      (∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) =
        Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) *
          (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) := by
    let E : ℂ := Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I))
    have hcongr :
        (∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) =
          ∫ t in Set.Ioi (1 : ℝ),
            E * Φ₅' u ((t : ℂ) * Complex.I) := by
      refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (1 : ℝ)) measurableSet_Ioi ?_
      intro t ht
      simpa [E, mul_assoc] using (Φ₁'_shift_left (u := u) (t := t))
    rw [hcongr]
    simpa [E] using
      (MeasureTheory.integral_const_mul
        (μ := volume.restrict (Set.Ioi (1 : ℝ)))
        (r := E)
        (f := fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)))
  have hRight_ray :
      (∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) =
        Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) *
          (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) := by
    let E : ℂ := Complex.exp (((π * u : ℝ) : ℂ) * Complex.I)
    have hcongr :
        (∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) =
          ∫ t in Set.Ioi (1 : ℝ),
            E * Φ₅' u ((t : ℂ) * Complex.I) := by
      refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (1 : ℝ)) measurableSet_Ioi ?_
      intro t ht
      simpa [E, mul_assoc] using (Φ₃'_shift_right (u := u) (t := t))
    rw [hcongr]
    simpa [E] using
      (MeasureTheory.integral_const_mul
        (μ := volume.restrict (Set.Ioi (1 : ℝ)))
        (r := E)
        (f := fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)))
  -- Combine and simplify; the `Φ₂'`/`Φ₄'` ray integrals cancel via the finite difference.
  -- (This is a purely algebraic rearrangement after rewriting `I₂'`, `I₄'`, `I₆'`.)
  -- Rewrite everything in terms of `∫ Φ₅'` and simplify.
  rw [I₂'_eq_deform_imag_axis (u := u) hu, I₄'_eq_deform_imag_axis (u := u) hu,
    I₆'_eq_deform_imag_axis (u := u) hu]
  -- Replace shifted rays.
  rw [hLeft_ray, hRight_ray]
  -- Final algebraic simplification: turn `•` into multiplication and let `ring` reorder.
  simp [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm]
  ring

end MagicFunction.g.CohnElkies.IntegralReps
