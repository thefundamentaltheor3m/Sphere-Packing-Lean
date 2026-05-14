module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.LaplaceRepresentation
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceB.LaplaceRepresentation
public import SpherePacking.ModularForms.FG.Basic
import SpherePacking.MagicFunction.b.PsiBounds
import SpherePacking.MagicFunction.g.CohnElkies.ImagAxisReal
import SpherePacking.MagicFunction.g.CohnElkies.IntegralB
import SpherePacking.ModularForms.FG.Inequalities


/-!
# Cohn-Elkies sign conditions for `g`

Sign conditions for `g` and `𝓕 g` needed for the Cohn-Elkies LP bound in dimension 8,
corresponding to (g1) and (g2) in `thm:g1`.

## Main statements
* `MagicFunction.g.CohnElkies.gRadial_eq_integral_A`
* `MagicFunction.g.CohnElkies.g_nonpos_of_norm_sq_ge_two`
* `MagicFunction.g.CohnElkies.fourier_g_nonneg`
-/

namespace MagicFunction.g.CohnElkies

open scoped FourierTransform SchwartzMap UpperHalfPlane
open MeasureTheory Real Complex
open MagicFunction.FourierEigenfunctions

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

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
