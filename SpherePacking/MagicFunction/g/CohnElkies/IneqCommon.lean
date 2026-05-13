module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
import SpherePacking.MagicFunction.b.PsiBounds
public import SpherePacking.ModularForms.FG.Basic

/-! # Common imaginary-axis identities relating `A`, `B` to modular forms `F`, `G`, `Δ`. -/

namespace MagicFunction.g.CohnElkies

open scoped UpperHalfPlane
open Real Complex

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

end MagicFunction.g.CohnElkies
