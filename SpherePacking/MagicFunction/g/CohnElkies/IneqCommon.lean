module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
import SpherePacking.MagicFunction.b.PsiBounds
public import SpherePacking.ModularForms.FG.Basic

/-!
# Common lemmas for `ineqA` and `ineqB`

This file collects identities on the imaginary axis relating the auxiliary functions `A` and `B`
to the modular forms `F`, `G`, and `Δ`. These are used to reduce the sign conditions to the
real inequalities for `FReal` and `GReal`.

## Main definitions
* `MagicFunction.g.CohnElkies.c`: the constant `18 / π^2`.

## Main statements
* `MagicFunction.g.CohnElkies.A_eq_neg_mul_FG_div_Delta`
* `MagicFunction.g.CohnElkies.B_eq_neg_mul_FG_div_Delta`
-/

namespace MagicFunction.g.CohnElkies

open scoped UpperHalfPlane
open Real Complex

noncomputable section

private lemma complex_eq_ofReal_of_im_eq_zero (z : ℂ) (hz : z.im = 0) : z = (z.re : ℂ) := by
  exact Complex.ext (by simp) (by simp [hz])

/-- The constant `c = 18 / π^2` appearing in the definitions of `A` and `B`. -/
public abbrev c : ℝ := 18 * (π ^ (-2 : ℤ))

/-- Express `ψS` in terms of the quotient `G / Δ`. -/
public lemma ψS_eq_neg_half_mul_G_div_Delta (z : ℍ) :
    ψS z = (-(1 / 2 : ℂ)) * (G z) / (Δ z) := by
  have hΔ : Δ z = (H₂ z * H₃ z * H₄ z) ^ 2 / (256 : ℂ) := by
    simpa [Delta_apply, mul_assoc] using (Delta_eq_H₂_H₃_H₄ z)
  rw [MagicFunction.b.PsiBounds.ψS_apply_eq_factor z]
  simp [G, hΔ]
  field_simp [H₂_ne_zero z, H₃_ne_zero z, H₄_ne_zero z]
  ring_nf

/-- Real part of `φ₀'' (I / t)` in terms of `FReal` and the imaginary-axis restriction of `Δ`. -/
public lemma phi0''_re_I_div (t : ℝ) (ht : 0 < t) :
    (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re =
      (FReal (1 / t)) / (Δ.resToImagAxis (1 / t)).re := by
  set s : ℝ := 1 / t
  have hs : 0 < s := one_div_pos.2 ht
  let z : ℍ := ⟨Complex.I * s, by simp [hs]⟩
  have hz : (z : ℂ) = (Complex.I : ℂ) / (t : ℂ) := by
    simp [z, s, div_eq_mul_inv]
  have hF : F z = (FReal s : ℂ) := by
    simpa [Function.resToImagAxis, ResToImagAxis, hs, z] using (F_eq_FReal (t := s) hs)
  have hΔ : Δ z = Δ.resToImagAxis s := by
    simp [Function.resToImagAxis, ResToImagAxis, hs, z]
  have hΔof : Δ.resToImagAxis s = ((Δ.resToImagAxis s).re : ℂ) :=
    complex_eq_ofReal_of_im_eq_zero _ (Delta_imag_axis_pos.1 s hs)
  calc
    (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re = (φ₀ z).re := by
      simpa [hz] using congrArg Complex.re (φ₀''_coe_upperHalfPlane z)
    _ = ((F z) / (Δ z)).re := by simp [φ₀, F]
    _ = ((FReal s : ℂ) / (Δ.resToImagAxis s)).re := by simp [hF, hΔ]
    _ = ((FReal s : ℂ) / ((Δ.resToImagAxis s).re : ℂ)).re := by
      rw [hΔof]
      rfl
    _ = (FReal s) / (Δ.resToImagAxis s).re := by
      rw [(Complex.ofReal_div (FReal s) (Δ.resToImagAxis s).re).symm]
      simp
    _ = (FReal (1 / t)) / (Δ.resToImagAxis (1 / t)).re := by
      simp [s]

/-- Real part of `ψS` on the imaginary axis, written using `GReal` and `Δ`. -/
public lemma ψS_resToImagAxis_re (s : ℝ) (hs : 0 < s) :
    (ψS.resToImagAxis s).re = -(2⁻¹ * GReal s) / (Δ.resToImagAxis s).re := by
  let z : ℍ := ⟨Complex.I * s, by simp [hs]⟩
  have hψ : ψS.resToImagAxis s = (-(1 / 2 : ℂ)) * (G.resToImagAxis s) / (Δ.resToImagAxis s) := by
    simpa [Function.resToImagAxis, ResToImagAxis, hs, z] using (ψS_eq_neg_half_mul_G_div_Delta z)
  have hG : ResToImagAxis G s = (GReal s : ℂ) := by
    simpa [Function.resToImagAxis_apply, GReal] using (G_eq_GReal (t := s) hs)
  have hΔof : Δ.resToImagAxis s = ((Δ.resToImagAxis s).re : ℂ) :=
    complex_eq_ofReal_of_im_eq_zero _ (Delta_imag_axis_pos.1 s hs)
  calc
    (ψS.resToImagAxis s).re = ((-(1 / 2 : ℂ)) * (G.resToImagAxis s) / (Δ.resToImagAxis s)).re := by
          simpa using congrArg Complex.re hψ
    _ = ((-(1 / 2 : ℂ)) * (GReal s : ℂ) / (Δ.resToImagAxis s)).re := by simp [hG]
    _ = ((-(1 / 2 : ℂ)) * (GReal s : ℂ) / ((Δ.resToImagAxis s).re : ℂ)).re := by
      rw [hΔof]
      rfl
    _ = (-(1 / 2 : ℝ)) * (GReal s) / (Δ.resToImagAxis s).re := by simp
    _ = -(2⁻¹ * GReal s) / (Δ.resToImagAxis s).re := by simp [div_eq_mul_inv, mul_assoc]

/-- Relate `ψI' (I * t)` to `ψS` at `1 / t` via the slash-action symmetry. -/
public lemma ψI'_re_mul_I (t : ℝ) (ht : 0 < t) :
    (ψI' ((Complex.I : ℂ) * (t : ℂ))).re =
      -(t ^ (2 : ℕ)) * (ψS.resToImagAxis (1 / t)).re := by
  set s : ℝ := 1 / t
  have hs : 0 < s := one_div_pos.2 ht
  have hψI' : ψI' ((Complex.I : ℂ) * (t : ℂ)) = ψI.resToImagAxis t := by
    simp [ψI', ResToImagAxis, ht]
  have hs' : (1 / s) = t := by simp [s]
  have hψS' : ψS.resToImagAxis s = ((-(s ^ (2 : ℕ)) : ℝ) : ℂ) * ψI.resToImagAxis t := by
    simpa [hs', zpow_ofNat, pow_two, mul_assoc, mul_left_comm, mul_comm] using
      (ResToImagAxis.SlashActionS (F := ψI) (k := (-2 : ℤ)) (t := s) hs)
  have hts : (t ^ (2 : ℕ)) * (s ^ (2 : ℕ)) = (1 : ℝ) := by
    simp [s, ht.ne', pow_two, div_eq_mul_inv, mul_assoc, mul_comm]
  have hψIaxis : ψI.resToImagAxis t = ((-(t ^ (2 : ℕ)) : ℝ) : ℂ) * ψS.resToImagAxis s := by
    have hmul := congrArg (fun w : ℂ => ((-(t ^ (2 : ℕ)) : ℝ) : ℂ) * w) hψS'
    have : ((-(t ^ (2 : ℕ)) : ℝ) : ℂ) * ψS.resToImagAxis s = ψI.resToImagAxis t := by
      calc
        ((-(t ^ (2 : ℕ)) : ℝ) : ℂ) * ψS.resToImagAxis s =
            ((t ^ (2 : ℕ) * s ^ (2 : ℕ) : ℝ) : ℂ) * ψI.resToImagAxis t := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
        _ = (1 : ℂ) * ψI.resToImagAxis t := by simp [hts]
        _ = ψI.resToImagAxis t := by simp
    simpa using this.symm
  calc
    (ψI' ((Complex.I : ℂ) * (t : ℂ))).re
        = (ψI.resToImagAxis t).re := by simpa using congrArg Complex.re hψI'
    _ = (-(t ^ (2 : ℕ)) : ℝ) * (ψS.resToImagAxis s).re := by
      rw [hψIaxis]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    _ = -(t ^ (2 : ℕ)) * (ψS.resToImagAxis (1 / t)).re := by
          simp [s]

/-- Rewrite `A t` as a quotient involving `FReal`, `GReal`, and `Δ` on the imaginary axis. -/
public lemma A_eq_neg_mul_FG_div_Delta (t : ℝ) (ht : 0 < t) :
    A t =
      (-(t ^ (2 : ℕ))) *
        ((FReal (1 / t) + c * GReal (1 / t)) / (Δ.resToImagAxis (1 / t)).re) := by
  set s : ℝ := 1 / t
  have hs : 0 < s := one_div_pos.2 ht
  set Δr : ℝ := (Δ.resToImagAxis s).re
  have hΔr : Δr ≠ 0 := ne_of_gt (Delta_imag_axis_pos.2 s hs)
  have hφ :
      (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re = (FReal s) / Δr := by
    simpa [s, Δr] using (phi0''_re_I_div (t := t) ht)
  have hψS : (ψS.resToImagAxis s).re = -(2⁻¹ * GReal s) / Δr := by
    simpa [Δr] using (ψS_resToImagAxis_re (s := s) hs)
  have hψS' : (ResToImagAxis ψS s).re = -(2⁻¹ * GReal s) / Δr := by
    simpa [Function.resToImagAxis_apply] using hψS
  have hψI :
      (ψI' ((Complex.I : ℂ) * (t : ℂ))).re = -(t ^ (2 : ℕ)) * (ψS.resToImagAxis s).re := by
    simpa [s] using (ψI'_re_mul_I (t := t) ht)
  have hψI' :
      (ψI' ((Complex.I : ℂ) * (t : ℂ))).re = -(t ^ (2 : ℕ)) * (ResToImagAxis ψS s).re := by
    simpa [Function.resToImagAxis_apply] using hψI
  calc
    A t =
        (-(t ^ (2 : ℕ))) * (FReal s / Δr) -
          (36 / (π ^ (2 : ℕ)) : ℝ) * (-(t ^ (2 : ℕ)) * (ψS.resToImagAxis s).re) := by
          simp [A, hφ, hψI']
    _ = (-(t ^ (2 : ℕ))) * (FReal s / Δr) + (t ^ (2 : ℕ)) * (-c) * (GReal s / Δr) := by
          simp [hψS', sub_eq_add_neg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          ring_nf
          have hpi : (π⁻¹ : ℝ) ^ 2 = (π ^ 2)⁻¹ := inv_pow (π : ℝ) 2
          rw [hpi]
          have hswap :
              t ^ 2 * (π ^ 2)⁻¹ * GReal s * Δr⁻¹ = t ^ 2 * GReal s * (π ^ 2)⁻¹ * Δr⁻¹ := by
            exact mul_mul_mul_comm' (t ^ 2) ((π ^ 2)⁻¹) (GReal s) (Δr⁻¹)
          have hcomm :
              t ^ 2 * GReal s * (π ^ 2)⁻¹ * Δr⁻¹ = t ^ 2 * GReal s * Δr⁻¹ * (π ^ 2)⁻¹ := by
            exact mul_right_comm (t ^ 2 * GReal s) ((π ^ 2)⁻¹) (Δr⁻¹)
          have hswap18 :
              t ^ 2 * (π ^ 2)⁻¹ * GReal s * Δr⁻¹ * 18 =
                t ^ 2 * GReal s * (π ^ 2)⁻¹ * Δr⁻¹ * 18 :=
            congrArg (fun x => x * 18) hswap
          have hcomm18 :
              t ^ 2 * GReal s * (π ^ 2)⁻¹ * Δr⁻¹ * 18 =
                t ^ 2 * GReal s * Δr⁻¹ * (π ^ 2)⁻¹ * 18 :=
            congrArg (fun x => x * 18) hcomm
          exact hswap18.trans hcomm18
    _ = (-(t ^ (2 : ℕ))) * ((FReal s + c * GReal s) / Δr) := by
          field_simp [hΔr]
          ring
    _ =
        (-(t ^ (2 : ℕ))) *
          ((FReal (1 / t) + c * GReal (1 / t)) / (Δ.resToImagAxis (1 / t)).re) := by
          simp [s, Δr, Function.resToImagAxis]

/-- Rewrite `B t` as a quotient involving `FReal`, `GReal`, and `Δ` on the imaginary axis. -/
public lemma B_eq_neg_mul_FG_div_Delta (t : ℝ) (ht : 0 < t) :
    B t =
      (-(t ^ (2 : ℕ))) *
        ((FReal (1 / t) - c * GReal (1 / t)) / (Δ.resToImagAxis (1 / t)).re) := by
  set s : ℝ := 1 / t
  have hs : 0 < s := one_div_pos.2 ht
  set Δr : ℝ := (Δ.resToImagAxis s).re
  have hΔr : Δr ≠ 0 := ne_of_gt (Delta_imag_axis_pos.2 s hs)
  have hφ :
      (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re = (FReal s) / Δr := by
    simpa [s, Δr] using (phi0''_re_I_div (t := t) ht)
  have hψS : (ψS.resToImagAxis s).re = -(2⁻¹ * GReal s) / Δr := by
    simpa [Δr] using (ψS_resToImagAxis_re (s := s) hs)
  have hψS' : (ResToImagAxis ψS s).re = -(2⁻¹ * GReal s) / Δr := by
    simpa [Function.resToImagAxis_apply] using hψS
  have hψI :
      (ψI' ((Complex.I : ℂ) * (t : ℂ))).re = -(t ^ (2 : ℕ)) * (ψS.resToImagAxis s).re := by
    simpa [s] using (ψI'_re_mul_I (t := t) ht)
  have hψI' :
      (ψI' ((Complex.I : ℂ) * (t : ℂ))).re = -(t ^ (2 : ℕ)) * (ResToImagAxis ψS s).re := by
    simpa [Function.resToImagAxis_apply] using hψI
  calc
    B t =
        (-(t ^ (2 : ℕ))) * (FReal s / Δr) +
          (36 / (π ^ (2 : ℕ)) : ℝ) * (-(t ^ (2 : ℕ)) * (ψS.resToImagAxis s).re) := by
          simp [B, hφ, hψI']
    _ = (-(t ^ (2 : ℕ))) * (FReal s / Δr) + (t ^ (2 : ℕ)) * c * (GReal s / Δr) := by
          simp [hψS', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          ring_nf
          have hpi : (π⁻¹ : ℝ) ^ 2 = (π ^ 2)⁻¹ := inv_pow (π : ℝ) 2
          rw [hpi]
          have hswap :
              t ^ 2 * (π ^ 2)⁻¹ * GReal s * Δr⁻¹ = t ^ 2 * GReal s * (π ^ 2)⁻¹ * Δr⁻¹ := by
            exact mul_mul_mul_comm' (t ^ 2) ((π ^ 2)⁻¹) (GReal s) (Δr⁻¹)
          have hcomm :
              t ^ 2 * GReal s * (π ^ 2)⁻¹ * Δr⁻¹ = t ^ 2 * GReal s * Δr⁻¹ * (π ^ 2)⁻¹ := by
            exact mul_right_comm (t ^ 2 * GReal s) ((π ^ 2)⁻¹) (Δr⁻¹)
          have hswap18 :
              t ^ 2 * (π ^ 2)⁻¹ * GReal s * Δr⁻¹ * 18 =
                t ^ 2 * GReal s * (π ^ 2)⁻¹ * Δr⁻¹ * 18 :=
            congrArg (fun x => x * 18) hswap
          have hcomm18 :
              t ^ 2 * GReal s * (π ^ 2)⁻¹ * Δr⁻¹ * 18 =
                t ^ 2 * GReal s * Δr⁻¹ * (π ^ 2)⁻¹ * 18 :=
            congrArg (fun x => x * 18) hcomm
          exact hswap18.trans hcomm18
    _ = (-(t ^ (2 : ℕ))) * ((FReal s - c * GReal s) / Δr) := by
          field_simp [hΔr]
          ring
    _ =
        (-(t ^ (2 : ℕ))) *
          ((FReal (1 / t) - c * GReal (1 / t)) / (Δ.resToImagAxis (1 / t)).re) := by
          simp [s, Δr, Function.resToImagAxis]

end

end MagicFunction.g.CohnElkies
