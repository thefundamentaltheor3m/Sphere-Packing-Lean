/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module


public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.a.Integrability.RealDecay

/-!
# Shared Majorants for the Contour Integrals `Iⱼ`

The six segments making up the contour defining `a` fall into three classes, and within each
class the analytic estimate is *the same*; only the parametrisation and a unit-modulus phase
differ. This file isolates the shared ingredients so that `I1.lean`–`I6.lean` and
`Integrability.lean` become thin specialisations.

## Main results

### The master bound on `φ₀''`

* `norm_φ₀''_le`: for `Im w > 1/2`, `‖φ₀'' w‖ ≤ C₀ * exp (-2π * Im w)`. This is
  `PolyFourierCoeffBound.norm_φ₀_le` transported from `ℍ` to `ℂ` once and for all.

Specialisations along the families of parametrisations:

* `norm_φ₀''_I_mul_le` (vertical ray `w = I * s`, `s > 1/2`),
* `norm_φ₀''_neg_inv_I_mul_le` (cusp ray `w = -1/(I * t)`, `0 < t < 2`).

### Majorant integrability, by contour class

* `integrableOn_majorant_cusp`: `C₀ * exp (-2πs) * exp (-πr/s)` on `[1, ∞)`,
* `integrableOn_majorant_vertical`: `C₀ * exp (-2πt) * exp (-πrt)` on `[1, ∞)` for `r ≥ 0`.

### Segment majorants for the real integrands

* `Φ₁_eq_Φ₅_mul_phase`, `Φ₃_eq_Φ₅_mul_phase`: the cusp-touching integrands agree up to a
  unit-modulus phase, so a single estimate covers all three,
* `norm_Φ₅_le`, `norm_Φ₁_le`, `norm_Φ₃_le`: uniform bounds on `(0, 1]`,
* `integrableOn_of_norm_le_const`: a continuous function with a uniform bound on a set of
  finite measure is integrable there.
-/

@[expose] public section

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals
  MagicFunction.a.RadialFunctions MagicFunction.PolyFourierCoeffBound
  MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter
open scoped Function UpperHalfPlane

noncomputable section

namespace MagicFunction.a.Majorants

/-! ## The master bound on `φ₀''` -/

/-- The `PolyFourierCoeffBound` for `φ₀`, transported to `φ₀''` on the half-plane `Im w > 1/2`.

Every estimate on the six contour segments is a specialisation of this one bound; the
segments differ only in the parametrisation `t ↦ w t` fed into it. -/
theorem norm_φ₀''_le : ∃ C₀ > 0, ∀ w : ℂ, 1 / 2 < w.im → ‖φ₀'' w‖ ≤ C₀ * rexp (-2 * π * w.im) := by
  refine norm_φ₀_le.imp fun C₀ ⟨hC₀_pos, hC₀⟩ ↦ ⟨hC₀_pos, fun w hw ↦ ?_⟩
  have hpos : 0 < w.im := one_half_pos.trans hw
  exact φ₀''_def hpos ▸ hC₀ ⟨w, hpos⟩ hw

/-! ### Imaginary parts of the families of parametrisations -/

/-- The cusp ray `-1/(I t)` is again a point of the imaginary axis, at height `t⁻¹`. -/
@[simp]
lemma im_neg_one_div_I_mul (t : ℝ) : (-1 / (I * (t : ℂ))).im = t⁻¹ := by
  simp [normSq_apply, neg_div, div_self_mul_self']

/-- The top edge of the fundamental domain, parametrised by `u ↦ -1 / (u + I)`. -/
lemma im_neg_one_div_add_I (u : ℝ) : (-1 / ((u : ℂ) + I)).im = 1 / (u ^ 2 + 1) := by
  simp [normSq_apply, neg_div, pow_two]

/-! ### Specialisations of the master bound -/

/-- Vertical-ray class (`I₆`, and `I₁`, `I₃`, `I₅` after the change of variables `s = 1/t`). -/
theorem norm_φ₀''_I_mul_le :
    ∃ C₀ > 0, ∀ s : ℝ, 1 / 2 < s → ‖φ₀'' (I * (s : ℂ))‖ ≤ C₀ * rexp (-2 * π * s) :=
  norm_φ₀''_le.imp fun C₀ ⟨h, hC₀⟩ ↦ ⟨h, fun s hs ↦ by simpa using hC₀ (I * s) (by simpa using hs)⟩

/-- Cusp-touching class (`I₁`, `I₃`, `I₅` in their original parametrisation): as `t → 0⁺` the
point `-1/(I t)` runs out to the cusp, and the bound decays like `exp (-2π/t)`. -/
theorem norm_φ₀''_neg_inv_I_mul_le : ∃ C₀ > 0, ∀ t : ℝ, 0 < t → t < 2 →
    ‖φ₀'' (-1 / (I * (t : ℂ)))‖ ≤ C₀ * rexp (-2 * π / t) :=
  norm_φ₀''_le.imp fun C₀ ⟨h, hC₀⟩ ↦ ⟨h, fun t ht ht' ↦ by
    simpa only [im_neg_one_div_I_mul, ← div_eq_mul_inv] using
      hC₀ (-1 / (I * t)) (by simpa using inv_strictAnti₀ ht ht')⟩

/-! ## Majorant integrability, by contour class -/

/-- Cusp class: after the change of variables `s = 1/t` the majorant is
`C₀ * exp (-2πs) * exp (-πr/s)` on `[1, ∞)`. The second factor is bounded there, so the
first factor carries the integrability. -/
theorem integrableOn_majorant_cusp (r C₀ : ℝ) :
    IntegrableOn (fun s ↦ C₀ * rexp (-2 * π * s) * rexp (-π * r / s)) (Ici 1) volume := by
  refine (((integrableOn_exp_mul_Ici (-2 * π) (by linarith [pi_pos])).const_mul
    |C₀|).mul_const (rexp (π * |r|))).mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with s (hs : 1 ≤ s)
  simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  gcongr
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < s)]
  nlinarith [mul_nonneg pi_pos.le (abs_nonneg r), pi_pos, neg_abs_le r]

/-- Vertical class: the majorant `C₀ * exp (-2πt) * exp (-πrt)` on `[1, ∞)`, for `r ≥ 0`. -/
theorem integrableOn_majorant_vertical (r C₀ : ℝ) (hr : 0 ≤ r) :
    IntegrableOn (fun t ↦ C₀ * rexp (-2 * π * t) * rexp (-π * r * t)) (Ici 1) volume := by
  simpa [IntegrableOn, add_mul, Real.exp_add, mul_assoc] using (integrableOn_exp_mul_Ici
    (-2 * π + -π * r) (by linarith [pi_pos, mul_nonneg pi_pos.le hr])).const_mul C₀

/-! ## Uniform bounds give integrability on sets of finite measure -/

/-- A continuous function with a uniform norm bound on a measurable set of finite measure is
integrable there. This is the segment-integrability workhorse for `Φ₁`–`Φ₅`. -/
theorem integrableOn_of_norm_le_const {f : ℝ → ℂ} {s : Set ℝ} {C : ℝ}
    (hs : MeasurableSet s) (hs' : volume s ≠ ⊤) (hf : ContinuousOn f s)
    (hb : ∀ t ∈ s, ‖f t‖ ≤ C) : IntegrableOn f s volume :=
  .of_bound hs'.lt_top (hf.aestronglyMeasurable hs) C ((ae_restrict_iff' hs).2 (.of_forall hb))

/-! ## Segment majorants for the real integrands `Φⱼ` -/

section RealIntegrands

variable {r t : ℝ}

/-- `π * I * r * (I * t) = -(π * r * t)`, the identity behind every cusp-class simplification. -/
lemma cexp_pi_I_mul_I (r t : ℝ) :
    cexp ((π : ℂ) * I * (r : ℂ) * (I * (t : ℂ))) = cexp (-((π : ℂ) * (r : ℂ) * (t : ℂ))) :=
  congrArg cexp (by linear_combination ((π : ℂ) * r * t) * I_sq)

/-- For `t ∈ (0, 1]`, `exp (-2π/t) * t² ≤ exp (-2π)`: the super-exponential decay at the cusp
swallows the quadratic factor coming from the parametrisation. -/
lemma exp_neg_two_pi_div_mul_sq_le (ht : 0 < t) (ht' : t ≤ 1) :
    rexp (-2 * π / t) * t ^ 2 ≤ rexp (-2 * π) := by
  have h1 : -2 * π / t ≤ -2 * π := by rw [div_le_iff₀ ht]; nlinarith [pi_pos]
  calc rexp (-2 * π / t) * t ^ 2 ≤ rexp (-2 * π) * 1 := by gcongr; nlinarith
    _ = rexp (-2 * π) := mul_one _

/-- `Φ₁` is `Φ₅` up to the unit-modulus phase `exp (-πIr)`: on `[0,1]`, `z₁' t + 1 = z₅' t`. -/
lemma Φ₁_eq_Φ₅_mul_phase (ht : t ∈ Icc (0 : ℝ) 1) :
    Φ₁ r t = Φ₅ r t * cexp ((-(π * r) : ℝ) * I) := by
  simp only [Φ₁, Φ₅, Φ₁', Φ₅', z₁'_eq_of_mem ht, z₅'_eq_of_mem ht, neg_add_cancel_comm]
  rw [show (π : ℂ) * I * (r : ℂ) * (-1 + I * (t : ℂ))
      = ((-(π * r) : ℝ) : ℂ) * I + (π : ℂ) * I * (r : ℂ) * (I * (t : ℂ)) by push_cast; ring,
    Complex.exp_add]
  ring

/-- `Φ₃` is `Φ₅` up to the unit-modulus phase `exp (πIr)`: on `[0,1]`, `z₃' t - 1 = z₅' t`. -/
lemma Φ₃_eq_Φ₅_mul_phase (ht : t ∈ Icc (0 : ℝ) 1) :
    Φ₃ r t = Φ₅ r t * cexp (((π * r) : ℝ) * I) := by
  simp only [Φ₃, Φ₅, Φ₃', Φ₅', z₃'_eq_of_mem ht, z₅'_eq_of_mem ht, add_sub_cancel_left]
  rw [show (π : ℂ) * I * (r : ℂ) * (1 + I * (t : ℂ))
      = (((π * r) : ℝ) : ℂ) * I + (π : ℂ) * I * (r : ℂ) * (I * (t : ℂ)) by push_cast; ring,
    Complex.exp_add]
  ring

/-- Uniform bound for `Φ₅` on `(0, 1]`, for `r ≥ 0`.

Writing `Φ₅ r t = I * φ₀''(-1/(It)) * (It)² * exp (-πrt)`, the three factors are handled by
`norm_φ₀''_neg_inv_I_mul_le`, `exp_neg_two_pi_div_mul_sq_le` and `exp (-πrt) ≤ 1`. -/
lemma norm_Φ₅_le (hr : 0 ≤ r) :
    ∃ C₀ > 0, ∀ t ∈ Ioc (0 : ℝ) 1, ‖Φ₅ r t‖ ≤ C₀ * rexp (-2 * π) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀''_neg_inv_I_mul_le
  refine ⟨C₀, hC₀_pos, fun t ht ↦ ?_⟩
  simp only [Φ₅, Φ₅', z₅'_eq_of_mem (mem_Icc_of_Ioc ht), cexp_pi_I_mul_I, norm_mul, norm_pow,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1,
    Complex.norm_exp, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  calc ‖φ₀'' (-1 / (I * (t : ℂ)))‖ * t ^ 2 * rexp (-(π * r * t))
      ≤ C₀ * rexp (-2 * π / t) * t ^ 2 * 1 := by
        gcongr
        · exact hC₀ t ht.1 (ht.2.trans_lt one_lt_two)
        · exact exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (mul_nonneg pi_pos.le hr) ht.1.le))
    _ = C₀ * (rexp (-2 * π / t) * t ^ 2) := by ring
    _ ≤ C₀ * rexp (-2 * π) := by gcongr; exact exp_neg_two_pi_div_mul_sq_le ht.1 ht.2

/-- Uniform bound for `Φ₁` on `(0, 1]`: it agrees with `Φ₅` up to a unit-modulus phase. -/
lemma norm_Φ₁_le (hr : 0 ≤ r) :
    ∃ C₀ > 0, ∀ t ∈ Ioc (0 : ℝ) 1, ‖Φ₁ r t‖ ≤ C₀ * rexp (-2 * π) :=
  (norm_Φ₅_le hr).imp fun C₀ ↦ And.imp_right fun hC₀ t ht ↦ by
    simpa [Φ₁_eq_Φ₅_mul_phase (mem_Icc_of_Ioc ht), Complex.norm_exp] using hC₀ t ht

/-- Uniform bound for `Φ₃` on `(0, 1]`: it agrees with `Φ₅` up to a unit-modulus phase. -/
lemma norm_Φ₃_le (hr : 0 ≤ r) :
    ∃ C₀ > 0, ∀ t ∈ Ioc (0 : ℝ) 1, ‖Φ₃ r t‖ ≤ C₀ * rexp (-2 * π) :=
  (norm_Φ₅_le hr).imp fun C₀ ↦ And.imp_right fun hC₀ t ht ↦ by
    simpa [Φ₃_eq_Φ₅_mul_phase (mem_Icc_of_Ioc ht), Complex.norm_exp] using hC₀ t ht

end RealIntegrands

end MagicFunction.a.Majorants

end
