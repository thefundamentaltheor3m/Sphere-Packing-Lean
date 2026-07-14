/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Tactic.Positivity.Core

/-!
# `positivity` extensions for `Complex.re` / `Complex.im` atoms

Mathlib already provides `positivity` extensions for `UpperHalfPlane.im` and
`UpperHalfPlane.coe`. This file adds extensions for the `Complex.re` / `Complex.im`
projections of the concrete complex expressions that appear throughout this repository,
most importantly the membership proof `0 < (Complex.I * ↑t).im` required to build points
`⟨Complex.I * t, by positivity⟩ : ℍ` on the imaginary axis.

Handled shapes (with `t : ℝ`, `w : ℂ`, `z : ℍ`):

* `(↑t).re` — positive / nonnegative / nonzero, from the corresponding fact about `t`;
* `(↑t).im` — nonnegative (it is zero);
* `(Complex.I * w).im` and `(w * Complex.I).im` — from the corresponding fact about `w.re`
  (recursively, so `0 < (Complex.I * ↑t).im` follows from `0 < t`);
* `Complex.I.im` — positive;
* `(↑z).im` for `z : ℍ` — positive.

These are natural candidates for upstreaming to Mathlib.
-/

@[expose] public section

open Complex

namespace Complex

theorem im_I_mul_pos {w : ℂ} (hw : 0 < w.re) : 0 < (I * w).im := by simpa using hw

theorem im_I_mul_nonneg {w : ℂ} (hw : 0 ≤ w.re) : 0 ≤ (I * w).im := by simpa using hw

theorem im_I_mul_ne_zero {w : ℂ} (hw : w.re ≠ 0) : (I * w).im ≠ 0 := by simpa using hw

theorem im_mul_I_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w * I).im := by simpa using hw

theorem im_mul_I_nonneg {w : ℂ} (hw : 0 ≤ w.re) : 0 ≤ (w * I).im := by simpa using hw

theorem im_mul_I_ne_zero {w : ℂ} (hw : w.re ≠ 0) : (w * I).im ≠ 0 := by simpa using hw

theorem im_I_pos : 0 < I.im := by simp

theorem im_ofReal_nonneg (t : ℝ) : 0 ≤ (t : ℂ).im := by simp

theorem re_ofReal_pos {t : ℝ} (ht : 0 < t) : 0 < (t : ℂ).re := by simpa using ht

theorem re_ofReal_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ (t : ℂ).re := by simpa using ht

theorem re_ofReal_ne_zero {t : ℝ} (ht : t ≠ 0) : (t : ℂ).re ≠ 0 := by simpa using ht

end Complex

namespace UpperHalfPlane

theorem im_coe_pos (z : ℍ) : 0 < (z : ℂ).im := coe_im z ▸ z.im_pos

end UpperHalfPlane

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `(↑t).re` for a real `t` inherits
positivity/nonnegativity/nonzeroness from `t`. -/
@[positivity Complex.re _]
meta def evalComplexRe : PositivityExt where eval {u α} zα pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Complex.re $w) =>
    assertInstancesCommute
    match w with
    | ~q(Complex.ofReal $t) =>
      match ← core zα pα t with
      | .positive pf => pure (.positive q(Complex.re_ofReal_pos $pf))
      | .nonnegative pf => pure (.nonnegative q(Complex.re_ofReal_nonneg $pf))
      | .nonzero pf => pure (.nonzero q(Complex.re_ofReal_ne_zero $pf))
      | .none => pure .none
    | _ => pure .none
  | _, _, _ => throwError "not Complex.re"

/-- Extension for the `positivity` tactic: imaginary parts of complex expressions.
Handles `(Complex.I * w).im` / `(w * Complex.I).im` (recursing into `w.re`, so in
particular `0 < (Complex.I * ↑t).im` follows from `0 < t`), `Complex.I.im`,
`(↑t).im` for real `t`, and `(↑z).im` for `z : ℍ`. -/
@[positivity Complex.im _]
meta def evalComplexIm : PositivityExt where eval {u α} zα pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Complex.im $w) =>
    assertInstancesCommute
    match w with
    | ~q(UpperHalfPlane.coe $z) =>
      pure (.positive q(UpperHalfPlane.im_coe_pos $z))
    | ~q(Complex.I * $v) =>
      match ← core zα pα q(Complex.re $v) with
      | .positive pf => pure (.positive q(Complex.im_I_mul_pos $pf))
      | .nonnegative pf => pure (.nonnegative q(Complex.im_I_mul_nonneg $pf))
      | .nonzero pf => pure (.nonzero q(Complex.im_I_mul_ne_zero $pf))
      | .none => pure .none
    | ~q($v * Complex.I) =>
      match ← core zα pα q(Complex.re $v) with
      | .positive pf => pure (.positive q(Complex.im_mul_I_pos $pf))
      | .nonnegative pf => pure (.nonnegative q(Complex.im_mul_I_nonneg $pf))
      | .nonzero pf => pure (.nonzero q(Complex.im_mul_I_ne_zero $pf))
      | .none => pure .none
    | ~q(Complex.I) =>
      pure (.positive q(Complex.im_I_pos))
    | ~q(Complex.ofReal $t) =>
      pure (.nonnegative q(Complex.im_ofReal_nonneg $t))
    | _ => pure .none
  | _, _, _ => throwError "not Complex.im"

end Mathlib.Meta.Positivity
