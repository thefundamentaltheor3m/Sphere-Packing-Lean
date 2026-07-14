/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import SpherePacking.Tactic.SlashSimpAttr -- shake: keep (tactic dependency)
public import SpherePacking.ModularForms.SlashActionAuxil
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# `slash_simp` tactic

Unfolds slash-action applications and clears the resulting `denom γ z` denominators, with
the nonvanishing side conditions (`denom γ z ≠ 0`, `(z : ℂ) ≠ 0`, `(π : ℂ) ≠ 0`,
`Complex.I ≠ 0`, ...) discharged automatically by the `slash_ne_zero` tactic.

The canonical normal form is the `SL_slash_apply` one: `(f ∣[k] γ) z` becomes
`f (γ • z) * denom γ z ^ (-k)`, with `denom` evaluated on the explicit generators
(`denom S z = z`, `denom T z = 1`). It replaces the recurring idiom

```lean
rw [SL_slash_apply] at h
simp only [ModularGroup.denom_S, zpow_neg, ModularForm.toFun_eq_coe] at h
have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
field_simp [ne_zero z] at h
```

with `slash_simp at h`.

* `slash_simp [foo, h]` adds extra simp lemmas to the unfolding phase;
* `slash_simp at h ⊢` works at hypotheses;
* `slash_ne_zero` is also available standalone for `≠ 0` goals of the above shapes.
-/

@[expose] public section

open UpperHalfPlane in
/-- `denom` of the translation generator `T` is `1`. Companion to `ModularGroup.denom_S`. -/
@[simp]
lemma ModularGroup.denom_T (z : ℍ) : UpperHalfPlane.denom ModularGroup.T z = 1 := by
  simp [ModularGroup.T, ModularGroup.denom_apply]

attribute [slash_simps]
  ModularForm.SL_slash_apply
  ModularForm.toFun_eq_coe
  ModularGroup.denom_S
  ModularGroup.denom_T
  zpow_neg
  one_zpow
  mul_one
  one_mul
  Int.cast_one
  Complex.ofReal_one
  Matrix.SpecialLinearGroup.coe_GL_coe_matrix
  Matrix.SpecialLinearGroup.map_apply_coe
  RingHom.mapMatrix_apply
  Int.coe_castRingHom
  Matrix.map_apply
  Matrix.of_apply
  Matrix.cons_val'
  Matrix.cons_val_zero
  Matrix.cons_val_fin_one
  Matrix.cons_val_one

/-- Discharges the `≠ 0` side conditions arising from slash-action denominators:
`denom γ z ≠ 0`, `(z : ℂ) ≠ 0` for `z : ℍ`, `(π : ℂ) ≠ 0`, `Complex.I ≠ 0`, and
products/powers thereof. -/
macro "slash_ne_zero" : tactic =>
  `(tactic| first
    | assumption
    | simp [ne_eq, mul_eq_zero, not_or, pow_eq_zero_iff, UpperHalfPlane.denom_ne_zero,
        UpperHalfPlane.ne_zero, Complex.ofReal_eq_zero, Real.pi_ne_zero, Complex.I_ne_zero])

/-- `slash_simp` unfolds slash-action applications to the `f (γ • z) * denom γ z ^ (-k)`
normal form (evaluating `denom` on the generators `S`, `T`) and then clears denominators
with `field_simp`, discharging nonvanishing side conditions with `slash_ne_zero`.

* `slash_simp [foo, h]` adds extra simp lemmas to the unfolding phase;
* `slash_simp at h ⊢` works at hypotheses. -/
syntax (name := slashSimpTac) "slash_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")?
  (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| slash_simp $[$loc:location]?) => do
    let s1 ← `(tactic| simp only [slash_simps] $[$loc:location]?)
    let s2 ← `(tactic| try field_simp (disch := slash_ne_zero) $[$loc:location]?)
    `(tactic| ($s1; $s2))
  | `(tactic| slash_simp [$ls,*] $[$loc:location]?) => do
    let s1 ← `(tactic| simp only [slash_simps, $ls,*] $[$loc:location]?)
    let s2 ← `(tactic| try field_simp (disch := slash_ne_zero) $[$loc:location]?)
    `(tactic| ($s1; $s2))
