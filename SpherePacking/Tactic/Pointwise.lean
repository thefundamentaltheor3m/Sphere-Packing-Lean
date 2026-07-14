/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import SpherePacking.Tactic.PointwiseAttr -- shake: keep (tactic dependency)
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.Ring

/-!
# `pointwise` tactic

A one-word replacement for the ubiquitous idiom

```lean
ext z
simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul, ...]
ring
```

used to prove pointwise identities between functions (typically `ℍ → ℂ` in this repository).

## Usage

* `pointwise` — `ext z; simp only [pointwise_simps]; try ring`.
* `pointwise [foo, h]` — also uses the extra simp lemmas/hypotheses `foo`, `h`
  (e.g. local definitions to unfold) in the `simp only` call.
* `pointwise using tac` — replaces the final `try ring` with `tac`
  (e.g. `pointwise using ring_nf`, `pointwise using (field_simp; ring)`).
* Both may be combined: `pointwise [foo] using ring_nf`.

To normalize a *hypothesis* instead of the goal, use the simp set directly:
`simp only [pointwise_simps] at h`.

The simp set `pointwise_simps` is registered in `SpherePacking.Tactic.PointwiseAttr`; further
lemmas can be added with `attribute [pointwise_simps] myLemma` or `@[pointwise_simps]`.
-/

@[expose] public section

attribute [pointwise_simps]
  Pi.add_apply
  Pi.mul_apply
  Pi.sub_apply
  Pi.div_apply
  Pi.smul_apply
  Pi.pow_apply
  Pi.neg_apply
  Pi.inv_apply
  Pi.one_apply
  Pi.zero_apply
  Pi.ofNat_apply
  Function.comp_apply
  Function.const_apply
  smul_eq_mul
  nsmul_eq_mul
  zsmul_eq_mul
  Nat.cast_ofNat
  Complex.real_smul
  Complex.ofReal_ofNat
  Complex.ofReal_natCast
  Complex.ofReal_intCast
  Complex.ofReal_one
  Complex.ofReal_zero

/-- `pointwise` proves pointwise identities between functions: it runs `ext z`, pushes
function-space algebra down to values with `simp only [pointwise_simps]`, and finishes
with `try ring`.

`pointwise [foo, h]` adds extra simp lemmas (e.g. local definitions to unfold);
`pointwise using tac` replaces the final `try ring` with `tac`. -/
syntax (name := pointwiseTac) "pointwise" (" [" Lean.Parser.Tactic.simpLemma,* "]")?
  (" using " Lean.Parser.Tactic.tacticSeq)? : tactic

macro_rules
  | `(tactic| pointwise) =>
    `(tactic| (ext z; simp only [pointwise_simps]; try ring))
  | `(tactic| pointwise [$ls,*]) =>
    `(tactic| (ext z; simp only [pointwise_simps, $ls,*]; try ring))
  | `(tactic| pointwise using $tac) =>
    `(tactic| (ext z; simp only [pointwise_simps]; ($tac)))
  | `(tactic| pointwise [$ls,*] using $tac) =>
    `(tactic| (ext z; simp only [pointwise_simps, $ls,*]; ($tac)))
