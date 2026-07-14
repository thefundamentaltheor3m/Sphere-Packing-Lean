/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import SpherePacking.Tactic.DNfAttr -- shake: keep (tactic dependency)
public import SpherePacking.Tactic.Pointwise
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum

/-!
# `d_nf` tactic — normalizer for the quasimodular differential ring

Proofs in the `(ℂ[E₂, E₄, E₆], D)` layer (`FG.lean`, `RamanujanIdentities.lean`,
`JacobiTheta/Derivative.lean`) repeat the pipeline

```lean
simp (disch := fun_prop) only [serre_D_eq, D_add, D_sub, D_mul, D_sq, D_cube,
  ramanujan_E₂, ramanujan_E₄, ramanujan_E₆]
ext z
simp [Pi.mul_apply, ...]
field_simp (disch := norm_num)
ring
```

`d_nf` packages it:

1. `simp (disch := fun_prop) only [d_simps]` — unfold `serre_D`, push `D` through the
   algebra (Leibniz/linearity, with `MDiff` side goals discharged by `fun_prop`), and
   substitute the Ramanujan/theta base derivatives;
2. `pointwise` — `ext z` and evaluate the function-space algebra pointwise;
3. `(try field_simp (disch := norm_num)); try ring` — clear denominators and close.

`d_nf [foo, h]` adds extra simp lemmas to both simp phases (e.g. local definitions such
as `F`, `Δ_fun` or previously proved formulas such as `F_aux`).

The `d_simps` set is registered in `SpherePacking.Tactic.DNfAttr` and populated at the
definition sites of the `D_*`/`serre_D_*`/`ramanujan_*` lemmas; extend it with
`attribute [d_simps] myLemma`.
-/

@[expose] public section

/-- `d_nf` normalizes identities in the quasimodular differential ring: it pushes
`D`/`serre_D` through the function algebra with `simp (disch := fun_prop) only [d_simps]`,
substitutes the base derivatives of `E₂`, `E₄`, `E₆`, `H₂`, `H₃`, `H₄`, goes pointwise
with `pointwise`, and closes with `field_simp`/`ring`.

`d_nf [foo, h]` adds extra simp lemmas (e.g. local definitions to unfold). -/
syntax (name := dNfTac) "d_nf" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| d_nf) => do
    let structural ← `(tactic| simp (disch := fun_prop) only [d_simps])
    let closer ← `(Lean.Parser.Tactic.tacticSeq|
      ((try field_simp (disch := norm_num)); try ring))
    `(tactic| ($structural; try pointwise using $closer))
  | `(tactic| d_nf [$ls,*]) => do
    let structural ← `(tactic| simp (disch := fun_prop) only [d_simps, $ls,*])
    let closer ← `(Lean.Parser.Tactic.tacticSeq|
      ((try field_simp (disch := norm_num)); try ring))
    `(tactic| ($structural; try pointwise [$ls,*] using $closer))
