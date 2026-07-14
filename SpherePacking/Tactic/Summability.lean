/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity.Basic

/-!
# `summability` tactic

Registers `Summable` as a `fun_prop` predicate — following the repository's
`ResToImagAxis.Real` precedent — together with its algebraic closure lemmas
(`Summable.add`, `Summable.mul_left`, ...) and the standard geometric-series leaf facts
(`summable_geometric_of_norm_lt_one`, `summable_pow_mul_geometric_of_norm_lt_one`, ...).

The `summability` tactic is `fun_prop` with a discharger tuned to the side conditions
that arise (`‖r‖ < 1` by assumption, `0 < c` by `positivity`, numeric goals by
`norm_num`):

```lean
example {r : ℂ} (hr : ‖r‖ < 1) (f : ℕ → ℂ) (hf : Summable f) :
    Summable (fun n => f n + (n : ℂ) ^ 3 * r ^ n) := by summability
```

`summability (disch := tac)` overrides the discharger. Reindexing between `ℕ`, `ℕ+`,
and `ℤ` (`Summable.comp_injective`, `summable_pnat_iff_summable_nat`, ...) is out of
scope and should be applied before calling the tactic.

`summable_pow_mul_cexp` is deliberately *not* tagged: its `cexp (2 * π * I * e * z) ^ c`
pattern sends the unifier unfolding `Complex.exp` when matched against unrelated
geometric leaves, causing `isDefEq` timeouts. Apply it explicitly at `q`-expansion
sites, or provide `‖cexp _‖ < 1` (e.g. via `exp_upperHalfPlane_lt_one`) and let the
generic geometric leaf fire.
-/

@[expose] public section

/-- `k = 1` specialization of `summable_pow_mul_geometric_of_norm_lt_one` for the common
bare form `↑n * r ^ n` (with no `^ k`).

Deliberately *not* `@[fun_prop]`-tagged: reconciling `↑n` with `↑n ^ ?k` (in either
direction) makes the unifier unfold `ℂ`-instance towers and time out, so the bare and
`^ k` leaf shapes cannot coexist in the rule set. For bare-form goals, `have` this lemma
into the context before calling `summability`. -/
theorem summable_cast_mul_geometric_of_norm_lt_one {R : Type*} [NormedRing R]
    [CompleteSpace R] {r : R} (hr : ‖r‖ < 1) : Summable (fun n : ℕ => (n : R) * r ^ n) := by
  simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr

attribute [fun_prop] Summable

attribute [fun_prop]
  Summable.add
  Summable.neg
  Summable.sub
  Summable.mul_left
  Summable.mul_right
  Summable.div_const
  Summable.const_smul
  Summable.of_finite
  summable_geometric_of_norm_lt_one
  summable_norm_geometric_of_norm_lt_one
  summable_pow_mul_geometric_of_norm_lt_one
  summable_norm_pow_mul_geometric_of_norm_lt_one

/-- `summability` proves `Summable f` goals compositionally via `fun_prop`, using the
`@[fun_prop]`-tagged closure lemmas (`Summable.add`, `Summable.mul_left`, ...) and leaf
facts (`summable_geometric_of_norm_lt_one`, `summable_pow_mul_cexp`, ...). Side
conditions are discharged by `assumption`/`positivity`/`norm_num`;
`summability (disch := tac)` overrides the discharger. -/
syntax (name := summabilityTac) "summability" (Lean.Parser.Tactic.discharger)? : tactic

macro_rules
  | `(tactic| summability) =>
    `(tactic| fun_prop (disch := first | assumption | positivity | norm_num))
  | `(tactic| summability $disch:discharger) =>
    `(tactic| fun_prop $disch:discharger)
