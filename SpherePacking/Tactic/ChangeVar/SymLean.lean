/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import SpherePacking.Tactic.ChangeVar.Core
public import CAS.Tactic.DerivativeRules
public meta import SpherePacking.Tactic.ChangeVar.Core
public meta import CAS.Tactic.DerivativeRules

/-!
# `change_var` with SymLean's derivative rules

`SpherePacking.Tactic.ChangeVar.Core` depends on Mathlib only and on no oracle. The one thing it
cannot do alone is compute an explicit derivative `ψ'`: without help it falls back to `fun_prop`
and an opaque `deriv ψ x`. This file declares SymLean's checked rule engine
(`CAS.Tactic.DerivativeRules.derive?`) as a *derivative oracle*, with `@[change_var_oracle]` (see
*Derivative oracles* in `Core`).

**Activation is silent.** The oracle is used by every file that imports this one, *directly or
transitively* (for instance through `import SpherePacking`, whose root file imports it): no
option or syntax in the user's file says so. It changes, with explicit derivatives:

* the search for the outer function `g` in `change_var!` / `change_var?` (it needs `ψ'` as an
  expression), which then succeeds without `using`;
* the derivative step of `change_var!` and of `change_var_deriv` / `change_var_disch` (the goal
  `deriv`);
* the scripts suggested by `change_var?` and `change_var_deriv?`: SymLean finds the proof, which
  is a chain of Mathlib lemmas only, and the suggestion replays without SymLean (it is replayed
  with the oracles off before being suggested). When no such script replays, `change_var?`
  suggests the compact `change_var (disch := change_var_disch) … with g`, which calls SymLean
  again on replay.

To see it: the report of `change_var?` names the source of the derivative ("SymLean's checked
derivative rules"). To switch it off without changing imports: `set_option
changeVar.derivOracles false`. Its behaviour is tested in
`SpherePacking/Tactic/Test/ChangeVarSymLean.lean`; the core's, without any oracle, in
`SpherePacking/Tactic/Test/ChangeVar.lean`.

It also extends SymLean's rules with Mathlib's chain rules for `log` and `√`. Nothing SymLean
returns is trusted: its proofs are checked by the kernel, and every derivative still enters the
change of variables through an obligation.

## Notes on SymLean as an oracle

* **Its proofs use Mathlib lemmas only** (`HasDerivAt.add`, `HasDerivAt.comp`,
  `Real.hasDerivAt_exp`, …): no `CAS.*` constant occurs in them, so the scripts of `change_var?`
  pass the core's check that a suggestion only uses the core's own dependencies.
* **`derive?` reads the main goal's context** (`withMainContext`): the core installs an auxiliary
  main goal inside its binders for that reason (`withRealVarIn`), and adds the domain facts
  `hpos`/`hneg`/`hne` as `let`s, from which SymLean closes the premises of its rules.
* **Inferred types use powers of functions** (`HasDerivAt ((fun x => x) ^ 2) …` for the power
  rule): the core pins the type to `HasDerivAt ψ v x` before rewriting.
* **Deterministic.** SymLean's only `Task.spawn` (`CAS/Numerics/CompactLiteralRuntime.lean`)
  computes a pure cached value; the same file compiled several times gives byte-identical messages.
-/

public meta section

namespace ChangeVar

/- Extend SymLean's derivative rules with Mathlib's chain rules for `log` and `√`
(`HasDerivAt.log : HasDerivAt f f' x → f x ≠ 0 → HasDerivAt (fun y => log (f y)) (f' / f x) x`,
and the same shape for `√` with `f' / (2 * √(f x))`). These are Mathlib theorems, so the rule set
stays kernel-checked; the premise `f x ≠ 0` is closed from the context built by
`withRealVarIn`. -/
attribute [cas_deriv] HasDerivAt.log HasDerivAt.sqrt

/-- SymLean's checked rule engine as a derivative oracle for `change_var`. -/
@[change_var_oracle]
def symLeanOracle : DerivOracle where
  name := "SymLean's checked derivative rules"
  run ψ x := CAS.Tactic.DerivativeRules.derive? ψ x

end ChangeVar

end
