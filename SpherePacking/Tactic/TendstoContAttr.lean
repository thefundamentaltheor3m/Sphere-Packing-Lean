/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Tactic.FunProp

/-!
# `@[tendsto_cont]` attribute

Environment extension and attribute registration for the `tendsto_cont` tactic.
Separated into its own file so that `meta` tactic code can access the extension
(which must be from a pre-compiled module).
-/

@[expose] public section

open Lean

/-- Environment extension storing `@[tendsto_cont]`-registered lemma names. -/
initialize tendstoContExt : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.insert n
    initial := default
  }

/-- Register a `Tendsto` lemma for automatic use by the `tendsto_cont` tactic.
    Only global scope is supported (not `local` or `scoped`). -/
initialize registerBuiltinAttribute {
  name := `tendsto_cont
  descr := "Register a Tendsto lemma for automatic use by the tendsto_cont tactic"
  applicationTime := .afterCompilation
  add := fun declName _stx kind => do
    unless kind == .global do
      throwError "`@[tendsto_cont]` only supports global scope (not `local` or `scoped`)"
    let info ← getConstInfo declName
    let ty := info.type
    -- Reject declarations with any binders — only closed lemmas are supported
    if ty.isForall then
      throwError "`@[tendsto_cont]`: declaration must be a closed `Tendsto` \
        lemma with no parameters; got a declaration with binders"
    match ty.getAppFnArgs with
    | (`Filter.Tendsto, args) =>
      if h : args.size ≥ 5 then
        match args[4].getAppFnArgs with
        | (`nhds, _) => pure ()
        | (other, _) =>
          throwError "`@[tendsto_cont]`: target filter must be `nhds _`, \
            got `{other}`"
      else
        throwError "`@[tendsto_cont]`: declaration type is not a fully \
          applied `Tendsto`"
    | (other, _) =>
      throwError "`@[tendsto_cont]`: declaration type must be \
        `Tendsto f l (nhds a)`, got head `{other}`"
    tendstoContExt.add declName
}
