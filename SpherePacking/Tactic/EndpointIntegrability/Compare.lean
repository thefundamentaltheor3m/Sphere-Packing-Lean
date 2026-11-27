/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
module

public import SpherePacking.Tactic.EndpointIntegrability.Exponent

/-!
# The comparison engine of `endpoint_integrability`

Given a filter `l`, either `atTop` or `𝓝[>] 0`, and a function `fun t ↦ e` from `ℝ` to `ℝ` or
`ℂ`, the engine computes a *majorant* `M`, a binary tree of comparison functions `powExp a k u`
(see `SpherePacking.Tactic.EndpointIntegrability.Scale`) combined by `fun t ↦ _ + _`, together
with a proof of `(fun t ↦ e) =O[l] M`. The result is *exact* when `M` is a single comparison
function and the proof is one of `(fun t ↦ e) =Θ[l] M`: `e` has the order of `M`, and not only
an upper bound. The engine works by recursion on `e`, applying one lemma of the scale per rule.
It tries, in this order:

1. If `e` does not depend on `t`: a constant, exact if the discharger or `norm_num` proves
   `e ≠ 0` (`isTheta_const_powExp`), and otherwise only `O(1)` (`isBigO_const_powExp`).
2. If `e` is `t`: the atom `t`, exact (`isTheta_id_powExp`).
3. The rules registered with the attribute `endpoint_compare` whose patterns match `e` (see
   below). The rules of the tactic are in `SpherePacking.Tactic.EndpointIntegrability.Rules`,
   which a module running the engine must import.
4. Along `𝓝[>] 0`, if `fun_prop` proves `ContinuousAt (fun t ↦ e) 0`, the bound `O(1)`
   (`isBigO_powExp_of_continuousAt`). It comes after the rules, so that, for instance, `t ^ 2`
   stays `powExp 2 0 0` near `0` instead of becoming `O(1)`.
5. A hypothesis `(fun t ↦ e) =O[l] g` given to the engine, followed by the bound of `g` without
   the hypotheses (see `hypothesisRule`). The caller gives the hypotheses of the local context
   at the end of the goal, transported to `l` along the change of variables which reduces that
   end to `l` (see `SpherePacking.Tactic.EndpointIntegrability.Endpoint`). A hypothesis is used only
   if its type is itself `(fun t ↦ e) =O[l] g`, without universal quantifiers or premises.
6. Otherwise the engine *declines* on `e`, with a message naming the innermost subexpression which
   no rule bounds: `e` itself, or a subexpression on which a rule tried in 3 declined.

## Rules

A rule is a declaration `r : Rule`, which must be `meta` and public, tagged in the module where
it is declared by `@[endpoint_compare pat₁, pat₂, …]`, where the patterns are terms with holes
`_`, such as `_ * _` or `_ ^ (_ : ℕ)`. The patterns are stored in a discrimination tree, and the
rules with a pattern which matches `e`, up to reducible unfolding and up to instances, are run on
`e`, each once, in an unspecified order: at most one rule should apply to an expression.

A rule may assume nothing of `e` beyond the reducible matching: it must check the shape of `e`,
for instance by `let_expr`, as well as the types it handles. It bounds the subexpressions of `e`
by `compare`, and returns
* `some r`, the result of `e`, which ends the search;
* `none` if it does not apply to `e`, and the next rule is tried;
* a decline, the error of the monad `CompareM`, thrown by `throwUnbounded` with a message saying
  which subexpression is not bounded, such as the one of `compare` on a subexpression: the state
  is restored and the next rule is tried, as for `none`. If nothing bounds `e`, the engine
  declines with the first such message, which names the innermost subexpression which no rule
  bounds;
* any other error, thrown by `throwError`, which is the failure of the engine: the next rules are
  not tried.

A rule author therefore calls `compare` on the subexpressions and need not handle its decline.
`observe` and `compare?`, which return the decline as a value, are for a rule which tries an
alternative itself when a subexpression is not bounded.

A rule may return an exact result only by a lemma concluding `=Θ[l]`; `termResult` reads the
exactness off the conclusion of the lemma. For instance, for a function `bump : ℝ → ℝ` and a lemma
`isTheta_bump_powExp (g : ℝ → ℝ) : (fun t ↦ bump (g t)) =Θ[l] powExp 0 0 fun t ↦ -g t`:
```
@[endpoint_compare bump _]
meta def bumpRule : Rule where
  eval e := do
    let_expr bump g := e | return none
    termResult e (← mkAppOptM ``isTheta_bump_powExp #[← filterExpr, ← lam g])
```
-/

@[expose] public section

open Lean Meta Elab Tactic Qq Asymptotics

namespace Mathlib.Tactic.EndpointIntegrability

/-! ### Majorants -/

/-- A majorant: a binary tree of comparison functions `powExp a k u`. -/
meta inductive Majorant where
  /-- The comparison function `powExp a k u`. -/
  | powExp (a k u : Expr)
  /-- The sum `fun t ↦ m₁ t + m₂ t`. -/
  | add (m₁ m₂ : Majorant)
  deriving Inhabited

/-- The majorant, as a function `ℝ → ℝ`. -/
meta def Majorant.toExpr : Majorant → Q(ℝ → ℝ)
  | .powExp a k u => mkApp3 (.const ``EndpointIntegrability.powExp []) a k u
  | .add m₁ m₂ =>
    have e₁ : Q(ℝ → ℝ) := m₁.toExpr
    have e₂ : Q(ℝ → ℝ) := m₂.toExpr
    q(fun t ↦ $e₁ t + $e₂ t)

/-- The result of the engine on `e`: a majorant `M` and a proof of `(fun t ↦ e) =O[l] M`, or, if
the result is *exact*, of `(fun t ↦ e) =Θ[l] M`, in which case `M` is a comparison function. -/
meta structure Result where
  /-- The majorant. -/
  majorant : Majorant
  /-- The proof of `(fun t ↦ e) =O[l] M`, or of `(fun t ↦ e) =Θ[l] M` if `exact`. -/
  proof : Expr
  /-- Whether `proof` proves `(fun t ↦ e) =Θ[l] M`. -/
  exact : Bool
  deriving Inhabited

/-- The proof of `(fun t ↦ e) =O[l] M` of the result, by `Asymptotics.IsTheta.isBigO` if it is
exact. -/
meta def Result.isBigO (r : Result) : MetaM Expr :=
  if r.exact then mkAppM ``IsTheta.isBigO #[r.proof] else return r.proof

/-! ### Messages -/

/-- The comparison function `powExp a k u` at `t`, as `t ^ a * |log t| ^ k * exp (u t)`, with `a`,
`k` and `u t` simplified by `displaySimp` and the factors `t ^ 0`, `|log t| ^ 0` and `exp 0`
omitted, for messages. -/
meta def displayTerm (t : Q(ℝ)) (a k u : Expr) : MetaM Q(ℝ) := do
  let a : Q(ℝ) ← displaySimp a
  let k : Q(ℝ) ← displaySimp k
  let e : Q(ℝ) ← displaySimp (u.beta #[t])
  let mut factors : Array Q(ℝ) := #[]
  unless a.numeral? == some 0 do factors := factors.push q($t ^ $a)
  unless k.numeral? == some 0 do factors := factors.push q(|Real.log $t| ^ $k)
  unless e.numeral? == some 0 do factors := factors.push q(Real.exp $e)
  let some first := factors[0]? | return q(1)
  return factors[1:].foldl (fun (acc f : Q(ℝ)) ↦ q($acc * $f)) first

/-- The majorant at `t`, the sum of its terms written by `displayTerm`, for messages. -/
meta def Majorant.displayAt (t : Q(ℝ)) : Majorant → MetaM Q(ℝ)
  | .powExp a k u => displayTerm t a k u
  | .add m₁ m₂ => do
    let e₁ ← m₁.displayAt t
    let e₂ ← m₂.displayAt t
    return q($e₁ + $e₂)

/-- The majorant `m` as a function `fun t ↦ …`, written by `Majorant.displayAt`, for messages. -/
meta def Majorant.display (m : Majorant) : MetaM Expr :=
  withLocalDeclD `t q(ℝ) fun t ↦ do mkLambdaFVars #[t] (← m.displayAt t)

/-- The term `powExp a k u` as a function, written by `displayTerm`, for messages. -/
meta def displayTermFun (a k u : Expr) : MetaM Expr :=
  withLocalDeclD `t q(ℝ) fun t ↦ do mkLambdaFVars #[t] (← displayTerm t a k u)

/-! ### Context and results -/

/-- The context of the engine. -/
meta structure Context where
  /-- The filter. -/
  filter : CanonicalFilter
  /-- The discharger, for the side goals of `fun_prop`, the signs of the coefficients and of the
  degrees of the exponents, the nonnegativity of real powers and the comparisons of powers. -/
  disch : TSyntax ``Parser.Tactic.tacticSeq
  /-- The variable `t`, a free variable of type `ℝ`. -/
  var : Expr
  /-- Proofs of `(fun t ↦ x) =O[l] g` along the filter, from the hypotheses of the local context,
  which bound the subexpressions `x` to which no rule applies. -/
  hypotheses : Array Expr

/-- The monad of the engine. The error of `ExceptT` is a *decline* of the engine, with a message
saying which subexpression is not bounded (see `throwUnbounded`); the errors of `TacticM` are
failures of the engine. -/
abbrev CompareM := ReaderT Context (ExceptT MessageData TacticM)

/-- The filter `l`, as an expression. -/
meta def filterExpr : CompareM Expr := return (← read).filter.toExpr

/-- The proof of `∀ᶠ t in l, 0 < t`. -/
meta def eventuallyPos : CompareM Expr := return (← read).filter.eventuallyPos

/-- The proof of `Tendsto (fun t ↦ |log t|) l atTop`. -/
meta def tendstoAbsLog : CompareM Expr := return (← read).filter.tendstoAbsLog

/-- The function `fun t ↦ e`. -/
meta def lam (e : Expr) : CompareM Expr := do mkLambdaFVars #[(← read).var] e

/-- Whether `e` depends on `t`. -/
meta def dependsOnVar (e : Expr) : CompareM Bool := return e.containsFVar (← read).var.fvarId!

/-- Check that `proof` proves `(fun t ↦ e) =O[l] M`, or `(fun t ↦ e) =Θ[l] M` if `exact`, and
return it as a `Result`, with this type. -/
meta def mkResult (e : Expr) (m : Majorant) (proof : Expr) (exact := false) :
    CompareM Result := do
  let type ← mkAppM (if exact then ``IsTheta else ``IsBigO) #[← filterExpr, ← lam e, m.toExpr]
  unless ← isDefEq (← inferType proof) type do
    throwError "endpoint_integrability: internal error: the proof{indentExpr proof}\n\
      does not prove{indentExpr type}"
  return ⟨m, ← mkExpectedTypeHint proof type, exact⟩

/-- The `Result` of a lemma concluding `(fun t ↦ e) =O[l] powExp a k u` or
`(fun t ↦ e) =Θ[l] powExp a k u`, read off its type: it is exact in the second case. -/
meta def termResult (e proof : Expr) : CompareM Result := do
  let type ← instantiateMVars (← inferType proof)
  let some g := type.getAppArgs.back? | throwError "endpoint_integrability: internal error: \
    not an `IsBigO` or `IsTheta` statement{indentExpr type}"
  let_expr powExp a k u := g | throwError "endpoint_integrability: internal error: not a \
    comparison function{indentExpr g}"
  mkResult e (.powExp a k u) proof (type.isAppOf ``IsTheta)

/-- Decline, with the message `msg` saying which subexpression is not bounded, so that the engine
tries the next rule (see `compare`). -/
meta def throwUnbounded {α : Type} (msg : MessageData) : CompareM α := do
  throwThe MessageData (← addMessageContext msg)

/-- Run `k`, returning its decline as a value, with the state restored. The failures of the
engine are thrown again. -/
meta def observe {α : Type} (k : CompareM α) : CompareM (Except MessageData α) := do
  let s ← Tactic.saveState
  let n := (← getTraces).size
  let r ← ((k.run (← read)).run : TacticM _)
  if r matches .error _ then
    s.restore
    dropSteps n
  return r

/-! ### Atoms -/

/-- A constant `c`: `isTheta_const_powExp` if `proveCondition?` proves `c ≠ 0`, and
`isBigO_const_powExp` otherwise. -/
meta def constResult (c : Expr) : CompareM Result := do
  let ne ← mkAppM ``Ne #[c, ← mkNumeral (← inferType c) 0]
  if let some hc ← proveCondition? (← read).disch ne then
    return ← termResult c (← mkAppOptM ``isTheta_const_powExp #[← filterExpr, none, none, c, hc])
  termResult c (← mkAppOptM ``isBigO_const_powExp #[← filterExpr, none, none, c])

/-- The atom `t`: `isTheta_id_powExp`. -/
meta def varResult (e : Expr) : CompareM Result := do
  termResult e (← mkAppOptM ``isTheta_id_powExp #[← filterExpr])

/-! ### Registration of the rules -/

/-- A rule of the engine, registered with the attribute `endpoint_compare`. -/
meta structure Rule where
  /-- Bound `fun t ↦ e`, calling `compare` on the subexpressions, or return `none` if the rule
  does not apply to `e`. -/
  eval (e : Expr) : CompareM (Option Result)

/-- Read a rule from a declaration of type `Rule`. -/
meta def mkRule (n : Name) : ImportM Rule := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck Rule opts ``Rule n

/-- The patterns of a rule, as paths in a discrimination tree, and the name of the rule. -/
abbrev RuleEntry := Array (Array DiscrTree.Key) × Name

/-- The environment extension of the rules: a discrimination tree whose values, one per pattern,
are the name of the rule and the rule. -/
meta initialize ruleExt : PersistentEnvExtension RuleEntry (RuleEntry × Rule)
    (List RuleEntry × DiscrTree (Name × Rule)) ←
  -- the values of the same rule are equal, so that a rule is inserted once per pattern
  have : BEq (Name × Rule) := ⟨fun a b ↦ a.1 == b.1⟩
  let insert kss n v dt := kss.foldl (fun dt ks ↦ dt.insertKeyValue ks (n, v)) dt
  registerPersistentEnvExtension {
    mkInitial := pure ([], {})
    addImportedFn := fun s ↦ do
      let dt ← s.foldlM (init := {}) fun dt s ↦ s.foldlM (init := dt) fun dt (kss, n) ↦ do
        pure (insert kss n (← mkRule n) dt)
      pure ([], dt)
    addEntryFn := fun (entries, s) ((kss, n), r) ↦ ((kss, n) :: entries, insert kss n r s)
    exportEntriesFn := fun s ↦ s.1.reverse.toArray
  }

/-- `@[endpoint_compare pat₁, pat₂, …]` registers a declaration of type
`Mathlib.Tactic.EndpointIntegrability.Rule` as a rule of the comparison engine of
`endpoint_integrability`, tried on the expressions which match one of the term patterns
`pat₁, pat₂, …`, such as `_ * _`. The declaration must be `meta` and public. -/
syntax (name := endpoint_compare) "endpoint_compare " term,+ : attr

meta initialize registerBuiltinAttribute {
  name := `endpoint_compare
  descr := "adds a rule to the comparison engine of `endpoint_integrability`"
  applicationTime := .afterCompilation
  add := fun declName stx kind ↦ match stx with
    | `(attr| endpoint_compare $es,*) => do
      ensureAttrDeclIsMeta `endpoint_compare declName kind
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'endpoint_compare', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'endpoint_compare', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let rule ← mkRule declName
      let keys ← MetaM.run' <| es.getElems.mapM fun stx ↦ do
        let e ← Elab.Term.TermElabM.run' <| withSaveInfoContext <|
          Elab.Term.withAutoBoundImplicit <| withReader ({ · with ignoreTCFailures := true }) do
            let e ← Elab.Term.elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e
      setEnv <| ruleExt.addEntry env ((keys, declName), rule)
      recordExtraRevUseOfCurrentModule
    | _ => throwUnsupportedSyntax
}

/-- The rules with a pattern matching `e`, each rule once, in the order of
`Lean.Meta.DiscrTree.getMatch`. -/
meta def matchingRules (e : Expr) : MetaM (Array Rule) := do
  let found ← (ruleExt.getState (← getEnv)).2.getMatch (← instantiateMVars e)
  let mut names : NameSet := {}
  let mut rules := #[]
  for (n, rule) in found do
    unless names.contains n do
      names := names.insert n
      rules := rules.push rule
  return rules

/-! ### Asymptotic facts from the context -/

/-- The function `g` of the hypothesis `h`, if its type is `(fun t ↦ e) =O[l] g` along the filter,
up to instances. The functions are compared up to instances only: a hypothesis about `f ∘ φ` must
be stated as `fun t ↦ f (φ t)`. -/
meta def isBigOHypothesis? (e h : Expr) : CompareM (Option Expr) := do
  let_expr IsBigO _ _ _ _ _ l' f' g := ← instantiateMVars (← inferType h) | return none
  let l ← filterExpr
  let f ← lam e
  let same : MetaM Bool := withNewMCtxDepth <| withTransparency .instances do
    isDefEq l' l <&&> isDefEq f' f
  unless ← same do return none
  return some g

/-! ### The engine -/

/-- Along `𝓝[>] 0`, a function continuous at `0`, as proved by `fun_prop`:
`isBigO_powExp_of_continuousAt`. It is tried after the rules (see `compare`). -/
meta def continuousAtResult? (e : Expr) : CompareM (Option Result) := do
  let .nhdsGT := (← read).filter | return none
  let some hc ← proveFunProp? (← read).disch (← mkAppM ``ContinuousAt #[← lam e, q((0 : ℝ))])
    | return none
  termResult e (← mkAppM ``isBigO_powExp_of_continuousAt #[hc])

mutual

/-- The engine: a majorant of `fun t ↦ e` along the filter, with its proof. A rule which declines
because a subexpression is not bounded is skipped, with the state restored; then the continuity
at `0` (see `continuousAtResult?`) and the hypotheses (see `hypothesisRule`) are tried. If nothing
bounds `e`, the engine declines with the first message of the rules, so that it names the innermost
subexpression which no rule bounds. The result for `e` is traced as a step, whose children are the
steps of the subexpressions which were used (see `nestSteps`): the order of each factor, then that
of the product. -/
meta partial def compare (e : Expr) : CompareM Result := do
  unless ← dependsOnVar e do return ← constResult e
  if e == (← read).var then return ← varResult e
  let n := (← getTraces).size
  let r ← compareTerm e
  have t : Q(ℝ) := (← read).var
  nestSteps n do
    let M ← r.majorant.displayAt t
    if r.exact then sentence [.expr e, .text " has the order of ", .expr M]
    else
      let bound ← ppExpr M
      sentence [.expr e, .text " is in ", .code s!"O({bound})"]
  return r

/-- The engine on an expression `e` which depends on the variable and is not the variable: the
rules, the continuity at `0` and the hypotheses (see `compare`). -/
meta partial def compareTerm (e : Expr) : CompareM Result := do
  let mut unbounded? : Option MessageData := none
  for rule in ← matchingRules e do
    match ← observe (rule.eval e) with
    | .ok (some r) => return r
    | .ok none => pure ()
    | .error msg => if unbounded?.isNone then unbounded? := some msg
  if let some r ← continuousAtResult? e then return r
  if let some r ← hypothesisRule e then return r
  if let some msg := unbounded? then throwUnbounded msg
  let var := (← read).var
  throwUnbounded (← tracedSentence do
    return [.text "no rule bounds ", .expr e, .text " as a function of ", .expr var])

/-- The engine on `e`, or `none`, with the state restored, if it declines. Its failures are thrown
again. A rule need not call it to decline when a subexpression is not bounded: it is for a rule
which tries an alternative itself. -/
meta partial def compare? (e : Expr) : CompareM (Option Result) := do
  match ← observe (compare e) with
  | .ok r => return some r
  | .error _ => return none

/-- A hypothesis `h : (fun t ↦ e) =O[l] g` of the context of the engine (see
`Context.hypotheses` and `isBigOHypothesis?`): `Asymptotics.IsBigO.trans` with the bound of `g`
by the engine. The first hypothesis for which the engine bounds `g` is used. The engine bounds `g`
without the hypotheses, so that hypotheses such as `f =O[l] g` and `g =O[l] f` do not make it
loop. It is tried after the rules. -/
meta partial def hypothesisRule (e : Expr) : CompareM (Option Result) := do
  for h in (← read).hypotheses do
    let some g ← isBigOHypothesis? e h | continue
    let some r ← withReader ({ · with hypotheses := #[] }) <| compare? (g.beta #[(← read).var])
      | continue
    return some (← mkResult e r.majorant (← mkAppM ``IsBigO.trans #[h, ← r.isBigO]))
  return none

end

/-- A majorant `M` of `f : ℝ → E`, for `E` equal to `ℝ` or `ℂ`, along `l`, with a proof of
`f =O[l] M`, or of `f =Θ[l] M` if the result is exact, where `f` is eta-expanded; or, if the
engine declines, its message, which names the innermost subexpression which no rule bounds. The
failures of the engine are thrown. The discharger `disch` proves the side goals of `fun_prop`, the
signs and the comparisons of powers. The `hypotheses`, proofs of `(fun t ↦ x) =O[l] g`, bound the
subexpressions `x` to which no rule applies. -/
meta def majorant (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (hypotheses : Array Expr) (f : Expr) : TacticM (Except MessageData Result) := do
  let s ← saveState
  let n := (← getTraces).size
  let r ← withLocalDeclD `t q(ℝ) fun t ↦ do
    let ctx : Context := { filter := l, disch, var := t, hypotheses }
    ((compare (f.beta #[t])).run ctx).run
  if r matches .error _ then
    s.restore
    dropSteps n
  return r

end Mathlib.Tactic.EndpointIntegrability
