/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Ring
public meta import SpherePacking.Tactic.TendstoContAttr
public meta import SpherePacking.Tactic.AtomEngine

/-!
# `tendsto_cont` tactic

A tactic for proving goals of the form
  `Tendsto (fun z => expr(f₁ z, ..., fₙ z)) l (nhds c)`
where atomic limits `Tendsto fᵢ l (nhds aᵢ)` are known from context
and the expression is continuous in the atoms (proved via `fun_prop`).

This handles any expression where `fun_prop` can prove continuity of the
abstracted body — including polynomials, trigonometric functions,
exponentials, and other compositions.

## Features

- **`tendsto_cont`**: Prove the goal automatically.
- **`tendsto_cont?`**: Report matched atoms and the computed limit
  (the body evaluated at atom limits), then prove.
- **`tendsto_cont (disch := tac)`**: Pass a discharger to `fun_prop` for
  side conditions (e.g., `disch := positivity` for `log`, `inv`, `div`).
- **`tendsto_cont [h₁, h₂]`**: Provide inline `Tendsto` hypotheses.
- Accepts `nhdsWithin` hypotheses (extracts limit via `nhdsWithin_le_nhds`).

## Strategy

1. Parse the goal to extract the body, filter, and target limit.
2. Scan context for `Tendsto` hypotheses matching the goal filter
   (accepts both `nhds` and `nhdsWithin` targets).
3. Identify which atoms appear in the goal body (via `AtomEngine`).
4. Bundle atoms into a right-associated product via `prodMk_nhds`.
5. Abstract the body: replace `fᵢ(z)` with projections from the product.
6. Prove continuity of the abstracted function via `fun_prop`.
7. Combine via `tendsto_continuousAt_comp` and close the goal.
-/

@[expose] public section

open Lean Meta Elab Tactic AtomEngine

/-- Compose a continuous function with a convergent one. Stated with an
    explicit lambda (no `Function.comp`) so the kernel sees the right type. -/
theorem tendsto_continuousAt_comp
    {α β γ : Type*} [TopologicalSpace β] [TopologicalSpace γ]
    {l : Filter α} {f : α → β} {h : β → γ} {b : β}
    (hh : ContinuousAt h b) (hf : Filter.Tendsto f l (nhds b)) :
    Filter.Tendsto (fun x => h (f x)) l (nhds (h b)) :=
  hh.tendsto.comp hf

namespace TendstoCont

-- ══════════════════════════════════════════════════════════════
-- Goal and hypothesis parsing
-- ══════════════════════════════════════════════════════════════

/-- Match `Filter.Tendsto f l target` returning (α, β, f, l, target). -/
private meta def matchTendsto? (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr × Expr)) :=
  return match (← whnfR e).getAppFnArgs with
  | (``Filter.Tendsto, #[α, β, f, l, tgt]) => some (α, β, f, l, tgt)
  | _ => none

/-- Extract the limit from `nhds a`, returning `a`. -/
private meta def matchNhds? (e : Expr) : MetaM (Option Expr) :=
  return match (← whnfR e).getAppFnArgs with
  | (``nhds, #[_, _, a]) => some a
  | _ => none

/-- Extract the limit from `nhdsWithin a s`, returning `(ty, inst, a, s)`. -/
private meta def matchNhdsWithin? (e : Expr) :
    MetaM (Option (Expr × Expr × Expr × Expr)) :=
  return match (← whnfR e).getAppFnArgs with
  | (``nhdsWithin, #[ty, inst, a, s]) => some (ty, inst, a, s)
  | _ => none

/-- Parse the goal `Tendsto goalFn l (nhds c)`, returning `(goalFn, l, domTy)`. -/
private meta def parseGoal (goal : Expr) :
    MetaM (Expr × Expr × Expr) := do
  match ← matchTendsto? goal with
  | some (domTy, _, goalFn, l, tgt) =>
    match ← matchNhds? tgt with
    | some _ => return (goalFn, l, domTy)
    | none =>
      throwError "tendsto_cont: target filter is not `nhds _`"
  | none =>
    throwError "tendsto_cont: goal is not `Tendsto f l (nhds c)`"

/-- Match `Tendsto f l (nhds a)` or `Tendsto f l (nhdsWithin a s)`.
    For `nhdsWithin`, wraps the proof with `mono_right nhdsWithin_le_nhds`
    to produce a `Tendsto f l (nhds a)` proof. -/
private meta def matchTendstoNhdsOrWithin? (e : Expr) (hypExpr : Expr) :
    MetaM (Option (Expr × Expr × Expr × Expr × Expr × Option Expr)) := do
  match ← matchTendsto? e with
  | some (_α, codTy, f, l, tgt) =>
    match ← matchNhds? tgt with
    | some a => return some (codTy, f, l, a, hypExpr, none)
    | none =>
      match ← matchNhdsWithin? tgt with
      | some (ty, inst, a, s) =>
        -- Wrap: Tendsto.mono_right h nhdsWithin_le_nhds
        let nhdsFilter ← mkAppOptM ``nhds #[some ty, some inst, some a]
        let leProof ← mkAppOptM ``nhdsWithin_le_nhds
          #[some ty, some inst, some a, some s]
        let wrappedHyp ← mkAppOptM ``Filter.Tendsto.mono_right
          #[none, none, none, none, none, some nhdsFilter,
            some hypExpr, some leProof]
        return some (codTy, f, l, a, wrappedHyp, some hypExpr)
      | none => return none
  | none => return none

-- ══════════════════════════════════════════════════════════════
-- Candidate collection (Tendsto-specific, three-bucket)
-- ══════════════════════════════════════════════════════════════

/-- Collect atom candidates matching the goal filter.
    Three-bucket collection with cross-bucket shadowing:
    inline args > local context > attribute registry.
    Returns `(candidates, usedAtoms)` — candidates for diagnostics. -/
private meta def collectAtoms (body : Expr) (bvar : FVarId)
    (goalFilter : Expr) (extraHyps : Array Expr := #[]) :
    TacticM (Array Atom × Array Atom) := do
  -- Bucket 1: inline args (highest priority)
  let mut inlineCands : Array Atom := #[]
  for hyp in extraHyps do
    let ty ← inferType hyp >>= instantiateMVars
    match ← matchTendstoNhdsOrWithin? ty hyp with
    | some (codTy, f, l, a, wrappedHyp, origHyp?) =>
      if ← withNewMCtxDepth (isDefEq l goalFilter) then
        inlineCands := inlineCands.push
          { fn := f, value := a, hyp := wrappedHyp, codTy := codTy,
            origHyp := origHyp? }
    | none => continue
  -- Warn about redundant inline args (local hyps that don't disambiguate)
  let ctx ← getLCtx
  for i in [:inlineCands.size] do
    let inlineCand := inlineCands[i]!
    let diagHyp := inlineCand.origHyp.getD inlineCand.hyp
    unless diagHyp.isFVar do continue
    let mut hasConflict := false
    -- Check other inline args for conflicts (same fn, different limit)
    for j in [:inlineCands.size] do
      if i == j then continue
      let other := inlineCands[j]!
      if ← withNewMCtxDepth (isDefEq other.fn inlineCand.fn) then
        unless ← withNewMCtxDepth (isDefEq other.value inlineCand.value) do
          hasConflict := true
    -- Check local context for conflicts (same fn, different limit)
    unless hasConflict do
      for decl in ctx do
        if decl.isImplementationDetail then continue
        if decl.fvarId == diagHyp.fvarId! then continue
        let ty ← instantiateMVars decl.type
        match ← matchTendstoNhdsOrWithin? ty decl.toExpr with
        | some (_, f, l, a, _, _) =>
          if ← withNewMCtxDepth (isDefEq l goalFilter) then
            if ← withNewMCtxDepth (isDefEq f inlineCand.fn) then
              unless ← withNewMCtxDepth (isDefEq a inlineCand.value) do
                hasConflict := true
        | none => continue
    unless hasConflict do
      let name ← ppExpr diagHyp
      logWarning m!"tendsto_cont: inline argument `{name}` is redundant \
        — it is already available as a local hypothesis"
  -- Bucket 2: local context (shadowed by inline)
  let mut contextCands : Array Atom := #[]
  for decl in ctx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    match ← matchTendstoNhdsOrWithin? ty decl.toExpr with
    | some (codTy, f, l, a, wrappedHyp, origHyp?) =>
      if ← withNewMCtxDepth (isDefEq l goalFilter) then
        let dominated ← inlineCands.anyM fun c =>
          withNewMCtxDepth (isDefEq c.fn f)
        unless dominated do
          contextCands := contextCands.push
            { fn := f, value := a, hyp := wrappedHyp, codTy := codTy,
              origHyp := origHyp? }
    | none => continue
  -- Bucket 3: attribute registry (shadowed by inline and context)
  let env ← getEnv
  let higherPriority := inlineCands ++ contextCands
  let mut attrCands : Array Atom := #[]
  for name in (tendstoContExt.getState env).toList do
    try
      let e ← mkConstWithFreshMVarLevels name
      let ty ← inferType e >>= instantiateMVars
      match ← matchTendstoNhdsOrWithin? ty e with
      | some (codTy, f, l, a, wrappedHyp, origHyp?) =>
        if ← withNewMCtxDepth (isDefEq l goalFilter) then
          let dominated ← higherPriority.anyM fun c =>
            withNewMCtxDepth (isDefEq c.fn f)
          unless dominated do
            attrCands := attrCands.push
              { fn := f, value := a, hyp := wrappedHyp, codTy := codTy,
                origHyp := origHyp? }
      | none => continue
    catch _ => continue
  -- Merge and discover atoms via AtomEngine
  let candidates := inlineCands ++ contextCands ++ attrCands
  let atoms ← AtomEngine.findAtoms body bvar candidates
  -- Ambiguity detection
  AtomEngine.checkAmbiguity atoms candidates "tendsto_cont"
  return (candidates, atoms)

-- ══════════════════════════════════════════════════════════════
-- Product proof builder (Tendsto-specific)
-- ══════════════════════════════════════════════════════════════

/-- Chain of `prodMk_nhds` applications from atom hypotheses. -/
private meta def buildProdMkNhds (atoms : Array Atom) :
    MetaM Expr := do
  if atoms.size = 1 then return atoms[0]!.hyp
  let mut proof := atoms.back!.hyp
  for i in List.range (atoms.size - 1) |>.reverse do
    proof ← mkAppM ``Filter.Tendsto.prodMk_nhds #[atoms[i]!.hyp, proof]
  return proof

-- ══════════════════════════════════════════════════════════════
-- Limit reconciliation
-- ══════════════════════════════════════════════════════════════

/-- Close a goal using a proof whose limit may differ from the stated one
    (e.g. `1 + 2` vs `3`, or `b + a` vs `a + b`).
    Uses `convert using 1` then `congr 1; norm_num <;> ring`. -/
private meta def reconcileLimits (goal : MVarId) (proof : Expr) :
    TacticM Unit := do
  let proofTy ← inferType proof
  let keyName := `_tendsto_cont_key
  let goal1 ← goal.define keyName proofTy proof
  let (_, goal2) ← goal1.intro keyName
  let keyId : Ident := mkIdent keyName
  let remaining ← Elab.Tactic.run goal2
    (Elab.Tactic.evalTactic
      (← `(tactic| convert ($keyId) using 1)))
  for g in remaining do
    try
      let r ← Elab.Tactic.run g
        (Elab.Tactic.evalTactic
          (← `(tactic| first
            | rfl
            | (congr 1; norm_num <;> ring))))
      unless r.isEmpty do
        let subgoalTy ← g.getType
        throwError m!"tendsto_cont: subgoal not closed \
          by `rfl`, `norm_num`, or `ring`:\n{subgoalTy}"
    catch e =>
      let subgoalTy ← g.getType
      throwError m!"tendsto_cont: failed to close \
        subgoal after convert:\n{subgoalTy}\n\
        {← e.toMessageData.format}"

-- ══════════════════════════════════════════════════════════════
-- Main tactic
-- ══════════════════════════════════════════════════════════════

/-- Build the continuity-based proof for a non-constant body with atoms.
    `dischStx?` is an optional discharger tactic sequence for `fun_prop`. -/
private meta def buildContinuityProof (body : Expr) (bvar : FVarId)
    (atoms : Array Atom)
    (dischStx? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) := none) :
    TacticM Expr := do
  let prodTy ← AtomEngine.buildProdType atoms
  let limitPt ← AtomEngine.buildValuePoint atoms
  let prodMkProof ← buildProdMkNhds atoms
  withLocalDecl `p .default prodTy fun pVar => do
    let abstracted ← AtomEngine.abstractBody body bvar pVar atoms
    let contFn ← mkLambdaFVars #[pVar] abstracted
    let contGoalTy ← mkAppM ``ContinuousAt #[contFn, limitPt]
    let contMVar ← mkFreshExprMVar contGoalTy
    try
      let _ ← Elab.Tactic.run contMVar.mvarId! <| do
        match dischStx? with
        | some disch =>
          Elab.Tactic.evalTactic (← `(tactic| fun_prop (disch := $disch)))
        | none =>
          Elab.Tactic.evalTactic (← `(tactic| fun_prop))
    catch e =>
      throwError m!"tendsto_cont: `fun_prop` failed:\
        \n{← e.toMessageData.format}\n\
        goal: {contGoalTy}"
    mkAppM ``tendsto_continuousAt_comp #[contMVar, prodMkProof]

/-- Core implementation of the `tendsto_cont` tactic.
    `traceMode` enables diagnostic output for `tendsto_cont?`. -/
private meta def tendstoCont (extraHyps : Array Expr := #[])
    (dischStx? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) := none)
    (traceMode : Bool := false) :
    TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalTy ← goal.getType >>= instantiateMVars

  let (goalFn, goalFilter, domTy) ← parseGoal goalTy

  let body ← match (← whnfR goalFn) with
    | .lam _ _ b _ => pure b
    | _ => throwError
      "tendsto_cont: goal function is not a lambda.\n\
       Hint: try `show Tendsto (fun z => ...) _ (nhds _)` \
       or `unfold ...`"

  let proof? ← withLocalDecl `z .default domTy fun zVar => do
    let body := body.instantiate1 zVar
    let bvar := zVar.fvarId!
    let (candidates, atoms) ← collectAtoms body bvar goalFilter extraHyps

    if atoms.size == 0 then
      if body.containsFVar bvar then
        if candidates.size == 0 then
          let filterFmt ← ppExpr goalFilter
          throwError m!"tendsto_cont: no `Tendsto` hypotheses \
            found for filter `{filterFmt}`"
        else
          let candFns ← candidates.mapM fun c => ppExpr c.fn
          throwError m!"tendsto_cont: body references the \
            bound variable but no candidate matched.\n\
            Available candidates: {candFns}"
      try
        let _ ← Elab.Tactic.run goal
          (Elab.Tactic.evalTactic
            (← `(tactic| exact tendsto_const_nhds)))
        return none
      catch _ =>
        throwError "tendsto_cont: constant body but \
          `tendsto_const_nhds` failed"

    -- Trace mode: report atoms and computed limit
    if traceMode then
      let mut atomDescs : Array MessageData := #[]
      for atom in atoms do
        let fnFmt ← ppExpr atom.fn
        let valFmt ← ppExpr atom.value
        atomDescs := atomDescs.push m!"  {fnFmt} → {valFmt}"
      -- Compute actual limit by substituting atom values into the body.
      -- Instead of going through product abstraction + projection,
      -- directly replace each fᵢ(bvar) with its limit value.
      let computedLimit ← AtomEngine.substituteAtomValues body bvar atoms
      let computedFmt ← ppExpr computedLimit
      logInfo m!"tendsto_cont?: matched atoms:\
        \n{MessageData.joinSep atomDescs.toList "\n"}\
        \ncomputed limit: {computedFmt}"

    some <$> buildContinuityProof body bvar atoms dischStx?

  match proof? with
  | none => return
  | some proof => reconcileLimits goal proof

-- ══════════════════════════════════════════════════════════════
-- Syntax
-- ══════════════════════════════════════════════════════════════

syntax (name := tendstoContBasic) "tendsto_cont" ("[" term,* "]")? : tactic
syntax (name := tendstoContDisch)
  "tendsto_cont" "(" &"disch" ":=" tacticSeq ")" ("[" term,* "]")? : tactic
syntax (name := tendstoContTrace) "tendsto_cont?" ("[" term,* "]")? : tactic
syntax (name := tendstoContTraceDisch)
  "tendsto_cont?" "(" &"disch" ":=" tacticSeq ")" ("[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| tendsto_cont [ $extras,* ]) => do
    let extraHyps ← withMainContext <|
      extras.getElems.mapM fun h => Term.elabTerm h none
    tendstoCont extraHyps
  | `(tactic| tendsto_cont) => tendstoCont
  | `(tactic| tendsto_cont ( disch := $disch ) [ $extras,* ]) => do
    let extraHyps ← withMainContext <|
      extras.getElems.mapM fun h => Term.elabTerm h none
    tendstoCont extraHyps (dischStx? := some disch)
  | `(tactic| tendsto_cont ( disch := $disch )) =>
    tendstoCont (dischStx? := some disch)
  | `(tactic| tendsto_cont? [ $extras,* ]) => do
    let extraHyps ← withMainContext <|
      extras.getElems.mapM fun h => Term.elabTerm h none
    tendstoCont extraHyps (traceMode := true)
  | `(tactic| tendsto_cont?) =>
    tendstoCont (traceMode := true)
  | `(tactic| tendsto_cont? ( disch := $disch ) [ $extras,* ]) => do
    let extraHyps ← withMainContext <|
      extras.getElems.mapM fun h => Term.elabTerm h none
    tendstoCont extraHyps (dischStx? := some disch) (traceMode := true)
  | `(tactic| tendsto_cont? ( disch := $disch )) =>
    tendstoCont (dischStx? := some disch) (traceMode := true)

end TendstoCont
