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
  `Tendsto (fun z => expr(f₁ z, ..., fₙ z)) l (nhds c)` or
  `Tendsto (fun z => expr(f₁ z, ..., fₙ z)) l (nhdsWithin c s)`
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
  continuity side conditions (e.g., `disch := positivity` for `log`, `inv`).
- **`tendsto_cont (within_disch := tac)`**: Discharge the `∀ᶠ x in l,
  body x ∈ s` obligation for `nhdsWithin` goals. The tactic is tried
  directly on the `∀ᶠ` goal, then auto-lifted pointwise via
  `Filter.univ_mem'` (so `within_disch := norm_num` works for constant
  membership like `2 ∈ Set.Ioi 0`). Both hooks compose in either order.
- **`tendsto_cont [h₁, h₂]`**: Provide inline `Tendsto` hypotheses.
- Accepts `nhdsWithin` hypotheses (extracts limit via `nhdsWithin_le_nhds`).
- Accepts `nhdsWithin` goals: proves the `nhds` part automatically, then
  tries to close `∀ᶠ x in l, body x ∈ s` via `assumption` or `univ_mem'`
  (when the predicate reduces to `True`). Leaves the `∀ᶠ` subgoal for
  the user if undischargeable.

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

/-- Result of parsing a `Tendsto` goal. -/
meta inductive GoalTarget
  | nhds
  | nhdsWithin (withinSet : Expr)

/-- Parse the goal `Tendsto goalFn l (nhds c)` or
    `Tendsto goalFn l (nhdsWithin c s)`,
    returning `(goalFn, l, domTy, target)`. -/
private meta def parseGoal (goal : Expr) :
    MetaM (Expr × Expr × Expr × GoalTarget) := do
  match ← matchTendsto? goal with
  | some (domTy, _, goalFn, l, tgt) =>
    match ← matchNhds? tgt with
    | some _ => return (goalFn, l, domTy, .nhds)
    | none =>
      match ← matchNhdsWithin? tgt with
      | some (_, _, _, s) => return (goalFn, l, domTy, .nhdsWithin s)
      | none =>
        throwError "tendsto_cont: target filter is not `nhds _` or `nhdsWithin _ _`"
  | none =>
    throwError "tendsto_cont: goal is not `Tendsto f l (nhds c)` or \
      `Tendsto f l (nhdsWithin c s)`"

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
-- nhdsWithin ∀ᶠ discharge
-- ══════════════════════════════════════════════════════════════

/-- How the ∀ᶠ obligation was discharged. -/
meta inductive EvDischargeMethod
  | assumption     -- matched a local hypothesis
  | univMem        -- predicate reduced to True (e.g., Set.univ)
  | withinDisch    -- user-provided within_disch tactic (direct)
  | pointwiseLift  -- user-provided within_disch tactic (pointwise lift)
  | undischarged   -- left for the user

/-- Format the discharge method for trace output. -/
private meta def EvDischargeMethod.toMessageData : EvDischargeMethod → MessageData
  | .assumption    => "discharged ∀ᶠ via assumption"
  | .univMem       => "discharged ∀ᶠ via univ_mem' (trivially true)"
  | .withinDisch   => "discharged ∀ᶠ via within_disch"
  | .pointwiseLift => "discharged ∀ᶠ via within_disch (pointwise lift)"
  | .undischarged  => "∀ᶠ membership obligation left for user"

/-- Try to close an `∀ᶠ x in l, body x ∈ s` goal from nhdsWithin splitting.
    Returns `(remaining_goals, discharge_method)`. -/
private meta def tryEvGoal (g : MVarId)
    (withinDischStx? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) := none) :
    TacticM (List MVarId × EvDischargeMethod) := do
  -- Try assumption (atomic, finds ∀ᶠ hypotheses in context)
  let r ← try
    Elab.Tactic.run g
      (Elab.Tactic.evalTactic (← `(tactic| assumption)))
  catch _ => pure [g]
  if r.isEmpty then return (r, .assumption)
  -- Try univ_mem' for Set.univ or other trivially-true membership.
  let gTy ← g.getType >>= instantiateMVars
  match gTy.getAppFnArgs with
  | (``Filter.Eventually, #[_, pred, _]) =>
    let domTy ← try
      let fnTy ← inferType pred
      match fnTy with
      | .forallE _ t _ _ => pure (some t)
      | _ => pure none
    catch _ => pure none
    match domTy with
    | some dt =>
      let bodyIsTrivial ← withLocalDecl `_x .default dt fun x => do
        let body := mkApp pred x
        let reduced ← whnf body
        return reduced.isConstOf ``True
      if bodyIsTrivial then
        let r ← try
          Elab.Tactic.run g
            (Elab.Tactic.evalTactic
              (← `(tactic| exact Filter.univ_mem' (fun _ => trivial))))
        catch _ => pure [g]
        if r.isEmpty then return (r, .univMem)
    | none => pure ()
  | _ => pure ()
  -- Try user-provided within_disch tactic
  match withinDischStx? with
  | some disch =>
    -- Direct attempt on the ∀ᶠ goal
    let r ← try
      Elab.Tactic.run g
        (Elab.Tactic.evalTactic (← `(tactic| ($disch))))
    catch _ => pure [g]
    if r.isEmpty then return (r, .withinDisch)
    -- Pointwise lift: apply Filter.univ_mem', intro, then the tactic
    let r ← try
      Elab.Tactic.run g
        (Elab.Tactic.evalTactic
          (← `(tactic| apply Filter.univ_mem'; intro _; ($disch))))
    catch _ => pure [g]
    if r.isEmpty then return (r, .pointwiseLift)
  | none => pure ()
  return ([g], .undischarged)

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
    (withinDischStx? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) := none)
    (traceMode : Bool := false) :
    TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalTy ← goal.getType >>= instantiateMVars

  let (goalFn, goalFilter, domTy, goalTarget) ← parseGoal goalTy

  let body ← match (← whnfR goalFn) with
    | .lam _ _ b _ => pure b
    | _ => throwError
      "tendsto_cont: goal function is not a lambda.\n\
       Hint: try `show Tendsto (fun z => ...) _ _` or `unfold ...`"

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
      -- Constant body: no atoms, body doesn't reference bound variable
      if traceMode then
        let valFmt ← ppExpr body
        let withinMsg ← match goalTarget with
          | .nhds => pure m!""
          | .nhdsWithin s =>
            let sFmt ← ppExpr s
            pure m!"\nnhdsWithin set: {sFmt}"
        logInfo m!"tendsto_cont?: constant body\
          \ncomputed limit: {valFmt}{withinMsg}"
      match goalTarget with
      | .nhds =>
        try
          let _ ← Elab.Tactic.run goal
            (Elab.Tactic.evalTactic
              (← `(tactic| exact tendsto_const_nhds)))
          return none
        catch _ =>
          throwError "tendsto_cont: constant body but \
            `tendsto_const_nhds` failed"
      | .nhdsWithin _ =>
        let remaining ← Elab.Tactic.run goal
          (Elab.Tactic.evalTactic
            (← `(tactic|
              refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds, ?_⟩)))
        let mut leftover : List MVarId := []
        for g in remaining do
          let (r, method) ← tryEvGoal g withinDischStx?
          if traceMode then
            logInfo m!"tendsto_cont?: {method.toMessageData}"
          leftover := leftover ++ r
        Elab.Tactic.replaceMainGoal leftover
        return (none : Option Expr)

    -- Trace mode: report atoms and computed limit
    if traceMode then
      let mut atomDescs : Array MessageData := #[]
      for atom in atoms do
        let fnFmt ← ppExpr atom.fn
        let valFmt ← ppExpr atom.value
        atomDescs := atomDescs.push m!"  {fnFmt} → {valFmt}"
      let computedLimit ← AtomEngine.substituteAtomValues body bvar atoms
      let computedFmt ← ppExpr computedLimit
      let withinMsg ← match goalTarget with
        | .nhds => pure m!""
        | .nhdsWithin s =>
          let sFmt ← ppExpr s
          pure m!"\nnhdsWithin set: {sFmt}\
            \n  (∀ᶠ membership obligation will be attempted)"
      logInfo m!"tendsto_cont?: matched atoms:\
        \n{MessageData.joinSep atomDescs.toList "\n"}\
        \ncomputed limit: {computedFmt}{withinMsg}"

    some <$> buildContinuityProof body bvar atoms dischStx?

  match proof? with
  | none => return
  | some nhdsProof =>
    match goalTarget with
    | .nhds => reconcileLimits goal nhdsProof
    | .nhdsWithin _withinSet =>
      -- For nhdsWithin goals, we have a proof of Tendsto body l (nhds c').
      -- We need: Tendsto body l (nhdsWithin c s).
      -- Strategy: apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      -- which requires (1) nhds proof and (2) ∀ᶠ x in l, body x ∈ s.
      -- First reconcile the nhds proof's limit with the goal's limit,
      -- then try to close the ∀ᶠ side condition.
      let remaining ← Elab.Tactic.run goal
        (Elab.Tactic.evalTactic
          (← `(tactic| apply tendsto_nhdsWithin_iff.mpr; constructor)))
      -- remaining should have two subgoals: nhds part and ∀ᶠ part
      match remaining with
      | [nhdsGoal, evGoal] =>
        -- Close nhds subgoal using the proof we built
        reconcileLimits nhdsGoal nhdsProof
        -- Try to close the ∀ᶠ subgoal. If we can't, leave it for user.
        let (evRemaining, method) ← tryEvGoal evGoal withinDischStx?
        if traceMode then
          logInfo m!"tendsto_cont?: {method.toMessageData}"
        Elab.Tactic.replaceMainGoal evRemaining
      | _ =>
        -- Fallback: just try reconcileLimits directly
        reconcileLimits goal nhdsProof

-- ══════════════════════════════════════════════════════════════
-- Syntax
-- ══════════════════════════════════════════════════════════════

-- Explicit syntax rules for all combinations.
-- Option order is flexible: disch and within_disch can appear in either order.
syntax "tendsto_cont" ("[" term,* "]")? : tactic
syntax "tendsto_cont" "(" &"disch" ":=" tacticSeq ")" ("[" term,* "]")? : tactic
syntax "tendsto_cont" "(" &"within_disch" ":=" tacticSeq ")"
  ("[" term,* "]")? : tactic
syntax "tendsto_cont" "(" &"disch" ":=" tacticSeq ")"
  "(" &"within_disch" ":=" tacticSeq ")" ("[" term,* "]")? : tactic
syntax "tendsto_cont" "(" &"within_disch" ":=" tacticSeq ")"
  "(" &"disch" ":=" tacticSeq ")" ("[" term,* "]")? : tactic
syntax "tendsto_cont?" ("[" term,* "]")? : tactic
syntax "tendsto_cont?" "(" &"disch" ":=" tacticSeq ")" ("[" term,* "]")? : tactic
syntax "tendsto_cont?" "(" &"within_disch" ":=" tacticSeq ")"
  ("[" term,* "]")? : tactic
syntax "tendsto_cont?" "(" &"disch" ":=" tacticSeq ")"
  "(" &"within_disch" ":=" tacticSeq ")" ("[" term,* "]")? : tactic
syntax "tendsto_cont?" "(" &"within_disch" ":=" tacticSeq ")"
  "(" &"disch" ":=" tacticSeq ")" ("[" term,* "]")? : tactic

private meta def elabExtras (extras : Syntax.TSepArray `term ",") :
    TacticM (Array Expr) :=
  withMainContext <| extras.getElems.mapM fun h => Term.elabTerm h none

-- Shared handler abbreviation
private meta def tc (extras? : Option (Syntax.TSepArray `term ",") := none)
    (d? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) := none)
    (wd? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) := none)
    (trace : Bool := false) : TacticM Unit := do
  let hyps ← match extras? with
    | some e => elabExtras e | none => pure #[]
  tendstoCont hyps d? wd? trace

elab_rules : tactic
  | `(tactic| tendsto_cont $[[ $e,* ]]?) => tc (extras? := e)
  | `(tactic| tendsto_cont ( disch := $d ) $[[ $e,* ]]?) =>
    tc (extras? := e) (d? := d)
  | `(tactic| tendsto_cont ( within_disch := $wd ) $[[ $e,* ]]?) =>
    tc (extras? := e) (wd? := wd)
  | `(tactic| tendsto_cont ( disch := $d ) ( within_disch := $wd )
      $[[ $e,* ]]?) => tc (extras? := e) (d? := d) (wd? := wd)
  | `(tactic| tendsto_cont ( within_disch := $wd ) ( disch := $d )
      $[[ $e,* ]]?) => tc (extras? := e) (d? := d) (wd? := wd)

elab_rules : tactic
  | `(tactic| tendsto_cont? $[[ $e,* ]]?) =>
    tc (extras? := e) (trace := true)
  | `(tactic| tendsto_cont? ( disch := $d ) $[[ $e,* ]]?) =>
    tc (extras? := e) (d? := d) (trace := true)
  | `(tactic| tendsto_cont? ( within_disch := $wd ) $[[ $e,* ]]?) =>
    tc (extras? := e) (wd? := wd) (trace := true)
  | `(tactic| tendsto_cont? ( disch := $d ) ( within_disch := $wd )
      $[[ $e,* ]]?) => tc (extras? := e) (d? := d) (wd? := wd) (trace := true)
  | `(tactic| tendsto_cont? ( within_disch := $wd ) ( disch := $d )
      $[[ $e,* ]]?) => tc (extras? := e) (d? := d) (wd? := wd) (trace := true)

end TendstoCont
