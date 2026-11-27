/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
module

public import SpherePacking.Tactic.EndpointIntegrability.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic.FunProp
public meta import Mathlib.Tactic.FunProp.Elab
public import Mathlib.Tactic.InferParam
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Tools of `endpoint_integrability`

The tools shared by the steps of the tactic (see `SpherePacking.Tactic.EndpointIntegrability.Tactic`
for the steps); this file belongs to none of them.

* Speculative runs, without error recovery and restoring the state on failure: `attempt?`,
  `attempt`, `tryClose` and `runTactic?`.
* Messages: `sentence`, which lays out a sentence with its expressions, and `traceFailureFirst`,
  which reports a failure with its reasons.
* Steps: `traceStep`, `nestSteps` and `dropSteps`, for the messages which say what the tactic
  establishes.
* Lemma application: `assignChecked`, `applyLemma`, `closeWith` and `proveWith`.
* Continuity, used by the middle of the split and by the measurability: the attribute `fun_prop` on
  `ContinuousOn.rpow_const` and `ContinuousOn.cpow_const`, which belongs in Mathlib; `funProp?`,
  which runs the core of `fun_prop` with only reducible definitions and instances unfolded and
  with a discharger run without error recovery (`funPropCore?`), may leave pointwise side goals,
  and uses the hypotheses about a compound function, such as `Continuous fun x ↦ f x * g x`, as
  `fun_prop` uses those about an opaque one (`funPropRefolded?`); and `proveFunProp?`,
  `proveContinuousOn?` and `throwNotContinuous`, which leave no side goal.
* The default discharger, `defaultDischarger`, and `discharge?`.
-/

@[expose] public section

open Lean Meta Elab Tactic Qq MeasureTheory

namespace Mathlib.Tactic.EndpointIntegrability

/-! ### Speculative runs -/

/-- Run `k`, which tries to close `goal`, without error recovery. Return the result of `k` if it
is `some` and `goal` is then assigned a proof without error-recovery `sorry` (the proof may
contain metavariables: the side goals); otherwise restore the state and return `none`. -/
meta def attempt? {α : Type} (goal : MVarId) (k : TacticM (Option α)) : TacticM (Option α) := do
  let s ← saveState
  try
    if let some a ← withoutRecover k then
      if ← goal.isAssignedOrDelayedAssigned then
        unless (← instantiateMVars (.mvar goal)).hasSyntheticSorry do return some a
  catch _ => pure ()
  s.restore
  return none

/-- Run `k`, which tries to close `goal`, without error recovery. Return `true` if `k` returns
`true` and `goal` is then closed by a proof without error-recovery `sorry`; otherwise restore the
state and return `false`. -/
meta def attempt (goal : MVarId) (k : TacticM Bool) : TacticM Bool :=
  return (← attempt? goal do return if ← k then some () else none).isSome

/-- Run the tactic `tac` on `goal` without error recovery. Return `true` if it closes `goal`;
otherwise restore the state and return `false`. -/
meta def tryClose (goal : MVarId) (tac : TSyntax `tactic) : TacticM Bool :=
  attempt goal do return (← evalTacticAt tac goal).isEmpty

/-- A proof of `type` by the tactic `tac`, run on a new goal by `tryClose`, so without error
recovery, if it closes the goal with a proof without metavariables; otherwise the state is
restored. It runs in `MetaM`, as the discharger of `fun_prop` must.

The discharger which `fun_prop (disch := tac)` builds from `tac` runs `tac` with error recovery
on, so that a failure of `tac` inside `<;>`, `all_goals` or a nested `by` admits the side goal
with `sorry`, and `fun_prop` then proves false statements. -/
meta def runTactic? (tac : TSyntax `tactic) (type : Expr) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let proof ← mkFreshExprSyntheticOpaqueMVar type
    let goal := proof.mvarId!
    discard <| (Tactic.run goal do discard <| tryClose goal tac).run'
    if ← goal.isAssigned then
      let proof ← instantiateMVars proof
      unless proof.hasMVar || proof.hasSyntheticSorry do return some proof
  catch _ => pure ()
  s.restore
  return none

/-! ### Messages -/

/-- A part of a sentence of a message (see `sentence`): static text, in which `\n` forces a line
break, an expression, or code already printed, shown in backticks. -/
meta inductive MsgPart where
  /-- Static text. -/
  | text (s : String)
  /-- An expression, inline in backticks if it is short, and otherwise as an indented block. -/
  | expr (e : Expr)
  /-- Code already printed, inline in backticks. -/
  | code (s : String)

meta instance : Coe String MsgPart := ⟨.text⟩
meta instance : Coe Expr MsgPart := ⟨.expr⟩

/-- The width of the lines of a sentence (see `sentence`): with the indentation of the bullets of
the explanation, at most ten characters, they make at most 96 characters. -/
meta def lineWidth : Nat := 86

/-- The longest expression which a sentence shows inline. -/
meta def inlineWidth : Nat := 50

/-- The sentence made of `parts`, for messages: an expression whose pretty-printed text has at
most `inlineWidth` characters and one line is shown inline in backticks, and a longer one as an
indented block on its own lines (`indentExpr`), the text after it starting a new line, without the
comma which would follow the expression. The words are wrapped greedily, by their measured
lengths, at `lineWidth` characters, and
`\n` in the text forces a line break, unless the line was started by wrapping and has fewer
than 40 characters. The expressions are printed when the sentence is made: it
must be made in their local context. -/
meta def sentence (parts : List MsgPart) : MetaM MessageData := do
  -- the items: words, forced line breaks and blocks
  let mut items : Array (Option (Sum String Expr)) := #[]
  let mut word := ""
  for p in parts do
    match p with
    | .text s =>
      for c in s.toList do
        if c == ' ' || c == '\n' then
          unless word.isEmpty do items := items.push (some (.inl word))
          word := ""
          if c == '\n' then items := items.push none
        else word := word.push c
    | .code s => word := word ++ "`" ++ s ++ "`"
    | .expr e =>
      let str := toString (← ppExpr e)
      if str.length ≤ inlineWidth && !str.contains '\n' then word := word ++ "`" ++ str ++ "`"
      else
        unless word.isEmpty do items := items.push (some (.inl word))
        word := ""
        items := items.push (some (.inr e))
  unless word.isEmpty do items := items.push (some (.inl word))
  let mut out : MessageData := .nil
  let mut line := ""
  -- whether the line was started by wrapping a longer one
  let mut wrapped := false
  let mut afterBlock := false
  for item in items do
    match item with
    | none =>
      -- a forced break right after a wrap would leave a short line: it is then a space
      if wrapped && line.length < 40 then continue
      out := out ++ .ofFormat (.text (line ++ "\n"))
      line := ""
      wrapped := false
    | some (.inr e) =>
      out := out ++ .ofFormat (.text line) ++ indentExpr e
      line := ""
      wrapped := false
      afterBlock := true
    | some (.inl w) =>
      let w := if afterBlock then (w.dropWhile (· == ',')).toString else w
      if afterBlock then
        afterBlock := false
        if w.isEmpty then continue
        out := out ++ .ofFormat (.text "\n")
      if line.isEmpty then line := w
      else if line.length + 1 + w.length ≤ lineWidth then line := line ++ " " ++ w
      else
        out := out ++ .ofFormat (.text (line ++ "\n"))
        line := w
        wrapped := true
  return out ++ .ofFormat (.text line)

/-- The sentence of the parts computed by `parts` (see `sentence`) if the trace class
`Tactic.endpoint_integrability` is enabled, and the empty message otherwise: for the messages which
only a trace shows, such as the declines of the comparison engine, which are frequent, so that
they cost nothing when nobody reads them. -/
meta def tracedSentence (parts : MetaM (List MsgPart)) : MetaM MessageData := do
  unless ← isTracingEnabledFor `Tactic.endpoint_integrability do return .nil
  sentence (← parts)

/-- The message `summary`, followed by the messages `reasons`, as bullets `◦` indented under it. -/
meta def withReasons (summary : MessageData) (reasons : Array MessageData) : MessageData :=
  reasons.foldl (fun m r ↦ m ++ .ofFormat (.text "\n◦ ") ++ .nest 2 r) summary

/-- Run `k`, and, if it returns `none` while the trace class `Tactic.endpoint_integrability` is
enabled, report the failure by the message `msg`: if `nest`, the messages of this class which `k`
produced are its reasons, and are replaced by one message, `msg` followed by them as nested
bullets (see `withReasons`), the other trace messages being left in place; otherwise `msg` is put
before them. Nested calls compose: the message of an inner call is a reason of the outer one. -/
meta def traceFailureFirst {α : Type} (k : TacticM (Option α)) (msg : TacticM MessageData)
    (nest := true) : TacticM (Option α) := do
  let n := (← getTraces).size
  let r ← k
  if r.isNone && (← isTracingEnabledFor `Tactic.endpoint_integrability) then
    let ts := (← getTraces).toArray
    let produced := ts.extract n ts.size
    let isOurs (e : TraceElem) : Bool := match e.msg with
      | .trace data .. => data.cls == `Tactic.endpoint_integrability
      | _ => false
    let summary ← msg
    if nest then
      let reasons := produced.filterMap fun e ↦ match e.msg with
        | .trace data m _ => if data.cls == `Tactic.endpoint_integrability then some m else none
        | _ => none
      modifyTraces fun _ ↦ (ts.extract 0 n ++ produced.filter (!isOurs ·)).toPArray'
      addTrace `Tactic.endpoint_integrability (withReasons summary reasons)
    else
      addTrace `Tactic.endpoint_integrability summary
      modifyTraces fun ts ↦
        let ts := ts.toArray
        (ts.extract 0 n ++ ts.extract (ts.size - 1) ts.size ++ ts.extract n (ts.size - 1)).toPArray'
  return r

/-! ### Steps -/

/-- The trace class of the *steps*: the messages which say what the tactic establishes, such as
the order of a factor, as opposed to those of `Tactic.endpoint_integrability`, which say why a
piece is not proved. They are shown with the latter, in the blocks of the trace (see
`traceBlocks`), and are not part of the explanation of the goals left. The class is not inherited:
it is enabled by the tactic when the user enables `trace.Tactic.endpoint_integrability`. -/
meta def stepClass : Name := `Tactic.endpoint_integrability.step

/-- Whether `e` is a trace message of the steps. -/
meta def isStep (e : TraceElem) : Bool := match e.msg with
  | .trace data .. => data.cls == stepClass
  | _ => false

/-- Trace the step `msg`, if the steps are traced. -/
meta def traceStep (msg : MetaM MessageData) : MetaM Unit := do
  if ← isTracingEnabledFor stepClass then addTrace stepClass (← msg)

/-- Replace the steps traced since the trace had `n` messages by the step `msg`, of which they
become the children: the steps which establish it. -/
meta def nestSteps (n : Nat) (msg : MetaM MessageData) : MetaM Unit := do
  unless ← isTracingEnabledFor stepClass do return
  let msg ← addMessageContext (← msg)
  let ref ← getRef
  modifyTraces fun ts ↦
    let ts := ts.toArray
    let produced := ts.extract n
    let node := .trace { cls := stepClass } msg ((produced.filter isStep).map (·.msg))
    ((ts.extract 0 n ++ produced.filter (!isStep ·)).push { ref, msg := node }).toPArray'

/-- Remove the steps traced since the trace had `n` messages: those of an attempt which is
abandoned. -/
meta def dropSteps (n : Nat) : MetaM Unit := do
  unless ← isTracingEnabledFor stepClass do return
  modifyTraces fun ts ↦
    let ts := ts.toArray
    (ts.extract 0 n ++ (ts.extract n).filter (!isStep ·)).toPArray'

/-! ### Lemma application -/

/-- Assign `proof` to `goal`, after checking that its type is the type of `goal`. -/
meta def assignChecked (goal : MVarId) (proof : Expr) : MetaM Unit := do
  unless ← isDefEq (← goal.getType) (← inferType proof) do
    throwError "endpoint_integrability: internal error: the proof{indentExpr proof}\n\
      does not prove{indentExpr (← goal.getType)}"
  goal.assign proof

/-- The internal error for a lemma `name` which does not have the expected hypotheses. -/
meta def throwUnexpectedHypotheses {α : Type} (name : Name) : MetaM α :=
  throwError "endpoint_integrability: internal error: unexpected hypotheses of `{name}`"

/-- Apply the lemma `name` to `goal`, returning the new goals. -/
meta def applyLemma (goal : MVarId) (name : Name) : MetaM (List MVarId) := do
  goal.apply (← mkConstWithFreshMVarLevels name)

/-- Close `goal` with the lemma `name` applied to `args`, the proofs of its explicit
hypotheses. -/
meta def closeWith (goal : MVarId) (name : Name) (args : List Expr) : MetaM Unit := do
  let goals ← applyLemma goal name
  unless goals.length == args.length do throwUnexpectedHypotheses name
  for g in goals, a in args do assignChecked g a

/-- A proof of `type` by the lemma `name`, which has no explicit hypotheses. -/
meta def proveWith (type : Expr) (name : Name) : MetaM Expr := do
  let proof ← mkFreshExprMVar type
  closeWith proof.mvarId! name []
  instantiateMVars proof

/-! ### Continuity -/

/-! #### `fun_prop` attributes which belong in Mathlib -/

/- Without this attribute, `fun_prop` proves `ContinuousOn (fun x ↦ f x ^ p) s` for a real power
`p` only when `f` is the identity: it decomposes the function as `(· ^ p) ∘ f`, and fails to find
the intermediate set. With it, the continuity of `(x - a) ^ p` on `Ioi a` reduces to the side goal
`∀ x ∈ Ioi a, x - a ≠ 0 ∨ 0 ≤ p`, for the discharger. -/
attribute [fun_prop] ContinuousOn.rpow_const

/- Without this attribute, `fun_prop` does not prove `ContinuousOn (fun x ↦ f x ^ s) t` for a
complex power `s`. With it, the continuity of `(x : ℂ) ^ s` on `Ioi 0` reduces to the side goal
`∀ x ∈ Ioi 0, ↑x ∈ Complex.slitPlane`, for the discharger. -/
attribute [fun_prop] ContinuousOn.cpow_const

/-! #### The discharger -/

/-- The default discharger for the side goals of `fun_prop`, such as `∀ x ∈ Ioi 0, x ≠ 0` or
`0 ≤ s - 1`: a hypothesis, `positivity` or `linarith`, possibly after unfolding the memberships in
intervals, splitting them into one hypothesis per inequality (`positivity` only sees hypotheses
`0 < x`, not conjunctions), writing `↑x ∈ Complex.slitPlane` as `0 < x`, and introducing the
variables and hypotheses of the goal, and then `grind`; a disjunction, such as
`1 + x ^ 2 ≠ 0 ∨ 0 ≤ -3 / 4`, by the same tactics on one of its sides. -/
meta def defaultDischarger : TacticM (TSyntax ``Parser.Tactic.tacticSeq) := do
  let close ← `(tacticSeq| first | assumption | positivity | linarith | grind)
  `(tacticSeq| first
    | assumption
    | positivity
    | linarith
    | (try simp only [Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici,
         Set.mem_Ioi, Set.mem_Iic, Set.mem_Iio, Set.mem_univ, Set.mem_uIcc,
         Complex.ofReal_mem_slitPlane, and_imp] at *
       intros
       first | $close | (left; ($close)) | (right; ($close))))

/-- Whether `type` is a closed pointwise condition `∀ x ∈ t, P x` on the set `t`: it has no
metavariable, and its free variables are in `lctx`. -/
meta def isPointwiseOn (t type : Expr) (lctx : LocalContext) : Bool :=
  !type.hasMVar && !type.hasAnyFVar (!lctx.contains ·) &&
    match type with
    | .forallE _ _ (.forallE _ mem _ _) _ =>
      mem.isAppOfArity ``Membership.mem 5 && mem.appFn!.appArg! == t && mem.appArg! == .bvar 0
    | _ => false

/-- The goals left by `proof`, a proof of `fun_prop` in which the discharger has replaced the side
goals `postponed` by metavariables: one goal per type of the metavariables of `proof` up to
reducible definitional equality (the same condition may come from several lemmas, with different
instances), with the case tag `continuity`, in the local context `lctx` with the instances
`insts`, to which these metavariables are assigned. Returns `none` if `proof` has a metavariable
which is not one of `postponed`, or is delayed-assigned, or a universe metavariable. -/
meta def postponedGoals? (proof : Expr) (postponed : Array MVarId) (lctx : LocalContext)
    (insts : LocalInstances) : MetaM (Option (List MVarId)) := do
  let mvars ← getMVars proof
  if proof.hasLevelMVar then return none
  if mvars.any (!postponed.contains ·) then return none
  if ← mvars.anyM (·.isDelayedAssigned) then return none
  let mut goals : Array (Expr × MVarId) := #[]
  for m in mvars do
    let type ← instantiateMVars (← m.getType)
    if let some (_, g) ← goals.findM? fun (t, _) ↦ withReducible <| isDefEq t type then
      m.assign (.mvar g)
    else
      let g ← mkFreshExprMVarAt lctx insts type .syntheticOpaque `continuity
      m.assign g
      goals := goals.push (type, g.mvarId!)
  return some (goals.toList.map (·.2))

/-- A proof of `type`, a goal of `fun_prop` such as a continuity statement, by `assumption` or by
`fun_prop` with the discharger `disch`, with the side goals left, if it succeeds: the core of
`funProp?`.

This replicates `fun_prop (disch := disch)`, with a fresh state and the default names to unfold:
the discharger tries `with_reducible assumption` and `infer_param`, then `disch`. `fun_prop`
unifies the conclusions of its lemmas with the goal at the ambient transparency. At the default
transparency, a failing unification may unfold the definitions down to filters: for
`ContinuousOn (fun x : ℝ ↦ (x : ℂ) ^ 2) s`, trying `ContinuousOn.zpow₀` on the natural power
costs about 170000 heartbeats. It is therefore run with only reducible definitions and instances
unfolded, and `disch` at the default transparency. Each tactic is run by `runTactic?`, without
error recovery.

If `postponeOn?` is `some t`, a side goal of `fun_prop` which the discharger does not prove and
which is a closed pointwise condition `∀ x ∈ t, P x` (see `isPointwiseOn`) is postponed: it is
left as a goal with the case tag `continuity`, each distinct condition once. The goals left are
the metavariables of the final proof, which must all be such postponed conditions: `fun_prop`
backtracks, and the abandoned attempts leave metavariables behind. If `postponeOn?` is `none`,
the proof has no metavariable. The goals left are created in the local context `lctx`, with the
instances `insts`, which may be smaller than the current one (see `funProp?`). -/
meta def funPropCore? (disch : TSyntax ``Parser.Tactic.tacticSeq) (type : Expr)
    (postponeOn? : Option Expr) (lctx : LocalContext) (insts : LocalInstances) :
    TacticM (Option (Expr × List MVarId)) := do
  let proof ← mkFreshExprMVar type
  if ← proof.mvarId!.assumptionCore then return some (← instantiateMVars proof, [])
  let builtin ← `(tactic| first | with_reducible assumption | infer_param)
  let disch ← `(tactic| ($disch))
  let postponed ← IO.mkRef (#[] : Array MVarId)
  let discharger (type : Expr) : MetaM (Option Expr) :=
      withTraceNode `Meta.Tactic.fun_prop (fun _ ↦ return m!"discharging: {type}") do
    if let some h ← runTactic? builtin type then return some h
    if let some h ← withTransparency .default <| runTactic? disch type then return some h
    let some t := postponeOn? | return none
    let type ← instantiateMVars type
    unless isPointwiseOn t type lctx do return none
    let goal ← mkFreshExprMVarAt lctx insts type .syntheticOpaque `continuity
    postponed.modify (·.push goal.mvarId!)
    return some goal
  let ctx : Mathlib.Meta.FunProp.Context :=
    { disch := discharger, constToUnfold := .ofArray Mathlib.Meta.FunProp.defaultNamesToUnfold _ }
  let env ← getEnv
  let state : Mathlib.Meta.FunProp.State :=
    { morTheorems := Mathlib.Meta.FunProp.morTheoremsExt.getState env
      transitionTheorems := Mathlib.Meta.FunProp.transitionTheoremsExt.getState env }
  let s ← saveState
  try
    let (r?, _) ← withReducibleAndInstances <|
      (Mathlib.Meta.FunProp.funProp type ctx).run state
    if let some r := r? then
      let proof ← instantiateMVars r.proof
      if let some goals ← postponedGoals? proof (← postponed.get) lctx insts then
        return some (← instantiateMVars proof, goals)
  catch _ => pure ()
  s.restore
  return none

/-- The hypotheses of the local context about a *compound* function: for each function `G` which
is a lambda and not the eta-expansion of another term, such as `fun x ↦ f x * g x`, the hypotheses
which state about `G` a property that `fun_prop` proves, such as `Continuous G` or
`ContinuousOn G s`. -/
meta def compoundHypotheses : MetaM (Array (Expr × Array Expr)) := do
  let mut groups : Array (Expr × Array Expr) := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let some (_, G) ← Mathlib.Meta.FunProp.getFunProp? (← instantiateMVars decl.type) | continue
    let .lam _ _ body _ := G | continue
    unless G.eta.isLambda && body.hasLooseBVars do continue
    match groups.findIdx? (·.1 == G) with
    | some i => groups := groups.modify i fun (G, hs) ↦ (G, hs.push decl.toExpr)
    | none => groups := groups.push (G, #[decl.toExpr])
  return groups

/-- The expression `e` with the instances `b x'` of the body of the function `G = fun x ↦ b x`
replaced by `φ x'`, and whether there is one: for `G = fun x ↦ f x * g x`, the subexpression
`f (1 + t) * g (1 + t)` becomes `φ (1 + t)`. -/
meta def abstractInstances (G φ e : Expr) : MetaM (Expr × Bool) := do
  let .lam _ α body _ := G | return (e, false)
  let found ← IO.mkRef false
  let e ← Meta.transform e (pre := fun s ↦ do
    unless s.getAppNumArgs == body.getAppNumArgs &&
      s.getAppFn.constName? == body.getAppFn.constName? do return .continue
    let x ← mkFreshExprMVar α
    unless ← withReducible <| isDefEq (body.instantiate1 x) s do return .continue
    let x ← instantiateMVars x
    if x.hasExprMVar then return .continue
    found.set true
    return .done (mkApp φ x))
  return (e, ← found.get)

/-- `funPropCore?` on `type` after *refolding* the compound functions of the `groups` (see
`compoundHypotheses`): each function `G` with an instance in `type` (see `abstractInstances`)
becomes a variable `φ`, with its hypotheses, so that `fun_prop` treats it as an opaque function
which has these properties; the proof is then applied to `G` and its hypotheses. Returns `none` if
no function has an instance in `type` (`found`), or if `fun_prop` fails. The goals left are in the
local context `lctx`, in which the variables `φ` do not occur. -/
meta def funPropRefolded? (disch : TSyntax ``Parser.Tactic.tacticSeq) (postponeOn? : Option Expr)
    (lctx : LocalContext) (insts : LocalInstances) (groups : List (Expr × Array Expr))
    (type : Expr) (found : Bool := false) : TacticM (Option (Expr × List MVarId)) := do
  match groups with
  | [] => if found then funPropCore? disch type postponeOn? lctx insts else return none
  | (G, hs) :: groups =>
    withLocalDeclD `φ (← inferType G) fun φ ↦ do
      let (type', here) ← abstractInstances G φ type
      unless here do return ← funPropRefolded? disch postponeOn? lctx insts groups type found
      let hTypes ← hs.mapM fun h ↦ do
        return (← instantiateMVars (← inferType h)).replace fun e ↦ if e == G then some φ else none
      withLocalDeclsDND (hTypes.map (`hφ, ·)) fun hφs ↦ do
        let some (proof, goals) ← funPropRefolded? disch postponeOn? lctx insts groups type' true
          | return none
        let proof := mkAppN (← mkLambdaFVars (#[φ] ++ hφs) proof) (#[G] ++ hs)
        return some (← mkExpectedTypeHint proof type, goals)

/-- A proof of `type`, a goal of `fun_prop` such as a continuity statement, by `assumption` or by
`fun_prop` with the discharger `disch`, with the side goals left, if it succeeds (see
`funPropCore?`, of which this is the entry, for the discharger and the goals postponed on
`postponeOn?`).

`fun_prop` uses a hypothesis about an opaque function `f`, such as `hf : Continuous f`, to prove
`ContinuousOn f s`, `Measurable f`, or the continuity of `fun t ↦ f (1 + t)`. It does not for a
compound function: with `hc : Continuous fun x ↦ f x * g x`, it does not prove
`ContinuousOn (fun x ↦ f x * g x) s`, since it looks for the continuity of `f` and of `g`. If it
fails, it is therefore run again with the compound functions of the hypotheses made opaque (see
`funPropRefolded?`). -/
meta def funProp? (disch : TSyntax ``Parser.Tactic.tacticSeq) (type : Expr)
    (postponeOn? : Option Expr := none) : TacticM (Option (Expr × List MVarId)) := do
  let lctx ← getLCtx
  let insts ← getLocalInstances
  if let some r ← funPropCore? disch type postponeOn? lctx insts then return some r
  funPropRefolded? disch postponeOn? lctx insts (← compoundHypotheses).toList type

/-- A proof of `type`, a goal of `fun_prop` such as a continuity statement, by `assumption` or by
`fun_prop` with the discharger `disch` (see `funProp?`), if it succeeds. -/
meta def proveFunProp? (disch : TSyntax ``Parser.Tactic.tacticSeq) (type : Expr) :
    TacticM (Option Expr) := do
  return (← funProp? disch type).map (·.1)

/-- A proof of `type` by the discharger `disch`, if it succeeds. -/
meta def discharge? (disch : TSyntax ``Parser.Tactic.tacticSeq) (type : Expr) :
    TacticM (Option Expr) := do
  let proof ← mkFreshExprMVar type
  unless ← tryClose proof.mvarId! (← `(tactic| ($disch))) do return none
  instantiateMVars proof

/-- A proof of `ContinuousOn f s` by `proveFunProp? disch`, if it succeeds. -/
meta def proveContinuousOn? (disch : TSyntax ``Parser.Tactic.tacticSeq) (f s : Expr) :
    TacticM (Option Expr) := do
  proveFunProp? disch (← mkAppM ``ContinuousOn #[f, s])

/-- The error for a continuity statement `type` which could not be proved. -/
meta def throwNotContinuous {α : Type} (type : Expr) : MetaM α :=
  throwError "endpoint_integrability: failed to prove{indentExpr type}\nby `assumption` or \
    `fun_prop`"

end Mathlib.Tactic.EndpointIntegrability
