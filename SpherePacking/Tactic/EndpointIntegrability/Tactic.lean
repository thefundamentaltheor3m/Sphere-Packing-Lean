/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
module

public import SpherePacking.Tactic.EndpointIntegrability.Domination
public import SpherePacking.Tactic.EndpointIntegrability.Endpoint

/-!
# The `endpoint_integrability` tactic

`endpoint_integrability` proves that a function `f : ℝ → E` is integrable on an interval. It
follows one idea, in four steps.

1. **Split.** A function is integrable on an interval if and only if it is locally integrable on
   the interval and integrable near each end which is open or infinite. The goal is split into
   one goal for the *middle*, `LocallyIntegrableOn f t μ`, and one goal `IntegrableAtFilter f l μ`
   per *end*, with `l` one of `atBot`, `atTop`, `𝓝[>] a` and `𝓝[<] b`
   (`SpherePacking.Tactic.EndpointIntegrability.Interval`).
2. **Classify.** Each piece is proved by dominating `f` there by a function known to be
   integrable. A term of the integrand is of one of three kinds:
   * *integrable*: a factor `G x` which the context proves integrable, such as `g x` with
     `Integrable g`. The other factors then need only be bounded
     (`SpherePacking.Tactic.EndpointIntegrability.Factor`);
   * *bounded*: a term which the context bounds, such as `g x` with `∀ x, ‖g x‖ ≤ C`, or
     `Int.fract x` with `∀ x, ‖Int.fract x‖ ≤ 1`. It is replaced by its bound
     (`SpherePacking.Tactic.EndpointIntegrability.Domination`);
   * *explicit*: everything else, which the next step bounds.
3. **Bound.** In the middle, an explicit function is locally bounded because it is continuous, by
   `fun_prop`. At an end, moved to `0⁺` or `+∞` by a change of variables, it is bounded by a sum
   of functions of one fixed scale, `t ^ a * |log t| ^ k * exp (u t)`, by one rule per operation
   (`SpherePacking.Tactic.EndpointIntegrability.Compare` and
   `SpherePacking.Tactic.EndpointIntegrability.Rules`).
4. **Decide.** Whether `t ^ a * |log t| ^ k * exp (u t)` is integrable, or bounded, at the end
   is read off `a`, `k` and the leading monomial of `u`
   (`SpherePacking.Tactic.EndpointIntegrability.Exponent` and
   `SpherePacking.Tactic.EndpointIntegrability.Decide`). With an integrable factor the bound of
   the other factors must be bounded; without one it must be integrable.

A piece which is not proved is left as a goal, as it is. One end, steps 2 to 4 at an end, is
`SpherePacking.Tactic.EndpointIntegrability.Endpoint`; the shared tools are
`SpherePacking.Tactic.EndpointIntegrability.Basic`, and the lemmas
`SpherePacking.Tactic.EndpointIntegrability.Lemmas` and
`SpherePacking.Tactic.EndpointIntegrability.Scale`. This file is the driver.

## Supported goals

The integrand is `f : ℝ → E`, for a normed group `E`, and the measure `μ` is any measure for which
the lemmas apply, typically `[IsLocallyFiniteMeasure μ]`; a missing instance is reported as an
error. The ends are proved by comparison or through an integrable factor only for the measure
`volume`. The supported goals are
* `IntegrableOn f s μ`, `Integrable f (μ.restrict s)` and `Integrable f μ` (on `univ`), for `s` one
  of `Icc a b`, `Ico a b`, `Ioc a b`, `Ioo a b`, `Ici a`, `Ioi a`, `Iic b`, `Iio b` and `univ`;
* `IntervalIntegrable f μ a b`, from the continuity of `f` on `uIcc a b`, or as
  `IntegrableOn f (Ioc a b) μ` if the discharger proves `a ≤ b`;
* `LocallyIntegrableOn f s μ`, for `s` as above, and `LocallyIntegrable f μ`, from the continuity
  of `f` only.

Before anything else, the operations on functions of a real variable are unfolded in the goal and
in the hypotheses (`unfoldPointwiseGoal`): `f * g` becomes `fun x ↦ f x * g x`, and likewise for
sums, differences, quotients, negations, inverses, powers, scalar multiples and compositions. The
factors of the integrand are then seen, and a hypothesis about `f * g` and an integrand
`fun x ↦ f x * g x` have the same shape, whichever way each was written; the goals left show the
unfolded form. Every goal is then first tried by `assumption` and `fun_prop`.

## Order

On `IntegrableOn f s μ` (`proveIntegrableOn`), the pieces of `f` are proved first (`provePieces`):
the middle by the continuity of `f`, or else through an integrable factor; each end by a
hypothesis, then by comparison with the scale, then through an integrable factor (`proveEnd`). If
this leaves an integrability goal and `f` has bounded terms, the pieces of its majorant are proved
instead, and replace those of `f` only if they leave no integrability goal.

## Goals left

The goals which are not closed are returned in this order, with these case tags: the side goals of
the continuity in the middle (`continuity`), each distinct one once, or else `locallyIntegrableOn`,
then the goal at the lower end, then the goal at the upper end: `atBot` and `atTop` for the
infinite ends, and a finite end is named after the end, as `nhds0` or `nhdsa` (`nhdsGT` and
`nhdsLT` if the end is not a numeral or a variable). An end which is proved up to conditions on
parameters, such as `1 < s` or `0 ≤ s`, or on the signs of the coefficients of an exponent, such as
`0 < n` for `rexp (-n * x)`, leaves these conditions instead, with the case tag of the end, in the
order of the terms of the majorant; a false condition only means that the comparison failed. When
the pieces of a majorant are kept, their goals are left, in the same order and with the same tags.
With `set_option trace.Tactic.endpoint_integrability true`, the tactic reports why an end, the
middle through an integrable factor, or a majorant is not proved.

When an integrability goal is left (a piece, not a side condition), the tactic logs one `info`
message which gives, for each piece left, the messages of this trace class about it, in order,
then those about the majorant, if it was tried, and the forms of the hypotheses which the tactic
uses (`withExplanation`). These messages are collected between the markers of `withPieceMarkers`,
which survive the restorations of the state. `set_option tactic.endpoint_integrability.explain
false` turns the message off.

## The discharger

The discharger proves the side goals of `fun_prop`, such as `∀ x ∈ Ioi 0, x ≠ 0`, the conditions
`a ≤ b` and `a < b` on the ends, and the signs and conditions of the comparison, such as `-b < 0`
or `-1 < s - 1`. The default one tries hypotheses, `positivity`, `linarith` and `grind`, after
unfolding memberships in intervals into one hypothesis per inequality, also on each side of a
disjunction (see `defaultDischarger`); it does not prove nonlinear conditions such as
`x ^ 2 - 1 ≠ 0` on `Ioi 2`. Another one is given by `endpoint_integrability (disch := tac)`, and is
run without error recovery (see `runTactic?`).

## What the tactic does not do

These are left to the user, as a `have` before the tactic or as a goal after it.
* Unknown terms are not assumed bounded: state `f =O[l] fun _ ↦ 1` or a pointwise bound
  `∀ x, ‖f x‖ ≤ C`.
* Hypotheses are used as stated, not instantiated: for `h : ∀ k, Integrable (φ k)`, state
  `have := h k`.
* The goal is not split on the order of the ends: have `a < b` in the context.
* No `split_ifs`: for `if p then g x else 0`, run `split_ifs <;> endpoint_integrability`.
* No finite sums: apply `MeasureTheory.integrable_finsetSum` first.
* An integrable factor must be a hypothesis: for a Schwartz function `b`,
  `have hb : Integrable b := b.integrable`.
* Hypotheses `F =O[l] G` must be along the filter of the end, such as `atTop`, not `cocompact ℝ`:
  state `h.mono atTop_le_cocompact`.
-/

@[expose] public section

open Lean Meta Elab Tactic Qq MeasureTheory

namespace Mathlib.Tactic.EndpointIntegrability

/-! ### Markers of the pieces -/

/-- The internal trace class of the markers which delimit, in the trace, the messages about each
piece of the split and about the majorant (see `pushMarker`). It is not inherited: it is enabled
only while the explanation of the goals left is collected (see `withExplanation`), and its messages
are never shown. -/
meta initialize registerTraceClass `Tactic.endpoint_integrability.piece

/-- The names of the markers: the start of the messages about the piece with the goal `g` is
`pieceBegin ++ g.name`, their end `pieceLeft ++ g.name` if `g` is left and `pieceProved ++ g.name`
otherwise; the messages about the majorant lie between `majorantBegin` and `majorantEnd`. -/
meta def pieceBegin : Name := `endpointIntegrabilityPieceBegin
@[inherit_doc pieceBegin] meta def pieceLeft : Name := `endpointIntegrabilityPieceLeft
@[inherit_doc pieceBegin] meta def pieceProved : Name := `endpointIntegrabilityPieceProved
@[inherit_doc pieceBegin] meta def majorantBegin : Name := `endpointIntegrabilityMajorantBegin
@[inherit_doc pieceBegin] meta def majorantEnd : Name := `endpointIntegrabilityMajorantEnd
@[inherit_doc pieceBegin] meta def majorantProved : Name := `endpointIntegrabilityMajorantProved

/-- Push the marker `tag` to the trace, if the trace class `Tactic.endpoint_integrability.piece`
is enabled. A marker which ends a piece or the majorant carries its `outcome`, such as
`: proved`, for the trace (see `traceBlocks`). -/
meta def pushMarker (tag : Name) (outcome : MessageData := .nil) : TacticM Unit := do
  if ← isTracingEnabledFor `Tactic.endpoint_integrability.piece then
    let msg := .trace { cls := `Tactic.endpoint_integrability.piece } (.tagged tag outcome) #[]
    modifyTraces (·.push { ref := ← getRef, msg })

/-- Run `k`, which proves the piece `goal` and returns the goals left, between the markers of
`goal` (see `pieceBegin`): `goal` is left if it is among them. The trace announces the piece first
by its case tag, `case atTop`, which is the first message between the markers, and the marker
which ends the piece says whether it is proved, and with how many conditions left as goals. -/
meta def withPieceMarkers (goal : MVarId) (k : TacticM (List MVarId)) : TacticM (List MVarId) := do
  pushMarker (pieceBegin ++ goal.name)
  trace[Tactic.endpoint_integrability] "case {← goal.getTag}"
  let goals ← try k catch e => pushMarker (pieceProved ++ goal.name); throw e
  if goals.contains goal then pushMarker (pieceLeft ++ goal.name) m!": not proved"
  else
    let n := goals.length
    pushMarker (pieceProved ++ goal.name) <| if n == 0 then m!": proved" else
      m!": proved, with {n} condition{if n == 1 then "" else "s"} left as \
        goal{if n == 1 then "" else "s"}"
  return goals

/-! ### The pieces -/

/-- The pieces: split `IntegrableOn f s μ` into the middle and the ends, and prove each.

The integrand is proved continuous on an interval `t` with the ends of `s`, as closed as possible
(`continuityInterval`), `IntegrableOn f t μ` is split by the decomposition lemma of `t`
(`decompose`), and the goal on `s` follows from it (`transport`). The middle is proved by the
continuity or, failing it, through an integrable factor (`proveMiddleByFactor?`), and each end by
`proveEnd`. Returns the goals which are left, in this order: the side goals of the continuity, or
else those of the integrable factor, or else the goal `LocallyIntegrableOn f t μ`, and the goals
of the ends. The messages call `f` `noun`: `the integrand`, or `the majorant` for the pieces of a
majorant. -/
meta def provePieces (disch : TSyntax ``Parser.Tactic.tacticSeq) (goal : MVarId) (f μ : Expr)
    (s : Interval) (noun := "the integrand") : TacticM (List MVarId) := do
  let (t, hc?, sideGoals) ← continuityInterval disch f s
  let ht ← mkFreshExprMVar (← mkAppM ``IntegrableOn #[f, ← t.toExpr, μ])
  let (loc?, ends) ← decompose ht.mvarId! f μ t hc? noun
  assignChecked goal (← transport ht t s)
  let locGoals ← match loc? with
    | some loc => withPieceMarkers loc do
      trace[Tactic.endpoint_integrability] "{← sentence [.text s!"{noun} is not proved continuous \
        on ", .expr (← t.toExpr), .text ", by a hypothesis or `fun_prop`"]}"
      return (← attempt? loc (proveMiddleByFactor? disch loc f μ t noun)).getD [loc]
    | none =>
      traceStep <| sentence [.text s!"{checkEmoji} in the middle: {noun} is continuous on ",
        .expr (← t.toExpr)]
      pure []
  let endGoals ← ends.flatMapM fun g ↦ withPieceMarkers g.goal (proveEnd disch g)
  return sideGoals ++ locGoals ++ endGoals

/-- Whether `goal` is an integrability goal, such as `IntegrableAtFilter f l μ`, rather than a side
condition. -/
meta def isIntegrabilityGoal (goal : MVarId) : MetaM Bool := do
  let type ← instantiateMVars (← goal.getType)
  return [``IntegrableAtFilter, ``LocallyIntegrableOn, ``IntegrableOn, ``Integrable].any
    type.isAppOf

/-- `IntegrableOn f s μ`: the pieces of `f`; if this leaves an integrability goal and `f` has
bounded terms, the pieces of its majorant instead.

The pieces of `f` which leave only side conditions are kept: the majorant could only replace them
by stronger ones. The result of the majorant replaces them only if it leaves no integrability
goal (see `majorantPieces?`). Returns the goals which are left. -/
meta def proveIntegrableOn (disch : TSyntax ``Parser.Tactic.tacticSeq) (goal : MVarId)
    (f μ : Expr) (s : Interval) : TacticM (List MVarId) := do
  let initial ← saveState
  let goals ← provePieces disch goal f μ s
  unless ← goals.anyM (isIntegrabilityGoal ·) do return goals
  let direct ← saveState
  initial.restore
  pushMarker majorantBegin
  let majorant? ← attempt? goal (majorantPieces? disch goal f μ s)
  if majorant?.isSome then
    pushMarker majorantProved m!": the majorant is integrable, and so is the integrand"
  else pushMarker majorantEnd m!": not proved"
  if let some goals := majorant? then return goals
  direct.restore
  return goals
where
  /-- Prove `goal : IntegrableOn f s μ` from the integrability on `s` of the majorant `M` of `f`
  (see `majorant?`), proved by `provePieces` (not again through a majorant), the bound
  `∀ x ∈ s, ‖f x‖ ≤ M x`, and the almost everywhere strong measurability of `f` on `s` (see
  `aestronglyMeasurable?`). Returns `none` if `f` has no bounded term, or if one of these is not
  proved, the pieces of `M` leaving an integrability goal counting as a failure; otherwise the
  side goals left by the pieces of `M`. -/
  majorantPieces? (disch : TSyntax ``Parser.Tactic.tacticSeq) (goal : MVarId) (f μ : Expr)
      (s : Interval) : TacticM (Option (List MVarId)) := do
    let set ← s.toExpr
    let majorant? ← tryCatch (majorant? f set) fun e ↦ do
      trace[Tactic.endpoint_integrability] "{e.toMessageData}"
      return none
    let some (M, hle) := majorant? | return none
    trace[Tactic.endpoint_integrability] "{← sentence ["the majorant is ", M]}"
    let hs ← proveWith (← mkAppM ``MeasurableSet #[set]) (← s.shape).measurableSet
    let some hf ← aestronglyMeasurable? disch f μ hs s
      | trace[Tactic.endpoint_integrability] "the integrand is not proved measurable"
        return none
    let hM ← mkFreshExprMVar (← mkAppM ``IntegrableOn #[M, set, μ])
    let goals ← provePieces disch hM.mvarId! M μ s "the majorant"
    if ← goals.anyM (isIntegrabilityGoal ·) then
      trace[Tactic.endpoint_integrability] "the majorant is not proved integrable"
      return none
    assignChecked goal (← mkAppM ``integrableOn_of_forall_norm_le #[hs, hf, hM, hle])
    return some goals

/-! ### The pointwise operations on functions -/

/-- The lemmas which unfold the operations on functions of a real variable, each with the head and
the number of arguments of its left-hand side: `pointwise_mul` is `f * g = fun x ↦ f x * g x`,
whose left-hand side is `HMul.hMul` applied to six arguments. They are proved by `rfl`. -/
meta def pointwiseLemmas : List (Name × Name × Nat) :=
  [(``pointwise_mul, ``HMul.hMul, 6), (``pointwise_add, ``HAdd.hAdd, 6),
    (``pointwise_sub, ``HSub.hSub, 6), (``pointwise_div, ``HDiv.hDiv, 6),
    (``pointwise_neg, ``Neg.neg, 3), (``pointwise_inv, ``Inv.inv, 3),
    (``pointwise_pow, ``HPow.hPow, 6), (``pointwise_const_smul, ``HSMul.hSMul, 6),
    (``pointwise_smul, ``HSMul.hSMul, 6), (``pointwise_comp, ``Function.comp, 5),
    (``pointwise_one, ``OfNat.ofNat, 3), (``pointwise_zero, ``OfNat.ofNat, 3)]

/-- The expression `e` with the operations on functions of a real variable unfolded, by the
`pointwiseLemmas`: `f * g + h` becomes `fun x ↦ f x * g x + h x`, and `(f * g) a` becomes
`f a * g a`. Nothing else is reduced: the only beta-redexes which are reduced are those which the
unfolding creates. The result is definitionally equal to `e`, and is `e` if it has no such
operation. -/
meta def unfoldPointwise (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e ↦ do
    let some head := e.getAppFn.constName? | return .done e
    let args := e.getAppArgs
    for (thm, head', arity) in pointwiseLemmas do
      unless head == head' && arity ≤ args.size do continue
      let (_, _, eq) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels thm))
      let some (_, lhs, rhs) := eq.eq? | continue
      unless ← withReducibleAndInstances <| isDefEq lhs (mkAppN e.getAppFn args[:arity]) do
        continue
      let rhs ← instantiateMVars rhs
      if rhs.hasExprMVar then continue
      return .done (mkAppN rhs args[arity:]).headBeta
    return .done e)

/-- The goal `goal` with the operations on functions of a real variable unfolded in its target and
in the hypotheses of its local context (see `unfoldPointwise`), so that the goal and the
hypotheses about the same function have the same shape: with `hc : Continuous (f * g)`, the goal
`IntegrableOn (f * g) s` becomes `IntegrableOn (fun x ↦ f x * g x) s`, with
`hc : Continuous fun x ↦ f x * g x`. The goal is `goal` itself if it has no such operation. -/
meta def unfoldPointwiseGoal (goal : MVarId) : MetaM MVarId := goal.withContext do
  let mut goal := goal
  let target ← instantiateMVars (← goal.getType)
  let target' ← unfoldPointwise target
  if target' != target then goal ← goal.replaceTargetDefEq target'
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    let type' ← unfoldPointwise type
    if type' != type then goal ← goal.replaceLocalDeclDefEq decl.fvarId type'
  return goal

/-! ### The goals -/

/-- The error for an unsupported goal. -/
meta def throwUnsupportedGoal {α : Type} (type : Expr) : MetaM α :=
  throwError "endpoint_integrability: unsupported goal{indentExpr type}\nThe supported goals \
    are `IntegrableOn f s μ`, `Integrable f (μ.restrict s)`, `Integrable f μ`, \
    `IntervalIntegrable f μ a b`, `LocallyIntegrableOn f s μ` and `LocallyIntegrable f μ`, \
    for a function `f : ℝ → E`."

/-- Check that the domain of `f` is `ℝ`, or throw the error for the unsupported goal `type`. -/
meta def checkDomain (f type : Expr) : MetaM Unit := do
  let .forallE _ α _ _ ← whnf (← inferType f) | throwUnsupportedGoal type
  unless α.isConstOf ``Real do throwUnsupportedGoal type

/-- Prove `goal : IntervalIntegrable f μ a b`: from the continuity of `f` on `uIcc a b`, or, if
`disch` proves `a ≤ b`, as `IntegrableOn f (Ioc a b) μ`, by `proveIntegrableOn`. -/
meta def proveIntervalIntegrable (disch : TSyntax ``Parser.Tactic.tacticSeq) (goal : MVarId)
    (f μ a b : Expr) : TacticM (List MVarId) := do
  let set ← mkAppM ``Set.uIcc #[a, b]
  if let some hc ← proveContinuousOn? disch f set then
    closeWith goal ``ContinuousOn.intervalIntegrable [hc]
    return []
  let le ← mkAppM ``LE.le #[a, b]
  let some hab ← discharge? disch le
    | throwError "endpoint_integrability: failed to prove{indentExpr
        (← mkAppM ``ContinuousOn #[f, set])}\nby `assumption` or `fun_prop`, and failed to \
        prove{indentExpr le}\nby the discharger, which is needed to reduce the goal to \
        `IntegrableOn f (Ioc a b) μ`."
  let [hle, g] ← evalTacticAt
      (← `(tactic| refine (intervalIntegrable_iff_integrableOn_Ioc_of_le ?_).mpr ?_)) goal
    | throwUnexpectedHypotheses ``intervalIntegrable_iff_integrableOn_Ioc_of_le
  assignChecked hle hab
  proveIntegrableOn disch g f μ ⟨.finite a false, .finite b true⟩

/-- `endpoint_integrability` on `goal`, with the discharger `disch`: the goal by `assumption` or
`fun_prop` (`proveFunProp?`), or else reduced to `IntegrableOn f s μ` and proved by
`proveIntegrableOn`, or, for the local integrability, proved from the continuity. Returns the goals
which are left. -/
meta def endpointIntegrabilityCore (disch : TSyntax ``Parser.Tactic.tacticSeq) (goal : MVarId) :
    TacticM (List MVarId) :=
    goal.withContext do
  if let some proof ← proveFunProp? disch (← instantiateMVars (← goal.getType)) then
    assignChecked goal proof
    return []
  let type ← whnfR (← instantiateMVars (← goal.getType))
  match_expr type with
  | IntegrableOn _ _ _ _ _ f s μ =>
    checkDomain f type
    proveIntegrableOn disch goal f μ (← parseInterval s)
  | Integrable _ _ _ _ _ f μ =>
    checkDomain f type
    match_expr μ with
    | Measure.restrict _ _ μ s =>
      let g ← goal.replaceTargetDefEq (← mkAppM ``IntegrableOn #[f, s, μ])
      proveIntegrableOn disch g f μ (← parseInterval s)
    | _ =>
      let [g] ← evalTacticAt (← `(tactic| refine MeasureTheory.integrableOn_univ.mp ?_)) goal
        | throwUnexpectedHypotheses ``integrableOn_univ
      proveIntegrableOn disch g f μ ⟨.infinite, .infinite⟩
  | IntervalIntegrable _ _ _ f μ a b =>
    proveIntervalIntegrable disch goal f μ a b
  | LocallyIntegrableOn _ _ _ _ _ _ f s _ =>
    checkDomain f type
    let shape ← (← parseInterval s).shape
    let some hc ← proveContinuousOn? disch f s
      | throwNotContinuous (← mkAppM ``ContinuousOn #[f, s])
    let hs ← proveWith (← mkAppM ``MeasurableSet #[s]) shape.measurableSet
    closeWith goal ``ContinuousOn.locallyIntegrableOn [hc, hs]
    return []
  | LocallyIntegrable _ _ _ _ _ _ f _ =>
    checkDomain f type
    let continuous ← mkAppM ``Continuous #[f]
    let some hc ← proveFunProp? disch continuous | throwNotContinuous continuous
    closeWith goal ``Continuous.locallyIntegrable [hc]
    return []
  | _ => throwUnsupportedGoal type

/-! ### The explanation of the goals left -/

meta section

/-- `set_option tactic.endpoint_integrability.explain false` turns off the message of
`endpoint_integrability` which explains, when it leaves an integrability goal, why it did not prove
each piece left and which hypotheses it uses. -/
register_option tactic.endpoint_integrability.explain : Bool := {
  defValue := true
  descr := "`endpoint_integrability` explains why it did not prove each integrability goal which \
    it leaves, and which hypotheses it uses"
}

end

/-- The messages of the trace class `Tactic.endpoint_integrability` about the pieces left and the
majorant, read off the trace messages `elems` of a run of the tactic between the markers of
`pushMarker`: for each piece left, its goal and its messages, without the header which announces
the piece (see `withPieceMarkers`); and the messages about the majorant, if it was tried, in which
each piece of the majorant which is left is one message, its header followed by its messages as
nested bullets (see `withReasons`). -/
meta def explanationLines (elems : Array TraceElem) :
    Array (Name × Array MessageData) × Array MessageData := Id.run do
  let mut pieces := #[]
  let mut current : Option (Name × Array MessageData) := none
  let mut inMajorant := false
  let mut majorant := #[]
  for e in elems do
    let .trace data msg _ := e.msg | continue
    if data.cls == `Tactic.endpoint_integrability.piece then
      let .tagged tag _ := msg | continue
      if tag == majorantBegin then inMajorant := true
      else if tag == majorantEnd || tag == majorantProved then inMajorant := false
      else if pieceBegin.isPrefixOf tag then
        current := some (tag.replacePrefix pieceBegin .anonymous, #[])
      else
        if pieceLeft.isPrefixOf tag then
          if let some (g, lines) := current then
            if inMajorant then
              if let some header := lines[0]? then
                majorant := majorant.push (withReasons (header ++ ":") (lines.extract 1 lines.size))
            else pieces := pieces.push (g, lines.extract 1 lines.size)
        current := none
    else if data.cls != `Tactic.endpoint_integrability then continue
    else if let some (g, lines) := current then current := some (g, lines.push msg)
    else if inMajorant then majorant := majorant.push msg
  return (pieces, majorant)

/-- The trace shown to the user, from the trace messages `elems` of a run of the tactic: one block
per piece of the split, between its markers, whose header is its case tag with `✅️` if it is
proved and `❌️` if it is left, and whose children are the messages about it, the steps which
succeed (see `stepClass`) among the reasons of the failures; and one block for the majorant, if it
was tried, which contains the blocks of its pieces. The messages of other trace classes are kept,
in their order. -/
meta def traceBlocks (elems : Array TraceElem) : Array TraceElem := Id.run do
  let cls := `Tactic.endpoint_integrability
  -- the steps are shown with the class of the tactic
  let rec relabel : MessageData → MessageData
    | .trace data msg children =>
      .trace { data with cls, collapsed := false } msg (children.map relabel)
    | msg => msg
  let mut out : Array TraceElem := #[]
  -- the open blocks, innermost first: the header, if it is known, and the children
  let mut stack : List (Option MessageData × Array MessageData) := []
  for e in elems do
    let .trace data msg _ := e.msg | out := out.push e
    unless cls.isPrefixOf data.cls do
      out := out.push e
      continue
    if data.cls == `Tactic.endpoint_integrability.piece then
      let .tagged tag outcome := msg | continue
      if pieceBegin.isPrefixOf tag then stack := (none, #[]) :: stack
      else if tag == majorantBegin then
        stack := (some m!"with each bounded term replaced by its bound", #[]) :: stack
      else
        let (header?, children) :: rest := stack | continue
        let proved := pieceProved.isPrefixOf tag || tag == majorantProved
        -- the majorant was not tried: the integrand has no bounded term
        if tag == majorantEnd && children.isEmpty then
          stack := rest
          continue
        let emoji := if proved then checkEmoji else crossEmoji
        let node := .trace { cls, collapsed := false }
          (m!"{emoji} " ++ header?.getD .nil ++ outcome) children
        match rest with
        | [] =>
          out := out.push { e with msg := node }
          stack := []
        | (h, c) :: rest => stack := (h, c.push node) :: rest
    else match stack with
      | [] => out := out.push { e with msg := relabel e.msg }
      | (none, children) :: rest => stack := (some msg, children) :: rest
      | (some h, children) :: rest => stack := (some h, children.push (relabel e.msg)) :: rest
  -- the blocks which an error left open
  for (header?, children) in stack.reverse do
    for msg in (header?.map fun h ↦ #[.trace { cls } h #[]]).getD #[] ++ children do
      out := out.push { ref := .missing, msg }
  return out

/-- What the tactic does and the forms of the hypotheses which it uses, in a few lines, and how to
hide the explanation. The details are in the docstring of the tactic. -/
meta def explanationHint : MessageData :=
  m!"This tactic proves integrability by bounding a function by another integrable function at \
    the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all \
    factors.\nThe tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, \
    `Measurable`, `Integrable`, `IntegrableOn`, a bound \
    `∀ x, ‖g x‖ ≤ b x`, and \
    `g =O[l] b` along the filter of an end.\n\n\
    To hide this message: `set_option tactic.endpoint_integrability.explain false`."

/-- The explanation of the integrability goals among `goals`, if there is one, from the trace
messages `elems` of the run of the tactic (see `explanationLines`): the number of these goals; for
each goal, its case tag and why it was not proved, the goals whose reasons are rendered the same
being given together, in the order of their first occurrence; then the messages about the
majorant, if it was tried, and the forms of the hypotheses which the tactic uses
(`explanationHint`). -/
meta def explanation (goals : List MVarId) (elems : Array TraceElem) :
    MetaM (Option MessageData) := do
  let left ← goals.filterM (isIntegrabilityGoal ·)
  if left.isEmpty then return none
  let (pieces, majorant) := explanationLines elems
  let item (line : MessageData) : MessageData := m!"\n  • " ++ .nest 4 line
  -- the goals with the same rendered reasons, together
  let mut groups : Array (String × Array Name × Array MessageData) := #[]
  for g in left do
    let lines := ((pieces.find? (·.1 == g.name)).map (·.2)).getD #[]
    let lines := if lines.isEmpty then #[m!"no reason was recorded"] else lines
    let text ← (MessageData.joinSep lines.toList "\n").toString
    let tag ← g.getTag
    match groups.findIdx? (·.1 == text) with
    | some i => groups := groups.modify i fun (t, tags, ls) ↦ (t, tags.push tag, ls)
    | none => groups := groups.push (text, #[tag], lines)
  let n := left.length
  let mut msg := m!"endpoint_integrability does not prove {n} integrability \
    goal{if n == 1 then "" else "s"}:"
  for (_, tags, lines) in groups do
    let cases := ", ".intercalate (tags.toList.map fun tag ↦ s!"case {tag}")
    msg := msg ++ m!"\n{cases}:"
    for line in lines do msg := msg ++ item line
  unless majorant.isEmpty do
    msg := msg ++ m!"\nWith each bounded term replaced by its bound:"
    for line in majorant do msg := msg ++ item line
  return some (msg ++ m!"\n\n" ++ explanationHint)

/-- Run `k`, the tactic, with the trace classes `Tactic.endpoint_integrability` and
`Tactic.endpoint_integrability.piece` enabled, and log, at the syntax of the tactic, the
explanation of the integrability goals which it leaves (see `explanation`), if `explain` holds and
there are any. The trace messages of these classes produced by `k` are then removed, and, if the
user enabled `trace.Tactic.endpoint_integrability`, replaced by the blocks of `traceBlocks`, with
the steps which succeed, which are traced only in this case; also when `k` throws an error or runs
out of heartbeats. -/
meta def withExplanation (explain : Bool) (k : TacticM (List MVarId)) : TacticM (List MVarId) := do
  let user ← isTracingEnabledFor `Tactic.endpoint_integrability
  let start := (← getTraces).size
  let isOurs (e : TraceElem) : Bool := match e.msg with
    | .trace data .. => (`Tactic.endpoint_integrability).isPrefixOf data.cls
    | _ => false
  let collect : TacticM (Array TraceElem) := do
    let ts := (← getTraces).toArray
    let run := ts.extract start ts.size
    let shown := if user then traceBlocks run else run.filter (!isOurs ·)
    modifyTraces fun _ ↦ (ts.extract 0 start ++ shown).toPArray'
    return run.filter isOurs
  let collected ← IO.mkRef #[]
  let goals ← try
      withSetOptionByName `trace.Tactic.endpoint_integrability true <|
        withSetOptionByName `trace.Tactic.endpoint_integrability.piece true <|
        withSetOptionByName `trace.Tactic.endpoint_integrability.step user k
    finally
      collected.set (← collect)
  if explain then
    if let some msg ← explanation goals (← collected.get) then logInfo msg
  return goals

/-! ### The tactic -/

/--
For `f : ℝ → E` and an interval `s`, `endpoint_integrability` tries to prove that `f` is
integrable on `s`: by its continuity inside `s`, and by bounding it by an integrable function at
the ends of `s`. The tactic proceeds as follows:
1. it splits the goal into the local integrability in the middle of the interval and the
   integrability `IntegrableAtFilter f l μ` at each open or infinite end `l`; the ends are moved
   to `0⁺` or `+∞`;
2. it classifies the factors of `f` into three categories by looking at the context: integrable
   (`hg : Integrable g`), bounded (`hb : ∀ x, ‖g x‖ ≤ b x`, replaced by its bound) and explicit
   (the rest);
3. it proves the middle by continuity, and at each end it compares what is not an integrable
   factor with `t ^ a * |log t| ^ k * exp (u t)`;
4. it decides from `a`, `k` and `u` whether this function is integrable, or, next to an
   integrable factor, bounded.

The tactic supports goals of the form `IntegrableOn f s μ`, `Integrable f (μ.restrict s)`,
`Integrable f μ`, `IntervalIntegrable f μ a b`, `LocallyIntegrableOn f s μ` and
`LocallyIntegrable f μ`. The interval `s` can be any of `Icc a b`, `Ico a b`, `Ioc a b`,
`Ioo a b`, `Ici a`, `Ioi a`, `Iic b`, `Iio b` and `univ`.

What is not proved is left as goals: `locallyIntegrableOn` for the middle, or `continuity` for a
side condition of the continuity; `atBot`, `atTop`, or the name of a finite end, such as `nhds0`,
for an end. A condition on a parameter, such as `0 < s`, is left under the name of its end. When
an integrability goal is left, a message says why
(`set_option tactic.endpoint_integrability.explain false` hides it), and
`set_option trace.Tactic.endpoint_integrability true` shows every step.

`endpoint_integrability (disch := tac)` proves with `tac` the side goals of `fun_prop`, such as
`∀ x ∈ Ioi 0, x ≠ 0`, the order `a ≤ b` of the ends, and the conditions of the comparison, such
as `-b < 0`. The default discharger tries hypotheses, `positivity`, `linarith` and `grind`.

```
example (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun x ↦ x ^ (s - 1) * Real.exp (-x)) (Ioi 0) := by
  endpoint_integrability
example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ x / (1 + x ^ 2) * g x := by
  endpoint_integrability
example (g : ℝ → ℝ) (hm : Measurable g) (hb : ∀ x, |g x| ≤ 1) :
    IntegrableOn (fun x ↦ g x * Real.exp (-x)) (Ioi 0) := by
  endpoint_integrability
```
-/
syntax (name := endpointIntegrability) "endpoint_integrability" (Parser.Tactic.discharger)? : tactic

elab_rules : tactic
  | `(tactic| endpoint_integrability $[$d]?) => do
    let disch ← match d with
      | some d => match d with
        | `(Parser.Tactic.discharger| (disch := $tac)) => pure tac
        | _ => throwUnsupportedSyntax
      | none => defaultDischarger
    let goal ← unfoldPointwiseGoal (← getMainGoal)
    let core := endpointIntegrabilityCore disch goal
    replaceMainGoal (← withExplanation
      ((← getOptions).getBool `tactic.endpoint_integrability.explain true) core)

end Mathlib.Tactic.EndpointIntegrability
