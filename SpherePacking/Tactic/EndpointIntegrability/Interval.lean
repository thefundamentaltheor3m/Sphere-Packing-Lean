/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
module

public import SpherePacking.Tactic.EndpointIntegrability.Basic

/-!
# The split of `endpoint_integrability`

The first step of the tactic (see `SpherePacking.Tactic.EndpointIntegrability.Tactic`): a goal
`IntegrableOn f s μ`, for one of the nine intervals of `shapes` (`parseInterval`), is split into
the *middle*, `LocallyIntegrableOn f t μ`, and one goal `IntegrableAtFilter f l μ` per open or
infinite end of an interval `t` with the ends of `s`, an `EndpointGoal`, with the case tag
`atBot` or `atTop`, or, for a finite end, `nhds0`, `nhds1` or `nhdsa`, named after the end
(`Interval.endTags`).

* `continuityInterval` chooses `t`: the most closed interval with the ends of `s` on which `f` is
  continuous, by a hypothesis or by `fun_prop`, so that a finite end at which `f` is continuous
  gives no goal. Its last run of `fun_prop` may leave pointwise side goals `∀ x ∈ t, P x`, with
  the case tag `continuity`; they are sufficient conditions, not necessary ones: for
  `|x - 1| ^ (-1 / 2)` on `Ioo 0 2` it leaves the false `∀ x ∈ Ioo 0 2, |x - 1| ≠ 0 ∨ 0 ≤ -1 / 2`.
* `decompose` applies the decomposition lemma of `t`, such as
  `MeasureTheory.LocallyIntegrableOn.integrableOn_Ioc` of
  `SpherePacking.Tactic.EndpointIntegrability.Lemmas`. These lemmas hold whatever the order of the
  ends. The middle is closed by the continuity, if it is proved; otherwise it is returned, with
  the case tag `locallyIntegrableOn`.
* `transport` deduces the goal on `s` from the integrability on `t`.
-/

@[expose] public section

open Lean Meta Elab Tactic Qq MeasureTheory

namespace Mathlib.Tactic.EndpointIntegrability

/-! ### Intervals -/

/-- An end of an interval of `ℝ`. -/
meta inductive End where
  /-- An infinite end, `-∞` for a lower end and `+∞` for an upper end. -/
  | infinite
  /-- A finite end at `point`, which belongs to the interval if and only if `closed`. -/
  | finite (point : Expr) (closed : Bool)

/-- The kind of an end: `none` if it is infinite, `some closed` if it is finite. -/
meta def End.kind : End → Option Bool
  | .infinite => none
  | .finite _ closed => some closed

/-- The same end, closed if `closed` and open otherwise when it is finite. -/
meta def End.setClosed (closed : Bool) : End → End
  | .infinite => .infinite
  | .finite a _ => .finite a closed

/-- The ends with the same point, the closed one first. -/
meta def End.variants : End → List End
  | .infinite => [.infinite]
  | .finite a _ => [.finite a true, .finite a false]

/-- Whether the end is finite and closed. -/
meta def End.isClosed : End → Bool
  | .infinite => false
  | .finite _ closed => closed

/-- Whether the end is finite and open. -/
meta def End.isOpen : End → Bool
  | .infinite => false
  | .finite _ closed => !closed

/-- The point of a finite end. -/
meta def End.point? : End → Option Expr
  | .infinite => none
  | .finite a _ => some a

/-- An interval of `ℝ`, given by its ends. -/
meta structure Interval where
  /-- The lower end. -/
  lower : End
  /-- The upper end. -/
  upper : End

/-- A kind of interval: a row of the table of the nine supported intervals. -/
meta structure Shape where
  /-- The constructor of the interval, such as `Set.Ioc`. -/
  set : Name
  /-- The kind of the lower end, as in `End.kind`. -/
  lower : Option Bool
  /-- The kind of the upper end, as in `End.kind`. -/
  upper : Option Bool
  /-- The measurability lemma, such as `measurableSet_Ioc`. -/
  measurableSet : Name
  /-- The decomposition lemma, such as `MeasureTheory.LocallyIntegrableOn.integrableOn_Ioc`. Its
  explicit hypotheses are the local integrability, then the integrability at the lower end if
  it is open or infinite, then at the upper end if it is open or infinite. -/
  decompose : Name
  /-- For an interval with an open finite end: the lemma closing its finite ends, such as
  `MeasureTheory.integrableOn_Icc_of_integrableOn_Ioc`, and the inclusion in the interval with
  closed finite ends, such as `Set.Ioc_subset_Icc_self`. -/
  closing : Option (Name × Name)

/-- The table of the nine supported intervals. -/
meta def shapes : List Shape := [
  ⟨``Set.Icc, some true, some true, ``measurableSet_Icc,
    ``LocallyIntegrableOn.integrableOn_Icc, none⟩,
  ⟨``Set.Ico, some true, some false, ``measurableSet_Ico,
    ``LocallyIntegrableOn.integrableOn_Ico,
    some (``integrableOn_Icc_of_integrableOn_Ico, ``Set.Ico_subset_Icc_self)⟩,
  ⟨``Set.Ioc, some false, some true, ``measurableSet_Ioc,
    ``LocallyIntegrableOn.integrableOn_Ioc,
    some (``integrableOn_Icc_of_integrableOn_Ioc, ``Set.Ioc_subset_Icc_self)⟩,
  ⟨``Set.Ioo, some false, some false, ``measurableSet_Ioo,
    ``LocallyIntegrableOn.integrableOn_Ioo,
    some (``integrableOn_Icc_of_integrableOn_Ioo, ``Set.Ioo_subset_Icc_self)⟩,
  ⟨``Set.Ici, some true, none, ``measurableSet_Ici,
    ``LocallyIntegrableOn.integrableOn_Ici, none⟩,
  ⟨``Set.Ioi, some false, none, ``measurableSet_Ioi,
    ``LocallyIntegrableOn.integrableOn_Ioi,
    some (``integrableOn_Ici_of_integrableOn_Ioi, ``Set.Ioi_subset_Ici_self)⟩,
  ⟨``Set.Iic, none, some true, ``measurableSet_Iic,
    ``LocallyIntegrableOn.integrableOn_Iic, none⟩,
  ⟨``Set.Iio, none, some false, ``measurableSet_Iio,
    ``LocallyIntegrableOn.integrableOn_Iio,
    some (``integrableOn_Iic_of_integrableOn_Iio, ``Set.Iio_subset_Iic_self)⟩,
  ⟨``Set.univ, none, none, ``MeasurableSet.univ,
    ``LocallyIntegrableOn.integrableOn_univ, none⟩]

/-- The finite points of the interval, lower end first. -/
meta def Interval.points (i : Interval) : List Expr :=
  [i.lower.point?, i.upper.point?].filterMap id

/-- The row of the table of the interval. -/
meta def Interval.shape (i : Interval) : MetaM Shape := do
  let some shape := shapes.find? fun s ↦ s.lower == i.lower.kind && s.upper == i.upper.kind
    | throwError "endpoint_integrability: internal error: no shape for an interval"
  return shape

/-- The interval as a set. -/
meta def Interval.toExpr (i : Interval) : MetaM Expr := do
  let shape ← i.shape
  if i.points.isEmpty then mkAppOptM shape.set #[mkConst ``Real]
  else mkAppM shape.set i.points.toArray

/-- The interval with the ends of `i`, each finite end closed if `closed` and open otherwise. -/
meta def Interval.setClosed (closed : Bool) (i : Interval) : Interval :=
  ⟨i.lower.setClosed closed, i.upper.setClosed closed⟩

/-- The intervals with the ends of `i`, from the most closed to the least: both finite ends
closed, then only the lower one, then only the upper one, then none. -/
meta def Interval.candidates (i : Interval) : List Interval :=
  i.lower.variants.flatMap fun l ↦ i.upper.variants.map fun u ↦ ⟨l, u⟩

/-- The error for an unsupported set. -/
meta def throwUnsupportedSet {α : Type} (s : Expr) : MetaM α :=
  throwError "endpoint_integrability: unsupported set{indentExpr s}\nThe supported sets are \
    `Icc a b`, `Ico a b`, `Ioc a b`, `Ioo a b`, `Ici a`, `Ioi a`, `Iic b`, `Iio b` and `univ`."

/-- The interval `s`, which must be a set of the table `shapes`. -/
meta def parseInterval (s : Expr) : MetaM Interval := do
  let some shape := shapes.find? (s.isAppOf ·.set) | throwUnsupportedSet s
  let n := [shape.lower, shape.upper].countP Option.isSome
  let args := s.getAppArgs
  unless args.size == if n == 0 then 1 else n + 2 do throwUnsupportedSet s
  let mkEnd (kind : Option Bool) (point : Expr) : End :=
    match kind with
    | none => .infinite
    | some closed => .finite point closed
  return ⟨mkEnd shape.lower (args.getD (args.size - n) s), mkEnd shape.upper (args.back?.getD s)⟩

/-! ### Endpoint goals -/

/-- A goal `IntegrableAtFilter f l μ` at an end of an interval `s`, as returned by `decompose`. -/
meta structure EndpointGoal where
  /-- The goal `IntegrableAtFilter f l μ`. -/
  goal : MVarId
  /-- The integrand `f`. -/
  f : Expr
  /-- The filter `l`: `atBot`, `atTop`, `𝓝[>] a` or `𝓝[<] b`. -/
  filter : Expr
  /-- The measure `μ`. -/
  μ : Expr
  /-- The interval `s`. -/
  set : Expr
  /-- A proof of `MeasurableSet s`. -/
  measurableSet : Expr
  /-- A proof of `ContinuousOn f s`, if one was found. -/
  continuousOn : Option Expr
  /-- The noun for `f` in messages: `the integrand`, or `the majorant` for the pieces of a
  majorant. -/
  noun : String := "the integrand"

/-- The name `nhds0`, `nhds1` or `nhdsa` of a finite end `a`, the word `nhds` followed by the
end, if the end is printed as a numeral or an identifier, so that this is a name which can be
written after `case`. -/
meta def endName? (a : Expr) : MetaM (Option Name) := do
  let s := toString (← ppExpr a)
  return if !s.isEmpty && s.all isIdRest then some (.mkSimple ("nhds" ++ s)) else none

/-- The case tags of the goals at the ends of the interval `i` which are open or infinite, lower
end first: `atBot` and `atTop` for the infinite ends, and for a finite end its name by `endName?`,
such as `nhds0`. If an end has no such name, as `a + 1` or `-1`, or if the two ends have the same
one, the tags of the finite ends are `nhdsGT` for the lower one and `nhdsLT` for the upper one. -/
meta def Interval.endTags (i : Interval) : MetaM (List Name) := do
  let name? : End → MetaM (Option Name)
    | .finite a _ => endName? a
    | .infinite => pure none
  let lowerName? ← name? i.lower
  let upperName? ← name? i.upper
  let distinct := lowerName? != upperName?
  let lower := match i.lower with
    | .infinite => some `atBot
    | .finite _ closed =>
      if closed then none else some (if distinct then lowerName?.getD `nhdsGT else `nhdsGT)
  let upper := match i.upper with
    | .infinite => some `atTop
    | .finite _ closed =>
      if closed then none else some (if distinct then upperName?.getD `nhdsLT else `nhdsLT)
  return [lower, upper].filterMap id

/-! ### Integrability on an interval -/

/-- If `cond`, the interval `t` with a proof of `ContinuousOn f t`, if it is proved. -/
meta def continuousOnInterval? (disch : TSyntax ``Parser.Tactic.tacticSeq) (f : Expr)
    (t : Interval) (cond : Bool) : TacticM (Option (Interval × Expr)) := do
  unless cond do return none
  return (← proveContinuousOn? disch f (← t.toExpr)).map (t, ·)

/-- The first interval of `Interval.candidates s` on which the continuity of `f` is a hypothesis,
with this hypothesis. -/
meta def continuityHypothesis? (f : Expr) (s : Interval) : MetaM (Option (Interval × Expr)) := do
  for t in s.candidates do
    let h ← mkFreshExprMVar (← mkAppM ``ContinuousOn #[f, ← t.toExpr])
    if ← h.mvarId!.assumptionCore then return some (t, ← instantiateMVars h)
  return none

/-- The most closed interval containing `t`, with the ends of `t`, on which `f` is proved
continuous, given a proof `ht` of continuity on `t`: each open finite end of `t` is closed
separately, and both together only if each can be; the lower end is preferred when only one of
them can be closed. -/
meta def closeEnds (disch : TSyntax ``Parser.Tactic.tacticSeq) (f : Expr) (t : Interval)
    (ht : Expr) : TacticM (Interval × Expr) := do
  let lower? ← continuousOnInterval? disch f ⟨t.lower.setClosed true, t.upper⟩ t.lower.isOpen
  let upper? ← continuousOnInterval? disch f ⟨t.lower, t.upper.setClosed true⟩ t.upper.isOpen
  let both? ← continuousOnInterval? disch f (t.setClosed true) (lower?.isSome && upper?.isSome)
  return (both? <|> lower? <|> upper?).getD (t, ht)

/-- The most closed interval with the ends of `s` on which `f` is proved continuous, with the proof
of continuity and the side goals left by this proof. If there is none, the open interval with the
ends of `s`, without proof.

The intervals with the ends of `s` are first tried by `assumption`, from the most closed to the
least. A failing run of `fun_prop` is expensive, so it is then run on `s` itself, and, only if this
fails, on the open interval. Its open finite ends are then closed by `closeEnds`. If both runs
fail, `fun_prop` is run a last time on the open interval, with the side goals which the
discharger does not prove and which are pointwise conditions on the open interval left as goals
(see `funProp?`); the ends are then not closed. These side goals may be stronger than needed, or
false: a discharger which never fails makes `fun_prop` keep the first lemma it tries. -/
meta def continuityInterval (disch : TSyntax ``Parser.Tactic.tacticSeq) (f : Expr)
    (s : Interval) : TacticM (Interval × Option Expr × List MVarId) := do
  if let some (t, h) ← continuityHypothesis? f s then return (t, some h, [])
  let o := s.setClosed false
  let onS? ← continuousOnInterval? disch f s true
  let some (t, ht) ← if onS?.isSome then pure onS? else
      continuousOnInterval? disch f o (s.lower.isClosed || s.upper.isClosed)
    | let set ← o.toExpr
      let some (h, goals) ← funProp? disch (← mkAppM ``ContinuousOn #[f, set]) set
        | return (o, none, [])
      return (o, some h, goals)
  let (t, h) ← closeEnds disch f t ht
  return (t, some h, [])

/-- Prove `goal : IntegrableOn f t μ` by the decomposition lemma of the interval `t`, with
`hc? : Option (ContinuousOn f t)`. Returns the goal `LocallyIntegrableOn f t μ` if there is no
proof of continuity, and the goals at the open or infinite ends of `t`, whose noun in messages is
`noun`. -/
meta def decompose (goal : MVarId) (f μ : Expr) (t : Interval) (hc? : Option Expr)
    (noun := "the integrand") :
    TacticM (Option MVarId × List EndpointGoal) := do
  let shape ← t.shape
  let set ← t.toExpr
  let hs ← proveWith (← mkAppM ``MeasurableSet #[set]) shape.measurableSet
  let hloc :: ends ← applyLemma goal shape.decompose | throwUnexpectedHypotheses shape.decompose
  let tags ← t.endTags
  unless ends.length == tags.length do throwUnexpectedHypotheses shape.decompose
  let loc? ← match hc? with
    | some hc => do
      closeWith hloc ``ContinuousOn.locallyIntegrableOn [hc, hs]
      pure none
    | none => do
      hloc.setTag `locallyIntegrableOn
      pure (some hloc)
  let ends ← (ends.zip tags).mapM fun (g, tag) ↦ do
    g.setTag tag
    let filter ← match_expr ← instantiateMVars (← g.getType) with
      | IntegrableAtFilter _ _ _ _ _ _ l _ => pure l
      | _ => throwUnexpectedHypotheses shape.decompose
    return { goal := g, f, filter, μ, set, measurableSet := hs, continuousOn := hc?, noun }
  return (loc?, ends)

/-- A proof of `IntegrableOn f s μ` from a proof `h` of `IntegrableOn f t μ`, where the interval
`t` has the ends of `s`: close the finite ends of `t`, then restrict to `s`. -/
meta def transport (h : Expr) (t s : Interval) : MetaM Expr := do
  let shapeT ← t.shape
  let shapeS ← s.shape
  if shapeT.set == shapeS.set then return h
  let h ← match shapeT.closing with
    | some (close, _) => mkAppM close #[h]
    | none => pure h
  let some (_, subset) := shapeS.closing | return h
  have set : Q(Set ℝ) := ← s.toExpr
  have closure : Q(Set ℝ) := ← (s.setClosed true).toExpr
  let hsub ← proveWith q($set ⊆ $closure) subset
  mkAppM ``IntegrableOn.mono_set #[h, hsub]

end Mathlib.Tactic.EndpointIntegrability
