/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
module

public import SpherePacking.Tactic.EndpointIntegrability.Factor

/-!
# Bounded terms for `endpoint_integrability`

The *bounded* terms of the second step of the tactic, the classification of the terms of the
integrand (see `SpherePacking.Tactic.EndpointIntegrability.Tactic`). A function `f` which is almost
everywhere strongly measurable on a measurable set `s`, and whose norm is bounded on `s` by a
function `M` integrable on `s`, is integrable on `s`
(`MeasureTheory.integrableOn_of_forall_norm_le`). This file builds such a *majorant* `M` for an
integrand with *bounded atoms*: subexpressions whose norm is bounded by a known function, such as a
function `g` with a hypothesis `∀ x, |g x| ≤ 1` in the context, which may be neither continuous
nor known to the comparison engine.

The majorant `M` is `f` with each bounded atom replaced by its bound, built by recursion on the
integrand along the path to the bounded atoms only: through products, sums, differences,
negations, natural powers, and quotients by a denominator without bounded atoms, `a / b` being
bounded by the bound of `a` times `‖b⁻¹‖`. A subexpression without bounded atoms is kept whole, as
its norm `‖e‖`, so that its exact order is seen by the comparison engine: `g x * (1 + x ^ 2)⁻¹`,
with `|g x| ≤ C`, has the majorant `C * ‖(1 + x ^ 2)⁻¹‖`. A bounded atom under any other function,
such as an inverse, an exponential, a real power, a logarithm or a cast, is not dominated, and
there is no majorant. The bound `∀ x ∈ s, ‖f x‖ ≤ M x` is assembled along the same recursion, by the
lemmas `norm_mul_le_of_le`, `norm_add_le_of_le` and the like.

A bounded atom is an expression to which a bound hypothesis of the local context applies (see
`atomBound?`): an expression `g a` with a hypothesis `∀ y, ‖g y‖ ≤ b y` or `∀ y, |g y| ≤ b y`,
bounded by `b a`, or, for a hypothesis `∀ y ∈ s, ‖g y‖ ≤ b y` on the set `s` of the goal, the
expression `g x` in the variable `x` of the integrand, bounded by `b x`. A hypothesis with
parameters quantified before the variable, such as `∀ k y, ‖φ k y‖ ≤ b k`, is not used: its
instance `∀ y, ‖φ k y‖ ≤ b k` is given as a hypothesis. A bound `∀ y, g y ≤ b y`, without norm or
absolute value, is not used. Other bounded functions, such as `Int.fract`, are given by such
hypotheses, as `∀ x, ‖Int.fract x‖ ≤ 1`.

The measurability of the integrand is proved from its continuity, or by `fun_prop`, with, as a
last resort, the measurability facts given by the integrability hypotheses of the context (see
`measurabilityFacts`), so that `φ x * g x` is dominated by `C * ‖g x‖` with `Measurable φ`,
`∀ x, ‖φ x‖ ≤ C` and `Integrable g`; the majorant is then proved integrable through its integrable
factor `‖g x‖` (see `SpherePacking.Tactic.EndpointIntegrability.Factor`). With only reducible
definitions unfolded, `fun_prop` does not prove the measurability of `fun x ↦ x * g x` or of a
quotient from these facts, nor of an `if … then … else` whose condition depends on the variable,
nor of the product of a function known only to be continuous on the set with a discontinuous one,
such as `g x * Int.fract x` with `ContinuousOn g (Ioi 0)`.

The driver (`proveIntegrableOn` in `SpherePacking.Tactic.EndpointIntegrability.Tactic`) proves the
pieces of `M` instead of those of `f` only if the pieces of `f` leave an integrability goal, and
keeps them only if they leave none.

## Main definitions

* `Mathlib.Tactic.EndpointIntegrability.majorant?`: the majorant and the bound.
* `Mathlib.Tactic.EndpointIntegrability.aestronglyMeasurable?`: the measurability of the
  integrand.
-/

@[expose] public section

open Lean Meta Elab Tactic MeasureTheory

namespace Mathlib.Tactic.EndpointIntegrability

/-! ### The majorant -/

/-- A bound `‖e‖ ≤ bound` on the norm of an expression `e`, with its proof. -/
meta structure NormBound where
  /-- The bound, a real expression. -/
  bound : Expr
  /-- The proof of `‖e‖ ≤ bound`. -/
  proof : Expr

/-- The context of the construction of the majorant: the variable `x` of the integrand, a proof of
`x ∈ s`, the set `s` of the goal, and the hypotheses of the local context which may bound atoms. -/
meta structure DominationContext where
  /-- The variable of the integrand. -/
  x : Expr
  /-- A proof of `x ∈ s`. -/
  hx : Expr
  /-- The set `s` of the goal. -/
  set : Expr
  /-- The hypotheses of the local context of the form `∀ y, P y` or `∀ y ∈ t, P y`, with `P y` an
  inequality (see `hypothesisBound?`). -/
  hypotheses : Array Expr

/-- The monad of the construction of the majorant. An error means that a bounded atom occurs where
it cannot be dominated: there is no majorant. -/
abbrev DominationM := ReaderT DominationContext MetaM

/-- The trivial bound `‖e‖ ≤ ‖e‖`. -/
meta def NormBound.self (e : Expr) : MetaM NormBound := do
  let norm ← mkAppM ``Norm.norm #[e]
  return ⟨norm, ← mkAppM ``le_refl #[norm]⟩

/-- The expression `a` and whether the norm is an absolute value, for `lhs` of the form `‖a‖` or
`|a|`. -/
meta def normOrAbs? (lhs : Expr) : Option (Expr × Bool) :=
  if lhs.isAppOfArity ``Norm.norm 3 then some (lhs.appArg!, false)
  else if lhs.isAppOfArity ``abs 4 then some (lhs.appArg!, true)
  else none

/-- The bound given by the hypothesis `h` to `e`, if `h` is `∀ y, ‖g y‖ ≤ b y` or
`∀ y, |g y| ≤ b y` (for real values), with `e` of the form `g a` up to reducible definitional
equality, `y` being instantiated by unification, or `∀ y ∈ s, ‖g y‖ ≤ b y` (or with `|g y|`), with
`s` the set of the goal and `e` the expression `g x` in the variable `x` of the integrand. The
bound may be a constant. A hypothesis with parameters quantified before the variable, such as
`∀ k y, ‖φ k y‖ ≤ b k`, is not used. -/
meta def hypothesisBound? (h e : Expr) : DominationM (Option NormBound) := do
  let ctx ← read
  let fn := e.getAppFn
  unless fn.isConst || fn.isFVar do return none
  let .forallE _ α body _ ← instantiateMVars (← inferType h) | return none
  withNewMCtxDepth do
    let y ← mkFreshExprMVar α
    let (mem?, body) := match body.instantiate1 y with
      | .forallE _ mem b _ => (some mem, b)
      | b => (none, b)
    if body.hasLooseBVars then return none
    let_expr LE.le _ _ lhs rhs := body | return none
    let some (inner, abs) := normOrAbs? lhs | return none
    unless inner.getAppFn == fn && inner.getAppNumArgs == e.getAppNumArgs do return none
    unless ← withReducible <| isDefEq inner e do return none
    let a ← instantiateMVars y
    let rhs ← instantiateMVars rhs
    if a.hasMVar || rhs.hasMVar then return none
    let mut proof := mkApp h a
    if let some mem := mem? then
      let mem ← instantiateMVars mem
      unless mem.isAppOfArity ``Membership.mem 5 && mem.appArg! == ctx.x do return none
      unless ← withReducible <| isDefEq mem.appFn!.appArg! ctx.set do return none
      proof := mkApp proof ctx.hx
    if abs then
      unless (← whnfR (← inferType e)).isConstOf ``Real do return none
      proof ← mkAppM ``Real.norm_le_of_abs_le #[proof]
    return some ⟨rhs.headBeta, proof⟩

/-- The bound of `e` if `e` is a bounded atom: an expression to which a hypothesis of the local
context applies (see `hypothesisBound?`), the first one. -/
meta def atomBound? (e : Expr) : DominationM (Option NormBound) := do
  for h in (← read).hypotheses do
    if let some b ← hypothesisBound? h e then return some b
  return none

/-- Whether `e` has a subexpression without loose bound variables which is a bounded atom. -/
meta partial def hasBoundedAtom (e : Expr) : DominationM Bool := do
  -- the guard is not a conjunction with `(← atomBound? e)`, which would be run first
  if !e.hasLooseBVars && e.isApp then
    if (← atomBound? e).isSome then return true
  match e with
  | .app f a => hasBoundedAtom f <||> hasBoundedAtom a
  | .lam _ t b _ | .forallE _ t b _ => hasBoundedAtom t <||> hasBoundedAtom b
  | .letE _ t v b _ => hasBoundedAtom t <||> hasBoundedAtom v <||> hasBoundedAtom b
  | .mdata _ b | .proj _ _ b => hasBoundedAtom b
  | _ => return false

/-- The bound `‖e‖ ≤ M` of the majorant: `none` if `e` has no bounded atom, so that it is
kept whole as `‖e‖`; otherwise `M` is `e` with each bounded atom replaced by its bound, through
products, sums, differences, negations, natural powers and quotients by denominators without
bounded atoms. Throws if a bounded atom occurs under any other function. -/
meta partial def normBound? (e : Expr) : DominationM (Option NormBound) := do
  if let some b ← atomBound? e then return some b
  match_expr e with
  | HMul.hMul _ _ _ _ a b => binary a b ``norm_mul_le_of_le ``HMul.hMul
  | HAdd.hAdd _ _ _ _ a b => binary a b ``norm_add_le_of_le ``HAdd.hAdd
  | HSub.hSub _ _ _ _ a b => binary a b ``norm_sub_le_of_le ``HAdd.hAdd
  | Neg.neg _ _ a =>
    let some b ← normBound? a | return none
    return some ⟨b.bound, ← mkAppM ``norm_neg_le_of_le #[b.proof]⟩
  | HPow.hPow _ n _ _ a k =>
    unless n.isConstOf ``Nat do return ← whole e
    let some b ← normBound? a | return none
    return some ⟨← mkAppM ``HPow.hPow #[b.bound, k], ← mkAppM ``norm_pow_le_pow_of_le #[b.proof, k]⟩
  | HDiv.hDiv _ _ _ _ a d =>
    if ← hasBoundedAtom d then throwUnderFunction e
    let some b ← normBound? a | return none
    let bound ← mkAppM ``HMul.hMul #[b.bound, ← mkAppM ``Norm.norm #[← mkAppM ``Inv.inv #[d]]]
    return some ⟨bound, ← mkAppM ``norm_div_le_mul_norm_inv_of_le #[b.proof, d]⟩
  | _ => whole e
where
  /-- The bound of `a ∘ b`, for the operation `∘` with the lemma `name` bounding it by
  `op` of the bounds of `a` and `b`. -/
  binary (a b : Expr) (name op : Name) : DominationM (Option NormBound) := do
    let ba? ← normBound? a
    let bb? ← normBound? b
    if ba?.isNone && bb?.isNone then return none
    let ba ← ba?.getDM (NormBound.self a)
    let bb ← bb?.getDM (NormBound.self b)
    return some ⟨← mkAppM op #[ba.bound, bb.bound], ← mkAppM name #[ba.proof, bb.proof]⟩
  /-- An expression through which the recursion does not go: kept whole if it has no bounded
  atom. -/
  whole (e : Expr) : DominationM (Option NormBound) := do
    if ← hasBoundedAtom e then throwUnderFunction e
    return none
  /-- The error for a bounded atom under a function through which it is not dominated. -/
  throwUnderFunction {α : Type} (e : Expr) : DominationM α := do
    throwError (← tracedSentence do
      return ["a bounded term occurs in ", e, ", under a function through which it is not \
        replaced by its bound: only products, sums, differences, negations, natural powers and \
        numerators of quotients are"])

/-- The hypotheses of the local context of the form `∀ y, P y` or `∀ y ∈ t, P y`, with `P y` an
inequality, which may bound atoms (see `hypothesisBound?`). -/
meta def boundHypotheses : MetaM (Array Expr) := do
  let mut hyps := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if let .forallE _ _ body _ ← instantiateMVars decl.type then
      let body := if let .forallE _ _ b _ := body then b else body
      if body.isAppOfArity ``LE.le 4 then hyps := hyps.push decl.toExpr
  return hyps

/-- The majorant `M` of `f : ℝ → E` on the set `s`, with a proof of `∀ x ∈ s, ‖f x‖ ≤ M x`, if `f`
has a bounded atom (see `normBound?`). Throws if a bounded atom occurs where it is not
dominated. -/
meta def majorant? (f s : Expr) : MetaM (Option (Expr × Expr)) := do
  let hypotheses ← boundHypotheses
  let name := if let .lam n .. := f then n else `x
  withLocalDeclD name (mkConst ``Real) fun x ↦ do
  withLocalDeclD `hx (← mkAppM ``Membership.mem #[s, x]) fun hx ↦ do
    let some b ← (normBound? (mkApp f x).headBeta).run { x, hx, set := s, hypotheses }
      | return none
    let hle ← mkLambdaFVars #[x, hx] b.proof
    check hle
    return some (← mkLambdaFVars #[x] b.bound, hle)

/-! ### Measurability -/

/-- A proof of `AEStronglyMeasurable f (μ.restrict s)` for the interval `s`, given a proof `hs` of
`MeasurableSet s`: from the continuity of `f` on `s`, or by `fun_prop` on this statement, or from
`Measurable f`, with the discharger `disch` (see `funProp?`); failing these, if the integrability
hypotheses of the context give measurability facts `AEStronglyMeasurable g (μ.restrict s)` (see
`measurabilityFacts`), by `fun_prop` on this statement again, with these facts as local
hypotheses. -/
meta def aestronglyMeasurable? (disch : TSyntax ``Parser.Tactic.tacticSeq) (f μ hs : Expr)
    (s : Interval) : TacticM (Option Expr) := do
  let set ← s.toExpr
  let type ← mkAppM ``AEStronglyMeasurable #[f, ← mkAppM ``Measure.restrict #[μ, set]]
  let proof ← mkFreshExprMVar type
  if let some hc ← proveContinuousOn? disch f set then
    closeWith proof.mvarId! ``ContinuousOn.aestronglyMeasurable [hc, hs]
    return some (← instantiateMVars proof)
  if let some h ← proveFunProp? disch type then return some h
  if let some hm ← proveFunProp? disch (← mkAppM ``Measurable #[f]) then
    closeWith proof.mvarId! ``Measurable.aestronglyMeasurable [hm]
    return some (← instantiateMVars proof)
  let facts ← measurabilityFacts μ s
  if facts.isEmpty then return none
  withMeasurabilityFacts facts (proveFunProp? disch type)

end Mathlib.Tactic.EndpointIntegrability
