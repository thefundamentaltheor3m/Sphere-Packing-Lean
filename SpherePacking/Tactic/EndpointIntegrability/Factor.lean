/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
module

public import SpherePacking.Tactic.EndpointIntegrability.Interval

/-!
# Integrable factors for `endpoint_integrability`

The *integrable* terms of the second step of the tactic, the classification of the terms of the
integrand (see `SpherePacking.Tactic.EndpointIntegrability.Tactic`). A function `f` whose norm is
bounded by `H x * ‖G x‖`, for a function `G` known to be integrable, is integrable at an end of an
interval if `H` is bounded there (`MeasureTheory.IntegrableAtFilter.of_norm_le_mul`), and locally
integrable on the interval if `H` is continuous there
(`MeasureTheory.LocallyIntegrableOn.of_norm_le_mul`), provided `f` is measurable. Thus an
integrable function of the context is a comparison function, alongside the scale of the
comparison engine. This file finds such *integrable factors* of an integrand, and proves the
middle from them (`proveMiddleByFactor?`), when the continuity of the integrand is not proved; the
ends are proved by `proveByFactor?` of `SpherePacking.Tactic.EndpointIntegrability.Endpoint`, which
bounds `H` by the comparison engine.

## The factorization

The integrand `fun x ↦ e` is traversed through products `a * b` (both factors), scalar
multiplications `c • v` (the vector), quotients `a / d` (the numerator), negations, norms,
absolute values and casts `Complex.ofReal`, and through nothing else (see `factorChildren`). Its
*candidate factors* are the subexpressions `G x` reached in this way, whatever their form, which
are the body at `x` of the function of an integrability hypothesis of the context, up to beta
reduction and instances (see `isFactorCandidate`): with `Integrable fun t ↦ g t * rexp (-t)`, the
factor `g x * rexp (-x)` of `cos x * (g x * rexp (-x))`, and with `Integrable g`, the factor `g x`.
A Schwartz function `b` is a candidate only with a hypothesis `Integrable b`, such as
`b.integrable`. A candidate is thus never under an inverse, a power, an exponential or any other
function: `(g x)⁻¹`, `g x ^ 2` and `rexp (g x)` are candidates only if a hypothesis is about them,
as a whole. The candidates are
listed with each subexpression before its own subexpressions, the largest first, and from left to
right. Finding them costs only unifications with the hypotheses, and no run of `fun_prop`.

For a candidate `G x`, the *cofactor* `H x` is the product of the norms of the other factors, the
denominators contributing `‖d⁻¹‖`, and `1` if there is none: `x * g x * (1 + x ^ 2)⁻¹` has the
cofactor `‖x‖ * ‖(1 + x ^ 2)⁻¹‖`, and `‖sin x * g x‖` the cofactor `‖sin x‖`. The bound
`‖f x‖ ≤ H x * ‖G x‖` is proved along the traversal by lemmas such as `norm_mul_le_mul_of_le_left`
(see `factorBound`), and the almost everywhere strong measurability of `f` along the same traversal,
from that of `G`, given by its integrability, and the measurability of the other factors, proved by
`fun_prop` (see `factorMeasurable?`). The measurability is not asked of `fun_prop` on `f` itself:
with only reducible definitions unfolded, `fun_prop` does not prove the measurability of
`fun x ↦ x * g x` or of a quotient from that of `g`.

The candidates are tried in this order; exactly one of them plays the role of `G`, the other
factors being part of the cofactor, which must then be bounded or continuous: the product
`g₁ x * g₂ x` of two integrable functions is not proved integrable.

## Integrability of the factor

The integrability of `G` on an interval `t` (`integrableOn?`) comes from a hypothesis of the local
context (`integrabilitySources`): `Integrable G μ`, on any interval, or `IntegrableOn G s' μ` or
`Integrable G (μ.restrict s')`, for `s'` an interval with the ends of `t` which contains `t`. A
hypothesis on another set is not used, nor an interval integrability, of which `hg.1` is the
integrability on `Ioc a b`. The function of the hypothesis is matched with `fun x ↦ G x`
up to beta reduction and instances. The type of the hypothesis must be the integrability statement
itself: a hypothesis with universal quantifiers, such as `∀ k, Integrable (φ k)`, is not used, and
its instance is given as a hypothesis. `fun_prop` is not run on the integrability of `G`.

## Measurability facts

The majorant of an integrand with bounded terms
(`SpherePacking.Tactic.EndpointIntegrability.Domination`) needs the measurability of the integrand,
proved by `fun_prop`, which does not derive `AEStronglyMeasurable g (μ.restrict s)` from
`Integrable g μ`. `measurabilityFacts` gives these facts, for the integrability hypotheses of the
context which apply on `s`, and `withMeasurabilityFacts` runs `fun_prop` with them as local
hypotheses.
-/

@[expose] public section

open Lean Meta Elab Tactic Qq MeasureTheory

namespace Mathlib.Tactic.EndpointIntegrability

/-! ### The factorization -/

/-- The subexpressions of `e` through which a candidate factor is looked for, with their
positions: both factors of a product, the vector of a scalar multiplication, the numerator of a
quotient, and the argument of a negation, a norm, an absolute value or a cast `Complex.ofReal`. -/
meta def factorChildren (e : Expr) : List (Nat × Expr) :=
  if e.isAppOfArity ``HMul.hMul 6 then [(0, e.appFn!.appArg!), (1, e.appArg!)]
  else if e.isAppOfArity ``HSMul.hSMul 6 || e.isAppOfArity ``HDiv.hDiv 6 then
    if e.isAppOf ``HSMul.hSMul then [(1, e.appArg!)] else [(0, e.appFn!.appArg!)]
  else if e.isAppOfArity ``Neg.neg 3 || e.isAppOfArity ``Norm.norm 3 ||
      e.isAppOfArity ``abs 4 || e.isAppOfArity ``Complex.ofReal 1 then [(0, e.appArg!)]
  else []

/-- The paths, as lists of positions (see `factorChildren`), to the candidate factors of `e` in the
variable `x`: the subexpressions reached through `factorChildren` for which `isCandidate x` holds,
each before its own subexpressions (the largest first), and from left to right. -/
meta partial def factorPaths (x e : Expr) (isCandidate : Expr → Expr → MetaM Bool) :
    MetaM (List (List Nat)) := do
  let here := if ← isCandidate x e then [[]] else []
  let below ← (factorChildren e).flatMapM fun (i, c) ↦ do
    return (← factorPaths x c isCandidate).map (i :: ·)
  return here ++ below

/-- A bound on the norm of a subexpression `e` of the integrand containing the factor `G x`:
`‖e‖ ≤ H * ‖G x‖` for the cofactor `H` of `e`, or `‖e‖ ≤ ‖G x‖` if it has none. -/
meta structure FactorBound where
  /-- The cofactor `H`, a real expression, if any. -/
  cofactor : Option Expr
  /-- The proof of the bound. -/
  proof : Expr

/-- The bound `‖e‖ ≤ H * ‖G x‖` of `e` for the factor at the end of `path` (see `factorPaths`),
with the lemmas `norm_mul_le_mul_of_le_left` and the like, the other factors contributing their
norms to `H`, and the denominators `‖d⁻¹‖`. -/
meta partial def factorBound (e : Expr) : List Nat → MetaM FactorBound
  | [] => return ⟨none, ← mkAppM ``le_refl #[← mkAppM ``Norm.norm #[e]]⟩
  | i :: path => do
    let norm (a : Expr) : MetaM Expr := mkAppM ``Norm.norm #[a]
    let mul (a b : Expr) : MetaM Expr := mkAppM ``HMul.hMul #[a, b]
    if e.isAppOfArity ``HMul.hMul 6 then
      let a := e.appFn!.appArg!
      let b := e.appArg!
      if i == 0 then
        let r ← factorBound a path
        match r.cofactor with
        | some H =>
          return ⟨← mul H (← norm b), ← mkAppM ``norm_mul_le_mul_of_le_left #[r.proof, b]⟩
        | none => return ⟨← norm b, ← mkAppM ``norm_mul_le_of_le_left #[r.proof, b]⟩
      let r ← factorBound b path
      match r.cofactor with
      | some H =>
        return ⟨← mul (← norm a) H, ← mkAppM ``norm_mul_le_mul_of_le_right #[a, r.proof]⟩
      | none => return ⟨← norm a, ← mkAppM ``norm_mul_le_of_le_right #[a, r.proof]⟩
    if e.isAppOfArity ``HSMul.hSMul 6 then
      let c := e.appFn!.appArg!
      let r ← factorBound e.appArg! path
      match r.cofactor with
      | some H => return ⟨← mul (← norm c) H, ← mkAppM ``norm_smul_le_mul_of_le #[c, r.proof]⟩
      | none => return ⟨← norm c, ← mkAppM ``norm_smul_le_of_le #[c, r.proof]⟩
    if e.isAppOfArity ``HDiv.hDiv 6 then
      let d := e.appArg!
      let r ← factorBound e.appFn!.appArg! path
      let inv ← norm (← mkAppM ``Inv.inv #[d])
      match r.cofactor with
      | some H => return ⟨← mul H inv, ← mkAppM ``norm_div_le_mul_of_le #[r.proof, d]⟩
      | none => return ⟨inv, ← mkAppM ``norm_div_le_inv_mul_of_le #[r.proof, d]⟩
    let some name :=
        if e.isAppOfArity ``Neg.neg 3 then some ``norm_neg_le_of_le
        else if e.isAppOfArity ``Norm.norm 3 then some ``norm_norm_le_of_le
        else if e.isAppOfArity ``abs 4 then some ``Real.norm_abs_le_of_le
        else if e.isAppOfArity ``Complex.ofReal 1 then some ``Complex.norm_ofReal_le_of_le
        else none
      | throwError "endpoint_integrability: internal error: no factor in{indentExpr e}"
    let r ← factorBound e.appArg! path
    return ⟨r.cofactor, ← mkAppM name #[r.proof]⟩

/-- A factorization of the integrand `f : ℝ → E` by a candidate factor `G`: `f x` is bounded in
norm by `H x * ‖G x‖`. -/
meta structure Factorization where
  /-- The path to the factor in the integrand (see `factorPaths`). -/
  path : List Nat
  /-- The factor `G`, as a function, `fun x ↦ G x`. -/
  factor : Expr
  /-- The cofactor `H : ℝ → ℝ`, `fun _ ↦ 1` if there is no other factor. -/
  cofactor : Expr
  /-- The proof of `∀ x, ‖f x‖ ≤ H x * ‖G x‖`. -/
  bound : Expr

/-- The factorizations of `f : ℝ → E` by its candidate factors, the subexpressions `G x`, reached
through `factorChildren`, for which `isCandidate x (G x)` holds in the variable `x`, the largest
first and from left to right (see `factorPaths`). -/
meta def factorizations (f : Expr) (isCandidate : Expr → Expr → MetaM Bool) :
    MetaM (List Factorization) := do
  let f ← instantiateMVars f
  let name := if let .lam n .. := f then n else `x
  withLocalDeclD name q(ℝ) fun x ↦ do
    let e := (mkApp f x).headBeta
    (← factorPaths x e isCandidate).mapM fun path ↦ do
      let leaf := path.foldl (fun e i ↦ ((factorChildren e).lookup i).getD e) e
      let r ← factorBound e path
      let (H, proof) ← match r.cofactor with
        | some H => pure (H, r.proof)
        | none => do
          let one ← mkEqSymm (← mkAppM ``one_mul #[← mkAppM ``Norm.norm #[leaf]])
          pure (q((1 : ℝ)), ← mkAppM ``le_of_le_of_eq #[r.proof, one])
      let factor := (← mkLambdaFVars #[x] leaf).eta
      let cofactor ← mkLambdaFVars #[x] H
      let bound ← mkLambdaFVars #[x] proof
      return { path, factor, cofactor, bound }

/-! ### Measurability -/

/-- A proof of `AEStronglyMeasurable (fun x ↦ c) μ`, for a subexpression `c` of the integrand in
the variable `x` which is not on the path to the factor: from `Measurable (fun x ↦ c)`, or else
`AEStronglyMeasurable (fun x ↦ c) μ`, by `fun_prop` with the discharger `disch`. -/
meta def otherFactorMeasurable? (disch : TSyntax ``Parser.Tactic.tacticSeq) (μ x c : Expr) :
    TacticM (Option Expr) := do
  let fn ← mkLambdaFVars #[x] c
  let type ← mkAppM ``AEStronglyMeasurable #[fn, μ]
  let measurable? ← try some <$> mkAppM ``Measurable #[fn] catch _ => pure none
  if let some measurable := measurable? then
    if let some hm ← proveFunProp? disch measurable then
      let proof ← mkFreshExprMVar type
      let closed ← attempt proof.mvarId! do
        closeWith proof.mvarId! ``Measurable.aestronglyMeasurable [hm]
        return true
      if closed then return some (← instantiateMVars proof)
  proveFunProp? disch type

/-- A proof of `AEStronglyMeasurable (fun x ↦ e) μ`, for a subexpression `e` of the integrand in the
variable `x`, along the path to the factor `G x`, given a proof `hG` of
`AEStronglyMeasurable (fun x ↦ G x) μ`, the other factors being measurable by
`otherFactorMeasurable?`. -/
meta partial def factorMeasurable? (disch : TSyntax ``Parser.Tactic.tacticSeq) (μ x hG : Expr)
    (e : Expr) : List Nat → TacticM (Option Expr)
  | [] => return some hG
  | i :: path => do
    let other (c : Expr) := otherFactorMeasurable? disch μ x c
    let next (c : Expr) := factorMeasurable? disch μ x hG c path
    if e.isAppOfArity ``HMul.hMul 6 then
      let a := e.appFn!.appArg!
      let b := e.appArg!
      let (ha?, hb?) ← if i == 0 then do pure (← next a, ← other b)
        else do pure (← other a, ← next b)
      let (some ha, some hb) := (ha?, hb?) | return none
      return some (← mkAppM ``AEStronglyMeasurable.fun_mul #[ha, hb])
    if e.isAppOfArity ``HSMul.hSMul 6 then
      let some hc ← other e.appFn!.appArg! | return none
      let some hv ← next e.appArg! | return none
      return some (← mkAppM ``AEStronglyMeasurable.fun_smul #[hc, hv])
    if e.isAppOfArity ``HDiv.hDiv 6 then
      let some ha ← next e.appFn!.appArg! | return none
      let some hd ← other e.appArg! | return none
      return some (← mkAppM ``AEStronglyMeasurable.div₀ #[ha, hd])
    let some ha ← next e.appArg! | return none
    if e.isAppOfArity ``Neg.neg 3 then return some (← mkAppM ``AEStronglyMeasurable.fun_neg #[ha])
    if e.isAppOfArity ``Norm.norm 3 then return some (← mkAppM ``AEStronglyMeasurable.norm #[ha])
    let continuous ←
      if e.isAppOfArity ``abs 4 then pure q((continuous_abs : Continuous fun y : ℝ ↦ |y|))
      else pure q(Complex.continuous_ofReal)
    return some (← mkAppM ``Continuous.comp_aestronglyMeasurable #[continuous, ha])

/-- A proof of `AEStronglyMeasurable f μ` from the factorization `fz` of `f` and a proof `hG` of
`AEStronglyMeasurable G μ` for its factor `G` (see `factorMeasurable?`). -/
meta def Factorization.measurable? (fz : Factorization)
    (disch : TSyntax ``Parser.Tactic.tacticSeq) (f μ hG : Expr) : TacticM (Option Expr) := do
  let f ← instantiateMVars f
  let name := if let .lam n .. := f then n else `x
  withLocalDeclD name q(ℝ) fun x ↦ factorMeasurable? disch μ x hG (mkApp f x).headBeta fz.path

/-! ### Integrability of the factor -/

/-- A hypothesis of integrability of a function (see `integrabilitySources`). -/
meta structure IntegrabilitySource where
  /-- The hypothesis. -/
  proof : Expr

/-- The function `g`, the measure `μ` and the set `s'`, `none` for an integrability on the whole
space, of an integrability statement: `Integrable g μ`, `Integrable g (μ.restrict s')` or
`IntegrableOn g s' μ`. -/
meta def integrabilityStatement? (type : Expr) : Option (Expr × Expr × Option Expr) :=
  match_expr type with
  | Integrable _ _ _ _ _ g μ =>
    match_expr μ with
    | Measure.restrict _ _ μ s => some (g, μ, some s)
    | _ => some (g, μ, none)
  | IntegrableOn _ _ _ _ _ g s μ => some (g, μ, some s)
  | _ => none

/-- The integrability hypotheses of the local context: the hypotheses whose types are statements of
`integrabilityStatement?`. -/
meta def integrabilitySources : MetaM (Array IntegrabilitySource) := do
  let mut sources := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    if (integrabilityStatement? type).isSome then
      sources := sources.push ⟨decl.toExpr⟩
  return sources

/-- A proof of `t ⊆ s'` for intervals with the same ends, `s'` being at least as closed as `t`. -/
meta def intervalSubset? (t s' : Expr) : TacticM (Option Expr) := do
  have t : Q(Set ℝ) := t
  have s' : Q(Set ℝ) := s'
  let proof ← mkFreshExprMVar q($t ⊆ $s')
  let tac ← `(tactic| (
    intro x hx
    simp only [Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi,
      Set.mem_Iic, Set.mem_Iio] at hx ⊢
    first
      | exact hx.le
      | exact ⟨hx.1.le, hx.2.le⟩
      | exact ⟨hx.1, hx.2.le⟩
      | exact ⟨hx.1.le, hx.2⟩))
  unless ← tryClose proof.mvarId! tac do return none
  instantiateMVars proof

/-- Whether the source `src` is about `G` on the interval `t` for the measure `μ`: its function is
`G`, up to beta reduction and instances, its measure is `μ`, and its set, if any, is one of the
intervals with the ends of `t` (`Interval.candidates`). -/
meta def IntegrabilitySource.isAbout (src : IntegrabilitySource) (G : Expr) (t : Interval)
    (μ : Expr) : MetaM Bool := do
  let candidates ← t.candidates.mapM (·.toExpr)
  let some (g, μ', s'?) := integrabilityStatement? (← instantiateMVars (← inferType src.proof))
    | return false
  withNewMCtxDepth <| withTransparency .instances do
    unless ← isDefEq g G <&&> isDefEq μ' μ do return false
    let some s' := s'? | return true
    candidates.anyM (isDefEq · s')

/-- Whether the subexpression `e` of an integrand in the variable `x` is a candidate factor for the
interval `t` and the measure `μ`: the body at `x` of the function of one of the `sources` about
`fun x ↦ e` (see `IntegrabilitySource.isAbout`), found by unification only. -/
meta def isFactorCandidate (sources : Array IntegrabilitySource) (t : Interval) (μ x e : Expr) :
    MetaM Bool := do
  if sources.isEmpty then return false
  let G := (← mkLambdaFVars #[x] e).eta
  sources.anyM (·.isAbout G t μ)

/-- If the trace class `Tactic.endpoint_integrability` is enabled, trace the hypotheses of
`sources` which are not used for the integrand `f`, called `noun` in the message, the interval `t`
and the measure `μ` only because of their set: their function is a candidate factor of `f` and their
measure is `μ`, but their set is not an interval with the ends of `t` (see
`IntegrabilitySource.isAbout`). -/
meta def traceUnusedSources (noun : String) (sources : Array IntegrabilitySource) (f : Expr)
    (t : Interval) (μ : Expr) : MetaM Unit := do
  unless ← isTracingEnabledFor `Tactic.endpoint_integrability do return
  let set ← t.toExpr
  for src in sources do
    let type ← instantiateMVars (← inferType src.proof)
    let some (g, μ', _) := integrabilityStatement? type | continue
    if ← src.isAbout g t μ then continue
    unless ← withNewMCtxDepth <| withTransparency .instances <| isDefEq μ' μ do continue
    let isFactor (x e : Expr) : MetaM Bool := do
      withNewMCtxDepth <| withTransparency .instances <| isDefEq (← mkLambdaFVars #[x] e).eta g
    if (← factorizations f isFactor).isEmpty then continue
    trace[Tactic.endpoint_integrability] "{← sentence [.text "the hypothesis ", .expr type,
      .text s!" is not used: it is about a factor of {noun}, but not on an interval with the ends \
      of ", .expr set]}"

/-- A proof of `IntegrableOn G t μ`, for an interval `t`, from one of the `sources` about `G` (see
`IntegrabilitySource.isAbout`): a proof of `Integrable G μ`, or of `IntegrableOn G s' μ` for an
interval `s'` with the ends of `t` which contains `t`. -/
meta def integrableOn? (sources : Array IntegrabilitySource) (G : Expr) (t : Interval) (μ : Expr) :
    TacticM (Option Expr) := do
  let set ← t.toExpr
  let fromSource (src : IntegrabilitySource) : TacticM (Option Expr) := do
    unless ← src.isAbout G t μ do return none
    let h := src.proof
    let some (_, _, s'?) := integrabilityStatement? (← instantiateMVars (← inferType h))
      | return none
    let some s' := s'? | do
      let proof ← mkFreshExprMVar (← mkAppM ``IntegrableOn #[G, set, μ])
      closeWith proof.mvarId! ``Integrable.integrableOn [h]
      return some (← instantiateMVars proof)
    if ← withNewMCtxDepth <| withTransparency .instances <| isDefEq s' set then return some h
    let some hsub ← intervalSubset? set s' | return none
    return some (← mkAppM ``IntegrableOn.mono_set #[h, hsub])
  for src in sources do
    let state ← saveState
    try
      if let some h ← fromSource src then return some h
    catch _ => state.restore
  return none

/-! ### Local integrability -/

/-- Prove `goal : LocallyIntegrableOn f t μ` through an integrable factor, on the open
interval `t` from a factorization of `f` (see `factorizations`) whose factor `G` is integrable on
`t` (see `integrableOn?`) and whose cofactor `H` is continuous on `t`, by `funProp?`, whose
pointwise side goals on `t` are left with the case tag `continuity`, and
`MeasureTheory.LocallyIntegrableOn.of_norm_le_mul`. The factorizations are tried in the order of
`factorizations`, the largest factor first. -/
meta def proveMiddleByFactor? (disch : TSyntax ``Parser.Tactic.tacticSeq) (goal : MVarId)
    (f μ : Expr) (t : Interval) (noun := "the integrand") : TacticM (Option (List MVarId)) := do
  let sources ← integrabilitySources
  let fzs ← factorizations f (isFactorCandidate sources t μ)
  if fzs.isEmpty then
    traceUnusedSources noun sources f t μ
    return none
  let set ← t.toExpr
  let restricted ← mkAppM ``Measure.restrict #[μ, set]
  for fz in fzs do
    let some hG ← integrableOn? sources fz.factor t μ | continue
    trace[Tactic.endpoint_integrability] "{← sentence [.expr fz.factor, .text " is an integrable \
      factor, with the cofactor ", .expr fz.cofactor]}"
    let some (hH, goals) ← funProp? disch (← mkAppM ``ContinuousOn #[fz.cofactor, set]) set
      | trace[Tactic.endpoint_integrability] "{← sentence ["the cofactor is not proved continuous \
          on ", set, ", by a hypothesis or `fun_prop`"]}"
        continue
    let hGm ← mkAppM ``Integrable.aestronglyMeasurable #[hG]
    let some hf ← fz.measurable? disch f restricted hGm
      | trace[Tactic.endpoint_integrability] "{noun} is not proved measurable"
        continue
    let hs ← proveWith (← mkAppM ``MeasurableSet #[set]) (← t.shape).measurableSet
    let hle ← withLocalDeclD `x q(ℝ) fun x ↦ do
      withLocalDeclD `hx (← mkAppM ``Membership.mem #[set, x]) fun hx ↦ do
        mkLambdaFVars #[x, hx] (mkApp fz.bound x)
    assignChecked goal (← mkAppM ``LocallyIntegrableOn.of_norm_le_mul
      #[hs, ← mkAppM ``IntegrableOn.locallyIntegrableOn #[hG], hH, hf, hle])
    traceStep (return m!"{checkEmoji} an integrable factor times a continuous cofactor: locally \
      integrable")
    return some goals
  return none

/-! ### Measurability facts -/

/-- The facts `AEStronglyMeasurable g (μ.restrict s)`, with their proofs, for the functions `g`
of the integrability hypotheses of the local context which apply on the interval `s` (see
`integrableOn?`). -/
meta def measurabilityFacts (μ : Expr) (s : Interval) : TacticM (Array (Expr × Expr)) := do
  let sources ← integrabilitySources
  let mut facts := #[]
  for src in sources do
    let some (g, _, _) := integrabilityStatement? (← instantiateMVars (← inferType src.proof))
      | continue
    let some h ← integrableOn? sources g s μ | continue
    let h ← mkAppM ``Integrable.aestronglyMeasurable #[h]
    facts := facts.push (← instantiateMVars (← inferType h), h)
  return facts

/-- Run `k` with the `facts`, types with their proofs, as local hypotheses, and replace these
hypotheses by their proofs in its result. The result must not contain metavariables depending on
the hypotheses. -/
meta def withMeasurabilityFacts (facts : Array (Expr × Expr)) (k : TacticM (Option Expr)) :
    TacticM (Option Expr) :=
  withLocalDeclsDND (facts.map fun (type, _) ↦ (`h, type)) fun hs ↦ do
    let some p ← k | return none
    return some ((← instantiateMVars p).replaceFVars hs (facts.map (·.2)))

end Mathlib.Tactic.EndpointIntegrability
