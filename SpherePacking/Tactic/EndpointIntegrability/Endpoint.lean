/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
module

public import SpherePacking.Tactic.EndpointIntegrability.Decide
public import SpherePacking.Tactic.EndpointIntegrability.Domination
public import SpherePacking.Tactic.EndpointIntegrability.Factor
public import SpherePacking.Tactic.EndpointIntegrability.Rules

/-!
# One end of `endpoint_integrability`

The steps of the tactic at one end (see `SpherePacking.Tactic.EndpointIntegrability.Tactic`):
`proveEnd` proves a goal `IntegrableAtFilter f l μ` of the split
(`SpherePacking.Tactic.EndpointIntegrability.Interval`) by the first of these which succeeds, run
by `attempt?`; if none does, the goal is left as it is.

1. A hypothesis (`proveByAssumption?`).
2. Comparison with the scale (`proveByComparison?`), for the measure `volume` and values in `ℝ` or
   `ℂ`: the integrand is proved strongly measurable at `l` (`stronglyMeasurableAtFilter?`), the end
   is moved to `atTop` or `𝓝[>] 0`, the comparison engine bounds the integrand by a sum of
   functions of the scale (`SpherePacking.Tactic.EndpointIntegrability.Compare`), and the
   integrability of this majorant is decided (`SpherePacking.Tactic.EndpointIntegrability.Decide`).
   A comparison which leaves a condition on parameters, such as `1 < s`, succeeds.
3. An integrable factor (`proveByFactor?`), for the measure `volume`: if the integrand has a
   factor `G x` which a hypothesis proves integrable
   (`SpherePacking.Tactic.EndpointIntegrability.Factor`), its cofactor `H` need only be bounded at
   `l`, which the engine proves on `H` alone (`proveBoundedAtEnd?`); the engine never sees `G`.

The side goals left by the first which succeeds get the case tag of the end. With
`set_option trace.Tactic.endpoint_integrability true`, the tactic reports why an end is not proved.

## Reduction to the canonical filters

The ends `atBot`, `𝓝[<] b` and `𝓝[>] a` (with `a` not `0`) are reduced (`reduction?`), by the
lemmas of `SpherePacking.Tactic.EndpointIntegrability.Lemmas`, to `atTop` for `fun t ↦ f (-t)`, and
to `𝓝[>] 0` for `fun t ↦ f (b - t)` and `fun t ↦ f (a + t)`. The new integrand is normalised by
`simp only` with `substitutionLemmas`, which cancels `a + t - a`, `b - (b - t)`, `-(-t)` and the
like, and nothing else, so that the rules still see the real powers and exponents as written: an
end `b` must appear in the integrand as the same expression, as in `x - b` or `b - x`.

The hypotheses `h : F =O[l] G` of the context, along the filter `l` of the end and without
quantifiers or premises, and the pointwise bounds on a set of `l`, such as
`∀ x ∈ Ici 2, ‖g x‖ ≤ b x` at `atTop`, which give `g =O[l] b` (`boundAtEnd?`), are transported
along the change of variables, by
`Asymptotics.IsBigO.comp_tendsto`, and normalised in the same way (`endpointHypotheses`), so that
the engine only sees hypotheses along its canonical filter and need not know the substitution.
The boundedness of the cofactor of an integrable factor is reduced in the same way
(`changeVariable`).
-/

@[expose] public section

open Lean Meta Elab Tactic Qq Filter Topology Asymptotics MeasureTheory Set

namespace Mathlib.Tactic.EndpointIntegrability

/-- The trace class of the tactic: `set_option trace.Tactic.endpoint_integrability true` reports
why an end, the middle through an integrable factor, or a majorant is not proved: the reductions,
the integrable factor chosen and its cofactor, the majorant, and the obligation which fails. Its
messages about the pieces which are left also make the explanation which the tactic logs (see
`Mathlib.Tactic.EndpointIntegrability.withExplanation`). -/
meta initialize registerTraceClass `Tactic.endpoint_integrability

@[inherit_doc stepClass]
meta initialize registerTraceClass `Tactic.endpoint_integrability.step

/-! ### Strong measurability at the filter -/

/-- The lemmas proving `s ∈ l` for an interval `s` and the filter `l` at one of its ends. Their
hypotheses, such as `a < b` for `Ioo a b ∈ 𝓝[>] a`, are given to the discharger. -/
meta def memFilterLemmas : List Name :=
  [``Ioi_mem_atTop, ``Ici_mem_atTop, ``Iio_mem_atBot, ``Iic_mem_atBot, ``univ_mem,
    ``self_mem_nhdsWithin, ``Ioo_mem_nhdsGT, ``Ioc_mem_nhdsGT, ``Ico_mem_nhdsGT, ``Icc_mem_nhdsGT,
    ``Ioo_mem_nhdsLT, ``Ico_mem_nhdsLT, ``Ioc_mem_nhdsLT, ``Icc_mem_nhdsLT]

/-- A proof of `s ∈ l` by one of `memFilterLemmas`, with the discharger `disch`. The conclusion of
a lemma is unified with `s ∈ l` with only reducible definitions and instances unfolded: at the
default transparency, comparing `Icc a b` with `Ioo ?a ?b` unfolds the order of `ℝ`. -/
meta def memFilter? (disch : TSyntax ``Parser.Tactic.tacticSeq) (s l : Expr) :
    TacticM (Option Expr) := do
  have s : Q(Set ℝ) := s
  have l : Q(Filter ℝ) := l
  for name in memFilterLemmas do
    let proof ← mkFreshExprMVar q($s ∈ $l)
    let closed ← attempt proof.mvarId! do
      (← withReducibleAndInstances <| applyLemma proof.mvarId! name).allM fun g ↦ do
        tryClose g (← `(tactic| ($disch)))
    if closed then return some (← instantiateMVars proof)
  return none

/-- A proof of `StronglyMeasurableAtFilter f l μ`: from `Measurable f`, proved by `fun_prop`, or
else from the continuity of `f` on the interval `s` of `g` and `s ∈ l`. -/
meta def stronglyMeasurableAtFilter? (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (g : EndpointGoal) : TacticM (Option Expr) := do
  let proof ← mkFreshExprMVar (← mkAppM ``StronglyMeasurableAtFilter #[g.f, g.filter, g.μ])
  if let some hm ← proveFunProp? disch (← mkAppM ``Measurable #[g.f]) then
    closeWith proof.mvarId! ``StronglyMeasurable.stronglyMeasurableAtFilter
      [← mkAppM ``Measurable.stronglyMeasurable #[hm]]
    return some (← instantiateMVars proof)
  let some hc := g.continuousOn | return none
  let some hmem ← memFilter? disch g.set g.filter | return none
  let name := ``AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
  let hae :: hl :: _ ← applyLemma proof.mvarId! name | throwUnexpectedHypotheses name
  assignChecked hl hmem
  closeWith hae ``ContinuousOn.aestronglyMeasurable [hc, g.measurableSet]
  return some (← instantiateMVars proof)

/-- Why the continuity of the integrand does not give its strong measurability at the end `g`
(see `stronglyMeasurableAtFilter?`), for messages. -/
meta def continuityStatus (disch : TSyntax ``Parser.Tactic.tacticSeq) (g : EndpointGoal) :
    TacticM (List MsgPart) := do
  if g.continuousOn.isNone then return [.text ", nor continuous on ", .expr g.set]
  if (← memFilter? disch g.set g.filter).isNone then
    return [.text ", and its continuity on ", .expr g.set, .text " gives its measurability near \
      this end only with ", .expr (← mkAppM ``Membership.mem #[g.filter, g.set]),
      .text ", which is not proved"]
  return [.text ", and its continuity does not give its measurability near this end"]

/-! ### Comparison with the scale -/

/-- The summary of a bound `r` of the function `f`, `what` (`the integrand` or `the cofactor`),
whose property `prop` (`integrable` or `bounded`) the tactic does not prove, for messages: that `f`
has the order of the majorant if the result is exact (a proof of `f =Θ[l] M`, which `mkResult`
checks; it is then a single comparison function), and otherwise that the majorant is only an upper
bound. -/
meta def boundSummary (what : String) (f : Expr) (r : Result) (prop : String) :
    MetaM MessageData := do
  let M ← r.majorant.display
  if r.exact then
    return ← sentence [.text s!"{what} ", .expr f, .text " has the order of ", .expr M,
      .text s!",\nwhich is not proved {prop}:"]
  sentence [.text s!"the tactic only bounds {what} ", .expr f, .text " from above,\nup to a \
    constant factor, by ", .expr M, .text s!", which is not proved {prop}:"]

/-- The comparison engine on `f` along `l`, with the `hypotheses` (see `majorant`), and the trace
of its decline or failure. -/
meta def runEngine (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (hypotheses : Array Expr) (f : Expr) : TacticM (Option Result) := do
  let r ← try majorant l disch hypotheses f catch e =>
    trace[Tactic.endpoint_integrability] "{e.toMessageData}"
    return none
  match r with
  | .ok r => return some r
  | .error msg =>
    trace[Tactic.endpoint_integrability] "{msg}"
    return none

/-- Prove `goal : IntegrableAtFilter f l volume` along a canonical filter `l`, given a proof `hf`
of `StronglyMeasurableAtFilter f l volume`: run the comparison engine on `f`, with the
`hypotheses`, proofs of `(fun t ↦ x) =O[l] g` (see `endpointHypotheses`), and decide the
integrability of its majorant. Returns the side goals. -/
meta def proveIntegrableAtFilter? (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (hypotheses : Array Expr) (goal : MVarId) (f hf : Expr) (noun := "the integrand") :
    TacticM (Option (List MVarId)) := do
  let some r ← runEngine l disch hypotheses f | return none
  let some (hM, goals) ← traceFailureFirst (proveMajorant? l disch false r.majorant).run do
      boundSummary noun f r "integrable"
    | return none
  assignChecked goal (← mkAppM ``IsBigO.integrableAtFilter #[← r.isBigO, hf, hM])
  traceStep <| sentence [.text s!"{checkEmoji} which is integrable at ", .expr l.toExpr,
    .text (if goals.isEmpty then "" else ", under the conditions left as goals")]
  return some goals

/-- Whether `μ` is the measure `volume` on `ℝ`. -/
meta def isVolume (μ : Expr) : MetaM Bool :=
  withNewMCtxDepth <| withTransparency .instances <| isDefEq μ q((volume : Measure ℝ))

/-- Whether the codomain of `f : ℝ → E` is `ℝ` or `ℂ`. -/
meta def hasScalarCodomain (f : Expr) : MetaM Bool := do
  let .forallE _ _ E _ ← whnf (← inferType f) | return false
  return E.isConstOf ``Real || E.isConstOf ``Complex

/-! ### Reduction to the canonical filters -/

/-- The reduction of an end `l` to a canonical filter `l₀` by a change of variables `φ`: the
lemmas `IntegrableAtFilter f l ↔ IntegrableAtFilter (fun t ↦ f (φ t)) l₀`,
`StronglyMeasurableAtFilter f l → StronglyMeasurableAtFilter (fun t ↦ f (φ t)) l₀`, for the
measure `volume`, and `f =O[l] g ↔ (fun t ↦ f (φ t)) =O[l₀] fun t ↦ g (φ t)`, and a proof of
`Tendsto φ l₀ l`, along which the hypotheses are transported. -/
meta structure Reduction where
  /-- The canonical filter `l₀`. -/
  filter : CanonicalFilter
  /-- The lemma reducing the integrability. -/
  integrable : Name
  /-- The lemma transporting the strong measurability. -/
  stronglyMeasurable : Name
  /-- The lemma reducing the asymptotic comparison `f =O[l] g`. -/
  isBigO : Name
  /-- A proof of `Tendsto φ l₀ l`, with `φ` a lambda: `fun t ↦ -t`, `fun t ↦ a + t` or
  `fun t ↦ b - t`. -/
  tendsto : Expr

/-- The reduction of the end `l` to a canonical filter: `atBot` to `atTop` by `t ↦ -t`, `𝓝[>] a`
to `𝓝[>] 0` by `t ↦ a + t` and `𝓝[<] b` to `𝓝[>] 0` by `t ↦ b - t`. -/
meta def reduction? (l : Expr) : Option Reduction :=
  match_expr l with
  | atBot _ _ =>
    some ⟨.atTop, ``integrableAtFilter_atBot_iff_comp_neg, ``StronglyMeasurableAtFilter.comp_neg,
      ``isBigO_atBot_iff_comp_neg,
      q(tendsto_neg_atTop_atBot : Tendsto (fun t : ℝ ↦ -t) atTop atBot)⟩
  | nhdsWithin _ _ _ s => match_expr s with
    | Set.Ioi _ _ a => some ⟨.nhdsGT, ``integrableAtFilter_nhdsGT_iff_comp_add_left,
        ``StronglyMeasurableAtFilter.comp_add_left, ``isBigO_nhdsGT_iff_comp_add_left,
        mkApp (.const ``Real.tendsto_add_left_nhdsGT_zero []) a⟩
    | Set.Iio _ _ b => some ⟨.nhdsGT, ``integrableAtFilter_nhdsLT_iff_comp_sub_left,
        ``StronglyMeasurableAtFilter.comp_sub_left, ``isBigO_nhdsLT_iff_comp_sub_left,
        mkApp (.const ``Real.tendsto_sub_left_nhdsGT_zero []) b⟩
    | _ => none
  | _ => none

/-- The change of variables `x = φ t` of the reduction `r`, `x` being the variable of the function
`f`, or `x` if it is `t`, printed, for messages. -/
meta def Reduction.display (r : Reduction) (f : Expr) : MetaM MsgPart := do
  let some φ := (← instantiateMVars (← inferType r.tendsto)).getAppArgs[2]? | return .code "?"
  let name := match f with
    | .lam n .. => if n == `t then `x else n
    | _ => `x
  withLocalDeclD name q(ℝ) fun x ↦ withLocalDeclD `t q(ℝ) fun t ↦ do
    return .code (toString (← ppExpr (← mkEq x (φ.beta #[t]))))

/-- The lemmas normalising the integrand after a change of variables, so that the rules see the
variable: `a + t - a`, `-a + (a + t)`, `a + (-a + t)`, `-a + t + a`, `b - (b - t)` and `-(-t)`
become `t`, and `b - t - b`, `a - (a + t)` and `0 - t` become `-t`. -/
meta def substitutionLemmas : List Name :=
  [``add_sub_cancel_left, ``neg_add_cancel_left, ``add_neg_cancel_left, ``neg_add_cancel_comm,
    ``sub_sub_cancel, ``sub_sub_cancel_left, ``sub_add_cancel_left, ``zero_sub, ``neg_neg]

/-! ### Hypotheses at the ends -/

/-- The proof `h : F =O[l] G` transported along the reduction `r` of the end `l` by a change of
variables `φ`: a proof of `(fun t ↦ F (φ t)) =O[l₀] fun t ↦ G (φ t)` by
`Asymptotics.IsBigO.comp_tendsto`, with its type beta-reduced and normalised by the
simplification context `ctx` of the integrand. -/
meta def transportHypothesis? (r : Reduction) (ctx : Simp.Context) (h : Expr) :
    MetaM (Option Expr) := do
  let h ← mkAppM ``IsBigO.comp_tendsto #[h, r.tendsto]
  let type ← instantiateMVars (← inferType h)
  let some φ := (← inferType r.tendsto).getAppArgs[2]? | return none
  let args := type.getAppArgs
  let (some F, some G) := (args[6]?, args[7]?) | return none
  -- `F ∘ φ` and `G ∘ φ`, applications of `Function.comp`
  let some F := F.getAppArgs[3]? | return none
  let some G := G.getAppArgs[3]? | return none
  let (Fφ, Gφ) ← withLocalDeclD `t q(ℝ) fun t ↦ do
    let x := φ.beta #[t]
    return (← mkLambdaFVars #[t] (F.beta #[x]), ← mkLambdaFVars #[t] (G.beta #[x]))
  let type' := mkAppN type.getAppFn ((args.set! 6 Fφ).set! 7 Gφ)
  unless ← isDefEq type type' do return none
  let (s, _) ← simp type' ctx
  match s.proof? with
  | some p => return some (← mkEqMP p (← mkExpectedTypeHint h type'))
  | none => return some (← mkExpectedTypeHint h s.expr)

/-- The asymptotic bound which the pointwise bound `h` gives at the end `l`: for
`h : ∀ x ∈ t, ‖g x‖ ≤ b x` with `t ∈ l`, proved by `memFilter?` (`Ici 2 ∈ atTop`, or
`Ioc a c ∈ 𝓝[>] a` if the discharger proves `a < c`), or `h : ∀ x, ‖g x‖ ≤ b x`, a proof of
`g =O[l] b`, by `Asymptotics.IsBigO.of_forall_mem_norm_le`; likewise with `|g x|`, for real
values. If `t ∈ l` is not proved and `g` occurs in `reportFor?`, the integrand of the end, the
trace reports that the bound is not used there. -/
meta def boundAtEnd? (disch : TSyntax ``Parser.Tactic.tacticSeq) (l h : Expr)
    (reportFor? : Option Expr := none) : TacticM (Option Expr) := do
  let type ← instantiateMVars (← inferType h)
  let .forallE n α body _ := type | return none
  unless α.isConstOf ``Real do return none
  withLocalDeclD n α fun x ↦ do
    let (mem?, body) := match body.instantiate1 x with
      | .forallE _ mem b _ => (some mem, b)
      | b => (none, b)
    if body.hasLooseBVars then return none
    let_expr LE.le β _ lhs rhs := body | return none
    unless β.isConstOf ``Real do return none
    let some (inner, abs) := normOrAbs? lhs | return none
    let g := (← mkLambdaFVars #[x] inner).eta
    let b ← mkLambdaFVars #[x] rhs
    let some mem := mem? | do
      let name := if abs then ``IsBigO.of_forall_abs_le else ``IsBigO.of_forall_norm_le
      return ← observing? <| mkAppOptM name <|
        if abs then #[l, g, b, h] else #[none, none, g, l, b, h]
    unless mem.isAppOfArity ``Membership.mem 5 && mem.appArg! == x do return none
    let t := mem.appFn!.appArg!
    if t.containsFVar x.fvarId! then return none
    let some ht ← memFilter? disch t l
      | if let some f := reportFor? then
          if (f.find? (· == g.getAppFn)).isSome then
            trace[Tactic.endpoint_integrability] "{← sentence ["the bound ", type, " is not used \
              at this end: ", ← mkAppM ``Membership.mem #[l, t], " is not proved"]}"
        return none
    let name := if abs then ``IsBigO.of_forall_mem_abs_le else ``IsBigO.of_forall_mem_norm_le
    observing? <| mkAppOptM name <|
      if abs then #[l, t, g, b, ht, h] else #[none, none, g, l, t, b, ht, h]

/-- The asymptotic bounds which the pointwise bounds of the local context give at the end `l` (see
`boundAtEnd?`, to which `reportFor?` is passed): those on a set of `l` first, then those which
hold everywhere, the engine using the first hypothesis about a term. -/
meta def boundsAtEnd (disch : TSyntax ``Parser.Tactic.tacticSeq) (l : Expr)
    (reportFor? : Option Expr := none) : TacticM (Array Expr) := do
  let mut onSet := #[]
  let mut everywhere := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    let .forallE _ _ body _ := type | continue
    let some h ← boundAtEnd? disch l decl.toExpr reportFor? | continue
    if body.isForall then onSet := onSet.push h else everywhere := everywhere.push h
  return onSet ++ everywhere

/-- The asymptotic hypotheses at the end `l` of the goal, as proofs along the canonical filter of
that end for the comparison engine: the hypotheses `h : F =O[l] G` of the local context, for
functions `F` on `ℝ`, along `l` up to instances, whose type is itself `F =O[l] G`, without
universal quantifiers or premises; then the proofs `bounds`, of the same form (see `boundsAtEnd`).
The stated hypotheses come first: the engine uses the first hypothesis about a term.

They are given as they are if `l` is canonical, and otherwise, for the reduction `r` of `l`, with
the simplification context `ctx` of the integrand, transported by `transportHypothesis?`, so that
the engine finds `F (φ t)` in the integrand as it is written after the change of variables. -/
meta def endpointHypotheses (l : Q(Filter ℝ)) (reduction? : Option (Reduction × Simp.Context))
    (bounds : Array Expr := #[]) : MetaM (Array Expr) := do
  let mut stated := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let_expr IsBigO α _ _ _ _ l' _ _ := ← instantiateMVars decl.type | continue
    unless α.isConstOf ``Real do continue
    unless ← withNewMCtxDepth <| withTransparency .instances <| isDefEq l' l do continue
    stated := stated.push decl.toExpr
  (stated ++ bounds).filterMapM fun h ↦ match reduction? with
    | none => pure (some h)
    | some (r, ctx) => transportHypothesis? r ctx h

/-- The function `f` of a goal `IntegrableAtFilter f l μ`. -/
meta def integrand (goal : MVarId) : MetaM Expr := do
  match_expr ← instantiateMVars (← goal.getType) with
  | IntegrableAtFilter _ _ _ _ _ f _ _ => return f
  | _ => throwError "endpoint_integrability: internal error: not an `IntegrableAtFilter` goal"

/-- Change the variable in `goal`, a statement about a function along an end, by the equivalence
`name` of the reduction of the end, one of the lemmas of `Reduction`, and normalise the new goal by
`substitutionLemmas`. Returns the new goal, or `none` if the normalisation closes it, with the
simplification context, which normalises the hypotheses in the same way. -/
meta def changeVariable (name : Name) (goal : MVarId) : TacticM (Option MVarId × Simp.Context) := do
  let [g] ← evalTacticAt (← `(tactic| refine ($(mkCIdent name)).mpr ?_)) goal
    | throwUnexpectedHypotheses name
  let ctx ← Simp.Context.ofNames substitutionLemmas (simpOnly := true)
  return ((← simpTarget g ctx).1, ctx)

/-- Prove `goal : IntegrableAtFilter f l volume`, given a proof `hf` of
`StronglyMeasurableAtFilter f l volume`, by the reduction `r` of `l` to a canonical filter: change
the variable, normalise the integrand by `substitutionLemmas` (see `changeVariable`), and prove the
integrability at the canonical filter by `proveIntegrableAtFilter?`, with the hypotheses of the
context transported along the change of variables (see `endpointHypotheses`). -/
meta def proveByReduction? (r : Reduction) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (goal : MVarId) (l hf : Expr) (noun := "the integrand") (bounds : Array Expr := #[]) :
    TacticM (Option (List MVarId)) := do
  let f₀ ← integrand goal
  let (some g, ctx) ← changeVariable r.integrable goal | return some []
  let hf ← mkAppM r.stronglyMeasurable #[hf]
  let (s, _) ← simp (← inferType hf) ctx
  let hf ← match s.proof? with
    | some h => mkEqMP h hf
    | none => mkExpectedTypeHint hf s.expr
  let f ← integrand g
  trace[Tactic.endpoint_integrability] "{← sentence [.text "with ", ← r.display f₀,
    .text s!", {noun} is ", .expr f, .text ", at ", .expr r.filter.toExpr]}"
  let hypotheses ← endpointHypotheses l (some (r, ctx)) bounds
  proveIntegrableAtFilter? r.filter disch hypotheses g f hf noun

/-- Prove the goal of `g` by asymptotic comparison, with the measure `volume` and an integrand with
values in `ℝ` or `ℂ`: along `atTop` and `𝓝[>] 0` directly, and along `atBot`, `𝓝[<] b` and
`𝓝[>] a` by the reduction to one of them, with the hypotheses of the context (see
`endpointHypotheses`). -/
meta def proveByComparison? (disch : TSyntax ``Parser.Tactic.tacticSeq) (g : EndpointGoal)
    (bounds : Array Expr := #[]) : TacticM (Option (List MVarId)) := do
  unless ← isVolume g.μ do
    trace[Tactic.endpoint_integrability] "{← sentence ["no asymptotic comparison: it needs the \
      measure `volume`, not ", g.μ]}"
    return none
  unless ← hasScalarCodomain g.f do
    trace[Tactic.endpoint_integrability] "{← sentence ["no asymptotic comparison: it needs \
      values in `ℝ` or `ℂ`, not in ", ← inferType (mkApp g.f q((0 : ℝ)))]}"
    return none
  let some hf ← stronglyMeasurableAtFilter? disch g
    | trace[Tactic.endpoint_integrability] "{← sentence <| [.text s!"no asymptotic comparison: \
        {g.noun} is not proved measurable by `fun_prop`"] ++ (← continuityStatus disch g)}"
      return none
  if let some l ← CanonicalFilter.ofExpr? g.filter then
    let hypotheses ← endpointHypotheses g.filter none bounds
    return ← proveIntegrableAtFilter? l disch hypotheses g.goal g.f hf g.noun
  let some r := reduction? g.filter | return none
  proveByReduction? r disch g.goal g.filter hf g.noun bounds

/-! ### Integrable factors -/

/-- Prove `goal : H =O[l] fun _ ↦ 1` along a canonical filter `l`: run the comparison engine on
`H`, with the `hypotheses` (see `endpointHypotheses`), and decide the boundedness of its majorant
by `proveBounded?`. Returns the side goals. -/
meta def proveBoundedAt? (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (hypotheses : Array Expr) (goal : MVarId) (H : Expr) : TacticM (Option (List MVarId)) := do
  let some r ← runEngine l disch hypotheses H | return none
  let some (hM, goals) ← traceFailureFirst (proveBounded? l disch false r.majorant).run do
      boundSummary "the cofactor" H r "bounded"
    | return none
  assignChecked goal (← mkAppM ``IsBigO.trans #[← r.isBigO, hM])
  traceStep <| sentence [.text s!"{checkEmoji} which is bounded at ", .expr l.toExpr,
    .text (if goals.isEmpty then "" else ", under the conditions left as goals")]
  return some goals

/-- A proof of `H =O[l] fun _ ↦ 1` at the end `l`, with its side goals: by `proveBoundedAt?`
along `l` if it is canonical, and otherwise after the change of variables of the reduction of
`l` (see `changeVariable`), with the hypotheses of the context transported along it (see
`endpointHypotheses`). -/
meta def proveBoundedAtEnd? (disch : TSyntax ``Parser.Tactic.tacticSeq) (l H : Expr) :
    TacticM (Option (Expr × List MVarId)) := do
  let proof ← mkFreshExprMVar (← mkAppM ``IsBigO #[l, H, q(fun _ : ℝ ↦ (1 : ℝ))])
  let withProof (goals? : Option (List MVarId)) : TacticM (Option (Expr × List MVarId)) :=
    goals?.mapM fun goals ↦ return (← instantiateMVars proof, goals)
  if let some c ← CanonicalFilter.ofExpr? l then
    let hypotheses ← endpointHypotheses l none (← boundsAtEnd disch l)
    return ← withProof (← proveBoundedAt? c disch hypotheses proof.mvarId! H)
  let some r := reduction? l | return none
  let (some g, ctx) ← changeVariable r.isBigO proof.mvarId! | withProof (some [])
  let_expr IsBigO _ _ _ _ _ _ H' _ := ← instantiateMVars (← g.getType)
    | throwUnexpectedHypotheses r.isBigO
  trace[Tactic.endpoint_integrability] "{← sentence [.text "with ", ← r.display H,
    .text ", the cofactor is ", .expr H', .text ", at ", .expr r.filter.toExpr]}"
  let hypotheses ← endpointHypotheses l (some (r, ctx)) (← boundsAtEnd disch l)
  withProof (← proveBoundedAt? r.filter disch hypotheses g H')

/-- Prove the goal of `g` through an integrable factor, for the measure `volume`: for the first
factorization of the integrand `f` (see `factorizations`) whose factor `G` is integrable on the
open interval `t` with the ends of the goal (see `integrableOn?`), with `t` in the filter `l` of
the end (proved by `memFilter?`, which asks the discharger for `a < b` if `t` is `Ioo a b`), and
whose cofactor `H` is bounded at `l` (see `proveBoundedAtEnd?`), prove
`IntegrableAtFilter f l volume` by `MeasureTheory.IntegrableAtFilter.of_norm_le_mul`, the strong
measurability of `f` at `l` coming from its measurability on `t` along the factorization (see
`Factorization.measurable?`). Returns the side goals of the boundedness: conditions on
parameters. -/
meta def proveByFactor? (disch : TSyntax ``Parser.Tactic.tacticSeq) (g : EndpointGoal) :
    TacticM (Option (List MVarId)) := do
  unless ← isVolume g.μ do return none
  let sources ← integrabilitySources
  let t := (← parseInterval g.set).setClosed false
  let fzs ← factorizations g.f (isFactorCandidate sources t g.μ)
  if fzs.isEmpty then
    traceUnusedSources g.noun sources g.f t g.μ
    return none
  let set ← t.toExpr
  let restricted ← mkAppM ``Measure.restrict #[g.μ, set]
  for fz in fzs do
    let some hG ← integrableOn? sources fz.factor t g.μ | continue
    trace[Tactic.endpoint_integrability] "{← sentence [.expr fz.factor, .text " is an integrable \
      factor, with the cofactor ", .expr fz.cofactor]}"
    let some hmem ← memFilter? disch set g.filter
      | let order : List MsgPart ← match t.lower, t.upper with
          | .finite a _, .finite b _ => pure [.text " (the discharger does not prove ",
              .expr (← mkAppM ``LT.lt #[a, b]), .text ")"]
          | _, _ => pure []
        trace[Tactic.endpoint_integrability] "{← sentence <| [.text "the integrable factor is not \
          used: ", .expr (← mkAppM ``Membership.mem #[g.filter, set]), .text " is not proved"] ++
          order}"
        continue
    let some (hH, goals) ← proveBoundedAtEnd? disch g.filter fz.cofactor | continue
    let hGm ← mkAppM ``Integrable.aestronglyMeasurable #[hG]
    let some hm ← fz.measurable? disch g.f restricted hGm
      | trace[Tactic.endpoint_integrability] "{g.noun} is not proved measurable"
        continue
    let hf ← mkAppM ``AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem #[hm, hmem]
    let hle ← mkAppOptM ``Filter.Eventually.of_forall #[none, none, g.filter, fz.bound]
    assignChecked g.goal (← mkAppM ``IntegrableAtFilter.of_norm_le_mul
      #[← mkAppM ``IntegrableOn.integrableAtFilter #[hG, hmem], hH, hf, hle])
    traceStep (return m!"{checkEmoji} an integrable factor times a bounded cofactor: integrable")
    return some goals
  return none

/-! ### One end -/

/-- Prove the goal of `g` by a hypothesis. -/
meta def proveByAssumption? (g : EndpointGoal) : MetaM (Option (List MVarId)) := do
  unless ← g.goal.assumptionCore do return none
  traceStep (return m!"{checkEmoji} by a hypothesis")
  return some []

/-- Prove the end `g`: by a hypothesis, by comparison with the scale, through an integrable
factor, or, last, by comparison with the scale with the pointwise bounds of the context read as
asymptotic bounds at this end (see `boundsAtEnd`): a bound such as `∀ x, ‖f x‖ ≤ 1` is a weaker
fact about `f` than a stated asymptotic bound or its integrability, and is used only when these
do not prove the end. Returns the goals left: the side goals of the first which succeeds, with
the case tag of the end, or the goal of `g` itself. -/
meta def proveEnd (disch : TSyntax ``Parser.Tactic.tacticSeq) (g : EndpointGoal) :
    TacticM (List MVarId) := do
  let tagged (goals : List MVarId) : TacticM (List MVarId) := do
    let tag ← g.goal.getTag
    for goal in goals do goal.setTag tag
    return goals
  if let some goals ← attempt? g.goal (proveByAssumption? g) then return ← tagged goals
  let start := (← getTraces).size
  if let some goals ← attempt? g.goal (proveByComparison? disch g) then return ← tagged goals
  let comparison := (← getTraces).toArray.extract start
  if let some goals ← attempt? g.goal (proveByFactor? disch g) then return ← tagged goals
  -- last, the comparison again, with the pointwise bounds read as asymptotic bounds
  let isVolume ← isVolume g.μ
  let bounds ← if isVolume then boundsAtEnd disch g.filter g.f else pure #[]
  if bounds.isEmpty then return [g.goal]
  -- its trace replaces that of the first comparison, which it repeats with more hypotheses
  modifyTraces fun ts ↦
    let ts := ts.toArray
    (ts.extract 0 start ++ (ts.extract (start + comparison.size))).toPArray'
  if let some goals ← attempt? g.goal (proveByComparison? disch g bounds) then return ← tagged goals
  return [g.goal]

end Mathlib.Tactic.EndpointIntegrability
