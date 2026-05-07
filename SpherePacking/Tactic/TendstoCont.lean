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

/-!
# `tendsto_cont` tactic

Proves `Tendsto (fun z => expr(f₁ z, ..., fₙ z)) l (nhds c)` from atomic
`Tendsto fᵢ l (nhds aᵢ)` hypotheses by abstracting the body and discharging
continuity via `fun_prop`. Strategy: parse goal → collect atoms → bundle via
`prodMk_nhds` → abstract body to a function of the product → `fun_prop` for
continuity → compose.
-/

@[expose] public section

open Lean Meta Elab Tactic

/-- Compose a continuous function with a convergent one (explicit lambda for kernel typing). -/
theorem tendsto_continuousAt_comp
    {α β γ : Type*} [TopologicalSpace β] [TopologicalSpace γ]
    {l : Filter α} {f : α → β} {h : β → γ} {b : β}
    (hh : ContinuousAt h b) (hf : Filter.Tendsto f l (nhds b)) :
    Filter.Tendsto (fun x => h (f x)) l (nhds (h b)) := hh.tendsto.comp hf

namespace TendstoCont

/-- An atom: a context hypothesis `Tendsto f l (nhds a)` appearing in the goal body. -/
meta structure Atom where
  fn : Expr
  limit : Expr
  hyp : Expr
  codTy : Expr
  deriving Inhabited

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

/-- Parse the goal `Tendsto goalFn l (nhds c)`, returning `(goalFn, l, domTy)`. -/
private meta def parseGoal (goal : Expr) : MetaM (Expr × Expr × Expr) := do
  let some (domTy, _, goalFn, l, tgt) ← matchTendsto? goal
    | throwError "tendsto_cont: goal is not `Tendsto f l (nhds c)`"
  let some _ ← matchNhds? tgt
    | throwError "tendsto_cont: target filter is not `nhds _`"
  return (goalFn, l, domTy)

/-- Match `Tendsto f l (nhds a)` in a hypothesis type. -/
private meta def matchTendstoNhds? (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let some (_α, codTy, f, l, tgt) ← matchTendsto? e | return none
  let some a ← matchNhds? tgt | return none
  return some (codTy, f, l, a)

/-- Check if `e` equals `cand.fn bvar` for some candidate (`isDefEq` handles coercions). -/
private meta def matchAtom? (e : Expr) (bvar : FVarId)
    (candidates : Array Atom) : MetaM (Option Atom) := do
  unless e.containsFVar bvar do return none
  for cand in candidates do
    if ← withNewMCtxDepth (isDefEq e (mkApp cand.fn (.fvar bvar))) then return some cand
  return none

/-- Children for left-to-right DFS. -/
private meta def exprChildren : Expr → Array Expr
  | .app f a => #[f, a]
  | .lam _ t b _ => #[t, b]
  | .forallE _ t b _ => #[t, b]
  | .letE _ t v b _ => #[t, v, b]
  | .mdata _ e => #[e]
  | .proj _ _ e => #[e]
  | _ => #[]

/-- DFS to find atoms. Uses IO.Ref for accumulation. -/
private meta partial def findAtomsAux (e : Expr) (bvar : FVarId) (candidates : Array Atom)
    (atomsRef : IO.Ref (Array Atom)) (fnsRef : IO.Ref (Array Expr)) : MetaM Unit := do
  if !e.containsFVar bvar then return
  match ← matchAtom? e bvar candidates with
  | some cand =>
    unless ← (← fnsRef.get).anyM (withNewMCtxDepth <| isDefEq · cand.fn) do
      atomsRef.modify (·.push cand)
      fnsRef.modify (·.push cand.fn)
  | none =>
    for child in exprChildren e do findAtomsAux child bvar candidates atomsRef fnsRef

/-- Collect atoms matching the goal filter and appearing in body. Returns
    `(candidates, usedAtoms)` — candidates for diagnostics. -/
private meta def collectAtoms (body : Expr) (bvar : FVarId)
    (goalFilter : Expr) : TacticM (Array Atom × Array Atom) := do
  let mut candidates : Array Atom := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    match ← matchTendstoNhds? (← instantiateMVars decl.type) with
    | some (codTy, f, l, a) =>
      if ← withNewMCtxDepth (isDefEq l goalFilter) then
        candidates := candidates.push
          { fn := f, limit := a, hyp := decl.toExpr, codTy := codTy }
    | none => continue
  let atomsRef ← IO.mkRef (α := Array Atom) #[]
  let fnsRef ← IO.mkRef (α := Array Expr) #[]
  findAtomsAux body bvar candidates atomsRef fnsRef
  let atoms ← atomsRef.get
  for atom in atoms do
    for cand in candidates do
      if ← withNewMCtxDepth (isDefEq atom.fn cand.fn) then
        unless ← withNewMCtxDepth (isDefEq atom.limit cand.limit) do
          throwError m!"tendsto_cont: ambiguous limit for atom — found hypotheses with \
            limits `{atom.limit}` and `{cand.limit}` for the same function"
  return (candidates, atoms)

/-- Fold atoms right-associatively using `combine` on the given per-atom field. -/
private meta def foldRightAssoc (atoms : Array Atom) (field : Atom → Expr)
    (combine : Expr → Expr → MetaM Expr) : MetaM Expr := do
  if atoms.size = 1 then return field atoms[0]!
  let mut acc := field atoms.back!
  for i in List.range (atoms.size - 1) |>.reverse do acc ← combine (field atoms[i]!) acc
  return acc

/-- Right-associated product type. -/
private meta def buildProdType (atoms : Array Atom) : MetaM Expr :=
  foldRightAssoc atoms (·.codTy) fun a b => mkAppM ``Prod #[a, b]

/-- Right-associated limit point. -/
private meta def buildLimitPoint (atoms : Array Atom) : MetaM Expr :=
  foldRightAssoc atoms (·.limit) fun a b => mkAppM ``Prod.mk #[a, b]

/-- Chain of `prodMk_nhds` applications. -/
private meta def buildProdMkNhds (atoms : Array Atom) : MetaM Expr :=
  foldRightAssoc atoms (·.hyp) fun a b => mkAppM ``Filter.Tendsto.prodMk_nhds #[a, b]

/-- Projection `p.2.2...fst/snd` for atom `i` of `n`. -/
private meta def buildProjection (p : Expr) (n i : Nat) :
    MetaM Expr := do
  if n = 1 then return p
  let mut e := p
  for _ in [:i] do
    e ← mkAppM ``Prod.snd #[e]
  if i < n - 1 then e ← mkAppM ``Prod.fst #[e]
  return e

/-- Replace `fᵢ(bvar)` with `projᵢ(p)` in the body. -/
private meta partial def abstractBody (body : Expr) (bvar : FVarId)
    (pVar : Expr) (atoms : Array Atom) : MetaM Expr := do
  if !body.containsFVar bvar then return body
  for i in [:atoms.size] do
    if ← withNewMCtxDepth (isDefEq body (mkApp atoms[i]!.fn (.fvar bvar))) then
      return ← buildProjection pVar atoms.size i
  let go := (abstractBody · bvar pVar atoms)
  match body with
  | .app f a => return .app (← go f) (← go a)
  | .lam n t b bi => return .lam n (← go t) (← go b) bi
  | .letE n t v b nd => return .letE n (← go t) (← go v) (← go b) nd
  | .mdata m e => return .mdata m (← go e)
  | .proj s i e => return .proj s i (← go e)
  | _ => return body

/-- Close a goal using a proof whose limit may differ from the stated one (e.g. `1 + 2` vs
    `3`); `convert using 1` then `congr 1; norm_num <;> ring`. -/
private meta def reconcileLimits (goal : MVarId) (proof : Expr) : TacticM Unit := do
  let keyName := `_tendsto_cont_key
  let goal1 ← goal.define keyName (← inferType proof) proof
  let (_, goal2) ← goal1.intro keyName
  let remaining ← Elab.Tactic.run goal2
    (Elab.Tactic.evalTactic (← `(tactic| convert ($(mkIdent keyName)) using 1)))
  for g in remaining do
    try
      let r ← Elab.Tactic.run g (Elab.Tactic.evalTactic
        (← `(tactic| first | rfl | (congr 1; norm_num <;> ring))))
      unless r.isEmpty do
        throwError m!"tendsto_cont: subgoal not closed by `rfl`, `norm_num`, or \
          `ring`:\n{← g.getType}"
    catch e =>
      throwError m!"tendsto_cont: failed to close subgoal after convert:\n{← g.getType}\n\
        {← e.toMessageData.format}"

/-- Build the continuity-based proof for a non-constant body with atoms. -/
private meta def buildContinuityProof (body : Expr) (bvar : FVarId)
    (atoms : Array Atom) : TacticM Expr := do
  withLocalDecl `p .default (← buildProdType atoms) fun pVar => do
    let contFn ← mkLambdaFVars #[pVar] (← abstractBody body bvar pVar atoms)
    let contGoalTy ← mkAppM ``ContinuousAt #[contFn, ← buildLimitPoint atoms]
    let contMVar ← mkFreshExprMVar contGoalTy
    try
      let _ ← Elab.Tactic.run contMVar.mvarId!
        (Elab.Tactic.evalTactic (← `(tactic| fun_prop)))
    catch e =>
      throwError m!"tendsto_cont: `fun_prop` failed:\n{← e.toMessageData.format}\ngoal: \
        {contGoalTy}"
    mkAppM ``tendsto_continuousAt_comp #[contMVar, ← buildProdMkNhds atoms]

/-- Core implementation of the `tendsto_cont` tactic. -/
private meta def tendstoCont : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let (goalFn, goalFilter, domTy) ← parseGoal (← goal.getType >>= instantiateMVars)
  let body ← match (← whnfR goalFn) with
    | .lam _ _ b _ => pure b
    | _ => throwError "tendsto_cont: goal function is not a lambda. Hint: try \
      `show Tendsto (fun z => ...) _ (nhds _)` or `unfold ...`"
  let proof? ← withLocalDecl `z .default domTy fun zVar => do
    let body := body.instantiate1 zVar
    let bvar := zVar.fvarId!
    let (candidates, atoms) ← collectAtoms body bvar goalFilter
    if atoms.size == 0 then
      if body.containsFVar bvar then
        if candidates.size == 0 then
          throwError m!"tendsto_cont: no `Tendsto` hypotheses found for filter \
            `{← ppExpr goalFilter}`"
        throwError m!"tendsto_cont: body references the bound variable but no \
          candidate matched.\nAvailable candidates: \
          {← candidates.mapM fun c => ppExpr c.fn}"
      try
        let _ ← Elab.Tactic.run goal
          (Elab.Tactic.evalTactic (← `(tactic| exact tendsto_const_nhds)))
        return none
      catch _ => throwError "tendsto_cont: constant body but `tendsto_const_nhds` failed"
    some <$> buildContinuityProof body bvar atoms
  if let some proof := proof? then reconcileLimits goal proof

elab "tendsto_cont" : tactic => TendstoCont.tendstoCont

end TendstoCont
