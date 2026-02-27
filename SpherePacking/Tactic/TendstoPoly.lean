/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert

/-!
# `tendsto_poly` tactic

A tactic for proving goals of the form
  `Tendsto (fun z => poly(f₁ z, ..., fₙ z)) l (nhds c)`
where atomic limits `Tendsto fᵢ l (nhds aᵢ)` are known from context.

## Strategy

1. Parse the goal to extract the body, filter, and target limit.
2. Scan context for `Tendsto` hypotheses matching the goal filter.
3. Identify which atoms appear in the goal body.
4. Bundle atoms into a right-associated product via `prodMk_nhds`.
5. Abstract the body: replace `fᵢ(z)` with projections from the product.
6. Prove continuity of the abstracted function via `fun_prop`.
7. Combine via `tendsto_continuousAt_comp` and close the goal.
-/

open Lean Meta Elab Tactic

/-- Compose a continuous function with a convergent one. Stated with an
    explicit lambda (no `Function.comp`) so the kernel sees the right type. -/
theorem tendsto_continuousAt_comp
    {α β γ : Type*} [TopologicalSpace β] [TopologicalSpace γ]
    {l : Filter α} {f : α → β} {h : β → γ} {b : β}
    (hh : ContinuousAt h b) (hf : Filter.Tendsto f l (nhds b)) :
    Filter.Tendsto (fun x => h (f x)) l (nhds (h b)) :=
  hh.tendsto.comp hf

namespace TendstoPoly

/-- An atom: a context hypothesis `Tendsto f l (nhds a)` appearing in the goal body. -/
structure Atom where
  fn : Expr
  limit : Expr
  hyp : Expr
  codTy : Expr
  deriving Inhabited

-- ══════════════════════════════════════════════════════════════
-- Goal and hypothesis parsing
-- ══════════════════════════════════════════════════════════════

/-- Match `Filter.Tendsto f l target` returning (α, β, f, l, target). -/
private def matchTendsto? (e : Expr) :
    MetaM (Option (Expr × Expr × Expr × Expr × Expr)) := do
  let match1 (e : Expr) := do
    match e.getAppFnArgs with
    | (``Filter.Tendsto, #[α, β, f, l, tgt]) =>
      return some (α, β, f, l, tgt)
    | _ => return none
  if let some r ← match1 e then return some r
  match1 (← whnfR e)

/-- Extract the limit from `nhds a`, returning `a`. -/
private def matchNhds? (e : Expr) : MetaM (Option Expr) := do
  let match1 (e : Expr) :=
    match e.getAppFnArgs with
    | (``nhds, #[_, _, a]) => some a
    | _ => none
  if let some a := match1 e then return some a
  return match1 (← whnfR e)

/-- Parse the goal `Tendsto goalFn l (nhds c)`. -/
private def parseGoal (goal : Expr) :
    MetaM (Expr × Expr × Expr × Expr × Expr) := do
  match ← matchTendsto? goal with
  | some (domTy, codTy, goalFn, l, tgt) =>
    match ← matchNhds? tgt with
    | some c => return (goalFn, l, c, domTy, codTy)
    | none =>
      throwError "tendsto_poly: target filter is not `nhds _`"
  | none =>
    throwError "tendsto_poly: goal is not `Tendsto f l (nhds c)`"

/-- Match `Tendsto f l (nhds a)` in a hypothesis type. -/
private def matchTendstoNhds? (e : Expr) :
    MetaM (Option (Expr × Expr × Expr × Expr)) := do
  match ← matchTendsto? e with
  | some (_α, codTy, f, l, tgt) =>
    match ← matchNhds? tgt with
    | some a => return some (codTy, f, l, a)
    | none => return none
  | none => return none

-- ══════════════════════════════════════════════════════════════
-- Atom discovery
-- ══════════════════════════════════════════════════════════════

/-- Check if `e` is `f(bvar)` for some candidate atom. -/
private def matchAtom? (e : Expr) (bvar : FVarId)
    (candidates : Array Atom) : MetaM (Option Atom) := do
  let bvarExpr := Expr.fvar bvar
  unless e.isApp do return none
  let args := e.getAppArgs
  unless args.size > 0 do return none
  unless args.back! == bvarExpr do return none
  let fn := e.getAppFn
  let fnApplied := if args.size == 1 then fn
    else mkAppN fn args.pop
  if fnApplied.containsFVar bvar then return none
  for cand in candidates do
    if ← withNewMCtxDepth (isDefEq fnApplied cand.fn) then
      return some cand
  return none

/-- Children for left-to-right DFS. -/
private def exprChildren (e : Expr) : Array Expr :=
  match e with
  | .app f a => #[f, a]
  | .lam _ t b _ => #[t, b]
  | .forallE _ t b _ => #[t, b]
  | .letE _ t v b _ => #[t, v, b]
  | .mdata _ e => #[e]
  | .proj _ _ e => #[e]
  | _ => #[]

/-- DFS to find atoms. Uses IO.Ref for accumulation. -/
private partial def findAtomsAux (e : Expr) (bvar : FVarId)
    (candidates : Array Atom)
    (atomsRef : IO.Ref (Array Atom))
    (fnsRef : IO.Ref (Array Expr)) : MetaM Unit := do
  if !e.containsFVar bvar then return
  match ← matchAtom? e bvar candidates with
  | some cand =>
    let usedFns ← fnsRef.get
    let isDup ← usedFns.anyM fun usedFn =>
      withNewMCtxDepth (isDefEq usedFn cand.fn)
    unless isDup do
      atomsRef.modify (·.push cand)
      fnsRef.modify (·.push cand.fn)
  | none =>
    for child in exprChildren e do
      findAtomsAux child bvar candidates atomsRef fnsRef

/-- Collect atoms matching the goal filter and appearing in body. -/
private def collectAtoms (body : Expr) (bvar : FVarId)
    (goalFilter : Expr) : TacticM (Array Atom) := do
  let ctx ← getLCtx
  let mut candidates : Array Atom := #[]
  for decl in ctx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    match ← matchTendstoNhds? ty with
    | some (codTy, f, l, a) =>
      if ← withNewMCtxDepth (isDefEq l goalFilter) then
        candidates := candidates.push
          { fn := f, limit := a, hyp := decl.toExpr
            codTy := codTy }
    | none => continue
  let atomsRef ← IO.mkRef (α := Array Atom) #[]
  let fnsRef ← IO.mkRef (α := Array Expr) #[]
  findAtomsAux body bvar candidates atomsRef fnsRef
  atomsRef.get

-- ══════════════════════════════════════════════════════════════
-- Product type / limit / proof builders
-- ══════════════════════════════════════════════════════════════

/-- Right-associated product type. -/
private def buildProdType (atoms : Array Atom) : MetaM Expr := do
  if atoms.size == 1 then return atoms[0]!.codTy
  let mut ty := atoms.back!.codTy
  for i in List.range (atoms.size - 1) |>.reverse do
    ty ← mkAppM ``Prod #[atoms[i]!.codTy, ty]
  return ty

/-- Right-associated limit point. -/
private def buildLimitPoint (atoms : Array Atom) :
    MetaM Expr := do
  if atoms.size == 1 then return atoms[0]!.limit
  let mut pt := atoms.back!.limit
  for i in List.range (atoms.size - 1) |>.reverse do
    pt ← mkAppM ``Prod.mk #[atoms[i]!.limit, pt]
  return pt

/-- Chain of `prodMk_nhds` applications. -/
private def buildProdMkNhds (atoms : Array Atom) :
    MetaM Expr := do
  if atoms.size == 1 then return atoms[0]!.hyp
  let mut proof := atoms.back!.hyp
  for i in List.range (atoms.size - 1) |>.reverse do
    proof ← mkAppM ``Filter.Tendsto.prodMk_nhds
      #[atoms[i]!.hyp, proof]
  return proof

/-- Projection `p.2.2...fst/snd` for atom `i` of `n`. -/
private def buildProjection (p : Expr) (n i : Nat) :
    MetaM Expr := do
  if n == 1 then return p
  let mut e := p
  for _ in List.range i do
    e ← mkAppM ``Prod.snd #[e]
  if i < n - 1 then
    e ← mkAppM ``Prod.fst #[e]
  return e


-- ══════════════════════════════════════════════════════════════
-- Body abstraction
-- ══════════════════════════════════════════════════════════════

/-- Replace `fᵢ(bvar)` with `projᵢ(p)` in the body. -/
private partial def abstractBody (body : Expr) (bvar : FVarId)
    (pVar : Expr) (atoms : Array Atom) : MetaM Expr := do
  if !body.containsFVar bvar then return body
  let bvarExpr := Expr.fvar bvar
  if body.isApp then
    let fn := body.getAppFn
    let args := body.getAppArgs
    if args.size > 0 && args.back! == bvarExpr then
      let fnApplied := if args.size == 1 then fn
        else mkAppN fn args.pop
      if !fnApplied.containsFVar bvar then
        for i in List.range atoms.size do
          if ← withNewMCtxDepth (isDefEq fnApplied atoms[i]!.fn)
          then
            return ← buildProjection pVar atoms.size i
  match body with
  | .app f a =>
    return .app (← abstractBody f bvar pVar atoms)
                (← abstractBody a bvar pVar atoms)
  | .lam n t b bi =>
    return .lam n (← abstractBody t bvar pVar atoms)
                  (← abstractBody b bvar pVar atoms) bi
  | .letE n t v b nd =>
    return .letE n (← abstractBody t bvar pVar atoms)
                   (← abstractBody v bvar pVar atoms)
                   (← abstractBody b bvar pVar atoms) nd
  | .mdata m e =>
    return .mdata m (← abstractBody e bvar pVar atoms)
  | .proj s i e =>
    return .proj s i (← abstractBody e bvar pVar atoms)
  | _ => return body

-- ══════════════════════════════════════════════════════════════
-- Main tactic
-- ══════════════════════════════════════════════════════════════

/-- The `tendsto_poly` tactic. -/
def tendstoPoly : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalTy ← goal.getType >>= instantiateMVars

  let (goalFn, goalFilter, _goalLimit, domTy, _codTy) ←
    parseGoal goalTy

  -- goalFn must be a lambda
  let body ← match goalFn with
    | .lam _ _ b _ => pure b
    | _ => throwError
      "tendsto_poly: goal function is not a lambda.\n\
       Hint: try `show Tendsto (fun z => ...) _ (nhds _)` \
       or `unfold ...`"

  -- Collect atoms and build proof components inside
  -- withLocalDecl, then do goal manipulation outside.
  let (atoms, _prodMkProof, _contMVar, proof) ← do
    withLocalDecl `z .default domTy fun zVar => do
      let body := body.instantiate1 zVar
      let bvar := zVar.fvarId!

      let atoms ← collectAtoms body bvar goalFilter

      -- 0 atoms: constant function
      if atoms.size == 0 then
        try
          let _ ← Elab.Tactic.run goal
            (Elab.Tactic.evalTactic
              (← `(tactic| exact tendsto_const_nhds)))
          return (atoms, default, default, default)
        catch _ =>
          throwError "tendsto_poly: constant body but \
            `tendsto_const_nhds` failed"

      let prodTy ← buildProdType atoms
      let limitPt ← buildLimitPoint atoms
      let prodMkProof ← buildProdMkNhds atoms

      -- Build polyFn via nested withLocalDecl
      let (contMVar, proof) ←
        withLocalDecl `p .default prodTy fun pVar => do
          let abstracted ←
            abstractBody body bvar pVar atoms
          let polyFn ← mkLambdaFVars #[pVar] abstracted

          let contGoalTy ←
            mkAppM ``ContinuousAt #[polyFn, limitPt]
          let contMVar ← mkFreshExprMVar contGoalTy
          try
            let _ ← Elab.Tactic.run contMVar.mvarId!
              (Elab.Tactic.evalTactic
                (← `(tactic| fun_prop)))
          catch e =>
            throwError m!"tendsto_poly: `fun_prop` failed:\
              \n{← e.toMessageData.format}\n\
              goal: {contGoalTy}"

          let proof ← mkAppM ``tendsto_continuousAt_comp
            #[contMVar, prodMkProof]
          return (contMVar, proof)

      return (atoms, prodMkProof, contMVar, proof)

  -- If 0 atoms, goal was already closed above
  if atoms.size == 0 then return

  -- The proof's limit may not be kernel-defeq to the
  -- goal's (e.g. `1 + 2` vs `3`). Use `convert using 1`
  -- to match function/filter by defeq, leaving only the
  -- `nhds` target equality, then close with `congr 1; norm_num`.
  let proofTy ← inferType proof
  let keyName := `_tendsto_poly_key
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
          (← `(tactic| first | rfl | (congr 1; norm_num))))
      unless r.isEmpty do
        throwError "tendsto_poly: subgoal not closed by \
          `rfl` or `congr 1; norm_num`"
    catch e =>
      throwError m!"tendsto_poly: failed to close \
        subgoal after convert:\n\
        {← e.toMessageData.format}"

elab "tendsto_poly" : tactic => tendstoPoly

end TendstoPoly
