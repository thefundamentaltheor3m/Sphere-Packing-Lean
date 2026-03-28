/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Tactic.FunProp

/-!
# Atom Engine

Reusable infrastructure for composite-atom discovery and abstraction over
a product of local hypotheses. Used by `tendsto_cont` and potentially
other tactics that prove properties by decomposing expressions into
atoms with known values, abstracting the body, and proving a property
(continuity, differentiability, etc.) of the abstraction.

## Architecture

A client tactic provides:
1. A list of **candidate atoms** — subexpressions with known values
   (e.g., functions with known limits, known derivatives, etc.).
2. A **body** expression containing occurrences of these atoms.

The atom engine then:
1. DFS-discovers which candidates actually appear in the body.
2. Builds a right-associated product type from atom codomain types.
3. Builds the product value point from atom values.
4. Abstracts the body by replacing `fᵢ(bvar)` with `projᵢ(p)`.

The client then proves whatever property it needs (continuity,
differentiability, etc.) of the abstracted function and composes
with the product proof.
-/

@[expose] public section

open Lean Meta

namespace AtomEngine

/-- An atom: a subexpression with a known value that a client tactic
    can use for decomposition. The meaning of `value` depends on the
    client: for `tendsto_cont` it is the limit; for a derivative
    tactic it would be the derivative value. -/
structure Atom where
  /-- The function expression (applied to bvar gives the subexpression). -/
  fn : Expr
  /-- The associated value (limit, derivative, etc.). -/
  value : Expr
  /-- The proof expression (Tendsto hypothesis, HasDerivAt proof, etc.). -/
  hyp : Expr
  /-- The codomain type. -/
  codTy : Expr
  deriving Inhabited

-- ══════════════════════════════════════════════════════════════
-- Atom discovery
-- ══════════════════════════════════════════════════════════════

/-- Check if `e` equals `cand.fn bvar` for some candidate atom,
    using `isDefEq` to handle coercions and implicit arguments. -/
def matchAtom? (e : Expr) (bvar : FVarId)
    (candidates : Array Atom) : MetaM (Option Atom) := do
  unless e.containsFVar bvar do return none
  let bvarExpr := Expr.fvar bvar
  for cand in candidates do
    let candApplied := mkApp cand.fn bvarExpr
    if ← withNewMCtxDepth (isDefEq e candApplied) then
      return some cand
  return none

/-- Children for left-to-right DFS. -/
def exprChildren (e : Expr) : Array Expr :=
  match e with
  | .app f a => #[f, a]
  | .lam _ t b _ => #[t, b]
  | .forallE _ t b _ => #[t, b]
  | .letE _ t v b _ => #[t, v, b]
  | .mdata _ e => #[e]
  | .proj _ _ e => #[e]
  | _ => #[]

/-- DFS to find atoms. Uses IO.Ref for accumulation. -/
partial def findAtomsAux (e : Expr) (bvar : FVarId)
    (candidates : Array Atom)
    (atomsRef : IO.Ref (Array Atom))
    (fnsRef : IO.Ref (Array Expr)) : MetaM Unit := do
  if !e.containsFVar bvar then return
  match ← matchAtom? e bvar candidates with
  | some cand =>
    let usedFns ← fnsRef.get
    let alreadyRecorded ← usedFns.anyM fun usedFn =>
      withNewMCtxDepth (isDefEq usedFn cand.fn)
    unless alreadyRecorded do
      atomsRef.modify (·.push cand)
      fnsRef.modify (·.push cand.fn)
  | none =>
    for child in exprChildren e do
      findAtomsAux child bvar candidates atomsRef fnsRef

/-- Find atoms in `body` that match `candidates`, via left-to-right DFS.
    Returns the subset of candidates that actually appear in the body,
    in discovery order. -/
def findAtoms (body : Expr) (bvar : FVarId)
    (candidates : Array Atom) : MetaM (Array Atom) := do
  let atomsRef ← IO.mkRef (α := Array Atom) #[]
  let fnsRef ← IO.mkRef (α := Array Expr) #[]
  findAtomsAux body bvar candidates atomsRef fnsRef
  atomsRef.get

/-- Check for ambiguous atoms: same `fn` but different `value` across
    candidates. Throws an error if ambiguity is detected. -/
def checkAmbiguity (atoms : Array Atom) (allCandidates : Array Atom)
    (tacticName : String := "atom engine") : MetaM Unit := do
  for atom in atoms do
    for cand in allCandidates do
      if ← withNewMCtxDepth (isDefEq atom.fn cand.fn) then
        unless ← withNewMCtxDepth (isDefEq atom.value cand.value) do
          throwError m!"{tacticName}: ambiguous value for atom — \
            found hypotheses with values `{atom.value}` and \
            `{cand.value}` for the same function"

-- ══════════════════════════════════════════════════════════════
-- Product type / value / projection builders
-- ══════════════════════════════════════════════════════════════

/-- Right-associated product type from atom codomain types. -/
def buildProdType (atoms : Array Atom) : MetaM Expr := do
  if atoms.size = 1 then return atoms[0]!.codTy
  let mut ty := atoms.back!.codTy
  for i in List.range (atoms.size - 1) |>.reverse do
    ty ← mkAppM ``Prod #[atoms[i]!.codTy, ty]
  return ty

/-- Right-associated value point from atom values. -/
def buildValuePoint (atoms : Array Atom) : MetaM Expr := do
  if atoms.size = 1 then return atoms[0]!.value
  let mut pt := atoms.back!.value
  for i in List.range (atoms.size - 1) |>.reverse do
    pt ← mkAppM ``Prod.mk #[atoms[i]!.value, pt]
  return pt

/-- Projection `p.2.2...fst/snd` for atom `i` of `n`. -/
def buildProjection (p : Expr) (n i : Nat) : MetaM Expr := do
  if n = 1 then return p
  let mut e := p
  for _ in [:i] do
    e ← mkAppM ``Prod.snd #[e]
  if i < n - 1 then
    e ← mkAppM ``Prod.fst #[e]
  return e

-- ══════════════════════════════════════════════════════════════
-- Body abstraction
-- ══════════════════════════════════════════════════════════════

/-- Replace `fᵢ(bvar)` with `projᵢ(pVar)` in the body.
    `pVar` is a free variable of the product type. -/
partial def abstractBody (body : Expr) (bvar : FVarId)
    (pVar : Expr) (atoms : Array Atom) : MetaM Expr := do
  if !body.containsFVar bvar then return body
  let bvarExpr := Expr.fvar bvar
  for i in [:atoms.size] do
    let candApplied := mkApp atoms[i]!.fn bvarExpr
    if ← withNewMCtxDepth (isDefEq body candApplied) then
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

end AtomEngine
