/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5338a3ee-42c0-4e72-b853-9e9cb4bb96e1

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- noncomputable def SchwartzMap.translation {d : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (a : EuclideanSpace ℝ (Fin d)) : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)

- lemma SpherePacking.centers_isSeparated (S : SpherePacking d) :
    IsSeparated (ENNReal.ofReal S.separation) S.centers

- lemma hsummable₁ (y : EuclideanSpace ℝ (Fin d))
    (hf : Summable fun (x : P.centers) ↦ f x) :
    Summable fun (b : P.centers) ↦ (f (b.val - y)).re

- lemma hsummable₄ (P : PeriodicSpherePacking d) (hf : Summable (fun (x : P.centers) => f x))
    (x y : EuclideanSpace ℝ (Fin d)) :
    Summable fun (ℓ : ↥P.lattice) ↦ f (x - y + ℓ.val)

- variable (P) in
noncomputable def eq₁ (y : EuclideanSpace ℝ (Fin d)) : ↥P.lattice ≃
    ↑(y +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d))))

The following was negated by Aristotle:

- variable (P D) in
lemma hunion [Fintype ↑(P.centers ∩ D)] : P.centers =
    ⋃ (x ∈ (P.centers ∩ D).toFinset), (x +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d))))

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```



At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.Analysis.RCLike.Inner


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

open scoped FourierTransform ENNReal SchwartzMap InnerProductSpace

open Metric BigOperators Pointwise Filter MeasureTheory Complex
  Real ZSpan Bornology Summable Module LinearMap SchwartzMap

variable {d : ℕ}

--Let `f : ℝᵈ → ℂ` be a Schwartz function.
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)

-- let `f` to be real-valued:
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))

-- let `𝓕 f` be real-valued:
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))

-- moreover, impose the Cohn-Elkies conditions:
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)

variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)

structure SpherePacking (d : ℕ) where
  centers : Set (EuclideanSpace ℝ (Fin d))
  separation : ℝ
  separation_pos : 0 < separation := by positivity
  centers_dist : Pairwise (separation < dist · · : centers → centers → Prop)

structure PeriodicSpherePacking (d : ℕ) extends SpherePacking d where
  lattice : Submodule ℤ (EuclideanSpace ℝ (Fin d))
  lattice_action : ∀ ⦃x y⦄, x ∈ lattice → y ∈ centers → x + y ∈ centers
  lattice_discrete : DiscreteTopology lattice := by infer_instance
  lattice_isZLattice : IsZLattice ℝ lattice := by infer_instance

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]

variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : Bornology.IsBounded D)

variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)

theorem _root_.Continuous.re {α 𝕜 : Type*} [TopologicalSpace α] [RCLike 𝕜] {f : α → 𝕜}
    (hf : Continuous f) : Continuous (fun x ↦ RCLike.re (f x)) :=
  RCLike.continuous_re.comp hf

theorem _root_.Continuous.im {α 𝕜 : Type*} [TopologicalSpace α] [RCLike 𝕜] {f : α → 𝕜}
    (hf : Continuous f) : Continuous (fun x ↦ RCLike.im (f x)) :=
  RCLike.continuous_im.comp hf

theorem _root_.Continuous.ofReal {α 𝕜 : Type*} [TopologicalSpace α] [RCLike 𝕜]
    {f : α → ℝ} (hf : Continuous f) : Continuous (fun (x : α) => (f x : 𝕜)) :=
  RCLike.continuous_ofReal.comp hf

theorem _root_.LipschitzWith.norm {α 𝕜 : Type*} [PseudoEMetricSpace α] [RCLike 𝕜]
    {K : NNReal} {f : α → 𝕜} (hf : LipschitzWith K f) :
    LipschitzWith K (fun x ↦ ‖f x‖) := by
  simpa using lipschitzWith_one_norm.comp hf

theorem _root_.LipschitzWith.re {α 𝕜 : Type*} [PseudoEMetricSpace α] [RCLike 𝕜]
    {K : NNReal} {f : α → 𝕜} (hf : LipschitzWith K f) :
    LipschitzWith K (fun x ↦ RCLike.re (f x)) := by
  simpa using RCLike.lipschitzWith_re.comp hf

theorem _root_.LipschitzWith.im {α 𝕜 : Type*} [PseudoEMetricSpace α] [RCLike 𝕜]
    {K : NNReal} {f : α → 𝕜} (hf : LipschitzWith K f) :
    LipschitzWith K (fun x ↦ RCLike.im (f x)) := by
  simpa using RCLike.lipschitzWith_im.comp hf

theorem _root_.LipschitzWith.ofReal {α 𝕜 : Type*} [PseudoEMetricSpace α] [RCLike 𝕜]
    {K : NNReal} {f : α → ℝ} (hf : LipschitzWith K f) :
    LipschitzWith K (fun (x : α) => (f x : 𝕜)) := by
  simpa using RCLike.lipschitzWith_ofReal.comp hf

open RCLike

theorem _root_.Memℓp.re {α : Type*} {𝕜 : α → Type*} {p : ENNReal} [(i : α) → RCLike (𝕜 i)]
    {f : ∀ i, 𝕜 i} (hf : Memℓp f p) :
    Memℓp (fun x ↦ re (f x)) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · refine memℓp_zero <| hf.finite_dsupport.subset fun i hi => ?_
    contrapose! hi
    simp only [Set.mem_setOf_eq, Decidable.not_not] at hi ⊢
    simp [hi]
  · exact memℓp_infty (BddAbove.range_mono _ (fun x ↦ abs_re_le_norm _) hf.bddAbove)
  · refine memℓp_gen <| Summable.of_nonneg_of_le ?_ ?_ (hf.summable hp)
    · exact fun x ↦ rpow_nonneg (norm_nonneg _) _
    · exact fun x ↦ by gcongr; exact abs_re_le_norm (f x)

theorem _root_.Memℓp.im {α : Type*} {𝕜 : α → Type*} {p : ENNReal} [(i : α) → RCLike (𝕜 i)]
    {f : ∀ i, 𝕜 i} (hf : Memℓp f p) : Memℓp (fun x ↦ im (f x)) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · refine memℓp_zero <| hf.finite_dsupport.subset fun i hi => ?_
    contrapose! hi
    simp only [Set.mem_setOf_eq, Decidable.not_not] at hi ⊢
    simp [hi]
  · exact memℓp_infty (BddAbove.range_mono _ (fun x ↦ abs_im_le_norm _) hf.bddAbove)
  · refine memℓp_gen <| Summable.of_nonneg_of_le ?_ ?_ (hf.summable hp)
    · exact fun x ↦ rpow_nonneg (norm_nonneg _) _
    · exact fun x ↦ by gcongr; exact abs_im_le_norm (f x)

theorem _root_.Memℓp.ofReal {α : Type*} {𝕜 : α → Type*} {p : ENNReal}
    [(i : α) → RCLike (𝕜 i)] {f : α → ℝ} (hf : Memℓp f p) :
    Memℓp (fun x ↦ (f x : 𝕜 x)) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · exact memℓp_zero <| hf.finite_dsupport.subset fun i => by simp
  · exact memℓp_infty (by simpa [BddAbove])
  · exact memℓp_gen (by simpa using hf.summable hp)

theorem memℓp_one_iff_summable {α : Type*} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : α → E} :
    Memℓp f 1 ↔ Summable f := by
  simpa [Memℓp] using summable_norm_iff

theorem _root_.Summable.re {α 𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜} (hf : Summable f) :
    Summable (fun x ↦ RCLike.re (f x)) := by
  rw [← memℓp_one_iff_summable] at hf ⊢
  exact hf.re

theorem _root_.Summable.im {α 𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜} (hf : Summable f) :
    Summable (fun x ↦ RCLike.im (f x)) := by
  rw [← memℓp_one_iff_summable] at hf ⊢
  exact hf.im

lemma ZLattice.isSeparated (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L]
    [hL : IsZLattice ℝ L] : ∃ ε > 0, IsSeparated ε (L : Set (EuclideanSpace ℝ (Fin d))) := by
  admit

lemma SchwartzMap.summableOn_iff {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : 𝓢(E, V)) (X : Set E) :
    Summable (fun (x : X) => f x) ↔ ∃ ε > 0, IsSeparated ε X := by
  admit

alias ⟨_, SchwartzMap.summableOn⟩ := SchwartzMap.summableOn_iff






lemma SpherePacking.centers_isSeparated (S : SpherePacking d) :
    IsSeparated (ENNReal.ofReal S.separation) S.centers := by
  -- By definition of `SpherePacking`, the centers are pairwise separated by a positive distance.
  have h_separated : ∀ x y : S.centers, x ≠ y →
    dist (x : EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin d)) > S.separation := by
    -- By definition of `SpherePacking`, the centers are pairwise separated by a positive
    -- distance. Therefore, for any two distinct centers `x` and `y`, we have `dist x y > S.
    -- separation`.
    intros x y hxy
    apply S.centers_dist hxy;
  -- By definition of `IsSeparated`, we need to show that for any two distinct points in
  -- `S.centers`, their distance is greater than `S.separation`. This follows directly
  -- from `h_separated`.
  intros x hx y hy hxy;
  rw [ edist_dist ] ; aesop;

lemma hsummable₁ (y : EuclideanSpace ℝ (Fin d)) :
    Summable fun (b : P.centers) ↦ (f (b.val - y)).re := by
  -- Since translation by y maps the centers of P to another set of points that are still
  -- separated by at least 1 (because the distance between any two points in P.centers - y
  -- is the same as the distance between the corresponding points in P.centers), the
  -- summability of the translated function should follow from the summability of f over
  -- the original set.
  have h_translated_summable : Summable (fun x : P.centers => f (x - y)) := by
    -- Since $P.centers$ is a separated set and $f$ is a Schwartz function, the series
    -- $\sum_{x \in P.centers} f(x - y)$ converges absolutely.
    have h_translated_summable : IsSeparated (ENNReal.ofReal P.separation) (P.centers - {y}) := by
      have h_translated_summable : IsSeparated (ENNReal.ofReal P.separation) P.centers := by
        exact SpherePacking.centers_isSeparated P.toSpherePacking
      generalize_proofs at *; (
      intro x hx y hy; aesop;);
    have h_translated_summable :
      Summable (fun x : (P.centers - {y} : Set (EuclideanSpace ℝ (Fin d))) => f x) := by
      -- Apply the SchwartzMap.summableOn_iff lemma with the separated set P.centers - {y}
      -- and the positive ε from h_translated_summable.
      apply (SchwartzMap.summableOn_iff f (P.centers - {y})).mpr;
      -- Since $P.separation$ is positive, we can take $\epsilon = P.separation$.
      use ENNReal.ofReal P.separation;
      exact ⟨ ENNReal.ofReal_pos.mpr P.separation_pos, h_translated_summable ⟩;
    convert h_translated_summable.comp_injective
      ( show Function.Injective ( fun x : P.centers =>
        ⟨ x - y, by aesop ⟩ : P.centers →
          ( P.centers - { y } : Set ( EuclideanSpace ℝ ( Fin d ) ) ) ) from
            fun x y hxy => by aesop ) using 1;
  convert h_translated_summable.re using 1

lemma hsummable₂ : Summable (Function.uncurry fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice))
    (x : ↑(P.centers ∩ D)) ↦
    ∑' (x_1 : ↑(P.centers ∩ D)), (𝓕 f m).re * exp (2 * π * I *
    ⟪(x.val).ofLp - (x_1.val).ofLp, (m.val).ofLp⟫_[ℝ])) := by
  simp [Function.uncurry_def]
  admit

lemma hsummable₃ : Summable (fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) =>
      (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪x.val, (m.val).ofLp⟫_[ℝ])) ^ 2)) := by
  admit

lemma hsummable₄ (P : PeriodicSpherePacking d)
    (x y : EuclideanSpace ℝ (Fin d)) :
    Summable fun (ℓ : ↥P.lattice) ↦ f (x - y + ℓ.val) := by
  have := f.summableOn ( Set.range ( fun ℓ : P.lattice => ( ℓ : EuclideanSpace ℝ ( Fin d ) ) + ( x - y ) ) ) (by
  have h_separated : ∃ ε > 0, IsSeparated ε (P.lattice : Set (EuclideanSpace ℝ (Fin d))) := by
    convert ZLattice.isSeparated P.lattice;
    exact P.lattice_discrete;
    exact P.lattice_isZLattice;
  -- Since addition by a constant preserves the separation property, the range of the function ℓ ↦ ℓ + (x - y) is also separated.
  obtain ⟨ε, hε_pos, hε_sep⟩ := h_separated;
  use ε, hε_pos;
  intro x hx y hy hxy;
  aesop);
  convert this.comp_injective ( show Function.Injective ( fun ℓ : P.lattice => ⟨ ( ℓ : EuclideanSpace ℝ ( Fin d ) ) + ( x - y ), Set.mem_range_self ℓ ⟩ ) from fun a b h => by simpa using congr_arg Subtype.val h ) using 1;
  exact funext fun _ => by simp +decide [ add_comm ] ;

lemma hsummable₅ : Summable
    fun (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) ↦
    (((𝓕 f) ↑m).re : ℂ) * ((Complex.normSq (∑' (x : ↑(P.centers ∩ D)),
    cexp (2 * (↑π * (I * ⟪x.val.ofLp, (m.val).ofLp⟫_[ℝ]))))) : ℂ) := by
  admit

lemma hsummable₆ (i : ↑(P.centers ∩ D)) [Fintype ↑(P.centers ∩ D)] : Summable fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) ↦
    ∑ (x_1 : ↑(P.centers ∩ D)), ↑((𝓕 f) ↑m).re *
    cexp (2 * ↑π * I * ⟪(i.val).ofLp - (x_1.val).ofLp, (m.val).ofLp⟫_[ℝ]) := by
  admit

lemma hsummable₇ {i : ↑(P.centers ∩ D)} (x_1 : ↑(P.centers ∩ D))
    [Fintype ↑(P.centers ∩ D)] : Summable fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) ↦
    ↑((𝓕 f) ↑m).re *
    cexp (2 * ↑π * I * ⟪(i.val).ofLp - (x_1.val).ofLp, (m.val).ofLp⟫_[ℝ]) := by
  admit

variable (P) in
noncomputable def eq₁ (y : EuclideanSpace ℝ (Fin d)) : ↥P.lattice ≃
    ↑(y +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))) :=
  {
    toFun := fun x ↦ ⟨y + x, by
      -- Since $x$ is in the lattice, adding $y$ to $x$ should still be in the lattice
      --shifted by $y$.
      simp [Set.mem_vadd_set]⟩,
    invFun := fun z ↦ ⟨z - y, by
      -- Since $z$ is in the set $y +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))$, there
      -- exists some $ℓ \in P.lattice$ such that $z = y + ℓ$.
      obtain ⟨ℓ, hℓ⟩ : ∃ ℓ ∈ P.lattice, z = y + ℓ := by
        -- By definition of $y +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))$, if $z \in
        -- y +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))$, then there exists some $ℓ
        -- \in P.lattice$ such that $z = y + ℓ$.
        obtain ⟨ℓ, hℓ⟩ := z.2;
        use ℓ;
        aesop;
      -- Substitute $z = y + ℓ$ into the expression $(z - y)$ and simplify.
      rw [hℓ.right]
      simp [hℓ.left]⟩,
    left_inv := by simp [Function.LeftInverse]
    right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  }



/-
Helper lemma: Any center point can be shifted by a lattice vector to land in the fundamental domain D.
-/
lemma hunion_lemma_1
  (P : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))
  (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
  (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ P.centers) :
    ∃ y ∈ P.centers ∩ D, ∃ ℓ ∈ P.lattice, x = y + ℓ := by
      obtain ⟨ g, hg₁, hg₂ ⟩ := hD_unique_covers x;
      refine' ⟨ g +ᵥ x, ⟨ _, _ ⟩, -g, _, _ ⟩ <;> simp_all +decide;
      · convert P.lattice_action g.2 hx using 1;
      · ext ; simp +decide [ add_comm ];
        exact?


/-
The corrected version of hunion, assuming D is a fundamental domain.
-/
lemma hunion_corrected (P : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    [Fintype ↑(P.centers ∩ D)] :
    P.centers =
      ⋃ (x ∈ (P.centers ∩ D).toFinset), (x +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))) := by
      -- Let's first show that the union of the lattice translates of the fundamental
      -- domain covers all centers.
      apply Set.ext
      intro x
      simp [Set.mem_iUnion, Set.mem_vadd_set];
      constructor;
      · intro hx
        obtain ⟨y, hyD, hy⟩ := hunion_lemma_1 P D hD_unique_covers x hx
        use y
        aesop;
      · rintro ⟨ y, ⟨ hy₁, hy₂ ⟩, z, hz₁, rfl ⟩;
        exact P.lattice_action hz₁ hy₁ |> fun h => by simpa [ add_comm ] using h;

lemma pairwise_disj [Fintype ↑(P.centers ∩ D)] :
    ((P.centers ∩ D).toFinset : Set (EuclideanSpace ℝ (Fin d))).Pairwise
    (Function.onFun Disjoint fun x ↦ x +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))) := by
  admit
