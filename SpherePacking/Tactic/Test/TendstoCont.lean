module

public import SpherePacking.Tactic.TendstoCont
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

@[expose] public section

open Filter Topology

variable {f g k : ℝ → ℝ}

-- Constant function
example : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := by tendsto_cont

-- Single atom, identity
example (h : Tendsto f atTop (nhds 3)) :
    Tendsto (fun z => f z) atTop (nhds 3) := by tendsto_cont

-- Single atom, scalar multiply
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => 2 * f z) atTop (nhds 0) := by tendsto_cont

-- Two atoms, sum
example (h₁ : Tendsto f atTop (nhds 1)) (h₂ : Tendsto g atTop (nhds 2)) :
    Tendsto (fun z => f z + g z) atTop (nhds 3) := by tendsto_cont

-- Two atoms, polynomial
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1)) :
    Tendsto (fun z => f z ^ 2 + f z * g z + g z ^ 2) atTop (nhds 1) := by tendsto_cont

-- Three atoms, subtraction
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1))
    (h₃ : Tendsto k atTop (nhds 1)) :
    Tendsto (fun z => f z + g z - k z) atTop (nhds 0) := by tendsto_cont

-- Unused hypotheses in context don't interfere
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1))
    (_h_unrelated : Tendsto f atBot (nhds 5)) :
    Tendsto (fun z => f z * g z) atTop (nhds 0) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Issue 1: Non-last-argument matching (isDefEq-based)
-- ══════════════════════════════════════════════════════════════

-- Atom where bound variable is not the last argument
example (H : ℝ → ℝ → ℝ) (hH : Tendsto (fun z => H z 5) atTop (nhds 3)) :
    Tendsto (fun z => H z 5 + 1) atTop (nhds 4) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Issue 2: Symbolic target limits (ring fallback)
-- ══════════════════════════════════════════════════════════════

-- Commutativity: target says b + a, computed limit is a + b
example (h₁ : Tendsto f atTop (nhds 1)) (h₂ : Tendsto g atTop (nhds 2)) :
    Tendsto (fun z => g z + f z) atTop (nhds 3) := by tendsto_cont

-- Symbolic commutativity: target limit (b + a) differs from computed (a + b)
example {a b : ℝ} (h₁ : Tendsto f atTop (nhds a)) (h₂ : Tendsto g atTop (nhds b)) :
    Tendsto (fun z => f z + g z) atTop (nhds (b + a)) := by tendsto_cont

-- Symbolic associativity: target limit a + (b + c) vs computed order
example {a b c : ℝ} (h₁ : Tendsto f atTop (nhds a)) (h₂ : Tendsto g atTop (nhds b))
    (h₃ : Tendsto k atTop (nhds c)) :
    Tendsto (fun z => f z + g z + k z) atTop (nhds (a + (b + c))) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Issue 3: Duplicate (same limit) hypotheses succeed
-- ══════════════════════════════════════════════════════════════

-- Two hypotheses for same atom with same limit should not error
example (h₁ : Tendsto f atTop (nhds 0)) (_h₂ : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => f z + 1) atTop (nhds 1) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Issue 3: Ambiguity detection (different limits for same atom)
-- ══════════════════════════════════════════════════════════════

/-- error: tendsto_cont: ambiguous limit for atom — found hypotheses with limits `0` and `1` for the same function -/
#guard_msgs(error, drop info) in
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto f atTop (nhds 1)) :
    Tendsto (fun z => f z + 1) atTop (nhds 1) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Issue 4a: Zero atoms, no candidates for filter
-- ══════════════════════════════════════════════════════════════

/-- error: tendsto_cont: no `Tendsto` hypotheses found for filter `atTop` -/
#guard_msgs(error, drop info) in
example : Tendsto (fun z : ℝ => z + 1) atTop (nhds 0) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Issue 4b: Zero atoms, candidates exist but none matched
-- ══════════════════════════════════════════════════════════════

/-- error: tendsto_cont: body references the bound variable but no candidate matched.
Available candidates: [f] -/
#guard_msgs(error, drop info) in
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => g z + 1) atTop (nhds 0) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Non-polynomial continuous functions (sin, exp)
-- ══════════════════════════════════════════════════════════════

-- sin of a convergent function
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => Real.sin (f z)) atTop (nhds 0) := by tendsto_cont

-- exp of a convergent function
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => Real.exp (f z)) atTop (nhds 1) := by tendsto_cont

-- Mixed: polynomial + sin
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1)) :
    Tendsto (fun z => f z ^ 2 + Real.sin (g z)) atTop (nhds (Real.sin 1)) := by tendsto_cont

-- exp * sin composition
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => Real.exp (f z) * Real.sin (f z)) atTop (nhds 0) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Complex numbers
-- ══════════════════════════════════════════════════════════════

section Complex
open Complex

variable {fc gc : ℝ → ℂ}

-- Complex: sum
example (h₁ : Tendsto fc atTop (nhds 1)) (h₂ : Tendsto gc atTop (nhds I)) :
    Tendsto (fun z => fc z + gc z) atTop (nhds (1 + I)) := by tendsto_cont

-- Complex: polynomial
example (h₁ : Tendsto fc atTop (nhds 0)) (h₂ : Tendsto gc atTop (nhds 1)) :
    Tendsto (fun z => fc z ^ 2 + fc z * gc z + gc z ^ 2) atTop (nhds 1) := by tendsto_cont

-- Complex: exp
example (h : Tendsto fc atTop (nhds 0)) :
    Tendsto (fun z => Complex.exp (fc z)) atTop (nhds 1) := by tendsto_cont

-- Complex.re composition (pattern from PR #307: continuous_re.tendsto.comp)
example (h : Tendsto fc atTop (nhds 1)) :
    Tendsto (fun z => (fc z).re) atTop (nhds 1) := by tendsto_cont

-- Complex.im composition
example (h : Tendsto fc atTop (nhds I)) :
    Tendsto (fun z => (fc z).im) atTop (nhds 1) := by tendsto_cont

end Complex

-- ══════════════════════════════════════════════════════════════
-- Goal function behind a reducible definition (whnfR needed)
-- ══════════════════════════════════════════════════════════════

-- When the goal function is a reducible definition (abbrev), tendsto_cont
-- should reduce it via whnfR to find the lambda (no `change` or `show` needed).
noncomputable abbrev myExpr (f g : ℝ → ℝ) : ℝ → ℝ := fun z => f z ^ 2 + g z

example (hf : Tendsto f atTop (nhds 1)) (hg : Tendsto g atTop (nhds 2)) :
    Tendsto (myExpr f g) atTop (nhds 3) := by tendsto_cont

noncomputable abbrev myExprMul (f g : ℝ → ℝ) : ℝ → ℝ := fun z => f z * g z

example (hf : Tendsto f atTop (nhds 2)) (hg : Tendsto g atTop (nhds 3)) :
    Tendsto (myExprMul f g) atTop (nhds 6) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- General topological ring
-- ══════════════════════════════════════════════════════════════

section GeneralRing

-- Sum over a general topological ring
example {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    {α : Type*} {l : Filter α}
    {f g : α → R} {a b : R}
    (h₁ : Tendsto f l (nhds a)) (h₂ : Tendsto g l (nhds b)) :
    Tendsto (fun z => f z + g z) l (nhds (a + b)) := by tendsto_cont

-- Product over a general topological ring
example {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    {α : Type*} {l : Filter α}
    {f g : α → R} {a b : R}
    (h₁ : Tendsto f l (nhds a)) (h₂ : Tendsto g l (nhds b)) :
    Tendsto (fun z => f z * g z) l (nhds (a * b)) := by tendsto_cont

-- Polynomial over a commutative topological ring (ring fallback)
example {R : Type*} [TopologicalSpace R] [CommRing R] [IsTopologicalRing R]
    {α : Type*} {l : Filter α}
    {f g : α → R} {a b : R}
    (h₁ : Tendsto f l (nhds a)) (h₂ : Tendsto g l (nhds b)) :
    Tendsto (fun z => f z * g z + g z * f z) l (nhds (2 * a * b)) := by tendsto_cont

end GeneralRing

-- ══════════════════════════════════════════════════════════════
-- Non-atTop filters (nhds 0, etc.)
-- ══════════════════════════════════════════════════════════════

-- Limit at nhds 0 (not atTop/atBot)
example (h : Tendsto f (nhds 0) (nhds 1)) :
    Tendsto (fun x => 2 * f x) (nhds 0) (nhds 2) := by tendsto_cont

-- Two hypotheses with different filters: picks the right one
example (_h₁ : Tendsto f (nhds 0) (nhds 1)) (h₂ : Tendsto f atTop (nhds 0)) :
    Tendsto (fun x => 2 * f x) atTop (nhds 0) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Composition: f(g(x)) as a single atom
-- ══════════════════════════════════════════════════════════════

-- Hypothesis about f(g(x)) treated as one atom
example (h : Tendsto (fun x => f (g x)) (nhds 0) (nhds 1)) :
    Tendsto (fun x => 2 * f (g x)) (nhds 0) (nhds 2) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Composition via continuity: g(f(x)) where g is continuous
-- ══════════════════════════════════════════════════════════════

-- g continuous + f → 1 at 0 gives g(f(x)) → g(1) at 0
example (hf : Tendsto f (nhds 0) (nhds 1)) (hg : Continuous g) :
    Tendsto (fun x => g (f x)) (nhds 0) (nhds (g 1)) := by tendsto_cont

-- Without continuity hypothesis, fun_prop can't prove ContinuousAt g
/--
error: tendsto_cont: `fun_prop` failed:
`fun_prop` was unable to prove `ContinuousAt (fun p ↦ g p) 1`

Issues:
  No theorems found for `g` in order to prove `ContinuousAt (fun p ↦ g p) 1`
goal: ContinuousAt (fun p ↦ g p) 1
-/
#guard_msgs(error, drop info) in
example (hf : Tendsto f (nhds 0) (nhds 1)) :
    Tendsto (fun x => g (f x)) (nhds 0) (nhds (g 1)) := by tendsto_cont

-- But known continuous functions (Real.sin, etc.) work fine via fun_prop
example (hf : Tendsto f (nhds 0) (nhds 1)) :
    Tendsto (fun x => Real.sin (f x)) (nhds 0) (nhds (Real.sin 1)) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Inline argument syntax: tendsto_cont [h₁, h₂]
-- ══════════════════════════════════════════════════════════════

section InlineArgs

private def inlineFn : ℝ → ℝ := fun _ => 3

private theorem inlineFn_tendsto : Tendsto inlineFn atTop (nhds 3) := by
  simpa [inlineFn] using tendsto_const_nhds

private def inlineFn₂ : ℝ → ℝ := fun _ => 2

private theorem inlineFn₂_tendsto : Tendsto inlineFn₂ atTop (nhds 2) := by
  simpa [inlineFn₂] using tendsto_const_nhds

-- Without inline arg, no candidate exists
/-- error: tendsto_cont: no `Tendsto` hypotheses found for filter `atTop` -/
#guard_msgs(error, drop info) in
example : Tendsto (fun z => inlineFn z + 1) atTop (nhds 4) := by
  tendsto_cont

-- Single inline argument makes it work
example : Tendsto (fun z => inlineFn z + 1) atTop (nhds 4) := by
  tendsto_cont [inlineFn_tendsto]

-- Multiple inline arguments
example : Tendsto (fun z => inlineFn z + inlineFn₂ z) atTop (nhds 5) := by
  tendsto_cont [inlineFn_tendsto, inlineFn₂_tendsto]

-- Inline arg shadows conflicting local hypothesis — no ambiguity error
example (_h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto f atTop (nhds 1)) :
    Tendsto (fun z => f z + 1) atTop (nhds 2) := by tendsto_cont [h₂]

end InlineArgs

-- ══════════════════════════════════════════════════════════════
-- @[tendsto_cont] attribute
-- ══════════════════════════════════════════════════════════════

section AttrRegistration

private def attrFn : ℝ → ℝ := fun _ => 0

private theorem attrFn_tendsto : Tendsto attrFn (nhds 0) (nhds 0) := by
  simpa [attrFn] using tendsto_const_nhds

-- Before registration: fails
/-- error: tendsto_cont: no `Tendsto` hypotheses found for filter `𝓝 0` -/
#guard_msgs(error, drop info) in
example : Tendsto (fun z => attrFn z + 1) (nhds 0) (nhds 1) := by
  tendsto_cont

-- Register via attribute
attribute [tendsto_cont] attrFn_tendsto

-- After registration: works
example : Tendsto (fun z => attrFn z + 1) (nhds 0) (nhds 1) := by
  tendsto_cont

end AttrRegistration

-- ══════════════════════════════════════════════════════════════
-- Negative tests: inline arguments
-- ══════════════════════════════════════════════════════════════

-- Wrong-filter inline arg is silently ignored → no candidates
/-- error: tendsto_cont: no `Tendsto` hypotheses found for filter `atTop` -/
#guard_msgs(error, drop info) in
example (h : Tendsto f (nhds 0) (nhds 1)) :
    Tendsto (fun z => f z + 1) atTop (nhds 2) := by tendsto_cont [h]

-- Non-Tendsto inline arg is silently ignored → no candidates
/-- error: tendsto_cont: no `Tendsto` hypotheses found for filter `atTop` -/
#guard_msgs(error, drop info) in
example (h : (1 : ℝ) + 1 = 2) :
    Tendsto (fun z : ℝ => z + 1) atTop (nhds 2) := by tendsto_cont [h]

-- Two inline args with same fn, different limits → ambiguity error
/-- error: tendsto_cont: ambiguous limit for atom — found hypotheses with limits `0` and `1` for the same function -/
#guard_msgs(error, drop info) in
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto f atTop (nhds 1)) :
    Tendsto (fun z => f z + 1) atTop (nhds 1) := by tendsto_cont [h₁, h₂]

-- ══════════════════════════════════════════════════════════════
-- Negative tests: attribute type validation
-- ══════════════════════════════════════════════════════════════

-- Non-Tendsto declaration rejected at registration time
/-- error: `@[tendsto_cont]`: declaration type must be `Tendsto f l (nhds a)`, got head `True` -/
#guard_msgs(error, drop info) in
@[tendsto_cont]
theorem notATendstoTheorem : True := trivial

-- Parameterized declaration rejected (only closed lemmas allowed)
/-- error: `@[tendsto_cont]`: declaration must be a closed `Tendsto` lemma with no parameters; got a declaration with binders -/
#guard_msgs(error, drop info) in
@[tendsto_cont]
theorem paramTendsto (_h : True) : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0) :=
  tendsto_const_nhds

-- Tendsto with wrong target filter rejected at registration time
/-- error: `@[tendsto_cont]`: target filter must be `nhds _`, got `Filter.atTop` -/
#guard_msgs(error, drop info) in
@[tendsto_cont]
theorem wrongTargetFilter : Tendsto (fun z : ℝ => z) atTop atTop := tendsto_id

-- ══════════════════════════════════════════════════════════════
-- Negative tests: attribute scope rejection
-- ══════════════════════════════════════════════════════════════

theorem testScopeRejection : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0) :=
  tendsto_const_nhds

/-- error: `@[tendsto_cont]` only supports global scope (not `local` or `scoped`) -/
#guard_msgs(error, drop info) in
attribute [local tendsto_cont] testScopeRejection

namespace TestScopeRejection
/-- error: `@[tendsto_cont]` only supports global scope (not `local` or `scoped`) -/
#guard_msgs(error, drop info) in
attribute [scoped tendsto_cont] testScopeRejection
end TestScopeRejection

-- ══════════════════════════════════════════════════════════════
-- Negative test: attribute-level ambiguity (same fn, different limits)
-- ══════════════════════════════════════════════════════════════

-- Use Bool with the indiscrete topology (⊤) so that nhds = ⊤ and
-- Tendsto holds trivially for any limit — no sorry needed.
section AttrAmbiguity

open Filter Topology

local instance : TopologicalSpace Bool := ⊤

private def bad : ℝ → Bool := fun _ => false

@[tendsto_cont]
private theorem bad_tendsto_false : Tendsto bad atTop (nhds false) := by
  rw [nhds_top]
  exact tendsto_top

@[tendsto_cont]
private theorem bad_tendsto_true : Tendsto bad atTop (nhds true) := by
  rw [nhds_top]
  exact tendsto_top

-- Same-bucket ambiguity: two attribute lemmas with same fn, different limits
/-- error: tendsto_cont: ambiguous limit for atom — found hypotheses with limits `false` and `true` for the same function -/
#guard_msgs(error, drop info) in
example : Tendsto (fun z => bad z) atTop (nhds false) := by
  tendsto_cont

end AttrAmbiguity

-- ══════════════════════════════════════════════════════════════
-- Cross-bucket shadowing: attribute vs local / attribute vs inline
-- ══════════════════════════════════════════════════════════════

-- Sierpinski-style topology on Bool via mkOfNhds:
-- nhds false = ⊤ (every set is a neighborhood of false)
-- nhds true = pure true (only sets containing true are neighborhoods)
-- These are genuinely distinguishable, so reconcileLimits cannot paper
-- over a wrong limit choice. Both Tendsto facts are provable because
-- good always returns true.
section AttrShadowing

open Filter Topology

local instance : TopologicalSpace Bool :=
  TopologicalSpace.mkOfNhds (Function.update pure false ⊤)

private lemma nhds_eq : ∀ b : Bool,
    @nhds Bool (TopologicalSpace.mkOfNhds (Function.update pure false ⊤)) b =
    Function.update pure false ⊤ b :=
  TopologicalSpace.nhds_mkOfNhds_single le_top

private def good : ℝ → Bool := fun _ => true

@[tendsto_cont]
private theorem good_attr_false : Tendsto good atTop (nhds false) := by
  rw [nhds_eq]; simp [Function.update_self]

private theorem good_inline_true : Tendsto good atTop (nhds true) := by
  rw [nhds_eq]; simp [good]

-- Local context shadows attribute registry.
-- Load-bearing: if the attributed false limit were used instead,
-- nhds false = ⊤ ≠ pure true = nhds true, so reconcileLimits fails.
example (h : Tendsto good atTop (nhds true)) :
    Tendsto (fun z => good z) atTop (nhds true) := by tendsto_cont

-- Inline arg shadows attribute registry.
example : Tendsto (fun z => good z) atTop (nhds true) := by
  tendsto_cont [good_inline_true]

end AttrShadowing
