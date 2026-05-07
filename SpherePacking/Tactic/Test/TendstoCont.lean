module

public import SpherePacking.Tactic.TendstoCont
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Tests for the `tendsto_cont` tactic

This file collects minimal-working examples exercising the `tendsto_cont` tactic defined in
`SpherePacking/Tactic/TendstoCont.lean`. It is kept separate so the tactic definition remains
test-free.
-/

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

/-! ### Issue 1: Non-last-argument matching (isDefEq-based) -/

-- Atom where bound variable is not the last argument
example (H : ℝ → ℝ → ℝ) (hH : Tendsto (fun z => H z 5) atTop (nhds 3)) :
    Tendsto (fun z => H z 5 + 1) atTop (nhds 4) := by tendsto_cont

/-! ### Issue 2: Symbolic target limits (ring fallback) -/

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

/-! ### Issue 3: Duplicate (same limit) hypotheses succeed -/

-- Two hypotheses for same atom with same limit should not error
example (h₁ : Tendsto f atTop (nhds 0)) (_h₂ : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => f z + 1) atTop (nhds 1) := by tendsto_cont

/-! ### Issue 3: Ambiguity detection (different limits for same atom) -/

/-- error: tendsto_cont: ambiguous limit for atom — found hypotheses with limits `0` and `1` for the same function -/
#guard_msgs(error, drop info) in
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto f atTop (nhds 1)) :
    Tendsto (fun z => f z + 1) atTop (nhds 1) := by tendsto_cont

/-! ### Issue 4a: Zero atoms, no candidates for filter -/

/-- error: tendsto_cont: no `Tendsto` hypotheses found for filter `atTop` -/
#guard_msgs(error, drop info) in
example : Tendsto (fun z : ℝ => z + 1) atTop (nhds 0) := by tendsto_cont

/-! ### Issue 4b: Zero atoms, candidates exist but none matched -/

/-- error: tendsto_cont: body references the bound variable but no candidate matched.
Available candidates: [f] -/
#guard_msgs(error, drop info) in
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => g z + 1) atTop (nhds 0) := by tendsto_cont

/-! ### Non-polynomial continuous functions (sin, exp) -/

example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => Real.sin (f z)) atTop (nhds 0) := by tendsto_cont

example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => Real.exp (f z)) atTop (nhds 1) := by tendsto_cont

example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1)) :
    Tendsto (fun z => f z ^ 2 + Real.sin (g z)) atTop (nhds (Real.sin 1)) := by tendsto_cont

example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => Real.exp (f z) * Real.sin (f z)) atTop (nhds 0) := by tendsto_cont

/-! ### Complex numbers -/

section Complex
open Complex

variable {fc gc : ℝ → ℂ}

example (h₁ : Tendsto fc atTop (nhds 1)) (h₂ : Tendsto gc atTop (nhds I)) :
    Tendsto (fun z => fc z + gc z) atTop (nhds (1 + I)) := by tendsto_cont

example (h₁ : Tendsto fc atTop (nhds 0)) (h₂ : Tendsto gc atTop (nhds 1)) :
    Tendsto (fun z => fc z ^ 2 + fc z * gc z + gc z ^ 2) atTop (nhds 1) := by tendsto_cont

example (h : Tendsto fc atTop (nhds 0)) :
    Tendsto (fun z => Complex.exp (fc z)) atTop (nhds 1) := by tendsto_cont

example (h : Tendsto fc atTop (nhds 1)) :
    Tendsto (fun z => (fc z).re) atTop (nhds 1) := by tendsto_cont

example (h : Tendsto fc atTop (nhds I)) :
    Tendsto (fun z => (fc z).im) atTop (nhds 1) := by tendsto_cont

end Complex

/-! ### Goal function behind a reducible definition (whnfR needed) -/

noncomputable abbrev myExpr (f g : ℝ → ℝ) : ℝ → ℝ := fun z => f z ^ 2 + g z

example (hf : Tendsto f atTop (nhds 1)) (hg : Tendsto g atTop (nhds 2)) :
    Tendsto (myExpr f g) atTop (nhds 3) := by tendsto_cont

noncomputable abbrev myExprMul (f g : ℝ → ℝ) : ℝ → ℝ := fun z => f z * g z

example (hf : Tendsto f atTop (nhds 2)) (hg : Tendsto g atTop (nhds 3)) :
    Tendsto (myExprMul f g) atTop (nhds 6) := by tendsto_cont

/-! ### General topological ring -/

section GeneralRing

example {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    {α : Type*} {l : Filter α} {f g : α → R} {a b : R}
    (h₁ : Tendsto f l (nhds a)) (h₂ : Tendsto g l (nhds b)) :
    Tendsto (fun z => f z + g z) l (nhds (a + b)) := by tendsto_cont

example {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    {α : Type*} {l : Filter α} {f g : α → R} {a b : R}
    (h₁ : Tendsto f l (nhds a)) (h₂ : Tendsto g l (nhds b)) :
    Tendsto (fun z => f z * g z) l (nhds (a * b)) := by tendsto_cont

example {R : Type*} [TopologicalSpace R] [CommRing R] [IsTopologicalRing R]
    {α : Type*} {l : Filter α} {f g : α → R} {a b : R}
    (h₁ : Tendsto f l (nhds a)) (h₂ : Tendsto g l (nhds b)) :
    Tendsto (fun z => f z * g z + g z * f z) l (nhds (2 * a * b)) := by tendsto_cont

end GeneralRing

/-! ### Non-atTop filters (nhds 0, etc.) -/

example (h : Tendsto f (nhds 0) (nhds 1)) :
    Tendsto (fun x => 2 * f x) (nhds 0) (nhds 2) := by tendsto_cont

example (_h₁ : Tendsto f (nhds 0) (nhds 1)) (h₂ : Tendsto f atTop (nhds 0)) :
    Tendsto (fun x => 2 * f x) atTop (nhds 0) := by tendsto_cont

/-! ### Composition: f(g(x)) as a single atom -/

example (h : Tendsto (fun x => f (g x)) (nhds 0) (nhds 1)) :
    Tendsto (fun x => 2 * f (g x)) (nhds 0) (nhds 2) := by tendsto_cont

/-! ### Composition via continuity: g(f(x)) where g is continuous -/

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

example (hf : Tendsto f (nhds 0) (nhds 1)) :
    Tendsto (fun x => Real.sin (f x)) (nhds 0) (nhds (Real.sin 1)) := by tendsto_cont
