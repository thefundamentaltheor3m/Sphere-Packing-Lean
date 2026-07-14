module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

@[expose] public section

/-
Probably put this at Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean
-/

open UpperHalfPlane Filter Topology

lemma Filter.eventually_atImInfty {p : ℍ → Prop} :
    (∀ᶠ x in atImInfty, p x) ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z :=
  atImInfty_mem (setOf p)

lemma Filter.tendsto_im_atImInfty : Tendsto (fun x : ℍ ↦ x.im) atImInfty atTop :=
  tendsto_iff_comap.mpr fun ⦃_⦄ a => a

/-- `eventually_im_infty A with z hz` turns a goal `∀ᶠ z in atImInfty, p z` into `p z` for
a fixed `z : ℍ` with `hz : A ≤ z.im`. Without the `with` clause it leaves the goal
`∀ z : ℍ, A ≤ z.im → p z` (useful when more variables must be introduced). -/
syntax (name := eventuallyImInftyTac) "eventually_im_infty" (ppSpace colGt term:max)
  (" with " ident ident)? : tactic

macro_rules
  | `(tactic| eventually_im_infty $A with $z $hz) =>
    `(tactic| refine Filter.eventually_atImInfty.mpr ⟨$A, fun $z $hz => ?_⟩)
  | `(tactic| eventually_im_infty $A) =>
    `(tactic| refine Filter.eventually_atImInfty.mpr ⟨$A, ?_⟩)

/-- `isbigo_im_infty C A with z hz` reduces a goal `f =O[atImInfty] g` to the elementwise
bound `‖f z‖ ≤ C * ‖g z‖` for a fixed `z : ℍ` with `hz : A ≤ z.im`. Without the `with`
clause it leaves the goal `∀ z : ℍ, A ≤ z.im → ‖f z‖ ≤ C * ‖g z‖`. -/
syntax (name := isBigOImInftyTac) "isbigo_im_infty" (ppSpace colGt term:max)
  (ppSpace colGt term:max) (" with " ident ident)? : tactic

macro_rules
  | `(tactic| isbigo_im_infty $C $A with $z $hz) => do
    let t1 ← `(tactic| rw [Asymptotics.isBigO_iff])
    let t2 ← `(tactic| refine ⟨$C, Filter.eventually_atImInfty.mpr ⟨$A, fun $z $hz => ?_⟩⟩)
    `(tactic| ($t1; $t2))
  | `(tactic| isbigo_im_infty $C $A) => do
    let t1 ← `(tactic| rw [Asymptotics.isBigO_iff])
    let t2 ← `(tactic| refine ⟨$C, Filter.eventually_atImInfty.mpr ⟨$A, ?_⟩⟩)
    `(tactic| ($t1; $t2))

/-- If f tends to c ≠ 0 at infinity, then f ≠ 0 as a function.

This packages the common argument: if f = 0, then f → 0, but also f → c by hypothesis.
By uniqueness of limits, 0 = c, contradicting c ≠ 0. -/
lemma ne_zero_of_tendsto_ne_zero {f : ℍ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hf : Tendsto f atImInfty (nhds c)) : f ≠ 0 := fun h =>
  hc (tendsto_nhds_unique tendsto_const_nhds (h ▸ hf)).symm
