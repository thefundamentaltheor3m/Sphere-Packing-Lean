import Mathlib

open Euclidean BigOperators

namespace EuclideanLattice  -- Perhaps this can be moved to a different file...

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

class isLattice (Λ : AddSubgroup V) [DiscreteTopology Λ] extends IsZlattice ℝ Λ

section Action

/-!
# The Lattice Action

We need to define an action of a lattice on a set of lattice-periodic points in Euclidean space.
This will allow us to formalise the theorem for the density of a periodic packing.
-/

def Periodic (Λ : AddSubgroup V) [DiscreteTopology Λ] [isLattice Λ] (X : Set V) : Prop :=
  ∀ x ∈ Λ, ∀ y ∈ X, x + y ∈ X

noncomputable instance instPeriodicToAction (Λ : AddSubgroup V) [DiscreteTopology Λ] [isLattice Λ] (X : Set V) (hPeriodic : Periodic Λ X) : AddAction Λ X where
  vadd := fun x y => ⟨(x : V) + (y : V), hPeriodic x (SetLike.coe_mem x) y (Subtype.coe_prop y)⟩
  zero_vadd := by
    intro x
    unfold instHVAdd
    simp only [ZeroMemClass.coe_zero, zero_add, Subtype.coe_eta]
  add_vadd := by
    intros x y v
    unfold instHVAdd
    simp only [AddSubmonoid.coe_add, AddSubgroup.coe_toAddSubmonoid, Subtype.mk.injEq, add_assoc]

/-
We now need to find a way to embed the quotient of any set by this action into Euclidean space.
-/



end Action

end EuclideanLattice
