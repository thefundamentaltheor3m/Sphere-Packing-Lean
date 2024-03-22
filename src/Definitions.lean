import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.LinearAlgebra.Basis
import Mathlib.LinearAlgebra.Span
import Mathlib.LinearAlgebra.LinearIndependent
-- TODO: Clean up imports once done with file

variable (n : ℕ)
-- The following (copied from Mathlib/MeasureTheory/Integral/TorusIntegral.lean)
-- allows the local notation ℝⁿ = Fin n → ℝ
local macro:arg t:term:max noWs "ⁿ" : term => `(Fin n → $t)

instance : AddCommMonoid (ℝⁿ) := Pi.addCommMonoid
noncomputable instance : Module ℝ (ℝⁿ) := Pi.module (Fin n) (fun i => ℝ) ℝ
instance : AddCommGroup (ℝⁿ) := Pi.addCommGroup
instance : FiniteDimensional ℝ ℝⁿ := sorry
instance : InnerProductSpace ℝ ℝⁿ := sorry
instance : Module ℤ (ℝⁿ) := by exact AddCommGroup.intModule (Fin n → ℝ)

open Euclidean

namespace SpherePacking

section Lattices
open BigOperators

-- What's the best way of defining a lattice??

def in_lattice (B : Basis (Fin n) ℝ ℝⁿ) (v : ℝⁿ) : Prop :=
  ∃ (a : ℤⁿ), v = ∑ i : (Fin n), ↑(a i) * (B i)

def lattice (B : Basis (Fin n) ℝ ℝⁿ) : Set ℝⁿ :=
  {v : ℝⁿ | in_lattice n B v}

instance {B : Basis (Fin n) ℝ ℝⁿ} : AddCommGroup ↑(lattice n B) := by
  sorry

-- structure lattice' (B : Basis (Fin n) ℝ ℝⁿ) :=
--   (vectors : Set ℝⁿ) (h : ∀ (v : ℝⁿ), v ∈ vectors → ∃ (a : ℤⁿ), v = ∑ i : (Fin n), ↑(a i) * (B i))

-- instance {B : Basis (Fin n) ℝ ℝⁿ} : AddCommGroup (lattice' n B) := sorry

end Lattices

section SpherePacking

/-
# We define a Sphere Packing as a 5-tuple consisting of
1. `centres`: A subset of ℝⁿ consisting of the centres of the spheres
2. `radius`: The (common) radius of each sphere in the packing
3. `hrad`: The hypothesis that `radius` is positive
4. `hpacking`: The hypothesis that no two spheres centred at points in `centres` with common
    radius `c` intersect---ie, that the spheres do, indeed, form a packing.
Remark. We define packings to be extensional: two packings are equal iff they have the same set of
centres and the same common radius. We
-/

def nonoverlapping (centres : Set ℝⁿ) (radius : ℝ) : Prop :=  ∀ p₁ p₂ : ℝⁿ, p₁ ∈ centres →
  p₂ ∈ centres → p₁ ≠ p₂ → Euclidean.dist p₁ p₂ > 2 * radius

@[ext]
structure SpherePacking where
  centres : Set ℝⁿ
  radius : ℝ
  hrad : radius > 0
  hpacking : nonoverlapping n centres radius

#check SpherePacking.ext_iff

-- Below, we give a few examples of sphere packings.

def EgPacking2 : SpherePacking 2 where -- An example of a sphere packing in two dimensions
  centres := ∅
  radius := 1
  hrad := by linarith
  hpacking := by
    intros p₁ p₂ hp₁ hp₂ hp₁p₂
    exfalso
    assumption

def EgPacking1 : SpherePacking 1 where -- An example of a sphere packing in one dimension
  centres := {2, 4}
  radius := 1
  hrad := by linarith
  hpacking := by
    intros p₁ p₂ hp₁ hp₂ hp₁p₂
    have h₁ : p₁ = 2 ∨ p₁ = 4 := hp₁
    have h₂ : p₂ = 2 ∨ p₂ = 4 := hp₂
    rcases h₁ with c₁ | c₂;
    { rcases h₂ with d₁ | d₂;
      { rw [c₁, d₁] at hp₁p₂
        contradiction }
      { rw [c₁, d₂]
        sorry } }
    { rcases h₂ with d₁ | d₂;
      { sorry }
      { rw [c₂, d₂] at hp₁p₂
        contradiction } }

/- A Packing is S-periodic if the set of centres is invariant under addition by elements of S. -/
def Periodic (P : SpherePacking n) (S : Set ℝⁿ) : Prop :=
  ∀ (s c : ℝⁿ), s ∈ S → c ∈ P.centres → c + s ∈ P.centres

example : Periodic 2 EgPacking2 {0} := by
  unfold Periodic
  intros s c hs hc
  contradiction

example (P : SpherePacking n) : Periodic n P {(0 : ℝⁿ)} := by
  intros s c hs hc
  have : s = (0 : ℝⁿ) := hs
  simp_rw [this, add_zero]  -- Make this less clunky looking
  assumption

lemma Countable_Centres (P : SpherePacking n) : Countable P.centres := by
  sorry

/- A Packing `P` is self-periodic if it is `P.centres`-periodic. -/
def SelfPeriodic (P : SpherePacking n) : Prop := Periodic n P P.centres

-- We'd like to be able to say of any packing `P` that if `P.centres` is a lattice, `P` is
-- self-periodic. To do so, we'd need some sort of `is_lattice` type result. This might generally
-- be a better approach: we could then define a structure for lattices whose first term is the
-- lattice (which'll have Type `Set ℝⁿ`) and whose second term has Type `is_lattice`.

end SpherePacking

end SpherePacking
