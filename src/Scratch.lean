import Mathlib

open Euclidean BigOperators

variable (n : ℕ)

-- The following (copied from Mathlib/MeasureTheory/Integral/TorusIntegral.lean)
-- allows the local notation ℝⁿ = Fin n → ℝ
local macro:arg t:term:max noWs "ⁿ" : term => `(Fin n → $t) -- EuclideanSpace
-- local macro:arg t:term:max noWs "ⁿ" : term => `(EuclideanSpace $t (Fin n))

namespace SpherePacking

section Lattices

-- What's the best way of defining a lattice??

def in_lattice (B : Basis (Fin n) ℝ ℝⁿ) (v : ℝⁿ) : Prop :=
  ∃ (a : Fin n → ℤ), v = ∑ i : (Fin n), ↑(a i) * (B i)

@[ext]
structure lattice where
  basis : Basis (Fin n) ℝ ℝⁿ
  vectors : Set ℝⁿ
  hlattice : ∀ v, v ∈ vectors ↔ in_lattice n basis v

#check lattice.ext_iff

-- instance {B : Basis (Fin n) ℝ ℝⁿ} : AddCommGroup (lattice' n B) := sorry

def E8 : lattice n where
  basis := sorry
  vectors := sorry --{v : ℝⁿ | ((∀ i : Fin n, v i ∈ ℤ) ∨ (∀ i : Fin n, (2 * v i) ∈ ℤ ∧ (v i ∉ ℤ))) ∧ ∑ i : Fin n, v i = 0}
  hlattice := sorry

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
centres and the same common radius.
-/

def nonoverlapping (centres : Set ℝⁿ) (radius : ℝ) : Prop :=  ∀ p₁ p₂ : ℝⁿ, p₁ ∈ centres →
  p₂ ∈ centres → (p₁ ≠ p₂ ↔ Dist.dist p₁ p₂ ≥ 2 * radius)

#check Dist.dist
#eval Dist.dist (2 : ℝ) 5
#eval Dist.dist (2 : Fin 1 → ℝ) 5
#eval Dist.dist (fun j => j + 3 : Fin 2 → ℝ) 0
#eval Dist.dist (fun j => j + 3 : Fin 4 → ℝ) (fun j => 2*j + 1 : Fin 4 → ℝ)

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
    intros p₁ p₂ hp₁
    contradiction

instance {m : ℕ} : OfNat (EuclideanSpace ℝ (Fin 1)) m := by
  -- use toEuclidean somehow
  sorry


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
  refine { exists_injective_nat' := ?exists_injective_nat' }
  sorry

/- A Packing `P` is self-periodic if it is `P.centres`-periodic. -/
def SelfPeriodic (P : SpherePacking n) : Prop := Periodic n P P.centres

-- We'd like to be able to say of any packing `P` that if `P.centres` is a lattice, `P` is
-- self-periodic. To do so, we'd need some sort of `is_lattice` type result. This might generally
-- be a better approach: we could then define a structure for lattices whose first term is the
-- lattice (which'll have Type `Set ℝⁿ`) and whose second term has Type `is_lattice`.

end SpherePacking

end SpherePacking
