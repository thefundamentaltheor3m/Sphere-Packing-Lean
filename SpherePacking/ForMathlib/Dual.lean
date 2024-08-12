/-
Intended for `Algebra.Module.Zlattice`
-/
import Mathlib.Algebra.Module.Zlattice.Basic
import Mathlib.Algebra.Module.Zlattice.Covolume
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.FreeModule.Basic

-- TODO: Generalise to other fields like ℂ

noncomputable section Zspan_Dual

namespace Zspan

open LinearMap (BilinForm)

variable {E ι : Type*} [DecidableEq ι] [Fintype ι]
variable [inst1 : NormedAddCommGroup E] -- [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [inst2 : InnerProductSpace ℝ E]
variable (b : Basis ι ℝ E)

-- local notation "Λ" => Submodule.span ℤ (Set.range b)

def dual : Submodule ℤ E :=
  BilinForm.dualSubmodule (bilinFormOfRealInner) (Submodule.span ℤ (Set.range b))

-- Error in the following declaration:
-- example : (bilinFormOfRealInner).Nondegenerate := sorry

theorem dual_eq : Zspan.dual b =
  Submodule.span ℤ (Set.range <| bilinFormOfRealInner.dualBasis (sorry) b) :=
  sorry

end Zspan

/-
Essentially, `LinearAlgebra.BilinearForm.DualLattice` contains a lot of things about dual
submodules. The key is to specialise everything to the case of ℤ-submodules and apply that to
lattices. The trouble is, we're doing everything using `Zlattice` instead of `Zspan`. We do not a
priori have access to any submodule-related results. We need to get to the submodule level somehow
and then use that to do things for `Zlattice`. I suspect that the entire thing is a lot simpler than
what I currently have in mind... I think the only solution is to study the mathlib code in more
detail. This comment is a note to myself to do just that.

Addendum: how much of this is actually necessary for the proof of the main theorem? It is worth
asking myself whether it can just be defined as a set (for now) in terms of which the PSF-L can be
defined. That would probably be a bit simpler...
-/

end Zspan_Dual

namespace Zlattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ProperSpace E] [MeasurableSpace E] [InnerProductSpace ℝ E]
  (L : AddSubgroup E) [inst1 : DiscreteTopology L] [inst2 : IsZlattice ℝ L]

def Dual : AddSubgroup E where
  carrier := { x | ∀ l : L, ∃ n : ℤ, ⟪x, l⟫_ℝ = ↑n }
  zero_mem' := by
    simp only [Subtype.forall, Set.mem_setOf_eq, inner_zero_left]
    intro a _
    use 0
    rw [Int.cast_zero]
  add_mem' := by
    intros x y hx hy l
    obtain ⟨n, hn⟩ := hx l
    obtain ⟨m, hm⟩ := hy l
    use n + m
    simp only [inner_add_left, hn, hm, Int.cast_add]
  neg_mem' := by
    intros x hx l
    obtain ⟨n, hn⟩ := hx l
    use -n
    simp only [inner_neg_left, hn, Int.cast_neg]

-- Note to self:
-- Fix the error by studying `LinearAlgebra.BilinearForm.DualLattice` in more detail
-- theorem Duel_eq_span_of_dual : Zlattice.Dual L =
--  Zspan.dual (Module.Free.chooseBasis ℤ L E) :=
--   sorry

instance instDiscreteTopologyDual : DiscreteTopology (Zlattice.Dual L) := by
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff] at inst1 ⊢
  rcases inst1 with ⟨ε, hε, hε'⟩
  use ε --/ (Zlattice.covolume L) -- Should divide by covolume; need to fix error
  constructor
  · exact hε
  · intro y hy1
    obtain ⟨y, hy2⟩ := y
    simp only [dist_zero_right, AddSubgroup.coe_norm, Subtype.forall,
      AddSubmonoid.mk_eq_zero] at *
    sorry

instance instIsZlatticeDual : IsZlattice ℝ (Zlattice.Dual L) := sorry

end Zlattice
