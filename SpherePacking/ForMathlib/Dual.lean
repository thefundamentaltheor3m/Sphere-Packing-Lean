/-
Intended for `Algebra.Module.Zlattice`
-/
import Mathlib.Algebra.Module.Zlattice.Basic
import Mathlib.Algebra.Module.Zlattice.Covolume
import Mathlib.Analysis.InnerProductSpace.Basic

-- TODO: Generalise to other fields like ℂ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ProperSpace E] [MeasurableSpace E] [InnerProductSpace ℝ E]
  (L : AddSubgroup E) [inst1 : DiscreteTopology L] [inst2 : IsZlattice ℝ L]

def Zlattice.Dual : AddSubgroup E where
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

-- Might be useful to say that the dual lattice is the ℤ-span of the dual basis

instance Zlattice.instDiscreteTopologyDual : DiscreteTopology (Zlattice.Dual L) := by
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

instance Zlattice.instIsZlatticeDual : IsZlattice ℝ (Zlattice.Dual L) := sorry

-- TODO: Rename, move
