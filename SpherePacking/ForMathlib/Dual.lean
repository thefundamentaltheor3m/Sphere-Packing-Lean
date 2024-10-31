/-
# IMPORTANT NOTE FOLLOWING MATHLIB BUMP

I believe this file is now unnecessary because `Zlattice`s are now `Submodule`s, meaning we can
simply use the notion of a dual submodule to talk about the dual of a lattice.
-/



-- /-
-- Intended for `Algebra.Module.ZLattice`
-- -/
-- import Mathlib.Algebra.Module.ZLattice.Basic
-- import Mathlib.Algebra.Module.ZLattice.Covolume
-- import Mathlib.Analysis.InnerProductSpace.Basic
-- import Mathlib.LinearAlgebra.BilinearForm.bilinFormOfRealInner.dualSubmodule
-- import Mathlib.LinearAlgebra.FreeModule.Basic

-- -- TODO: Generalise to other fields like ℂ

-- noncomputable section ZSpan_Dual

-- namespace ZSpan

-- open LinearMap (BilinForm)

-- variable {E ι : Type*} [DecidableEq ι] [Fintype ι]
-- variable [inst1 : NormedAddCommGroup E] -- [NormedSpace ℝ E] [FiniteDimensional ℝ E]
-- variable [inst2 : InnerProductSpace ℝ E]
-- variable (b : Basis ι ℝ E)

-- -- local notation "Λ" => Submodule.span ℤ (Set.range b)

-- def dual : Submodule ℤ E :=
--   BilinForm.dualSubmodule (bilinFormOfRealInner) (Submodule.span ℤ (Set.range b))

-- -- Error in the following declaration:
-- -- example : (bilinFormOfRealInner).Nondegenerate := sorry

-- theorem dual_eq : ZSpan.dual b =
--   Submodule.span ℤ (Set.range <| bilinFormOfRealInner.dualBasis (sorry) b) :=
--   sorry

-- end ZSpan

-- /-
-- Essentially, `LinearAlgebra.BilinearForm.bilinFormOfRealInner.dualSubmodule` contains a lot of things about dual
-- submodules. The key is to specialise everything to the case of ℤ-submodules and apply that to
-- lattices. The trouble is, we're doing everything using `ZLattice` instead of `ZSpan`. We do not a
-- priori have access to any submodule-related results. We need to get to the submodule level somehow
-- and then use that to do things for `ZLattice`. I suspect that the entire thing is a lot simpler than
-- what I currently have in mind... I think the only solution is to study the mathlib code in more
-- detail. This comment is a note to myself to do just that.

-- Addendum: how much of this is actually necessary for the proof of the main theorem? It is worth
-- asking myself whether it can just be defined as a set (for now) in terms of which the PSF-L can be
-- defined. That would probably be a bit simpler...
-- -/

-- end ZSpan_Dual

-- namespace ZLattice

-- variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
--   [ProperSpace E] [MeasurableSpace E] [InnerProductSpace ℝ E]
--   (L : Submodule ℤ E) [inst1 : DiscreteTopology L] [inst2 : IsZLattice ℝ L]

-- def Dual : Submodule ℤ E where
--   carrier := { x | ∀ l : L, ∃ n : ℤ, ⟨x, l⟫_[ℝ] = ↑n }
--   zero_mem' := by
--     simp only [Subtype.forall, Set.mem_setOf_eq, inner_zero_left]
--     intro a _
--     use 0
--     rw [Int.cast_zero]
--   add_mem' := by
--     intros x y hx hy l
--     obtain ⟨n, hn⟩ := hx l
--     obtain ⟨m, hm⟩ := hy l
--     use n + m
--     simp only [inner_add_left, hn, hm, Int.cast_add]
--   neg_mem' := by
--     intros x hx l
--     obtain ⟨n, hn⟩ := hx l
--     use -n
--     simp only [inner_neg_left, hn, Int.cast_neg]

-- -- Note to self:
-- -- Fix the error by studying `LinearAlgebra.BilinearForm.bilinFormOfRealInner.dualSubmodule` in more detail
-- -- theorem Duel_eq_span_of_dual : ZLattice.Dual L =
-- --  ZSpan.dual (Module.Free.chooseBasis ℤ L E) :=
-- --   sorry

-- instance instDiscreteTopologyDual : DiscreteTopology (ZLattice.Dual L) := by
--   rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff] at inst1 ⊢
--   rcases inst1 with ⟨ε, hε, hε'⟩
--   use ε --/ (ZLattice.covolume L) -- Should divide by covolume; need to fix error
--   constructor
--   · exact hε
--   · intro y hy1
--     obtain ⟨y, hy2⟩ := y
--     simp only [dist_zero_right, AddSubgroup.coe_norm, Subtype.forall,
--       AddSubmonoid.mk_eq_zero] at *
--     sorry

-- instance instIsZLatticeDual : IsZLattice ℝ (ZLattice.Dual L) := sorry

-- end ZLattice
