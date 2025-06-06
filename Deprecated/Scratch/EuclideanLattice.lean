import Mathlib

open Euclidean BigOperators

namespace EuclideanLattice

section Definitions

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

def inLattice (B : Basis (Fin d) ℝ V) (v : V) :=
  ∃ (a : Fin d → ℤ), v = ∑ i : (Fin d), ↑(a i) • (B i)

def isLattice (Λ : Set V) : Prop := ∃ (B : Basis (Fin d) ℝ V), Λ = Submodule.span ℤ (Set.range B)

#check isLattice

class isLattice' (Λ : AddSubgroup V) [DiscreteTopology Λ] extends IsZLattice ℝ Λ

example (Λ : Set V) (hΛ : isLattice Λ) : ∃ m : ℕ, m = 4 := by
  rcases hΛ with ⟨B, hB⟩
  use 4

instance (Λ : Set V) (hΛ : isLattice Λ) : Membership V Λ := -- inLattice hΛ.1 -- by
  -- rcases hΛ with ⟨B, hB⟩
  -- exact inLattice B v
  sorry

def isPeriodic (Λ : Set V) -- (hΛ : isLattice Λ)
  (X : Set V) : Prop := ∀ v x : V, v ∈ Λ → x ∈ X → v + x ∈ Λ

end Definitions

section ActionbyTranslation

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)
variable {X Λ : Set V} (hΛ : isLattice Λ) (hX : isPeriodic Λ X)

-- First, we show that a lattice is an additive, commutative group.

instance : Membership V Λ := inLattice hΛ.1

lemma closed_under_addition : ∀ v w : V, v ∈ Λ → w ∈ Λ → v + w ∈ Λ := by
  intro v w
  sorry

-- instance : AddCommGroup Λ where
--   add := fun v w => ⟨v + w, sorry
--   ⟩
--   add_assoc := fun v w x => add_assoc v w x
--   zero := ⟨0, sorry⟩
--   zero_add := fun v => zero_add v
--   nsmul := sorry
--   zsmul := sorry
--   neg := fun v => ⟨-v, sorry⟩
--   add_zero := fun v => add_zero v
--   add_left_neg := fun v => add_left_neg v
--   add_comm := fun v w => add_comm v w

instance ActionOnPeriodic : AddAction Λ X := ⟨
  fun v x => v + x,
  fun v w x => rfl,
  fun v => (add_zero v).symm⟩

instance : AddAction Λ V := ActionOnPeriodic hΛ sorry

end ActionbyTranslation

noncomputable section E8

local notation "V" => EuclideanSpace ℝ (Fin 8)

instance : SMul ℝ V := ⟨fun (r : ℝ) (v : V) => (fun i => r * v i)⟩

instance : HMul ℝ V V := ⟨fun (r : ℝ) (v : V) => (fun i => r * v i)⟩

def ℤ_as_ℝ : Set ℝ := {r : ℝ | ∃ (n : ℤ), ↑n = r}
local notation "↑ℤ" => ℤ_as_ℝ

def E8_Set : Set V := {v : V | ((∀ i : Fin 8, v i ∈ ↑ℤ) ∨ (∀ i : Fin 8, (2 * v i) ∈ ↑ℤ ∧ (v i ∉ ↑ℤ))) ∧ ∑ i : Fin 8, v i ≡ 0 [PMOD 2]}

def E8_Normalised_Set : Set V := {v : V | ∃ w ∈ E8_Set, v = ((1 : ℝ) / (Real.sqrt 2)) • w}

def E8_Normalised_Lattice : AddSubgroup V where
  carrier := E8_Normalised_Set
  zero_mem' := by
    simp
    use (0 : V)
    constructor
    { constructor
      { left
        intro i
        use 0
        rw [PiLp.zero_apply, Int.cast_zero] }
      { simp only [PiLp.zero_apply, Finset.sum_const_zero, AddCommGroup.modEq_refl] } }
    { rw [one_div, smul_zero] }
  add_mem' := by
    intros a b ha hb
    unfold E8_Normalised_Set at *
    unfold E8_Set at *
    rw [Set.mem_setOf_eq] at *
    rcases ha with ⟨v, hv, rfl⟩
    rcases hb with ⟨w, hw, rfl⟩
    use v + w
    rcases hv with ⟨hv1, hv2⟩
    rcases hw with ⟨hw1, hw2⟩
    constructor
    { constructor
      { cases hv1
        case inl hv1 =>
          cases hw1
          case inl hw1 =>
            left
            intro i
            specialize hv1 i
            specialize hw1 i
            rcases hv1 with ⟨n, hn⟩
            rcases hw1 with ⟨m, hm⟩
            use n + m
            rw [PiLp.add_apply, Int.cast_add, hn, hm]
          case inr hw1 =>
            right
            intro i
            specialize hv1 i
            specialize hw1 i
            rcases hv1 with ⟨n, hn⟩
            rcases hw1 with ⟨⟨m, hm⟩, hm2⟩
            constructor
            { rw [PiLp.add_apply]
              use 2 * n + m
              rw [Int.cast_add, mul_add, ← hn, hm, Int.cast_mul, Int.cast_ofNat] }
            { intro HContra
              apply hm2
              rcases HContra with ⟨p, hp⟩
              rw [PiLp.add_apply, ← hn] at hp
              use ↑p - ↑n
              rw [Int.cast_sub, hp, add_sub_cancel_left] }
        case inr hv1 =>
          cases hw1
          case inl hw1 =>
            right
            intro i
            specialize hv1 i
            specialize hw1 i
            rcases hv1 with ⟨⟨n, hn⟩, hn2⟩
            rcases hw1 with ⟨m, hm⟩
            constructor
            { rw [PiLp.add_apply]
              use 2 * m + n
              rw [Int.cast_add, mul_add, ← hm, hn, Int.cast_mul, Int.cast_ofNat, add_comm] }
            { intro HContra
              apply hn2
              rcases HContra with ⟨p, hp⟩
              rw [PiLp.add_apply, ← hm] at hp
              use ↑p - ↑m
              rw [Int.cast_sub, hp, add_sub_cancel_right] }
          case inr hw1 =>
            left
            intro i
            specialize hv1 i
            specialize hw1 i
            rcases hv1 with ⟨⟨n, hn⟩, hn2⟩
            rcases hw1 with ⟨⟨m, hm⟩, hm2⟩
            let f : ℝ → ℝ := fun x => ↑2 * x
            have hf : Function.Injective f := by
              unfold Function.Injective
              intros x y hfxfy
              simp [f] at hfxfy
              exact hfxfy
            have hnp : ∃ p : ℤ, n = 2 * p + 1 := by
              rcases Int.even_or_odd' n with ⟨p, hp⟩
              cases hp
              case inl hp =>
                exfalso
                apply hn2
                use p
                apply hf
                simp only [f, ← hn, hp, Int.cast_mul, Int.cast_ofNat]
              case inr hp =>
                use p
            have hmq : ∃ q : ℤ, m = 2 * q + 1 := by
              rcases Int.even_or_odd' m with ⟨q, hq⟩
              cases hq
              case inl hq =>
                exfalso
                apply hm2
                use q
                apply hf
                simp only [f, ← hm, hq, Int.cast_mul, Int.cast_ofNat]
              case inr hq =>
                use q
            rcases hnp with ⟨p, hp⟩
            rcases hmq with ⟨q, hq⟩
            use p + q + 1
            apply hf
            simp only [f, mul_add, PiLp.add_apply, Int.cast_add, ←hn, ←hm, hp, hq, Int.cast_one, mul_one, Int.cast_mul, Int.cast_ofNat]
            linarith }
      { simp only [PiLp.add_apply, Finset.sum_add_distrib]
        have HMODSUM : ∀ x y : ℝ, x ≡ 0 [PMOD 2] → y ≡ 0 [PMOD 2] → (x + y) ≡ 0 [PMOD 2] := by  -- Should exist in Mathlib in some shape or form
          intros x y hx hy
          rcases hx with ⟨z1, hz1⟩
          rcases hy with ⟨z2, hz2⟩
          use z1 + z2
          rw [zero_sub] at hz1 hz2
          rw [zero_sub, neg_add_rev, add_smul, hz1, hz2, add_comm]
        exact HMODSUM (∑ x : Fin 8, v x) (∑ x : Fin 8, w x) hv2 hw2 } }
    { rw [one_div, smul_add] }
  neg_mem' := by
    intro x hx
    dsimp at *
    rcases hx with ⟨v, hv, rfl⟩
    use -v
    constructor
    { constructor
      { rcases hv with ⟨hv1, _⟩
        cases hv1
        case inl hv1 =>
          left
          intro i
          specialize hv1 i
          rcases hv1 with ⟨n, hn⟩
          use -n
          rw [PiLp.neg_apply, Int.cast_neg, neg_inj]
          exact hn
        case inr hv1 =>
          right
          intro i
          specialize hv1 i
          rcases hv1 with ⟨hn1, hn2⟩
          constructor
          { rcases hn1 with ⟨n, hn⟩
            use -n
            rw [Int.cast_neg, PiLp.neg_apply, mul_neg, neg_inj]
            exact hn }
          { intro HContra
            apply hn2
            rcases HContra with ⟨n, hn⟩
            use -n
            rw [Int.cast_neg, hn, PiLp.neg_apply, neg_neg] } }
      { unfold E8_Set at hv
        rw [Set.mem_setOf_eq] at hv
        rcases hv with ⟨_, z, hz⟩
        rw [zero_sub] at hz
        use -z
        simp only [PiLp.neg_apply, Finset.sum_neg_distrib, zero_sub, neg_inj, neg_smul]
        exact hz } }
    { rw [one_div, smul_neg] }

instance : TopologicalSpace E8_Normalised_Lattice := by infer_instance

instance : PseudoMetricSpace V := by infer_instance

instance : MetricSpace V := by infer_instance

instance : Dist V where
  dist := Dist.dist

lemma resolve_dist_self (x : E8_Normalised_Set) : Euclidean.dist (x : V) (x : V) = Dist.dist (x : V) (x : V) := by rw [Euclidean.dist, dist_self, dist_self]

instance instDiscreteE8NormalisedSet : DiscreteTopology E8_Normalised_Set := singletons_open_iff_discrete.mp fun x => by
  -- unfold IsOpen
  -- unfold TopologicalSpace.IsOpen
  -- unfold instTopologicalSpaceSubtype.1
  have H : ∀ U : Set E8_Normalised_Lattice, (∃ U' : Set V, IsOpen U' ∧ U = E8_Normalised_Set ∩ U') → IsOpen U := by
    -- intros U hU
    -- rcases hU with ⟨U', hU', hU⟩
    -- unfold IsOpen
    -- unfold TopologicalSpace.IsOpen
    -- simp [hU, hU']
    -- rw []

    sorry
  apply H {x}
  use Euclidean.ball x 0.5
  constructor
  { exact Euclidean.isOpen_ball}
  { unfold E8_Normalised_Set ball E8_Set
    ext y
    constructor
    { simp only [SetLike.coe_sort_coe, Set.image_singleton, Set.mem_singleton_iff, Set.mem_setOf_eq, Set.mem_inter_iff]
      rintro ⟨w, hw, rfl⟩
      constructor
      { exact x.2 }
      { simp only [resolve_dist_self, PseudoMetricSpace.dist_self (↑x : V)]
        suffices hself : Dist.dist (x : V) (x : V) = 0
        { norm_num }
        exact dist_self (x : V) } }
    { simp only [Set.mem_setOf_eq, one_div, Set.mem_inter_iff, SetLike.coe_sort_coe,
      Set.image_singleton, Set.mem_singleton_iff, and_imp, forall_exists_index]
      rintro v H1 H2 H3 H4
      sorry } }

instance instDiscreteE8NormalisedLattice : DiscreteTopology E8_Normalised_Lattice := instDiscreteE8NormalisedSet

instance : isLattice' E8_Normalised_Lattice where
  span_top := by
    unfold Submodule.span
    simp only [sInf_eq_top, Set.mem_setOf_eq]
    intros M hM
    have HSet : ↑E8_Normalised_Lattice = E8_Normalised_Set := rfl
    rw [HSet] at hM
    suffices hbasis : ∃ B : Basis (Fin 8) ℝ V, ((Set.range B) : Set V) ⊆ (M : Set V)
    { rcases hbasis with ⟨B, hB⟩
      ext y
      constructor
      { simp only [Submodule.mem_top, implies_true] }
      { intro hy
        have h1 : ((Submodule.span ℝ (Set.range B)) : Set V) ⊆ (M : Set V) := by
          intro z hz
          have h2 : ∃ (a : Fin 8 → ℝ), z = ∑ i : (Fin 8), a i • (B i) := by
            rw [Basis.span_eq] at hz
            -- rw [← Submodule.top_coe] at B
            sorry
          -- rcases h2 with ⟨a, ha⟩
          -- apply (Basis.mem_submodule_iff B).2

          sorry
        rw [Basis.span_eq] at h1
        exact h1 hy } }

    sorry
    -- let hM' := Set.inclusion hM
    -- ext v
    -- constructor
    -- { simp only [Submodule.mem_top, implies_true] }
    -- { intro hv

    --   sorry }

end E8

end EuclideanLattice
