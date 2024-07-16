import Mathlib
-- import SpherePacking.Basic.EuclideanLattice
import SpherePacking.Basic.SpherePacking

open Euclidean BigOperators EuclideanLattice SpherePacking

local notation "V" => EuclideanSpace ℝ (Fin 8)
local notation "ℝ⁸" => Fin 8 → ℝ

instance : SMul ℝ V := ⟨fun (r : ℝ) (v : V) => (fun i => r * v i)⟩

instance : HMul ℝ V V := ⟨fun (r : ℝ) (v : V) => (fun i => r * v i)⟩

def ℤ_as_ℝ : Set ℝ := {r : ℝ | ∃ (n : ℤ), ↑n = r}
local notation "↑ℤ" => ℤ_as_ℝ

def E8_Set : Set V := {v : V | ((∀ i : Fin 8, v i ∈ ↑ℤ) ∨ (∀ i : Fin 8, (2 * v i) ∈ ↑ℤ
  ∧ (v i ∉ ↑ℤ))) ∧ ∑ i : Fin 8, v i ≡ 0 [PMOD 2]}

def E8_Normalised_Set : Set V := {v : V | ∃ w ∈ E8_Set, v = ((1 : ℝ) / (Real.sqrt 2)) • w}

noncomputable section Basis

def coords_to_R8 (v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : ℝ) : ℝ⁸ := fun i => match i with
| ⟨0, _⟩ => v₀
| ⟨1, _⟩ => v₁
| ⟨2, _⟩ => v₂
| ⟨3, _⟩ => v₃
| ⟨4, _⟩ => v₄
| ⟨5, _⟩ => v₅
| ⟨6, _⟩ => v₆
| ⟨7, _⟩ => v₇

def R8_to_V (v : ℝ⁸) : V := fun i => v i

def coords_to_V (v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : ℝ) : V := R8_to_V (coords_to_R8 v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇)

def E8_Basis_Vecs : Fin 8 → V := fun i => match i with
  | ⟨0, _⟩ => coords_to_V 2 (-1) 0 0 0 0 0 0.5
  | ⟨1, _⟩ => coords_to_V 0 1 (-1) 0 0 0 0 0.5
  | ⟨2, _⟩ => coords_to_V 0 0 1 (-1) 0 0 0 0.5
  | ⟨3, _⟩ => coords_to_V 0 0 0 1 (-1) 0 0 0.5
  | ⟨4, _⟩ => coords_to_V 0 0 0 0 1 (-1) 0 0.5
  | ⟨5, _⟩ => coords_to_V 0 0 0 0 0 1 (-1) 0.5
  | ⟨6, _⟩ => coords_to_V 0 0 0 0 0 0 1 0.5
  | ⟨7, _⟩ => coords_to_V 0 0 0 0 0 0 0 0.5

def E8_Normalised_Basis_Vecs : Fin 8 → V := (√2)⁻¹ • E8_Basis_Vecs

def E8_Normalised_Basis_Set : Set V := Set.range E8_Normalised_Basis_Vecs

lemma E8_Normalised_Basis_LI : LinearIndependent ℝ E8_Normalised_Basis_Vecs := by
  -- rw [LinearIndependent, LinearMap.ker_eq_bot']
  -- intros m hm
  -- unfold Finsupp.total at hm
  -- simp only [Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
  --   E8_Basis_Vecs] at hm
  rw [Fintype.linearIndependent_iff', LinearMap.lsum_apply] -- , LinearMap.ker_eq_bot']
  -- intros x hx
  sorry

lemma E8_Normalised_Basis_SP : ⊤ ≤ Submodule.span ℝ (Set.range E8_Normalised_Basis_Vecs) := by
  intro x hx
  unfold Set.range
  unfold Submodule.span
  unfold sInf
  sorry

def E8_Normalised_Basis : Basis (Fin 8) ℝ V := Basis.mk
  E8_Normalised_Basis_LI E8_Normalised_Basis_SP

end Basis

noncomputable section Lattice

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
            simp only [f, mul_add, PiLp.add_apply, Int.cast_add, ←hn, ←hm, hp, hq, Int.cast_one,
              mul_one, Int.cast_mul, Int.cast_ofNat]
            linarith }
      { simp only [PiLp.add_apply, Finset.sum_add_distrib]
        have HMODSUM : ∀ x y : ℝ, x ≡ 0 [PMOD 2] → y ≡ 0 [PMOD 2] → (x + y) ≡ 0 [PMOD 2] := by
          -- Should exist in Mathlib in some shape or form
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

-- lemma resolve_dist (x y : V) : Euclidean.dist x y = Dist.dist x y := by
--   rw [Euclidean.dist, Dist.dist]
--   sorry

lemma resolve_dist_self (x : E8_Normalised_Set) : Euclidean.dist (x : V) (x : V) =
  Dist.dist (x : V) (x : V) := by rw [Euclidean.dist, dist_self, dist_self]

instance instDiscreteE8NormalisedSet : DiscreteTopology E8_Normalised_Set :=
  singletons_open_iff_discrete.mp fun x => by
  -- unfold IsOpen
  -- unfold TopologicalSpace.IsOpen
  -- unfold instTopologicalSpaceSubtype.1
  have H : ∀ U : Set E8_Normalised_Lattice, (∃ U' : Set V, IsOpen U' ∧ U = E8_Normalised_Set ∩ U')
    → IsOpen U := by
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
    { simp only [SetLike.coe_sort_coe, Set.image_singleton, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Set.mem_inter_iff]
      rintro ⟨w, hw, rfl⟩
      constructor
      { exact x.2 }
      { simp only [resolve_dist_self, PseudoMetricSpace.dist_self (↑x : V)]
        suffices hself : Dist.dist (x : V) (x : V) = 0
        { norm_num }
        exact dist_self (x : V) } }
    { simp only [Set.mem_setOf_eq, one_div, Set.mem_inter_iff, SetLike.coe_sort_coe,
      Set.image_singleton, Set.mem_singleton_iff, and_imp, forall_exists_index]
      simp only [E8_Normalised_Set, Set.coe_setOf] at x
      rcases x with ⟨x, w, hw1, hw2⟩
      rintro v H1 H2 H3 H4
      simp only [H3, hw2, one_div] at H4 ⊢
      suffices hvw : v = w  -- Wasn't sure what kind of mul_eq thing to apply...
      { rw [hvw] }

      sorry } }

instance instDiscreteE8NormalisedLattice : DiscreteTopology E8_Normalised_Lattice :=
  instDiscreteE8NormalisedSet

instance instLatticeE8 : isLattice E8_Normalised_Lattice where
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
          rw [Basis.span_eq] at hz
          rw [← B.span_eq] at hz
          unfold Submodule.span at hz
          simp only [Submodule.sInf_coe, Set.mem_setOf_eq, Set.mem_iInter, SetLike.mem_coe] at hz ⊢
          specialize hz M hB
          exact hz
        rw [Basis.span_eq] at h1
        exact h1 hy } }
    suffices hE8basis : ∃ B : Basis (Fin 8) ℝ V, ((Set.range B) : Set V) ⊆ E8_Normalised_Set
    { rcases hE8basis with ⟨B, hB⟩
      use B
      intro x hx
      exact hM (hB hx) }
    -- *TODO:* We need to feed in the (normalised) E8 basis uere.
    -- This requires us to construct it in the first place.
    -- This requires us to be able to get elements of `V` from elements of `ℝ⁸`.
    use E8_Normalised_Basis
    have hbasiselts : Set.range E8_Normalised_Basis = E8_Normalised_Basis_Set := by
      ext x
      constructor
      { intro hx
        rcases hx with ⟨i, hi⟩
        use i
        rw [← hi]
        simp only [E8_Basis_Vecs]
        sorry }
      { sorry }
    intro x hx
    cases' hx with i hi
    -- unfold E8_Basis at hi
    rcases i with ⟨i₀ | i₁ | i₂ | i₃ | i₄ | i₅ | i₆ | i₇⟩
    { unfold E8_Normalised_Set
      simp only [Set.mem_setOf_eq, E8_Set]
      use E8_Basis_Vecs 0
      constructor
      {
        sorry }
      { rw [← hi, E8_Normalised_Basis]
        sorry } }
    { sorry }
    { sorry }
    { sorry }
    { sorry }
    { sorry }
    { sorry }
    { sorry }


end Lattice

section Packing

-- def E8 := Packing_of_Centres 8 (EuclideanLattice.E8_Normalised_Set)

instance : SpherePackingCentres 8 E8_Normalised_Set where
  nonoverlapping := by
    intros x hx y hy hxy
    rcases hx with ⟨v, hv1, hv2⟩
    rcases hy with ⟨w, hw1, hw2⟩
    unfold E8_Set at hv1 hw1
    rw [Set.mem_setOf_eq] at hv1 hw1
    rcases hv1 with ⟨hv11, hv12⟩
    rcases hw1 with ⟨hw11, hw12⟩
    -- rw [PiLp.dist_eq_of_L2 x y]
    -- The above doesn't work because of the difference between `Dist.dist` and ``Euclidean.dist`!!
    sorry

local notation "P" => Packing_of_Centres 8 E8_Normalised_Set

theorem Main : Constant 8 = Density 8 E8_Normalised_Set := sorry

end Packing
