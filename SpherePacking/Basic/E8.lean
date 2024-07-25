import Mathlib
-- import SpherePacking.Basic.EuclideanLattice
import SpherePacking.Basic.SpherePacking

open Euclidean EuclideanSpace BigOperators EuclideanLattice SpherePacking Matrix algebraMap
  Pointwise

/--
* NOTE: *
It will probably be useful, at some point in the future, to subsume this file under a more general
file tackling the classification of crystallographic, irreducible Coxeter groups and their root
systems (or something like that). It might also be useful to add general API that will make it
easier to construct a `SpherePackingCentres` instance for such lattices, which would be useful for
the sphere packing problem in other dimensions.
-/

local notation "V" => EuclideanSpace ℝ (Fin 8)
-- def V : Type := EuclideanSpace ℝ (Fin 8)
local notation "ℝ⁸" => Fin 8 → ℝ

#check V

instance : SMul ℝ V := ⟨fun (r : ℝ) (v : V) => (fun i => r * v i)⟩

instance : HMul ℝ V V := ⟨fun (r : ℝ) (v : V) => (fun i => r * v i)⟩

@[simp]
def ℤ_as_ℝ : Set ℝ := {r : ℝ | ∃ (n : ℤ), ↑n = r}
local notation "↑ℤ" => ℤ_as_ℝ

@[simp]
def E8_Set : Set V := {v : V | ((∀ i : Fin 8, v i ∈ ↑ℤ) ∨ (∀ i : Fin 8, (2 * v i) ∈ ↑ℤ
  ∧ (v i ∉ ↑ℤ))) ∧ ∑ i : Fin 8, v i ≡ 0 [PMOD 2]}

@[simp]
def E8_Normalised_Set : Set V := (1 / Real.sqrt 2) • E8_Set
-- {v : V | ∃ w ∈ E8_Set, v = ((1 : ℝ) / (Real.sqrt 2)) • w}

section E₈_Over_ℚ
/-! Credit for the code proving linear independence goes to Gareth Ma. -/

/-! # Choice of Simple Roots
There are many possible choices of simple roots for the E₈ root system. Here, we choose the one
mentioned in the Wikipedia article https://en.wikipedia.org/wiki/E8_(mathematics).
-/

@[simp]
def E₈' : Matrix (Fin 8) (Fin 8) ℚ := !![
1,-1,0,0,0,0,0,0;
0,1,-1,0,0,0,0,0;
0,0,1,-1,0,0,0,0;
0,0,0,1,-1,0,0,0;
0,0,0,0,1,-1,0,0;
0,0,0,0,0,1,1,0;
-1/2,-1/2,-1/2,-1/2,-1/2,-1/2,-1/2,-1/2;
0,0,0,0,0,1,-1,0
]

@[simp]
def F₈' : Matrix (Fin 8) (Fin 8) ℚ := !![
1,1,1,1,1,1/2,0,1/2;
0,1,1,1,1,1/2,0,1/2;
0,0,1,1,1,1/2,0,1/2;
0,0,0,1,1,1/2,0,1/2;
0,0,0,0,1,1/2,0,1/2;
0,0,0,0,0,1/2,0,1/2;
0,0,0,0,0,1/2,0,-1/2;
-1,-2,-3,-4,-5,-7/2,-2,-5/2
]

@[simp]
theorem E₈_mul_F₈_eq_id_Q : E₈' * F₈' = !![
    1,0,0,0,0,0,0,0;
    0,1,0,0,0,0,0,0;
    0,0,1,0,0,0,0,0;
    0,0,0,1,0,0,0,0;
    0,0,0,0,1,0,0,0;
    0,0,0,0,0,1,0,0;
    0,0,0,0,0,0,1,0;
    0,0,0,0,0,0,0,1;
    ] := by
  rw [E₈', F₈']
  norm_num

@[simp]
theorem E₈_mul_F₈_eq_one_Q : E₈' * F₈' = 1 := by
  -- TODO: uncomment when needed (because it's slow)
  sorry
  /- convert E₈_mul_F₈_eq_id_Q -/
  /- rw [← Matrix.diagonal_one] -/
  /- ext i j -/
  /- by_cases h : i = j -/
  /- · subst h -/
  /-   fin_cases i <;> norm_num -/
  /- · rw [Matrix.diagonal_apply_ne _ h] -/
  /-   fin_cases i <;> fin_cases j <;> norm_num at h ⊢ -/

@[simp]
theorem F₈_mul_E₈_eq_one_Q : F₈' * E₈' = 1 := by
  rw [Matrix.mul_eq_one_comm, E₈_mul_F₈_eq_one_Q]

end E₈_Over_ℚ

noncomputable section E₈_Over_ℝ

@[simp]
def E₈_Matrix : Matrix (Fin 8) (Fin 8) ℝ := (algebraMap ℚ ℝ).mapMatrix E₈'

@[simp]
def F₈_Matrix : Matrix (Fin 8) (Fin 8) ℝ := (algebraMap ℚ ℝ).mapMatrix F₈'

@[simp]
theorem E₈_mul_F₈_eq_one_R : E₈_Matrix * F₈_Matrix = 1 := by
  rw [E₈_Matrix, F₈_Matrix, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← Matrix.map_mul,
    E₈_mul_F₈_eq_one_Q] --, map_one _ coe_zero coe_one]  -- Doesn't work for some reason
  simp only [map_zero, _root_.map_one, Matrix.map_one]

@[simp]
theorem F₈_mul_E₈_eq_one_R : F₈_Matrix * E₈_Matrix = 1 := by
  rw [E₈_Matrix, F₈_Matrix, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← Matrix.map_mul,
    F₈_mul_E₈_eq_one_Q] --, map_one _ coe_zero coe_one]
  simp only [map_zero, _root_.map_one, Matrix.map_one]

theorem E₈_is_basis :
    LinearIndependent ℝ E₈_Matrix ∧ Submodule.span ℝ (Set.range E₈_Matrix) = ⊤ := by
  -- This code seems to be generating a recursion error for some reason
  -- rw [is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det]
  -- change IsUnit E₈_Matrix.det
  -- have : E₈_Matrix.det * F₈_Matrix.det = 1 := by
  --   rw [← det_mul, E₈_mul_F₈_eq_one_R, det_one]
  -- exact isUnit_of_mul_eq_one _ _ this
  sorry

lemma Top_Le_Span_E₈ : ⊤ ≤ Submodule.span ℝ (Set.range E₈_Matrix) := by
  rw [← E₈_is_basis.2]

@[simp]
def E₈_Basis : Basis (Fin 8) ℝ V := Basis.mk E₈_is_basis.1 Top_Le_Span_E₈

end E₈_Over_ℝ

noncomputable section E₈_Normalised_Over_ℝ

@[simp]
def E₈_Normalised_Matrix : Matrix (Fin 8) (Fin 8) ℝ := (1 / Real.sqrt 2) • E₈_Matrix

@[simp]
def E₈_Normalised_Basis_Set : Set V := Set.range E₈_Normalised_Matrix

@[simp]
def F₈_Normalised_Matrix : Matrix (Fin 8) (Fin 8) ℝ := (Real.sqrt 2) • F₈_Matrix

@[simp]
theorem E₈_Normalised_mul_F₈_Normalised_eq_one_R : E₈_Normalised_Matrix * F₈_Normalised_Matrix = 1
  := by
  have : (Real.sqrt 2) ≠ 0 := by
    simp only [ne_eq, Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true]
  rw [E₈_Normalised_Matrix, F₈_Normalised_Matrix, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    one_div, inv_smul_smul₀ this]
  exact E₈_mul_F₈_eq_one_R

theorem E₈_Normalised_is_basis :
    LinearIndependent ℝ E₈_Normalised_Matrix ∧
      Submodule.span ℝ (Set.range E₈_Normalised_Matrix) = ⊤ := by
  -- Commented out due to deep recursion error
  -- rw [is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det]
  -- change IsUnit E₈_Normalised_Matrix.det
  -- have : E₈_Normalised_Matrix.det * F₈_Normalised_Matrix.det = 1 := by
  --   rw [← det_mul, E₈_Normalised_mul_F₈_Normalised_eq_one_R, det_one]
  -- exact isUnit_of_mul_eq_one _ _ this
  sorry

lemma Top_Le_Span_E₈_Normalised : ⊤ ≤ Submodule.span ℝ (Set.range E₈_Normalised_Matrix) := by
  rw [← E₈_Normalised_is_basis.2]

@[simp]
def E₈_Normalised_Basis : Basis (Fin 8) ℝ V := Basis.mk E₈_Normalised_is_basis.1
  Top_Le_Span_E₈_Normalised

end E₈_Normalised_Over_ℝ

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
    { rw [smul_zero] }
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
      { rcases hv with ⟨_, z, hz⟩
        rw [zero_sub] at hz
        use -z
        simp only [PiLp.neg_apply, Finset.sum_neg_distrib, zero_sub, neg_inj, neg_smul]
        exact hz } }
    { rw [one_div, smul_neg] }

open Topology TopologicalSpace Filter Function

@[simp]
instance instTopSpaceE8Normalised : TopologicalSpace E8_Normalised_Lattice := by infer_instance

@[simp]
instance : PseudoMetricSpace V := by infer_instance

@[simp]
instance : MetricSpace V := by infer_instance

@[simp]
instance instTopSpaceV : TopologicalSpace V := by infer_instance

instance : Dist V where
  dist := Dist.dist

-- lemma resolve_dist (x y : V) : Euclidean.dist x y = Dist.dist x y := by
--   rw [Euclidean.dist, Dist.dist]
--   sorry

lemma resolve_dist_self (x : V) : Euclidean.dist (x : V) (x : V) =
  Dist.dist (x : V) (x : V) := by rw [Euclidean.dist, dist_self, dist_self]

instance instDiscreteE8NormalisedSet : DiscreteTopology E8_Normalised_Set := by
  rw [discreteTopology_iff_singleton_mem_nhds]
  intro x
  rcases x with ⟨x, v, ⟨hv1, hv2⟩, hx⟩
  rw [mem_nhds_subtype]
  simp only [instTopSpaceV, E8_Normalised_Set, E8_Set, ℤ_as_ℝ, Set.mem_setOf_eq, Set.coe_setOf,
    Set.subset_singleton_iff, Set.mem_preimage, Subtype.forall, not_exists, one_div,
    Subtype.mk.injEq, forall_exists_index, and_imp]
  use ball x 0.5
  constructor
  { simp only [instTopSpaceV, isOpen_ball, ball, Set.mem_setOf_eq, dist_self, _root_.mem_nhds_iff]
    use ball x 0.25
    constructor
    { intro y hy
      simp only [instTopSpaceV, Set.mem_setOf_eq]
      have : (0.25 : ℝ) ≤ 0.5 := by norm_num
      rw [ball, Set.mem_setOf_eq] at hy
      exact lt_of_lt_of_le hy this }
    { constructor
      { exact isOpen_ball }
      { rw [ball, Set.mem_setOf_eq, resolve_dist_self x, dist_self]
        norm_num } } }
  { intros y z h1 h2 hyz hy
    -- We would need to show that the distance between two points in the normalised lattice
    -- is at least 1.
    sorry }

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
    use E₈_Normalised_Basis
    have hbasiselts : Set.range E₈_Normalised_Basis = E₈_Normalised_Basis_Set := by
      ext x
      constructor
      { intro hx
        rcases hx with ⟨i, hi⟩
        use i
        simp only [← hi, E₈_Normalised_Basis, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul,
          coe_basisOfLinearIndependentOfCardEqFinrank, E₈_Normalised_Matrix, Pi.smul_apply,
          E₈_Matrix, Basis.coe_mk] }
      { intro hx
        apply Set.mem_range.mpr
        rcases hx with ⟨i, hi⟩
        use i
        simp only [hi, E₈_Normalised_Basis, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul,
          coe_basisOfLinearIndependentOfCardEqFinrank, E₈_Normalised_Matrix, Pi.smul_apply,
          E₈_Matrix, Basis.coe_mk, Pi.smul_apply, ← hi] }
    intro x hx
    rw [hbasiselts] at hx
    cases' hx with i hi
    unfold E8_Normalised_Set
    simp only [Set.mem_setOf_eq, E8_Set]
    sorry
    /-
    rcases i with ⟨i₀ | i₁ | i₂ | i₃ | i₄ | i₅ | i₆ | i₇ | n, hn⟩
    -- A lot of steps here are repeated. Can this code be optimised?
    { use E₈_Matrix 0
      constructor
      { constructor
        { left
          intro j
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { use 1
            simp only [Int.cast_one, Fin.isValue, Fin.zero_eta, E₈_Matrix, E₈_Matrix,
              Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
              Matrix.empty_val', Matrix.cons_val_fin_one] }
          { use (-1)
            simp only [Int.cast_one, Fin.zero_eta, E₈_Matrix, E₈_Matrix,
              Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
              Int.reduceNeg, Int.cast_neg, zero_add, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
              Matrix.head_cons] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_two, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_three, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_four, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_zero]
            sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { simp only [E₈_Matrix, E₈_Matrix, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero]
          sorry } }
      { simp only [E₈_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, Fin.isValue, one_div] } }
    { use E₈_Matrix 1
      constructor
      { constructor
        { left
          intro j
          -- Rest done by copilot, pattern-matching with first. Very cool
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, Fin.zero_eta,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons] }
          { use 1
            simp only [Int.cast_one, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add, Fin.mk_one,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one] }
          { use (-1)
            simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, E₈_Matrix, E₈_Matrix,
              Fin.isValue, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply,
              Matrix.cons_val', Matrix.cons_val_two, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_three, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_four, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons]
            sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { simp only [Finset.sum, Fin.isValue, Fin.univ_val_map, List.ofFn_succ,
            Fin.succ_zero_eq_one, Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe,
            List.sum_cons, List.sum_nil, add_zero, Fin.succ, Fin.isValue, Nat.succ_eq_add_one,
            Nat.reduceAdd, Fin.val_zero, Fin.mk_one, Fin.reduceFinMk, E₈_Matrix, Int.cast_zero,
            Int.cast_one, add_right_neg, AddCommGroup.modEq_refl]
          simp only [E₈_Matrix, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
            Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
            Matrix.head_cons, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd,
            Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four, zero_add,
            add_neg_cancel_left]
          sorry } }
      { simp only [E₈_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, Fin.isValue, one_div, zero_add, Fin.mk_one, Fin.isValue] } }
    { use E₈_Matrix 2
      constructor
      { constructor
        { left
          intro j
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, Fin.zero_eta,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd,
              Matrix.tail_cons, Matrix.head_cons] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add, Fin.mk_one,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two, Nat.succ_eq_add_one,
              Nat.reduceAdd, Matrix.tail_cons] }
          { use 1
            simp only [Int.cast_one, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add, Nat.reduceAdd,
              Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_two,
              Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons, Matrix.empty_val',
              Matrix.cons_val_fin_one] }
          { use (-1)
            simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, E₈_Matrix, E₈_Matrix,
              Fin.isValue, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply,
              Matrix.cons_val', Matrix.cons_val_three, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_four, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_two, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_two, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_two, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { sorry } }
      { simp only [E₈_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, one_div] } }
    { use E₈_Matrix 3
      constructor
      { constructor
        { left
          intro j
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, Fin.zero_eta,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_three, Nat.succ_eq_add_one, Nat.reduceAdd,
              Matrix.tail_cons, Matrix.head_cons] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add, Fin.mk_one,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_three,
              Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_two, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_three] }
          { use 1
            simp only [Int.cast_one, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add, Nat.reduceAdd,
              Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_three,
              Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons, Matrix.empty_val',
              Matrix.cons_val_fin_one] }
          { use (-1)
            simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, E₈_Matrix, E₈_Matrix,
              Fin.isValue, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply,
              Matrix.cons_val', Matrix.cons_val_four, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_three] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_three, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_three, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_three, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { sorry } }
      { simp only [E₈_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, one_div] } }
    { use E₈_Matrix 4
      constructor
      { constructor
        { left
          intro j
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, Fin.zero_eta,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_four, Nat.succ_eq_add_one, Nat.reduceAdd,
              Matrix.tail_cons, Matrix.head_cons] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add, Fin.mk_one,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_four, Nat.succ_eq_add_one,
              Nat.reduceAdd, Matrix.tail_cons] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_two, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_four] }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_three, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_four] }
          { use 1
            simp only [Int.cast_one, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add, Nat.reduceAdd,
              Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_four,
              Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons, Matrix.empty_val',
              Matrix.cons_val_fin_one] }
          { use (-1)
            simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, E₈_Matrix, E₈_Matrix,
              Fin.isValue, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply,
              Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_four,
              Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_four, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_four, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { sorry } }
      { simp only [E₈_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, one_div] } }
    { use E₈_Matrix 5
      constructor
      { constructor
        { left
          intro j
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, Fin.zero_eta,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
              Matrix.cons_val_fin_one]
            sorry }
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, zero_add, Fin.mk_one,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E₈_Matrix, Int.cast_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E₈_Matrix, Int.cast_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E₈_Matrix, Int.cast_zero]
            sorry }
          { use 1
            simp only [Int.cast_zero, Fin.isValue, E₈_Matrix, Int.cast_zero]
            sorry }
          { use 1
            simp only [Int.cast_zero, Fin.isValue, E₈_Matrix, Int.cast_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E₈_Matrix, Int.cast_zero]
            sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { sorry } }
      { simp only [E₈_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, one_div] } }
    { -- This case will need to be dealt with slightly differently
      use E₈_Matrix 6
      constructor
      { constructor
        { right
          intro j
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { constructor
            { use -1
              simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, E₈_Matrix, E₈_Matrix,
                Fin.isValue, Fin.zero_eta, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
                Matrix.empty_val', Matrix.cons_val_fin_one]
              sorry }
            { intro hcontra
              simp only [Int.cast_one, Fin.isValue, E₈_Matrix, Int.reduceNeg, Int.cast_neg,
                Int.cast_one] at hcontra
              rcases hcontra with ⟨p, hp⟩
              have even_one : Even (1 : ℤ) := by
              { use -1 * p
                rify
                simp only [hp, E₈_Matrix, Fin.isValue, Fin.zero_eta, Matrix.of_apply,
                  Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
                  Matrix.cons_val_fin_one, neg_mul, one_mul]
                norm_num
                sorry }
              contradiction } }
          { sorry }
          { sorry }
          { sorry }
          { sorry }
          { sorry }
          { sorry }
          { sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { sorry } }
      { simp only [E₈_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, one_div] } }
    { use E₈_Matrix 7
      constructor
      { constructor
        { left
          intro j
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { use 0
            simp only [Int.cast_zero, E₈_Matrix, E₈_Matrix, Fin.isValue, Fin.zero_eta,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
              Matrix.cons_val_fin_one]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E₈_Matrix, Int.cast_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E₈_Matrix, Int.cast_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E₈_Matrix, Int.cast_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E₈_Matrix, Int.cast_zero]
            sorry }
          { use 1
            simp only [Int.cast_zero, Fin.isValue, E₈_Matrix, Int.cast_zero]
            sorry }
          { use -1
            simp only [Int.cast_zero, Fin.isValue, E₈_Matrix, Int.cast_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E₈_Matrix, Int.cast_zero]
            sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { sorry } }
      { simp only [E₈_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, one_div] } }
    { exfalso
      simp only [Nat.add_one, Nat.succ] at hn
      cases n
      { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hn }
      { linarith } }
    -/


end Lattice

section Packing

-- def E8 := Packing_of_Centres 8 (EuclideanLattice.E8_Normalised_Set)

instance instSpherePackingE8NormalisedLattice : SpherePackingCentres 8 E8_Normalised_Lattice where
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
    -- The only strategy that comes to mind to tackle this proof is to expand `Euclidean.dist`
    -- somehow and then do cases on `hv11` and `hw11` (as in the def of `E8_Normalised_Lattice`, ie,
    -- the proof that it is an additive, commutative subgroup of the ambient space).
    sorry

def E8_Packing := Packing_of_Centres 8 E8_Normalised_Lattice

theorem Main : Constant 8 = Density 8 E8_Normalised_Lattice := sorry

end Packing
