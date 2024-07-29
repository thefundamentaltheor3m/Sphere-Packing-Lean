import Mathlib
import SpherePacking.ForMathlib.VolumeOfBalls
import SpherePacking.ForMathlib.Real

open BigOperators MeasureTheory Metric

/-!
# The choices made in this file mirror those made in `Algebra.Module.Zlattice.Basic`. Specifically,
- All conditions pertaining to types of sphere packings are defined on the sets of centres
- A sphere packing can be built from any set of centres using `Packing_of_Centres`.
-/

namespace SpherePacking

section Definitions

variable (d : ℕ)
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "V" d => EuclideanSpace ℝ (Fin d)

-- TODO: Rename to IsSpherePackingCentres, then define SpherePackingCentres as the univ
-- and define Constant below as a sSup over this set
class SpherePackingCentres (X : Set V) (r : ℝ) [DiscreteTopology X] where
  nonoverlapping : ∀ x y, x ∈ X → y ∈ X → x ≠ y → r ≤ ‖x - y‖

class LatticePackingCentres (X : AddSubgroup V) (r : ℝ)
    [DiscreteTopology X] [IsZlattice ℝ X] extends
  SpherePackingCentres d X r

class PeriodicPackingCentres (X : Set V) (r : ℝ) [DiscreteTopology X] [SpherePackingCentres d X r]
    (Λ : AddSubgroup V) [DiscreteTopology Λ] [IsZlattice ℝ Λ] where
  periodic : ∀ x ∈ X, ∀ y ∈ Λ, x + y ∈ X

def Packing_of_Centres (X : Set V) (r : ℝ) [DiscreteTopology X] [SpherePackingCentres d X r] :
    Set V :=
  ⋃ x ∈ X, (ball x (r / 2))

end Definitions

noncomputable section Density

variable (d : ℕ)
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "V" d => EuclideanSpace ℝ (Fin d)

open scoped ENNReal

def FiniteDensity (X : Set V) (r : ℝ) [DiscreteTopology X] [SpherePackingCentres d X r] (R : ℝ) :
    ℝ≥0∞ :=
  volume ((Packing_of_Centres d X r) ∩ ball (0 : V) R) / (volume (ball (0 : V) R))

def PeriodicDensity (X : Set V) (r : ℝ) [DiscreteTopology X] [SpherePackingCentres d X r]
    (Λ : AddSubgroup V) [DiscreteTopology Λ] [IsZlattice ℝ Λ] [PeriodicPackingCentres d X r Λ]
      {F : Set V} (_hF : IsAddFundamentalDomain Λ F volume) :
        ℝ≥0∞ :=
  volume ((Packing_of_Centres d X r) ∩ F) / volume F

def Density (X : Set V) (r : ℝ) [DiscreteTopology X] [SpherePackingCentres d X r] : ℝ≥0∞ :=
  Filter.limsup (FiniteDensity d X r) Filter.atTop

def PeriodicConstant : ENNReal :=
  sSup {x : ℝ≥0∞ |
    ∃ (X : Set V) (r : ℝ) (Λ : AddSubgroup V)
      (_inst1 : DiscreteTopology X) (_inst2 : SpherePackingCentres d X r)
      (_inst3 : DiscreteTopology Λ) (_inst4 : IsZlattice ℝ Λ)
      (_inst5 : PeriodicPackingCentres d X r Λ), Density d X r = x}

def Constant : ENNReal :=
  sSup {x : ℝ≥0∞ |
    ∃ (X : Set V) (r : ℝ) (_inst1 : DiscreteTopology X) (_inst2 : SpherePackingCentres d X r),
      Density d X r = x}
  -- I don't really like how this looks. Is there a better way of formalising it?

end Density

section PeriodicDensity

/- In this subsection, we prove that PeriodicDensity is equivalent to Density. This would allow us
to compute density of a periodic sphere packing easier. -/

variable (d : ℕ)
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "V" d => EuclideanSpace ℝ (Fin d)

variable
  (X : Set (V d)) (r : ℝ) [DiscreteTopology X] [SpherePackingCentres d X r]
  (Λ : AddSubgroup (V d)) [DiscreteTopology Λ] [IsZlattice ℝ Λ] [PeriodicPackingCentres d X r Λ]
  {F : Set (V d)} (hF : IsAddFundamentalDomain Λ F volume)

theorem Main : Density d X r = PeriodicDensity d X r Λ hF := by
  sorry

end PeriodicDensity

section BasicResults

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "V" d => EuclideanSpace ℝ (Fin d)

open scoped ENNReal
open EuclideanSpace

variable (X : Set (V d)) (r R : ℝ) [DiscreteTopology X] [hX : SpherePackingCentres d X r]

instance : Countable X := countable_of_Lindelof_of_discrete

/- In this section we establish basic results about FiniteDensity and Density of different types of
packings. -/

def instDiscreteX (hr : 0 < r) : DiscreteTopology X := by
  simp_rw [← singletons_open_iff_discrete, Metric.isOpen_iff]
  intro ⟨u, hu⟩ ⟨v, hv⟩ huv
  simp only [Set.mem_singleton_iff, Subtype.mk.injEq, Set.subset_singleton_iff, mem_ball,
    Subtype.forall] at huv ⊢
  subst huv
  use r, hr
  intro a ha ha_dist
  have hX_dist := hX.nonoverlapping a v ha hv
  contrapose! hX_dist
  use hX_dist, ha_dist

theorem biUnion_inter_balls_subset_biUnion_balls_inter (r R : ℝ) :
    ⋃ x ∈ X ∩ ball 0 R, ball x r ⊆ (⋃ x ∈ X, ball x r) ∩ ball 0 (R + r) := by
  intro x hx
  simp at hx ⊢
  obtain ⟨y, ⟨hy₁, hy₂⟩⟩ := hx
  use ⟨y, ⟨hy₁.left, hy₂⟩⟩
  apply lt_of_le_of_lt <| norm_le_norm_add_norm_sub' x y
  gcongr <;> tauto

theorem biUnion_balls_inter_subset_biUnion_inter_balls (r R : ℝ) :
    (⋃ x ∈ X, ball x r) ∩ ball 0 (R - r) ⊆ ⋃ x ∈ X ∩ ball 0 R, ball x r := by
  intro x hx
  simp at hx ⊢
  obtain ⟨⟨y, ⟨hy₁, hy₂⟩⟩, hx⟩ := hx
  use y, ⟨hy₁, ?_⟩, hy₂
  calc
    ‖y‖ ≤ ‖x‖ + ‖y - x‖ := norm_le_norm_add_norm_sub' y x
    _ = ‖x‖ + dist x y := by rw [dist_comm]; rfl
    _ < R - r + r := by gcongr
    _ = R := by ring

theorem volume_iUnion_balls_eq_tsum (hr : 0 < r) (R : ℝ) {r' : ℝ} (hr' : r' ≤ r / 2) :
    volume (⋃ x : ↑(X ∩ ball 0 R), ball (x : EuclideanSpace ℝ (Fin d)) r')
      = ∑' x : ↑(X ∩ ball 0 R), volume (ball (x : EuclideanSpace ℝ (Fin d)) r') := by
  have : DiscreteTopology X := instDiscreteX _ _ hr
  have : Countable X := countable_of_Lindelof_of_discrete
  have : Countable ↑(X ∩ ball 0 R) := Set.Countable.mono (Set.inter_subset_left) this
  apply measure_iUnion ?_ (fun _ ↦ measurableSet_ball)
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  apply ball_disjoint_ball
  simp_rw [ne_eq, Subtype.mk.injEq] at h ⊢
  change _ ≤ ‖x - y‖
  linarith [hX.nonoverlapping x y hx.left hy.left h]

-- https://github.com/leanprover-community/mathlib4/pull/15214/files
-- Putting it as axioms so that #print axioms will show that this should be removed
-- TODO: remove when merged
axiom ENNReal.tsum_const_eq' {α : Type*} (s : Set α) (c : ENNReal) :
    ∑' (_ : s), c = s.encard * c

/-- This gives an upper bound on the number of points in the sphere packing X with norm less than R.
-/
theorem inter_ball_encard_le (hd : 0 < d) (hr : 0 < r) (R : ℝ) :
    (X ∩ ball 0 R).encard ≤
      volume ((⋃ (x : X), ball (x : V) (r / 2)) ∩ ball 0 (R + r / 2))
        / volume (ball (0 : V) (r / 2)) := by
  have h := volume.mono <| biUnion_inter_balls_subset_biUnion_balls_inter X (r / 2) R
  change volume _ ≤ volume _ at h
  simp_rw [Set.biUnion_eq_iUnion, volume_iUnion_balls_eq_tsum X r hr _ (le_refl _),
    Measure.addHaar_ball_center, ENNReal.tsum_const_eq'] at h
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rwa [← ENNReal.le_div_iff_mul_le] at h <;> left
  · exact (volume_ball_pos _ (by linarith)).ne.symm
  · exact (volume_ball_lt_top _).ne

/-- This gives an upper bound on the number of points in the sphere packing X with norm less than R.
-/
theorem inter_ball_encard_ge (hd : 0 < d) (hr : 0 < r) (R : ℝ) :
    (X ∩ ball 0 R).encard ≥
      volume ((⋃ (x : X), ball (x : V) (r / 2)) ∩ ball 0 (R - r / 2))
        / volume (ball (0 : V) (r / 2)) := by
  have h := volume.mono <| biUnion_balls_inter_subset_biUnion_inter_balls X (r / 2) R
  change volume _ ≤ volume _ at h
  simp_rw [Set.biUnion_eq_iUnion, volume_iUnion_balls_eq_tsum X r hr _ (le_refl _),
    Measure.addHaar_ball_center, ENNReal.tsum_const_eq'] at h
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rwa [← ENNReal.div_le_iff_le_mul] at h <;> left
  · exact (volume_ball_pos _ (by linarith)).ne.symm
  · exact (volume_ball_lt_top _).ne

theorem aux6 (hr : 0 < r) (R : ℝ) : Finite ↑(X ∩ ball 0 R) := by
  apply Set.encard_lt_top_iff.mp
  by_cases hd : 0 < d
  · haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    apply ENat.toENNReal_lt.mp
    apply lt_of_le_of_lt (inter_ball_encard_le X r hd hr R)
    apply ENNReal.div_lt_top ?_ (volume_ball_pos _ (by linarith)).ne.symm
    rw [← lt_top_iff_ne_top]
    calc
      _ ≤ volume (ball 0 (R + r / 2)) := volume.mono Set.inter_subset_right
      _ < ⊤ := EuclideanSpace.volume_ball_lt_top _
  · rw [not_lt, nonpos_iff_eq_zero] at hd
    have : (ball (0 : EuclideanSpace ℝ (Fin 0)) R).encard ≤ 1 := by
      rw [← Set.Finite.cast_ncard_eq (Set.toFinite _), Nat.cast_le_one]
      exact Set.ncard_le_one_of_subsingleton _
    subst hd
    apply lt_of_le_of_lt (Set.encard_mono inf_le_right)
    apply lt_of_le_of_lt this (by decide)

theorem finite_density_lower_bound [DiscreteTopology X] (hd : 0 < d) (hr : 0 < r) :
    FiniteDensity d X r R
      ≥ (X ∩ ball 0 (R - r / 2)).encard * volume (ball (0 : V) (r / 2))
        / volume (ball (0 : V) R) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [FiniteDensity, Packing_of_Centres, Set.biUnion_eq_iUnion]
  apply ENNReal.div_le_div_right
  rw [← ENNReal.le_div_iff_mul_le] <;> try left
  · have := inter_ball_encard_le X _ hd hr (R - r / 2)
    rwa [sub_add_cancel] at this
  · exact (volume_ball_pos _ (by linarith)).ne.symm
  · exact (volume_ball_lt_top _).ne

theorem finite_density_upper_bound [DiscreteTopology X] (hd : 0 < d) (hr : 0 < r) :
    FiniteDensity d X r R
      ≤ (X ∩ ball 0 (R + r / 2)).encard * volume (ball (0 : V) (r / 2))
        / volume (ball (0 : V) R) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [FiniteDensity, Packing_of_Centres, Set.biUnion_eq_iUnion]
  apply ENNReal.div_le_div_right
  rw [← ENNReal.div_le_iff_le_mul] <;> try left
  · have := inter_ball_encard_ge X _ hd hr (R + r / 2)
    rwa [add_sub_cancel_right] at this
  · exact (volume_ball_pos _ (by linarith)).ne.symm
  · exact (volume_ball_lt_top _).ne

example : volume (ball (0 : EuclideanSpace ℝ (Fin 8)) (√2 / 2))
    = ENNReal.ofReal (Real.pi ^ 4 / 384) := by
  have h₁ : √2 ^ 8 = 16 := by
    trans (√2 ^ 2) ^ 4
    · rw [← pow_mul]
    · norm_num
  have h₂ : √Real.pi ^ 8 = Real.pi ^ 4 := by
    trans (√Real.pi ^ 2) ^ 4
    · rw [← pow_mul]
    · rw [Real.sq_sqrt Real.pi_nonneg]
  have h₃ : Nat.factorial 4 = 24 := by
    decide
  rw [volume_ball, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul] <;> try positivity
  norm_num
  rw [h₁, h₂, h₃]
  congr 1
  ring_nf

open scoped Topology NNReal
open Asymptotics Filter ENNReal

private lemma aux {ε : ℝ≥0∞} (hε : 0 < ε) (hd : 0 < d) :
    ∃ k : ℝ, k ≥ 0 ∧ ∀ k' ≥ k, ENNReal.ofReal ((k' / (k' + 1)) ^ d) ∈ Set.Icc (1 - ε) (1 + ε) := by
  -- wtf
  by_cases hε' : ε = ⊤
  · use 0
    subst hε'
    simp
  · have : ∃ t : ℝ, 0 < t ∧ ε = ENNReal.ofReal t := by
      obtain ⟨⟨t, ht_nonneg⟩, rfl⟩ := Option.ne_none_iff_exists'.mp hε'
      rw [ENNReal.some_eq_coe, ENNReal.coe_pos] at hε
      use t, hε, (ENNReal.ofReal_eq_coe_nnreal ht_nonneg).symm
    obtain ⟨t, ht_pos, rfl⟩ := this
    by_cases ht : t ≤ 1
    · have hd' : (d : ℝ) ≠ 0 := by rw [ne_eq, Nat.cast_eq_zero]; exact Nat.not_eq_zero_of_lt hd
      let K : ℝ := 1 / (1 - (1 - t) ^ (1 / (d : ℝ))) - 1
      have hK : 0 ≤ K := by
        simp_rw [K]
        apply sub_nonneg.mpr
        apply one_le_one_div
        · rw [sub_pos]
          apply Real.rpow_lt_one
          · linarith
          · linarith
          · exact one_div_pos.mpr <| Nat.cast_pos'.mpr hd
        · rw [sub_le_self_iff]
          apply Real.rpow_nonneg
          linarith
      use K, hK
      intro k' hk'
      have : 1 - 1 / (k' + 1) ≥ 1 - 1 / (K + 1) := by
        gcongr
      have hK' : (k' / (k' + 1)) ^ d ≥ 1 - t := calc
        -- (K / (K + 1)) ^ d = (1 - 1 / (K + 1)) ^ d := by
        (k' / (k' + 1)) ^ d = (1 - 1 / (k' + 1)) ^ d := by
          congr
          rw [eq_sub_iff_add_eq, div_add_div_same, div_self]
          linarith
        _ ≥ (1 - 1 / (K + 1)) ^ d := by
          gcongr
          rw [sub_nonneg, one_div_le, div_one]
          · linarith
          · linarith
          · linarith
        _ = ((1 - t) ^ (1 / (d : ℝ))) ^ d := by simp [K]
        _ = 1 - t := by
          rw [← Real.rpow_mul_natCast (by linarith), one_div_mul_cancel hd', Real.rpow_one]
      rw [Set.mem_Icc, tsub_le_iff_right, ← ENNReal.ofReal_add]
      · constructor
        · apply ENNReal.one_le_ofReal.mpr
          linarith
        · trans 1
          · apply ENNReal.ofReal_le_one.mpr
            apply pow_le_one
            · apply div_nonneg
              · linarith
              · linarith
            · apply (div_le_one _).mpr
              · linarith
              · linarith
          · exact le_self_add
      · linarith
      · linarith
    · use 0, le_refl 0
      intro k' hk'
      have : 0 ≤ k' ^ d / (k' + 1) ^ d := by
        apply div_nonneg
        · apply pow_nonneg
          linarith
        · apply pow_nonneg
          linarith
      have : k' ^ d / (k' + 1) ^ d ≤ 1 := by
        apply (div_le_one _).mpr
        · apply pow_le_pow_left
          · linarith
          · linarith
        · apply pow_pos
          linarith
      rw [not_le] at ht
      rw [div_pow, Set.mem_Icc, tsub_le_iff_right]
      constructor
      · rw [← ENNReal.ofReal_add, ENNReal.one_le_ofReal]
        · linarith
        · linarith
        · linarith
      · trans 1
        · exact ENNReal.ofReal_le_one.mpr this
        · apply le_self_add

theorem volume_ball_ratio_tendsto_nhds_one {C : ℝ} (hd : 0 < d) (hC : 0 < C) :
    Tendsto (fun R ↦ volume (ball (0 : V d) R) / volume (ball (0 : V d) (R + C))) atTop (𝓝 1) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have (R : ℝ) (hR : 0 ≤ R) : volume (ball (0 : V d) R) / volume (ball (0 : V d) (R + C))
      = ENNReal.ofReal (R ^ d / (R + C) ^ d) := by
    rw [volume_ball, volume_ball, Fintype.card_fin, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_div_of_pos, mul_div_mul_right]
    <;> positivity
  rw [ENNReal.tendsto_atTop (by decide)]
  intro ε hε
  obtain ⟨k, ⟨hk₁, hk₂⟩⟩ := aux hε hd
  use k * C
  intro n hn
  specialize hk₂ (n / C) ((le_div_iff hC).mpr hn)
  -- boring
  rw [this]
  · convert hk₂
    rw [← div_pow]
    congr 1
    rw [div_eq_div_iff]
    · rw [mul_add, mul_add, ← mul_div_assoc, mul_one, div_mul_cancel₀, mul_div_right_comm]
      exact hC.ne.symm
    · apply ne_of_gt
      calc
        n + C ≥ k * C + C := by gcongr
        _ > 0 := by positivity
    · apply ne_of_gt
      calc
        n / C + 1 ≥ k * C / C + 1 := by gcongr
        _ = k + 1 := by rw [mul_div_cancel_right₀ _ hC.ne.symm]
        _ > 0 := by linarith
  · exact (by positivity : 0 ≤ k * C).trans hn

end BasicResults

end SpherePacking
