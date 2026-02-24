module
public import SpherePacking.Basic.PeriodicPacking.Aux

/-!
# Periodic packings: Theorem 2.2 (blueprint)

This file proves Theorem 2.2 from the blueprint. Under a strengthened "unique cover" hypothesis on a
measurable set `D` (every point has a unique translate in `D`), we obtain two-sided volume bounds
for the lattice point count `(↑S.lattice ∩ ball 0 R).encard`.

These bounds are then turned into upper and lower estimates for `S.finiteDensity R` (the lemmas
`aux_big_le` and `aux_big_ge`) and convergence statements for ratios of ball volumes as `R → ∞`.
-/

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module

section theorem_2_2

/-! ## Theorem 2.2 -/

open scoped Pointwise
variable {d : ℕ} (S : PeriodicSpherePacking d)
  {ι : Type*} [Finite ι]
  (D : Set (EuclideanSpace ℝ (Fin d))) {L : ℝ} (R : ℝ)

theorem hD_isAddFundamentalDomain
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D) :
    IsAddFundamentalDomain S.lattice D :=
  MeasureTheory.IsAddFundamentalDomain.mk' (μ := volume) hD_measurable.nullMeasurableSet
    hD_unique_covers

private theorem ball_subset_iUnion_lattice_inter_ball_vadd
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    ball 0 (R - L) ⊆ ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D) := by
  intro x hx
  have hx' : ‖x‖ < R - L := by simpa [mem_ball_zero_iff] using hx
  rcases hD_unique_covers x with ⟨g, hg, -⟩
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_inter_iff]
  refine ⟨-g.val, ⟨⟨by simp, ?_⟩, ?_⟩⟩
  · have : ‖g.val‖ < R := by
      have htri : ‖g.val‖ ≤ ‖g.val + x‖ + ‖x‖ := by
        simpa [sub_eq_add_neg, add_assoc] using (norm_sub_le (a := g.val + x) (b := x))
      refine lt_of_le_of_lt htri ?_
      calc
        ‖g.val + x‖ + ‖x‖ < L + (R - L) := add_lt_add_of_le_of_lt (hL _ (by simpa using hg)) hx'
        _ = R := by abel
    simpa [mem_ball_zero_iff, norm_neg] using this
  · exact (Set.mem_vadd_set_iff_neg_vadd_mem).2 (by simpa using hg)

/--
An add-left-invariant measure is invariant under translations by a submodule.

This is used to package translation invariance in the volume computations for Theorem 2.2.
-/
public instance (E : Type*) [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E] [Module ℤ E]
    [Module ℝ E] (μ : Measure E) [μ.IsAddLeftInvariant] [IsScalarTower ℤ ℝ E] (s : Submodule ℤ E) :
    VAddInvariantMeasure s E μ where
  measure_preimage_vadd c t ht := by
    simp only [Submodule.vadd_def, vadd_eq_add, measure_preimage_add]

-- Theorem 2.2, lower bound
theorem PeriodicSpherePacking.aux2_ge
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
    (hL : ∀ x ∈ D, ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L)) / volume D := by
  rw [ge_iff_le, ENNReal.div_le_iff]
  · convert volume.mono <| ball_subset_iUnion_lattice_inter_ball_vadd S D R hD_unique_covers hL
    rw [OuterMeasure.measureOf_eq_coe, Measure.coe_toOuterMeasure]
    have : Countable ↑S.lattice := inferInstance
    have : Countable ↑(↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
      Set.Countable.mono (Set.inter_subset_left) this
    rw [Set.biUnion_eq_iUnion, measure_iUnion]
    · rw [tsum_congr fun i ↦ measure_vadd .., ENNReal.tsum_set_const]
    · intro i j hij
      have hgh : (⟨i.1, i.2.1⟩ : S.lattice) ≠ ⟨j.1, j.2.1⟩ := by
        intro h
        exact hij <| Subtype.ext <|
          congrArg (fun u : S.lattice => (u : EuclideanSpace ℝ (Fin d))) h
      simpa using
        disjoint_vadd_of_unique_covers (d := d) (Λ := S.lattice) (D := D) hD_unique_covers hgh
    · exact fun i => MeasurableSet.const_vadd hD_measurable i.1
  · exact (hD_isAddFundamentalDomain S D ‹_› ‹_›).measure_ne_zero (NeZero.ne volume)
  · have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    rw [← lt_top_iff_ne_top]
    exact Bornology.IsBounded.measure_lt_top (isBounded_iff_forall_norm_le.mpr ⟨L, hL⟩)

private theorem iUnion_lattice_inter_ball_vadd_subset_ball (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D) ⊆ ball 0 (R + L) := by
  intro x hx
  rw [mem_ball_zero_iff]
  rcases (by simpa [Set.mem_iUnion, exists_prop, Set.mem_inter_iff] using hx) with
    ⟨i, ⟨-, hi_ball⟩, hi_mem⟩
  have hi_ball' : ‖i‖ < R := by simpa [mem_ball_zero_iff] using hi_ball
  have hi_mem' : ‖-i + x‖ ≤ L := hL _ (Set.mem_vadd_set_iff_neg_vadd_mem.mp hi_mem)
  calc
    _ = ‖i + (-i + x)‖ := by congr; abel
    _ ≤ ‖i‖ + ‖-i + x‖ := norm_add_le _ _
    _ < R + L := add_lt_add_of_lt_of_le hi_ball' hi_mem'

-- Theorem 2.2, upper bound
theorem PeriodicSpherePacking.aux2_le
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
    (hL : ∀ x ∈ D, ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)) / volume D := by
  rw [ENNReal.le_div_iff_mul_le]
  · convert volume.mono <| iUnion_lattice_inter_ball_vadd_subset_ball S D R hL
    rw [OuterMeasure.measureOf_eq_coe, Measure.coe_toOuterMeasure]
    have : Countable ↑S.lattice := inferInstance
    have : Countable ↑(↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
      Set.Countable.mono (Set.inter_subset_left) this
    rw [Set.biUnion_eq_iUnion, measure_iUnion]
    · rw [tsum_congr fun i ↦ measure_vadd .., ENNReal.tsum_set_const]
    · intro i j hij
      have hgh : (⟨i.1, i.2.1⟩ : S.lattice) ≠ ⟨j.1, j.2.1⟩ := by
        intro h
        exact hij <| Subtype.ext <|
          congrArg (fun u : S.lattice => (u : EuclideanSpace ℝ (Fin d))) h
      simpa using
        disjoint_vadd_of_unique_covers (d := d) (Λ := S.lattice) (D := D) hD_unique_covers hgh
    · exact fun i => MeasurableSet.const_vadd hD_measurable i.1
  · left
    exact (hD_isAddFundamentalDomain S D ‹_› ‹_›).measure_ne_zero (NeZero.ne volume)
  · left
    have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    rw [← lt_top_iff_ne_top]
    exact Bornology.IsBounded.measure_lt_top (isBounded_iff_forall_norm_le.mpr ⟨L, hL⟩)

open ZSpan

variable (b : Basis ι ℤ S.lattice)

-- Theorem 2.2 lower bound, in terms of fundamental domain of Z-lattice
public theorem PeriodicSpherePacking.aux2_ge'
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  refine S.aux2_ge _ R ?_ (fundamentalDomain_measurableSet _) hL hd
  intro x
  obtain ⟨⟨v, hv⟩, hv'⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  simp only [S.basis_Z_span] at hv hv' ⊢
  use ⟨v, hv⟩, hv'.left, ?_
  intro ⟨y, hy⟩ hy'
  have := hv'.right ⟨y, ?_⟩ hy'
  · rwa [Subtype.ext_iff] at this ⊢
  · simpa [S.basis_Z_span] using hy

-- Theorem 2.2 upper bound, in terms of fundamental domain of Z-lattice
public theorem PeriodicSpherePacking.aux2_le'
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  refine S.aux2_le _ R ?_ (fundamentalDomain_measurableSet _) hL hd
  intro x
  obtain ⟨⟨v, hv⟩, hv'⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  simp only [S.basis_Z_span] at hv hv' ⊢
  use ⟨v, hv⟩, hv'.left, ?_
  intro ⟨y, hy⟩ hy'
  have := hv'.right ⟨y, ?_⟩ hy'
  · rwa [Subtype.ext_iff] at this ⊢
  · simpa [S.basis_Z_span] using hy

section finiteDensity_limit

open MeasureTheory Measure Metric ZSpan

variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

/--
Upper bound for `S.finiteDensity R` in terms of a fundamental domain, up to a ball-volume ratio.
-/
public theorem aux_big_le
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.finiteDensity R ≤
      S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := calc
  _ ≤ (S.centers ∩ ball 0 (R + S.separation / 2)).encard
      * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
    S.finiteDensity_le hd R
  _ ≤ S.numReps
        • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L)).encard
          * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
            / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    gcongr
    simpa using ENat.toENNReal_le.mpr (S.aux_le hd b hL _)
  _ ≤ S.numReps
        * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L + L))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))
            * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    rw [nsmul_eq_mul]
    gcongr
    exact S.aux2_le' _ b hL hd
  _ = S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, mul_two, ← add_assoc, ← ENNReal.mul_div_right_comm,
      ← ENNReal.mul_div_right_comm, mul_assoc, mul_assoc]
    congr 3
    rw [mul_comm]

/--
Lower bound for `S.finiteDensity R` in terms of a fundamental domain, up to a ball-volume ratio.
-/
public theorem aux_big_ge
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.finiteDensity R ≥
      S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := calc
  _ ≥ (S.centers ∩ ball 0 (R - S.separation / 2)).encard
      * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
    S.finiteDensity_ge hd R
  _ ≥ S.numReps
        • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L)).encard
          * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
            / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    gcongr
    simpa using ENat.toENNReal_le.mpr (S.aux_ge hd b hL _)
  _ ≥ S.numReps
        * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L - L))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))
            * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    rw [nsmul_eq_mul]
    gcongr
    exact S.aux2_ge' _ b hL hd
  _ = S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, mul_two, ← sub_sub, ← ENNReal.mul_div_right_comm,
      ← ENNReal.mul_div_right_comm, mul_assoc, mul_assoc]
    congr 3
    rw [mul_comm]

open Filter Topology

section VolumeBallRatio

open scoped Topology NNReal
open Asymptotics Filter ENNReal EuclideanSpace

-- Credits to Bhavik Mehta for this <3 my original code is 92 lines long x)
lemma aux_bhavik {d : ℝ} {ε : ℝ≥0∞} (hd : 0 ≤ d) (hε : 0 < ε) :
    ∃ k : ℝ, k ≥ 0 ∧ ∀ k' ≥ k, ENNReal.ofReal ((k' / (k' + 1)) ^ d) ∈ Set.Icc (1 - ε) (1 + ε) := by
  suffices Filter.Tendsto
      (fun k => (ENNReal.ofReal (1 - (k + 1)⁻¹) ^ d)) atTop (𝓝 (ENNReal.ofReal (1 - 0) ^ d)) by
    rw [ENNReal.tendsto_atTop (by simp)] at this
    obtain ⟨k, hk⟩ := this ε hε
    refine ⟨max 0 k, by simp, ?_⟩
    simp only [ge_iff_le, max_le_iff, and_imp]
    intro k' hk₀ hk₁
    have := hk k' hk₁
    rwa [sub_zero, ofReal_one, one_rpow, ←one_div, one_sub_div, add_sub_cancel_right,
      ENNReal.ofReal_rpow_of_nonneg] at this
    · positivity
    · positivity
    · positivity
  refine Tendsto.ennrpow_const d (tendsto_ofReal (Tendsto.const_sub 1 ?_))
  exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)

lemma aux_bhavik' {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ k : ℝ, k ≥ 0 ∧ ∀ k' ≥ k, ENNReal.ofReal ((k' / (k' + 1)) ^ d) ∈ Set.Icc (1 - ε) (1 + ε) := by
  simpa using aux_bhavik (d := d) (Nat.cast_nonneg _) hε

/--
As `R → ∞`, the ratio `volume (ball 0 R) / volume (ball 0 (R + C))` tends to `1` (for `C ≥ 0`).
-/
public theorem volume_ball_ratio_tendsto_nhds_one {C : ℝ} (hd : 0 < d) (hC : 0 ≤ C) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))) atTop (𝓝 1) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rcases le_iff_eq_or_lt.mp hC with (rfl | hC)
  · simp_rw [add_zero]
    apply Tendsto.congr' (f₁ := 1) ?_ tendsto_const_nhds
    rw [EventuallyEq, eventually_atTop]
    use 1
    intro b hb
    rw [ENNReal.div_self, Pi.one_apply]
    · exact (volume_ball_pos _ (by linarith)).ne.symm
    · exact (volume_ball_lt_top _).ne
  · have (R : ℝ) (hR : 0 ≤ R) : volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
          = ENNReal.ofReal (R ^ d / (R + C) ^ d) := by
      rw [volume_ball, volume_ball, Fintype.card_fin, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul,
        ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_div_of_pos, mul_div_mul_right]
      <;> positivity
    rw [ENNReal.tendsto_atTop (by decide)]
    intro ε hε
    obtain ⟨k, ⟨hk₁, hk₂⟩⟩ := aux_bhavik' (d := d) hε
    use k * C
    intro n hn
    rw [this _ ((by positivity : 0 ≤ k * C).trans hn)]
    convert hk₂ (n / C) ((le_div_iff₀ hC).mpr hn)
    rw [div_add_one, div_div_div_cancel_right₀, div_pow]
    · positivity
    · positivity

/--
As `R → ∞`, the ratio `volume (ball 0 (R + C)) / volume (ball 0 (R + C'))` tends to `1`
for nonnegative constants `C` and `C'`.
-/
public theorem volume_ball_ratio_tendsto_nhds_one'
    {d : ℕ} {C C' : ℝ} (hd : 0 < d) (hC : 0 ≤ C) (hC' : 0 ≤ C') :
      Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) atTop (𝓝 1) := by
  -- I love ENNReal (I don't)
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  apply Tendsto.congr' (f₁ := fun R ↦
    volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))
        / (volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))))
  · rw [EventuallyEq, eventually_atTop]
    use 1
    intro R hR
    have hR' : 0 < R := lt_of_lt_of_le zero_lt_one hR
    rw [ENNReal.div_div_div_cancel_left]
    · exact (volume_ball_pos _ hR').ne.symm
    · exact (volume_ball_lt_top _).ne
    · exact (volume_ball_lt_top _).ne
  · convert ENNReal.Tendsto.div (volume_ball_ratio_tendsto_nhds_one hd hC') ?_
      (volume_ball_ratio_tendsto_nhds_one hd hC) ?_ <;> simp

/--
Shifting the argument by a constant does not change convergence to `atTop`.
-/
public theorem Filter.map_add_atTop_eq' {β : Type*} {f : ℝ → β} (C : ℝ) (α : Filter β) :
    Tendsto f atTop α ↔ Tendsto (fun x ↦ f (x + C)) atTop α := by
  have hmap : Filter.map (fun x : ℝ => x + C) atTop = atTop := by
    simpa using (Filter.map_add_atTop_eq (α := ℝ) (k := C))
  constructor <;> intro hf
  · exact tendsto_map'_iff.mp (by simpa [hmap] using hf)
  · exact (by
      have : Tendsto f (Filter.map (fun x : ℝ => x + C) atTop) α := tendsto_map'_iff.mpr hf
      simpa [hmap] using this)

/--
As `R → ∞`, the ratio `volume (ball 0 (R + C)) / volume (ball 0 (R + C'))` tends to `1`,
without assuming signs on `C` and `C'`.
-/
public theorem volume_ball_ratio_tendsto_nhds_one'' {d : ℕ} {C C' : ℝ} (hd : 0 < d) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) atTop (𝓝 1) := by
  have hC₀ : 0 ≤ max (-C) (-C') + C := by linarith [le_max_left (-C) (-C')]
  have hC'₀ : 0 ≤ max (-C) (-C') + C' := by linarith [le_max_right (-C) (-C')]
  refine (Filter.map_add_atTop_eq' (f := fun R ↦
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C)) /
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) (max (-C) (-C')) _).mpr ?_
  simpa [add_assoc] using
    volume_ball_ratio_tendsto_nhds_one' (d := d) (C := max (-C) (-C') + C)
      (C' := max (-C) (-C') + C') hd hC₀ hC'₀

end VolumeBallRatio
end finiteDensity_limit
end theorem_2_2
