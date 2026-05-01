module
public import SpherePacking.Basic.PeriodicPacking.Aux

/-!
# Periodic packings: Theorem 2.2 (blueprint)
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
  .mk' (μ := volume) hD_measurable.nullMeasurableSet hD_unique_covers

private theorem ball_subset_iUnion_lattice_inter_ball_vadd
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    ball 0 (R - L) ⊆ ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D) := by
  intro x hx
  obtain ⟨g, hg, -⟩ := hD_unique_covers x
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_inter_iff]
  refine ⟨-g.val, ⟨⟨by simp, ?_⟩, Set.mem_vadd_set_iff_neg_vadd_mem.2 (by simpa using hg)⟩⟩
  simpa [mem_ball_zero_iff, norm_neg] using lt_of_le_of_lt
    (by simpa [sub_eq_add_neg, add_assoc] using norm_sub_le (a := g.val + x) (b := x) :
      ‖g.val‖ ≤ ‖g.val + x‖ + ‖x‖) <| by
    linarith [hL _ (by simpa using hg : g.val + x ∈ D), mem_ball_zero_iff.mp hx]

/-- An add-left-invariant measure is invariant under translations by a submodule. -/
public instance (E : Type*) [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E] [Module ℤ E]
    [Module ℝ E] (μ : Measure E) [μ.IsAddLeftInvariant] [IsScalarTower ℤ ℝ E] (s : Submodule ℤ E) :
    VAddInvariantMeasure s E μ :=
  ⟨fun _ _ _ => by simp [Submodule.vadd_def, measure_preimage_add]⟩

private lemma measure_biUnion_lattice_inter_ball_vadd
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D) :
    volume (⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D)) =
      (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard * volume D := by
  have : Countable ↑(↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
    Set.Countable.mono Set.inter_subset_left (inferInstance : Countable ↑S.lattice)
  rw [Set.biUnion_eq_iUnion, measure_iUnion]
  · rw [tsum_congr fun i ↦ measure_vadd .., ENNReal.tsum_set_const]
  · exact fun i j hij => by
      simpa using disjoint_vadd_of_unique_covers (d := d) (Λ := S.lattice) (D := D)
        hD_unique_covers (fun h => hij <|
          Subtype.ext <| congrArg (fun u : S.lattice => (u : EuclideanSpace ℝ (Fin d))) h :
          (⟨i.1, i.2.1⟩ : S.lattice) ≠ ⟨j.1, j.2.1⟩)
  · exact fun i => hD_measurable.const_vadd i.1

/-- Theorem 2.2, lower bound. -/
theorem PeriodicSpherePacking.aux2_ge
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
    (hL : ∀ x ∈ D, ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L)) / volume D := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [ge_iff_le, ENNReal.div_le_iff
    ((hD_isAddFundamentalDomain S D ‹_› ‹_›).measure_ne_zero (NeZero.ne volume))
    (lt_top_iff_ne_top.mp <|
      Bornology.IsBounded.measure_lt_top (isBounded_iff_forall_norm_le.mpr ⟨L, hL⟩)),
    ← measure_biUnion_lattice_inter_ball_vadd S D R hD_unique_covers hD_measurable]
  exact volume.mono <| ball_subset_iUnion_lattice_inter_ball_vadd S D R hD_unique_covers hL

private theorem iUnion_lattice_inter_ball_vadd_subset_ball (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D) ⊆ ball 0 (R + L) := by
  intro x hx
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_inter_iff, mem_ball_zero_iff] at hx ⊢
  obtain ⟨i, ⟨-, hi_ball⟩, hi_mem⟩ := hx
  exact lt_of_le_of_lt ((show ‖x‖ = ‖i + (-i + x)‖ by congr; abel).le.trans (norm_add_le _ _))
    (add_lt_add_of_lt_of_le hi_ball (hL _ (Set.mem_vadd_set_iff_neg_vadd_mem.mp hi_mem)))

/-- Theorem 2.2, upper bound. -/
theorem PeriodicSpherePacking.aux2_le
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
    (hL : ∀ x ∈ D, ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)) / volume D := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [ENNReal.le_div_iff_mul_le (.inl <| (hD_isAddFundamentalDomain S D ‹_› ‹_›).measure_ne_zero
    (NeZero.ne volume)) (.inl <| lt_top_iff_ne_top.mp <|
      Bornology.IsBounded.measure_lt_top (isBounded_iff_forall_norm_le.mpr ⟨L, hL⟩)),
    ← measure_biUnion_lattice_inter_ball_vadd S D R hD_unique_covers hD_measurable]
  exact volume.mono <| iUnion_lattice_inter_ball_vadd_subset_ball S D R hL

variable (b : Basis ι ℤ S.lattice)

private lemma fundamentalDomain_unique_covers (x : EuclideanSpace ℝ (Fin d)) :
    ∃! g : S.lattice, g +ᵥ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) := by
  obtain ⟨⟨v, hv⟩, hvD, hvuniq⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  exact ⟨⟨v, by simpa [S.basis_Z_span] using hv⟩, hvD, fun ⟨y, hy⟩ hyD => Subtype.ext <| by
    simpa using congrArg Subtype.val (hvuniq ⟨y, by simpa [S.basis_Z_span] using hy⟩ hyD)⟩

/-- Theorem 2.2 lower bound, in terms of fundamental domain of Z-lattice. -/
public theorem PeriodicSpherePacking.aux2_ge'
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
  S.aux2_ge _ R (fundamentalDomain_unique_covers S b) (fundamentalDomain_measurableSet _) hL hd

/-- Theorem 2.2 upper bound, in terms of fundamental domain of Z-lattice. -/
public theorem PeriodicSpherePacking.aux2_le'
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
  S.aux2_le _ R (fundamentalDomain_unique_covers S b) (fundamentalDomain_measurableSet _) hL hd

section finiteDensity_limit

open Measure

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
    gcongr; simpa using ENat.toENNReal_le.mpr (S.aux_le hd b hL _)
  _ ≤ S.numReps
        * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L + L))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))
            * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    rw [nsmul_eq_mul]; gcongr; exact S.aux2_le' _ b hL hd
  _ = S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, mul_two, ← add_assoc, ← ENNReal.mul_div_right_comm,
      ← ENNReal.mul_div_right_comm, mul_assoc, mul_assoc, mul_comm (volume _) (volume _)]

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
    gcongr; simpa using ENat.toENNReal_le.mpr (S.aux_ge hd b hL _)
  _ ≥ S.numReps
        * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L - L))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))
            * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    rw [nsmul_eq_mul]; gcongr; exact S.aux2_ge' _ b hL hd
  _ = S.numReps
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, mul_two, ← sub_sub, ← ENNReal.mul_div_right_comm,
      ← ENNReal.mul_div_right_comm, mul_assoc, mul_assoc, mul_comm (volume _) (volume _)]

open Filter Topology

section VolumeBallRatio

open ENNReal

lemma aux_bhavik {d : ℝ} {ε : ℝ≥0∞} (hd : 0 ≤ d) (hε : 0 < ε) :
    ∃ k : ℝ, k ≥ 0 ∧ ∀ k' ≥ k, ENNReal.ofReal ((k' / (k' + 1)) ^ d) ∈ Set.Icc (1 - ε) (1 + ε) := by
  obtain ⟨k, hk⟩ := (ENNReal.tendsto_atTop (by simp)).mp
    (Tendsto.ennrpow_const d <| tendsto_ofReal <| Tendsto.const_sub 1 <|
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_id) :
      Filter.Tendsto (fun k => (ENNReal.ofReal (1 - (k + 1)⁻¹) ^ d)) atTop
        (𝓝 (ENNReal.ofReal (1 - 0) ^ d))) ε hε
  refine ⟨max 0 k, by simp, fun k' hk' => ?_⟩
  obtain ⟨hk₀, hk₁⟩ := max_le_iff.mp hk'
  have := hk k' hk₁
  rwa [sub_zero, ofReal_one, one_rpow, ← one_div, one_sub_div, add_sub_cancel_right,
    ENNReal.ofReal_rpow_of_nonneg] at this <;> positivity

/--
As `R → ∞`, the ratio `volume (ball 0 R) / volume (ball 0 (R + C))` tends to `1` (for `C ≥ 0`).
-/
public theorem volume_ball_ratio_tendsto_nhds_one {C : ℝ} (hd : 0 < d) (hC : 0 ≤ C) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))) atTop (𝓝 1) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rcases le_iff_eq_or_lt.mp hC with (rfl | hC)
  · exact Tendsto.congr' (f₁ := 1) (eventually_atTop.mpr ⟨1, fun b hb => by
      simp [add_zero, ENNReal.div_self (Metric.measure_ball_pos volume _
        (by linarith)).ne.symm (MeasureTheory.measure_ball_lt_top (μ := volume)).ne]⟩)
      tendsto_const_nhds
  · have hfmt (R : ℝ) (hR : 0 ≤ R) : volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
          = ENNReal.ofReal (R ^ d / (R + C) ^ d) := by
      rw [volume_ball, volume_ball, Fintype.card_fin, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul,
        ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_div_of_pos,
        mul_div_mul_right] <;> positivity
    rw [ENNReal.tendsto_atTop (by decide)]
    intro ε hε
    obtain ⟨k, _, hk₂⟩ : ∃ k : ℝ, k ≥ 0 ∧ ∀ k' ≥ k,
        ENNReal.ofReal ((k' / (k' + 1)) ^ d) ∈ Set.Icc (1 - ε) (1 + ε) := by
      simpa using aux_bhavik (Nat.cast_nonneg d) hε
    refine ⟨k * C, fun n hn => ?_⟩
    rw [hfmt _ ((by positivity : 0 ≤ k * C).trans hn)]
    convert hk₂ (n / C) ((le_div_iff₀ hC).mpr hn)
    rw [div_add_one, div_div_div_cancel_right₀, div_pow] <;> positivity

/--
As `R → ∞`, the ratio `volume (ball 0 (R + C)) / volume (ball 0 (R + C'))` tends to `1`
for nonnegative constants `C` and `C'`.
-/
public theorem volume_ball_ratio_tendsto_nhds_one'
    {d : ℕ} {C C' : ℝ} (hd : 0 < d) (hC : 0 ≤ C) (hC' : 0 ≤ C') :
      Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) atTop (𝓝 1) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  refine Tendsto.congr' (f₁ := fun R ↦
    volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))
        / (volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))))
    (eventually_atTop.mpr ⟨1, fun R hR => ENNReal.div_div_div_cancel_left
      (Metric.measure_ball_pos volume _ (lt_of_lt_of_le zero_lt_one hR)).ne.symm
      (MeasureTheory.measure_ball_lt_top (μ := volume)).ne
      (MeasureTheory.measure_ball_lt_top (μ := volume)).ne⟩) ?_
  convert ENNReal.Tendsto.div (volume_ball_ratio_tendsto_nhds_one hd hC') ?_
    (volume_ball_ratio_tendsto_nhds_one hd hC) ?_ <;> simp

/--
Shifting the argument by a constant does not change convergence to `atTop`.
-/
public theorem Filter.map_add_atTop_eq' {β : Type*} {f : ℝ → β} (C : ℝ) (α : Filter β) :
    Tendsto f atTop α ↔ Tendsto (fun x ↦ f (x + C)) atTop α := by
  have hmap : Filter.map (fun x : ℝ => x + C) atTop = atTop := by
    simpa using Filter.map_add_atTop_eq (α := ℝ) (k := C)
  exact ⟨fun hf => tendsto_map'_iff.mp (by simpa [hmap]), fun hf => by simpa [hmap] using
    (tendsto_map'_iff.mpr hf : Tendsto f (Filter.map (fun x : ℝ => x + C) atTop) α)⟩

/--
As `R → ∞`, the ratio `volume (ball 0 (R + C)) / volume (ball 0 (R + C'))` tends to `1`,
without assuming signs on `C` and `C'`.
-/
public theorem volume_ball_ratio_tendsto_nhds_one'' {d : ℕ} {C C' : ℝ} (hd : 0 < d) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) atTop (𝓝 1) := by
  refine (Filter.map_add_atTop_eq' (f := fun R ↦
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C)) /
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) (max (-C) (-C')) _).mpr ?_
  simpa [add_assoc] using volume_ball_ratio_tendsto_nhds_one' (d := d)
    (C := max (-C) (-C') + C) (C' := max (-C) (-C') + C') hd
    (by linarith [le_max_left (-C) (-C')]) (by linarith [le_max_right (-C) (-C')])

end VolumeBallRatio
end finiteDensity_limit
end theorem_2_2
