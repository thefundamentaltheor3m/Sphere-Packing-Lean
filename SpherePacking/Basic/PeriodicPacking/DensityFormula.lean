module
public import Mathlib.Order.Filter.Defs
public import SpherePacking.Basic.PeriodicPacking.Aux

/-!
# Periodic packings: Theorem 2.2 (blueprint) and density formula

Theorem 2.2 bounds, volume-ball-ratio limits, and the density formula for periodic sphere
packings: the density can be computed from a fundamental domain `D` as the number of centers in
`D` times the volume of a ball of radius `S.separation / 2`, divided by `volume D`.
-/

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module

/-- Cancel a common numerator in a ratio of `ENNReal` divisions.
If `a` is nonzero and finite, and `c` is finite, then `(a / b) / (a / c) = c / b`. -/
private theorem ENNReal.div_div_div_cancel_left {a b c : ENNReal} (ha : a ≠ 0) (ha' : a ≠ ⊤)
    (hc : c ≠ ⊤) : (a / b) / (a / c) = c / b := by
  by_cases hb : b = 0
  · simp [ha, hb, div_zero, top_div, div_eq_top, hc, ha']
    split_ifs with hct <;> simp [hct, eq_comm, div_eq_top]
  · rw [← ENNReal.toReal_eq_toReal_iff', ENNReal.toReal_div, ENNReal.toReal_div,
      ENNReal.toReal_div, ENNReal.toReal_div]
    · rw [div_div_div_cancel_left']
      rw [ne_eq, ENNReal.toReal_eq_zero_iff, not_or]; tauto
    · simp [*, ne_eq, ENNReal.div_eq_top]
    · simp [*, ne_eq, ENNReal.div_eq_top]

section theorem_2_2

open scoped Pointwise
variable {d : ℕ} (S : PeriodicSpherePacking d) {ι : Type*} [Finite ι]
  (D : Set (EuclideanSpace ℝ (Fin d))) {L : ℝ} (R : ℝ)

theorem hD_isAddFundamentalDomain (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hD_measurable : MeasurableSet D) : IsAddFundamentalDomain S.lattice D :=
  .mk' (μ := volume) hD_measurable.nullMeasurableSet hD_unique_covers

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

variable (b : Basis ι ℤ S.lattice)

private lemma fundamentalDomain_unique_covers (x : EuclideanSpace ℝ (Fin d)) :
    ∃! g : S.lattice, g +ᵥ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) :=
  let ⟨⟨v, hv⟩, hvD, hvuniq⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  ⟨⟨v, by simpa [S.basis_Z_span] using hv⟩, hvD, fun ⟨y, hy⟩ hyD => Subtype.ext <| by
    simpa using congrArg Subtype.val (hvuniq ⟨y, by simpa [S.basis_Z_span] using hy⟩ hyD)⟩

/-- Theorem 2.2 lower bound, in terms of fundamental domain of Z-lattice. -/
public theorem PeriodicSpherePacking.aux2_ge'
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  set D : Set (EuclideanSpace ℝ (Fin d)) := fundamentalDomain (b.ofZLatticeBasis ℝ _)
  have hD_unique_covers := fundamentalDomain_unique_covers S b
  have hD_measurable : MeasurableSet D := fundamentalDomain_measurableSet _
  rw [ge_iff_le, ENNReal.div_le_iff
    ((hD_isAddFundamentalDomain S D ‹_› ‹_›).measure_ne_zero (NeZero.ne volume))
    (Bornology.IsBounded.measure_lt_top (isBounded_iff_forall_norm_le.mpr ⟨L, hL⟩)).ne,
    ← measure_biUnion_lattice_inter_ball_vadd S D R hD_unique_covers hD_measurable]
  refine volume.mono fun x hx => ?_
  obtain ⟨g, hg, -⟩ := hD_unique_covers x
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_inter_iff]
  refine ⟨-g.val, ⟨⟨by simp, ?_⟩, Set.mem_vadd_set_iff_neg_vadd_mem.2 (by simpa using hg)⟩⟩
  simpa [mem_ball_zero_iff, norm_neg] using lt_of_le_of_lt
    (by simpa [sub_eq_add_neg, add_assoc] using norm_sub_le (a := g.val + x) (b := x) :
      ‖g.val‖ ≤ ‖g.val + x‖ + ‖x‖) (by
    linarith [hL _ (by simpa using hg : g.val + x ∈ D), mem_ball_zero_iff.mp hx])

/-- Theorem 2.2 upper bound, in terms of fundamental domain of Z-lattice. -/
public theorem PeriodicSpherePacking.aux2_le'
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  set D : Set (EuclideanSpace ℝ (Fin d)) := fundamentalDomain (b.ofZLatticeBasis ℝ _)
  have hD_unique_covers := fundamentalDomain_unique_covers S b
  have hD_measurable : MeasurableSet D := fundamentalDomain_measurableSet _
  rw [ENNReal.le_div_iff_mul_le (.inl <| (hD_isAddFundamentalDomain S D ‹_› ‹_›).measure_ne_zero
    (NeZero.ne volume)) (.inl <| (Bornology.IsBounded.measure_lt_top
      (isBounded_iff_forall_norm_le.mpr ⟨L, hL⟩)).ne),
    ← measure_biUnion_lattice_inter_ball_vadd S D R hD_unique_covers hD_measurable]
  refine volume.mono fun x hx => ?_
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_inter_iff, mem_ball_zero_iff] at hx ⊢
  obtain ⟨i, ⟨-, hi_ball⟩, hi_mem⟩ := hx
  exact lt_of_le_of_lt ((show ‖x‖ = ‖i + (-i + x)‖ by congr; abel).le.trans (norm_add_le _ _))
    (add_lt_add_of_lt_of_le hi_ball (hL _ (Set.mem_vadd_set_iff_neg_vadd_mem.mp hi_mem)))

section finiteDensity_limit

variable {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

/-- Upper bound for `S.finiteDensity R` in terms of a fundamental domain. -/
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

/-- Lower bound for `S.finiteDensity R` in terms of a fundamental domain. -/
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

/-- As `R → ∞`, `volume (ball 0 R) / volume (ball 0 (R + C))` → `1` for `C ≥ 0`. -/
public theorem volume_ball_ratio_tendsto_nhds_one {C : ℝ} (hd : 0 < d) (hC : 0 ≤ C) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))) atTop (𝓝 1) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rcases le_iff_eq_or_lt.mp hC with (rfl | hC)
  · exact Tendsto.congr' (f₁ := 1) (eventually_atTop.mpr ⟨1, fun b hb => by
      simp [add_zero, ENNReal.div_self (Metric.measure_ball_pos volume _
        (by linarith)).ne.symm (MeasureTheory.measure_ball_lt_top (μ := volume)).ne]⟩)
      tendsto_const_nhds
  have hfmt (R : ℝ) (hR : 0 ≤ R) : volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
        = ENNReal.ofReal (R ^ d / (R + C) ^ d) := by
    rw [volume_ball, volume_ball, Fintype.card_fin, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_div_of_pos,
      mul_div_mul_right] <;> positivity
  rw [ENNReal.tendsto_atTop (by decide)]
  intro ε hε
  obtain ⟨k, _, hk₂⟩ : ∃ k : ℝ, k ≥ 0 ∧ ∀ k' ≥ k,
      ENNReal.ofReal ((k' / (k' + 1)) ^ d) ∈ Set.Icc (1 - ε) (1 + ε) := by
    obtain ⟨k, hk⟩ := (ENNReal.tendsto_atTop (by simp)).mp
      (Tendsto.ennrpow_const (d : ℝ) <| tendsto_ofReal <| Tendsto.const_sub 1 <|
        tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_id) :
        Filter.Tendsto (fun k => (ENNReal.ofReal (1 - (k + 1)⁻¹) ^ (d : ℝ))) atTop
          (𝓝 (ENNReal.ofReal (1 - 0) ^ (d : ℝ)))) ε hε
    refine ⟨max 0 k, by simp, fun k' hk' => ?_⟩
    obtain ⟨_, hk₁⟩ := max_le_iff.mp hk'
    have := hk k' hk₁
    have hgoal :
        ENNReal.ofReal ((k' / (k' + 1)) ^ (d : ℝ)) ∈ Set.Icc (1 - ε) (1 + ε) := by
      rwa [sub_zero, ofReal_one, one_rpow, ← one_div, one_sub_div, add_sub_cancel_right,
        ENNReal.ofReal_rpow_of_nonneg] at this <;> positivity
    simpa using hgoal
  refine ⟨k * C, fun n hn => ?_⟩
  rw [hfmt _ ((by positivity : 0 ≤ k * C).trans hn)]
  convert hk₂ (n / C) ((le_div_iff₀ hC).mpr hn)
  rw [div_add_one, div_div_div_cancel_right₀, div_pow] <;> positivity

/-- As `R → ∞`, `volume (ball 0 (R + C)) / volume (ball 0 (R + C'))` → `1` for `C, C' ≥ 0`. -/
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
      measure_ball_lt_top.ne measure_ball_lt_top.ne⟩) ?_
  convert ENNReal.Tendsto.div (volume_ball_ratio_tendsto_nhds_one hd hC') ?_
    (volume_ball_ratio_tendsto_nhds_one hd hC) ?_ <;> simp

/-- Shifting the argument by a constant does not change convergence to `atTop`. -/
public theorem Filter.map_add_atTop_eq' {β : Type*} {f : ℝ → β} (C : ℝ) (α : Filter β) :
    Tendsto f atTop α ↔ Tendsto (fun x ↦ f (x + C)) atTop α :=
  have hmap : Filter.map (fun x : ℝ => x + C) atTop = atTop := by
    simpa using Filter.map_add_atTop_eq (α := ℝ) (k := C)
  ⟨fun hf => tendsto_map'_iff.mp (by simpa [hmap]),
    fun hf => by simpa [hmap] using tendsto_map'_iff.mpr hf⟩

/-- Same as `volume_ball_ratio_tendsto_nhds_one'`, without sign assumptions on `C, C'`. -/
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

/-! ## Density formula -/

open scoped Pointwise Topology
open Filter

variable {d : ℕ}

section DensityEqFdDensity

variable
  {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

/-- Compute the density of a periodic packing using a (bounded) fundamental domain. -/
public theorem PeriodicSpherePacking.density_eq
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.density
      = S.numReps * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  refine limsSup_eq_of_le_nhds ?_
  have hmul_one : ∀ a : ENNReal, 𝓝 a = 𝓝 (a * 1) := fun _ => by rw [mul_one]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ ?_
      (aux_big_ge b · hL hd) (aux_big_le b · hL hd) <;>
    rw [hmul_one] <;> refine ENNReal.Tendsto.const_mul ?_ (Or.inl one_ne_zero)
  · simp_rw [sub_sub, sub_eq_add_neg]
    convert volume_ball_ratio_tendsto_nhds_one'' hd (C := -(S.separation / 2 + L * 2))
    rw [add_zero]
  · simp_rw [add_assoc]
    convert volume_ball_ratio_tendsto_nhds_one'' hd (C := S.separation / 2 + L * 2)
    rw [add_zero]

end DensityEqFdDensity

/-- Normalize `PeriodicSpherePackingConstant d` as a sup over packings with `separation = 1`. -/
public theorem periodic_constant_eq_periodic_constant_normalized :
    PeriodicSpherePackingConstant d = ⨆ (S : PeriodicSpherePacking d) (_ : S.separation = 1),
    S.density := by
  rw [iSup_subtype', PeriodicSpherePackingConstant]
  refine le_antisymm (iSup_le fun S => ?_) (iSup_le fun ⟨S, _⟩ =>
    le_iSup (fun S : PeriodicSpherePacking d => S.density) S)
  rw [← scale_density _ (inv_pos.mpr S.separation_pos)]
  exact le_iSup (fun x : { x : PeriodicSpherePacking d // x.separation = 1 } ↦ x.val.density)
    ⟨S.scale (inv_pos.mpr S.separation_pos), inv_mul_cancel₀ S.separation_pos.ne.symm⟩

section Fundamental_Domains_in_terms_of_Basis

open Submodule

variable (S : PeriodicSpherePacking d) (b : Basis (Fin d) ℤ S.lattice)

/-- Every point has a unique translate in the fundamental domain associated to a lattice basis. -/
public theorem PeriodicSpherePacking.fundamental_domain_unique_covers :
    ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) := fun x =>
  have hspan : S.lattice = span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) :=
    (Basis.ofZLatticeBasis_span ℝ S.lattice b).symm
  let ⟨g, hg, hguniq⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  ⟨⟨(g : EuclideanSpace ℝ (Fin d)), by simp [hspan]⟩, hg, fun y hy => Subtype.ext <|
    congrArg (fun z : span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) => (z : EuclideanSpace ℝ (Fin d)))
      (hguniq ⟨(y : EuclideanSpace ℝ (Fin d)), by simpa [hspan] using y.property⟩ hy)⟩

end Fundamental_Domains_in_terms_of_Basis

/-- An index equivalence for the default basis of the lattice of a periodic packing. -/
@[expose] public noncomputable def PeriodicSpherePacking.basis_index_equiv
    (P : PeriodicSpherePacking d) : (Module.Free.ChooseBasisIndex ℤ ↥P.lattice) ≃ (Fin d) :=
  ZLattice.basis_index_equiv P.lattice

noncomputable def PeriodicSpherePacking.defaultBasis (S : PeriodicSpherePacking d) :
    Basis (Fin d) ℤ ↥S.lattice :=
  ((ZLattice.module_free ℝ S.lattice).chooseBasis).reindex S.basis_index_equiv

/-- A basis-free variant of `PeriodicSpherePacking.density_eq`, stated using `ZLattice.covolume`. -/
@[simp] public theorem PeriodicSpherePacking.density_eq'
    (S : PeriodicSpherePacking d) (hd : 0 < d) : S.density =
    (ENat.toENNReal (S.numReps : ENat)) *
    volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) /
    Real.toNNReal (ZLattice.covolume S.lattice) := by
  let b : Basis (Fin d) ℤ ↥S.lattice := S.defaultBasis
  obtain ⟨L, hL⟩ := isBounded_iff_forall_norm_le.1
    (fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b))
  rw [Real.toNNReal_of_nonneg (ZLattice.covolume_pos S.lattice volume).le,
    S.density_eq b hL hd, ENat.toENNReal_coe]
  refine congrArg _ ((ENNReal.toReal_eq_toReal_iff' (IsBounded.measure_lt_top
      (fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b))).ne
    ENNReal.coe_ne_top).mp ?_)
  rw [ENNReal.coe_toReal, NNReal.coe_mk]
  exact (ZLattice.covolume_eq_measure_fundamentalDomain S.lattice volume
    (ZLattice.isAddFundamentalDomain b volume)).symm

/-- If a periodic packing has no centers, then its density is zero. -/
public theorem PeriodicSpherePacking.density_of_centers_empty (S : PeriodicSpherePacking d)
    (hd : 0 < d) [instEmpty : IsEmpty S.centers] : S.density = 0 := by
  let b := S.defaultBasis
  let D := fundamentalDomain (Basis.ofZLatticeBasis ℝ S.lattice b)
  haveI : IsEmpty (↥(S.centers ∩ D)) := ⟨fun x => instEmpty.false ⟨x.1, x.2.1⟩⟩
  rw [S.density_eq' hd, ← S.card_centers_inter_isFundamentalDomain D
    (fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b))
    (S.fundamental_domain_unique_covers b) hd]
  simp
