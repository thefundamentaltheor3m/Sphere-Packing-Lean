module
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import SpherePacking.ModularForms.Cauchylems
public import SpherePacking.ModularForms.limunder_lems
public import SpherePacking.ModularForms.tendstolems
import SpherePacking.ModularForms.SummableLemmas.Basic
import SpherePacking.ModularForms.SummableLemmas.Cotangent
import SpherePacking.ModularForms.SummableLemmas.G2
import SpherePacking.ModularForms.SummableLemmas.QExpansion
import SpherePacking.ModularForms.SummableLemmas.IntPNat


/-!
# The Eisenstein series `E₂`

This file defines the weight-2 Eisenstein series `E₂` on the upper half-plane, together with the
auxiliary series `G₂` used to define it and a correction term `D₂` which appears in its modular
transformation behavior.

## Main definitions
* `G₂`, `G₂_a`
* `E₂`
* `D₂`
-/

open scoped Interval Real Topology BigOperators Nat Matrix.SpecialLinearGroup

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory
  Metric Filter Function Complex MatrixGroups Matrix.SpecialLinearGroup

open ArithmeticFunction

noncomputable section Definitions


/-- The series `G₂`, defined using symmetric partial sums over `Ico (-N) N` and `limUnder`. -/
@[expose] public def G₂ : ℍ → ℂ := fun z => limUnder (atTop)
    (fun N : ℕ => ∑ m ∈ Finset.Ico (-N : ℤ) N, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2)))

/-- A variant of `G₂` using symmetric partial sums over `Icc (-N) N`. -/
@[expose] public def G₂_a : ℍ → ℂ := fun z => limUnder (atTop)
    (fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2)))

/-- The Eisenstein series `E₂`, normalized as a scalar multiple of `G₂`. -/
@[expose] public def E₂ : ℍ → ℂ := (1 / (2 * riemannZeta 2)) • G₂

/-- Coercion of `SL(2,ℤ)` matrices to `GL(2,ℝ)` via the standard map. -/
@[coe, reducible, expose] public def coe2 (g : SL(2, ℤ)) : (GL (Fin 2) ℝ) :=
  Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)

/-- The canonical coercion `SL(2,ℤ) → GL(2,ℝ)`. -/
public instance : Coe SL(2, ℤ) (GL (Fin 2) ℝ) := ⟨coe2⟩

/-- Compatibility of `coe2` with multiplication. -/
@[simp]
public lemma coe2_mul (A B : SL(2, ℤ)) :
     coe2 (A * B) = (coe2 A) * (coe2 B) := by simp [coe2]

/-- The correction term appearing in the weight-2 transformation law. -/
@[expose] public def D₂ (γ : SL(2, ℤ)) : ℍ → ℂ := fun z => (2 * π * Complex.I * γ 1 0) / (denom γ z)

lemma D₂_apply (γ : SL(2, ℤ)) (z : ℍ) :
    D₂ γ z = (2 * π * Complex.I * γ 1 0) / (γ 1 0 * z + γ 1 1) :=
  by rfl

lemma extracted_77 (z : ℍ) (n : ℤ) : Summable fun b : ℤ ↦ (((b : ℂ) * ↑z + ↑n) ^ 2)⁻¹ := by
  have := (
      G2_summable_aux (-n) ⟨-1 /z, by simpa using pnat_div_upper 1 z⟩ 2 (by norm_num)
    ).mul_left ((z : ℂ)^2)⁻¹
  refine this.congr ?_
  intro b
  have hz : (z : ℂ) ≠ 0 := by simpa using (ne_zero z)
  simp only [Int.cast_neg, neg_mul]
  field_simp [hz]
  ring_nf

theorem extracted_66 (z : ℍ) :
  (fun _ => ((z : ℂ) ^ 2)⁻¹) *
    (fun N : ℕ ↦ ∑ x ∈ Finset.Ico (-↑N : ℤ) ↑N, ∑' (n : ℤ), (((x : ℂ) * (-↑z)⁻¹ + ↑n) ^ 2)⁻¹) =
  fun N : ℕ ↦
    ∑' (n : ℤ), ∑ x ∈ Finset.Ico (-↑N : ℤ) ↑N, (((n : ℂ) * ↑z + ↑x) ^ 2)⁻¹ := by
  ext N
  simp only [inv_neg, mul_neg, Pi.mul_apply]
  rw [@Finset.mul_sum]
  rw [Summable.tsum_finsetSum]
  · congr
    ext n
    rw [← tsum_mul_left]
    rw [int_sum_neg]
    congr
    ext d
    have hz : (z : ℂ) ≠ 0 := by simpa using (ne_zero z)
    simp only [Int.cast_neg]
    field_simp [hz]
    ring_nf
  · intro i hi
    exact extracted_77 z i

lemma G2_S_act (z : ℍ) : (z.1 ^ 2)⁻¹ * G₂ (ModularGroup.S • z) = limUnder (atTop)
    fun N : ℕ => ((∑' (n : ℤ), ∑ m ∈ Finset.Ico (-N : ℤ) N, (1 / ((n : ℂ) * z + m) ^ 2))) := by
  rw [ modular_S_smul]
  simp only [G₂, inv_neg, one_div]
  rw [ limUnder_mul_const]
  · congr
    simpa using extracted_66 z
  · apply CauchySeq_Icc_iff_CauchySeq_Ico
    · intro d
      rw [int_sum_neg]
      congr
      ext n
      simp only [Int.cast_neg, neg_mul, inv_inj]
      ring
    have := G2_cauchy ⟨-(1 : ℂ) / z, by simpa using pnat_div_upper 1 z⟩
    simp only [one_div] at this
    apply this.congr
    ext N
    congr
    ext m
    congr
    ext n
    congr 1
    field_simp [ne_zero z]


theorem series_eql' (z : ℍ) :
    ↑π * Complex.I - 2 * ↑π * Complex.I * ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * z * n) =
      1 / z + ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) := by
  rw [EisensteinSeries_Identity z]
  congr
  ext n
  rw [← Complex.exp_nat_mul]
  ring_nf

theorem extracted_summable (z : ℍ) (n : ℕ+) : Summable fun m : ℕ ↦
    cexp (2 * ↑π * Complex.I * (-↑↑n / ↑z) * ↑m) := by
  have A1 := a1 1 1 ⟨ -n / z , pnat_div_upper n z⟩
  simp at A1
  apply A1

theorem tsum_exp_tendsto_zero (z : ℍ) :
    Tendsto (fun x : ℕ+ ↦ 2 / ↑z * 2 * ↑π * Complex.I *
    ∑' (n : ℕ), cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z) * ↑n)) atTop (𝓝 (4 * ↑π * Complex.I / ↑z))
    := by
  -- Reduce to the geometric series formula.
  set r : ℂ := cexp (2 * ↑π * Complex.I * (-1 / (z : ℂ)))
  have hr : ‖r‖ < 1 := by
    simpa [r] using exp_upperHalfPlane_lt_one ⟨-1 / z, by simpa using pnat_div_upper 1 z⟩
  have hr0 : Tendsto (fun x : ℕ+ ↦ cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z))) atTop (𝓝 (0 : ℂ)) := by
    have hxr :
        (fun x : ℕ+ ↦ cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z))) = fun x : ℕ+ ↦ r ^ (x : ℕ) := by
      funext x
      have hx :
          2 * ↑π * Complex.I * (-↑↑x / ↑z) =
            (x : ℕ) * (2 * ↑π * Complex.I * (-1 / ↑z)) := by
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      simpa [r, hx] using (Complex.exp_nat_mul (2 * ↑π * Complex.I * (-1 / ↑z)) (x : ℕ))
    have hp : Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 (0 : ℂ)) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr
    have hp' : Tendsto (fun x : ℕ+ ↦ r ^ (x : ℕ)) atTop (𝓝 (0 : ℂ)) :=
      tendsto_comp_val_Ioi_atTop.mpr hp
    simpa [hxr] using hp'
  have htsum :
      Tendsto (fun x : ℕ+ ↦ ∑' n : ℕ, cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z) * ↑n)) atTop
        (𝓝 (1 : ℂ)) := by
    have hgeom :
        (fun x : ℕ+ ↦ ∑' n : ℕ, cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z) * ↑n)) =
          fun x : ℕ+ ↦ (1 - cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z)))⁻¹ := by
      funext x
      set ξ : ℂ := cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z))
      have hξ : ‖ξ‖ < 1 := by
        simpa [ξ] using exp_upperHalfPlane_lt_one ⟨-x / z, by simpa using pnat_div_upper x z⟩
      have hterm :
          (fun n : ℕ ↦ cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z) * ↑n)) = fun n : ℕ ↦ ξ ^ n := by
        funext n
        simpa [ξ, mul_assoc, mul_left_comm, mul_comm] using
          (Complex.exp_nat_mul (2 * ↑π * Complex.I * (-↑↑x / ↑z)) n)
      simpa [hterm] using (tsum_geometric_of_norm_lt_one (ξ := ξ) hξ)
    have h1 :
        Tendsto (fun x : ℕ+ ↦ 1 - cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z))) atTop (𝓝 (1 : ℂ)) := by
      simpa using (tendsto_const_nhds.sub hr0)
    have h1inv :
        Tendsto (fun x : ℕ+ ↦ (1 - cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z)))⁻¹) atTop
          (𝓝 (1 : ℂ)) := by
      simpa using (h1.inv₀ (by simp))
    simpa [hgeom] using h1inv
  -- Reinsert the constant prefactor.
  have :=
    (tendsto_const_nhds.mul htsum : Tendsto
      (fun x : ℕ+ ↦ (2 / ↑z * 2 * ↑π * Complex.I) *
        (∑' n : ℕ, cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z) * ↑n))) atTop
        (𝓝 ((2 / ↑z * 2 * ↑π * Complex.I) * (1 : ℂ))))
  have h22 : (2 : ℂ) * 2 = 4 := by norm_num
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, h22] using this


theorem extracted_12 (z : ℍ) :
    Tendsto (fun n : ℕ => (2 / (z : ℂ) * ∑' (m : ℕ+),
    (1 / (-(n : ℂ) / ↑z - ↑↑m) + 1 / (-↑↑n / ↑z + ↑↑m)))) atTop (𝓝 (-2 * ↑π * Complex.I / ↑z))
    := by
  have : Tendsto (fun n : ℕ+ => (2 / (z : ℂ) * ∑' (m : ℕ+),
    (1 / (-(n : ℂ) / ↑z - ↑↑m) + 1 / (-↑↑n / ↑z + ↑↑m)))) atTop (𝓝 (-2 * ↑π * Complex.I / ↑z))
    := by
    have : (fun n : ℕ+ => (2 / (z : ℂ) * ∑' (m : ℕ+),
     (1 / (-(n : ℂ) / ↑z - ↑↑m) + 1 / (-↑↑n / ↑z + ↑↑m)))) = (fun N : ℕ+ =>
      (2 / (z : ℂ) * (↑π * Complex.I - 2 * ↑π * Complex.I *
      ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * (-(N : ℂ) / z) * n) - z / (-(N : ℂ))))) := by
      funext N
      set Z : ℍ := ⟨-(N : ℂ) / z, by simpa using pnat_div_upper N z⟩
      have hS := series_eql' Z
      have hsum :
          (∑' n : ℕ+, (1 / ((Z : ℂ) - n) + 1 / (Z + n))) =
            (↑π * Complex.I -
                2 * ↑π * Complex.I *
                  ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * (Z : ℂ) * n)) -
              1 / (Z : ℂ) := by
        have := congrArg (fun t : ℂ => t - 1 / (Z : ℂ)) hS
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this.symm
      have hz : (1 / (Z : ℂ)) = (z : ℂ) / (-(N : ℂ)) := by
        simp [Z]
      simpa [Z, hz, mul_sub] using congrArg (fun t : ℂ => (2 / (z : ℂ)) * t) hsum
    rw [this]
    have h3 : (fun N : ℕ+ =>
        (2 / (z : ℂ) * (↑π * Complex.I - 2 * ↑π * Complex.I *
        ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * (-(N : ℂ) / z) * n) - z / (-(N : ℂ))))) =
        (fun N : ℕ+ => ((2 / (z : ℂ)) * ↑π * Complex.I - ((2 / z) * 2 * ↑π * Complex.I *
          ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * (-(N : ℂ) / z) * n)) - 2 / (-(N : ℂ)))) := by
        funext N
        have hz : 2 / (-(N : ℂ)) = (2 / z) * (z / (-(N : ℂ))) := by
          have : (z : ℂ) ≠ 0 := ne_zero z
          field_simp
        rw [hz]
        ring
    rw [h3]
    rw [show -2 * ↑π * Complex.I / ↑z = 2 * ↑π * Complex.I / ↑z - 4 * ↑π * Complex.I / ↑z - 0 by
      ring]
    apply Tendsto.sub
    · apply Tendsto.sub
      · simp only [tendsto_const_nhds_iff]
        ring
      apply tsum_exp_tendsto_zero
    have := tendsto_const_div_pow 2 1 (Nat.one_ne_zero)
    rw [Metric.tendsto_atTop] at *
    simp only [one_div, gt_iff_lt, ge_iff_le, pow_one, dist_zero_right, norm_div, Real.norm_ofNat,
      Real.norm_natCast, norm_ofNat, norm_neg] at *
    intro ε hε
    have ht := this ε hε
    obtain ⟨N,HN ⟩ := ht
    use ⟨(N + 1), Nat.zero_lt_succ N⟩
    intro n hn
    have hn1 : N + 1 ≤ (n : ℕ) := by
      have : ((⟨N + 1, Nat.zero_lt_succ N⟩ : ℕ+) : ℕ) ≤ n := (PNat.coe_le_coe _ _).2 hn
      simpa using this
    have hn' : N ≤ (n : ℕ) := Nat.le_trans (Nat.le_succ N) hn1
    simpa [RCLike.norm_natCast] using HN (n : ℕ) hn'
  rw [Metric.tendsto_atTop] at *
  simp only [gt_iff_lt, ge_iff_le, one_div, neg_mul] at *
  intro ε hε
  have th := this ε hε
  obtain ⟨N, hN⟩ := th
  use N
  intro n hn
  have hn0 : 0 < n := by
   have l := N.2
   simp only [gt_iff_lt] at *
   apply Nat.lt_of_lt_of_le l hn
  have HNN := hN ⟨n, hn0⟩ ?_
  · simp only [PNat.mk_coe, gt_iff_lt] at *
    exact HNN
  norm_cast

theorem PS3tn22 (z : ℍ) :
  Tendsto (fun N : ℕ+ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N,
    ∑' (m : ℤ), (1 / ((m : ℂ) * ↑z + ↑n) - 1 / (↑m * ↑z + ↑n + 1))) atTop
    (𝓝 (-2 * ↑π * Complex.I / ↑z)) := by
  have : (fun N : ℕ+ => ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    ∑' m : ℤ , (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) =
    (fun N : ℕ+ =>
    ∑' m : ℤ , ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)), (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)))
      := by
    ext n
    rw [Summable.tsum_finsetSum]
    intro i hi
    apply summable_pain
  conv at this =>
    enter [2]
    ext
    conv =>
      enter [1]
      ext m
      rw [telescope_aux z]
  have hp := sum_int_pnat2_pnat z
  conv at this =>
    enter [2]
    ext m
    rw [show (m : ℂ) = (m : ℕ+) by simp]
    rw [hp]
  rw [this]
  rw [show -2 * ↑π * Complex.I / ↑z = 0 + -2 * ↑π * Complex.I / ↑z by ring]
  apply Tendsto.add
  · exact nat_tendsto_pnat _ _ (tendsto_const_div_atTop_nhds_zero_nat (-2 : ℂ))
  · conv =>
      enter [1]
      ext n
      rw [show (n : ℂ) = (n : ℤ) by simp]
      rw [sum_int_pnat3]
    have := nat_tendsto_pnat _ _ (extracted_12 z)
    exact this

lemma PS3 (z : ℍ) : limUnder atTop
  (fun N : ℕ => ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    ∑' m : ℤ , (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) = -2 * π * Complex.I / z := by
  refine Filter.Tendsto.limUnder_eq ?_
  exact pnat_tendsto_nat _ _ (PS3tn22 z)


/-- An algebraic identity used to rewrite terms in the transformed `G₂` series. -/
public theorem poly_id (z : ℍ) (b n : ℤ) :
  ((b : ℂ) * ↑z + ↑n + 1)⁻¹ * (((b : ℂ) * ↑z + ↑n) ^ 2)⁻¹ + (δ b n) +
    (((b : ℂ) * ↑z + ↑n)⁻¹ - ((b : ℂ) * ↑z + ↑n + 1)⁻¹) =
    (((b : ℂ) * ↑z + ↑n) ^ 2)⁻¹ := by
  by_cases h : b = 0 ∧ n = 0
  · simp [δ, h.1, h.2]
  have hn0_of_b0 : b = 0 → n ≠ 0 := fun hb hn => h ⟨hb, hn⟩
  by_cases hb : b = 0
  · subst hb
    by_cases hn : n = -1
    · simp [δ, hn]
      ring
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (hn0_of_b0 rfl)
    have hn1 : (n : ℂ) + 1 ≠ 0 := by
      have : (n : ℂ) ≠ (-1 : ℂ) := by exact_mod_cast hn
      simpa [add_eq_zero_iff_eq_neg] using this
    have hδ : δ 0 n = 0 := by simp [δ, hn0_of_b0 rfl, hn]
    simp [hδ]
    field_simp [hn0, hn1]
    ring
  have hδ : δ b n = 0 := by simp [δ, hb]
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hcd1 : (![(b : ℝ), n + 1] : Fin 2 → ℝ) ≠ 0 := by
    intro h0
    exact hbR (by simpa using congrArg (fun v : Fin 2 → ℝ => v 0) h0)
  have hcd0 : (![(b : ℝ), n] : Fin 2 → ℝ) ≠ 0 := by
    intro h0
    exact hbR (by simpa using congrArg (fun v : Fin 2 → ℝ => v 0) h0)
  have h0 : (b : ℂ) * (z : ℂ) + n + 1 ≠ 0 := by
    simpa [add_assoc] using (linear_ne_zero (cd := ![(b : ℝ), n + 1]) z hcd1)
  have h1 : (b : ℂ) * (z : ℂ) + n ≠ 0 := by
    simpa using (linear_ne_zero (cd := ![(b : ℝ), n]) z hcd0)
  simp [hδ]
  field_simp [h0, h1]
  ring

theorem extracted_66c (z : ℍ) :
  (fun _ => ((z : ℂ) ^ 2)⁻¹) *
    (fun N : ℕ ↦ ∑ x ∈ Finset.Icc (-↑N : ℤ) ↑N, ∑' (n : ℤ), (((x : ℂ) * (-↑z)⁻¹ + ↑n) ^ 2)⁻¹) =
  fun N : ℕ ↦
    ∑' (n : ℤ), ∑ x ∈ Finset.Icc (-↑N : ℤ) ↑N, (((n : ℂ) * ↑z + ↑x) ^ 2)⁻¹ := by
  ext N
  simp only [inv_neg, mul_neg, Pi.mul_apply]
  rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum]
  · congr
    ext n
    rw [← tsum_mul_left]
    rw [int_sum_neg]
    congr
    ext d
    have hz : (z : ℂ) ≠ 0 := by simpa using (ne_zero z)
    simp only [Int.cast_neg]
    field_simp [hz]
    ring_nf
  · intro i hi
    exact extracted_77 z i

theorem extracted_6 (z : ℍ) : CauchySeq fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-(N : ℤ)) ↑N,
  ∑' (m : ℤ), (1 / ((m : ℂ) * ↑z + ↑n) - 1 / (↑m * ↑z + ↑n + 1)) := by
  refine Filter.Tendsto.cauchySeq (x := (-2 * π * Complex.I / z)) ?_
  exact pnat_tendsto_nat _ _ (PS3tn22 z)

/-- An `ℤ × ℤ` reindexing of the transformed `G₂` expression on the left-hand side. -/
public lemma G2_inde_lhs (z : ℍ) : (z.1 ^ 2)⁻¹ * G₂ (ModularGroup.S • z) - -2 * π * Complex.I / z =
  ∑' n : ℤ, ∑' m : ℤ, (1 / (((m : ℂ)* z +n)^2 * (m * z + n +1)) + δ m n) := by
  rw [G2_S_act, ← PS3 z, tsum_limUnder_atTop, limUnder_sub]
  · congr
    ext N
    simp only [one_div, Pi.sub_apply, mul_inv_rev]
    rw [Summable.tsum_finsetSum, ← Finset.sum_sub_distrib ]
    · congr
      ext n
      rw [← Summable.tsum_sub]
      · congr
        ext m
        have := poly_id z m n
        nth_rw 1 [← this]
        simp only [add_sub_cancel_right]
      · exact extracted_77 z n
      · simpa only [one_div] using (summable_pain z n)
    · intro i hi
      exact extracted_77 z i
  · conv =>
      enter [1]
      ext N
      rw [Summable.tsum_finsetSum (by intro i hi; simp only [one_div]; exact extracted_77 z i)]
    apply CauchySeq_Icc_iff_CauchySeq_Ico
    · intro n
      nth_rw 2 [int_sum_neg]
      congr
      ext m
      simp only [one_div, Int.cast_neg, neg_mul, inv_inj]
      ring
    conv =>
      enter [1]
      ext N
      rw [← Summable.tsum_finsetSum (by intro i hi; simp only [one_div]; exact extracted_77 z i)]
    have := G2_cauchy ⟨-1 / z, by simpa using pnat_div_upper 1 z⟩
    have hC := cauchy_seq_mul_const _ ((z : ℂ) ^ 2)⁻¹ this
    apply hC.congr
    have H := extracted_66c z
    simp only [one_div] at *
    rw [← H]
    ext N
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    apply mul_left_cancel₀ (by simpa using inv_ne_zero (pow_ne_zero 2 (ne_zero z)))
    congr
    ext n
    congr
    ext m
    congr
    ring
  · apply extracted_6
  · have := G_2_alt_summable_δ z
    simp only [Fin.isValue, one_div, mul_inv_rev] at this
    rw [← swap_equiv.summable_iff, ← (finTwoArrowEquiv _).symm.summable_iff] at this
    have ht := Summable.prod this
    simp only [Fin.isValue, swap_equiv, Equiv.coe_fn_mk, finTwoArrowEquiv_symm_apply, comp_apply,
      swap_apply, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_one,
      Matrix.cons_val_zero, one_div, mul_inv_rev] at *
    exact ht

lemma PS1 (z : ℍ) (m : ℤ) : limUnder atTop
  (fun N : ℕ => ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) = 0 := by
  refine Filter.Tendsto.limUnder_eq ?_
  -- Telescoping sum and known `tendsto` facts.
  have htel :
      (fun N : ℕ => ∑ n ∈ Finset.Ico (-(N : ℤ)) (N : ℤ),
          (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) =
        fun N : ℕ => 1 / ((m : ℂ) * z - N) - 1 / (m * z + N) := by
    ext N
    simpa using telescope_aux z m N
  rw [htel]
  simpa using (tendstozero_inv_linear_neg z m).sub (tendstozero_inv_linear z m)


lemma PS2 (z : ℍ) : ∑' m : ℤ, (limUnder atTop
  (fun N : ℕ => ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)))) = 0 := by
  simpa using (tsum_congr fun m => (PS1 z m))

lemma auxr (z : ℍ) (b : ℤ) :
    ((limUnder atTop fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1)) + δ b n)) +
    limUnder atTop fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * ↑z + ↑n) - 1 / (↑b * ↑z + ↑n + 1))) =
    limUnder atTop fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * ↑z + ↑n) ^ 2) := by
  have := limUnder_add (f := fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1))+ δ b n))
    (g := fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * ↑z + ↑n) - 1 / (↑b * ↑z + ↑n + 1)))
      (extracted_2_δ z b) (by apply extracted_3 z b)
  rw [this]
  refine limUnder_congr_eventually _ _ ?_ (by
    apply CauchySeq.add (extracted_2_δ z b) (extracted_3 z b))
  simp only [one_div, mul_inv_rev, Pi.add_apply, eventually_atTop,
    ge_iff_le]
  use 1
  intro c hc
  rw [← Finset.sum_add_distrib ]
  congr
  ext n
  apply poly_id z b n


--this sum is now abs convergent. Idea is to subtract PS1 from the G₂ defn.
lemma G2_alt_eq (z : ℍ) : G₂ z = ∑' m : ℤ, ∑' n : ℤ,
    (1 / (((m : ℂ) * z + n) ^ 2 * (m * z + n + 1)) + δ m n) := by
  rw [G₂]
  have := PS2 z
  set t := ∑' m : ℤ, ∑' n : ℤ, (1 / (((m : ℂ) * z + n) ^ 2 * (m * z + n + 1)) + δ m n)
  rw [show t = t + 0 by ring, ← this]
  simp only [t]
  have hG2AltProd :=
    (by
        have H := G_2_alt_summable_δ z
        rw [← (finTwoArrowEquiv _).symm.summable_iff] at H
        exact H.prod)
  rw [← Summable.tsum_add]
  · rw [tsum_limUnder_atTop]
    · congr
      ext n
      congr
      ext m
      rw [tsum_limUnder_atTop, tsum_limUnder_atTop, auxr z m]
      · have H := G2_prod_summable1_δ z m
        simpa using H
      · have H := G2_summable_aux m z 2 (by norm_num)
        simpa using H
    · refine hG2AltProd.congr ?_
      intro b
      simpa using PS1 z b
  · refine hG2AltProd.congr ?_
    intro b
    simp only [Fin.isValue, one_div, mul_inv_rev, finTwoArrowEquiv_symm_apply, comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  · refine (summable_zero : Summable fun _ : ℤ => (0 : ℂ)).congr ?_
    intro b
    simpa using (PS1 z b).symm


lemma G2_transf_aux (z : ℍ) : (z.1 ^ 2)⁻¹ * G₂ (ModularGroup.S • z) - -2 * π * Complex.I / z =
  G₂ z := by
  rw [G2_inde_lhs, G2_alt_eq z , ← G2_alt_indexing2_δ , G2_alt_indexing_δ]

public lemma ModularGroup.coe_mul (A B : SL(2, ℤ)) :
    (ModularGroup.coe A) * B = ModularGroup.coe (A * B) := by
  have : Matrix.SpecialLinearGroup.toGLPos ∘ (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) =
    ModularGroup.coe := by
    funext A
    rfl
  let C := MonoidHom.comp Matrix.SpecialLinearGroup.toGLPos
    (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom ℝ))
  have hC : C = ModularGroup.coe := by
    rw [← this]
    rfl
  have := C.map_mul A B
  rw [hC] at this
  exact this.symm

lemma denom_diff (A B : SL(2, ℤ)) (z : ℍ) : ((A * B) 1 0) * (denom B z) =
  (A 1 0) * B.1.det + (B 1 0) * denom (A * B) z := by
  have h0 := Matrix.two_mul_expl A.1 B.1
  have h1 := Matrix.det_fin_two B.1
  simp_rw [← map_mul, ModularGroup.denom_apply]
  simp [Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, h0.2.2.1, Int.cast_add, Int.cast_mul, h1,
    Int.cast_sub, h0.2.2.2]
  ring


@[simp]
lemma denom_sim (A : SL(2, ℤ)) (z : ℍ) :
    denom (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) A)) z = denom (coe2 A) z :=
  rfl

@[simp]
lemma coe2_smul (A : SL(2, ℤ)) (z : ℍ) :
  (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) A)) • z = (coe2 A) • z :=
  rfl

lemma D2_mul (A B : SL(2, ℤ)) : D₂ (A * B) = ((D₂ A) ∣[(2 : ℤ)] B) + (D₂ B):= by
  ext z
  have hco := denom_cocycle A B z.im_ne_zero
  simp_rw [SL_slash_def]
  simp_rw [denom_sim]
  simp only [D₂, Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, Int.reduceNeg, zpow_neg,
    Pi.add_apply]
  simp_rw [coe2_mul]
  simp_rw [← mul_div, mul_assoc, ← mul_add]
  congr
  simp only [Fin.isValue, ModularGroup.sl_moeb, coe2_smul]
  have hde : denom B z ≠ 0 := by exact denom_ne_zero (↑B) z
  field_simp [hde]
  have hd := denom_diff A B z
  rw [ ← sub_eq_iff_eq_add] at hd
  simp only [Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.det_coe,
    Int.cast_one, mul_one] at hd
  simp only [Fin.isValue, ← hd, hco, pow_two]
  have : denom (↑A) (num ↑B ↑z / denom ↑B ↑z) = denom ↑A ↑(↑B • z) := by
    congr 1
    simp [UpperHalfPlane.specialLinearGroup_apply]
    congr
  rw [this]
  rw [sub_div, ← mul_assoc, mul_div_assoc _ (denom _ _ * denom _ _)]
  simp_rw [mul_div_mul_right _ _ hde]
  simp only [Fin.isValue, ModularGroup.sl_moeb, coe2_smul]
  rw [mul_div_cancel_left₀ _ (denom_ne_zero _ _)]
  ring


lemma D2_one : D₂ 1 = 0 := by
  ext z; simp [D₂]

lemma D2_inv (A : SL(2, ℤ)) : (D₂ A)∣[(2 : ℤ)] A⁻¹ = - D₂ (A⁻¹) := by
  have h : (D₂ A)∣[(2 : ℤ)] A⁻¹ + D₂ (A⁻¹) = 0 := by
    simpa [mul_inv_cancel, SL_slash, D2_one] using (D2_mul A A⁻¹).symm
  exact eq_neg_of_add_eq_zero_left h


lemma D2_T : D₂ ModularGroup.T = 0 := by
  ext z; simp [D₂, ModularGroup.T]

lemma D2_S (z : ℍ) : D₂ ModularGroup.S z = 2 * (π : ℂ) * Complex.I / z := by
  simp [D₂, ModularGroup.S, ModularGroup.denom_apply]

lemma SL2_gens : Subgroup.closure {ModularGroup.S, ModularGroup.T} = ⊤ := by
  exact SpecialLinearGroup.SL2Z_generators


variable (f : ℍ → ℂ) (k : ℤ) (z : ℍ)
theorem modular_slash_S_apply :
    (f ∣[k] ModularGroup.S) z = f (UpperHalfPlane.mk (-z)⁻¹ z.im_inv_neg_coe_pos) * z ^ (-k) := by
  rw [SL_slash_apply, denom, UpperHalfPlane.modular_S_smul]
  simp [ModularGroup.S]



theorem modular_slash_T_apply : (f ∣[k] ModularGroup.T) z = f ((1 : ℝ) +ᵥ z) := by
  rw [SL_slash_apply, denom, UpperHalfPlane.modular_T_smul]
  simp [ModularGroup.T]



lemma G₂_eq_G₂_a (z : ℍ) : G₂ z = G₂_a z := by
  rw [G₂, G₂_a]
  rw [Filter.Tendsto.limUnder_eq]
  have := CauchySeq.tendsto_limUnder (G2_cauchy z)
  apply tendsto_of_tendsto_sub _ _ _ this
  have h0 := cc _ (G2_cauchy z) ?_
  conv =>
    enter [1]
    ext N
    simp
    rw [sum_Icc_eq_sum_Ico_succ _ (by omega)]
    simp
  · have := Filter.Tendsto.neg h0
    simp only [one_div, neg_zero] at this
    have := int_tendsto_nat this
    apply this
  · intro n
    nth_rw 2 [int_sum_neg]
    congr
    ext m
    simp only [one_div, Int.cast_neg, neg_mul, inv_inj]
    ring

/-- Fourier expansion of `G₂` as a constant term plus an exponential series. -/
public lemma G2_q_exp (z : ℍ) : G₂ z = (2 * riemannZeta 2) - 8 * π ^ 2 *
    ∑' n : ℕ+, sigma 1 n * cexp (2 * π * Complex.I * n * z) := by
  rw [G₂_eq_G₂_a, G₂_a]
  refine Filter.Tendsto.limUnder_eq ?_
  rw [t8 z, sub_eq_add_neg]
  refine tendsto_const_nhds.add ?_
  simpa [neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one, Nat.factorial_one, Nat.cast_one,
    div_one, pow_one] using G2_c_tendsto z

lemma G2_periodic : (G₂ ∣[(2 : ℤ)] ModularGroup.T) = G₂ := by
  ext z
  rw [modular_slash_T_apply, G2_q_exp, G2_q_exp]
  congr 2
  refine tsum_congr ?_
  intro n
  congr 1
  -- `exp_periodo` is stated with `(1 + z)`; rewrite `((1 : ℝ) +ᵥ z)` accordingly.
  simpa [coe_vadd, add_comm, add_left_comm, add_assoc] using exp_periodo z (n : ℕ)

/-- The Eisenstein series `E₂` is 1-periodic: `E₂ ((1 : ℝ) +ᵥ z) = E₂ z`. -/
public lemma E₂_periodic (z : ℍ) : E₂ ((1 : ℝ) +ᵥ z) = E₂ z := by
  have h := congrFun G2_periodic z
  rw [modular_slash_T_apply] at h
  simp only [E₂, Pi.smul_apply, smul_eq_mul, h]

/-- The modular transformation law for `G₂`, with the correction term `D₂`. -/
public lemma G₂_transform (γ : SL(2, ℤ)) : (G₂ ∣[(2 : ℤ)] γ) = G₂ - (D₂ γ) := by
  refine
    Subgroup.closure_induction (G := SL(2, ℤ))
      (p := fun γ _ ↦ G₂ ∣[(2 : ℤ)] γ = G₂ - D₂ γ)
      (k := ({ModularGroup.S, ModularGroup.T} : Set (SL(2, ℤ))))
      (fun a ha => ?_) ?_ (fun a b ha hb HA HB => ?_) (fun g hg hg2 => ?_) ?_
  · dsimp
    rcases (by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ha) with rfl | rfl
    · ext z
      simp only [Pi.sub_apply]
      rw [D2_S z]
      have := modular_slash_S_apply G₂ 2 z
      simp only [Int.reduceNeg, zpow_neg] at this
      rw [this, mul_comm]
      rw [← G2_transf_aux z]
      ring_nf
      rw [modular_S_smul]
      congr
      · simp [inv_pow, inv_inj]
        norm_cast
      · simp
    · simpa [D2_T, sub_zero] using G2_periodic
  · simp only [SlashAction.slash_one, D2_one, sub_zero]
  · dsimp at HA HB ⊢
    rw [D2_mul, SlashAction.slash_mul, HA, sub_eq_add_neg, SlashAction.add_slash, HB]
    ext z
    simp only [SlashAction.neg_slash, SL_slash, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
    ring
  · dsimp at hg2 ⊢
    have H1 : (G₂ ∣[(2 : ℤ)] g) ∣[(2 : ℤ)] g⁻¹ = (G₂ - D₂ g) ∣[(2 : ℤ)] g⁻¹ := by
      simpa using congrArg (fun F => F ∣[(2 : ℤ)] g⁻¹) hg2
    rw [← SlashAction.slash_mul, sub_eq_add_neg, SlashAction.add_slash] at H1
    simp only [mul_inv_cancel, SlashAction.slash_one, SL_slash, SlashAction.neg_slash] at H1
    nth_rw 2 [H1]
    rw [← sub_eq_add_neg]
    have := D2_inv g
    simp only [SL_slash] at this
    rw [this]
    simp only [SL_slash, sub_neg_eq_add, add_sub_cancel_right]
  · simp [SL2_gens]


/-- The `S`-transform of `E₂` in slash-action form. -/
public lemma E₂_transform (z : ℍ) : (E₂ ∣[(2 : ℤ)] ModularGroup.S) z =
    E₂ z + 6 / (π * Complex.I * z) := by
  rw [E₂, ModularForm.SL_smul_slash (2 : ℤ) ModularGroup.S G₂ (1 / (2 * riemannZeta 2))]
  have hG := G₂_transform (ModularGroup.S)
  simp only [SL_slash, one_div, mul_inv_rev, Pi.smul_apply, smul_eq_mul] at *
  rw [hG]
  simp only [Pi.sub_apply]
  rw [D2_S]
  ring_nf
  rw [sub_eq_add_neg]
  congr
  rw [riemannZeta_two]
  have hpi : (π : ℂ) ≠ 0 := by simp
  ring_nf
  simp only [inv_pow, inv_I, mul_neg, neg_mul, neg_inj, mul_eq_mul_right_iff, OfNat.ofNat_ne_zero,
    or_false]
  rw [← inv_pow, pow_two, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  ring

/-- E₂ transforms under SL(2,ℤ) as: E₂ ∣[2] γ = E₂ - α • D₂ γ where α = 1/(2ζ(2)) -/
public lemma E₂_slash_transform (γ : SL(2, ℤ)) :
    (E₂ ∣[(2 : ℤ)] γ) = E₂ - (1 / (2 * riemannZeta 2)) • D₂ γ := by
  ext z
  simp [E₂, G₂_transform γ]
  ring

/-- E₂ transforms under S as: E₂(-1/z) = z² · (E₂(z) + 6/(πIz)).
    This is derived from E₂_transform by relating the slash action to the direct value. -/
public lemma E₂_S_transform (z : ℍ) :
    E₂ (ModularGroup.S • z) = z ^ 2 * (E₂ z + 6 / (π * Complex.I * z)) := by
  have h := E₂_transform z
  rw [SL_slash_apply, ModularGroup.denom_S, zpow_neg, zpow_two] at h
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  have hz2 : (z : ℂ) * (z : ℂ) ≠ 0 := mul_ne_zero hz hz
  have h' := congrArg (· * ((z : ℂ) * (z : ℂ))) h
  simp only at h'
  -- Cancel the `z^(-2)` factor coming from the slash action.
  rw [mul_assoc, inv_mul_cancel₀ hz2, mul_one] at h'
  simpa [sq, mul_comm, mul_left_comm, mul_assoc] using h'

/-- Convert a geometric-series expression to a divisor-sum expression via `sigma`. -/
public lemma tsum_eq_tsum_sigma (z : ℍ) : ∑' n : ℕ, (n + 1) *
    cexp (2 * π * Complex.I * (n + 1) * z) / (1 - cexp (2 * π * Complex.I * (n + 1) * z)) =
    ∑' n : ℕ, sigma 1 (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) := by
  -- Use the general sigma identity for geometric series from Mathlib, then shift `ℕ+` → `ℕ`.
  set r : ℂ := cexp (2 * ↑π * Complex.I * (z : ℂ))
  have hr : ‖r‖ < 1 := by simpa [r] using exp_upperHalfPlane_lt_one z
  have hσ :
      (∑' n : ℕ+, (n : ℂ) * r ^ (n : ℕ) / (1 - r ^ (n : ℕ))) =
        ∑' n : ℕ+, (sigma 1 n : ℂ) * r ^ (n : ℕ) := by
    simpa [pow_one] using (tsum_pow_div_one_sub_eq_tsum_sigma (𝕜 := ℂ) (r := r) hr 1)
  -- Convert both sides of the goal to `ℕ+`-indexed sums and apply `hσ`.
  have hL :
      (∑' n : ℕ, (n + 1) * r ^ (n + 1) / (1 - r ^ (n + 1))) =
        ∑' n : ℕ+, (n : ℂ) * r ^ (n : ℕ) / (1 - r ^ (n : ℕ)) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using
      (tsum_pnat_eq_tsum_succ3 (fun n : ℕ => (n : ℂ) * r ^ n / (1 - r ^ n))).symm
  have hR :
      (∑' n : ℕ, sigma 1 (n + 1) * r ^ (n + 1)) =
        ∑' n : ℕ+, (sigma 1 n : ℂ) * r ^ (n : ℕ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using
      (tsum_pnat_eq_tsum_succ3 (fun n : ℕ => (sigma 1 n : ℂ) * r ^ n)).symm
  -- Rewrite the original sums as `r`-powers via `exp_aux`.
  have hL' :
      (∑' n : ℕ, (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) /
          (1 - cexp (2 * π * Complex.I * (n + 1) * z))) =
        ∑' n : ℕ, (n + 1) * r ^ (n + 1) / (1 - r ^ (n + 1)) := by
    refine tsum_congr fun n => ?_
    have : cexp (2 * π * Complex.I * (n + 1) * z) = r ^ (n + 1) := by
      simpa [r, mul_assoc, mul_left_comm, mul_comm] using (exp_aux z (n + 1))
    simp [this]
  have hR' :
      (∑' n : ℕ, sigma 1 (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z)) =
        ∑' n : ℕ, sigma 1 (n + 1) * r ^ (n + 1) := by
    refine tsum_congr fun n => ?_
    have : cexp (2 * π * Complex.I * (n + 1) * z) = r ^ (n + 1) := by
      simpa [r, mul_assoc, mul_left_comm, mul_comm] using (exp_aux z (n + 1))
    simp [this]
  -- Combine.
  calc
    (∑' n : ℕ,
          (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) /
            (1 - cexp (2 * π * Complex.I * (n + 1) * z))) =
        ∑' n : ℕ, (n + 1) * r ^ (n + 1) / (1 - r ^ (n + 1)) := hL'
    _ = ∑' n : ℕ+, (n : ℂ) * r ^ (n : ℕ) / (1 - r ^ (n : ℕ)) := hL
    _ = ∑' n : ℕ+, (sigma 1 n : ℂ) * r ^ (n : ℕ) := hσ
    _ = ∑' n : ℕ, sigma 1 (n + 1) * r ^ (n + 1) := hR.symm
    _ = ∑' n : ℕ, sigma 1 (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) := hR'.symm

/-- A standard Fourier expansion formula for `E₂`. -/
public lemma E₂_eq (z : UpperHalfPlane) : E₂ z =
    1 - 24 * ∑' (n : ℕ+),
    ↑n * cexp (2 * π * Complex.I * n * z) / (1 - cexp (2 * π * Complex.I * n * z)) := by
  rw [E₂]
  simp only [one_div, mul_inv_rev, Pi.smul_apply, smul_eq_mul]
  rw [G2_q_exp]
  rw [mul_sub]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.pi_pos.ne')
  congr 1
  · rw [riemannZeta_two]
    field_simp [hpi]
  · rw [← mul_assoc]
    congr 1
    · rw [riemannZeta_two]
      field_simp [hpi]
      ring
    · have hl := tsum_pnat_eq_tsum_succ3 (fun n => sigma 1 n * cexp (2 * π * Complex.I * n * z))
      have hr := tsum_pnat_eq_tsum_succ3 (fun n => n * cexp (2 * π * Complex.I * n * z) / (1 - cexp
        (2 * π * Complex.I * n * z)))
      rw [hl, hr]
      simpa [Nat.cast_add, Nat.cast_one] using (tsum_eq_tsum_sigma z).symm

end Definitions
