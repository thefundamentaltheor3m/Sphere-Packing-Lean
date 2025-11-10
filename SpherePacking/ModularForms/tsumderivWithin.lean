import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.ContinuousMap.Compact
import SpherePacking.ModularForms.exp_lems
import SpherePacking.ModularForms.iteratedderivs


open UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat


abbrev ℍ' := {z : ℂ | 0 < z.im}

lemma upper_half_plane_isOpen :
    IsOpen ℍ' := by
  apply isOpen_lt (by fun_prop) (by fun_prop)

theorem derivWithin_tsum_fun' {α : Type _} (f : α → ℂ → ℂ) {s : Set ℂ}
    (hs : IsOpen s) (x : ℂ) (hx : x ∈ s) (hf : ∀ y ∈ s, Summable fun n : α => f n y)
    (hu :∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ n (k : K), ‖derivWithin (f n) s k‖ ≤ u n)
    (hf2 : ∀ n (r : s), DifferentiableAt ℂ (f n) r) :
    derivWithin (fun z => ∑' n : α, f n z) s x = ∑' n : α, derivWithin (fun z => f n z) s x := by
  apply HasDerivWithinAt.derivWithin
  · apply HasDerivAt.hasDerivWithinAt
    have A :
      ∀ x : ℂ,
        x ∈ s →
          Tendsto (fun t : Finset α => ∑ n ∈ t, (fun z => f n z) x) atTop
            (𝓝 (∑' n : α, (fun z => f n z) x)) :=
          fun y hy ↦ Summable.hasSum <| hf y hy
    apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ A hx
    · use fun n : Finset α => fun a => ∑ i ∈ n, derivWithin (fun z => f i z) s a
    · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
      intro K hK1 hK2
      have HU := hu K hK1 hK2
      obtain ⟨u, hu1, hu2⟩ := HU
      apply tendstoUniformlyOn_tsum hu1
      intro n x hx
      apply hu2 n ⟨x, hx⟩
    filter_upwards
    intro t r hr
    apply HasDerivAt.fun_sum
    intro q hq
    apply HasDerivWithinAt.hasDerivAt
    · apply DifferentiableWithinAt.hasDerivWithinAt
      apply (hf2 q ⟨r, hr⟩).differentiableWithinAt
    exact IsOpen.mem_nhds hs hr
  apply IsOpen.uniqueDiffWithinAt hs hx


theorem der_iter_eq_der_aux2 (k n : ℕ) (r : ℍ') :
  DifferentiableAt ℂ
    (fun z : ℂ =>
      iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ' z) ↑r :=
  by
  have hh :
      DifferentiableOn ℂ (fun t => (2 * ↑π * Complex.I * n) ^ k *
      Complex.exp (2 * ↑π * Complex.I * n * t)) ℍ' := by
    apply Differentiable.differentiableOn;
    apply Differentiable.const_mul
    apply Differentiable.cexp
    apply Differentiable.const_mul
    apply differentiable_id
  apply DifferentiableOn.differentiableAt
  · apply DifferentiableOn.congr hh
    intro x hx
    apply exp_iter_deriv_within k n hx
  refine IsOpen.mem_nhds ?_ ?_
  · apply isOpen_lt (by fun_prop) (by fun_prop)
  exact r.2

theorem der_iter_eq_der2 (k n : ℕ) (r : ℍ') :
    deriv (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ↑r =
      derivWithin (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ')
        ℍ'
        ↑r :=
  by
  simp
  apply symm
  apply DifferentiableAt.derivWithin
  · apply der_iter_eq_der_aux2
  apply IsOpen.uniqueDiffOn upper_half_plane_isOpen
  apply r.2

theorem der_iter_eq_der2' (k n : ℕ) (r : ℍ') :
    derivWithin (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ')
      ℍ' ↑r =
      iteratedDerivWithin (k + 1) (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ' ↑r :=
  by
  rw [iteratedDerivWithin_succ]


noncomputable def cts_exp_two_pi_n (K : Set ℂ) : ContinuousMap K ℂ where
  toFun := fun r : K => Complex.exp (2 * ↑π * Complex.I * r)


theorem iter_deriv_comp_bound2 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ,
      Summable u ∧
        ∀ (n : ℕ) (r : K),
        ‖(derivWithin (iteratedDerivWithin k
          (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ℍ' r)‖ ≤ u n := by
  have : CompactSpace K := by
    rw [← isCompact_univ_iff]
    rw [isCompact_iff_isCompact_univ] at hK2
    apply hK2
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖
  have hr : ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖ < 1 :=
    by
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact]
    intro x; rw [BoundedContinuousFunction.mkOfCompact_apply]; simp_rw [cts_exp_two_pi_n]
    simp only [ContinuousMap.coe_mk]
    apply exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩; linarith
  have hr2 : 0 ≤ r := by apply norm_nonneg _
  have hu : Summable fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ (k + 1) * r ^ n)‖ :=
    by
    have : ∀ (n : ℕ), ((2 * ↑π)^(k+1))* ‖((n) ^ (k + 1) * (r ^ n))‖ =
      ‖((2 * ↑π * Complex.I * n) ^ (k + 1) * r ^ n)‖ := by
        intro n
        norm_cast
        simp only [Nat.cast_pow, norm_mul, norm_pow, Real.norm_eq_abs,
          ofReal_mul, ofReal_ofNat, ofReal_pow, norm_ofNat, norm_real, norm_I,
          mul_one, norm_natCast]
        norm_cast
        simp only [Nat.cast_pow]
        have hh : |π| = π := by simp [Real.pi_pos.le]
        rw [hh]
        ring
    apply Summable.congr _ this
    rw [summable_mul_left_iff]
    apply summable_norm_pow_mul_geometric_of_norm_lt_one
    convert hr
    rw [norm_norm]
    norm_cast
    apply pow_ne_zero
    apply mul_ne_zero
    linarith
    apply Real.pi_ne_zero
  · use fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ (k + 1) * r ^ n)‖, hu
    intro n t
    have go := der_iter_eq_der2' k n ⟨t.1, hK1 t.2⟩
    simp at *
    simp_rw [go]
    have h1 := exp_iter_deriv_within (k + 1) n (hK1 t.2)
    norm_cast at *
    simp at *
    rw [h1]
    simp
    have ineqe : ‖(Complex.exp (2 * π * Complex.I * n * t))‖ ≤ ‖r‖ ^ n := by
      have hw1 :
        ‖ (Complex.exp (2 * π * Complex.I * n * t))‖ =
          ‖ (Complex.exp (2 * π * Complex.I * t))‖ ^ n := by
            norm_cast
            rw [← Complex.norm_pow];
            congr;
            rw [← exp_nat_mul];
            ring_nf
      rw [hw1]
      norm_cast
      apply pow_le_pow_left₀
      simp only [norm_nonneg]
      have :=
        BoundedContinuousFunction.norm_coe_le_norm
          (BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)) t
      rw [norm_norm]
      simpa using this
    apply mul_le_mul
    · simp
    · simp at ineqe
      convert ineqe
    · positivity
    positivity


theorem hasDerivAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) x :=
  by
  have A :
    ∀ x : ℂ,
      x ∈ s →
        Tendsto (fun t : Finset α => ∑ n ∈ t, (fun z => f n z) x) atTop
          (𝓝 (∑' n : α, (fun z => f n z) x)) :=
    by
    intro y hy
    apply Summable.hasSum
    simp
    apply hf y hy
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ A hx
  · use fun n : Finset α => fun a => ∑ i ∈ n, derivWithin (fun z => f i z) s a
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
    intro K hK1 hK2
    have HU := hu K hK1 hK2
    obtain ⟨u, hu1, hu2⟩ := HU
    apply tendstoUniformlyOn_tsum hu1
    intro n x hx
    apply hu2 n ⟨x, hx⟩
  filter_upwards
  intro t r hr
  apply HasDerivAt.fun_sum
  intro q hq
  apply HasDerivWithinAt.hasDerivAt
  · apply DifferentiableWithinAt.hasDerivWithinAt
    apply (hf2 q ⟨r, hr⟩).differentiableWithinAt
  exact IsOpen.mem_nhds hs hr


theorem hasDerivWithinAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :
      ∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivWithinAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) s x :=
      by
  apply (hasDerivAt_tsum_fun f hs x hx hf hu hf2).hasDerivWithinAt




theorem iter_deriv_comp_bound3 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ,
      Summable u ∧
        ∀ (n : ℕ) (r : K),
          (2 * |π| * n) ^ k * ‖(Complex.exp (2 * ↑π * Complex.I * n * r))‖ ≤ u n :=
  by
  have : CompactSpace K := by
    rw [← isCompact_univ_iff]
    rw [isCompact_iff_isCompact_univ] at hK2
    apply hK2
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖
  have hr : ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖ < 1 :=
    by
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact]
    intro x; rw [BoundedContinuousFunction.mkOfCompact_apply]; simp_rw [cts_exp_two_pi_n]
    simp only [ContinuousMap.coe_mk]
    apply exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩; linarith
  have hr2 : 0 ≤ r := by apply norm_nonneg _
  have hu : Summable fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ (k) * r ^ n)‖ :=
    by
    have : ∀ (n : ℕ), ((2 * ↑π)^(k))* ‖((n) ^ (k) * (r ^ n))‖ =
      ‖((2 * ↑π * Complex.I * n) ^ (k) * r ^ n)‖ := by
        intro n
        norm_cast
        simp only [Nat.cast_pow, norm_mul, norm_pow, Real.norm_eq_abs,
          ofReal_mul, ofReal_ofNat, ofReal_pow, norm_ofNat, norm_real, norm_I,
          mul_one, norm_natCast]
        norm_cast
        simp only [Nat.cast_pow]
        have hh : |π| = π := by simp [Real.pi_pos.le]
        rw [hh]
        ring
    apply Summable.congr _ this
    rw [summable_mul_left_iff]
    apply summable_norm_pow_mul_geometric_of_norm_lt_one
    convert hr
    rw [norm_norm]
    norm_cast
    apply pow_ne_zero
    apply mul_ne_zero
    linarith
    apply Real.pi_ne_zero
  use fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ (k) * r ^ n)‖, hu
  intro n t
  simp
  have ineqe : ‖(Complex.exp (2 * π * Complex.I * n * t))‖ ≤ ‖r‖ ^ n :=
    by
    have hw1 :
      ‖ (Complex.exp (2 * π * Complex.I * n * t))‖ =
        ‖ (Complex.exp (2 * π * Complex.I * t))‖ ^ n := by
          norm_cast
          rw [← Complex.norm_pow];
          congr;
          rw [← exp_nat_mul];
          ring_nf
    rw [hw1]
    norm_cast
    apply pow_le_pow_left₀
    simp only [norm_nonneg]
    have :=
      BoundedContinuousFunction.norm_coe_le_norm
        (BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)) t
    rw [norm_norm]
    simpa using this
  apply mul_le_mul
  · simp
  · simp at ineqe
    convert ineqe
  · positivity
  positivity
