module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.ContinuousMap.Compact
public import SpherePacking.ModularForms.exp_lems

/-!
# Termwise differentiation of series

`hasDerivAt_tsum_fun` differentiates a series of functions termwise on an open set, given
locally-uniform summable bounds on the derivatives on compact subsets. Mathlib's
`derivWithin_tsum` (in `Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn`) is the
`derivWithin` version of this; the `HasDerivAt` form proved here is not yet in Mathlib.

`iter_deriv_comp_bound3` provides the summable geometric bounds on compact subsets of the
upper half-plane for `(2π n)^k · ‖exp (2π i n z)‖`, used for the q-expansion derivative
bounds in `FG.lean`.
-/

@[expose] public section


open UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat


noncomputable def cts_exp_two_pi_n (K : Set ℂ) : ContinuousMap K ℂ where
  toFun := fun r : K => Complex.exp (2 * ↑π * Complex.I * r)


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


theorem iter_deriv_comp_bound3 (K : Set ℂ) (hK1 : K ⊆ {z : ℂ | 0 < z.im}) (hK2 : IsCompact K)
    (k : ℕ) :
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
    · intro x; rw [BoundedContinuousFunction.mkOfCompact_apply]; simp_rw [cts_exp_two_pi_n]
      simp only [ContinuousMap.coe_mk]
      apply exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩
    linarith
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
    · apply summable_norm_pow_mul_geometric_of_norm_lt_one
      convert hr
      rw [norm_norm]
    norm_cast
    apply pow_ne_zero
    apply mul_ne_zero
    · linarith
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
    · simp only [norm_nonneg]
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
