module
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.ContinuousMap.Compact
public import SpherePacking.ModularForms.IteratedDerivs


/-!
# Termwise differentiation of `tsum`

This file contains infrastructure for differentiating a series `∑' n, f n z` termwise using
`derivWithin` and `iteratedDerivWithin`, specialized to exponential series on the upper half-plane.

## Main definitions
* `ℍ'`

## Main statements
* `derivWithin_tsum_fun'`
* `hasDerivAt_tsum_fun`
* `hasDerivWithinAt_tsum_fun`
-/

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

/-- The exponential `exp(2π i z)` has norm strictly less than `1` for `z ∈ ℍ`. -/
public theorem exp_upperHalfPlane_lt_one (z : ℍ) :
    ‖(Complex.exp (2 * ↑π * Complex.I * z))‖ < 1 := by
  simpa using UpperHalfPlane.norm_exp_two_pi_I_lt_one z

/-- A shifted-power variant of `exp_upperHalfPlane_lt_one`. -/
public theorem exp_upperHalfPlane_lt_one_nat (z : ℍ) (n : ℕ) :
    ‖(Complex.exp (2 * ↑π * Complex.I * (n + 1) * z))‖ < 1 := by
  have hn : (0 : ℝ) < (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  let z' : ℍ :=
    ⟨(n + 1 : ℂ) * z, by
      simpa [Complex.mul_im] using mul_pos hn z.im_pos⟩
  simpa [z', mul_assoc] using UpperHalfPlane.norm_exp_two_pi_I_lt_one z'

/-- Periodicity of the exponential factor under integer translation. -/
public lemma exp_periodo (z : ℍ) (n : ℕ) :
    cexp (2 * ↑π * Complex.I * ↑↑n * (1 + ↑z)) = cexp (2 * ↑π * Complex.I * ↑↑n * ↑z) := by
  simpa [mul_add, add_mul, mul_assoc, add_assoc, add_comm, mul_comm, mul_left_comm]
    using (exp_periodic.nat_mul n (2 * π * Complex.I * n * z))


/-! ## The open upper half-plane as a subset of `ℂ` -/

/--
The subset of `ℂ` with positive imaginary part, used for `derivWithin` and `iteratedDerivWithin`.
-/
@[expose, reducible] public def ℍ' : Set ℂ := {z : ℂ | 0 < z.im}

/-- The set `ℍ'` is open. -/
public lemma upper_half_plane_isOpen :
    IsOpen ℍ' := by
  simpa [ℍ'] using isOpen_upperHalfPlaneSet

private theorem hasDerivAt_tsum_fun_core {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu : ∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) x := by
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy => (hf y hy).hasSum) hx
    (f' := fun t : Finset α => fun a => ∑ i ∈ t, derivWithin (fun z => f i z) s a)
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
    intro K hK1 hK2
    obtain ⟨u, hu1, hu2⟩ := hu K hK1 hK2
    refine tendstoUniformlyOn_tsum hu1 ?_
    intro n x hx
    exact hu2 n ⟨x, hx⟩
  · filter_upwards with t r hr using HasDerivAt.fun_sum
      (fun q hq =>
        ((hf2 q ⟨r, hr⟩).differentiableWithinAt.hasDerivWithinAt.hasDerivAt) (hs.mem_nhds hr))

/-- A `derivWithin`-of-`tsum` lemma under a locally uniform summability bound. -/
public theorem derivWithin_tsum_fun' {α : Type _} (f : α → ℂ → ℂ) {s : Set ℂ}
    (hs : IsOpen s) (x : ℂ) (hx : x ∈ s) (hf : ∀ y ∈ s, Summable fun n : α => f n y)
    (hu :∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ n (k : K), ‖derivWithin (f n) s k‖ ≤ u n)
    (hf2 : ∀ n (r : s), DifferentiableAt ℂ (f n) r) :
    derivWithin (fun z => ∑' n : α, f n z) s x = ∑' n : α, derivWithin (fun z => f n z) s x := by
  simpa using
    (HasDerivWithinAt.derivWithin (hasDerivAt_tsum_fun_core f hs x hx hf hu hf2).hasDerivWithinAt
      (IsOpen.uniqueDiffWithinAt hs hx))

theorem der_iter_eq_der_aux2 (k n : ℕ) (r : ℍ') :
  DifferentiableAt ℂ
    (fun z : ℂ =>
      iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ' z) ↑r := by
  let f : ℂ → ℂ :=
    iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ'
  let g : ℂ → ℂ := fun t =>
    (2 * ↑π * Complex.I * n) ^ k * Complex.exp (2 * ↑π * Complex.I * n * t)
  have hfg : f =ᶠ[𝓝 (↑r : ℂ)] g := by
    filter_upwards [upper_half_plane_isOpen.mem_nhds r.2] with z hz
    simpa [f, g, ℍ'] using exp_iter_deriv_within k n hz
  have hg : DifferentiableAt ℂ g (↑r : ℂ) := by
    fun_prop
  simpa [f] using hg.congr_of_eventuallyEq hfg

theorem der_iter_eq_der2 (k n : ℕ) (r : ℍ') :
    deriv (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ↑r =
      derivWithin (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ')
        ℍ'
        ↑r := by
  simpa using (derivWithin_of_isOpen (f := iteratedDerivWithin k
    (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') upper_half_plane_isOpen r.2).symm

theorem der_iter_eq_der2' (k n : ℕ) (r : ℍ') :
    derivWithin (iteratedDerivWithin k
        (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ℍ' ↑r =
      iteratedDerivWithin (k + 1)
        (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ' ↑r := by
  rw [iteratedDerivWithin_succ]


noncomputable def cts_exp_two_pi_n (K : Set ℂ) : ContinuousMap K ℂ where
  toFun := fun r : K => Complex.exp (2 * ↑π * Complex.I * r)

private lemma norm_exp_two_pi_I_mul_le_norm_pow (K : Set ℂ) [CompactSpace K] (t : K) (n : ℕ) :
    ‖Complex.exp (2 * π * Complex.I * n * (t : ℂ))‖ ≤
      ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)‖ ^ n := by
  have hpow :
      ‖Complex.exp (2 * π * Complex.I * n * (t : ℂ))‖ =
        ‖Complex.exp (2 * π * Complex.I * (t : ℂ))‖ ^ n := by
    simpa [Complex.norm_pow, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun z : ℂ => ‖z‖) (exp_nat_mul (2 * π * Complex.I * (t : ℂ)) n)
  have hle : ‖Complex.exp (2 * π * Complex.I * (t : ℂ))‖ ≤
      ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)‖ := by
    simpa [BoundedContinuousFunction.mkOfCompact_apply, cts_exp_two_pi_n] using
      BoundedContinuousFunction.norm_coe_le_norm
        (BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)) t
  simpa [hpow] using (pow_le_pow_left₀ (by positivity) hle n)

theorem iter_deriv_comp_bound2 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ,
      Summable u ∧
        ∀ (n : ℕ) (r : K),
        ‖(derivWithin (iteratedDerivWithin k
          (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ℍ' r)‖ ≤ u n := by
  have : CompactSpace K := by
    exact isCompact_iff_compactSpace.mp hK2
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖
  have hr : ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖ < 1 := by
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact]
    · intro x
      simpa [BoundedContinuousFunction.mkOfCompact_apply, cts_exp_two_pi_n]
        using exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩
    linarith
  have hr2 : 0 ≤ r := by apply norm_nonneg _
  have hr' : ‖(r : ℂ)‖ < 1 := by
    have : r < 1 := by simpa [r] using hr
    simpa [Complex.norm_real, Real.norm_of_nonneg hr2] using this
  have huBase : Summable fun n : ℕ => ‖(((n : ℂ) ^ (k + 1) * (r : ℂ) ^ n : ℂ))‖ := by
    simpa using
      (summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℂ) (k := k + 1) (r := (r : ℂ)) hr')
  have hu :
      Summable fun n : ℕ => ‖(((2 * ↑π * Complex.I * n : ℂ) ^ (k + 1) * (r : ℂ) ^ n : ℂ))‖ := by
    have := (huBase.mul_left ‖((2 * ↑π * Complex.I : ℂ) ^ (k + 1))‖)
    refine this.congr (fun n => ?_)
    simp [mul_pow, mul_assoc, mul_left_comm, mul_comm]
  refine ⟨fun n : ℕ => ‖(((2 * ↑π * Complex.I * n : ℂ) ^ (k + 1) * (r : ℂ) ^ n : ℂ))‖, hu, ?_⟩
  intro n t
  have ht : (t : ℂ) ∈ ℍ' := hK1 t.2
  have ineqe : ‖Complex.exp (2 * ↑π * Complex.I * n * t)‖ ≤ r ^ n := by
    simpa [r] using norm_exp_two_pi_I_mul_le_norm_pow (K := K) t n
  have hrn : ‖((r : ℂ) ^ n)‖ = r ^ n := by
    simp [Complex.norm_real, Real.norm_of_nonneg hr2]
  have ineqe' : ‖Complex.exp (2 * ↑π * Complex.I * n * t)‖ ≤ ‖((r : ℂ) ^ n)‖ := by
    simpa [hrn] using ineqe
  have hmul :=
    mul_le_mul_of_nonneg_left ineqe'
      (norm_nonneg (((2 * ↑π * Complex.I * n : ℂ) ^ (k + 1)) : ℂ))
  have hmul' :
      ‖((2 * ↑π * Complex.I * n : ℂ) ^ (k + 1) * Complex.exp (2 * ↑π * Complex.I * n * t))‖ ≤
        ‖((2 * ↑π * Complex.I * n : ℂ) ^ (k + 1) * (r : ℂ) ^ n)‖ := by
    simpa [norm_mul, mul_assoc] using hmul
  simpa [der_iter_eq_der2' k n ⟨(t : ℂ), ht⟩, exp_iter_deriv_within (k + 1) n ht] using hmul'


/-- A `HasDerivAt`-of-`tsum` lemma under the same hypotheses as `derivWithin_tsum_fun'`. -/
public theorem hasDerivAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) x :=
  hasDerivAt_tsum_fun_core f hs x hx hf hu hf2


/-- A `HasDerivWithinAt`-of-`tsum` lemma under the same hypotheses as `derivWithin_tsum_fun'`. -/
public theorem hasDerivWithinAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :
      ∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivWithinAt (fun z => ∑' n : α, f n z)
      (∑' n : α, derivWithin (fun z => f n z) s x) s x :=
  (hasDerivAt_tsum_fun f hs x hx hf hu hf2).hasDerivWithinAt

theorem iter_deriv_comp_bound3 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ,
      Summable u ∧
        ∀ (n : ℕ) (r : K),
          (2 * |π| * n) ^ k * ‖(Complex.exp (2 * ↑π * Complex.I * n * r))‖ ≤ u n := by
  have : CompactSpace K := by
    exact isCompact_iff_compactSpace.mp hK2
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖
  have hr : ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖ < 1 := by
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact]
    · intro x
      simpa [BoundedContinuousFunction.mkOfCompact_apply, cts_exp_two_pi_n]
        using exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩
    linarith
  have hr2 : 0 ≤ r := by apply norm_nonneg _
  have hr' : ‖(r : ℂ)‖ < 1 := by
    have : r < 1 := by simpa [r] using hr
    simpa [Complex.norm_real, Real.norm_of_nonneg hr2] using this
  have huBase : Summable fun n : ℕ => ‖(((n : ℂ) ^ k * (r : ℂ) ^ n : ℂ))‖ := by
    simpa using
      (summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℂ) (k := k) (r := (r : ℂ)) hr')
  have hu : Summable fun n : ℕ => ‖(((2 * ↑π * Complex.I * n : ℂ) ^ k * (r : ℂ) ^ n : ℂ))‖ := by
    have := (huBase.mul_left ‖((2 * ↑π * Complex.I : ℂ) ^ k)‖)
    refine this.congr (fun n => ?_)
    simp [mul_pow, mul_assoc, mul_left_comm, mul_comm]
  refine ⟨fun n : ℕ => ‖(((2 * ↑π * Complex.I * n : ℂ) ^ k * (r : ℂ) ^ n : ℂ))‖, hu, ?_⟩
  intro n t
  have ineqe : ‖Complex.exp (2 * ↑π * Complex.I * n * t)‖ ≤ r ^ n := by
    simpa [r] using norm_exp_two_pi_I_mul_le_norm_pow (K := K) t n
  have hrn : ‖((r : ℂ) ^ n)‖ = r ^ n := by
    simp [Complex.norm_real, Real.norm_of_nonneg hr2]
  have ineqe' : ‖Complex.exp (2 * ↑π * Complex.I * n * t)‖ ≤ ‖((r : ℂ) ^ n)‖ := by
    simpa [hrn] using ineqe
  have hmul :=
    mul_le_mul_of_nonneg_left ineqe'
      (norm_nonneg (((2 * ↑π * Complex.I * n : ℂ) ^ k) : ℂ))
  have hmul' :
      ‖((2 * ↑π * Complex.I * n : ℂ) ^ k)‖ * ‖Complex.exp (2 * ↑π * Complex.I * n * t)‖ ≤
        ‖((2 * ↑π * Complex.I * n : ℂ) ^ k * (r : ℂ) ^ n)‖ := by
    simpa [norm_mul, mul_assoc] using hmul
  have hnormPow : ‖((2 * ↑π * Complex.I * n : ℂ) ^ k)‖ = (2 * |π| * n) ^ k := by
    simp [norm_pow, mul_left_comm, mul_comm, Real.norm_eq_abs]
  simpa [hnormPow, hrn, mul_assoc] using hmul'
