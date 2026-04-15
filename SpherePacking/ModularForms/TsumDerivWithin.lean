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

