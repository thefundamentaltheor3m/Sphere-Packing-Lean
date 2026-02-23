module
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Elementary exponential bounds

This file collects elementary estimates of the form `x ^ k * exp (-π * x) ≤ C` on `ℝ≥0`, and
packages them into convenient decay lemmas used when proving that a function (or its derivatives)
is Schwartz.

## Main statements
* `pow_mul_exp_neg_pi_bounded`
* `decay_of_bounding_uniform_norm`
* `decay_of_bounding_uniform_norm_iteratedDeriv`
-/

namespace MagicFunction.a.IntegralEstimates

open scoped Real Topology
open Real Set Filter

/-- For each `k`, the function `x ↦ x ^ k * exp (-π * x)` is bounded on `[0, ∞)`. -/
public lemma pow_mul_exp_neg_pi_bounded (k : ℕ) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → x ^ k * rexp (-π * x) ≤ C := by
  let f : ℝ → ℝ := fun x => x ^ k * rexp (-π * x)
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
      (tendsto_id.const_mul_atTop Real.pi_pos)
    have hpi0 : (π ^ k : ℝ) ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
    have hf : f = fun x : ℝ => (π ^ k)⁻¹ * ((π * x) ^ k * rexp (-(π * x))) := by
      funext x
      simp [f, mul_assoc, mul_left_comm, mul_comm, mul_pow, hpi0]
    simpa [hf] using (tendsto_const_nhds.mul h)
  have h_event : ∀ᶠ x in atTop, f x ≤ 1 :=
    (hlim.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))).mono fun _ hx => le_of_lt hx
  rcases (Filter.eventually_atTop.1 h_event) with ⟨N, hN⟩
  let N0 : ℝ := max N 0
  have hN0 : ∀ x ≥ N0, f x ≤ 1 := fun x hx => hN x ((le_max_left N 0).trans hx)
  have hf_cont : Continuous f := by
    fun_prop
  have hne : (Set.Icc (0 : ℝ) N0).Nonempty := nonempty_Icc.2 (le_max_right N 0)
  obtain ⟨x0, hx0, hxmax⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) N0)).exists_isMaxOn hne (hf_cont.continuousOn)
  refine ⟨max 1 (f x0), ?_⟩
  intro x hx
  by_cases hxN : x ≤ N0
  · have hxIcc : x ∈ Set.Icc (0 : ℝ) N0 := ⟨hx, hxN⟩
    exact (hxmax hxIcc).trans (le_max_right _ _)
  · exact (hN0 x (le_of_not_ge hxN)).trans (le_max_left _ _)

/--
Turn a uniform exponential bound `‖I x‖ ≤ C₁ * exp (-π * x)` into the inverse-power decay
statement required by `SchwartzMap`.
-/
public lemma decay_of_bounding_uniform_norm {E : Type*} [SeminormedAddCommGroup E] {I : ℝ → E}
    (hI : ∃ C₁ > 0, ∀ x : ℝ, 0 ≤ x → ‖I x‖ ≤ C₁ * rexp (-π * x)) :
    ∀ (k : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖I x‖ ≤ C := by
  intro k
  rcases hI with ⟨C₁, hC₁_pos, hC₁⟩
  rcases pow_mul_exp_neg_pi_bounded (k := k) with ⟨Cpow, hCpow⟩
  refine ⟨C₁ * Cpow, ?_⟩
  intro x hx
  have hIx : ‖I x‖ ≤ C₁ * rexp (-π * x) := hC₁ x hx
  calc
    ‖x‖ ^ k * ‖I x‖ ≤ ‖x‖ ^ k * (C₁ * rexp (-π * x)) :=
      mul_le_mul_of_nonneg_left hIx (by positivity)
    _ = C₁ * (x ^ k * rexp (-π * x)) := by
      simp [Real.norm_of_nonneg hx, mul_left_comm, mul_comm]
    _ ≤ C₁ * Cpow := by gcongr; exact hCpow x hx

/--
Variant of `decay_of_bounding_uniform_norm` for iterated derivatives.  The input bound is stated
using `iteratedDeriv`, and is transferred to `iteratedFDeriv`.
-/
public lemma decay_of_bounding_uniform_norm_iteratedDeriv {I : ℝ → ℂ} (n : ℕ)
    (hI : ∃ C₁ > 0, ∀ x : ℝ, 0 ≤ x → ‖iteratedDeriv n I x‖ ≤ C₁ * rexp (-π * x)) :
    ∀ (k : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I x‖ ≤ C := by
  rcases hI with ⟨C₁, hC₁_pos, hC₁⟩
  refine decay_of_bounding_uniform_norm (I := fun x : ℝ ↦ iteratedFDeriv ℝ n I x) ?_
  refine ⟨C₁, hC₁_pos, ?_⟩
  intro x hx
  simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := n) (f := I) (x := x)] using
    hC₁ x hx

end MagicFunction.a.IntegralEstimates
