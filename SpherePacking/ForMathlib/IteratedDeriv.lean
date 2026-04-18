module
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.RealDeriv
public import SpherePacking.ForMathlib.DerivHelpers


/-!
# Iterated derivative helpers

This file collects small lemmas about `iteratedDeriv` and `iteratedFDeriv` that are duplicated
across the project.
-/

namespace SpherePacking.ForMathlib

open scoped Topology
open Filter

/-- If `I (n+1)` is the derivative of `I n` at every point, then the `n`-th iterated derivative of
`I 0` is `I n`. -/
public lemma iteratedDeriv_eq_of_hasDerivAt_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : ℕ → ℝ → E)
    (hI : ∀ n x, HasDerivAt (fun y : ℝ => I n y) (I (n + 1) x) x) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => I 0 x) = fun x : ℝ => I n x := by
  induction n with
  | zero => ext x; simp [iteratedDeriv_zero]
  | succ n ih => ext x; simpa [iteratedDeriv_succ, ih] using (hI n x).deriv

/-- Under the same recurrence hypothesis as `iteratedDeriv_eq_of_hasDerivAt_succ`, the iterated
derivative is differentiable. -/
public lemma differentiable_iteratedDeriv_of_hasDerivAt_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : ℕ → ℝ → E)
    (hI : ∀ n x, HasDerivAt (fun y : ℝ => I n y) (I (n + 1) x) x) (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n (fun x : ℝ => I 0 x)) := by
  simpa [iteratedDeriv_eq_of_hasDerivAt_succ (I := I) hI n] using fun x => (hI n x).differentiableAt

/-- If `I (n+1)` is the derivative of `I n` at every point, then `I 0` is smooth. -/
public theorem contDiff_of_hasDerivAt_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : ℕ → ℝ → E)
    (hI : ∀ n x, HasDerivAt (fun y : ℝ => I n y) (I (n + 1) x) x) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => I 0 x) :=
  contDiff_of_differentiable_iteratedDeriv (n := (⊤ : ℕ∞))
    fun m _ => differentiable_iteratedDeriv_of_hasDerivAt_succ (I := I) hI m

/-- If `deriv (G n) = G (n+1)` holds on an open set, then iterated derivatives of `G m` agree with
`G (n+m)` on that set. -/
public lemma eqOn_iteratedDeriv_eq_of_deriv_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} (hs : IsOpen s) (G : ℕ → ℝ → E)
    (hderiv : ∀ n x, x ∈ s → deriv (G n) x = G (n + 1) x) :
    ∀ n m : ℕ, Set.EqOn (iteratedDeriv n (G m)) (G (n + m)) s := by
  intro n
  induction n with
  | zero => intro m x _; simp [iteratedDeriv_zero]
  | succ n ih =>
      intro m x hx
      have hEq : iteratedDeriv n (G m) =ᶠ[𝓝 x] G (n + m) := by
        filter_upwards [hs.mem_nhds hx] with y hy
        exact ih (m := m) hy
      simpa [iteratedDeriv_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Filter.EventuallyEq.deriv_eq hEq).trans (hderiv (n + m) x hx)

/-- Closed form for iterated derivatives of `x ↦ exp (x * c)`. -/
public lemma iteratedDeriv_cexp_mul_const (c : ℂ) (m : ℕ) :
    iteratedDeriv m (fun x : ℝ ↦ Complex.exp ((x : ℂ) * c)) =
      fun x : ℝ ↦ c ^ m * Complex.exp ((x : ℂ) * c) := by
  induction m with
  | zero => funext x; simp [iteratedDeriv_zero]
  | succ m ih => funext x; simpa [iteratedDeriv_succ, ih, mul_assoc] using
      (hasDerivAt_pow_mul_mul_cexp_ofReal_mul_const (a := (1 : ℂ)) (c := c) (n := m) x).deriv

/-- Bound the norm of `m`-th iterated derivative of `t ↦ exp(t * a * I)` by `|a| ^ m` for any
real `a`. -/
public lemma norm_iteratedFDeriv_cexp_mul_ofReal_mul_I_le (a : ℝ) (m : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ m (fun t : ℝ ↦ Complex.exp ((t : ℂ) * ((a : ℂ) * Complex.I))) x‖ ≤
      |a| ^ m := by
  let c : ℂ := (a : ℂ) * Complex.I
  have hnorm_exp : ‖Complex.exp ((x : ℂ) * c)‖ = 1 := by
    simp [Complex.norm_exp, show ((x : ℂ) * c).re = 0 by simp [c, mul_left_comm, mul_comm]]
  calc
    ‖iteratedFDeriv ℝ m (fun t : ℝ ↦ Complex.exp ((t : ℂ) * ((a : ℂ) * Complex.I))) x‖
        = ‖iteratedDeriv m (fun t : ℝ ↦ Complex.exp ((t : ℂ) * c)) x‖ :=
          norm_iteratedFDeriv_eq_norm_iteratedDeriv
    _ = ‖c ^ m * Complex.exp ((x : ℂ) * c)‖ := by
          simpa using congrArg (fun F : ℝ → ℂ => ‖F x‖) (iteratedDeriv_cexp_mul_const (c := c) m)
    _ ≤ |a| ^ m := by simp [norm_pow, c, hnorm_exp]

/-- Bound the norm of `m`-th iterated derivative of `t ↦ exp (t * π i)` by `π ^ m`. -/
public lemma norm_iteratedFDeriv_cexp_mul_pi_I_le (m : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ m (fun t : ℝ ↦ Complex.exp ((t : ℂ) * ((Real.pi : ℂ) * Complex.I))) x‖ ≤
      Real.pi ^ m := by
  simpa [abs_of_nonneg Real.pi_pos.le] using
    norm_iteratedFDeriv_cexp_mul_ofReal_mul_I_le Real.pi m x

/-- Bound the norm of the `m`-th iterated derivative of `(-1/2) • exp (t * π i)`. -/
public lemma norm_iteratedFDeriv_smul_cexp_mul_pi_I_le (m : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ m
        (fun t : ℝ ↦ (-1 / 2 : ℂ) • Complex.exp ((t : ℂ) * ((Real.pi : ℂ) * Complex.I))) x‖ ≤
      (1 / 2 : ℝ) * Real.pi ^ m := by
  let e : ℝ → ℂ := fun t ↦ Complex.exp ((t : ℂ) * ((Real.pi : ℂ) * Complex.I))
  have hsmul : ‖iteratedFDeriv ℝ m (fun t : ℝ ↦ (-1 / 2 : ℂ) • e t) x‖ =
      ‖(-1 / 2 : ℂ)‖ * ‖iteratedFDeriv ℝ m e x‖ := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := m) (f := e) (x := x)]
    simp
  calc
    ‖iteratedFDeriv ℝ m (fun t : ℝ ↦ (-1 / 2 : ℂ) • e t) x‖
        = ‖(-1 / 2 : ℂ)‖ * ‖iteratedFDeriv ℝ m e x‖ := hsmul
    _ ≤ ‖(-1 / 2 : ℂ)‖ * Real.pi ^ m := by
          gcongr
          simpa [e] using norm_iteratedFDeriv_cexp_mul_pi_I_le (m := m) (x := x)
    _ = (1 / 2 : ℝ) * Real.pi ^ m := by simp

/-- If `f` has bounded derivatives and `g` has one-sided decay of all derivatives, then the product
`f * g` has one-sided decay for a fixed iterated derivative order. -/
public theorem decay_iteratedFDeriv_mul_of_bound_left
    {f g : ℝ → ℂ} (k n : ℕ) (B : ℕ → ℝ)
    (hf_cont : ContDiff ℝ (⊤ : ℕ∞) f) (hg_cont : ContDiff ℝ (⊤ : ℕ∞) g)
    (hbound_f : ∀ m : ℕ, ∀ x : ℝ, ‖iteratedFDeriv ℝ m f x‖ ≤ B m)
    (hdec_g :
      ∀ m : ℕ, ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ m g x‖ ≤ C) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : ℝ ↦ f y * g y) x‖ ≤ C := by
  let Cg : ℕ → ℝ := fun m ↦ Classical.choose (hdec_g m)
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B i * Cg (n - i), fun x hx => ?_⟩
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (⊤ : ℕ∞)) hf_cont hg_cont x (n := n)
    (hn := WithTop.coe_le_coe.2 (show (n : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : ℝ ↦ f y * g y) x‖
        ≤ ∑ i ∈ Finset.range (n + 1),
          ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖
            * ‖iteratedFDeriv ℝ (n - i) g x‖) := by
          simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ ‖x‖ ^ k)
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B i * Cg (n - i) :=
          Finset.sum_le_sum fun i _ => by
            have hfi : ‖iteratedFDeriv ℝ i f x‖ ≤ B i := hbound_f i x
            have hgi : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g x‖ ≤ Cg (n - i) :=
              Classical.choose_spec (hdec_g (n - i)) x hx
            have hchoose0 : 0 ≤ (n.choose i : ℝ) := by positivity
            have hBi0 : 0 ≤ B i := (norm_nonneg _).trans hfi
            have hleft : (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ ≤ (n.choose i : ℝ) * B i :=
              mul_le_mul_of_nonneg_left hfi hchoose0
            have hprod := mul_le_mul hleft hgi (by positivity) (mul_nonneg hchoose0 hBi0)
            grind only

end SpherePacking.ForMathlib
