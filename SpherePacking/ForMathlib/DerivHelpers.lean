module
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Derivative helpers

Small `HasDerivAt`, `iteratedDeriv`, `iteratedFDeriv`, norm/inequality, and compact-interval
bound lemmas duplicated across the project.
-/

namespace SpherePacking.ForMathlib

open scoped Complex Topology
open Filter

/-- A continuous function on `Icc a b` admits a (global) upper bound on that interval. -/
public lemma exists_upper_bound_on_Icc {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b)) : ∃ C, ∀ x ∈ Set.Icc a b, g x ≤ C :=
  let ⟨x0, _, hxmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hab) hg
  ⟨g x0, fun _ hx => hxmax hx⟩

/-- If `g` is positive and continuous on `Icc a b`, then it admits a positive uniform
lower bound. -/
public lemma exists_lower_bound_pos_on_Icc {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b)) (hpos : ∀ x ∈ Set.Icc a b, 0 < g x) :
    ∃ c, 0 < c ∧ ∀ x ∈ Set.Icc a b, c ≤ g x := by
  simpa using isCompact_Icc.exists_forall_le' (f := g) hg (a := (0 : ℝ)) hpos

/-- Derivative of `y ↦ a * exp((y : ℂ) * c)`. -/
public lemma hasDerivAt_mul_cexp_ofReal_mul_const (a c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ a * cexp ((y : ℂ) * c))
      (c * (a * cexp ((x : ℂ) * c))) x := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (show HasDerivAt (fun y : ℝ ↦ cexp ((y : ℂ) * c)) (cexp ((x : ℂ) * c) * c) x by
      simpa using ((hasDerivAt_mul_const (x := (x : ℂ)) c).comp_ofReal).cexp).const_mul a

/-- Derivative of `y ↦ (c ^ n) * (a * exp((y : ℂ) * c))`. -/
public lemma hasDerivAt_pow_mul_mul_cexp_ofReal_mul_const (a c : ℂ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (c ^ n) * (a * cexp ((y : ℂ) * c)))
      ((c ^ (n + 1)) * (a * cexp ((x : ℂ) * c))) x := by
  simpa [pow_succ, mul_assoc] using
    (hasDerivAt_mul_cexp_ofReal_mul_const a c x).const_mul (c ^ n)

/-- If `x ∈ ball x₀ ε`, then `|x| ≤ |x₀| + ε`. -/
public lemma abs_le_abs_add_of_mem_ball {x x₀ ε : ℝ} (hx : x ∈ Metric.ball x₀ ε) :
    |x| ≤ |x₀| + ε := by
  have : |x - x₀| < ε := by simpa [Metric.mem_ball, Real.dist_eq] using hx
  linarith [abs_sub_abs_le_abs_sub x x₀]

/-- If `‖z‖ ≤ 2`, then `‖(π * I) * z‖ ≤ 2 * π`. -/
public lemma norm_mul_pi_I_le_two_pi {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ‖((Real.pi : ℂ) * (Complex.I : ℂ)) * z‖ ≤ 2 * Real.pi := by
  simpa [mul_assoc, abs_of_nonneg Real.pi_pos.le, mul_comm] using
    mul_le_mul_of_nonneg_left hz Real.pi_pos.le

/-- If `0 ≤ a ≤ C * b` with `0 < b`, then `0 ≤ C`. -/
public lemma nonneg_of_nonneg_le_mul {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (h : a ≤ C * b) :
    0 ≤ C :=
  nonneg_of_mul_nonneg_left (ha.trans h) hb

/-- If `I (n+1)` is the derivative of `I n`, then iteratedDeriv `n` of `I 0` is `I n`. -/
public lemma iteratedDeriv_eq_of_hasDerivAt_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (I : ℕ → ℝ → E)
    (hI : ∀ n x, HasDerivAt (I n) (I (n + 1) x) x) (n : ℕ) :
    iteratedDeriv n (I 0) = I n := by
  induction n with
  | zero => ext x; simp [iteratedDeriv_zero]
  | succ n ih => ext x; simpa [iteratedDeriv_succ, ih] using (hI n x).deriv

/-- If `I (n+1)` is the derivative of `I n` at every point, then `I 0` is smooth. -/
public theorem contDiff_of_hasDerivAt_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (I : ℕ → ℝ → E)
    (hI : ∀ n x, HasDerivAt (I n) (I (n + 1) x) x) : ContDiff ℝ (⊤ : ℕ∞) (I 0) :=
  contDiff_of_differentiable_iteratedDeriv (n := (⊤ : ℕ∞)) fun m _ => by
    simpa [iteratedDeriv_eq_of_hasDerivAt_succ (I := I) hI m] using
      fun x => (hI m x).differentiableAt

/-- Bound the norm of `m`-th iterated derivative of `t ↦ exp(t * a * I)` by `|a| ^ m`. -/
public lemma norm_iteratedFDeriv_cexp_mul_ofReal_mul_I_le (a : ℝ) (m : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ m (fun t : ℝ ↦ Complex.exp ((t : ℂ) * ((a : ℂ) * Complex.I))) x‖ ≤
      |a| ^ m := by
  have hiter : ∀ (c : ℂ) (m : ℕ),
      iteratedDeriv m (fun x : ℝ ↦ Complex.exp ((x : ℂ) * c)) =
        fun x : ℝ ↦ c ^ m * Complex.exp ((x : ℂ) * c) := by
    intro c m
    induction m with
    | zero => funext x; simp [iteratedDeriv_zero]
    | succ m ih => funext x; simpa [iteratedDeriv_succ, ih, mul_assoc] using
        (hasDerivAt_pow_mul_mul_cexp_ofReal_mul_const (a := (1 : ℂ)) (c := c) (n := m) x).deriv
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    show iteratedDeriv m (fun t : ℝ ↦ Complex.exp ((t : ℂ) * ((a : ℂ) * Complex.I))) x =
      ((a : ℂ) * Complex.I) ^ m * Complex.exp ((x : ℂ) * ((a : ℂ) * Complex.I)) from
      congrArg (fun F : ℝ → ℂ => F x) (hiter ((a : ℂ) * Complex.I) m)]
  simp [norm_pow, Complex.norm_exp,
    show ((x : ℂ) * ((a : ℂ) * Complex.I)).re = 0 by simp [mul_left_comm, mul_comm]]

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
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    show iteratedDeriv m (fun t : ℝ ↦ (-1 / 2 : ℂ) •
        Complex.exp ((t : ℂ) * ((Real.pi : ℂ) * Complex.I))) x =
      (-1 / 2 : ℂ) • iteratedDeriv m
        (fun t : ℝ ↦ Complex.exp ((t : ℂ) * ((Real.pi : ℂ) * Complex.I))) x by simp]
  simpa [show ‖(-1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by simp] using
    mul_le_mul_of_nonneg_left
      (by simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
        norm_iteratedFDeriv_cexp_mul_pi_I_le m x : _ ≤ Real.pi ^ m)
      (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))

/-- If `f` has bounded derivatives and `g` has one-sided decay of all derivatives, then `f * g`
has one-sided decay for a fixed iterated derivative order. -/
public theorem decay_iteratedFDeriv_mul_of_bound_left
    {f g : ℝ → ℂ} (k n : ℕ) (B : ℕ → ℝ)
    (hf_cont : ContDiff ℝ (⊤ : ℕ∞) f) (hg_cont : ContDiff ℝ (⊤ : ℕ∞) g)
    (hbound_f : ∀ m : ℕ, ∀ x : ℝ, ‖iteratedFDeriv ℝ m f x‖ ≤ B m)
    (hdec_g : ∀ m : ℕ, ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ m g x‖ ≤ C) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : ℝ ↦ f y * g y) x‖ ≤ C := by
  let Cg : ℕ → ℝ := fun m ↦ Classical.choose (hdec_g m)
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B i * Cg (n - i), fun x hx => ?_⟩
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : ℝ ↦ f y * g y) x‖
        ≤ ∑ i ∈ Finset.range (n + 1),
          ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖
            * ‖iteratedFDeriv ℝ (n - i) g x‖) := by
          simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (⊤ : ℕ∞))
              hf_cont hg_cont x (n := n) (hn := WithTop.coe_le_coe.2 le_top))
              (by positivity : (0 : ℝ) ≤ ‖x‖ ^ k)
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B i * Cg (n - i) :=
          Finset.sum_le_sum fun i _ => by
            have hfi : ‖iteratedFDeriv ℝ i f x‖ ≤ B i := hbound_f i x
            have hchoose0 : 0 ≤ (n.choose i : ℝ) := by positivity
            have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hfi hchoose0)
              (Classical.choose_spec (hdec_g (n - i)) x hx) (by positivity)
              (mul_nonneg hchoose0 ((norm_nonneg _).trans hfi))
            grind only

end SpherePacking.ForMathlib
