module
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Derivative helpers

Small `HasDerivAt`, `iteratedDeriv`, `iteratedFDeriv`, norm/inequality, and compact-interval
bound lemmas duplicated across the project.
-/

namespace SpherePacking.ForMathlib

open MeasureTheory
open scoped Complex Topology
open Filter

/-- `t ↦ t ^ n * exp (-b * t)` is integrable on `[1, ∞)` when `0 < b`. -/
public lemma integrableOn_pow_mul_exp_neg_mul_Ici (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ ↦ t ^ n * Real.exp (-b * t)) (Set.Ici (1 : ℝ)) volume :=
  (show IntegrableOn (fun t : ℝ ↦ t ^ n * Real.exp (-b * t)) (Set.Ioi (0 : ℝ)) volume by
    simpa [Real.rpow_one, Real.rpow_natCast, one_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (n : ℝ)) (b := b)
        (Nat.cast_nonneg n |>.trans_lt' (by norm_num)) (by simp) hb).mono_set
    fun _ ht => lt_of_lt_of_le (zero_lt_one' ℝ) ht

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
        fun x : ℝ ↦ c ^ m * Complex.exp ((x : ℂ) * c) := fun c m => by
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
        (fun t : ℝ ↦ Complex.exp ((t : ℂ) * ((Real.pi : ℂ) * Complex.I))) x from
      iteratedDeriv_fun_const_smul_field _ _]
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

/-! ## One-sided decay to a radial Schwartz function

Defines the smooth cutoff `cutoff`/`cutoffC` for radial Schwartz constructions and proves the
bridge to global Schwartz on `ℝ`: if `f : ℝ → ℂ` is smooth and satisfies Schwartz-type bounds for
all iterated derivatives on `0 ≤ r`, then the radial function `x ↦ f (‖x‖ ^ 2)` is Schwartz on any
real inner product space `F`.
-/

namespace RadialSchwartz

noncomputable section

open Complex Real

/-- Smooth cutoff: `cutoff r = 0` for `r ≤ -1/2`, `cutoff r = 1` for `0 ≤ r`. -/
@[expose] public def cutoff (r : ℝ) : ℝ := Real.smoothTransition (2 * r + 1)

@[simp] public lemma cutoff_eq_zero_of_le_neg_half {r : ℝ} (hr : r ≤ (-1 / 2 : ℝ)) :
    cutoff r = 0 := by
  simpa [cutoff] using Real.smoothTransition.zero_of_nonpos (x := 2 * r + 1) (by linarith)

@[simp] public lemma cutoff_eq_zero_of_le {r : ℝ} (hr : r ≤ -1) : cutoff r = 0 :=
  cutoff_eq_zero_of_le_neg_half (r := r) (by linarith [hr])

@[simp] public lemma cutoff_eq_one_of_nonneg {r : ℝ} (hr : 0 ≤ r) : cutoff r = 1 := by
  simpa [cutoff] using Real.smoothTransition.one_of_one_le (x := 2 * r + 1) (by linarith)

@[fun_prop]
public lemma cutoff_contDiff : ContDiff ℝ (⊤ : ℕ∞) cutoff := by
  simpa [cutoff] using
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

/-- Complex-valued version of `cutoff`. -/
@[expose] public def cutoffC (r : ℝ) : ℂ := (cutoff r : ℂ)

@[simp] public lemma cutoffC_eq_zero_of_le_neg_half {r : ℝ} (hr : r ≤ (-1 / 2 : ℝ)) :
    cutoffC r = 0 := by simp [cutoffC, cutoff_eq_zero_of_le_neg_half hr]

@[simp] public lemma cutoffC_eq_zero_of_le {r : ℝ} (hr : r ≤ -1) : cutoffC r = 0 := by
  simp [cutoffC, cutoff_eq_zero_of_le hr]

@[simp] public lemma cutoffC_eq_one_of_nonneg {r : ℝ} (hr : 0 ≤ r) : cutoffC r = 1 := by
  simp [cutoffC, cutoff_eq_one_of_nonneg hr]

@[fun_prop]
public lemma cutoffC_contDiff : ContDiff ℝ (⊤ : ℕ∞) cutoffC := by
  simpa [cutoffC] using ofRealCLM.contDiff.comp cutoff_contDiff

/-- If `f` is smooth on `(-1, ∞)` then `r ↦ cutoffC r * f r` is smooth on all of `ℝ`. -/
public lemma contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1 {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioi (-1 : ℝ))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun r ↦ cutoffC r * f r) := by
  rw [contDiff_iff_contDiffAt (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (f := fun r ↦ cutoffC r * f r)]
  intro x
  by_cases hx : x < (-1 / 2 : ℝ)
  · refine (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ ↦ (0 : ℂ)) x).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [cutoffC_eq_zero_of_le_neg_half (r := y) hy.le]
  · have hx' : (-1 : ℝ) < x := by linarith [le_of_not_gt hx]
    exact cutoffC_contDiff.contDiffAt.mul (hf.contDiffAt (isOpen_Ioi.mem_nhds hx'))

end

end RadialSchwartz

section
open SchwartzMap Function RCLike

/-- Lift a Schwartz function on `ℝ` to a Schwartz function on `F` by composing with `‖x‖ ^ 2`. -/
@[expose, simps!]
public noncomputable def schwartzMap_multidimensional_of_schwartzMap_real
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : 𝓢(ℝ, ℂ)) : 𝓢(F, ℂ) :=
  f.compCLM ℝ (Function.hasTemperateGrowth_norm_sq F) <| ⟨1, 1, fun _ => by
    simp only [norm_pow, norm_norm]; nlinarith⟩
end

namespace RadialSchwartz

noncomputable section

open scoped Topology
open Set SchwartzMap

/-- If `cutoffC * f` is smooth and `f` satisfies Schwartz decay bounds on `0 ≤ x`, then
`cutoffC * f` satisfies the global Schwartz decay bounds on `ℝ`. -/
public theorem cutoffC_mul_decay_of_nonneg_of_contDiff
    {f : ℝ → ℂ} (hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r ↦ cutoffC r * f r))
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x‖ ≤ C := fun k n => by
  obtain ⟨Cpos, hCpos⟩ := hf_decay k n
  obtain ⟨Cmid, hCmid⟩ :=
    SpherePacking.ForMathlib.exists_upper_bound_on_Icc
      (g := fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x‖)
      (a := (-1 : ℝ)) (b := 0) (by norm_num) <| by
        simpa using ((continuous_norm.pow k).mul (continuous_norm.comp
          (hg_smooth.continuous_iteratedFDeriv (m := n) (by
            exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))))).continuousOn
  refine ⟨max (max Cmid Cpos) 0, fun x => ?_⟩
  by_cases hx₁ : x < -1
  · simp [show iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x = 0 by
      simpa using (show (fun r ↦ cutoffC r * f r) =ᶠ[𝓝 x] fun _ ↦ (0 : ℂ) by
        filter_upwards [Iio_mem_nhds hx₁] with y hy
        simp [cutoffC_eq_zero_of_le hy.le]).iteratedFDeriv (𝕜 := ℝ) n |>.self_of_nhds]
  · by_cases hx₂ : x ≤ 0
    · exact (hCmid x ⟨le_of_not_gt hx₁, hx₂⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
    · have hxpos : 0 < x := lt_of_not_ge hx₂
      simpa [show iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x = iteratedFDeriv ℝ n f x by
        simpa using (show (fun r ↦ cutoffC r * f r) =ᶠ[𝓝 x] f by
          filter_upwards [Ioi_mem_nhds hxpos] with y hy
          simp [cutoffC_eq_one_of_nonneg hy.le]).iteratedFDeriv (𝕜 := ℝ) n |>.self_of_nhds] using
        (hCpos x hxpos.le).trans ((le_max_right Cmid Cpos).trans (le_max_left _ _))

/-- If `f` is smooth and satisfies one-sided Schwartz decay on `0 ≤ x`, then `cutoffC * f`
satisfies global Schwartz decay on `ℝ`. -/
public theorem cutoffC_mul_decay_of_nonneg
    {f : ℝ → ℂ} (hf_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x‖ ≤ C :=
  cutoffC_mul_decay_of_nonneg_of_contDiff (f := f) (cutoffC_contDiff.mul hf_smooth) hf_decay

namespace Bridge

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### The bridge to `𝓢(F,ℂ)` -/

/-- A cutoff-modified radial profile, used to build a Schwartz function on `ℝ`. -/
@[expose] public def fCut (f : ℝ → ℂ) (r : ℝ) : ℂ := cutoffC r * f r

/-- Package `fCut f` as an element of `𝓢(ℝ, ℂ)`. -/
@[expose] public def fCutSchwartz (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) : 𝓢(ℝ, ℂ) where
  toFun := fCut f
  smooth' := by simpa [fCut] using cutoffC_contDiff.mul hf
  decay' := by simpa [fCut] using cutoffC_mul_decay_of_nonneg (f := f) hf hf_decay

/-- On `0 ≤ r`, `fCut f` agrees with `f`. -/
public lemma fCut_apply_of_nonneg (f : ℝ → ℂ) {r : ℝ} (hr : 0 ≤ r) : fCut f r = f r := by
  simp [fCut, hr]

end Bridge

end

end RadialSchwartz

/-! ## Gaussian Fourier transform lemmas (even dimension `2k`) -/

namespace SpherePacking.ForMathlib

open scoped FourierTransform RealInnerProductSpace Topology
open Complex Real MeasureTheory Filter

noncomputable section

/-! ### Fourier phase factor -/

/-- The phase factor `exp (i * real)` has norm `1`. -/
public lemma norm_phase_eq_one {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (w x : V) :
    ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I)‖ = (1 : ℝ) := by
  simpa using (Complex.norm_exp_ofReal_mul_I (-2 * (π * ⟪x, w⟫)))

/-- The phase factor is a.e. strongly measurable with respect to Lebesgue measure. -/
public lemma aestronglyMeasurable_phase {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasureSpace V] [BorelSpace V] (w : V) :
    AEStronglyMeasurable (fun x : V ↦ cexp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I))
      (volume : Measure V) := by fun_prop

/-- Almost everywhere, the phase factor has norm at most `1`. -/
public lemma ae_norm_phase_le_one {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasureSpace V] (w : V) :
    (∀ᵐ x : V ∂(volume : Measure V),
      ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I)‖ ≤ (1 : ℝ)) :=
  Filter.Eventually.of_forall (fun x => (norm_phase_eq_one (w := w) (x := x)).le)

/-! ### Gaussian factor identities -/

/-- The norm of the Gaussian factor `cexp (π * I * ‖x‖^2 * z)` depends only on `Im z`. -/
public lemma norm_cexp_pi_mul_I_mul_sq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (z : ℂ) (x : V) :
    ‖cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z)‖ = rexp (-π * (‖x‖ ^ 2) * z.im) := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im, pow_two]

/-- A complex Gaussian with positive imaginary parameter is integrable. -/
public lemma integrable_gaussian_cexp_pi_mul_I_mul
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun x : V ↦ cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z)) (volume : Measure V) := by
  simpa [mul_assoc, mul_comm] using
    (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := -((π : ℂ) * I * z))
      (c := (0 : ℂ)) (w := (0 : V))
      (by simpa [Complex.mul_re, Complex.mul_im, mul_comm] using mul_pos Real.pi_pos hz))

/-- Fourier transform of the complex Gaussian in even dimension `2k`. -/
public lemma fourier_gaussian_pi_mul_I_mul_even (k : ℕ) (z : ℂ) (hz : 0 < z.im)
    (w : EuclideanSpace ℝ (Fin (2 * k))) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin (2 * k)) ↦ cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z)) w =
      (((I : ℂ) / z) ^ k) * cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z)) := by
  have hz0 : z ≠ 0 := fun hz0 => (ne_of_gt hz) (by simp [hz0])
  have hπ0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set b : ℂ := -((π : ℂ) * I * z)
  have hb : 0 < b.re := by
    simpa [b, Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm] using
      (mul_pos Real.pi_pos hz : 0 < Real.pi * z.im)
  have hL :
      (fun x : EuclideanSpace ℝ (Fin (2 * k)) ↦ cexp (-(b * ‖x‖ ^ 2))) =
        fun x : EuclideanSpace ℝ (Fin (2 * k)) ↦ cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z) := by
    funext x; simp [b, mul_assoc, mul_comm]
  have hb0 : b ≠ 0 := by
    simpa [b] using neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hπ0 Complex.I_ne_zero) hz0)
  have hdiv : π / b = (I : ℂ) / z := by
    field_simp [b, hb0, hz0]
    have hIIπ : (I : ℂ) * (I * (π : ℂ)) = -(π : ℂ) := by
      rw [show (I : ℂ) * (I * (π : ℂ)) = (I * I) * (π : ℂ) by ac_rfl]; simp [Complex.I_mul_I]
    simp [b, hIIπ, mul_left_comm, mul_comm]
  have hexp : cexp (-(π ^ 2 * ‖w‖ ^ 2) / b) = cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z)) := by
    congr 1
    calc (-(π ^ 2 * ‖w‖ ^ 2) / b : ℂ) = (-(π : ℂ) * ((‖w‖ : ℂ) ^ (2 : ℕ))) * (π / b) := by
          simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]
      _ = (π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z) := by
          simp [hdiv, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  simpa [hL, hdiv, hexp, mul_assoc, mul_left_comm, mul_comm] using
    fourier_gaussian_innerProductSpace (V := EuclideanSpace ℝ (Fin (2 * k))) (b := b) hb w

/-- Integral of the phase factor times a complex Gaussian in even dimension `2k`. -/
public lemma integral_phase_gaussian_pi_mul_I_mul_even (k : ℕ)
    (w : EuclideanSpace ℝ (Fin (2 * k))) (z : ℂ) (hz : 0 < z.im) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)),
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
          cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z)) =
      (((I : ℂ) / z) ^ k) * cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z)) := by
  simpa [fourier_eq', smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    (fourier_gaussian_pi_mul_I_mul_even (k := k) (z := z) hz (w := w))

/-- Evaluate a Fourier-type Gaussian integral in even real dimension, pulling out a constant `c`. -/
public lemma integral_const_mul_phase_gaussian_pi_mul_I_mul_even (k : ℕ)
    (w : EuclideanSpace ℝ (Fin (2 * k))) (z : ℂ) (hz : 0 < z.im) (c : ℂ) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)), c *
        (Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z))) =
      c * ((((Complex.I : ℂ) / z) ^ k) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * (‖w‖ ^ 2 : ℝ) * (-1 / z))) := by
  trans (c * ∫ x : EuclideanSpace ℝ (Fin (2 * k)),
      Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z))
  · exact MeasureTheory.integral_const_mul c _
  · rw [integral_phase_gaussian_pi_mul_I_mul_even (k := k) (w := w) (z := z) hz]

/-- Fourier transform of the real Gaussian `x ↦ exp (-π * ‖x‖^2 / s)` in even dimension `2k`. -/
public lemma fourier_gaussian_norm_sq_div_even (k : ℕ) (s : ℝ) (hs : 0 < s)
    (w : EuclideanSpace ℝ (Fin (2 * k))) :
    𝓕 (fun v : EuclideanSpace ℝ (Fin (2 * k)) ↦ cexp (-π * (‖v‖ ^ 2) / s)) w =
      (s ^ k : ℂ) * cexp (-π * (‖w‖ ^ 2) * s) := by
  have hbase : (π : ℂ) / (π / s : ℂ) = (s : ℂ) := by
    field_simp [(by exact_mod_cast (ne_of_gt hs) : (s : ℂ) ≠ 0),
      (by exact_mod_cast Real.pi_ne_zero : (π : ℂ) ≠ 0)]
  have hfinrank : ((Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * k))) : ℂ) / 2) = (k : ℂ) := by
    simp [Nat.cast_mul]
  simpa [div_eq_mul_inv, hbase, hfinrank, pow_two, mul_assoc,
    mul_left_comm, mul_comm] using
    (fourier_gaussian_innerProductSpace
      (V := EuclideanSpace ℝ (Fin (2 * k))) (b := (π / s : ℂ))
      (by simpa using (div_pos Real.pi_pos hs)) w)

/-- Integral of the phase factor times the real Gaussian in even dimension `2k`. -/
public lemma integral_phase_gaussian_even (k : ℕ) (w : EuclideanSpace ℝ (Fin (2 * k)))
    (s : ℝ) (hs : 0 < s) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)),
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) =
      (s ^ k : ℂ) * cexp (-π * (‖w‖ ^ 2) * s) := by
  simpa [fourier_eq', smul_eq_mul, mul_assoc] using
    (fourier_gaussian_norm_sq_div_even (k := k) (s := s) hs (w := w))

/-! ### `rexp` Gaussian integrals on `ℝ⁸` -/

/-- For `s > 0`, `∫ exp (-π ‖x‖² / s)` over `ℝ^(2k)` equals `s ^ k`. -/
public lemma integral_gaussian_rexp_even (k : ℕ) (s : ℝ) (hs : 0 < s) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)), rexp (-π * (‖x‖ ^ 2) / s)) = s ^ k := by
  rw [integral_congr_ae (ae_of_all _ fun x => show rexp (-π * (‖x‖ ^ 2) / s) =
        rexp (-(π / s) * ‖x‖ ^ 2) by ring_nf),
    GaussianFourier.integral_rexp_neg_mul_sq_norm (div_pos Real.pi_pos hs)]
  simp [show (π / (π / s)) = s from by field_simp]

/-- Gaussian `rexp` integral over `ℝ⁸` with a scale parameter. -/
public lemma integral_gaussian_rexp (s : ℝ) (hs : 0 < s) :
    (∫ x : EuclideanSpace ℝ (Fin 8), rexp (-π * (‖x‖ ^ 2) / s)) = s ^ 4 := by
  simpa using integral_gaussian_rexp_even (k := 4) s hs

/-- The real Gaussian `x ↦ exp (-π * ‖x‖^2 / s)` is integrable on `ℝ⁸` for `s > 0`. -/
public lemma integrable_gaussian_rexp (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 8) ↦ rexp (-π * (‖x‖ ^ 2) / s))
      (volume : Measure (EuclideanSpace ℝ (Fin 8))) := by
  simpa using
    (MeasureTheory.Integrable.of_integral_ne_zero (μ := volume) <| by
      rw [integral_gaussian_rexp_even (k := 4) (s := s) hs]; exact pow_ne_zero 4 hs.ne' :
      Integrable (fun x : EuclideanSpace ℝ (Fin (2 * 4)) ↦ rexp (-π * (‖x‖ ^ 2) / s))
        (volume : Measure (EuclideanSpace ℝ (Fin (2 * 4)))))

end

end SpherePacking.ForMathlib
