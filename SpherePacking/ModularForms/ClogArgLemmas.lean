module
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Log and argument lemmas

This file contains lemmas relating `Complex.arg` and `Complex.log` to powers of a complex number,
specialized to expressions of the form `1 + f x` with `f x → 0`.
-/

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open UpperHalfPlane TopologicalSpace Set Metric Filter Function Complex

lemma arg_pow_aux (n : ℕ) (x : ℂ) (hna : |arg x| < π / n) :
    Complex.arg (x ^ n) = n * Complex.arg x := by
  cases n with
  | zero => simp
  | succ n =>
    have hmem : Complex.arg x ∈ Set.Ioc (-π / Nat.succ n) (π / Nat.succ n) := by
      have h := (abs_lt.1 hna)
      exact ⟨by simpa [neg_div] using h.1, le_of_lt h.2⟩
    have hmem' :
        ((Complex.arg x : Real.Angle).toReal) ∈ Set.Ioc (-π / Nat.succ n) (π / Nat.succ n) := by
      simpa [Complex.arg_coe_angle_toReal_eq_arg] using hmem
    have htoreal :
        ((Nat.succ n : ℕ) • (Complex.arg x : Real.Angle)).toReal =
          (Nat.succ n : ℝ) * (Complex.arg x : Real.Angle).toReal :=
      (Real.Angle.nsmul_toReal_eq_mul (n := Nat.succ n) (h := Nat.succ_ne_zero n)).2 hmem'
    calc
      Complex.arg (x ^ Nat.succ n) = (Complex.arg (x ^ Nat.succ n) : Real.Angle).toReal := by
        symm
        simp
      _ = ((Nat.succ n : ℕ) • (Complex.arg x : Real.Angle)).toReal := by
        simpa using congrArg Real.Angle.toReal (Complex.arg_pow_coe_angle x (Nat.succ n))
      _ = (Nat.succ n : ℝ) * Complex.arg x := by
        simpa [Complex.arg_coe_angle_toReal_eq_arg] using htoreal

lemma arg_pow_filter {α : Type*} (l : Filter α) (n : ℕ) (f : α → ℂ) (hf : Tendsto f l (𝓝 0)) :
    ∀ᶠ m : α in l, Complex.arg ((1 + f m) ^ n) = n * Complex.arg (1 + f m) := by
  by_cases hn0 : n = 0
  · subst hn0; simp
  have hf1 : Tendsto (fun m : α ↦ 1 + f m) l (𝓝 (1 : ℂ)) := by
    simpa using hf.const_add 1
  have harg : Tendsto (fun m : α ↦ Complex.arg (1 + f m)) l (𝓝 0) := by
    have hcont : ContinuousAt Complex.arg (1 : ℂ) :=
      Complex.continuousAt_arg (x := 1) (by simp)
    simpa [arg_one] using hcont.tendsto.comp hf1
  have hpi : 0 < π / n := by
    have : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    exact div_pos Real.pi_pos this
  filter_upwards [(Metric.tendsto_nhds.1 harg) (π / n) hpi] with m hmarg
  have hmarg' : |Complex.arg (1 + f m)| < π / n := by simpa [Real.dist_eq] using hmarg
  simpa using arg_pow_aux n (1 + f m) hmarg'

lemma clog_pow_filter {α : Type*} (l : Filter α) (n : ℕ) (f : α → ℂ) (hf : Tendsto f l (𝓝 0)) :
    ∀ᶠ m : α in l, Complex.log ((1 + f m) ^ n) = n * Complex.log (1 + f m) := by
  filter_upwards [arg_pow_filter (l := l) n f hf] with m hm
  simp [Complex.log, hm, norm_pow, Real.log_pow, ofReal_mul, ofReal_natCast]
  ring

lemma clog_pow (n : ℕ) (f : ℕ → ℂ) (hf : Tendsto f atTop (𝓝 0)) : ∀ᶠ m : ℕ in atTop,
    Complex.log ((1 + f m) ^ n) = n * Complex.log (1 + f m) := by
  simpa using clog_pow_filter (l := atTop) n f hf

/-- A `Complex.log` power rule along `atImInfty`, assuming `f z → 0`. -/
public lemma clog_pow2 (n : ℕ) (f : ℍ → ℂ) (hf : Tendsto f atImInfty (𝓝 0)) :
    ∀ᶠ m : ℍ in atImInfty, Complex.log ((1 + f m) ^ n) = n * Complex.log (1 + f m) := by
  simpa using clog_pow_filter (l := atImInfty) n f hf

/-- Summability of `n ↦ log ((1 + f n)^m)` assuming `f` is summable. -/
public lemma log_summable_pow (f : ℕ → ℂ) (hf : Summable f) (m : ℕ) :
    Summable (fun n => Complex.log ((1 + f n)^m)) := by
  have hfl := Complex.summable_log_one_add_of_summable hf
  refine Summable.congr_atTop (Summable.mul_left m (f := fun n => Complex.log (1 + f n)) hfl) ?_
  exact (clog_pow m f hf.tendsto_atTop_zero).mono fun _ hn => hn.symm
