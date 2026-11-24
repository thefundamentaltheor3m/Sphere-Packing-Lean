/-
Copyright (c) 2026 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The Laplace transform

We define the Laplace transform `laplace f s = ∫ t in Ioi 0, cexp (-s * t) • f t` of a function
`f : ℝ → E` with values in a complex normed space. For `f` locally integrable on `[0, ∞)` and
`O(exp (a * t))` at infinity, we prove that it converges absolutely and is holomorphic on the
half-plane `a < re s`. We also compute the Laplace transform of `t ↦ t ^ n`.

The definition and its API follow `mellin` (`Mathlib.Analysis.MellinTransform`). The contents of
this file should eventually be moved to Mathlib.

## Main definitions

* `LaplaceConvergent f s`: the Laplace integral of `f` converges absolutely at `s`.
* `laplace f s`: the Laplace transform of `f` at `s`.

## Main results

* `isLittleO_rpow_smul_of_isBigO_exp`: multiplying a function of exponential order `a` by a power
  of `t` gives a function which is `o(exp (a' * t))` for every `a < a'`.
* `integrableOn_cexp_neg_mul_smul_of_isBigO_exp`, `laplaceConvergent_of_isBigO_exp`: absolute
  convergence on `a < re s`.
* `hasDerivAt_integral_cexp_neg_mul_smul_of_isBigO_exp`, `laplace_hasDerivAt_of_isBigO_exp`: the
  Laplace transform is complex differentiable at every `s` with `a < re s`, and its derivative is
  minus the Laplace transform of `t ↦ t • f t`.
* `laplace_differentiableOn_of_isBigO_exp`, `laplace_analyticOnNhd_of_isBigO_exp`: holomorphy on
  the half-plane.
* `integral_pow_mul_cexp_neg_mul_Ioi`, `laplace_pow`: the Laplace transform of `t ↦ t ^ n` is
  `n ! / s ^ (n + 1)` on `0 < re s`.

## Implementation notes

The integrability and differentiability results are first proved for integrals over `Ioi c` with
an arbitrary lower limit `c`, in the style of `Mathlib.MeasureTheory.Integral.ExpDecay`. The
statements about `laplace` are the case `c = 0`.

## References

* [FGH] A. S. Feigenbaum, P. J. Grabner, D. P. Hardin, *Eigenfunctions of the Fourier transform
  with specified zeros*, arXiv:1907.08558v3, proof of Proposition 2.1.
-/

@[expose] public section

open MeasureTheory Set Filter Asymptotics Complex Real Topology
open scoped Nat

section Asymptotics

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {a a' : ℝ} {f : ℝ → E}

/-- If `f = O(exp (a * t))` at infinity, then `t ^ r • f t = o(exp (a' * t))` for every real `r`
and every `a < a'`: multiplying by a power of `t` costs an arbitrarily small exponential rate. The
inequality must be strict (take `f = 1`, `r = 1` and `a = a' = 0`). -/
theorem isLittleO_rpow_smul_of_isBigO_exp (r : ℝ) (hO : f =O[atTop] fun t ↦ rexp (a * t))
    (ha : a < a') : (fun t : ℝ ↦ t ^ r • f t) =o[atTop] fun t ↦ rexp (a' * t) := by
  simpa [← Real.exp_add, ← add_mul] using
    (isLittleO_rpow_exp_pos_mul_atTop r (sub_pos.2 ha)).smul_isBigO hO

end Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {a c : ℝ} {f : ℝ → E} {s : ℂ}

section ExpDecay

/-- If `f` is locally integrable on `[c, ∞)` and `O(exp (a * t))` at infinity, then
`t ↦ cexp (-s * t) • f t` is integrable on `(c, ∞)` for every `s` with `a < re s`.
This is the complex-parameter version of `integrableOn_exp_neg_smul_of_isBigO_exp`. -/
theorem integrableOn_cexp_neg_mul_smul_of_isBigO_exp
    (hf : LocallyIntegrableOn f (Ici c)) (hO : f =O[atTop] fun t ↦ rexp (a * t)) (hs : a < s.re) :
    IntegrableOn (fun t : ℝ ↦ cexp (-s * t) • f t) (Ioi c) :=
  .mono_set ((integrableOn_exp_neg_smul_of_isBigO_exp hf hO hs).congr'
    (.smul (by fun_prop) hf.aestronglyMeasurable)
    (.of_forall (fun t ↦ by simp [norm_smul, Complex.norm_exp]))) Ioi_subset_Ici_self

/-- If `f` is locally integrable on `[c, ∞)` and `O(exp (a * t))` at infinity, then all moments
`t ↦ (t ^ n * cexp (-s * t)) • f t` are integrable on `(c, ∞)` for `a < re s`. The case `n = 1` is
the integrability of the derivative in `hasDerivAt_integral_cexp_neg_mul_smul_of_isBigO_exp`. -/
theorem integrableOn_pow_mul_cexp_neg_mul_smul_of_isBigO_exp (n : ℕ)
    (hf : LocallyIntegrableOn f (Ici c)) (hO : f =O[atTop] fun t ↦ rexp (a * t)) (hs : a < s.re) :
    IntegrableOn (fun t : ℝ ↦ ((t : ℂ) ^ n * cexp (-s * t)) • f t) (Ioi c) := by
  obtain ⟨a', haa', ha's⟩ := exists_between hs
  exact (integrableOn_cexp_neg_mul_smul_of_isBigO_exp (f := fun t ↦ t ^ n • f t)
    (hf.continuousOn_smul isClosed_Ici.isLocallyClosed (by fun_prop))
    (by simpa using (isLittleO_rpow_smul_of_isBigO_exp n hO haa').isBigO) ha's).congr_fun
    (fun t _ ↦ by simp only [← Complex.coe_smul, smul_smul, ofReal_pow, mul_comm]) measurableSet_Ioi

private theorem norm_neg_mul_cexp_neg_mul_smul_le {σ σ' t : ℝ} {z : ℂ} (x : E) (hσ : σ ≤ z.re)
    (hσ' : z.re ≤ σ') : ‖(-(t : ℂ) * cexp (-z * t)) • x‖ ≤
    ‖((t : ℂ) * cexp (-σ * t)) • x‖ + ‖((t : ℂ) * cexp (-σ' * t)) • x‖ := by
  simp only [norm_smul, norm_mul, norm_neg, norm_real, norm_exp, re_mul_ofReal, neg_re, ofReal_re,
    Real.norm_eq_abs]
  rcases le_total 0 t with ht | ht
  · exact le_add_of_le_of_nonneg (by gcongr) (by positivity)
  · exact le_add_of_nonneg_of_le (by positivity) (by gcongr ?_ * rexp ?_ * _; nlinarith)

/-- If `f` is locally integrable on `[c, ∞)` and `O(exp (a * t))` at infinity, then
`z ↦ ∫ t in Ioi c, cexp (-z * t) • f t` is complex differentiable at every `s` with `a < re s`, and
may be differentiated under the integral sign.
This is an analogue of `mellin_hasDerivAt_of_isBigO_rpow`. -/
theorem hasDerivAt_integral_cexp_neg_mul_smul_of_isBigO_exp
    (hf : LocallyIntegrableOn f (Ici c)) (hO : f =O[atTop] fun t ↦ rexp (a * t)) (hs : a < s.re) :
    HasDerivAt (fun z : ℂ ↦ ∫ t in Ioi c, cexp (-z * t) • f t)
      (∫ t in Ioi c, (-(t : ℂ) * cexp (-s * t)) • f t) s := by
  obtain ⟨σ, haσ, hσs⟩ := exists_between hs
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun (z : ℂ) (t : ℝ) ↦ (-(t : ℂ) * cexp (-z * t)) • f t)
    (((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)).mem_nhds ⟨hσs, lt_add_one s.re⟩) ?_ ?_ ?_
    (.of_forall fun t z hz ↦ norm_neg_mul_cexp_neg_mul_smul_le (f t) hz.1.le hz.2.le) ?_ ?_).2
  · exact .of_forall fun _ ↦
      .smul (by fun_prop) (hf.aestronglyMeasurable.mono_set Ioi_subset_Ici_self)
  · exact integrableOn_cexp_neg_mul_smul_of_isBigO_exp hf hO hs
  · exact .smul (by fun_prop) (hf.aestronglyMeasurable.mono_set Ioi_subset_Ici_self)
  · simpa [Pi.add_def] using (integrableOn_pow_mul_cexp_neg_mul_smul_of_isBigO_exp 1 hf hO
      haσ).norm.add (integrableOn_pow_mul_cexp_neg_mul_smul_of_isBigO_exp 1 hf hO
      (s := s.re + 1) (haσ.trans (hσs.trans (lt_add_one _)))).norm
  · exact .of_forall fun t z _ ↦ by
      simpa [mul_comm] using ((hasDerivAt_neg z).mul_const t).cexp.smul_const (f t)

/-- If `f` is locally integrable on `[c, ∞)` and `O(exp (a * t))` at infinity, then
`z ↦ ∫ t in Ioi c, cexp (-z * t) • f t` is complex differentiable on the open half-plane
`a < re z`. See `hasDerivAt_integral_cexp_neg_mul_smul_of_isBigO_exp` for the derivative. -/
theorem differentiableOn_integral_cexp_neg_mul_smul_of_isBigO_exp
    (hf : LocallyIntegrableOn f (Ici c)) (hO : f =O[atTop] fun t ↦ rexp (a * t)) :
    DifferentiableOn ℂ (fun z : ℂ ↦ ∫ t in Ioi c, cexp (-z * t) • f t) {z | a < z.re} :=
  fun _ hz ↦ hasDerivAt_integral_cexp_neg_mul_smul_of_isBigO_exp hf hO hz
    |>.differentiableAt.differentiableWithinAt

/-- If `E` is complete and `f` is locally integrable on `[c, ∞)` and `O(exp (a * t))` at infinity,
then `z ↦ ∫ t in Ioi c, cexp (-z * t) • f t` is analytic on the open half-plane `a < re z`. -/
theorem analyticOnNhd_integral_cexp_neg_mul_smul_of_isBigO_exp [CompleteSpace E]
    (hf : LocallyIntegrableOn f (Ici c)) (hO : f =O[atTop] fun t ↦ rexp (a * t)) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∫ t in Ioi c, cexp (-z * t) • f t) {z | a < z.re} :=
  (differentiableOn_integral_cexp_neg_mul_smul_of_isBigO_exp hf hO).analyticOnNhd
    (isOpen_lt continuous_const continuous_re)

end ExpDecay

section Monomial

private
theorem isBigO_ofReal_pow_exp (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (fun t : ℝ ↦ (t : ℂ) ^ n) =O[atTop] fun t ↦ rexp (ε * t) := by
  simpa using isBigO_ofReal_left.2 (isLittleO_pow_exp_pos_mul_atTop n hε).isBigO

/-- The function `t ↦ t ^ n * cexp (-w * t)` is integrable on `(c, ∞)` when `0 < re w`. The
hypothesis is sharp: for `re w ≤ 0` the integrand has norm at least `t ^ n` for `0 ≤ t`. Unlike
`Complex.integral_cpow_mul_exp_neg_mul_Ioi`, the rate `w` may be complex. See
`integrableOn_exp_mul_complex_Ioi` for the case `n = 0`, and `integral_pow_mul_cexp_neg_mul_Ioi`
for the value of the integral over `(0, ∞)`. -/
theorem integrableOn_pow_mul_cexp_neg_mul_Ioi (n : ℕ) {w : ℂ} (hw : 0 < w.re) (c : ℝ) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ n * cexp (-w * t)) (Ioi c) := by
  simpa [mul_comm] using integrableOn_cexp_neg_mul_smul_of_isBigO_exp (c := c)
    ((continuous_ofReal.pow n).locallyIntegrable.locallyIntegrableOn _)
    (isBigO_ofReal_pow_exp n (half_pos hw)) (half_lt_self hw)

/-- For `0 < re w`, `∫ t in Ioi 0, t ^ n * cexp (-w * t) = n ! / w ^ (n + 1)`. -/
theorem integral_pow_mul_cexp_neg_mul_Ioi (n : ℕ) {w : ℂ} (hw : 0 < w.re) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ n * cexp (-w * t) = n ! / w ^ (n + 1) := by
  induction n generalizing w with
  | zero => simpa using integral_exp_mul_complex_Ioi (a := -w) (by simpa using hw) 0
  | succ n ih =>
    convert congr_arg Neg.neg ((hasDerivAt_integral_cexp_neg_mul_smul_of_isBigO_exp (s := w)
      ((continuous_ofReal.pow n).locallyIntegrable.locallyIntegrableOn _)
      (isBigO_ofReal_pow_exp n (half_pos hw)) (half_lt_self hw)).unique
      ((((hasDerivAt_pow (n + 1) w).inv (pow_ne_zero _ (ne_zero_of_re_pos hw))).const_mul
      (n ! : ℂ)).congr_of_eventuallyEq (by
      filter_upwards [continuous_re.continuousAt.eventually (lt_mem_nhds hw)] with z hz
      simpa [mul_comm, div_eq_mul_inv] using ih hz))) using 1
    · simp [← integral_neg, pow_succ', mul_assoc, mul_comm (cexp _)]
    · push_cast [Nat.factorial_succ]
      field_simp [ne_zero_of_re_pos hw]
      ring

end Monomial

section Laplace

variable {g : ℝ → E}

/-- Predicate on `f` and `s` asserting that the Laplace integral of `f` converges absolutely at
`s`. -/
def LaplaceConvergent (f : ℝ → E) (s : ℂ) : Prop :=
  IntegrableOn (fun t : ℝ ↦ cexp (-s * t) • f t) (Ioi 0)

/-- The Laplace transform of a function `f : ℝ → E` (for a complex normed space `E`), defined as
the integral of `cexp (-s * t) • f t` over `Ioi 0`. It takes the junk value `0` where the integral
does not converge absolutely. -/
noncomputable
def laplace (f : ℝ → E) (s : ℂ) : E :=
  ∫ t : ℝ in Ioi 0, cexp (-s * t) • f t

theorem LaplaceConvergent.const_smul (hf : LaplaceConvergent f s) {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E] [SMulCommClass ℂ 𝕜 E] (r : 𝕜) :
    LaplaceConvergent (fun t ↦ r • f t) s := by
  simpa only [LaplaceConvergent, smul_comm] using! hf.smul r

theorem LaplaceConvergent.add (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    LaplaceConvergent (fun t ↦ f t + g t) s := by
  simpa only [LaplaceConvergent, smul_add] using! Integrable.add hf hg

theorem LaplaceConvergent.sub (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    LaplaceConvergent (fun t ↦ f t - g t) s := by
  simpa only [LaplaceConvergent, smul_sub] using! Integrable.sub hf hg

theorem laplace_const_smul (f : ℝ → E) (s : ℂ) {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℂ 𝕜 E] (r : 𝕜) : laplace (fun t ↦ r • f t) s = r • laplace f s := by
  simp only [laplace, smul_comm, integral_smul]

theorem laplace_add (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    laplace (fun t ↦ f t + g t) s = laplace f s + laplace g s := by
  simpa only [laplace, smul_add] using integral_add hf hg

theorem laplace_sub (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    laplace (fun t ↦ f t - g t) s = laplace f s - laplace g s := by
  simpa only [laplace, smul_sub] using integral_sub hf hg

/-- If `f` is locally integrable on `[0, ∞)` and `O(exp (a * t))` at infinity, then its Laplace
integral converges absolutely on the half-plane `a < re s`. -/
theorem laplaceConvergent_of_isBigO_exp (hf : LocallyIntegrableOn f (Ici 0))
    (hO : f =O[atTop] fun t ↦ rexp (a * t)) (hs : a < s.re) : LaplaceConvergent f s :=
  integrableOn_cexp_neg_mul_smul_of_isBigO_exp hf hO hs

/-- If `f` is locally integrable on `[0, ∞)` and `O(exp (a * t))` at infinity, then the Laplace
integral of `t ↦ t ^ n • f t` converges absolutely on the half-plane `a < re s`. -/
theorem laplaceConvergent_pow_smul_of_isBigO_exp (n : ℕ) (hf : LocallyIntegrableOn f (Ici 0))
    (hO : f =O[atTop] fun t ↦ rexp (a * t)) (hs : a < s.re) :
    LaplaceConvergent (fun t ↦ t ^ n • f t) s :=
  (integrableOn_pow_mul_cexp_neg_mul_smul_of_isBigO_exp n hf hO hs).congr_fun
    (fun t _ ↦ (by simp only [← Complex.coe_smul, smul_smul, ofReal_pow, mul_comm]))
    measurableSet_Ioi

/-- If `f` is locally integrable on `[0, ∞)` and `O(exp (a * t))` at infinity, then its Laplace
transform is complex differentiable at every `s` with `a < re s`, with derivative minus the
Laplace transform of `t ↦ t • f t`.
This is the analogue of `mellin_hasDerivAt_of_isBigO_rpow`. -/
theorem laplace_hasDerivAt_of_isBigO_exp (hf : LocallyIntegrableOn f (Ici 0))
    (hO : f =O[atTop] fun t ↦ rexp (a * t)) (hs : a < s.re) :
    HasDerivAt (laplace f) (-laplace (fun t ↦ t • f t) s) s := by
  refine (hasDerivAt_integral_cexp_neg_mul_smul_of_isBigO_exp hf hO hs).congr_deriv ?_
  simpa [laplace, ← integral_neg] using integral_congr_ae (.of_forall fun t ↦
    (by simp only [← Complex.coe_smul, smul_smul, mul_comm (t : ℂ)]))

/-- If `f` is locally integrable on `[0, ∞)` and `O(exp (a * t))` at infinity, then its Laplace
transform is complex differentiable on the open half-plane `a < re s`. -/
theorem laplace_differentiableOn_of_isBigO_exp (hf : LocallyIntegrableOn f (Ici 0))
    (hO : f =O[atTop] fun t ↦ rexp (a * t)) : DifferentiableOn ℂ (laplace f) {z | a < z.re} :=
  differentiableOn_integral_cexp_neg_mul_smul_of_isBigO_exp hf hO

/-- If `E` is complete and `f` is locally integrable on `[0, ∞)` and `O(exp (a * t))` at infinity,
then its Laplace transform is analytic on the open half-plane `a < re s`. -/
theorem laplace_analyticOnNhd_of_isBigO_exp [CompleteSpace E] (hf : LocallyIntegrableOn f (Ici 0))
    (hO : f =O[atTop] fun t ↦ rexp (a * t)) : AnalyticOnNhd ℂ (laplace f) {z | a < z.re} :=
  analyticOnNhd_integral_cexp_neg_mul_smul_of_isBigO_exp hf hO

/-- The Laplace integral of `t ↦ t ^ n` converges absolutely on the half-plane `0 < re s`. -/
theorem laplaceConvergent_pow (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    LaplaceConvergent (fun t : ℝ ↦ (t : ℂ) ^ n) s := by
  simpa [LaplaceConvergent, mul_comm] using integrableOn_pow_mul_cexp_neg_mul_Ioi n hs 0

/-- The Laplace transform of `t ↦ t ^ n` is `n ! / s ^ (n + 1)` on the half-plane `0 < re s`. -/
theorem laplace_pow (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    laplace (fun t : ℝ ↦ (t : ℂ) ^ n) s = n ! / s ^ (n + 1) := by
  simpa [laplace, mul_comm] using integral_pow_mul_cexp_neg_mul_Ioi n hs

end Laplace
