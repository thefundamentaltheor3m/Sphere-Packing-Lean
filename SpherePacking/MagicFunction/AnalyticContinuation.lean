/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Analytic continuation of Laplace transforms

Let `t ↦ ψ(it)` be locally integrable on `[0, ∞)` with
`ψ(it) = ∑_{k=0}^n (a_k + t b_k) e^{2πkt} + O(e^{-Ct})` as `t → ∞`. Then for `Re s > 2n`,
`W(s) = ∫₀^∞ ψ(it) e^{-πst} dt` equals
`∑_{k=0}^n (a_k / (π(s - 2k)) + b_k / (π²(s - 2k)²)) + ∫₀^∞ (ψ(it) - P(t)) e^{-πst} dt`,
where `P = expPoly n a b`, and the last integral is holomorphic on `Re s > -C/π`.
This is used for the analytic continuation of `a` and `b`.

## References

* [A. S. Feigenbaum, P. J. Grabner and D. P. Hardin, *Eigenfunctions of the Fourier transform
  with specified zeros*][feigenbaumgrabnerhardin2021]
-/

@[expose] public section

open Set Filter MeasureTheory Asymptotics Real Complex Finset

namespace MagicFunction.DoubleZeroes

section ExpDecay

/-! ### Integrals `∫₀^∞ f(t) e^{-st} dt` of functions of exponential order -/

variable {f : ℝ → ℂ} {r : ℝ} {s w : ℂ}

/-- If `f = O(e^{rt})` and `r < r'`, then `t f(t) = O(e^{r't})`. -/
theorem ofReal_mul_isBigO_exp (hO : f =O[atTop] fun t ↦ rexp (r * t)) {r' : ℝ} (hr : r < r') :
    (fun t : ℝ ↦ t * f t) =O[atTop] fun t ↦ rexp (r' * t) := by
  simpa [← Real.exp_add, ← add_mul] using
    (isBigO_ofReal_left.2 (isLittleO_pow_exp_pos_mul_atTop 1 (sub_pos.2 hr)).isBigO).mul hO

/-- If `f` is locally integrable on `[0, ∞)` and `O(e^{rt})`, then `f(t) e^{-st}` is integrable
on `(0, ∞)` for `r < re s`. This is a complex-parameter version of
`integrableOn_exp_neg_smul_of_isBigO_exp`. -/
theorem integrableOn_mul_cexp_neg_mul (hf : LocallyIntegrableOn f (Ici 0))
    (hO : f =O[atTop] fun t ↦ rexp (r * t)) (hs : r < s.re) :
    IntegrableOn (fun t : ℝ ↦ f t * cexp (-s * t)) (Ioi 0) :=
  .mono_set ((integrableOn_exp_neg_smul_of_isBigO_exp hf hO hs).congr'
    (hf.aestronglyMeasurable.mul (by fun_prop))
    (.of_forall fun t ↦ by simp [Complex.norm_exp, mul_comm])) Set.Ioi_subset_Ici_self

/-- If `f` is locally integrable on `[0, ∞)` and `O(e^{rt})`, then `z ↦ ∫₀^∞ f(t) e^{-zt} dt`
may be differentiated under the integral sign at every `s` with `r < re s`. -/
theorem hasDerivAt_integral_mul_cexp_neg_mul (hf : LocallyIntegrableOn f (Ici 0))
    (hO : f =O[atTop] fun t ↦ rexp (r * t)) (hs : r < s.re) :
    HasDerivAt (fun z : ℂ ↦ ∫ t in Ioi 0, f t * cexp (-z * t))
      (∫ t in Ioi 0, -(t * f t * cexp (-s * t))) s := by
  obtain ⟨σ, hrσ, hσs⟩ := exists_between hs
  obtain ⟨r', hrr', hr'σ⟩ := exists_between hrσ
  have hfm := hf.aestronglyMeasurable.mono_set Set.Ioi_subset_Ici_self
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun z t ↦ f t * cexp (-z * t)) (F' := fun z t ↦ -(t * f t * cexp (-z * t)))
    (bound := fun t ↦ ‖t * f t * cexp (-σ * t)‖)
    ((isOpen_lt continuous_const continuous_re).mem_nhds hσs) (.of_forall fun z ↦ by fun_prop)
    (integrableOn_mul_cexp_neg_mul hf hO hs) (by fun_prop) ?_ ?_ ?_).2
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (.of_forall fun t (ht : 0 < t) z hz ↦ ?_)
    simp only [norm_neg, norm_mul, Complex.norm_exp, re_mul_ofReal, neg_re, ofReal_re]
    gcongr
    exact hz.le
  · exact (integrableOn_mul_cexp_neg_mul (hf.continuousOn_mul (by fun_prop)
      isClosed_Ici.isLocallyClosed) (ofReal_mul_isBigO_exp hO hrr') (by simpa using hr'σ)).norm
  · exact .of_forall fun t z _ ↦
      (((hasDerivAt_neg z).mul_const (t : ℂ)).cexp.const_mul (f t)).congr_deriv (by ring)

/-- If `f` is locally integrable on `[0, ∞)` and `O(e^{rt})`, then `z ↦ ∫₀^∞ f(t) e^{-zt} dt` is
analytic on the half-plane `r < re z`. -/
theorem analyticOnNhd_integral_mul_cexp_neg_mul (hf : LocallyIntegrableOn f (Ici 0))
    (hO : f =O[atTop] fun t ↦ rexp (r * t)) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∫ t in Ioi 0, f t * cexp (-z * t)) {z | r < z.re} :=
  DifferentiableOn.analyticOnNhd (fun _ hz ↦ (hasDerivAt_integral_mul_cexp_neg_mul hf hO hz)
    |>.differentiableAt.differentiableWithinAt) (isOpen_lt continuous_const continuous_re)

/-- `t e^{-wt}` is integrable on `(0, ∞)` for `0 < re w`. -/
theorem integrableOn_ofReal_mul_cexp_neg_mul (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) * cexp (-w * t)) (Ioi 0) := by
  refine integrableOn_mul_cexp_neg_mul (r := w.re / 2) ?_ ?_ (half_lt_self hw)
  · exact continuous_ofReal.locallyIntegrable.locallyIntegrableOn _
  · simpa using isBigO_ofReal_left.2 (isLittleO_pow_exp_pos_mul_atTop 1 (half_pos hw)).isBigO

/-- `∫₀^∞ t e^{-wt} dt = 1 / w²` for `0 < re w`. -/
theorem integral_ofReal_mul_cexp_neg_mul (hw : 0 < w.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) * cexp (-w * t) = 1 / w ^ 2 := by
  /- Both sides are minus the derivative at `w` of `z ↦ ∫₀^∞ e^{-zt} dt = 1 / z`. -/
  rw [← neg_inj, ← integral_neg, one_div]
  convert (hasDerivAt_integral_mul_cexp_neg_mul (f := fun _ ↦ 1) (r := 0) ?_ ?_ hw).unique
    ((hasDerivAt_inv (ne_zero_of_re_pos hw)).congr_of_eventuallyEq ?_)
  · rw [mul_one]
  · exact (locallyIntegrable_const 1).locallyIntegrableOn _
  · simp [isBoundedUnder_const]
  · filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hw] with z hz
    simpa using integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0

end ExpDecay

/-- The main term `P(t) = ∑_{k=0}^n (a_k + t b_k) e^{2πkt}` of `ψ(it)` as `t → ∞`. -/
noncomputable def expPoly (n : ℕ) (a b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (a k + t * b k) * cexp (2 * π * k * t)

@[simp] theorem expPoly_apply (n : ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    expPoly n a b t = ∑ k ∈ range (n + 1), (a k + t * b k) * cexp (2 * π * k * t) :=
  rfl

variable {ψ : ℂ → ℂ} {n : ℕ} {a b : ℕ → ℂ} {C : ℝ} {s : ℂ}

section ExpPoly

theorem continuous_expPoly : Continuous (expPoly n a b) := by
  fun_prop [expPoly]

private theorem expPoly_mul_cexp (t : ℝ) : expPoly n a b t * cexp (-π * s * t) =
    ∑ k ∈ range (n + 1), (a k * cexp (-(π * (s - 2 * k)) * t) +
      b k * (t * cexp (-(π * (s - 2 * k)) * t))) := by
  simpa [expPoly, sum_mul, mul_assoc, ← Complex.exp_add] using sum_congr rfl fun k _ ↦ by ring_nf

private theorem re_pi_mul_sub_pos (hs : 2 * n < s.re) {k : ℕ} (hk : k ∈ range (n + 1)) :
    0 < (π * (s - 2 * k)).re := by
  rw [re_ofReal_mul]
  exact mul_pos pi_pos (by simp; linarith [(Nat.cast_le (α := ℝ)).2 (mem_range_succ_iff.1 hk)])

private theorem integrableOn_expPoly_term (hs : 2 * n < s.re) {k : ℕ} (hk : k ∈ range (n + 1)) :
    IntegrableOn (fun t : ℝ ↦ a k * cexp (-(π * (s - 2 * k)) * t) +
      b k * (t * cexp (-(π * (s - 2 * k)) * t))) (Ioi 0) :=
  ((integrableOn_exp_mul_complex_Ioi (by simpa using re_pi_mul_sub_pos hs hk) 0).const_mul _).add
    ((integrableOn_ofReal_mul_cexp_neg_mul (re_pi_mul_sub_pos hs hk)).const_mul _)

/-- `∫₀^∞ P(t) e^{-πst} dt` converges absolutely for `Re s > 2n`. -/
theorem integrableOn_expPoly_mul_cexp (hs : 2 * n < s.re) :
    IntegrableOn (fun t : ℝ ↦ expPoly n a b t * cexp (-π * s * t)) (Ioi 0) := by
  simp_rw [expPoly_mul_cexp]
  exact integrable_finsetSum _ fun k hk ↦ integrableOn_expPoly_term hs hk

/-- `∫₀^∞ P(t) e^{-πst} dt` is the sum of the principal parts at `s = 2k` for `Re s > 2n`. -/
theorem integral_expPoly_mul_cexp (hs : 2 * n < s.re) :
    ∫ t in Ioi (0 : ℝ), expPoly n a b t * cexp (-π * s * t) =
      ∑ k ∈ range (n + 1), (a k / (π * (s - 2 * k)) + b k / (π ^ 2 * (s - 2 * k) ^ 2)) := by
  simp_rw [expPoly_mul_cexp]
  rw [integral_finsetSum _ fun k hk ↦ integrableOn_expPoly_term hs hk]
  refine sum_congr rfl fun k hk ↦ ?_
  have hw := re_pi_mul_sub_pos hs hk
  rw [integral_add ((integrableOn_exp_mul_complex_Ioi (by simpa using hw) 0).const_mul _)
    ((integrableOn_ofReal_mul_cexp_neg_mul hw).const_mul _), integral_const_mul,
    integral_const_mul, integral_exp_mul_complex_Ioi (by simpa using hw),
    integral_ofReal_mul_cexp_neg_mul hw]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq]
  ring

end ExpPoly

/-- `∫₀^∞ (ψ(it) - P(t)) e^{-πst} dt` converges absolutely for `Re s > -C/π`. -/
theorem integrableOn_sub_expPoly_mul_cexp (hs : -C / π < s.re)
    (hloc : LocallyIntegrableOn (fun t : ℝ ↦ ψ (I * t)) (Ici 0))
    (hexp : (fun t : ℝ ↦ ψ (I * t) - expPoly n a b t) =O[atTop] fun t ↦ rexp (-C * t)) :
    IntegrableOn (fun t : ℝ ↦ (ψ (I * t) - expPoly n a b t) * cexp (-π * s * t)) (Ioi 0) := by
  simpa only [Pi.sub_apply, neg_mul] using integrableOn_mul_cexp_neg_mul
    (hloc.sub (continuous_expPoly.locallyIntegrable.locallyIntegrableOn _)) hexp
    (by simpa [re_ofReal_mul] using (div_lt_iff₀' pi_pos).1 hs)

/-- `W(s) = ∫₀^∞ ψ(it) e^{-πst} dt` converges absolutely for `Re s > 2n`. -/
theorem integrableOn_mul_cexp (hC : 0 < C) (hs : 2 * n < s.re)
    (hloc : LocallyIntegrableOn (fun t : ℝ ↦ ψ (I * t)) (Ici 0))
    (hexp : (fun t : ℝ ↦ ψ (I * t) - expPoly n a b t) =O[atTop] fun t ↦ rexp (-C * t)) :
    IntegrableOn (fun t : ℝ ↦ ψ (I * t) * cexp (-π * s * t)) (Ioi 0) :=
  ((integrableOn_expPoly_mul_cexp hs).add (integrableOn_sub_expPoly_mul_cexp
    ((div_neg_of_neg_of_pos (neg_lt_zero.2 hC) pi_pos).trans
      ((by positivity : (0 : ℝ) ≤ 2 * n).trans_lt hs)) hloc hexp)).congr_fun
    (fun t _ ↦ by simp only [Pi.add_apply]; ring) measurableSet_Ioi

/-- FGH Proposition 2.1: for `Re s > 2n`, `W(s)` is the sum of its principal parts at `s = 2k`
and `∫₀^∞ (ψ(it) - P(t)) e^{-πst} dt`. -/
theorem integral_eq_sum_add_integral_sub (hC : 0 < C) (hs : 2 * n < s.re)
    (hloc : LocallyIntegrableOn (fun t : ℝ ↦ ψ (I * t)) (Ici 0))
    (hexp : (fun t : ℝ ↦ ψ (I * t) - expPoly n a b t) =O[atTop] fun t ↦ rexp (-C * t)) :
    ∫ t in Ioi (0 : ℝ), ψ (I * t) * cexp (-π * s * t) =
      ∑ k ∈ range (n + 1), (a k / (π * (s - 2 * k)) + b k / (π ^ 2 * (s - 2 * k) ^ 2)) +
        ∫ t in Ioi (0 : ℝ), (ψ (I * t) - expPoly n a b t) * cexp (-π * s * t) := by
  rw [← integral_expPoly_mul_cexp hs, ← integral_add (integrableOn_expPoly_mul_cexp hs)
    (integrableOn_sub_expPoly_mul_cexp ((div_neg_of_neg_of_pos (neg_lt_zero.2 hC) pi_pos).trans
      ((by positivity : (0 : ℝ) ≤ 2 * n).trans_lt hs)) hloc hexp)]
  grind

/-- `∫₀^∞ (ψ(it) - P(t)) e^{-πst} dt` is holomorphic on `Re s > -C/π`, so the right hand side of
`integral_eq_sum_add_integral_sub` is a meromorphic continuation of `W` to this half-plane, with at
most double poles at `s = 2k`. -/
theorem analyticOnNhd_integral_sub_expPoly
    (hloc : LocallyIntegrableOn (fun t : ℝ ↦ ψ (I * t)) (Ici 0))
    (hexp : (fun t : ℝ ↦ ψ (I * t) - expPoly n a b t) =O[atTop] fun t ↦ rexp (-C * t)) :
    AnalyticOnNhd ℂ (fun s : ℂ ↦ ∫ t in Ioi (0 : ℝ),
      (ψ (I * t) - expPoly n a b t) * cexp (-π * s * t)) {s | -C / π < s.re} := by
  simpa only [Function.comp_def, Pi.sub_apply, neg_mul] using
    (analyticOnNhd_integral_mul_cexp_neg_mul
      (hloc.sub (continuous_expPoly.locallyIntegrable.locallyIntegrableOn _)) hexp).comp
      (fun _ _ ↦ by fun_prop : AnalyticOnNhd ℂ (fun s : ℂ ↦ π * s) _)
      fun s hs ↦ by simpa [re_ofReal_mul] using (div_lt_iff₀' pi_pos).1 hs

/-- FGH (2.4) without the factor `-4`: the holomorphic continuation of `sin(πs/2)^2 W(s)` to
`Re s > -C/π`, where `W(s) = ∫₀^∞ ψ(it) e^{-πst} dt`. It is `sin(πs/2)^2` times the right hand side
of `integral_eq_sum_add_integral_sub`, with the removable singularities at `s = 2k` removed:
`dslope (fun s : ℂ ↦ sin (π * s / 2)) (2 * k) s` is `sin(πs/2) / (s - 2k)` for `s ≠ 2k`. -/
noncomputable def U (ψ : ℂ → ℂ) (n : ℕ) (a b : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ k ∈ range (n + 1),
      (a k / π * sin (π * s / 2) * dslope (fun s : ℂ ↦ sin (π * s / 2)) (2 * k) s +
        b k / π ^ 2 * dslope (fun s : ℂ ↦ sin (π * s / 2)) (2 * k) s ^ 2) +
    sin (π * s / 2) ^ 2 * ∫ t in Ioi (0 : ℝ), (ψ (I * t) - expPoly n a b t) * cexp (-π * s * t)

/-- FGH Proposition 2.2 (holomorphy): `U` is holomorphic on `Re s > -C/π`. -/
theorem analyticOnNhd_U (hloc : LocallyIntegrableOn (fun t : ℝ ↦ ψ (I * t)) (Ici 0))
    (hexp : (fun t : ℝ ↦ ψ (I * t) - expPoly n a b t) =O[atTop] fun t ↦ rexp (-C * t)) :
    AnalyticOnNhd ℂ (U ψ n a b) {s | -C / π < s.re} := by
  have h : Differentiable ℂ fun s : ℂ ↦ sin (π * s / 2) := by fun_prop
  have (k : ℕ) : Differentiable ℂ (dslope (fun s : ℂ ↦ sin (π * s / 2)) (2 * k)) :=
    differentiableOn_univ.mp <| (Complex.differentiableOn_dslope univ_mem).mpr <|
      h.differentiableOn
  refine DifferentiableOn.analyticOnNhd (.add (Differentiable.differentiableOn
    (Differentiable.fun_sum (by fun_prop))) ?_) (isOpen_lt continuous_const continuous_re)
  exact (h.pow 2).differentiableOn.mul
    (analyticOnNhd_integral_sub_expPoly hloc hexp).differentiableOn

/-- `U` is the continuation of `sin(πs/2)^2 W(s)`: they agree where the integral converges. -/
theorem U_eq_sin_sq_mul_integral (hC : 0 < C) (hs : 2 * n < s.re)
    (hloc : LocallyIntegrableOn (fun t : ℝ ↦ ψ (I * t)) (Ici 0))
    (hexp : (fun t : ℝ ↦ ψ (I * t) - expPoly n a b t) =O[atTop] fun t ↦ rexp (-C * t)) :
    U ψ n a b s = sin (π * s / 2) ^ 2 * ∫ t in Ioi (0 : ℝ), ψ (I * t) * cexp (-π * s * t) := by
  rw [U, integral_eq_sum_add_integral_sub hC hs hloc hexp, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [dslope_of_ne _ (by rintro rfl; simp at hs hk; omega), slope_def_field,
    show (π : ℂ) * (2 * k) / 2 = k * π by ring, Complex.sin_nat_mul_pi, sub_zero]
  field_simp

end MagicFunction.DoubleZeroes
