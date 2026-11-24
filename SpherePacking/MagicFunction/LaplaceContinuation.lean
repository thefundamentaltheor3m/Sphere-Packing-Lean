/-
Copyright (c) 2026 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import SpherePacking.ForMathlib.LaplaceTransform

/-!
# Analytic continuation of Laplace transforms with exponential-polynomial growth

This file formalises Proposition 2.1 of [FGH], in the real parametrisation `z = i t` of the
positive imaginary axis, in terms of the Laplace transform `laplace`. Let `g : ℝ → E` satisfy, for
`t > 0`,

`g t = ∑ k ∈ range (n + 1), cexp (2 * π * k * t) • (a k + t • b k) + h t`,

where the remainder `h` is locally integrable on `[0, ∞)` and `O(exp (-C * t))` at infinity. Then
for `2 * n < re s`

`laplace g (π * s) =
  ∑ k ∈ range (n + 1), ((π * (s - 2 * k))⁻¹ • a k + ((π * (s - 2 * k)) ^ 2)⁻¹ • b k)
    + laplace h (π * s)`,

and `s ↦ laplace h (π * s)` is holomorphic on the half-plane `-C / π < re s`. So the right-hand
side continues `s ↦ laplace g (π * s)` meromorphically to that half-plane, with at most double poles
at `s = 2 * k`, `k ≤ n`.

Since `sin (π * s / 2) ^ 2` has double zeros at the even integers, the product of
`sin (π * s / 2) ^ 2` with the continuation is holomorphic on the whole half-plane. This product,
with its removable singularities filled in, is `sinSqLaplace`; it is the form in which the
continuation is applied in the blueprint (Propositions `prop:a-double-zeros`,
`prop:a-another-integral`, `prop:b-double-zeros`, `prop:b-another-integral`, and the special values
`prop:a0`, `prop:b0`).

The blueprint writes these Laplace transforms as integrals `∫ t in Ioi 0, cexp (-π * s * t) • g t`;
`laplace_pi_mul_eq_integral` converts between the two forms.

## Main statements

* `laplaceConvergent_pi_mul`: the Laplace integral of `g` converges absolutely at `π * s` for
  `2 * n < re s`.
* `laplace_pi_mul_eq_sum_add`: formula (2.3) of [FGH].
* `differentiableOn_laplace_pi_mul`: `s ↦ laplace h (π * s)` is holomorphic on `-C / π < re s`.
* `sinSqLaplace_eq_of_ne`, `sinSqLaplace_two_mul`, `sinSqLaplace_eq_sin_sq_smul_laplace`,
  `analyticOnNhd_sinSqLaplace`: the function `sinSqLaplace`, its values, and its analyticity.
* `eq_smul_sinSqLaplace_of_analyticOnNhd`: the identity-principle step, in the form used to prove
  `prop:a-another-integral` and `prop:b-another-integral` of the blueprint.

## References

* [FGH] A. S. Feigenbaum, P. J. Grabner, D. P. Hardin, *Eigenfunctions of the Fourier transform
  with specified zeros*, arXiv:1907.08558v3, Proposition 2.1 and Proposition 2.2.
-/

@[expose] public section

open MeasureTheory Set Filter Asymptotics Complex Real Finset

namespace MagicFunction.LaplaceContinuation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {g h : ℝ → E} {a b : ℕ → E} {n : ℕ} {C : ℝ} {s : ℂ}

/-- The Laplace transform at `π * s`, written as the integral which appears in the blueprint. -/
theorem laplace_pi_mul_eq_integral (g : ℝ → E) (s : ℂ) :
    laplace g (π * s) = ∫ t in Ioi (0 : ℝ), cexp (-π * s * t) • g t := by
  simp only [laplace, neg_mul]

section Remainder

/-- The Laplace integral of the remainder converges absolutely at `π * s` on the half-plane
`-C / π < re s`. -/
theorem laplaceConvergent_pi_mul_of_isBigO (hh : LocallyIntegrableOn h (Ici 0))
    (hO : h =O[atTop] fun t ↦ rexp (-C * t)) (hs : -C / π < s.re) :
    LaplaceConvergent h (π * s) :=
  laplaceConvergent_of_isBigO_exp hh hO <| by simpa [re_ofReal_mul] using (div_lt_iff₀' pi_pos).1 hs

/-- The function `s ↦ laplace h (π * s)` is holomorphic on the half-plane `-C / π < re s`. -/
theorem differentiableOn_laplace_pi_mul (hh : LocallyIntegrableOn h (Ici 0))
    (hO : h =O[atTop] fun t ↦ rexp (-C * t)) :
    DifferentiableOn ℂ (fun s : ℂ ↦ laplace h (π * s)) {s | -C / π < s.re} :=
  (laplace_differentiableOn_of_isBigO_exp hh hO).comp (differentiableOn_id.const_mul (π : ℂ))
    fun s hs ↦ by simpa [re_ofReal_mul] using (div_lt_iff₀' pi_pos).1 hs

end Remainder

section MainTerm

private
theorem sum_smul_eq_cexp_smul_sum (a b : ℕ → E) (n : ℕ) (s : ℂ) (t : ℝ) :
    ∑ k ∈ range (n + 1), (cexp (-(π * (s - 2 * k)) * t) • a k +
        (t * cexp (-(π * (s - 2 * k)) * t)) • b k) =
      cexp (-(π * s) * t) • ∑ k ∈ range (n + 1), cexp (2 * π * k * t) • (a k + (t : ℂ) • b k) := by
  rw [smul_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [smul_smul, ← Complex.exp_add, smul_add, smul_smul, mul_comm (cexp _) t]
  ring_nf

private
theorem re_pi_mul_sub_pos (hs : 2 * n < s.re) {k : ℕ} (hk : k ∈ range (n + 1)) :
    0 < ((π : ℂ) * (s - 2 * k)).re := by
  rw [re_ofReal_mul]
  exact mul_pos pi_pos (by simp; linarith [(Nat.cast_le (α := ℝ)).2 (mem_range_succ_iff.1 hk)])

/-- The Laplace integral of the exponential-polynomial main term converges absolutely at `π * s`
for `2 * n < re s`. -/
theorem laplaceConvergent_pi_mul_sum (hs : 2 * n < s.re) : LaplaceConvergent
    (fun t : ℝ ↦ ∑ k ∈ range (n + 1), cexp (2 * π * k * t) • (a k + (t : ℂ) • b k)) (π * s) :=
  IntegrableOn.congr_fun (integrable_finsetSum _ fun k hk ↦
    ((integrableOn_exp_mul_complex_Ioi (by simpa using re_pi_mul_sub_pos hs hk) 0).smul_const
    (a k)).add (Integrable.smul_const (by simpa using (integrableOn_pow_mul_cexp_neg_mul_Ioi 1
    (re_pi_mul_sub_pos hs hk) 0).integrable) (b k))) (fun t _ ↦ sum_smul_eq_cexp_smul_sum a b n s
    t) measurableSet_Ioi

/-- The Laplace transform at `π * s` of the exponential-polynomial main term is the principal part
`∑ k, ((π * (s - 2 * k))⁻¹ • a k + ((π * (s - 2 * k)) ^ 2)⁻¹ • b k)`. -/
theorem laplace_pi_mul_sum [CompleteSpace E] (hs : 2 * n < s.re) : laplace (fun t : ℝ ↦ ∑ k ∈
    range (n + 1), cexp (2 * π * k * t) • (a k + (t : ℂ) • b k)) (π * s) =
    ∑ k ∈ range (n + 1), ((π * (s - 2 * k))⁻¹ • a k + ((π * (s - 2 * k)) ^ 2)⁻¹ • b k) := by
  have h1 (k : ℕ) (hk : k ∈ range (n + 1)) :
      IntegrableOn (fun t : ℝ ↦ cexp (-(π * (s - 2 * k)) * t) • a k) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (by simpa using re_pi_mul_sub_pos hs hk) 0).smul_const _
  have h2 (k : ℕ) (hk : k ∈ range (n + 1)) :
      IntegrableOn (fun t : ℝ ↦ ((t : ℂ) * cexp (-(π * (s - 2 * k)) * t)) • b k) (Ioi 0) := by
    simpa only [pow_one, IntegrableOn] using
      (integrableOn_pow_mul_cexp_neg_mul_Ioi 1 (re_pi_mul_sub_pos hs hk) 0).smul_const _
  refine (setIntegral_congr_fun measurableSet_Ioi fun t _ ↦
    (sum_smul_eq_cexp_smul_sum a b n s t).symm).trans ?_
  rw [integral_finsetSum _ fun k hk ↦ ?_]
  · refine sum_congr rfl fun k hk ↦ ?_
    rw [integral_add (h1 k hk) (h2 k hk), integral_smul_const, integral_smul_const,
      integral_exp_mul_complex_Ioi (by simpa using re_pi_mul_sub_pos hs hk) 0]
    simpa using congr_arg (· • b k) (integral_pow_mul_cexp_neg_mul_Ioi 1 (re_pi_mul_sub_pos hs hk))
  · exact (h1 k hk).add (h2 k hk)

end MainTerm

section Continuation

/-- The Laplace integral of `g` converges absolutely at `π * s` for `2 * n < re s`. -/
theorem laplaceConvergent_pi_mul (hh : LocallyIntegrableOn h (Ici 0))
    (hO : h =O[atTop] fun t ↦ rexp (-C * t)) (hC : 0 ≤ C) (hgh : ∀ t : ℝ, 0 < t → g t =
    ∑ k ∈ range (n + 1), cexp (2 * π * k * t) • (a k + (t : ℂ) • b k) + h t) (hs : 2 * n < s.re) :
    LaplaceConvergent g (π * s) :=
  IntegrableOn.congr_fun ((laplaceConvergent_pi_mul_sum (a := a) (b := b) hs).add
    (laplaceConvergent_pi_mul_of_isBigO hh hO ((div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hC)
    pi_pos.le).trans_lt ((by positivity : (0 : ℝ) ≤ 2 * n).trans_lt hs))))
    (fun t ht ↦ by simp only [hgh t ht]) measurableSet_Ioi


/-- **Proposition 2.1 of [FGH]**: for `2 * n < re s` the Laplace transform of `g`
at `π * s` is the sum of the principal part and the Laplace transform of the remainder. -/
theorem laplace_pi_mul_eq_sum_add [CompleteSpace E] (hh : LocallyIntegrableOn h (Ici 0))
    (hO : h =O[atTop] fun t ↦ rexp (-C * t)) (hC : 0 ≤ C) (hgh : ∀ t : ℝ, 0 < t → g t =
    ∑ k ∈ range (n + 1), cexp (2 * π * k * t) • (a k + (t : ℂ) • b k) + h t) (hs : 2 * n < s.re) :
    laplace g (π * s) = ∑ k ∈ range (n + 1), ((π * (s - 2 * k))⁻¹ • a k +
    ((π * (s - 2 * k)) ^ 2)⁻¹ • b k) + laplace h (π * s) := by
  rw [← laplace_pi_mul_sum hs, ← laplace_add (laplaceConvergent_pi_mul_sum hs)
    (laplaceConvergent_pi_mul_of_isBigO hh hO ((div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hC)
    pi_pos.le).trans_lt ((by positivity : (0 : ℝ) ≤ 2 * n).trans_lt hs)))]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ by simp only [hgh t ht]

end Continuation

section SinSq

/-- The product of `sin (π * s / 2) ^ 2` with the meromorphic continuation
`∑ k, ((π * (s - 2 * k))⁻¹ • a k + ((π * (s - 2 * k)) ^ 2)⁻¹ • b k) + laplace h (π * s)`
of Proposition 2.1 of [FGH], with the removable singularities at `s = 2 * k` filled in.
Up to the factor `-4` this is the function `U` of [FGH], Proposition 2.2, equation (2.4). -/
noncomputable
def sinSqLaplace (a b : ℕ → E) (n : ℕ) (h : ℝ → E) (s : ℂ) : E :=
  ∑ k ∈ range (n + 1), ((Complex.sin (π * (s - 2 * k) / 2) * dslope Complex.sin 0
    (π * (s - 2 * k) / 2) / 2) • a k + (dslope Complex.sin 0 (π * (s - 2 * k) / 2) ^ 2 / 4) • b k) +
    Complex.sin (π * s / 2) ^ 2 • laplace h (π * s)

theorem sinSqLaplace_def : sinSqLaplace a b n h = fun s : ℂ ↦
    ∑ k ∈ range (n + 1), ((Complex.sin (π * (s - 2 * k) / 2) * dslope Complex.sin 0
    (π * (s - 2 * k) / 2) / 2) • a k + (dslope Complex.sin 0 (π * (s - 2 * k) / 2) ^ 2 / 4) • b k) +
    Complex.sin (π * s / 2) ^ 2 • laplace h (π * s) :=
  rfl

/-- Away from the poles `s = 2 * k`, `k ≤ n`, the function `sinSqLaplace` is the product of
`sin (π * s / 2) ^ 2` with the continuation of Proposition 2.1 of [FGH]. -/
theorem sinSqLaplace_eq_of_ne (hs : ∀ k ≤ n, s ≠ 2 * k) : sinSqLaplace a b n h s =
    Complex.sin (π * s / 2) ^ 2 • (∑ k ∈ range (n + 1), ((π * (s - 2 * k))⁻¹ • a k +
    ((π * (s - 2 * k)) ^ 2)⁻¹ • b k) + laplace h (π * s)) := by
  simp only [sinSqLaplace, smul_add, smul_sum, smul_smul]
  refine congrArg₂ (· + ·) (sum_congr rfl fun k hk ↦ ?_) rfl
  have := sub_ne_zero.2 (hs k (mem_range_succ_iff.1 hk))
  rw [dslope_of_ne _ (by simpa [pi_ne_zero]), slope_def_field, Complex.sin_zero, sub_zero,
    sub_zero, show (π : ℂ) * s / 2 = π * (s - 2 * k) / 2 + k * π by ring,
    Complex.sin_antiperiodic.add_nat_mul_eq, mul_pow, ← pow_mul,
    (even_two.mul_left k).neg_one_pow]
  match_scalars <;> field_simp
  ring

/-- The value of `sinSqLaplace` at the pole `s = 2 * k`, `k ≤ n`, is a quarter of the coefficient
of the double pole. -/
theorem sinSqLaplace_two_mul {k : ℕ} (hk : k ≤ n) :
    sinSqLaplace a b n h (2 * k) = (1 / 4 : ℂ) • b k := by
  rw [sinSqLaplace, show (π : ℂ) * (2 * k) / 2 = k * π by ring, Complex.sin_nat_mul_pi,zero_pow
    two_ne_zero, zero_smul, add_zero, sum_eq_single_of_mem k (mem_range.2 (Nat.lt_succ_of_le hk))]
  · simp [dslope_same, Complex.deriv_sin]
  · intro j _ hjk
    rw [show (π : ℂ) * (2 * k - 2 * j) / 2 = (((k : ℤ) - j : ℤ) : ℂ) * π by push_cast; ring,
      dslope_of_ne _ (mul_ne_zero (Int.cast_ne_zero.2 (sub_ne_zero.2 (by exact_mod_cast hjk.symm)))
      (ofReal_ne_zero.2 pi_ne_zero)), slope_def_field, Complex.sin_int_mul_pi]
    simp

/-- For `2 * n < re s`, the function `sinSqLaplace` is `sin (π * s / 2) ^ 2` times the Laplace
transform of `g` at `π * s`. -/
theorem sinSqLaplace_eq_sin_sq_smul_laplace [CompleteSpace E] (hh : LocallyIntegrableOn h (Ici 0))
    (hO : h =O[atTop] fun t ↦ rexp (-C * t)) (hC : 0 ≤ C) (hgh : ∀ t : ℝ, 0 < t → g t =
    ∑ k ∈ range (n + 1), cexp (2 * π * k * t) • (a k + (t : ℂ) • b k) + h t) (hs : 2 * n < s.re) :
    sinSqLaplace a b n h s = Complex.sin (π * s / 2) ^ 2 • laplace g (π * s) := by
  rw [sinSqLaplace_eq_of_ne, laplace_pi_mul_eq_sum_add hh hO hC hgh hs]
  rintro k hk rfl
  simp only [mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero, sub_zero, Nat.ofNat_pos,
    mul_lt_mul_iff_right₀, Nat.cast_lt] at hs
  linarith [(Nat.cast_le (α := ℝ)).2 hk]

/-- The function `sinSqLaplace` is holomorphic on the half-plane `-C / π < re s`. -/
theorem differentiableOn_sinSqLaplace (hh : LocallyIntegrableOn h (Ici 0))
    (hO : h =O[atTop] fun t ↦ rexp (-C * t)) :
    DifferentiableOn ℂ (sinSqLaplace a b n h) {s | -C / π < s.re} :=
  .add (.fun_sum fun k _ ↦ AnalyticOnNhd.differentiableOn fun z _ ↦ by fun_prop)
    (.smul (Differentiable.differentiableOn (by fun_prop)) (differentiableOn_laplace_pi_mul hh hO))

/-- The function `sinSqLaplace` is analytic on the half-plane `-C / π < re s`. -/
theorem analyticOnNhd_sinSqLaplace [CompleteSpace E] (hh : LocallyIntegrableOn h (Ici 0))
    (hO : h =O[atTop] fun t ↦ rexp (-C * t)) :
    AnalyticOnNhd ℂ (sinSqLaplace a b n h) {s | -C / π < s.re} :=
  (differentiableOn_sinSqLaplace hh hO).analyticOnNhd (isOpen_lt continuous_const continuous_re)

/-- The restriction of `sinSqLaplace` to the real axis is real-analytic on `(-C / π, ∞)`. -/
theorem analyticOnNhd_sinSqLaplace_ofReal [CompleteSpace E] (hh : LocallyIntegrableOn h (Ici 0))
    (hO : h =O[atTop] fun t ↦ rexp (-C * t)) :
    AnalyticOnNhd ℝ (fun x : ℝ ↦ sinSqLaplace a b n h x) (Ioi (-C / π)) :=
  ((analyticOnNhd_sinSqLaplace hh hO).restrictScalars (𝕜 := ℝ)).comp
    (ofRealCLM.analyticOnNhd _) fun x hx ↦ by simpa using hx

/-- Identity principle: a real-analytic function which agrees with `c • sin (π * x / 2) ^ 2` times
the Laplace transform of `g` at `π * x` for `x > 2 * n` is equal to `c • sinSqLaplace a b n h`
wherever it is analytic. -/
theorem eq_smul_sinSqLaplace_of_analyticOnNhd [CompleteSpace E] {A : ℝ → E} {c : ℂ} {x₀ x : ℝ}
    (hh : LocallyIntegrableOn h (Ici 0)) (hO : h =O[atTop] fun t ↦ rexp (-C * t)) (hC : 0 ≤ C)
    (hgh : ∀ t : ℝ, 0 < t →
      g t = ∑ k ∈ range (n + 1), cexp (2 * π * k * t) • (a k + (t : ℂ) • b k) + h t)
    (hx₀ : -C / π ≤ x₀) (hA : AnalyticOnNhd ℝ A (Ioi x₀))
    (hAg : ∀ y : ℝ, 2 * n < y → A y = c • Complex.sin (π * y / 2) ^ 2 • laplace g (π * y))
    (hx : x₀ < x) : A x = c • sinSqLaplace a b n h x := by
  refine hA.eqOn_of_preconnected_of_eventuallyEq
    ((analyticOnNhd_sinSqLaplace_ofReal hh hO).mono (Ioi_subset_Ioi hx₀)).const_smul
    isPreconnected_Ioi ((le_max_right (2 * (n : ℝ)) x₀).trans_lt (lt_add_one _)) ?_ hx
  filter_upwards [Ioi_mem_nhds (lt_add_one (max (2 * (n : ℝ)) x₀))] with y hy
  rw [hAg y (max_lt_iff.1 hy).1, Pi.smul_apply,
    sinSqLaplace_eq_sin_sq_smul_laplace hh hO hC hgh (by simpa using (max_lt_iff.1 hy).1)]

end SinSq

end MagicFunction.LaplaceContinuation
