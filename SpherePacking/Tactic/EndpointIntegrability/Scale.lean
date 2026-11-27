/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# A scale of comparison functions for `endpoint_integrability`

The `endpoint_integrability` tactic proves that a function `f : ℝ → E` is integrable at an end
of an interval, along a filter `l`, by comparison: it proves `f =O[l] g` for a function `g` in a
fixed scale of comparison functions, proves that `g` is integrable at `l`, and concludes by
`Asymptotics.IsBigO.integrableAtFilter`. The ends of interest are `atTop` and `𝓝[>] 0`; both
satisfy `∀ᶠ t in l, 0 < t`, the hypothesis `hl` taken by the lemmas which need positivity, and
`Tendsto (fun t ↦ |log t|) l atTop`, the hypothesis `hlog` taken by the lemmas which need the
logarithm not to vanish eventually: the products and the dominance.

The comparison functions are `powExp a k u t = t ^ a * |log t| ^ k * exp (u t)`, for real powers
`a` and `k` and `u : ℝ → ℝ`, and the finite sums of them, written `fun t ↦ m₁ t + m₂ t`. The scale
is closed under products, which add the powers, inverses, which negate them, and real powers,
which multiply them. This file contains the lemmas applied by the rules of the tactic, each rule
applying exactly one lemma.

## Rules

A rule of the tactic proves either `f =O[l] g` or, for an *exact* result, `f =Θ[l] g`.

* Exact atoms: `isTheta_const_powExp` (for a nonzero constant), `isTheta_id_powExp`,
  `isTheta_exp_powExp`, `isTheta_cexp_powExp` and `isTheta_log_powExp`.
* Other atoms: `isBigO_const_powExp`, and the bounded factors `isBigO_sin_powExp`,
  `isBigO_cos_powExp` and `isBigO_powExp_of_continuousAt`.
* Products and powers of comparison functions: `isBigO_mul_powExp` and `isBigO_pow_powExp`, and
  `isTheta_mul_powExp` and `isTheta_pow_powExp` for exact results, from
  `powExp_mul_powExp_eventuallyEq` and `powExp_pow_eventuallyEq`.
* Real powers, square roots and complex powers of a function bounded by a comparison function:
  `isBigO_rpow_powExp` (for a nonnegative power) and `isBigO_sqrt_powExp`, and
  `isTheta_rpow_powExp`, `isTheta_sqrt_powExp` and `isTheta_cpow_powExp` for exact results of
  eventually nonnegative, respectively positive, functions, from `powExp_rpow_eventuallyEq`.
* Numeral powers of sums, expanded into products: `isBigO_pow_one` and `isBigO_pow_succ`.
* Integer powers, as natural powers and their inverses: `isBigO_zpow_natCast` and
  `isBigO_zpow_neg_natCast`, and `isTheta_zpow_natCast` and `isTheta_zpow_neg_natCast` for exact
  results.
* Quotients and inverses, pushed inwards: `isBigO_div` for `f / g` as `f * g⁻¹`,
  `isBigO_inv_mul`, `isBigO_inv_div` for `(f / g)⁻¹` as `g / f`, `isBigO_inv_pow` and
  `isBigO_inv_inv`, and `isTheta_div`, `isTheta_inv_mul`, `isTheta_inv_div`, `isTheta_inv_pow`
  and `isTheta_inv_inv` for exact results.
* Sums: `isBigO_add_of_nonneg` and `isBigO_sub_of_nonneg`, with the nonnegativity side goals
  closed by `eventually_nonneg_powExp` and `eventually_nonneg_add`; and, when one summand is exact
  and dominates the other, `isTheta_add_left`, `isTheta_add_right`, `isTheta_sub_left` and
  `isTheta_sub_right`; and, when the summands have the same order, are eventually nonnegative and
  one of them is exact, `isTheta_add_of_nonneg` and `isTheta_add_of_nonneg_right`, with the
  comparison `isBigO_powExp_of_eq`.
* Inverses of exact functions: `isTheta_inv_of_isTheta_powExp`, for instance `(log t)⁻¹`, which
  is `Θ(powExp 0 (-1) 0)`.
* Products of sums: `isBigO_mul_of_isBigO_mul`, then recursively `isBigO_add_mul`,
  `isBigO_mul_add` and `isBigO_powExp_mul_powExp` (see `isBigO_mul_of_isBigO_mul`).
* Norm-preserving wrappers: `Asymptotics.IsBigO.neg_left` and `Asymptotics.IsTheta.neg_left` for
  `-f`, `Asymptotics.IsBigO.norm_left` and `Asymptotics.IsTheta.norm_left` for `‖f‖`,
  `Asymptotics.IsBigO.abs_left` and `Asymptotics.IsTheta.abs_left` for `|f|`, and
  `Complex.isBigO_ofReal_left.2` and `Complex.isTheta_ofReal_left.2` for the cast
  `(f · : ℝ → ℂ)`. The lemmas `Asymptotics.IsTheta.neg_left` and `Asymptotics.IsTheta.abs_left`
  are proved here.

## Exponent bounds

The decision lemmas need exponents which are eventually bounded above, stated as
`Filter.IsBoundedUnder (· ≤ ·) l u`. Constants are handled by Mathlib's
`Filter.isBoundedUnder_const`, sums by `isBoundedUnder_le_fun_add` (or, for `u + v`, by
Mathlib's `Filter.isBoundedUnder_le_add`), and eventual equality by
`isBoundedUnder_le_of_eventuallyEq`. The monomials `c * t ^ p`, with a real degree `p`, are
handled by `isBoundedUnder_le_mul_rpow_atTop`, `isBoundedUnder_le_mul_rpow_of_nonpos` and
`isBoundedUnder_le_mul_rpow_nhdsGT`. A monomial `d * t ^ q` of any sign is absorbed by a monomial
`c * t ^ p` with `c < 0` of more singular degree (`isBoundedUnder_le_mul_rpow_add_mul_rpow`, with
`isBoundedUnder_le_mul_rpow_add_mul_rpow_atTop` for `q < p` and
`isBoundedUnder_le_mul_rpow_add_mul_rpow_nhdsGT` for `p < q`).

## Real parts

`Complex.re_ofReal_pow` and `Complex.im_ofReal_pow` compute the real and imaginary parts of
`(t : ℂ) ^ n`, for the exponents of complex exponentials.

## Decision lemmas

* `integrableAtFilter_powExp_atTop_of_lt`: `powExp a k u` with `a < -1` and `u` bounded above.
* `integrableAtFilter_powExp_atTop_of_log_lt`: `powExp a k u` with `a = -1`, `k < -1` and `u`
  bounded above.
* `integrableAtFilter_powExp_atTop_of_mul_rpow`: decay at `atTop`, as `exp (c * t ^ p)` for
  `c < 0` and `0 < p`.
* `integrableAtFilter_powExp_nhdsGT_of_lt`: `powExp a k u` with `-1 < a` and `u` bounded above.
* `integrableAtFilter_powExp_nhdsGT_of_log_lt`: `powExp a k u` with `a = -1`, `k < -1` and `u`
  bounded above.
* `integrableAtFilter_powExp_nhdsGT_of_mul_rpow`: decay at `𝓝[>] 0`, as `exp (c * t ^ p)` for
  `c < 0` and `p < 0`.

Away from the borderline `a = -1`, the power `k` of the logarithm is absorbed by a power of `t`:
`|log t| ^ k` is `O(t ^ ε)` at `atTop` for `0 < ε` (`isBigO_abs_log_rpow_atTop`) and at `𝓝[>] 0`
for `ε < 0` (`isBigO_abs_log_rpow_nhdsGT`), and then `powExp a k u` is `O(powExp (a + ε) 0 u)`
(`isBigO_powExp_of_isBigO_abs_log`). The borderline cases are the Bertrand integrals
`integrableOn_Ioi_inv_mul_log_rpow` and `integrableOn_Ioc_inv_mul_neg_log_rpow`, proved with the
antiderivatives `log t ^ (k + 1) / (k + 1)` and `-((-log t) ^ (k + 1) / (k + 1))`; for `-1 ≤ k`
the function `t⁻¹ * |log t| ^ k` is not integrable at either end.

A sum `fun t ↦ m₁ t + m₂ t` of comparison functions is integrable at `l` by Mathlib's
`MeasureTheory.IntegrableAtFilter.add`.

## Boundedness lemmas

For an integrable factor of the integrand, the cofactor need only be bounded, `O(1)`, at the end.
`powExp a k u` is `O(1)` in three cases, with `u` eventually bounded above, or with exponential
decay:
* `isBigO_powExp_one_atTop_of_lt`, `isBigO_powExp_one_atTop_of_le` and
  `isBigO_powExp_one_atTop_of_mul_rpow`: at `atTop`, `a < 0`, or `a ≤ 0` and `k ≤ 0`, or decay;
* `isBigO_powExp_one_nhdsGT_of_lt`, `isBigO_powExp_one_nhdsGT_of_le` and
  `isBigO_powExp_one_nhdsGT_of_mul_rpow`: at `𝓝[>] 0`, `0 < a`, or `0 ≤ a` and `k ≤ 0`, or decay.

These are the cases of the decision lemmas with `-1` replaced by `0`; the case `a ≤ 0`, `k ≤ 0`
covers the borderline `a = 0`, `k ≤ 0`, and also gives the weaker condition `a ≤ 0` when `k ≤ 0`
is known.

## Dominance lemmas

`powExp b j v =o[l] powExp a k u` follows from `powExp (b - a) (j - k) (v - u) → 0`, since
`powExp b j v` is eventually the product of this function and `powExp a k u`
(`isLittleO_powExp_of_tendsto`). This limit holds in four cases, whatever `j` and `k`:
* `isLittleO_powExp_atTop_of_lt`: at `atTop`, `b < a` and `v - u` bounded above;
* `isLittleO_powExp_atTop_of_mul_rpow`: at `atTop`, `exp (v - u)` decays as `exp (c * t ^ p)`;
* `isLittleO_powExp_nhdsGT_of_lt`: at `𝓝[>] 0`, `a < b` and `v - u` bounded above;
* `isLittleO_powExp_nhdsGT_of_mul_rpow`: at `𝓝[>] 0`, `exp (v - u)` decays as `exp (c * t ^ p)`.

When the powers of `t` are equal, `isLittleO_powExp_of_log_lt` decides by the real powers of the
logarithm, along both filters: `powExp a j v = o(powExp a k u)` if `j < k` and `v - u` is bounded
above, since then `|log t| ^ (j - k) → 0`.
-/

@[expose] public section

open Filter Asymptotics MeasureTheory Set Topology Real

section Theta

variable {α E F : Type*} [SeminormedAddCommGroup E] [Norm F] {l : Filter α} {g : α → F}

/-- The negation of a function is `Θ` of what the function is. -/
theorem _root_.Asymptotics.IsTheta.neg_left {f : α → E} (h : f =Θ[l] g) :
    (fun x ↦ -f x) =Θ[l] g :=
  isTheta_norm_left.mp <| by simpa only [norm_neg] using h.norm_left

/-- The absolute value of a real function is `Θ` of what the function is. -/
theorem _root_.Asymptotics.IsTheta.abs_left {f : α → ℝ} (h : f =Θ[l] g) :
    (fun x ↦ |f x|) =Θ[l] g := by
  simpa only [Real.norm_eq_abs] using h.norm_left

end Theta

namespace Mathlib.Tactic.EndpointIntegrability

/-- `powExp a k u t = t ^ a * |log t| ^ k * exp (u t)`: the comparison functions of
`endpoint_integrability`. -/
noncomputable def powExp (a k : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ := t ^ a * |log t| ^ k * rexp (u t)

variable {l : Filter ℝ} {a b k j : ℝ} {u v : ℝ → ℝ}

section Basic

/-- `powExp a k u` is nonnegative on `[0, ∞)`. -/
theorem powExp_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ powExp a k u t := by
  unfold powExp
  positivity

/-- `powExp a k u` is measurable when `u` is. -/
theorem measurable_powExp (hu : Measurable u) (a k : ℝ) : Measurable (powExp a k u) :=
  ((measurable_id.pow_const a).mul
    ((continuous_abs.measurable.comp measurable_log).pow_const k)).mul hu.exp

/-- `powExp a k u` is eventually nonnegative along a filter of positive reals. -/
theorem eventually_nonneg_powExp (hl : ∀ᶠ t in l, 0 < t) : 0 ≤ᶠ[l] powExp a k u :=
  hl.mono fun _ ht ↦ powExp_nonneg ht.le

/-- A sum of eventually nonnegative functions is eventually nonnegative: the nonnegativity of a
sum of comparison functions is proved by recursion, with `eventually_nonneg_powExp` at the
leaves. -/
theorem eventually_nonneg_add {m₁ m₂ : ℝ → ℝ} (h₁ : 0 ≤ᶠ[l] m₁) (h₂ : 0 ≤ᶠ[l] m₂) :
    0 ≤ᶠ[l] fun t ↦ m₁ t + m₂ t := by
  filter_upwards [h₁, h₂] with t h₁ h₂ using add_nonneg h₁ h₂

/-- If `u - w` is eventually bounded above, then `powExp a k u =O[l] powExp a k w` along a filter
of positive reals. -/
theorem isBigO_powExp_powExp (hl : ∀ᶠ t in l, 0 < t) {w : ℝ → ℝ}
    (h : IsBoundedUnder (· ≤ ·) l fun t ↦ u t - w t) : powExp a k u =O[l] powExp a k w := by
  obtain ⟨M, hM⟩ := h
  refine .of_bound (rexp M) ?_
  filter_upwards [hl, hM] with t ht hM
  rw [norm_of_nonneg (powExp_nonneg ht.le), norm_of_nonneg (powExp_nonneg ht.le), powExp,
    powExp, mul_left_comm, ← exp_add]
  gcongr
  linarith [show u t - w t ≤ M from hM]

/-- If `b = a`, `j = k` and `v - u` is eventually bounded above, then
`powExp b j v =O[l] powExp a k u` along a filter of positive reals: the comparison of two
comparison functions of the same order. -/
theorem isBigO_powExp_of_eq (hl : ∀ᶠ t in l, 0 < t) (hab : b = a) (hjk : j = k)
    (h : IsBoundedUnder (· ≤ ·) l fun t ↦ v t - u t) : powExp b j v =O[l] powExp a k u := by
  subst hab hjk
  exact isBigO_powExp_powExp hl h

/-- If `u` is eventually bounded above, then `powExp a 0 u =O[l] fun t ↦ t ^ a` along a filter of
positive reals. -/
theorem isBigO_powExp_rpow (hl : ∀ᶠ t in l, 0 < t) (hu : IsBoundedUnder (· ≤ ·) l u) :
    powExp a 0 u =O[l] fun t ↦ t ^ a :=
  (isBigO_powExp_powExp (w := 0) hl <| hu.mono_le <| .of_forall fun t ↦ by simp).congr_right
    fun t ↦ by simp [powExp]

/-- `powExp a k u` is strongly measurable at every filter when `u` is measurable. -/
theorem stronglyMeasurableAtFilter_powExp (hu : Measurable u) (a k : ℝ) {μ : Measure ℝ} :
    StronglyMeasurableAtFilter (powExp a k u) l μ :=
  (measurable_powExp hu a k).aestronglyMeasurable.stronglyMeasurableAtFilter

end Basic

section RealParts

/-- The real part of the power of a real number. The simplification of the exponents of complex
exponentials uses it to compute the real part of a polynomial in `(t : ℂ)`. -/
theorem _root_.Complex.re_ofReal_pow (r : ℝ) (n : ℕ) : ((r : ℂ) ^ n).re = r ^ n := by
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- The imaginary part of the power of a real number is `0`. -/
theorem _root_.Complex.im_ofReal_pow (r : ℝ) (n : ℕ) : ((r : ℂ) ^ n).im = 0 := by
  rw [← Complex.ofReal_pow, Complex.ofReal_im]

end RealParts

section Atoms

variable {E : Type*} [NormedAddCommGroup E]

/-- A constant is `O(powExp 0 0 0)`. -/
theorem isBigO_const_powExp (c : E) : (fun _ : ℝ ↦ c) =O[l] powExp 0 0 0 :=
  (isBigO_const_one ℝ c l).congr_right fun t ↦ by simp [powExp]

/-- A nonzero constant is `Θ(powExp 0 0 0)`. -/
theorem isTheta_const_powExp {c : E} (hc : c ≠ 0) : (fun _ : ℝ ↦ c) =Θ[l] powExp 0 0 0 :=
  (isTheta_const_const hc one_ne_zero).trans_eventuallyEq <| .of_forall fun t ↦ by simp [powExp]

/-- The identity is `Θ(powExp 1 0 0)`. -/
theorem isTheta_id_powExp : (fun t : ℝ ↦ t) =Θ[l] powExp 1 0 0 :=
  EventuallyEq.isTheta <| .of_forall fun t ↦ by simp [powExp]

/-- `exp (u t)` is `Θ(powExp 0 0 u)`. -/
theorem isTheta_exp_powExp : (fun t ↦ rexp (u t)) =Θ[l] powExp 0 0 u :=
  EventuallyEq.isTheta <| .of_forall fun t ↦ by simp [powExp]

/-- A complex exponential `exp (z t)` is `Θ(powExp 0 0 (re ∘ z))`. -/
theorem isTheta_cexp_powExp (z : ℝ → ℂ) :
    (fun t ↦ Complex.exp (z t)) =Θ[l] powExp 0 0 fun t ↦ (z t).re :=
  .of_norm_eventuallyEq <| .of_forall fun t ↦ by simp [powExp, Complex.norm_exp]

/-- The logarithm `log t` is `Θ(powExp 0 1 0)`. -/
theorem isTheta_log_powExp : (fun t : ℝ ↦ log t) =Θ[l] powExp 0 1 0 :=
  .of_norm_eventuallyEq <| .of_forall fun t ↦ by simp [powExp]

/-- `sin (g t)` is `O(powExp 0 0 0)`. -/
theorem isBigO_sin_powExp (g : ℝ → ℝ) : (fun t ↦ sin (g t)) =O[l] powExp 0 0 0 :=
  isBigO_of_le _ fun t ↦ by simpa [powExp] using abs_sin_le_one (g t)

/-- `cos (g t)` is `O(powExp 0 0 0)`. -/
theorem isBigO_cos_powExp (g : ℝ → ℝ) : (fun t ↦ cos (g t)) =O[l] powExp 0 0 0 :=
  isBigO_of_le _ fun t ↦ by simpa [powExp] using abs_cos_le_one (g t)

/-- A function continuous at `0` is `O(powExp 0 0 0)` along `𝓝[>] 0`. -/
theorem isBigO_powExp_of_continuousAt {f : ℝ → E} (hf : ContinuousAt f 0) :
    f =O[𝓝[>] 0] powExp 0 0 0 :=
  ((hf.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ).congr_right fun t ↦ by simp [powExp]

end Atoms

section Combination

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E]

/-- A product of two comparison functions is eventually a comparison function, along a filter of
positive reals along which `|log t| → ∞`. -/
theorem powExp_mul_powExp_eventuallyEq (hl : ∀ᶠ t in l, 0 < t)
    (hlog : Tendsto (fun t ↦ |log t|) l atTop) :
    (fun t ↦ powExp a k u t * powExp b j v t) =ᶠ[l] powExp (a + b) (k + j) (u + v) := by
  filter_upwards [hl, hlog.eventually_gt_atTop 0] with t ht hlog
  simp only [powExp, rpow_add ht, rpow_add hlog, Pi.add_apply, exp_add]
  ring

/-- A product of two comparison functions is a comparison function, up to `O`, along a filter of
positive reals along which `|log t| → ∞`. This is the leaf case of the recursion of
`isBigO_mul_of_isBigO_mul`. -/
theorem isBigO_powExp_mul_powExp (hl : ∀ᶠ t in l, 0 < t)
    (hlog : Tendsto (fun t ↦ |log t|) l atTop) :
    (fun t ↦ powExp a k u t * powExp b j v t) =O[l] powExp (a + b) (k + j) (u + v) :=
  (powExp_mul_powExp_eventuallyEq hl hlog).isBigO

/-- Product rule: if `f = O(powExp a k u)` and `g = O(powExp b j v)`, then
`f * g = O(powExp (a + b) (k + j) (u + v))`, along a filter of positive reals along which
`|log t| → ∞`. -/
theorem isBigO_mul_powExp (hl : ∀ᶠ t in l, 0 < t) (hlog : Tendsto (fun t ↦ |log t|) l atTop)
    {f g : ℝ → 𝕜} (hf : f =O[l] powExp a k u) (hg : g =O[l] powExp b j v) :
    (fun t ↦ f t * g t) =O[l] powExp (a + b) (k + j) (u + v) :=
  (hf.mul hg).trans_eventuallyEq (powExp_mul_powExp_eventuallyEq hl hlog)

/-- Exact product rule: if `f = Θ(powExp a k u)` and `g = Θ(powExp b j v)`, then
`f * g = Θ(powExp (a + b) (k + j) (u + v))`, along a filter of positive reals along which
`|log t| → ∞`. -/
theorem isTheta_mul_powExp (hl : ∀ᶠ t in l, 0 < t) (hlog : Tendsto (fun t ↦ |log t|) l atTop)
    {f g : ℝ → 𝕜} (hf : f =Θ[l] powExp a k u) (hg : g =Θ[l] powExp b j v) :
    (fun t ↦ f t * g t) =Θ[l] powExp (a + b) (k + j) (u + v) :=
  (hf.mul hg).trans_eventuallyEq (powExp_mul_powExp_eventuallyEq hl hlog)

/-- A natural power of a comparison function is eventually a comparison function, along a filter
of positive reals. -/
theorem powExp_pow_eventuallyEq (hl : ∀ᶠ t in l, 0 < t) (n : ℕ) :
    (fun t ↦ powExp a k u t ^ n) =ᶠ[l] powExp (n * a) (n * k) (n • u) :=
  hl.mono fun t ht ↦ by
    simp only [powExp, mul_pow, mul_comm (n : ℝ) a, mul_comm (n : ℝ) k, rpow_mul_natCast ht.le,
      rpow_mul_natCast (abs_nonneg (log t)), Pi.smul_apply, nsmul_eq_mul, exp_natCast_mul]

/-- Power rule: if `f = O(powExp a k u)`, then `f ^ n = O(powExp (n * a) (n * k) (n • u))`, along
a filter of positive reals. -/
theorem isBigO_pow_powExp (hl : ∀ᶠ t in l, 0 < t) {f : ℝ → 𝕜} (hf : f =O[l] powExp a k u)
    (n : ℕ) : (fun t ↦ f t ^ n) =O[l] powExp (n * a) (n * k) (n • u) :=
  (hf.pow n).trans_eventuallyEq (powExp_pow_eventuallyEq hl n)

/-- Exact power rule: if `f = Θ(powExp a k u)`, then `f ^ n = Θ(powExp (n * a) (n * k) (n • u))`,
along a filter of positive reals. -/
theorem isTheta_pow_powExp (hl : ∀ᶠ t in l, 0 < t) {f : ℝ → 𝕜} (hf : f =Θ[l] powExp a k u)
    (n : ℕ) : (fun t ↦ f t ^ n) =Θ[l] powExp (n * a) (n * k) (n • u) :=
  (hf.pow n).trans_eventuallyEq (powExp_pow_eventuallyEq hl n)

/-- Sum rule: if `f = O(m₁)` and `g = O(m₂)` for eventually nonnegative `m₁` and `m₂`, then
`f + g = O(m₁ + m₂)`. -/
theorem isBigO_add_of_nonneg {m₁ m₂ : ℝ → ℝ} {f g : ℝ → E} (hf : f =O[l] m₁) (hg : g =O[l] m₂)
    (h₁ : 0 ≤ᶠ[l] m₁) (h₂ : 0 ≤ᶠ[l] m₂) : (fun t ↦ f t + g t) =O[l] fun t ↦ m₁ t + m₂ t := by
  have h (m m' : ℝ → ℝ) (h : 0 ≤ᶠ[l] m) (h' : 0 ≤ᶠ[l] m') : m =O[l] fun t ↦ m t + m' t :=
    .of_bound' <| by
      filter_upwards [h, h'] with t h h'
      rw [norm_of_nonneg h, norm_of_nonneg (add_nonneg h h')]
      linarith [show (0 : ℝ) ≤ m' t from h']
  exact (hf.trans (h _ _ h₁ h₂)).add <| (hg.trans (h _ _ h₂ h₁)).congr_right fun t ↦ add_comm _ _

/-- Difference rule: if `f = O(m₁)` and `g = O(m₂)` for eventually nonnegative `m₁` and `m₂`,
then `f - g = O(m₁ + m₂)`. -/
theorem isBigO_sub_of_nonneg {m₁ m₂ : ℝ → ℝ} {f g : ℝ → E} (hf : f =O[l] m₁) (hg : g =O[l] m₂)
    (h₁ : 0 ≤ᶠ[l] m₁) (h₂ : 0 ≤ᶠ[l] m₂) : (fun t ↦ f t - g t) =O[l] fun t ↦ m₁ t + m₂ t := by
  simpa only [sub_eq_add_neg] using isBigO_add_of_nonneg hf hg.neg_left h₁ h₂

/-- Dominant sum rule: if `f = Θ(m)`, `g = O(m')` and `m' = o(m)`, then `f + g = Θ(m)`. -/
theorem isTheta_add_left {m m' : ℝ → ℝ} {f g : ℝ → E} (hf : f =Θ[l] m) (hg : g =O[l] m')
    (h : m' =o[l] m) : (fun t ↦ f t + g t) =Θ[l] m :=
  hf.add_isLittleO (hg.trans_isLittleO h)

/-- Dominant sum rule: if `f = O(m')`, `g = Θ(m)` and `m' = o(m)`, then `f + g = Θ(m)`. -/
theorem isTheta_add_right {m m' : ℝ → ℝ} {f g : ℝ → E} (hf : f =O[l] m') (hg : g =Θ[l] m)
    (h : m' =o[l] m) : (fun t ↦ f t + g t) =Θ[l] m :=
  (hf.trans_isLittleO h).add_isTheta hg

/-- Dominant difference rule: if `f = Θ(m)`, `g = O(m')` and `m' = o(m)`, then `f - g = Θ(m)`. -/
theorem isTheta_sub_left {m m' : ℝ → ℝ} {f g : ℝ → E} (hf : f =Θ[l] m) (hg : g =O[l] m')
    (h : m' =o[l] m) : (fun t ↦ f t - g t) =Θ[l] m := by
  simpa only [sub_eq_add_neg] using isTheta_add_left hf hg.neg_left h

/-- Dominant difference rule: if `f = O(m')`, `g = Θ(m)` and `m' = o(m)`, then `f - g = Θ(m)`. -/
theorem isTheta_sub_right {m m' : ℝ → ℝ} {f g : ℝ → E} (hf : f =O[l] m') (hg : g =Θ[l] m)
    (h : m' =o[l] m) : (fun t ↦ f t - g t) =Θ[l] m := by
  simpa only [sub_eq_add_neg] using isTheta_add_right hf hg.neg_left h

/-- Sum rule for summands of the same order: if `f = Θ(m)`, `g = O(m)` and `f` and `g` are
eventually nonnegative, then `f + g = Θ(m)`, since `f ≤ f + g` eventually. -/
theorem isTheta_add_of_nonneg {m : ℝ → ℝ} {f g : ℝ → ℝ} (hf : f =Θ[l] m) (hg : g =O[l] m)
    (hf₀ : ∀ᶠ t in l, 0 ≤ f t) (hg₀ : ∀ᶠ t in l, 0 ≤ g t) : (fun t ↦ f t + g t) =Θ[l] m := by
  refine ⟨hf.isBigO.add hg, hf.symm.isBigO.trans <| .of_bound' ?_⟩
  filter_upwards [hf₀, hg₀] with t hf₀ hg₀
  rw [norm_of_nonneg hf₀, norm_of_nonneg (add_nonneg hf₀ hg₀)]
  linarith

/-- Sum rule for summands of the same order: if `f = O(m)`, `g = Θ(m)` and `f` and `g` are
eventually nonnegative, then `f + g = Θ(m)`. -/
theorem isTheta_add_of_nonneg_right {m : ℝ → ℝ} {f g : ℝ → ℝ} (hf : f =O[l] m) (hg : g =Θ[l] m)
    (hf₀ : ∀ᶠ t in l, 0 ≤ f t) (hg₀ : ∀ᶠ t in l, 0 ≤ g t) : (fun t ↦ f t + g t) =Θ[l] m := by
  simpa only [add_comm] using isTheta_add_of_nonneg hg hf hg₀ hf₀

/-- Product rule for sums of comparison functions: if `f = O(m₁)`, `g = O(m₂)` and
`m₁ * m₂ = O(p)`, then `f * g = O(p)`.

To bound `f * g` when `m₁` and `m₂` are binary trees of comparison functions `powExp a k u`
combined by `fun t ↦ _ + _`, apply this lemma and prove `(fun t ↦ m₁ t * m₂ t) =O[l] ?p` by
recursion, applying one lemma per node: `isBigO_add_mul` if `m₁` is a sum, otherwise
`isBigO_mul_add` if `m₂` is a sum, otherwise `isBigO_powExp_mul_powExp`. The nonnegativity side
goals are closed by `eventually_nonneg_add` and `eventually_nonneg_powExp`. -/
theorem isBigO_mul_of_isBigO_mul {m₁ m₂ p : ℝ → ℝ} {f g : ℝ → 𝕜} (hf : f =O[l] m₁)
    (hg : g =O[l] m₂) (h : (fun t ↦ m₁ t * m₂ t) =O[l] p) : (fun t ↦ f t * g t) =O[l] p :=
  (hf.mul hg).trans h

/-- Distributivity on the left for the recursion of `isBigO_mul_of_isBigO_mul`: if
`m₁ * m₃ = O(p₁)` and `m₂ * m₃ = O(p₂)` for eventually nonnegative `p₁` and `p₂`, then
`(m₁ + m₂) * m₃ = O(p₁ + p₂)`. -/
theorem isBigO_add_mul {m₁ m₂ m₃ p₁ p₂ : ℝ → ℝ} (h₁ : (fun t ↦ m₁ t * m₃ t) =O[l] p₁)
    (h₂ : (fun t ↦ m₂ t * m₃ t) =O[l] p₂) (hp₁ : 0 ≤ᶠ[l] p₁) (hp₂ : 0 ≤ᶠ[l] p₂) :
    (fun t ↦ (m₁ t + m₂ t) * m₃ t) =O[l] fun t ↦ p₁ t + p₂ t := by
  simpa only [add_mul] using isBigO_add_of_nonneg h₁ h₂ hp₁ hp₂

/-- Distributivity on the right for the recursion of `isBigO_mul_of_isBigO_mul`: if
`m₁ * m₂ = O(p₁)` and `m₁ * m₃ = O(p₂)` for eventually nonnegative `p₁` and `p₂`, then
`m₁ * (m₂ + m₃) = O(p₁ + p₂)`. -/
theorem isBigO_mul_add {m₁ m₂ m₃ p₁ p₂ : ℝ → ℝ} (h₁ : (fun t ↦ m₁ t * m₂ t) =O[l] p₁)
    (h₂ : (fun t ↦ m₁ t * m₃ t) =O[l] p₂) (hp₁ : 0 ≤ᶠ[l] p₁) (hp₂ : 0 ≤ᶠ[l] p₂) :
    (fun t ↦ m₁ t * (m₂ t + m₃ t)) =O[l] fun t ↦ p₁ t + p₂ t := by
  simpa only [mul_add] using isBigO_add_of_nonneg h₁ h₂ hp₁ hp₂

/-- Base case of the expansion of a power of a sum: `f ^ 1 = O(m)` if `f = O(m)`. -/
theorem isBigO_pow_one {m : ℝ → ℝ} {f : ℝ → 𝕜} (hf : f =O[l] m) :
    (fun t ↦ f t ^ 1) =O[l] m := by
  simpa only [pow_one] using hf

/-- Expansion of a power of a sum: if `f ^ n = O(m₁)`, `f = O(m₂)` and `m₁ * m₂ = O(p)`, then
`f ^ (n + 1) = O(p)`. -/
theorem isBigO_pow_succ {m₁ m₂ p : ℝ → ℝ} {f : ℝ → 𝕜} {n : ℕ}
    (hn : (fun t ↦ f t ^ n) =O[l] m₁) (hf : f =O[l] m₂) (h : (fun t ↦ m₁ t * m₂ t) =O[l] p) :
    (fun t ↦ f t ^ (n + 1)) =O[l] p := by
  simpa only [pow_succ] using isBigO_mul_of_isBigO_mul hn hf h

/-- Quotient rule: `f / g` is bounded as `f * g⁻¹`. -/
theorem isBigO_div {m : ℝ → ℝ} {f g : ℝ → 𝕜} (h : (fun t ↦ f t * (g t)⁻¹) =O[l] m) :
    (fun t ↦ f t / g t) =O[l] m := by
  simpa only [div_eq_mul_inv] using h

/-- Exact quotient rule: `f / g` is `Θ` of what `f * g⁻¹` is. -/
theorem isTheta_div {m : ℝ → ℝ} {f g : ℝ → 𝕜} (h : (fun t ↦ f t * (g t)⁻¹) =Θ[l] m) :
    (fun t ↦ f t / g t) =Θ[l] m := by
  simpa only [div_eq_mul_inv] using h

/-- The inverse of a product is bounded as the product of the inverses. -/
theorem isBigO_inv_mul {m : ℝ → ℝ} {f g : ℝ → 𝕜} (h : (fun t ↦ (f t)⁻¹ * (g t)⁻¹) =O[l] m) :
    (fun t ↦ (f t * g t)⁻¹) =O[l] m := by
  simpa only [mul_inv] using h

/-- The inverse of a product is `Θ` of what the product of the inverses is. -/
theorem isTheta_inv_mul {m : ℝ → ℝ} {f g : ℝ → 𝕜} (h : (fun t ↦ (f t)⁻¹ * (g t)⁻¹) =Θ[l] m) :
    (fun t ↦ (f t * g t)⁻¹) =Θ[l] m := by
  simpa only [mul_inv] using h

/-- The inverse of a quotient `f / g` is bounded as `g / f`. -/
theorem isBigO_inv_div {m : ℝ → ℝ} {f g : ℝ → 𝕜} (h : (fun t ↦ g t / f t) =O[l] m) :
    (fun t ↦ (f t / g t)⁻¹) =O[l] m := by
  simpa only [inv_div] using h

/-- The inverse of a quotient `f / g` is `Θ` of what `g / f` is. -/
theorem isTheta_inv_div {m : ℝ → ℝ} {f g : ℝ → 𝕜} (h : (fun t ↦ g t / f t) =Θ[l] m) :
    (fun t ↦ (f t / g t)⁻¹) =Θ[l] m := by
  simpa only [inv_div] using h

/-- The inverse of a power is bounded as the power of the inverse. -/
theorem isBigO_inv_pow {m : ℝ → ℝ} {f : ℝ → 𝕜} {n : ℕ} (h : (fun t ↦ (f t)⁻¹ ^ n) =O[l] m) :
    (fun t ↦ (f t ^ n)⁻¹) =O[l] m := by
  simpa only [inv_pow] using h

/-- The inverse of a power is `Θ` of what the power of the inverse is. -/
theorem isTheta_inv_pow {m : ℝ → ℝ} {f : ℝ → 𝕜} {n : ℕ} (h : (fun t ↦ (f t)⁻¹ ^ n) =Θ[l] m) :
    (fun t ↦ (f t ^ n)⁻¹) =Θ[l] m := by
  simpa only [inv_pow] using h

/-- The inverse of an inverse is bounded as the function itself. -/
theorem isBigO_inv_inv {m : ℝ → ℝ} {f : ℝ → 𝕜} (h : f =O[l] m) :
    (fun t ↦ (f t)⁻¹⁻¹) =O[l] m := by
  simpa only [inv_inv] using h

/-- The inverse of an inverse is `Θ` of what the function itself is. -/
theorem isTheta_inv_inv {m : ℝ → ℝ} {f : ℝ → 𝕜} (h : f =Θ[l] m) :
    (fun t ↦ (f t)⁻¹⁻¹) =Θ[l] m := by
  simpa only [inv_inv] using h

/-- An integer power `f ^ (n : ℤ)` with `n : ℕ` is bounded as the natural power `f ^ n`. -/
theorem isBigO_zpow_natCast {m : ℝ → ℝ} {f : ℝ → 𝕜} {n : ℕ} (h : (fun t ↦ f t ^ n) =O[l] m) :
    (fun t ↦ f t ^ (n : ℤ)) =O[l] m := by
  simpa only [zpow_natCast] using h

/-- An integer power `f ^ (n : ℤ)` with `n : ℕ` is `Θ` of what the natural power `f ^ n` is. -/
theorem isTheta_zpow_natCast {m : ℝ → ℝ} {f : ℝ → 𝕜} {n : ℕ} (h : (fun t ↦ f t ^ n) =Θ[l] m) :
    (fun t ↦ f t ^ (n : ℤ)) =Θ[l] m := by
  simpa only [zpow_natCast] using h

/-- An integer power `f ^ (-n : ℤ)` with `n : ℕ` is bounded as the inverse `(f ^ n)⁻¹`. -/
theorem isBigO_zpow_neg_natCast {m : ℝ → ℝ} {f : ℝ → 𝕜} {n : ℕ}
    (h : (fun t ↦ (f t ^ n)⁻¹) =O[l] m) : (fun t ↦ f t ^ (-(n : ℤ))) =O[l] m := by
  simpa only [zpow_neg, zpow_natCast] using h

/-- An integer power `f ^ (-n : ℤ)` with `n : ℕ` is `Θ` of what the inverse `(f ^ n)⁻¹` is. -/
theorem isTheta_zpow_neg_natCast {m : ℝ → ℝ} {f : ℝ → 𝕜} {n : ℕ}
    (h : (fun t ↦ (f t ^ n)⁻¹) =Θ[l] m) : (fun t ↦ f t ^ (-(n : ℤ))) =Θ[l] m := by
  simpa only [zpow_neg, zpow_natCast] using h

/-- Exact inverse rule: if `f = Θ(powExp a k u)`, then `f⁻¹ = Θ(powExp (-a) (-k) (-u))`, along a
filter of positive reals. -/
theorem isTheta_inv_of_isTheta_powExp (hl : ∀ᶠ t in l, 0 < t) {f : ℝ → 𝕜}
    (hf : f =Θ[l] powExp a k u) : (fun t ↦ (f t)⁻¹) =Θ[l] powExp (-a) (-k) (-u) :=
  hf.inv.trans_eventuallyEq <| hl.mono fun t ht ↦ by
    simp [powExp, rpow_neg ht.le, rpow_neg (abs_nonneg (log t)), exp_neg, mul_comm]

end Combination

section RealPowers

/-- A real power of a comparison function is eventually a comparison function, along a filter of
positive reals. -/
theorem powExp_rpow_eventuallyEq (hl : ∀ᶠ t in l, 0 < t) (p : ℝ) :
    (fun t ↦ powExp a k u t ^ p) =ᶠ[l] powExp (p * a) (p * k) (p • u) :=
  hl.mono fun t ht ↦ by
    simp only [powExp, Pi.smul_apply, smul_eq_mul]
    rw [mul_rpow (by positivity) (exp_pos _).le, mul_rpow (by positivity) (by positivity),
      ← rpow_mul ht.le, ← rpow_mul (abs_nonneg _), mul_comm a p, mul_comm k p, ← exp_mul,
      mul_comm (u t) p]

/-- Real power rule: if `f = O(powExp a k u)` and `0 ≤ p`, then
`f ^ p = O(powExp (p * a) (p * k) (p • u))`, along a filter of positive reals. -/
theorem isBigO_rpow_powExp (hl : ∀ᶠ t in l, 0 < t) {f : ℝ → ℝ} (hf : f =O[l] powExp a k u)
    {p : ℝ} (hp : 0 ≤ p) : (fun t ↦ f t ^ p) =O[l] powExp (p * a) (p * k) (p • u) :=
  (hf.rpow hp (eventually_nonneg_powExp hl)).trans_eventuallyEq (powExp_rpow_eventuallyEq hl p)

/-- Exact real power rule: if `f = Θ(powExp a k u)` and `f` is eventually nonnegative, then
`f ^ p = Θ(powExp (p * a) (p * k) (p • u))`, along a filter of positive reals. -/
theorem isTheta_rpow_powExp (hl : ∀ᶠ t in l, 0 < t) {f : ℝ → ℝ} (hf : f =Θ[l] powExp a k u)
    (hf₀ : ∀ᶠ t in l, 0 ≤ f t) (p : ℝ) :
    (fun t ↦ f t ^ p) =Θ[l] powExp (p * a) (p * k) (p • u) :=
  (hf.rpow hf₀ (eventually_nonneg_powExp hl)).trans_eventuallyEq (powExp_rpow_eventuallyEq hl p)

/-- Square root rule: if `f = O(powExp a k u)`, then
`√f = O(powExp (1 / 2 * a) (1 / 2 * k) ((1 / 2) • u))`, along a filter of positive reals. -/
theorem isBigO_sqrt_powExp (hl : ∀ᶠ t in l, 0 < t) {f : ℝ → ℝ} (hf : f =O[l] powExp a k u) :
    (fun t ↦ √(f t)) =O[l] powExp (1 / 2 * a) (1 / 2 * k) ((1 / 2 : ℝ) • u) := by
  simpa only [sqrt_eq_rpow] using isBigO_rpow_powExp hl hf (p := 1 / 2) (by norm_num)

/-- Exact square root rule: if `f = Θ(powExp a k u)` and `f` is eventually nonnegative, then
`√f = Θ(powExp (1 / 2 * a) (1 / 2 * k) ((1 / 2) • u))`, along a filter of positive reals. -/
theorem isTheta_sqrt_powExp (hl : ∀ᶠ t in l, 0 < t) {f : ℝ → ℝ} (hf : f =Θ[l] powExp a k u)
    (hf₀ : ∀ᶠ t in l, 0 ≤ f t) :
    (fun t ↦ √(f t)) =Θ[l] powExp (1 / 2 * a) (1 / 2 * k) ((1 / 2 : ℝ) • u) := by
  simpa only [sqrt_eq_rpow] using isTheta_rpow_powExp hl hf hf₀ (1 / 2)

/-- Exact complex power rule: if `f = Θ(powExp a k u)` and `f` is eventually positive, then
`(f : ℂ) ^ s = Θ(powExp (s.re * a) (s.re * k) (s.re • u))`, along a filter of positive reals,
since `‖(f t : ℂ) ^ s‖ = f t ^ s.re`. -/
theorem isTheta_cpow_powExp (hl : ∀ᶠ t in l, 0 < t) {f : ℝ → ℝ} (hf : f =Θ[l] powExp a k u)
    (hf₀ : ∀ᶠ t in l, 0 < f t) (s : ℂ) :
    (fun t ↦ (f t : ℂ) ^ s) =Θ[l] powExp (s.re * a) (s.re * k) (s.re • u) :=
  isTheta_norm_left.mp <| EventuallyEq.trans_isTheta
    (hf₀.mono fun _ h ↦ Complex.norm_cpow_eq_rpow_re_of_pos h s)
    (isTheta_rpow_powExp hl hf (hf₀.mono fun _ h ↦ h.le) s.re)

end RealPowers

section ExponentBounds

/-- A sum of functions eventually bounded above is eventually bounded above. This is
`Filter.isBoundedUnder_le_add` for `fun t ↦ u t + v t` instead of `u + v`. -/
theorem isBoundedUnder_le_fun_add (hu : IsBoundedUnder (· ≤ ·) l u)
    (hv : IsBoundedUnder (· ≤ ·) l v) : IsBoundedUnder (· ≤ ·) l fun t ↦ u t + v t :=
  isBoundedUnder_le_add hu hv

/-- Being eventually bounded above is invariant under eventual equality. -/
theorem isBoundedUnder_le_of_eventuallyEq (h : u =ᶠ[l] v) (hu : IsBoundedUnder (· ≤ ·) l u) :
    IsBoundedUnder (· ≤ ·) l v :=
  hu.mono_le h.symm.le

/-- `c * t ^ p` is eventually bounded above along `atTop` when `p ≤ 0`. -/
theorem isBoundedUnder_le_mul_rpow_atTop (c : ℝ) {p : ℝ} (hp : p ≤ 0) :
    IsBoundedUnder (· ≤ ·) atTop fun t : ℝ ↦ c * t ^ p := by
  refine isBoundedUnder_of_eventually_le (a := |c|) ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  exact (mul_le_mul_of_nonneg_right (le_abs_self c) (rpow_nonneg (zero_le_one.trans ht) p)).trans
    (mul_le_of_le_one_right (abs_nonneg c) (rpow_le_one_of_one_le_of_nonpos ht hp))

/-- `c * t ^ p` is eventually bounded above along a filter of positive reals when `c ≤ 0`. -/
theorem isBoundedUnder_le_mul_rpow_of_nonpos (hl : ∀ᶠ t in l, 0 < t) {c : ℝ} (hc : c ≤ 0)
    (p : ℝ) : IsBoundedUnder (· ≤ ·) l fun t : ℝ ↦ c * t ^ p :=
  isBoundedUnder_of_eventually_le (a := 0) <|
    hl.mono fun _ ht ↦ mul_nonpos_of_nonpos_of_nonneg hc (rpow_nonneg ht.le p)

/-- `c * t ^ p` is eventually bounded above along `𝓝[>] 0` when `0 ≤ p`. -/
theorem isBoundedUnder_le_mul_rpow_nhdsGT (c : ℝ) {p : ℝ} (hp : 0 ≤ p) :
    IsBoundedUnder (· ≤ ·) (𝓝[>] 0) fun t : ℝ ↦ c * t ^ p := by
  refine isBoundedUnder_of_eventually_le (a := |c|) ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
  exact (mul_le_mul_of_nonneg_right (le_abs_self c) (rpow_nonneg ht.1.le p)).trans
    (mul_le_of_le_one_right (abs_nonneg c) (rpow_le_one ht.1.le ht.2.le hp))

/-- A monomial `d * t ^ q` is absorbed by a monomial `c * t ^ p` with `c < 0`, whatever the sign
of `d`, along a filter of positive reals along which `t ^ (p - q)` tends to `atTop`:
`c * t ^ p + d * t ^ q` is eventually nonpositive. -/
theorem isBoundedUnder_le_mul_rpow_add_mul_rpow (hl : ∀ᶠ t in l, 0 < t) {c p q : ℝ} (hc : c < 0)
    (hpq : Tendsto (fun t : ℝ ↦ t ^ (p - q)) l atTop) (d : ℝ) :
    IsBoundedUnder (· ≤ ·) l fun t : ℝ ↦ c * t ^ p + d * t ^ q := by
  refine isBoundedUnder_of_eventually_le (a := 0) ?_
  filter_upwards [hl, tendsto_atTop.mp hpq (|d| / -c)] with t ht h
  have hq : 0 < t ^ q := rpow_pos_of_pos ht q
  have hp : t ^ p = t ^ (p - q) * t ^ q := by rw [← rpow_add ht, sub_add_cancel]
  have : |d| ≤ -c * t ^ (p - q) := by rwa [div_le_iff₀' (neg_pos.mpr hc)] at h
  rw [hp]
  nlinarith [le_abs_self d, mul_le_mul_of_nonneg_right this hq.le]

/-- Along `atTop`, a monomial `d * t ^ q` is absorbed by a monomial `c * t ^ p` with `c < 0` and
`q < p`, whatever the sign of `d`. -/
theorem isBoundedUnder_le_mul_rpow_add_mul_rpow_atTop {c p q : ℝ} (hc : c < 0) (hqp : q < p)
    (d : ℝ) : IsBoundedUnder (· ≤ ·) atTop fun t : ℝ ↦ c * t ^ p + d * t ^ q :=
  isBoundedUnder_le_mul_rpow_add_mul_rpow (eventually_gt_atTop 0) hc
    (tendsto_rpow_atTop (sub_pos.mpr hqp)) d

/-- Along `𝓝[>] 0`, a monomial `d * t ^ q` is absorbed by a monomial `c * t ^ p` with `c < 0` and
`p < q`, whatever the sign of `d`. -/
theorem isBoundedUnder_le_mul_rpow_add_mul_rpow_nhdsGT {c p q : ℝ} (hc : c < 0) (hpq : p < q)
    (d : ℝ) : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) fun t : ℝ ↦ c * t ^ p + d * t ^ q :=
  isBoundedUnder_le_mul_rpow_add_mul_rpow self_mem_nhdsWithin hc
    (tendsto_rpow_neg_nhdsGT_zero (sub_neg.mpr hpq)) d

end ExponentBounds

section Decision

/-- A real power of `|log t|` is `O` of any positive power of `t` at `atTop`. -/
theorem isBigO_abs_log_rpow_atTop (k : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (fun t ↦ |log t| ^ k) =O[atTop] fun t ↦ t ^ ε :=
  (isLittleO_log_rpow_rpow_atTop k hε).isBigO.congr'
    ((eventually_ge_atTop 1).mono fun t ht ↦ by simp only [abs_of_nonneg (log_nonneg ht)]) .rfl

/-- A real power of `|log t|` is `O` of any negative power of `t` at `𝓝[>] 0`. -/
theorem isBigO_abs_log_rpow_nhdsGT (k : ℝ) {ε : ℝ} (hε : ε < 0) :
    (fun t ↦ |log t| ^ k) =O[𝓝[>] 0] fun t ↦ t ^ ε :=
  (isLittleO_abs_log_rpow_rpow_nhdsGT_zero k hε).isBigO

/-- If `|log t| ^ k = O(t ^ ε)`, then `powExp a k u = O(powExp (a + ε) 0 u)`, along a filter of
positive reals: the power of the logarithm is absorbed by the power of `t`. -/
theorem isBigO_powExp_of_isBigO_abs_log (hl : ∀ᶠ t in l, 0 < t) {ε : ℝ}
    (h : (fun t ↦ |log t| ^ k) =O[l] fun t ↦ t ^ ε) : powExp a k u =O[l] powExp (a + ε) 0 u :=
  (((isBigO_refl (fun t : ℝ ↦ t ^ a) l).mul h).mul (isBigO_refl (fun t ↦ rexp (u t)) l))
    |>.trans_eventuallyEq <| hl.mono fun t ht ↦ by simp [powExp, rpow_add ht]

/-- If `t ^ p → ∞` along a filter of positive reals, with `p ≠ 0`, then
`powExp b 0 (c * t ^ p) → 0` for `c < 0`. -/
theorem tendsto_powExp_mul_rpow (hl : ∀ᶠ t in l, 0 < t) {c : ℝ} (hc : c < 0) {p : ℝ}
    (hp : p ≠ 0) (h : Tendsto (fun t : ℝ ↦ t ^ p) l atTop) (b : ℝ) :
    Tendsto (powExp b 0 fun t ↦ c * t ^ p) l (𝓝 0) := by
  refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b / p) (-c) (by linarith)).comp
    h).congr' <| hl.mono fun t ht ↦ ?_
  simp only [Function.comp_apply, powExp, neg_neg, ← rpow_mul ht.le, mul_div_cancel₀ b hp,
    rpow_zero, mul_one]

/-- The Bertrand integral at `∞`: `t⁻¹ * log t ^ k` is integrable on `(c, ∞)` for `1 < c` when
`k < -1`, with the antiderivative `log t ^ (k + 1) / (k + 1)`, which tends to `0`. -/
theorem integrableOn_Ioi_inv_mul_log_rpow {k : ℝ} (hk : k < -1) {c : ℝ} (hc : 1 < c) :
    IntegrableOn (fun t ↦ t⁻¹ * log t ^ k) (Ioi c) := by
  have hk₁ : k + 1 ≠ 0 := by linarith
  refine integrableOn_Ioi_deriv_of_nonneg' (g := fun t ↦ log t ^ (k + 1) / (k + 1)) (l := 0)
    (fun t ht ↦ ?_) (fun t ht ↦ ?_) ?_
  · have hlog : 0 < log t := log_pos (hc.trans_le ht)
    convert ((hasDerivAt_log (by linarith [mem_Ici.1 ht])).rpow_const (p := k + 1)
      (.inl hlog.ne')).div_const (k + 1) using 1
    field_simp
    ring_nf
  · have hlog : 0 < log t := log_pos (hc.trans ht)
    have : 0 < t := by linarith [mem_Ioi.1 ht]
    positivity
  · simpa using ((tendsto_rpow_neg_atTop (y := -(k + 1)) (by linarith)).comp
      tendsto_log_atTop).div_const (k + 1)

/-- The Bertrand integral at `0`: `t⁻¹ * (-log t) ^ k` is integrable on `(0, c]` for `c < 1` when
`k < -1`, with the antiderivative `-((-log t) ^ (k + 1) / (k + 1))`, which tends to `0` at `0`. -/
theorem integrableOn_Ioc_inv_mul_neg_log_rpow {k : ℝ} (hk : k < -1) {c : ℝ} (hc : c < 1) :
    IntegrableOn (fun t ↦ t⁻¹ * (-log t) ^ k) (Ioc 0 c) := by
  have hk₁ : k + 1 ≠ 0 := by linarith
  set G : ℝ → ℝ := fun t ↦ -((-log t) ^ (k + 1) / (k + 1))
  have hderiv : ∀ t ∈ Ioo 0 1, HasDerivAt G (t⁻¹ * (-log t) ^ k) t := by
    intro t ht
    have hlog : 0 < -log t := neg_pos.2 (log_neg ht.1 ht.2)
    convert (((hasDerivAt_log ht.1.ne').neg.rpow_const (p := k + 1) (.inl hlog.ne')).div_const
      (k + 1)).neg using 1
    simp only [Pi.neg_apply]
    field_simp
    ring_nf
  refine intervalIntegral.integrableOn_deriv_of_nonneg (g := G) (fun t ht ↦ ?_)
    (fun t ht ↦ hderiv t ⟨ht.1, ht.2.trans hc⟩) fun t ht ↦ ?_
  · rcases ht.1.eq_or_lt with rfl | ht₀
    · refine (continuousWithinAt_Ioi_iff_Ici.1 ?_).mono Icc_subset_Ici_self
      have h : Tendsto G (𝓝[>] 0) (𝓝 (-(0 / (k + 1)))) :=
        (((tendsto_rpow_neg_atTop (y := -(k + 1)) (by linarith)).comp
          (tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero)).div_const (k + 1)).neg.congr
          fun t ↦ by simp [G]
      simpa [ContinuousWithinAt, G, zero_rpow hk₁] using h
    · exact (hderiv t ⟨ht₀, ht.2.trans_lt hc⟩).continuousAt.continuousWithinAt
  · have hlog : 0 < -log t := neg_pos.2 (log_neg ht.1 (ht.2.trans hc))
    have := ht.1
    positivity

/-- `t ^ a * |log t| ^ k * exp (u t)` is integrable at `atTop` when `a < -1` and `u` is
eventually bounded above. The power of the logarithm is absorbed by `t ^ ε` for
`ε = (-1 - a) / 2`. -/
theorem integrableAtFilter_powExp_atTop_of_lt (hum : Measurable u) (ha : a < -1)
    (hu : IsBoundedUnder (· ≤ ·) atTop u) : IntegrableAtFilter (powExp a k u) atTop := by
  have hl : ∀ᶠ t : ℝ in atTop, 0 < t := eventually_gt_atTop 0
  have hε : 0 < (-1 - a) / 2 := by linarith
  exact ((isBigO_powExp_of_isBigO_abs_log hl (isBigO_abs_log_rpow_atTop k hε)).trans
    (isBigO_powExp_rpow hl hu)).integrableAtFilter (stronglyMeasurableAtFilter_powExp hum a k)
    (integrableAtFilter_rpow_atTop_iff.2 (by linarith))

/-- `t ^ a * |log t| ^ k * exp (u t)` is integrable at `atTop` when `a = -1`, `k < -1` and `u` is
eventually bounded above, by `integrableOn_Ioi_inv_mul_log_rpow`. -/
theorem integrableAtFilter_powExp_atTop_of_log_lt (hum : Measurable u) (ha : a = -1)
    (hk : k < -1) (hu : IsBoundedUnder (· ≤ ·) atTop u) :
    IntegrableAtFilter (powExp a k u) atTop := by
  subst ha
  have hl : ∀ᶠ t : ℝ in atTop, 0 < t := eventually_gt_atTop 0
  refine (isBigO_powExp_powExp (w := 0) hl (hu.mono_le <| .of_forall fun t ↦ by simp))
    |>.integrableAtFilter (stronglyMeasurableAtFilter_powExp hum _ k) ⟨Ioi 2, Ioi_mem_atTop 2,
      (integrableOn_Ioi_inv_mul_log_rpow hk one_lt_two).congr_fun (fun t ht ↦ ?_)
        measurableSet_Ioi⟩
  have : 0 ≤ log t := log_nonneg (by linarith [mem_Ioi.1 ht])
  simp [powExp, abs_of_nonneg this, rpow_neg_one]

/-- `t ^ a * |log t| ^ k * exp (u t)` is integrable at `atTop` when `u t - c * t ^ p` is
eventually bounded above for some `c < 0` and `0 < p`. This covers `exp (-b * t)`, Gaussians and
`exp (-√t)`. -/
theorem integrableAtFilter_powExp_atTop_of_mul_rpow (hum : Measurable u) {c : ℝ} (hc : c < 0)
    {p : ℝ} (hp : 0 < p) (hu : IsBoundedUnder (· ≤ ·) atTop fun t ↦ u t - c * t ^ p) :
    IntegrableAtFilter (powExp a k u) atTop := by
  have hl : ∀ᶠ t : ℝ in atTop, 0 < t := eventually_gt_atTop 0
  have hlim := tendsto_powExp_mul_rpow hl hc hp.ne' (tendsto_rpow_atTop hp) (a + 1 + 2)
  have h : powExp a k u =O[atTop] powExp (-2) 0 0 := by
    refine (isBigO_powExp_of_isBigO_abs_log hl (isBigO_abs_log_rpow_atTop k one_pos)).trans <|
      (isBigO_powExp_powExp hl hu).trans <| ((hlim.isBigO_one ℝ).mul
        (isBigO_refl (powExp (-2) 0 0) _)).congr' (hl.mono fun t ht ↦ ?_) (.of_forall fun t ↦ ?_)
    · simp only [powExp, Pi.zero_apply, exp_zero, rpow_zero, mul_one]
      rw [mul_right_comm, ← rpow_add ht, add_neg_cancel_right]
    · simp
  exact h.integrableAtFilter (stronglyMeasurableAtFilter_powExp hum a k)
    (integrableAtFilter_powExp_atTop_of_lt measurable_const (by norm_num) isBoundedUnder_const)

/-- `t ^ a * |log t| ^ k * exp (u t)` is integrable at `𝓝[>] 0` when `-1 < a` and `u` is
eventually bounded above. The power of the logarithm is absorbed by `t ^ ε` for
`ε = (-1 - a) / 2`. -/
theorem integrableAtFilter_powExp_nhdsGT_of_lt (hum : Measurable u) (ha : -1 < a)
    (hu : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) u) : IntegrableAtFilter (powExp a k u) (𝓝[>] 0) := by
  have hl : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hε : (-1 - a) / 2 < 0 := by linarith
  exact ((isBigO_powExp_of_isBigO_abs_log hl (isBigO_abs_log_rpow_nhdsGT k hε)).trans
    (isBigO_powExp_rpow hl hu)).integrableAtFilter (stronglyMeasurableAtFilter_powExp hum a k)
    ⟨_, Ioo_mem_nhdsGT one_pos, (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2
      (by linarith)⟩

/-- `t ^ a * |log t| ^ k * exp (u t)` is integrable at `𝓝[>] 0` when `a = -1`, `k < -1` and `u`
is eventually bounded above, by `integrableOn_Ioc_inv_mul_neg_log_rpow`. -/
theorem integrableAtFilter_powExp_nhdsGT_of_log_lt (hum : Measurable u) (ha : a = -1)
    (hk : k < -1) (hu : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) u) :
    IntegrableAtFilter (powExp a k u) (𝓝[>] 0) := by
  subst ha
  have hl : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  refine (isBigO_powExp_powExp (w := 0) hl (hu.mono_le <| .of_forall fun t ↦ by simp))
    |>.integrableAtFilter (stronglyMeasurableAtFilter_powExp hum _ k) ⟨Ioc 0 (1 / 2),
      Ioc_mem_nhdsGT (by norm_num), (integrableOn_Ioc_inv_mul_neg_log_rpow hk
        (by norm_num)).congr_fun (fun t ht ↦ ?_) measurableSet_Ioc⟩
  have : log t < 0 := log_neg ht.1 (by linarith [ht.2])
  simp [powExp, abs_of_neg this, rpow_neg_one]

/-- `t ^ a * |log t| ^ k * exp (u t)` is integrable at `𝓝[>] 0` when `u t - c * t ^ p` is
eventually bounded above for some `c < 0` and `p < 0`. This covers `exp (-b / t)` and
`exp (-1 / √t)`. -/
theorem integrableAtFilter_powExp_nhdsGT_of_mul_rpow (hum : Measurable u) {c : ℝ} (hc : c < 0)
    {p : ℝ} (hp : p < 0) (hu : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) fun t ↦ u t - c * t ^ p) :
    IntegrableAtFilter (powExp a k u) (𝓝[>] 0) := by
  have hl : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have h : powExp a k u =O[𝓝[>] 0] powExp 0 0 0 :=
    (isBigO_powExp_of_isBigO_abs_log hl (isBigO_abs_log_rpow_nhdsGT k neg_one_lt_zero)).trans <|
      (isBigO_powExp_powExp hl hu).trans <| ((tendsto_powExp_mul_rpow hl hc hp.ne
        (tendsto_rpow_neg_nhdsGT_zero hp) (a + -1)).isBigO_one ℝ).congr_right fun t ↦ by
          simp [powExp]
  exact h.integrableAtFilter (stronglyMeasurableAtFilter_powExp hum a k)
    (integrableAtFilter_powExp_nhdsGT_of_lt measurable_const (by norm_num) isBoundedUnder_const)

end Decision

section Boundedness

/-- `t ^ a * |log t| ^ k` is `O(1)` at `atTop` when `a ≤ 0` and `k ≤ 0`: both factors are at most
`1` for `t ≥ e`. -/
theorem isBigO_powExp_zero_one_atTop (ha : a ≤ 0) (hk : k ≤ 0) :
    powExp a k 0 =O[atTop] fun _ ↦ (1 : ℝ) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (rexp 1)] with t ht
  have ht1 : 1 ≤ t := (one_le_exp zero_le_one).trans ht
  have hlog : 1 ≤ |log t| := by
    rw [abs_of_nonneg (log_nonneg ht1)]
    exact (le_log_iff_exp_le (by linarith)).2 ht
  rw [norm_of_nonneg (powExp_nonneg (by linarith)), norm_one, one_mul, powExp]
  simp only [Pi.zero_apply, exp_zero, mul_one]
  exact (mul_le_mul (rpow_le_one_of_one_le_of_nonpos ht1 ha)
    (rpow_le_one_of_one_le_of_nonpos hlog hk) (by positivity) zero_le_one).trans_eq (one_mul 1)

/-- `t ^ a * |log t| ^ k` is `O(1)` at `𝓝[>] 0` when `0 ≤ a` and `k ≤ 0`: both factors are at most
`1` for `0 < t < e⁻¹`. -/
theorem isBigO_powExp_zero_one_nhdsGT (ha : 0 ≤ a) (hk : k ≤ 0) :
    powExp a k 0 =O[𝓝[>] 0] fun _ ↦ (1 : ℝ) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT (exp_pos (-1))] with t ht
  have hlog : 1 ≤ |log t| := by
    have : log t ≤ -1 := (log_le_iff_le_exp ht.1).2 ht.2.le
    rw [abs_of_neg (by linarith)]
    linarith
  have ht1 : t ≤ 1 := ht.2.le.trans (exp_le_one_iff.2 (by norm_num))
  rw [norm_of_nonneg (powExp_nonneg ht.1.le), norm_one, one_mul, powExp]
  simp only [Pi.zero_apply, exp_zero, mul_one]
  exact (mul_le_mul (rpow_le_one ht.1.le ht1 ha) (rpow_le_one_of_one_le_of_nonpos hlog hk)
    (by positivity) zero_le_one).trans_eq (one_mul 1)

/-- `t ^ a * |log t| ^ k * exp (u t)` is `O(1)` at `atTop` when `a ≤ 0`, `k ≤ 0` and `u` is
eventually bounded above. -/
theorem isBigO_powExp_one_atTop_of_le (ha : a ≤ 0) (hk : k ≤ 0)
    (hu : IsBoundedUnder (· ≤ ·) atTop u) : powExp a k u =O[atTop] fun _ ↦ (1 : ℝ) :=
  (isBigO_powExp_powExp (w := 0) (eventually_gt_atTop 0)
    (hu.mono_le <| .of_forall fun t ↦ by simp)).trans (isBigO_powExp_zero_one_atTop ha hk)

/-- `t ^ a * |log t| ^ k * exp (u t)` is `O(1)` at `atTop` when `a < 0` and `u` is eventually
bounded above. The power of the logarithm is absorbed by `t ^ ε` for `ε = -a / 2`. -/
theorem isBigO_powExp_one_atTop_of_lt (ha : a < 0) (hu : IsBoundedUnder (· ≤ ·) atTop u) :
    powExp a k u =O[atTop] fun _ ↦ (1 : ℝ) :=
  (isBigO_powExp_of_isBigO_abs_log (eventually_gt_atTop 0)
    (isBigO_abs_log_rpow_atTop k (ε := -a / 2) (by linarith))).trans
    (isBigO_powExp_one_atTop_of_le (by linarith) le_rfl hu)

/-- `t ^ a * |log t| ^ k * exp (u t)` is `O(1)` at `atTop` when `u t - c * t ^ p` is eventually
bounded above for some `c < 0` and `0 < p`. -/
theorem isBigO_powExp_one_atTop_of_mul_rpow {c : ℝ} (hc : c < 0) {p : ℝ} (hp : 0 < p)
    (hu : IsBoundedUnder (· ≤ ·) atTop fun t ↦ u t - c * t ^ p) :
    powExp a k u =O[atTop] fun _ ↦ (1 : ℝ) := by
  have hl : ∀ᶠ t : ℝ in atTop, 0 < t := eventually_gt_atTop 0
  exact (isBigO_powExp_of_isBigO_abs_log hl (isBigO_abs_log_rpow_atTop k one_pos)).trans <|
    (isBigO_powExp_powExp hl hu).trans <|
      (tendsto_powExp_mul_rpow hl hc hp.ne' (tendsto_rpow_atTop hp) _).isBigO_one ℝ

/-- `t ^ a * |log t| ^ k * exp (u t)` is `O(1)` at `𝓝[>] 0` when `0 ≤ a`, `k ≤ 0` and `u` is
eventually bounded above. -/
theorem isBigO_powExp_one_nhdsGT_of_le (ha : 0 ≤ a) (hk : k ≤ 0)
    (hu : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) u) : powExp a k u =O[𝓝[>] 0] fun _ ↦ (1 : ℝ) :=
  (isBigO_powExp_powExp (w := 0) self_mem_nhdsWithin
    (hu.mono_le <| .of_forall fun t ↦ by simp)).trans (isBigO_powExp_zero_one_nhdsGT ha hk)

/-- `t ^ a * |log t| ^ k * exp (u t)` is `O(1)` at `𝓝[>] 0` when `0 < a` and `u` is eventually
bounded above. The power of the logarithm is absorbed by `t ^ ε` for `ε = -a / 2`. -/
theorem isBigO_powExp_one_nhdsGT_of_lt (ha : 0 < a) (hu : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) u) :
    powExp a k u =O[𝓝[>] 0] fun _ ↦ (1 : ℝ) :=
  (isBigO_powExp_of_isBigO_abs_log self_mem_nhdsWithin
    (isBigO_abs_log_rpow_nhdsGT k (ε := -a / 2) (by linarith))).trans
    (isBigO_powExp_one_nhdsGT_of_le (by linarith) le_rfl hu)

/-- `t ^ a * |log t| ^ k * exp (u t)` is `O(1)` at `𝓝[>] 0` when `u t - c * t ^ p` is eventually
bounded above for some `c < 0` and `p < 0`. -/
theorem isBigO_powExp_one_nhdsGT_of_mul_rpow {c : ℝ} (hc : c < 0) {p : ℝ} (hp : p < 0)
    (hu : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) fun t ↦ u t - c * t ^ p) :
    powExp a k u =O[𝓝[>] 0] fun _ ↦ (1 : ℝ) := by
  have hl : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  exact (isBigO_powExp_of_isBigO_abs_log hl
    (isBigO_abs_log_rpow_nhdsGT k neg_one_lt_zero)).trans <|
    (isBigO_powExp_powExp hl hu).trans <|
      (tendsto_powExp_mul_rpow hl hc hp.ne (tendsto_rpow_neg_nhdsGT_zero hp) _).isBigO_one ℝ

end Boundedness

section Dominance

/-- `powExp b j v` is eventually the product of `powExp (b - a) (j - k) (v - u)` and
`powExp a k u`, along a filter of positive reals along which `|log t| → ∞`. -/
theorem powExp_eventuallyEq_mul (hl : ∀ᶠ t in l, 0 < t)
    (hlog : Tendsto (fun t ↦ |log t|) l atTop) :
    powExp b j v =ᶠ[l] fun t ↦ powExp (b - a) (j - k) (fun t ↦ v t - u t) t * powExp a k u t := by
  filter_upwards [powExp_mul_powExp_eventuallyEq (a := b - a) (k := j - k)
    (u := fun t ↦ v t - u t) (b := a) (j := k) (v := u) hl hlog] with t ht
  simpa [powExp] using ht.symm

/-- If `powExp (b - a) (j - k) (v - u) → 0` along a filter of positive reals along which
`|log t| → ∞`, then `powExp b j v = o(powExp a k u)`, by `powExp_eventuallyEq_mul`. -/
theorem isLittleO_powExp_of_tendsto (hl : ∀ᶠ t in l, 0 < t)
    (hlog : Tendsto (fun t ↦ |log t|) l atTop)
    (h : Tendsto (powExp (b - a) (j - k) fun t ↦ v t - u t) l (𝓝 0)) :
    powExp b j v =o[l] powExp a k u :=
  (((isLittleO_one_iff ℝ).2 h).mul_isBigO (isBigO_refl (powExp a k u) l)).congr'
    (powExp_eventuallyEq_mul hl hlog).symm (.of_forall fun _ ↦ one_mul _)

/-- At `atTop`, `powExp b j v = o(powExp a k u)` if `b < a` and `v - u` is eventually bounded
above. -/
theorem isLittleO_powExp_atTop_of_lt (hba : b < a)
    (h : IsBoundedUnder (· ≤ ·) atTop fun t ↦ v t - u t) :
    powExp b j v =o[atTop] (powExp a k u) := by
  have hl : ∀ᶠ t : ℝ in atTop, 0 < t := eventually_gt_atTop 0
  have hε : 0 < (a - b) / 2 := by linarith
  refine isLittleO_powExp_of_tendsto hl (tendsto_abs_atTop_atTop.comp tendsto_log_atTop) <|
    ((isBigO_powExp_of_isBigO_abs_log hl (isBigO_abs_log_rpow_atTop (j - k) hε)).trans
      (isBigO_powExp_rpow hl h)).trans_tendsto <|
    (tendsto_rpow_neg_atTop hε).congr fun t ↦ by ring_nf

/-- At `atTop`, `powExp b j v = o(powExp a k u)` if `v t - u t - c * t ^ p` is eventually bounded
above for some `c < 0` and `0 < p`. -/
theorem isLittleO_powExp_atTop_of_mul_rpow {c : ℝ} (hc : c < 0) {p : ℝ} (hp : 0 < p)
    (h : IsBoundedUnder (· ≤ ·) atTop fun t ↦ v t - u t - c * t ^ p) :
    powExp b j v =o[atTop] (powExp a k u) := by
  have hl : ∀ᶠ t : ℝ in atTop, 0 < t := eventually_gt_atTop 0
  exact isLittleO_powExp_of_tendsto hl (tendsto_abs_atTop_atTop.comp tendsto_log_atTop) <|
    ((isBigO_powExp_of_isBigO_abs_log hl (isBigO_abs_log_rpow_atTop (j - k) one_pos)).trans
      (isBigO_powExp_powExp hl h)).trans_tendsto <|
    tendsto_powExp_mul_rpow hl hc hp.ne' (tendsto_rpow_atTop hp) _

/-- At `𝓝[>] 0`, `powExp b j v = o(powExp a k u)` if `a < b` and `v - u` is eventually bounded
above. -/
theorem isLittleO_powExp_nhdsGT_of_lt (hab : a < b)
    (h : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) fun t ↦ v t - u t) :
    powExp b j v =o[𝓝[>] 0] (powExp a k u) := by
  have hl : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hε : (a - b) / 2 < 0 := by linarith
  have hpos : 0 < b - a + (a - b) / 2 := by linarith
  refine isLittleO_powExp_of_tendsto hl (tendsto_abs_atBot_atTop.comp tendsto_log_nhdsGT_zero) <|
    ((isBigO_powExp_of_isBigO_abs_log hl (isBigO_abs_log_rpow_nhdsGT (j - k) hε)).trans
      (isBigO_powExp_rpow hl h)).trans_tendsto ?_
  simpa [zero_rpow hpos.ne'] using
    ((continuousAt_rpow_const 0 _ (.inr hpos.le)).tendsto.mono_left nhdsWithin_le_nhds)

/-- At `𝓝[>] 0`, `powExp b j v = o(powExp a k u)` if `v t - u t - c * t ^ p` is eventually bounded
above for some `c < 0` and `p < 0`. -/
theorem isLittleO_powExp_nhdsGT_of_mul_rpow {c : ℝ} (hc : c < 0) {p : ℝ} (hp : p < 0)
    (h : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) fun t ↦ v t - u t - c * t ^ p) :
    powExp b j v =o[𝓝[>] 0] (powExp a k u) := by
  have hl : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  exact isLittleO_powExp_of_tendsto hl (tendsto_abs_atBot_atTop.comp tendsto_log_nhdsGT_zero) <|
    ((isBigO_powExp_of_isBigO_abs_log hl
      (isBigO_abs_log_rpow_nhdsGT (j - k) neg_one_lt_zero)).trans
      (isBigO_powExp_powExp hl h)).trans_tendsto <|
    tendsto_powExp_mul_rpow hl hc hp.ne (tendsto_rpow_neg_nhdsGT_zero hp) _

/-- Along a filter of positive reals along which `|log t| → ∞`, `powExp b j v = o(powExp a k u)`
if `b = a`, `j < k` and `v - u` is eventually bounded above: `powExp 0 (j - k) (v - u)` is
`O(|log t| ^ (j - k))`, which tends to `0`. -/
theorem isLittleO_powExp_of_log_lt (hl : ∀ᶠ t in l, 0 < t)
    (hlog : Tendsto (fun t ↦ |log t|) l atTop) (hab : b = a) (hjk : j < k)
    (h : IsBoundedUnder (· ≤ ·) l fun t ↦ v t - u t) : powExp b j v =o[l] powExp a k u := by
  subst hab
  refine isLittleO_powExp_of_tendsto hl hlog <|
    (isBigO_powExp_powExp (w := 0) hl (h.mono_le <| .of_forall fun t ↦ by simp)).trans_tendsto <|
    ((tendsto_rpow_neg_atTop (y := k - j) (by linarith)).comp hlog).congr fun t ↦ ?_
  simp [powExp]

end Dominance

end Mathlib.Tactic.EndpointIntegrability
