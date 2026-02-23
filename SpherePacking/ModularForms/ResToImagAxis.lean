module
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.NumberTheory.ModularForms.QExpansion

public import SpherePacking.ModularForms.SlashActionAuxil
public import SpherePacking.ForMathlib.AtImInfty


/-!
# Polynomial decay on the imaginary axis

This file studies the restriction of functions `F : ℍ → ℂ` to the positive imaginary axis
`t ↦ F (I * t)` and proves polynomial decay results from exponential bounds at `atImInfty`.

## Main definitions
* `ResToImagAxis`
* `ResToImagAxis.Real`, `ResToImagAxis.Pos`, `ResToImagAxis.EventuallyPos`

## Main statements
* `tendsto_rpow_mul_resToImagAxis_of_isBigO_exp`
* `cuspForm_rpow_mul_resToImagAxis_tendsto_zero`
-/


open scoped Real Topology Manifold ModularForm MatrixGroups

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup ModularGroup Filter Asymptotics

/--
Restrict a function `F : ℍ → ℂ` to the positive imaginary axis, i.e. `t ↦ F (I * t)`.
If $t \le 0$, then `F (I * t)` is not defined, and we return `0` in that case.
-/
@[expose] public noncomputable def ResToImagAxis (F : ℍ → ℂ) : ℝ → ℂ :=
  fun t => if ht : 0 < t then F ⟨(I * t), by simp [ht]⟩ else 0

namespace Function

/-- Dot notation alias for `ResToImagAxis`. -/
@[expose] public noncomputable def resToImagAxis (F : ℍ → ℂ) : ℝ → ℂ := ResToImagAxis F

/-- The dot-notation definition `F.resToImagAxis` is `ResToImagAxis F`. -/
@[simp] public lemma resToImagAxis_eq_resToImagAxis (F : ℍ → ℂ) :
    F.resToImagAxis = ResToImagAxis F := rfl

/-- Unfold `F.resToImagAxis t` to `ResToImagAxis F t`. -/
@[simp] public lemma resToImagAxis_apply (F : ℍ → ℂ) (t : ℝ) :
    F.resToImagAxis t = ResToImagAxis F t := rfl

/--
If `F` is continuous on `ℍ`, then its restriction to the imaginary axis is continuous on `Ioi 0`.
-/
public lemma continuousOn_resToImagAxis_Ioi_of {F : ℍ → ℂ} (hF : Continuous F) :
    ContinuousOn F.resToImagAxis (Set.Ioi (0 : ℝ)) := by
  rw [continuousOn_iff_continuous_restrict]
  let z : Set.Ioi (0 : ℝ) → UpperHalfPlane :=
    fun t =>
      ⟨(Complex.I : ℂ) * (t : ℝ), by
        have ht : (0 : ℝ) < (t : ℝ) := t.property
        simpa [Complex.mul_im] using ht⟩
  have hz : Continuous z := by
    have hC : Continuous fun t : Set.Ioi (0 : ℝ) => (Complex.I : ℂ) * (t : ℝ) :=
      continuous_const.mul (Complex.continuous_ofReal.comp continuous_subtype_val)
    simpa [z] using hC.upperHalfPlaneMk fun t =>
      (by
        have ht : (0 : ℝ) < (t : ℝ) := t.property
        simpa [Complex.mul_im] using ht)
  refine (hF.comp hz).congr fun t => ?_
  have ht : (0 : ℝ) < (t : ℝ) := t.property
  simp [Set.restrict, ResToImagAxis, z, ht]

/-- A variant of `continuousOn_resToImagAxis_Ioi_of` on the closed ray `Ici 1`. -/
public lemma continuousOn_resToImagAxis_Ici_one_of {F : ℍ → ℂ} (hF : Continuous F) :
    ContinuousOn F.resToImagAxis (Set.Ici (1 : ℝ)) := by
  refine (continuousOn_resToImagAxis_Ioi_of (F := F) hF).mono ?_
  intro t ht
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht



/-- If `F z → l` as `im z → ∞`, then `F (I * t) → l` as `t → ∞`. -/
public lemma tendsto_resToImagAxis_atImInfty (F : ℍ → ℂ) (l : ℂ)
    (hF : Tendsto F UpperHalfPlane.atImInfty (𝓝 l)) :
    Tendsto (fun t : ℝ => F.resToImagAxis t) atTop (𝓝 l) := by
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  rcases (Filter.eventually_atImInfty).1 (by
    simpa [Metric.ball] using hF.eventually (Metric.ball_mem_nhds l hε)) with ⟨A, hA⟩
  refine (eventually_atTop.2 ⟨max A 1, ?_⟩)
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans ht)
  have hAt : A ≤ t := (le_max_left _ _).trans ht
  simpa [ResToImagAxis, ht0] using hA ⟨Complex.I * t, by simp [ht0]⟩
    (by simpa using hAt)

@[grind =] lemma resToImagAxis_im_add (F G : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    ((F + G).resToImagAxis t).im = (F.resToImagAxis t).im + (G.resToImagAxis t).im := by
  simp [ResToImagAxis, ht]

@[grind =] lemma resToImagAxis_im_mul (F G : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    ((F * G).resToImagAxis t).im =
      (F.resToImagAxis t).re * (G.resToImagAxis t).im +
        (F.resToImagAxis t).im * (G.resToImagAxis t).re := by
  simp [ResToImagAxis, ht, mul_im]

@[grind =] lemma resToImagAxis_im_smul (c : ℝ) (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    ((c • F).resToImagAxis t).im = c * (F.resToImagAxis t).im := by
  simp [ResToImagAxis, ht]

@[grind =] lemma resToImagAxis_re_add (F G : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    ((F + G).resToImagAxis t).re = (F.resToImagAxis t).re + (G.resToImagAxis t).re := by
  simp [ResToImagAxis, ht]

end Function

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is real-valued,
i.e. imaginary part is zero.
-/
@[expose] public noncomputable def ResToImagAxis.Real (F : ℍ → ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → (F.resToImagAxis t).im = 0

/--
Function $F : \mathbb{H} \to \mathbb{C}$ is real and positive on the imaginary axis.
-/
@[expose] public noncomputable def ResToImagAxis.Pos (F : ℍ → ℂ) : Prop :=
  ResToImagAxis.Real F ∧ ∀ t : ℝ, 0 < t → 0 < (F.resToImagAxis t).re

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is eventually
positive, i.e. there exists $t_0 > 0$ such that for all $t \ge t_0$, $F(it)$ is real and positive.
-/
@[expose] public noncomputable def ResToImagAxis.EventuallyPos (F : ℍ → ℂ) : Prop :=
  ResToImagAxis.Real F ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, t₀ ≤ t → 0 < (F.resToImagAxis t).re

/--
If `F` is complex-differentiable on `ℍ`, then `t ↦ F (I * t)` is real-differentiable for `t > 0`.
-/
public theorem ResToImagAxis.Differentiable (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (t : ℝ)
    (ht : 0 < t) : DifferentiableAt ℝ F.resToImagAxis t := by
  rw [Function.resToImagAxis_eq_resToImagAxis]
  have := hF ⟨Complex.I * t, by norm_num [Complex.I_re, ht]⟩
  rw [mdifferentiableAt_iff] at this
  have h_diff :
      DifferentiableAt ℝ (fun t : ℝ => F (ofComplex (Complex.I * t))) t := by
    convert this.restrictScalars ℝ |> DifferentiableAt.comp t <|
      DifferentiableAt.const_mul ofRealCLM.differentiableAt _ using 1
  refine h_diff.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with u hu
  simp [ResToImagAxis, hu, ofComplex_apply_of_im_pos]

/--
Restriction and slash action under S: $(F |_k S) (it) = (it)^{-k} * F(it)$
-/
public theorem ResToImagAxis.SlashActionS (F : ℍ → ℂ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    (F ∣[k] S).resToImagAxis t = (Complex.I) ^ (-k) * t ^ (-k) * F.resToImagAxis (1 / t) := by
  have ht' : 0 < (1 / t : ℝ) := one_div_pos.2 ht
  set z : ℍ := ⟨I * t, by simp [ht]⟩
  set z' : ℍ := ⟨I * (1 / t : ℝ), by simpa [ht']⟩
  have h : mk (-z)⁻¹ z.im_inv_neg_coe_pos = z' := by
    ext1
    simp [z, z', Complex.ofReal_inv, mul_comm]
  simp [Function.resToImagAxis, ResToImagAxis, ht, modular_slash_S_apply,
    mul_zpow I (t : ℂ) (-k), mul_assoc, mul_comm]

/-- The property `ResToImagAxis.Real` is closed under addition. -/
public theorem ResToImagAxis.Real.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F + G) := by
  intro t ht
  grind [hF t ht, hG t ht]

/-- The property `ResToImagAxis.Real` is closed under multiplication. -/
public theorem ResToImagAxis.Real.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F * G) := by
  intro t ht
  grind [hF t ht, hG t ht]

/-- The property `ResToImagAxis.Real` is closed under real scalar multiplication. -/
public theorem ResToImagAxis.Real.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Real F) :
    ResToImagAxis.Real (c • F) := by
  intro t ht
  grind [hF t ht]

/-- The property `ResToImagAxis.Real` is closed under negation. -/
public theorem ResToImagAxis.Real.neg {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) :
    ResToImagAxis.Real (-F) := by
  simpa using (ResToImagAxis.Real.smul (F := F) (c := (-1 : ℝ)) hF)

/-- The property `ResToImagAxis.Real` is closed under subtraction. -/
public theorem ResToImagAxis.Real.sub {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F - G) := by
  simpa [sub_eq_add_neg] using ResToImagAxis.Real.add hF (ResToImagAxis.Real.neg hG)

/-- The property `ResToImagAxis.Pos` is closed under addition. -/
public theorem ResToImagAxis.Pos.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F + G) := by
  rw [Pos]
  refine ⟨Real.add hF.1 hG.1, fun t ht ↦ ?_⟩
  grind [hF.2 t ht, hG.2 t ht]

/-- The property `ResToImagAxis.Pos` is closed under multiplication. -/
public theorem ResToImagAxis.Pos.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F * G) := by
  rw [Pos]
  refine ⟨Real.mul hF.1 hG.1, fun t ht ↦ ?_⟩
  have hFreal := hF.1 t ht
  have hGreal := hG.1 t ht
  have hFpos := hF.2 t ht
  have hGpos := hG.2 t ht
  simp [Function.resToImagAxis, ResToImagAxis, ht] at hFreal hGreal hFpos hGpos
  simpa [Function.resToImagAxis, ResToImagAxis, ht, mul_re, hFreal, hGreal] using
    mul_pos hFpos hGpos

/-- The property `ResToImagAxis.Pos` is closed under positive scalar multiplication. -/
public theorem ResToImagAxis.Pos.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Pos F)
    (hc : 0 < c) : ResToImagAxis.Pos (c • F) := by
  rw [Pos]
  refine ⟨Real.smul hF.1, fun t ht ↦ ?_⟩
  have hF' : 0 < (ResToImagAxis F t).re := by
    simpa [ResToImagAxis, ht] using hF.2 t ht
  have hmul : (ResToImagAxis (c • F) t).re = c * (ResToImagAxis F t).re := by
    simp [ResToImagAxis, ht]
  simpa [hmul] using mul_pos hc hF'

theorem ResToImagAxis.EventuallyPos.add {F G : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (hG : ResToImagAxis.EventuallyPos G) :
    ResToImagAxis.EventuallyPos (F + G) := by
  rw [EventuallyPos]
  rcases hF with ⟨hFreal, ⟨tF, hF0, hFpos⟩⟩
  rcases hG with ⟨hGreal, ⟨tG, hG0, hGpos⟩⟩
  refine ⟨ResToImagAxis.Real.add hFreal hGreal, ⟨max tF tG, by positivity, ?_⟩⟩
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le hF0 ((le_max_left _ _).trans ht)
  simpa [ResToImagAxis, htpos] using
    add_pos (hFpos t ((le_max_left _ _).trans ht)) (hGpos t ((le_max_right _ _).trans ht))






/--
If `F : ℍ → ℂ` is `O(exp(-c * im τ))` at `atImInfty` for some `c > 0`, then
the restriction to the imaginary axis `t ↦ F(it)` is `O(exp(-c * t))` at `atTop`.
-/
lemma isBigO_resToImagAxis_of_isBigO_atImInfty {F : ℍ → ℂ} {c : ℝ}
    (hF : F =O[atImInfty] fun τ => Real.exp (-c * τ.im)) :
    F.resToImagAxis =O[atTop] fun t => Real.exp (-c * t) := by
  rw [Asymptotics.isBigO_iff] at hF ⊢
  rcases hF with ⟨C, hC⟩
  rcases (Filter.eventually_atImInfty).1 hC with ⟨A, hA⟩
  refine ⟨C, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (max A 1)] with t ht
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos (le_of_max_le_right ht)
  simpa [ResToImagAxis, ht_pos] using
    hA ⟨Complex.I * t, by simp [ht_pos]⟩ (by simpa using le_of_max_le_left ht)

/--
The analytic kernel: if `g : ℝ → ℂ` is eventually bounded by `C * exp(-b * t)` for some
`b > 0`, then `t^s * g(t) → 0` as `t → ∞` for any real power `s`.

This follows from the fact that `t^s * exp(-b * t) → 0` (mathlib's
`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`) combined with the big-O transfer lemma.
-/
lemma tendsto_rpow_mul_of_isBigO_exp {g : ℝ → ℂ} {s b : ℝ} (hb : 0 < b)
    (hg : g =O[atTop] fun t => rexp (-b * t)) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (s : ℂ) * g t) atTop (𝓝 0) := by
  refine ((isBigO_refl _ _).mul (Complex.isBigO_ofReal_right.mpr hg)).trans_tendsto ?_
  refine (tendsto_ofReal_iff.mpr (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt ht)]

/--
If `F : ℍ → ℂ` is `O(exp(-c * im τ))` at `atImInfty` for some `c > 0`, then
`t^s * F(it) → 0` as `t → ∞` for any real power `s`.
-/
theorem tendsto_rpow_mul_resToImagAxis_of_isBigO_exp {F : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hF : F =O[atImInfty] fun τ => rexp (-c * τ.im)) (s : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (s : ℂ) * F.resToImagAxis t) atTop (𝓝 0) :=
  tendsto_rpow_mul_of_isBigO_exp hc (isBigO_resToImagAxis_of_isBigO_atImInfty hF)



/-!
## Fourier expansion approach for polynomial decay

This section provides an alternative approach to polynomial decay that works directly from
Fourier expansions. If `F` has a Fourier expansion `∑_{m≥0} a_m exp(2πi(m+n₀)z)` with `n₀ > 0`,
then `F = O(exp(-2π n₀ · im z))` at `atImInfty`, which gives `t^s * F(it) → 0`.

This is useful for functions with q-expansions starting at a positive index (like `(E₂E₄ - E₆)²`).
-/

/--
If `F` has a Fourier expansion `∑_{m≥0} a_m exp(2πi(m+n₀)z)` with `n₀ > 0`,
and the coefficients are absolutely summable at height `im z = c`,
then `F = O(exp(-2π n₀ · im z))` at `atImInfty`.

The key bound is: for `im z ≥ c`,
  `‖F(z)‖ ≤ (∑_m ‖a_m‖ · exp(-2π c m)) · exp(-2π n₀ · im z)`
-/
public lemma isBigO_atImInfty_of_fourier_shift
    {F : ℍ → ℂ} {a : ℕ → ℂ} {n₀ : ℕ} {c : ℝ}
    (hF : ∀ z : ℍ, F z =
      ∑' m : ℕ, a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * (z : ℂ)))
    (ha : Summable (fun m : ℕ => ‖a m‖ * rexp (-(2 * π * c) * (m : ℝ)))) :
    F =O[atImInfty] fun z : ℍ => rexp (-(2 * π * (n₀ : ℝ)) * z.im) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨∑' m, ‖a m‖ * rexp (-(2 * π * c) * m), ?_⟩
  rw [Filter.eventually_atImInfty]
  refine ⟨c, fun z hz => ?_⟩
  rw [hF z, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
  -- Real part of 2πi(m+n₀)z is -2π(m+n₀)·im z
  have hexp_re m : (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z).re = -(2 * π) * (m + n₀) * z.im := by
    simp only [Nat.cast_add, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
      Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, add_re, natCast_re,
      add_im, natCast_im, coe_re, zero_add, coe_im, zero_sub, neg_mul]
  -- Key bound: for y ≥ c, exp(-(2π)(m+n₀)y) ≤ exp(-(2πc)m) * exp(-(2πc)n₀)
  have hexp_bound (m : ℕ) :
      rexp (-(2 * π) * (↑m + ↑n₀) * z.im) ≤
        rexp (-(2 * π * c) * m) * rexp (-(2 * π * c) * n₀) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have _ : (↑m + ↑n₀) * z.im ≥ (↑m + ↑n₀) * c := by nlinarith
    nlinarith [Real.pi_pos, (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
      (Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀), z.im_pos]
  -- Summability of norms
  have hsum_norms : Summable fun m => ‖a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z)‖ := by
    refine .of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      (ha.mul_right (rexp (-(2 * π * c) * n₀)))
    simp only [norm_mul, norm_exp, hexp_re]
    calc ‖a m‖ * rexp (-(2 * π) * (↑m + ↑n₀) * z.im)
        ≤ ‖a m‖ * (rexp (-(2 * π * c) * m) * rexp (-(2 * π * c) * n₀)) :=
          mul_le_mul_of_nonneg_left (hexp_bound m) (norm_nonneg _)
      _ = ‖a m‖ * rexp (-(2 * π * c) * m) * rexp (-(2 * π * c) * n₀) := by ring
  have hsum_norms' : Summable fun m => ‖a m‖ * rexp (-(2 * π) * (m + n₀) * z.im) := by
    convert hsum_norms with m; rw [norm_mul, norm_exp, hexp_re]
  -- Main calculation
  calc ‖∑' m, a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z)‖
      ≤ ∑' m, ‖a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z)‖ :=
        norm_tsum_le_tsum_norm hsum_norms
    _ = ∑' m, ‖a m‖ * rexp (-(2 * π) * (m + n₀) * z.im) := by
        simp only [norm_mul, norm_exp, hexp_re]
    _ ≤ ∑' m, ‖a m‖ * rexp (-(2 * π * c) * m) * rexp (-(2 * π) * n₀ * z.im) := by
        refine Summable.tsum_le_tsum (fun m => ?_) hsum_norms'
          (ha.mul_right (rexp (-(2 * π) * n₀ * z.im)))
        have hsplit : rexp (-(2 * π) * (↑m + ↑n₀) * z.im) =
            rexp (-(2 * π) * m * z.im) * rexp (-(2 * π) * n₀ * z.im) := by
          rw [← Real.exp_add]; ring_nf
        have hexp_m : rexp (-(2 * π) * m * z.im) ≤ rexp (-(2 * π * c) * m) := by
          rw [Real.exp_le_exp]
          have key : (m : ℝ) * z.im ≥ m * c := by nlinarith
          nlinarith [Real.pi_pos, (Nat.cast_nonneg m : (0 : ℝ) ≤ m), z.im_pos]
        calc ‖a m‖ * rexp (-(2 * π) * (↑m + ↑n₀) * z.im)
            = ‖a m‖ * rexp (-(2 * π) * m * z.im) * rexp (-(2 * π) * n₀ * z.im) := by
              rw [hsplit]; ring
          _ ≤ ‖a m‖ * rexp (-(2 * π * c) * m) * rexp (-(2 * π) * n₀ * z.im) := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
              exact mul_le_mul_of_nonneg_left hexp_m (norm_nonneg _)
    _ = (∑' m, ‖a m‖ * rexp (-(2 * π * c) * m)) * rexp (-(2 * π) * n₀ * z.im) := tsum_mul_right
    _ = _ := by ring_nf

/--
If `F` has a Fourier expansion starting at index `n₀ > 0` with absolutely summable coefficients
at height `c > 0`, then `t^s * F(it) → 0` as `t → ∞` for any real power `s`.

This converts a Fourier expansion representation directly into polynomial decay on the
imaginary axis.
-/
public theorem tendsto_rpow_mul_resToImagAxis_of_fourier_shift
    {F : ℍ → ℂ} {a : ℕ → ℂ} {n₀ : ℕ} {c : ℝ} (hn₀ : 0 < n₀)
    (hF : ∀ z : ℍ, F z =
      ∑' m : ℕ, a m * Complex.exp (2 * π * Complex.I * ((m + n₀ : ℕ) : ℂ) * (z : ℂ)))
    (ha : Summable (fun m : ℕ => ‖a m‖ * rexp (-(2 * π * c) * (m : ℝ)))) (s : ℝ) :
    Tendsto (fun t : ℝ => t ^ (s : ℂ) * F.resToImagAxis t) atTop (𝓝 0) :=
  tendsto_rpow_mul_resToImagAxis_of_isBigO_exp (F := F) (c := 2 * π * (n₀ : ℝ)) (s := s)
    (by positivity [hn₀]) (isBigO_atImInfty_of_fourier_shift hF ha)
