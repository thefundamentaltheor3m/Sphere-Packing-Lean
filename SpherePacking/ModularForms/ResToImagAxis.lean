import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.NumberTheory.ModularForms.QExpansion

import SpherePacking.ModularForms.SlashActionAuxil
import SpherePacking.ForMathlib.AtImInfty

open UpperHalfPlane hiding I

open Real Complex ContinuousMap Matrix CongruenceSubgroup ModularGroup

open scoped Interval Real Topology Manifold ModularForm MatrixGroups

/--
Restrict a function `F : ℍ → ℂ` to the positive imaginary axis, i.e. `t ↦ F (I * t)`.
If $t \le 0$, then `F (I * t)` is not defined, and we return `0` in that case.
-/
noncomputable def ResToImagAxis (F : ℍ → ℂ) : ℝ → ℂ :=
  fun t => if ht : 0 < t then F ⟨(Complex.I * t), by simp [ht]⟩ else 0

namespace Function

/-- Dot notation alias for `ResToImagAxis`. -/
noncomputable def resToImagAxis (F : ℍ → ℂ) : ℝ → ℂ :=
  ResToImagAxis F

@[simp] lemma resToImagAxis_eq_resToImagAxis (F : ℍ → ℂ) :
    F.resToImagAxis = ResToImagAxis F := rfl

@[simp] lemma resToImagAxis_apply (F : ℍ → ℂ) (t : ℝ) :
    F.resToImagAxis t = ResToImagAxis F t := rfl

end Function

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is real-valued,
i.e. imaginary part is zero.
-/
noncomputable def ResToImagAxis.Real (F : ℍ → ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → (F.resToImagAxis t).im = 0

/--
Function $F : \mathbb{H} \to \mathbb{C}$ is real and positive on the imaginary axis.
-/
noncomputable def ResToImagAxis.Pos (F : ℍ → ℂ) : Prop :=
  ResToImagAxis.Real F ∧ ∀ t : ℝ, 0 < t → 0 < (F.resToImagAxis t).re

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is eventually
positive, i.e. there exists $t_0 > 0$ such that for all $t \ge t_0$, $F(it)$ is real and positive.
-/
noncomputable def ResToImagAxis.EventuallyPos (F : ℍ → ℂ) : Prop :=
  ResToImagAxis.Real F ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, t₀ ≤ t → 0 < (F.resToImagAxis t).re

theorem ResToImagAxis.Differentiable (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (t : ℝ)
    (ht : 0 < t) : DifferentiableAt ℝ F.resToImagAxis t := by
  rw [Function.resToImagAxis_eq_resToImagAxis]
  have := hF ⟨Complex.I * t, by norm_num [Complex.I_re, ht]⟩
  rw [mdifferentiableAt_iff] at this
  have h_diff :
      DifferentiableAt ℝ (fun t : ℝ => F (ofComplex (Complex.I * t))) t := by
    convert this.restrictScalars ℝ |> DifferentiableAt.comp t <|
      DifferentiableAt.const_mul ofRealCLM.differentiableAt _ using 1
  apply h_diff.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with t ht
  simp_all only [coe_mk_subtype, ResToImagAxis, ↓reduceDIte]
  rw [ofComplex_apply_of_im_pos]

/--
Restriction and slash action under S: $(F |_k S) (it) = (it)^{-k} * F(it)$
-/
theorem ResToImagAxis.SlashActionS (F : ℍ → ℂ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    (F ∣[k] S).resToImagAxis t = (Complex.I) ^ (-k) * t ^ (-k) * F.resToImagAxis (1 / t) := by
  set z : ℍ := ⟨I * t, by simp [ht]⟩ with hzdef
  set z' : ℍ := ⟨I * (1 / t : ℝ), by simpa [one_div_pos.2 ht]⟩ with hz'def
  have h : mk (-z)⁻¹ z.im_inv_neg_coe_pos = z' := UpperHalfPlane.ext (by simp [hzdef, hz'def, mul_comm])
  simpa [ResToImagAxis, ht, hz'def] using (by
    rw [modular_slash_S_apply, h]; simp [hzdef, mul_zpow I (t : ℂ) (-k), mul_comm (F z')] :
    (F ∣[k] S) z = I ^ (-k) * t ^ (-k) * F z')

/--
Realenss, positivity and essential positivity are closed under the addition and multiplication.
-/
theorem ResToImagAxis.Real.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F + G) := by
  intro t ht
  have hFreal := hF t ht
  have hGreal := hG t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal
  simp [ResToImagAxis, ht, hFreal, hGreal]

theorem ResToImagAxis.Real.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F * G) := by
  intro t ht
  have hFreal := hF t ht
  have hGreal := hG t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal
  simp [ResToImagAxis, ht, hFreal, hGreal]

theorem ResToImagAxis.Real.hmul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Real F) :
    ResToImagAxis.Real (c • F) := by
  intro t ht
  have hFreal := hF t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal
  simp [ResToImagAxis, ht, hFreal]

theorem ResToImagAxis.Pos.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F + G) := by
  rw [Pos]
  refine ⟨Real.add hF.1 hG.1, fun t ht ↦ ?_⟩
  have hFpos := hF.2 t ht
  have hGpos := hG.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFpos hGpos
  simp [ResToImagAxis, ht, add_pos hFpos hGpos]

theorem ResToImagAxis.Pos.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F * G) := by
  rw [Pos]
  refine ⟨Real.mul hF.1 hG.1, fun t ht ↦ ?_⟩
  have hFreal := hF.1 t ht
  have hGreal := hG.1 t ht
  have hFpos := hF.2 t ht
  have hGpos := hG.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFpos hGpos
  simp [ResToImagAxis, ht, hFreal, hGreal, mul_pos hFpos hGpos]

theorem ResToImagAxis.Pos.hmul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Pos F)
    (hc : 0 < c) : ResToImagAxis.Pos (fun z => c * F z) := by
  rw [Pos]
  refine ⟨Real.hmul hF.1, fun t ht ↦ ?_⟩
  have hFreal := hF.1 t ht
  have hFpos := hF.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFpos
  simp [ResToImagAxis, ht, mul_pos hc hFpos]

theorem ResToImagAxis.EventuallyPos.add {F G : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (hG : ResToImagAxis.EventuallyPos G) :
    ResToImagAxis.EventuallyPos (F + G) := by
  rw [EventuallyPos]
  refine ⟨ResToImagAxis.Real.add hF.1 hG.1, ?_⟩
  obtain ⟨tF, hF0, hFpos⟩ := hF.2
  obtain ⟨tG, hG0, hGpos⟩ := hG.2
  let t₀ := max tF tG
  use t₀
  refine ⟨by positivity, fun t ht ↦ ?_⟩
  have htF₀ : tF ≤ t₀ := by grind
  have htG₀ : tG ≤ t₀ := by grind
  have htF : tF ≤ t := htF₀.trans ht
  have htG : tG ≤ t := htG₀.trans ht
  have hFpos_t := hFpos t htF
  have hGpos_t := hGpos t htG
  have htpos : 0 < t := by grind
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos] at hFpos_t hGpos_t
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos]
  exact add_pos hFpos_t hGpos_t

theorem ResToImagAxis.EventuallyPos.mul {F G : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (hG : ResToImagAxis.EventuallyPos G) :
    ResToImagAxis.EventuallyPos (F * G) := by
  rw [EventuallyPos]
  refine ⟨ResToImagAxis.Real.mul hF.1 hG.1, ?_⟩
  obtain ⟨tF, hF0, hFpos⟩ := hF.2
  obtain ⟨tG, hG0, hGpos⟩ := hG.2
  let t₀ := max tF tG
  use t₀
  refine ⟨by positivity, fun t ht ↦ ?_⟩
  have htpos : 0 < t := by grind
  have hFreal_t := hF.1 t htpos
  have hGreal_t := hG.1 t htpos
  have htF₀ : tF ≤ t₀ := by grind
  have htG₀ : tG ≤ t₀ := by grind
  have htF : tF ≤ t := htF₀.trans ht
  have htG : tG ≤ t := htG₀.trans ht
  have hFpos_t := hFpos t htF
  have hGpos_t := hGpos t htG
  have htpos : 0 < t := by grind
  simp only [Function.resToImagAxis, ResToImagAxis, htpos] at hFpos_t hGpos_t
  simp only [Function.resToImagAxis, ResToImagAxis, htpos, ↓reduceDIte] at hFreal_t hGreal_t
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos, ↓reduceDIte, Pi.mul_apply, mul_re,
    hFreal_t, hGreal_t, mul_zero, sub_zero]
  exact mul_pos hFpos_t hGpos_t

theorem ResToImagAxis.EventuallyPos.hmul {F : ℍ → ℂ} {c : ℝ}
    (hF : ResToImagAxis.EventuallyPos F) (hc : 0 < c) :
    ResToImagAxis.EventuallyPos (fun z => c * F z) := by
  rw [EventuallyPos]
  refine ⟨ResToImagAxis.Real.hmul hF.1, ?_⟩
  obtain ⟨t₀, hF0, hFpos⟩ := hF.2
  use t₀
  refine ⟨hF0, fun t ht ↦ ?_⟩
  have htpos : 0 < t := by grind
  have hFreal_t := hF.1 t htpos
  have hFpos_t := hFpos t ht
  simp only [Function.resToImagAxis, ResToImagAxis, htpos] at hFreal_t
  simp only [Function.resToImagAxis, ResToImagAxis, htpos] at hFpos_t
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos, ↓reduceDIte, mul_re, ofReal_re,
    ofReal_im, zero_mul, sub_zero]
  exact mul_pos hc hFpos_t

/-!
## Polynomial decay of functions with exponential bounds

This section establishes that if a function `F : ℍ → ℂ` is `O(exp(-c * im τ))` at infinity,
then `t^s * F(it) → 0` as `t → ∞` for any real power `s`.

The main application is to cusp forms, which satisfy such exponential decay bounds.
-/

open Filter Asymptotics in
/--
If `F : ℍ → ℂ` is `O(exp(-c * im τ))` at `atImInfty` for some `c > 0`, then
the restriction to the imaginary axis `t ↦ F(it)` is `O(exp(-c * t))` at `atTop`.
-/
lemma isBigO_resToImagAxis_of_isBigO_atImInfty {F : ℍ → ℂ} {c : ℝ} (_hc : 0 < c)
    (hF : F =O[atImInfty] fun τ => Real.exp (-c * τ.im)) :
    F.resToImagAxis =O[atTop] fun t => Real.exp (-c * t) := by
  rw [Asymptotics.isBigO_iff] at hF ⊢
  obtain ⟨C, hC⟩ := hF
  use C
  rw [Filter.eventually_atImInfty] at hC
  obtain ⟨A, hA⟩ := hC
  filter_upwards [Filter.eventually_ge_atTop (max A 1)] with t ht
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos (le_of_max_le_right ht)
  have ht_A : A ≤ t := le_of_max_le_left ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht_pos, ↓reduceDIte]
  set z : ℍ := ⟨Complex.I * t, by simp [ht_pos]⟩
  have him : z.im = t := by
    change (Complex.I * t).im = t
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add]
  specialize hA z (by rw [him]; exact ht_A)
  simpa only [him] using hA

open Filter Asymptotics Real in
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
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt ht)]

open Filter Asymptotics Real UpperHalfPlane in
/--
If `F : ℍ → ℂ` is `O(exp(-c * im τ))` at `atImInfty` for some `c > 0`, then
`t^s * F(it) → 0` as `t → ∞` for any real power `s`.
-/
theorem tendsto_rpow_mul_resToImagAxis_of_isBigO_exp {F : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hF : F =O[atImInfty] fun τ => rexp (-c * τ.im)) (s : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (s : ℂ) * F.resToImagAxis t) atTop (𝓝 0) :=
  tendsto_rpow_mul_of_isBigO_exp hc (isBigO_resToImagAxis_of_isBigO_atImInfty hc hF)

open Filter Asymptotics Real UpperHalfPlane CuspFormClass in
/--
For a cusp form `f` of level `Γ(n)`, we have `t^s * f(it) → 0` as `t → ∞` for any real power `s`.

This follows from the exponential decay of cusp forms at infinity: `f = O(exp(-2π τ.im / n))`.
-/
theorem cuspForm_rpow_mul_resToImagAxis_tendsto_zero {n : ℕ} {k : ℤ} {F : Type*}
    [NeZero n] [FunLike F ℍ ℂ] [CuspFormClass F Γ(n) k] (f : F) (s : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (s : ℂ) * (f : ℍ → ℂ).resToImagAxis t) atTop (𝓝 0) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hdecay' : (f : ℍ → ℂ) =O[atImInfty] fun τ => rexp (-(2 * π / n) * τ.im) := by
    convert exp_decay_atImInfty n f using 2 with τ; field_simp
  exact tendsto_rpow_mul_resToImagAxis_of_isBigO_exp (div_pos (by positivity) hn_pos) hdecay' s
