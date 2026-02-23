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
    fun_prop
  refine (hF.comp hz).congr fun t => ?_
  have ht : (0 : ℝ) < (t : ℝ) := t.property
  simp [Set.restrict, ResToImagAxis, z, ht]

/-- A variant of `continuousOn_resToImagAxis_Ioi_of` on the closed ray `Ici 1`. -/
public lemma continuousOn_resToImagAxis_Ici_one_of {F : ℍ → ℂ} (hF : Continuous F) :
    ContinuousOn F.resToImagAxis (Set.Ici (1 : ℝ)) := by
  refine (continuousOn_resToImagAxis_Ioi_of hF).mono fun _ ht => by
    simpa [Set.mem_Ioi] using lt_of_lt_of_le zero_lt_one ht

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
  have h_diff : DifferentiableAt ℝ (fun t : ℝ => F (ofComplex (Complex.I * t))) t := by
    let g : ℝ → ℂ := fun s => Complex.I * (s : ℂ)
    have hF_diff : DifferentiableAt ℂ (F ∘ ofComplex) (g t) := by
      simpa [g] using UpperHalfPlane.mdifferentiableAt_iff.mp
        (hF ⟨Complex.I * t, by norm_num [Complex.I_re, ht]⟩)
    have hg : DifferentiableAt ℝ g t := by
      simpa [g] using
        (Complex.ofRealCLM.hasFDerivAt (x := t)).differentiableAt.const_mul Complex.I
    simpa [Function.comp_def, g] using (hF_diff.restrictScalars ℝ).comp t hg
  apply h_diff.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with t ht
  simp_all only [ResToImagAxis, ↓reduceDIte]
  rw [ofComplex_apply_of_im_pos]

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

theorem ResToImagAxis.SlashActionS' (F : ℍ → ℂ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    F.resToImagAxis (1 / t) = (Complex.I) ^ k * t ^ k * (F ∣[k] S).resToImagAxis t := by
  have hS := ResToImagAxis.SlashActionS F k ht
  calc F.resToImagAxis (1 / t)
      = I ^ k * I ^ (-k) * (t ^ k * t ^ (-k)) * F.resToImagAxis (1 / t) := by
          simp only [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero k I_ne_zero),
                     mul_inv_cancel₀ (zpow_ne_zero k (ofReal_ne_zero.mpr ht.ne')), one_mul]
    _ = I ^ k * t ^ k * (I ^ (-k) * t ^ (-k) * F.resToImagAxis (1 / t)) := by ring
    _ = I ^ k * t ^ k * (F ∣[k] S).resToImagAxis t := by rw [← hS]

/-- For any function F : ℍ → ℂ and t > 0, F.resToImagAxis (1/t) = F(S • (I*t)). -/
theorem ResToImagAxis.one_div_eq_S_smul (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    let z : ℍ := ⟨I * t, by simp [ht]⟩
    F.resToImagAxis (1 / t) = F (S • z) := by
  have ht_inv : 0 < 1 / t := one_div_pos.mpr ht
  set z : ℍ := ⟨I * t, by simp [ht]⟩ with hz_def
  have hS_z : S • z = ⟨I / t, by simp [ht]⟩ := by
    apply UpperHalfPlane.ext
    simp only [UpperHalfPlane.modular_S_smul, hz_def, div_eq_mul_inv]
    change (-(I * ↑t))⁻¹ = I * (↑t)⁻¹
    have hne : (I : ℂ) * t ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr ht.ne')
    field_simp [hne, I_sq]
    ring_nf
    simp only [I_sq, mul_neg, mul_one]
  simp only [Function.resToImagAxis, ResToImagAxis, ht_inv, ↓reduceDIte, hS_z]
  congr 1; apply UpperHalfPlane.ext
  simp only [div_eq_mul_inv, mul_comm I, one_mul, ofReal_inv]

/--
Realness, positivity and essential positivity are closed under the addition and multiplication.
-/
@[fun_prop]
theorem ResToImagAxis.Real.const (c : ℝ) : ResToImagAxis.Real (fun _ => c) := by
  intro t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, ofReal_im]

@[fun_prop]
theorem ResToImagAxis.Real.zero : ResToImagAxis.Real (fun _ => 0) := ResToImagAxis.Real.const 0

@[fun_prop]
theorem ResToImagAxis.Real.one : ResToImagAxis.Real (fun _ => 1) := ResToImagAxis.Real.const 1

@[fun_prop]
theorem ResToImagAxis.Real.neg {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) : ResToImagAxis.Real (-F)
    := by
  intro t ht
  have hFreal := hF t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal
  simp [ResToImagAxis, ht, hFreal]

@[fun_prop]
theorem ResToImagAxis.Real.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
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

@[fun_prop]
theorem ResToImagAxis.Real.inv {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) :
    ResToImagAxis.Real F⁻¹ := by
  intro t ht
  have hFreal := hF t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal
  simp [ResToImagAxis, ht, Pi.inv_apply, Complex.inv_im, hFreal]

@[fun_prop]
theorem ResToImagAxis.Real.div {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F / G) := by
  simpa [div_eq_mul_inv] using hF.mul hG.inv

/-- `(a/b).re = a.re/b.re` when `b` is real-valued (building block for `re_div_eq`). -/
private theorem div_re_of_im_eq_zero {a b : ℂ} (hb : b.im = 0) : (a / b).re = a.re / b.re := by
  rw [show b = ↑b.re from Complex.ext rfl (by simp [hb])]; exact Complex.div_ofReal_re a b.re

/-- Real part of a quotient on the imaginary axis is the quotient of real parts, provided the
denominator `G` is real-valued there (the numerator's realness is not needed). -/
theorem ResToImagAxis.Real.re_div_eq {F G : ℍ → ℂ} (hG : ResToImagAxis.Real G) (t : ℝ) :
    ((F / G).resToImagAxis t).re = (F.resToImagAxis t).re / (G.resToImagAxis t).re := by
  simp only [Function.resToImagAxis, ResToImagAxis]
  split_ifs with ht
  · have hGreal := hG t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hGreal
    simpa only [Pi.div_apply] using div_re_of_im_eq_zero hGreal
  · simp

/-- Real part of a product on the imaginary axis is the product of real parts, when both factors are
real-valued there. -/
theorem ResToImagAxis.Real.re_mul_eq {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) (t : ℝ) :
    ((F * G).resToImagAxis t).re = (F.resToImagAxis t).re * (G.resToImagAxis t).re := by
  simp only [Function.resToImagAxis, ResToImagAxis]
  split_ifs with ht
  · have hFreal := hF t ht
    have hGreal := hG t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal
    simp [Pi.mul_apply, Complex.mul_re, hFreal, hGreal]
  · simp

/-- Real part of `F / (G * H)` on the imaginary axis, with `G` and `H` real-valued there. -/
theorem ResToImagAxis.Real.re_div_mul_eq {F G H : ℍ → ℂ} (hG : ResToImagAxis.Real G)
    (hH : ResToImagAxis.Real H) (t : ℝ) :
    ((F / (G * H)).resToImagAxis t).re =
      (F.resToImagAxis t).re / ((G.resToImagAxis t).re * (H.resToImagAxis t).re) := by
  rw [ResToImagAxis.Real.re_div_eq (hG.mul hH) t, ResToImagAxis.Real.re_mul_eq hG hH t]

theorem ResToImagAxis.Pos.const (c : ℝ) (hc : 0 < c) : ResToImagAxis.Pos (fun _ => c) :=
  ⟨ResToImagAxis.Real.const c, fun t ht ↦ by simp [ResToImagAxis, ht, hc]⟩

/-- The property `ResToImagAxis.Pos` is closed under addition. -/
public theorem ResToImagAxis.Pos.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F + G) := by
  refine ⟨Real.add hF.1 hG.1, fun t ht => by grind [hF.2 t ht, hG.2 t ht]⟩

/-- The property `ResToImagAxis.Pos` is closed under multiplication. -/
public theorem ResToImagAxis.Pos.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F * G) := by
  rw [Pos]
  refine ⟨Real.mul hF.1 hG.1, fun t ht ↦ ?_⟩
  rw [Real.re_mul_eq hF.1 hG.1 t]
  exact mul_pos (hF.2 t ht) (hG.2 t ht)

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

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.mul {F G : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (hG : ResToImagAxis.EventuallyPos G) :
    ResToImagAxis.EventuallyPos (F * G) := by
  rw [EventuallyPos]
  refine ⟨ResToImagAxis.Real.mul hF.1 hG.1, ?_⟩
  obtain ⟨tF, hF0, hFpos⟩ := hF.2
  obtain ⟨tG, hG0, hGpos⟩ := hG.2
  refine ⟨max tF tG, by positivity, fun t ht ↦ ?_⟩
  rw [ResToImagAxis.Real.re_mul_eq hF.1 hG.1 t]
  exact mul_pos (hFpos t ((le_max_left tF tG).trans ht)) (hGpos t ((le_max_right tF tG).trans ht))

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.pow {F : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (n : ℕ) :
    ResToImagAxis.EventuallyPos (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.EventuallyPos.one
  | succ n hn => exact hn.mul hF

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.EventuallyPos F)
    (hc : 0 < c) : ResToImagAxis.EventuallyPos (c • F) := by
  rw [EventuallyPos]
  refine ⟨ResToImagAxis.Real.smul hF.1, ?_⟩
  obtain ⟨t₀, hF0, hFpos⟩ := hF.2
  use t₀
  refine ⟨hF0, fun t ht ↦ ?_⟩
  have htpos : 0 < t := by grind
  have hFreal_t := hF.1 t htpos
  have hFpos_t := hFpos t ht
  simp only [Function.resToImagAxis, ResToImagAxis, htpos, ↓reduceDIte] at hFreal_t
  simp only [Function.resToImagAxis, ResToImagAxis, htpos, ↓reduceDIte] at hFpos_t
  simp [ResToImagAxis, htpos, mul_pos hc hFpos_t]

theorem ResToImagAxis.I_mul_t_eq (F : ℍ → ℂ) (t : ℝ) (ht : 0 < t) :
    F ⟨I * t, by simp [ht]⟩ = F.resToImagAxis t := by
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]

/-- If `F` is real-valued, then `F` is equal to the real part of itself on imaginary axis. -/
theorem ResToImagAxis.Real.eq_real_part {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) (t : ℝ) :
    F.resToImagAxis t = (F.resToImagAxis t).re := by
  simp only [Function.resToImagAxis, ResToImagAxis]
  split_ifs with ht
  exacts [Complex.ext rfl (by simpa [Function.resToImagAxis, ResToImagAxis, ht]
    using (hF t ht)), rfl]

/-- For real-valued `F`, `G`, the complex quotient on the imaginary axis equals the (coerced) real
quotient of real parts. -/
theorem ResToImagAxis.Real.div_eq_real_div {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) (t : ℝ) :
    F.resToImagAxis t / G.resToImagAxis t =
      ((F.resToImagAxis t).re / (G.resToImagAxis t).re : ℝ) := by
  rw [hF.eq_real_part t, hG.eq_real_part t]
  push_cast
  rw [Complex.ofReal_re, Complex.ofReal_re]

/-!
## Polynomial decay of functions with exponential bounds

This section establishes that if a function `F : ℍ → ℂ` is `O(exp(-c * im τ))` at infinity,
then `t^s * F(it) → 0` as `t → ∞` for any real power `s`.

One application is to cusp forms, which satisfy such exponential decay bounds.
-/

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
  tendsto_rpow_mul_of_isBigO_exp hc (isBigO_resToImagAxis_of_isBigO_atImInfty hc hF)

/--
If `F : ℍ → ℂ` is `O(exp(-c * im τ))` at `atImInfty` for some `c > 0`, then
`t^n * re (F(it)) → 0` as `t → ∞` for any natural power `n`.
-/
theorem tendsto_pow_mul_resToImagAxis_re_of_isBigO_exp {F : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hF : F =O[atImInfty] fun τ => rexp (-c * τ.im)) (n : ℕ) :
    Tendsto (fun t : ℝ => t ^ n * (F.resToImagAxis t).re) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Complex.ofReal_natCast, Complex.cpow_natCast,
    ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.zero_re] using
    (Complex.continuous_re.tendsto 0).comp
      (tendsto_rpow_mul_resToImagAxis_of_isBigO_exp hc hF n)

/--
For a cusp form `f` of level `Γ(n)`, we have `t^s * f(it) → 0` as `t → ∞` for any real power `s`.

This follows from the exponential decay of cusp forms at infinity: `f = O(exp(-2π τ.im / n))`.
-/
theorem cuspForm_rpow_mul_resToImagAxis_tendsto_zero {n : ℕ} {k : ℤ} {F : Type*}
    [NeZero n] [FunLike F ℍ ℂ] [CuspFormClass F Γ(n) k] (f : F) (s : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (s : ℂ) * (f : ℍ → ℂ).resToImagAxis t) atTop (𝓝 0) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hmem : (n : ℝ) ∈ (Γ(n) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp only [strictPeriods_Gamma]
    exact AddSubgroup.mem_zmultiples (n : ℝ)
  have hdecay' : (f : ℍ → ℂ) =O[atImInfty] fun τ => rexp (-(2 * π / n) * τ.im) := by
    convert CuspFormClass.exp_decay_atImInfty hn_pos hmem (f := f) using 2 with τ; field_simp
  exact tendsto_rpow_mul_resToImagAxis_of_isBigO_exp (div_pos (by positivity) hn_pos) hdecay' s

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
