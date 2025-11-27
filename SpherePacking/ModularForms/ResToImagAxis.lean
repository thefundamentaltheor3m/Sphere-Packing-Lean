import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashActions

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
Restriction and slash action under S: $(F |_k S) (it) = t^{-k} * F(it)$
-/
theorem ResToImagAxis.SlashActionS (F : ℍ → ℂ) (k : ℤ) (t : ℝ)
    (ht : 0 < t) : (F ∣[k] S).resToImagAxis t = Complex.I ^ k * t ^ (-k) * F.resToImagAxis (1 / t)
    := by
  sorry

/--
Realenss, positivity and essential positivity are closed under the addition and multiplication.
-/
theorem ResToImagAxis.Real.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F + G) := by
  intro t ht
  have hFreal := hF t ht
  have hGreal := hG t ht
  simp [Function.resToImagAxis, ResToImagAxis, ht] at hFreal hGreal
  simp [Function.resToImagAxis, ResToImagAxis, ht, add_im, hFreal, hGreal]

theorem ResToImagAxis.Real.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F * G) := by
  intro t ht
  have hFreal := hF t ht
  have hGreal := hG t ht
  simp [Function.resToImagAxis, ResToImagAxis, ht] at hFreal hGreal
  simp [Function.resToImagAxis, ResToImagAxis, ht, mul_im, hFreal, hGreal]

theorem ResToImagAxis.Real.hmul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Real F) :
    ResToImagAxis.Real (c • F) := by
  intro t ht
  have hFreal := hF t ht
  simp [Function.resToImagAxis, ResToImagAxis, ht] at hFreal
  simp [Function.resToImagAxis, ResToImagAxis, ht, hFreal]

theorem ResToImagAxis.Pos.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F + G) := by
  rw [Pos]
  refine ⟨Real.add hF.1 hG.1, ?_⟩
  intro t ht
  have hFpos := hF.2 t ht
  have hGpos := hG.2 t ht
  simp [Function.resToImagAxis, ResToImagAxis, ht] at hFpos hGpos
  simp [Function.resToImagAxis, ResToImagAxis, ht, add_re, add_pos hFpos hGpos]

theorem ResToImagAxis.Pos.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F * G) := by
  rw [Pos]
  refine ⟨Real.mul hF.1 hG.1, ?_⟩
  intro t ht
  have hFreal := hF.1 t ht
  have hGreal := hG.1 t ht
  have hFpos := hF.2 t ht
  have hGpos := hG.2 t ht
  simp [Function.resToImagAxis, ResToImagAxis, ht] at hFreal hGreal
  simp [Function.resToImagAxis, ResToImagAxis, ht] at hFpos hGpos
  simp [Function.resToImagAxis, ResToImagAxis, ht, mul_re, hFreal, hGreal, mul_pos hFpos hGpos]

theorem ResToImagAxis.Pos.hmul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Pos F)
    (hc : 0 < c) : ResToImagAxis.Pos (fun z => c * F z) := by
  rw [Pos]
  refine ⟨Real.hmul hF.1, ?_⟩
  intro t ht
  have hFreal := hF.1 t ht
  have hFpos := hF.2 t ht
  simp [Function.resToImagAxis, ResToImagAxis, ht] at hFreal
  simp [Function.resToImagAxis, ResToImagAxis, ht] at hFpos
  simp [Function.resToImagAxis, ResToImagAxis, ht, mul_re, hFreal, mul_pos hc hFpos]

theorem ResToImagAxis.EventuallyPos.add {F G : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (hG : ResToImagAxis.EventuallyPos G) :
    ResToImagAxis.EventuallyPos (F + G) := by
  rw [EventuallyPos]
  refine ⟨ResToImagAxis.Real.add hF.1 hG.1, ?_⟩
  obtain ⟨tF, hF0, hFpos⟩ := hF.2
  obtain ⟨tG, hG0, hGpos⟩ := hG.2
  let t₀ := max tF tG
  use t₀
  refine ⟨by positivity, ?_⟩
  intro t ht
  have htF₀ : tF ≤ t₀ := by grind
  have htG₀ : tG ≤ t₀ := by grind
  have htF : tF ≤ t := htF₀.trans ht
  have htG : tG ≤ t := htG₀.trans ht
  have hFpos_t := hFpos t htF
  have hGpos_t := hGpos t htG
  have htpos : 0 < t := by grind
  simp [Function.resToImagAxis, ResToImagAxis, htpos] at hFpos_t hGpos_t
  simp [ResToImagAxis, htpos]
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
  refine ⟨by positivity, ?_⟩
  intro t ht
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
  simp [Function.resToImagAxis, ResToImagAxis, htpos] at hFpos_t hGpos_t
  simp [Function.resToImagAxis, ResToImagAxis, htpos] at hFreal_t hGreal_t
  simp [ResToImagAxis, htpos, hFreal_t, hGreal_t]
  exact mul_pos hFpos_t hGpos_t

theorem ResToImagAxis.EventuallyPos.hmul {F : ℍ → ℂ} {c : ℝ}
    (hF : ResToImagAxis.EventuallyPos F) (hc : 0 < c) :
    ResToImagAxis.EventuallyPos (fun z => c * F z) := by
  rw [EventuallyPos]
  refine ⟨ResToImagAxis.Real.hmul hF.1, ?_⟩
  obtain ⟨t₀, hF0, hFpos⟩ := hF.2
  use t₀
  refine ⟨hF0, ?_⟩
  intro t ht
  have htpos : 0 < t := by grind
  have hFreal_t := hF.1 t htpos
  have hFpos_t := hFpos t ht
  simp [Function.resToImagAxis, ResToImagAxis, htpos] at hFreal_t
  simp [Function.resToImagAxis, ResToImagAxis, htpos] at hFpos_t
  simp [ResToImagAxis, htpos, hFreal_t]
  exact mul_pos hc hFpos_t
