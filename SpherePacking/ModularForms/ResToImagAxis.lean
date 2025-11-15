import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashActions

open UpperHalfPlane hiding I

open Real Complex ContinuousMap Matrix CongruenceSubgroup ModularGroup

open scoped Interval Real Topology Manifold ModularForm MatrixGroups

/--
Restrict a function `F : ℍ → ℂ` to the positive imaginary axis, i.e. `t ↦ F (I * t)`.
If $t \le 0$, then `F (I * t)` is not defined, so we return `0` in that case.
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
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is real-valued.
-/
noncomputable def ResToImagAxis.Real (F : ℍ → ℂ) : Prop :=
  ∃ f : ℝ → ℝ, ∀ t : ℝ, ∀ ht : 0 < t, F ⟨(Complex.I * t), by simp [ht]⟩ = f t

/--
Function $F : \mathbb{H} \to \mathbb{C}$ is postive on the imaginary axis.
-/
noncomputable def ResToImagAxis.Pos (F : ℍ → ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → ∃ r : ℝ, 0 < r ∧ F.resToImagAxis t = r

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is eventually
positive, i.e. there exists $t_0 > 0$ such that for all $t \ge t_0$, $F(it)$ is positive.
-/
noncomputable def ResToImagAxis.EventuallyPos (F : ℍ → ℂ) : Prop :=
  ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∃ r : ℝ, 0 < r ∧ F.resToImagAxis t = r

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
  rw [ofComplex_apply_of_im_pos _]

/--
Restriction and slash action under S: $(F |_k S) (it) = t^{-k} * F(it)$
-/
theorem ResToImagAxis.SlashActionS (F : ℍ → ℂ) (k : ℤ) (t : ℝ)
    (ht : 0 < t) : (F ∣[k] S).resToImagAxis t = Complex.I ^ k * t ^ (-k) * F.resToImagAxis (1 / t)
    := by
  sorry
