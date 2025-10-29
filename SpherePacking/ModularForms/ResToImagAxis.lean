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

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is real-valued.
-/
noncomputable def ResToImagAxisReal (F : ℍ → ℂ) : Prop :=
  ∃ f : ℝ → ℝ, ∀ t : ℝ, ∀ ht : 0 < t, F ⟨(Complex.I * t), by simp [ht]⟩ = f t

/--
Function $F : \mathbb{H} \to \mathbb{C}$ is postive on the imaginary axis.
-/
noncomputable def ResToImagAxisPos (F : ℍ → ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → ∃ r : ℝ, 0 < r ∧ ResToImagAxis F t = r

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is eventually
positive, i.e. there exists $t_0 > 0$ such that for all $t \ge t_0$, $F(it)$ is positive.
-/
noncomputable def ResToImagAxisEventuallyPos (F : ℍ → ℂ) : Prop :=
  ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∃ r : ℝ, 0 < r ∧ ResToImagAxis F t = r

theorem ResToImagAxisDifferentiable (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (t : ℝ)
    (ht : 0 < t) : DifferentiableAt ℝ (ResToImagAxis F) t := by
  sorry

/--
Restriction and slash action under S: $(F |_k S) (it) = t^{-k} * F(it)$
-/
theorem ResToImagAxisSlashActionS (F : ℍ → ℂ) (k : ℤ) (t : ℝ)
    (ht : 0 < t) : ResToImagAxis (F ∣[k] S) t = Complex.I ^ k * t ^ (-k) * ResToImagAxis F (1 / t)
    := by
  sorry
