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

theorem ResToImagAxisDifferentiable (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (t : ℝ)
    (ht : 0 < t) : DifferentiableAt ℝ (ResToImagAxis F) t := by
  sorry

/--
Restriction and slash action under S: (F |_k S) (I * t) = t^(-k) * F(I / t)
-/
theorem ResToImagAxisSlashActionS (F : ℍ → ℂ) (k : ℤ) (t : ℝ)
    (ht : 0 < t) : ResToImagAxis (F ∣[k] S) t = Complex.I ^ k * t ^ (-k) * ResToImagAxis F (1 / t)
    := by
  sorry
