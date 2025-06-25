import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs

open UpperHalfPlane

open scoped Interval Real NNReal ENNReal Topology Manifold


/--
Restrict a function `F : ℍ → ℂ` to the positive imaginary axis, i.e. `t ↦ F (I * t)`.
If $t \le 0$, then `F (I * t)` is not defined, so we return `0` in that case.
-/
noncomputable def ResToImagAxis (F : ℍ → ℂ) : ℝ → ℂ :=
  fun t => if ht : 0 < t then F ⟨(Complex.I * t), by simp [ht]⟩ else 0
