module
import SpherePacking.Tactic.FunPropExt
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-! # Tests for `SpherePacking.Tactic.FunPropExt` -/

open scoped Manifold

/-! ### `MDifferentiable` -/

example (F : UpperHalfPlane → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F ^ 2) := by fun_prop

example (F : UpperHalfPlane → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F ^ 6 - 3 * F ^ 2 + 7) := by fun_prop

example (H₂ H₄ : UpperHalfPlane → ℂ)
    (hH₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂) (hH₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 3 * (2 * H₂ ^ 2 + 5 * H₂ * H₄ + 5 * H₄ ^ 2)) := by fun_prop

/-! ### `Summable` and `HasSum` -/

section Summable
variable {f g h : ℕ → ℝ} {a b : ℝ}

example (hf : Summable f) (hg : Summable g) : Summable (fun n => f n + g n) := by fun_prop

example (hf : Summable f) (hg : Summable g) (hh : Summable h) :
    Summable (fun n => f n + g n - h n) := by fun_prop

example (hf : Summable f) (hg : Summable g) :
    Summable (fun n => (3 : ℝ) * f n + g n * (5 : ℝ)) := by fun_prop

example (hf : Summable f) : Summable (fun n => (2 : ℝ) • f n) := by fun_prop

example (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun n => f n + g n) (a + b) := by fun_prop

example (hf : HasSum f a) : HasSum (fun n => (3 : ℝ) * f n) ((3 : ℝ) * a) := by fun_prop

end Summable

/-! ### `MeasureTheory.Integrable` -/

section Integrable
open MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
  {E : Type*} [NormedAddCommGroup E] {f g : α → E}

example (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => f x + g x) μ := by fun_prop

example (hf : Integrable f μ) : Integrable (fun x => ‖f x‖) μ := by fun_prop

end Integrable

section IntegrableScalar
open MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
  {𝕜 : Type*} [NormedRing 𝕜] {f : α → 𝕜}

example (hf : Integrable f μ) : Integrable (fun x => (7 : 𝕜) * f x) μ := by fun_prop

example (hf : Integrable f μ) : Integrable (fun x => f x * (9 : 𝕜)) μ := by fun_prop

end IntegrableScalar
