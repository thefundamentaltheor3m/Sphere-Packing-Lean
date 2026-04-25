/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.RCLike.Inner
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular

public import SpherePacking.Basic.SpherePacking
public import SpherePacking.Basic.PeriodicPacking.Aux
public import SpherePacking.Basic.PeriodicPacking.Theorem22
public import SpherePacking.Basic.PeriodicPacking.DensityFormula
public import SpherePacking.Basic.PeriodicPacking.PeriodicConstant
public import SpherePacking.Basic.PeriodicPacking.BoundaryControl
public import SpherePacking.CohnElkies.PoissonSummationGeneral


/-!
# Cohn-Elkies prerequisites

This file collects auxiliary imports, instances, and small lemmas used across the Cohn-Elkies
development (in particular `SpherePacking.CohnElkies.LPBound`).

Many statements here are general-purpose, but keeping them together provides a stable import
boundary for the analytic part of the argument (Poisson summation, Fourier inversion, and
integration/positivity lemmas).
-/

variable {d : ℕ} [Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- Convenience: `Fin d` is nonempty when `0 < d`. -/
public instance instNonemptyFin : Nonempty (Fin d) := ⟨0, Fact.out⟩

noncomputable section

open scoped BigOperators FourierTransform

namespace SchwartzMap

section FourierSchwartz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
  (f : 𝓢(V, E))

/-- Fourier inversion for Schwartz functions. -/
@[simp]
public theorem fourierInversion : 𝓕⁻ (𝓕 ⇑f) = f := by
  rw [← fourier_coe, ← fourierInv_coe]; simp

end FourierSchwartz

end SchwartzMap
section Positivity_on_Nhd

variable {E : Type*} [TopologicalSpace E]

theorem Continuous.pos_iff_exists_nhd_pos {f : E → ℝ} (hf₁ : Continuous f) (x : E) :
    0 < f x ↔ ∃ U ∈ (nhds x), ∀ y ∈ U, 0 < f y :=
  ⟨fun hx => ⟨{y : E | 0 < f y}, (isOpen_lt continuous_const hf₁).mem_nhds hx, fun _ hy => hy⟩,
    fun ⟨_, hU, hUpos⟩ => hUpos x (mem_of_mem_nhds hU)⟩

open MeasureTheory

variable [MeasureSpace E] [BorelSpace E]

end Positivity_on_Nhd

section Integration

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [MeasureSpace E] [BorelSpace E]
variable [(volume : Measure E).IsAddLeftInvariant] [(volume : Measure E).Regular]
  [NeZero (volume : Measure E)]

instance : (volume : Measure E).IsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_regular

/--
If `f` is continuous, integrable, and pointwise nonnegative, then `∫ f = 0` iff `f = 0`.

This uses that an additive-invariant regular measure is positive on nonempty open sets.
-/
public theorem Continuous.integral_zero_iff_zero_of_nonneg {f : E → ℝ} (hf₁ : Continuous f)
    (hf₂ : Integrable f) (hnn : ∀ x, 0 ≤ f x) : ∫ (v : E), f v = 0 ↔ f = 0 := by
  refine ⟨fun hintf => ?_, fun hf => by simp [hf]⟩
  have hne_zero : (volume : Measure E) {y | f y ≠ 0} = 0 :=
    (integral_eq_zero_iff_of_nonneg hnn hf₂).1 hintf
  funext x
  by_contra hx
  obtain ⟨U, hU₁, hU₃⟩ :=
    (hf₁.pos_iff_exists_nhd_pos x).1 (lt_of_le_of_ne (hnn x) (Ne.symm hx))
  exact (MeasureTheory.Measure.measure_pos_of_mem_nhds volume hU₁).ne'
    (measure_mono_null (fun y hy => (hU₃ y hy).ne') hne_zero)

end Integration

section Misc

omit [Fact (0 < d)]
local notation "conj" => starRingEnd ℂ
/--
Complex exponential conjugation identity for real inner products.

This is used to relate `cexp (2 * pi * I * <x,m>)` and its conjugate.
-/
public theorem Complex.exp_neg_real_I_eq_conj (x m : EuclideanSpace ℝ (Fin d)) :
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ))) =
      conj (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ))) := calc
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ)))
      = Circle.exp (-2 * Real.pi * ⟪x, m⟫_[ℝ]) := by
        rw [Circle.coe_exp]; push_cast; ring_nf
    _ = conj (Circle.exp (2 * Real.pi * ⟪x, m⟫_[ℝ])) := by
        rw [mul_assoc, neg_mul, ← mul_assoc, ← Circle.coe_inv_eq_conj, Circle.exp_neg]
    _ = conj (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ))) := by
        rw [Circle.coe_exp]; apply congrArg conj; push_cast; ring_nf

end Misc

end
