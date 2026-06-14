/-
Copyright (c) 2026 Auguste Poiroux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Auguste Poiroux
-/
module
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Fourier.AddCircleMulti

/-! # The quotient map `(ι → ℝ) → (ℝ/ℤ)^ι` presenting the unit torus

For an index type `ι`, the coordinatewise quotient map `coeFun ι : (ι → ℝ) → UnitAddTorus ι`
presents the `ι`-dimensional unit torus `(ℝ/ℤ)^ι` as a quotient of `ℝ^ι`. We record its
continuity, that it is an open quotient map, the value of the Fourier monomials `mFourier k` on
its image, and the pull-back of Haar integration on the torus to a fundamental cube
`∏ i, (t, t+1] ⊆ ℝ^ι`.

This is a companion to `Mathlib.Analysis.Fourier.AddCircleMulti` (which defines `UnitAddTorus`,
`mFourier`, and `mFourierCoeff`).

Upstream target: `Mathlib/Analysis/Fourier/AddCircleMulti.lean` (or a sibling file). Imports here
are left as `public import Mathlib`; they are narrowed at upstreaming time.
-/

open scoped FourierTransform Real
open MeasureTheory

namespace UnitAddTorus

variable {ι : Type*}

/-- The coordinatewise quotient map `(ι → ℝ) → (ℝ/ℤ)^ι`, sending `x` to `i ↦ (x i : ℝ/ℤ)`. It is
the fundamental projection presenting the torus as a quotient of `ℝ^ι`. -/
@[expose] public def coeFun (ι : Type*) : (ι → ℝ) → UnitAddTorus ι :=
  fun x i => (x i : UnitAddCircle)

@[simp] public theorem coeFun_apply (x : ι → ℝ) (i : ι) :
    coeFun ι x i = (x i : UnitAddCircle) := rfl

/-- The coordinatewise quotient map `coeFun` is continuous. -/
@[continuity, fun_prop]
public theorem continuous_coeFun : Continuous (coeFun ι) :=
  continuous_pi fun i => (AddCircle.continuous_mk' 1).comp (continuous_apply i)

/-- `coeFun` is an open quotient map, so it presents `(ℝ/ℤ)^ι` as a quotient of `ℝ^ι`. -/
public theorem isOpenQuotientMap_coeFun (ι : Type*) : IsOpenQuotientMap (coeFun ι) :=
  .piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk

variable [Fintype ι]

/-- Evaluate the additive character `mFourier k` on a point `x : ℝ^ι` viewed in the torus
via `coeFun`. -/
public theorem mFourier_apply_coeFun_ofLp (k : ι → ℤ) (x : EuclideanSpace ℝ ι) :
    UnitAddTorus.mFourier k (coeFun ι (WithLp.ofLp x)) =
      Complex.exp (2 * π * Complex.I * (∑ i : ι, (k i : ℝ) * x i)) := by
  simp [UnitAddTorus.mFourier, coeFun, ← Complex.exp_sum, Finset.mul_sum, mul_assoc]

/-- Pull back Haar integration on `(ℝ/ℤ)^ι` to the fundamental cube `∏ i, (t, t+1] ⊆ ℝ^ι`. -/
public theorem integral_eq_integral_preimage_coeFun (t : ℝ) (g : UnitAddTorus ι → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure (UnitAddTorus ι))) :
    (∫ y : UnitAddTorus ι, g y) =
      ∫ x, g (coeFun ι x) ∂(volume : Measure (ι → ℝ)).restrict
        (Set.univ.pi fun _ : ι => Set.Ioc t (t + 1)) := by
  have hmp : MeasurePreserving (coeFun ι)
      (Measure.pi fun _ : ι => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)))
      (volume : Measure (UnitAddTorus ι)) :=
    measurePreserving_pi _ _ fun _ => UnitAddCircle.measurePreserving_mk t
  have hrestrict : (volume : Measure (ι → ℝ)).restrict
        (Set.univ.pi fun _ : ι => Set.Ioc t (t + 1)) =
      Measure.pi fun _ : ι => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)) :=
    Measure.restrict_pi_pi _ _
  rw [hrestrict, ← hmp.map_eq]
  exact integral_map hmp.aemeasurable (hmp.map_eq.symm ▸ hg)

end UnitAddTorus
