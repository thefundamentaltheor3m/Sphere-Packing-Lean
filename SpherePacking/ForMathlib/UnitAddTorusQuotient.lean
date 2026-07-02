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
continuity, that it is an open quotient map, and the value of the Fourier monomials `mFourier k`
on its image.

We also record the pull-back of Haar integration on the torus to a fundamental cube
`∏ i, (t, t+1] ⊆ ℝ^ι`. Mathlib already proves this, more generally, as
`UnitAddTorus.integral_preimage` — but that lemma is stated under a file-`local` measure-space
instance `⟨AddCircle.haarAddCircle⟩` on `UnitAddCircle`, which differs (by a defeq-trivial `1 •`)
from the global `AddCircle.measureSpace 1` that this project's torus integrals use, so it is not a
drop-in. We therefore keep our own version against the global instance; at upstreaming time, once
the instances are reconciled, it is subsumed by `UnitAddTorus.integral_preimage`.

This is a companion to `Mathlib.Analysis.Fourier.AddCircleMulti` (which defines `UnitAddTorus`,
`mFourier`, and `mFourierCoeff`).

Upstream note: `coeFun ι` is definitionally `Pi.map (fun _ => QuotientAddGroup.mk)` (the coercion
`(· : UnitAddCircle)` is `QuotientAddGroup.mk`), and `mFourier_apply_coeFun` is a single-`simp`
unfolding; on upstreaming `coeFun` would be inlined and these lemmas folded into
`Mathlib/Analysis/Fourier/AddCircleMulti.lean`. They are kept here as the project-local quotient
API on which `PoissonSummationGeneral.lean` builds. Imports here are left as `public import
Mathlib`; they are narrowed at upstreaming time.
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
public theorem mFourier_apply_coeFun (k : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier k (coeFun ι x) =
      Complex.exp (2 * π * Complex.I * (∑ i : ι, (k i : ℝ) * x i)) := by
  simp [UnitAddTorus.mFourier, coeFun, ← Complex.exp_sum, Finset.mul_sum, mul_assoc]

/-- Pull back Haar integration on `(ℝ/ℤ)^ι` to the fundamental cube `∏ i, (t, t+1] ⊆ ℝ^ι`. Stated
against the global `AddCircle.measureSpace 1` instance (see the module docstring on why mathlib's
`UnitAddTorus.integral_preimage` is not a drop-in). -/
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
