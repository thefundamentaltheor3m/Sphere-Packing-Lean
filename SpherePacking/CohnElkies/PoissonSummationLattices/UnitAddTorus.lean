module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
Helper lemmas about the quotient map `(Fin n → ℝ) → (ℝ/ℤ)^n` used in the Poisson summation
development.
-/

open scoped BigOperators Real
open MeasureTheory

namespace SchwartzMap.UnitAddTorus

/-- The coordinatewise quotient map `(Fin n → ℝ) → (ℝ/ℤ)^n`. -/
@[expose] public def coeFun (n : ℕ) : (Fin n → ℝ) → UnitAddTorus (Fin n) :=
  fun x i => (x i : UnitAddCircle)

/-- Continuity of the coordinatewise quotient map `coeFun`. -/
@[continuity]
public theorem continuous_coeFun {n : ℕ} : Continuous (coeFun n) := by
  refine continuous_pi (fun i => ?_)
  simpa [coeFun, UnitAddCircle] using
    (AddCircle.continuous_mk' (p := (1 : ℝ))).comp (continuous_apply i)

/-- A homeomorphism `α × (Fin n → α) ≃ (Fin (n+1) → α)`, specialized to constant families. -/
def finSuccPiHomeomorph (α : Type*) [TopologicalSpace α] (n : ℕ) :
    (α × (Fin n → α)) ≃ₜ (Fin n.succ → α) where
  toEquiv :=
    { toFun := fun p => Fin.cons p.1 p.2
      invFun := fun f => (f 0, fun i => f (Fin.succ i))
      left_inv := by
        rintro ⟨a, f⟩
        ext <;> simp
      right_inv := by
        intro f
        ext i
        cases i using Fin.cases with
        | zero => simp
        | succ i => simp }
  continuous_toFun := by
    -- `Fin.cons` is continuous coordinatewise.
    refine continuous_pi ?_
    intro i
    cases i using Fin.cases with
    | zero =>
        simpa using continuous_fst
    | succ i =>
        simpa using (continuous_apply i |>.comp continuous_snd)
  continuous_invFun := by
    refine (continuous_apply (0 : Fin n.succ)).prodMk ?_
    refine continuous_pi ?_
    intro i
    simpa using (continuous_apply (Fin.succ i))

/-- `coeFun` is an open quotient map, so it presents `(ℝ/ℤ)^n` as a quotient of `ℝ^n`. -/
public theorem isOpenQuotientMap_coeFun (n : ℕ) : IsOpenQuotientMap (coeFun n) := by
  induction n with
  | zero =>
      have h :
          coeFun 0 =
            (Homeomorph.homeomorphOfUnique (Fin 0 → ℝ) (UnitAddTorus (Fin 0)) : _ → _) := by
        funext x
        exact Subsingleton.elim _ _
      simpa [h] using
        (Homeomorph.homeomorphOfUnique (Fin 0 → ℝ) (UnitAddTorus (Fin 0))).isOpenQuotientMap
  | succ n ih =>
      -- Reduce to the product case using `finSuccPiHomeomorph`.
      have h₁ : IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle)) := by
        simpa using
          (QuotientAddGroup.isOpenQuotientMap_mk (G := ℝ) (N := AddSubgroup.zmultiples (1 : ℝ)))
      let eX := (finSuccPiHomeomorph (α := ℝ) n).symm
      let eY := finSuccPiHomeomorph (α := UnitAddCircle) n
      have heX : IsOpenQuotientMap (eX : (Fin n.succ → ℝ) → ℝ × (Fin n → ℝ)) :=
        eX.isOpenQuotientMap
      have hprod :
          IsOpenQuotientMap (Prod.map (fun x : ℝ => (x : UnitAddCircle)) (coeFun n)) :=
        IsOpenQuotientMap.prodMap h₁ (ih)
      -- `coeFun (n+1)` is conjugate to `Prod.map` by these homeomorphisms.
      have hconj :
          coeFun n.succ =
            (fun x =>
              eY
                (Prod.map (fun x : ℝ => (x : UnitAddCircle)) (coeFun n) (eX x))) := by
        funext x
        ext i
        cases i using Fin.cases with
        | zero => simp [coeFun, eY, finSuccPiHomeomorph, eX, Prod.map]
        | succ i => simp [coeFun, eY, finSuccPiHomeomorph, eX, Prod.map]
      have hhomeoY : IsOpenQuotientMap eY := eY.isOpenQuotientMap
      -- Compose: `Fin n.succ → ℝ` --eX--> `ℝ × (Fin n → ℝ)` --Prod.map--> ...
      --   --> `Fin n.succ → UnitAddCircle` via the homeomorphism.
      simpa [hconj] using
        (IsOpenQuotientMap.comp hhomeoY (IsOpenQuotientMap.comp hprod heX))

theorem measurePreserving_coeFun (n : ℕ) (t : ℝ) :
    MeasurePreserving (coeFun n)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)))
      (volume : Measure (UnitAddTorus (Fin n))) := by
  -- `coeFun` is the product of the coordinatewise quotient maps `ℝ → UnitAddCircle`,
  -- each of which is measure-preserving on a fundamental interval.
  simpa [coeFun] using
    (MeasureTheory.measurePreserving_pi
      (μ := fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)))
      (ν := fun _ : Fin n => (volume : Measure UnitAddCircle))
      (hf := fun _ => UnitAddCircle.measurePreserving_mk t))

theorem volume_restrict_pi_eq_pi_restrict (n : ℕ) (t : ℝ) :
    (volume : Measure (Fin n → ℝ)).restrict (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) =
      Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)) := by
  simpa using
    (Measure.restrict_pi_pi
      (μ := fun _ : Fin n => (volume : Measure ℝ))
      (s := fun _ : Fin n => Set.Ioc t (t + 1)))

theorem mFourier_apply_coeFun (n : ℕ) (k : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier k (coeFun n x) =
      Complex.exp
        (2 * π * Complex.I *
          (∑ i : Fin n, (k i : ℝ) * x i)) := by
  -- Unfold, then rewrite `fourier` explicitly on real representatives and use `exp_sum`.
  simpa [UnitAddTorus.mFourier, ContinuousMap.coe_mk, coeFun, fourier_coe_apply, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using
    (Complex.exp_sum (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => 2 * π * Complex.I * ((k i : ℝ) * x i))).symm

/--
Evaluate the additive character `mFourier k` on a point `x : ℝ^n`
viewed in the torus via `coeFun`.
-/
public theorem mFourier_apply_coeFun_ofLp (n : ℕ) (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    UnitAddTorus.mFourier k (coeFun n (WithLp.ofLp x)) =
      Complex.exp
        (2 * π * Complex.I *
          (∑ i : Fin n, (k i : ℝ) * x i)) := by
  simpa using (mFourier_apply_coeFun (n := n) (k := k) (x := WithLp.ofLp x))

/--
Pull back Haar integration on `(ℝ/ℤ)^n` to the fundamental cube `∏ i, (t, t+1] ⊆ ℝ^n`.
-/
public theorem integral_eq_integral_preimage_coeFun (n : ℕ) (t : ℝ) (g : UnitAddTorus (Fin n) → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure (UnitAddTorus (Fin n)))) :
    (∫ y : UnitAddTorus (Fin n), g y) =
      ∫ x, g (coeFun n x) ∂(volume : Measure (Fin n → ℝ)).restrict
        (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) := by
  have hmp :
      MeasurePreserving (coeFun n)
        (Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)))
        (volume : Measure (UnitAddTorus (Fin n))) :=
    measurePreserving_coeFun n t
  have h1 :
      (∫ y : UnitAddTorus (Fin n), g y) =
        ∫ x, g (coeFun n x) ∂(Measure.pi fun _ : Fin n =>
          (volume : Measure ℝ).restrict (Set.Ioc t (t + 1))) := by
    rw [← hmp.map_eq]
    simpa using
      (MeasureTheory.integral_map (hφ := hmp.aemeasurable) (f := g)
        (hfm := by simpa [hmp.map_eq] using hg))
  have hμ :
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1))) =
        (volume : Measure (Fin n → ℝ)).restrict (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) :=
    (volume_restrict_pi_eq_pi_restrict n t).symm
  simpa [hμ] using h1

end SchwartzMap.UnitAddTorus
