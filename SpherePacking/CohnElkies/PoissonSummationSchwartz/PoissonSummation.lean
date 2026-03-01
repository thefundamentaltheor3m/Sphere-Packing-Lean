module
public import SpherePacking.CohnElkies.PoissonSummationLattices.PoissonSummation
import SpherePacking.CohnElkies.PoissonSummationSchwartz.Basic


/-!
#### Fourier coefficients of the descended periodization

We compute the Fourier coefficient of the descended, periodized Schwartz function and identify it
with the Fourier transform of the original Schwartz function at integer frequencies.

Main result: `poissonSummation_standard`.
-/

open scoped BigOperators FourierTransform

open MeasureTheory

namespace SchwartzMap.PoissonSummation.Standard

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Λ" => SchwartzMap.standardLattice d

open UnitAddTorus

variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))


noncomputable def ball : TopologicalSpace.Compacts E :=
  ⟨Metric.closedBall (0 : E) (Real.sqrt d), isCompact_closedBall (0 : E) (Real.sqrt d)⟩

lemma norm_mFourier_mul_translate_le (n : Fin d → ℤ) (ℓ : Λ)
    (x : E) (hx : x ∈ SchwartzMap.PoissonSummation.Standard.iocCube (d := d)) :
    ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
          f (x + (ℓ : E))‖ ≤ ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖ := by
  have hxK : x ∈ (ball (d := d) : Set E) := (iocCube_subset_closedBall (d := d)) hx
  have hmFourier :
      ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x)‖ ≤ 1 := by
    simpa [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using
      (ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n))
        (PoissonSummation.Standard.coeFunE (d := d) x))
  have hsup :
      ‖f (x + (ℓ : E))‖ ≤ ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖ := by
    simpa [translate_apply, ContinuousMap.restrict_apply] using
      (ContinuousMap.norm_coe_le_norm ((translate (d := d) f ℓ).restrict (ball (d := d))) ⟨x, hxK⟩)
  calc
    ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
          f (x + (ℓ : E))‖
        = ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x)‖ *
            ‖f (x + (ℓ : E))‖ := by simp
    _ ≤ 1 * ‖f (x + (ℓ : E))‖ := by gcongr
    _ = ‖f (x + (ℓ : E))‖ := by simp
    _ ≤ ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖ := hsup

lemma summable_integral_norm_mFourier_mul_translate_iocCube (n : Fin d → ℤ) :
    Summable
        (fun ℓ : Λ =>
          ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
            ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
                f (x + (ℓ : E))‖ ∂(volume : Measure E)) := by
  let s : Set E := SchwartzMap.PoissonSummation.Standard.iocCube (d := d)
  let μ : Measure E := (volume : Measure E).restrict s
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ, s] using (volume_iocCube_lt_top (d := d))
  have hsum_norm :
      Summable (fun ℓ : Λ =>
        μ.real Set.univ * ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (summable_norm_translate_restrict (d := d) f (ball (d := d))).mul_left (μ.real Set.univ)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ℓ => ?_) hsum_norm
  have hle_ae :
      (fun x : E =>
        ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              f (x + (ℓ : E))‖) ≤ᵐ[μ] fun _ : E =>
        ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖ := by
    refine ae_restrict_of_forall_mem
      (SchwartzMap.PoissonSummation.Standard.measurableSet_iocCube (d := d)) ?_
    intro x hx
    exact norm_mFourier_mul_translate_le (d := d) (f := f) n ℓ x hx
  have hnonneg :
      (0 : E → ℝ) ≤ᵐ[μ] fun x : E =>
        ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              f (x + (ℓ : E))‖ :=
    ae_of_all _ (fun _ => by positivity)
  have hle' :
      (∫ x, ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              f (x + (ℓ : E))‖ ∂μ) ≤
        μ.real Set.univ * ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖ := by
    -- Bound by the integral of a constant function.
    have hle :
        (∫ x, ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
                f (x + (ℓ : E))‖ ∂μ) ≤
          ∫ x, ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖ ∂μ :=
      integral_mono_of_nonneg hnonneg
        (integrable_const ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖) hle_ae
    simpa [MeasureTheory.integral_const (μ := μ), smul_eq_mul, mul_comm] using hle
  -- Convert back to `∫ x in s, ...`.
  simpa [μ, s, mul_comm, mul_left_comm, mul_assoc] using hle'

lemma mFourierCoeff_descended (n : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (descended (d := d) f) n =
      𝓕 (fun x : E => f x) (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n) := by
  -- Pull back Haar integration on the torus to the cube in `E`.
  have hmeas :
      AEStronglyMeasurable
          (fun y : UnitAddTorus (Fin d) =>
            UnitAddTorus.mFourier (-n) y • (descended (d := d) f y))
          (volume : Measure (UnitAddTorus (Fin d))) :=
    ((UnitAddTorus.mFourier (-n)).continuous.smul (descended (d := d) f).continuous)
      |> fun h => h.aestronglyMeasurable
  have hpull :
      (∫ y : UnitAddTorus (Fin d),
            UnitAddTorus.mFourier (-n) y • (descended (d := d) f y)) =
        ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) •
            (descended (d := d) f (PoissonSummation.Standard.coeFunE (d := d) x))
            ∂(volume : Measure E) := integral_eq_integral_preimage_coeFunE
              (fun y => (UnitAddTorus.mFourier (-n)) y • (descended f) y) hmeas
  -- Expand `descended` back to the periodization on `E`, and swap `tsum` and integral.
  have hsum_int :
      (∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
            UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              (∑' ℓ : Λ, f (x + (ℓ : E))) ∂(volume : Measure E)) =
        ∑' ℓ : Λ,
          ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
            UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              f (x + (ℓ : E)) ∂(volume : Measure E) := by
    let s : Set E := SchwartzMap.PoissonSummation.Standard.iocCube (d := d)
    have hInt :
        ∀ ℓ : Λ,
          Integrable
              (fun x : E =>
                UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
                  f (x + (ℓ : E)))
              ((volume : Measure E).restrict s) := by
      intro ℓ
      simpa [IntegrableOn, s] using
        (integrableOn_mFourier_mul_translate_iocCube (d := d) (f := f) n ℓ)
    have hSum :
        Summable (fun ℓ : Λ =>
          ∫ x, ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
                f (x + (ℓ : E))‖ ∂((volume : Measure E).restrict s)) := by
      -- This is the required absolute convergence to justify Fubini.
      simpa [s] using
        (summable_integral_norm_mFourier_mul_translate_iocCube (d := d) (f := f) n)
    have :=
      (MeasureTheory.integral_tsum_of_summable_integral_norm
          (μ := (volume : Measure E).restrict s)
          (F := fun ℓ : Λ =>
            fun x : E =>
              UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
                f (x + (ℓ : E)))
          hInt hSum)
    -- `integral_tsum_of_summable_integral_norm` gives `tsum (∫...) = ∫ (tsum ...)`; rearrange.
    simpa [s, tsum_mul_left, mul_assoc] using this.symm
  -- Identify the sum of integrals with the integral over the whole space using the cube
  -- as a fundamental domain, exploiting periodicity of the kernel factor.
  have hFD :=
    (PoissonSummation.Standard.isAddFundamentalDomain_iocCube (d := d))
  have hint :
      Integrable
          (fun x : E =>
            UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) * f x)
          (volume : Measure E) := by
    have hf : Integrable (fun x : E => f x) (volume : Measure E) :=
      SchwartzMap.integrable (μ := (volume : Measure E)) f
    have hmeas :
        AEStronglyMeasurable
            (fun x : E =>
              UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x))
            (volume : Measure E) :=
      ((UnitAddTorus.mFourier (-n)).continuous.comp
        (PoissonSummation.Standard.continuous_coeFunE (d := d))).aestronglyMeasurable
    have hbound :
        ∀ᵐ x : E ∂(volume : Measure E),
          ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x)‖ ≤ (1 : ℝ) :=
      ae_of_all _ fun x => by
        simpa [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using
          (ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n))
            (PoissonSummation.Standard.coeFunE (d := d) x))
    simpa using (Integrable.bdd_mul (μ := (volume : Measure E)) hf hmeas hbound)
  have hFD' :
      ∑' ℓ : Λ,
          ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
            UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              f (x + (ℓ : E)) ∂(volume : Measure E) =
        ∫ x : E,
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) * f x
            ∂(volume : Measure E) := by
    -- Use `integral_eq_tsum''` for the fundamental domain on the integrable function
    -- `g x = mFourier(-n)(coeFunE x) * f x`, and rewrite each translate using periodicity.
    let g : E → ℂ :=
      fun x : E => UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) * f x
    have hmain :
        (∫ x : E, g x ∂(volume : Measure E)) =
          ∑' ℓ : Λ,
            ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d), g (ℓ +ᵥ x)
              ∂(volume : Measure E) := by
      simpa [g] using
        (MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum'' (μ := (volume : Measure E))
          hFD (f := g) hint)
    -- Rewrite the integrand `g (ℓ +ᵥ x)` as `mFourier(-n)(x) * f(x+ℓ)`.
    have hterm :
        ∀ ℓ : Λ,
          (∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d), g (ℓ +ᵥ x)
              ∂(volume : Measure E)) =
            ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
              UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
                f (x + (ℓ : E)) ∂(volume : Measure E) := by
      intro ℓ
      refine integral_congr_ae ?_
      refine ae_restrict_of_forall_mem
        (SchwartzMap.PoissonSummation.Standard.measurableSet_iocCube (d := d)) ?_
      intro x hx
      have hper' :
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) (x + (ℓ : E))) =
            UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) := by
        simpa using
          (mFourier_neg_apply_coeFunE_add_standardLattice (d := d) (n := n) (ℓ := ℓ) (x := x))
      calc
        g (ℓ +ᵥ x) =
            UnitAddTorus.mFourier (-n)
                (PoissonSummation.Standard.coeFunE (d := d) ((ℓ : E) + x)) *
              f ((ℓ : E) + x) := by
          simp [g, Submodule.vadd_def, vadd_eq_add]
        _ =
            UnitAddTorus.mFourier (-n)
                (PoissonSummation.Standard.coeFunE (d := d) (x + (ℓ : E))) *
              f (x + (ℓ : E)) := by
          simp [add_comm]
        _ =
            UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              f (x + (ℓ : E)) := by
          simp [hper']
    -- Combine.
    have hmain' := hmain.symm
    -- Replace the `tsum` termwise using `hterm`.
    simpa [g, hterm] using hmain'
  -- Put everything together and recognize the Fourier integral.
  calc
    UnitAddTorus.mFourierCoeff (descended (d := d) f) n
        = ∫ y : UnitAddTorus (Fin d), UnitAddTorus.mFourier (-n) y • descended (d := d) f y := by
            -- The Fourier-theory `mFourierCoeff` in Mathlib is defined using the probability Haar
            -- measure on `UnitAddCircle`, while this project works with the standard measure on
            -- `AddCircle 1`. These coincide as measures, but are not definitional equal as
            -- `MeasureSpace` instances, so we bridge them via equality of the induced `volume`s.
            simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul]
            haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
            have hμ_circle :
                (@volume UnitAddCircle instMeasureSpaceUnitAddCircle) =
                  (@volume UnitAddCircle (AddCircle.measureSpace (1 : ℝ))) := by
              change (AddCircle.haarAddCircle (T := (1 : ℝ)) : Measure UnitAddCircle) =
                (@volume UnitAddCircle (AddCircle.measureSpace (1 : ℝ)))
              simp [UnitAddCircle, AddCircle.volume_eq_smul_haarAddCircle]
            have hμ_torus :
                (@volume (UnitAddTorus (Fin d))
                    (@MeasureSpace.pi (Fin d) (Fin.fintype d) (fun _ => UnitAddCircle)
                      (fun _ => instMeasureSpaceUnitAddCircle))) =
                  (@volume (UnitAddTorus (Fin d))
                    (@MeasureSpace.pi (Fin d) (Fin.fintype d) (fun _ => UnitAddCircle)
                      (fun _ => AddCircle.measureSpace (1 : ℝ)))) := by
              -- Unfold `volume` on a finite product and rewrite each component by `hμ_circle`.
              change
                Measure.pi (fun _ : Fin d => @volume UnitAddCircle instMeasureSpaceUnitAddCircle) =
                  Measure.pi
                    (fun _ : Fin d =>
                      @volume UnitAddCircle (AddCircle.measureSpace (1 : ℝ)))
              exact congrArg Measure.pi (funext fun _ => hμ_circle)
            -- Rewrite the measure on the LHS; the remaining goal is definitional.
            simp [hμ_torus]
    _ = ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) •
            descended (d := d) f (PoissonSummation.Standard.coeFunE (d := d) x)
            ∂(volume : Measure E) := by
          simpa using hpull
    _ = ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
            (∑' ℓ : Λ, f (x + (ℓ : E))) ∂(volume : Measure E) := by
          -- `ℂ`-scalar multiplication is multiplication.
          refine integral_congr_ae ?_
          refine ae_restrict_of_forall_mem
            (SchwartzMap.PoissonSummation.Standard.measurableSet_iocCube (d := d)) ?_
          intro x hx
          simp [descended_comp (d := d) (f := f), periodized_apply (d := d) (f := f),
            smul_eq_mul]
    _ = ∑' ℓ : Λ,
          ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
            UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              f (x + (ℓ : E)) ∂(volume : Measure E) := by
          simpa using hsum_int
    _ = ∫ x : E,
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) * f x
            ∂(volume : Measure E) := by
          simpa using hFD'
    _ = 𝓕 (fun x : E => f x) (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n) := by
          -- Unfold the Fourier transform integral and identify the phase factor.
          simp [Real.fourier_eq, Circle.smul_def, smul_eq_mul,
            mFourier_neg_apply_coeFunE (d := d) (n := n)]

lemma summable_mFourierCoeff_descended :
    Summable (UnitAddTorus.mFourierCoeff (descended (d := d) f)) := by
  -- Reduce to summability of the Fourier transform on integer frequencies, using Schwartz decay.
  have hsum_norm :
      Summable (fun n : Fin d → ℤ =>
        ‖𝓕 (fun x : E => f x) (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n)‖) := by
    -- Prove absolute summability over the standard lattice and reindex by `intVec`.
    let k : ℕ := d + 1
    have hk : Module.finrank ℤ Λ < k := by
      have hrank : Module.finrank ℤ Λ = d := by
        have h := (ZLattice.rank (K := ℝ) (L := Λ))
        simpa using (h.trans (by simp))
      simp [hrank, k]
    -- Use decay of the Fourier transform (which is again a Schwartz function).
    obtain ⟨C, hCpos, hC⟩ := (FourierTransform.fourierCLE ℂ (SchwartzMap E ℂ) f).decay k 0
    have hC' : ∀ x : E, ‖x‖ ^ k * ‖𝓕 (fun y : E => f y) x‖ ≤ C := by
      simpa [FourierTransform.fourierCLE_apply, fourier_coe, norm_iteratedFDeriv_zero] using hC
    have hsum_pow :
        Summable (fun ℓ : Λ => (‖(ℓ : E)‖⁻¹ ^ k : ℝ)) := by
      simpa [k] using (ZLattice.summable_norm_pow_inv (L := Λ) (n := k) hk)
    have hsum_bd : Summable (fun ℓ : Λ => (C : ℝ) * (‖(ℓ : E)‖⁻¹ ^ k)) :=
      hsum_pow.mul_left C
    have hsum_lattice : Summable (fun ℓ : Λ => ‖𝓕 (fun y : E => f y) (ℓ : E)‖) := by
      -- Control the tail using the decay estimate (away from the finite set `‖ℓ‖ ≤ 1`).
      have hfin : ({ℓ : Λ | ‖(ℓ : E)‖ ≤ (1 : ℝ)} : Set _).Finite :=
        finite_norm_le_lattice (d := d) 1
      refine Summable.of_norm_bounded_eventually hsum_bd ?_
      filter_upwards [hfin.compl_mem_cofinite] with ℓ hℓ
      have hnorm_gt : (1 : ℝ) < ‖(ℓ : E)‖ := lt_of_not_ge (by simpa using hℓ)
      have hnorm_pos : 0 < ‖(ℓ : E)‖ := lt_trans (by positivity) hnorm_gt
      have hpow_pos : 0 < ‖(ℓ : E)‖ ^ k := pow_pos hnorm_pos _
      have hmain := hC' (ℓ : E)
      have : ‖𝓕 (fun y : E => f y) (ℓ : E)‖ ≤ C / (‖(ℓ : E)‖ ^ k) :=
        (le_div_iff₀' hpow_pos).2 hmain
      have hdiv :
          ‖𝓕 (fun y : E => f y) (ℓ : E)‖ ≤ (C : ℝ) * (‖(ℓ : E)‖⁻¹ ^ k) := by
        simpa [div_eq_mul_inv, inv_pow, one_div] using this
      -- Convert `‖‖z‖‖` to `‖z‖` (as a real number).
      simpa [Real.norm_of_nonneg (norm_nonneg _)] using hdiv
    -- Reindex from the standard lattice to integer vectors using `equivIntVec`.
    let e := (PoissonSummation.Standard.equivIntVec (d := d))
    have : Summable (fun n : Fin d → ℤ => ‖𝓕 (fun y : E => f y) ((e n : Λ) : E)‖) := by
      simpa using (Summable.comp_injective hsum_lattice e.injective)
    simpa [PoissonSummation.Standard.coe_equivIntVec] using this
  -- Convert from absolute summability to summability in `ℂ`, using the coefficient identity.
  refine (Summable.of_norm ?_)
  simpa [mFourierCoeff_descended (d := d) (f := f)] using hsum_norm

/-- Poisson summation for Schwartz functions over the standard lattice `ℤ^d`. -/
public theorem poissonSummation_standard (v : E) :
    (∑' ℓ : Λ, f (v + (ℓ : E))) =
      ∑' n : Fin d → ℤ,
        (𝓕 (fun x : E => f x) (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n)) *
          Complex.exp
            (2 * Real.pi * Complex.I *
              ⟪v, SchwartzMap.PoissonSummation.Standard.intVec (d := d) n⟫_[ℝ]) := by
  simpa [descended_comp (d := d) (f := f) v, periodized_apply (d := d) (f := f), smul_eq_mul,
    mFourierCoeff_descended (d := d) (f := f), mFourier_apply_coeFunE_exp (d := d), mul_assoc,
    mul_left_comm, mul_comm] using
    (UnitAddTorus.hasSum_mFourier_series_apply_of_summable
        (f := descended (d := d) f)
        (summable_mFourierCoeff_descended (d := d) (f := f))
        (coeFunE (d := d) v)).tsum_eq.symm

end SchwartzMap.PoissonSummation.Standard
