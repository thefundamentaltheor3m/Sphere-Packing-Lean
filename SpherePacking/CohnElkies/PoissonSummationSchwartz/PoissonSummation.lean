module
public import SpherePacking.CohnElkies.PoissonSummationLattices.PoissonSummation
import SpherePacking.CohnElkies.PoissonSummationSchwartz.Basic

/-! Poisson summation for Schwartz functions over the standard lattice. -/

open scoped BigOperators FourierTransform
open MeasureTheory

namespace SchwartzMap.PoissonSummation.Standard

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Λ" => SchwartzMap.standardLattice d

open UnitAddTorus PoissonSummation.Standard

variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))

noncomputable def ball : TopologicalSpace.Compacts E :=
  ⟨Metric.closedBall (0 : E) (Real.sqrt d), isCompact_closedBall (0 : E) (Real.sqrt d)⟩

lemma summable_integral_norm_mFourier_mul_translate_iocCube (n : Fin d → ℤ) :
    Summable
        (fun ℓ : Λ =>
          ∫ x in iocCube (d := d),
            ‖UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
                f (x + (ℓ : E))‖ ∂(volume : Measure E)) := by
  let s : Set E := iocCube (d := d)
  let μ : Measure E := (volume : Measure E).restrict s
  haveI : IsFiniteMeasure μ := ⟨by simpa [μ, s] using volume_iocCube_lt_top (d := d)⟩
  have hsum_norm : Summable (fun ℓ : Λ =>
      μ.real Set.univ * ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (summable_norm_translate_restrict (d := d) f (ball (d := d))).mul_left (μ.real Set.univ)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ℓ => ?_) hsum_norm
  simpa [μ, s, MeasureTheory.integral_const (μ := μ), smul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc] using integral_mono_of_nonneg (ae_of_all _ fun _ => by positivity)
      (integrable_const ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖)
      (ae_restrict_of_forall_mem (measurableSet_iocCube (d := d)) fun x hx => by
        have hmFourier : ‖UnitAddTorus.mFourier (-n) (coeFunE (d := d) x)‖ ≤ 1 := by
          simpa [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using
            ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n)) (coeFunE (d := d) x)
        simpa using (mul_le_mul hmFourier
          (by simpa [translate_apply, ContinuousMap.restrict_apply] using
              ContinuousMap.norm_coe_le_norm ((translate (d := d) f ℓ).restrict (ball (d := d)))
                ⟨x, iocCube_subset_closedBall (d := d) hx⟩ :
            ‖f (x + (ℓ : E))‖ ≤ ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖)
          (norm_nonneg _) (by norm_num)).trans (one_mul _).le)

lemma mFourierCoeff_descended (n : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (descended (d := d) f) n =
      𝓕 (fun x : E => f x) (intVec (d := d) n) := by
  have hpull : (∫ y : UnitAddTorus (Fin d), UnitAddTorus.mFourier (-n) y • descended (d := d) f y) =
        ∫ x in iocCube (d := d), UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) •
            descended (d := d) f (coeFunE (d := d) x) ∂(volume : Measure E) :=
    integral_eq_integral_preimage_coeFunE
      (fun y => UnitAddTorus.mFourier (-n) y • descended f y)
      ((UnitAddTorus.mFourier (-n)).continuous.smul
        (descended (d := d) f).continuous).aestronglyMeasurable
  have hsum_int :
      (∫ x in iocCube (d := d),
            UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
              (∑' ℓ : Λ, f (x + (ℓ : E))) ∂(volume : Measure E)) =
        ∑' ℓ : Λ,
          ∫ x in iocCube (d := d),
            UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
              f (x + (ℓ : E)) ∂(volume : Measure E) := by
    let s : Set E := iocCube (d := d)
    simpa [s, tsum_mul_left, mul_assoc] using
      (MeasureTheory.integral_tsum_of_summable_integral_norm
          (μ := (volume : Measure E).restrict s)
          (F := fun ℓ : Λ => fun x : E =>
            UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f (x + (ℓ : E)))
          (fun ℓ => by
            simpa [IntegrableOn, s] using
              (integrableOn_mFourier_mul_translate_iocCube (d := d) (f := f) n ℓ))
          (by simpa [s] using
            (summable_integral_norm_mFourier_mul_translate_iocCube (d := d) (f := f) n))).symm
  have hint : Integrable
      (fun x : E => UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f x)
      (volume : Measure E) := by
    simpa using Integrable.bdd_mul (μ := (volume : Measure E))
      (SchwartzMap.integrable (μ := (volume : Measure E)) f)
      (((UnitAddTorus.mFourier (-n)).continuous.comp
        (continuous_coeFunE (d := d))).aestronglyMeasurable)
      (ae_of_all _ fun x => by
        simpa [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using
          (ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n)) (coeFunE (d := d) x)))
  have hFD' : ∑' ℓ : Λ,
        ∫ x in iocCube (d := d),
          UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
            f (x + (ℓ : E)) ∂(volume : Measure E) =
        ∫ x : E, UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f x
          ∂(volume : Measure E) := by
    let g : E → ℂ := fun x : E => UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f x
    have hterm : ∀ ℓ : Λ,
        (∫ x in iocCube (d := d), g (ℓ +ᵥ x) ∂(volume : Measure E)) =
            ∫ x in iocCube (d := d),
              UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
                f (x + (ℓ : E)) ∂(volume : Measure E) := fun ℓ =>
      integral_congr_ae <| ae_restrict_of_forall_mem (measurableSet_iocCube (d := d)) fun x _ => by
        simp [g, Submodule.vadd_def, vadd_eq_add, add_comm,
          mFourier_neg_apply_coeFunE_add_standardLattice (d := d) (n := n) (ℓ := ℓ) (x := x)]
    simpa [g, hterm] using
      (MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum'' (μ := (volume : Measure E))
        (isAddFundamentalDomain_iocCube (d := d)) (f := g) hint).symm
  calc
    UnitAddTorus.mFourierCoeff (descended (d := d) f) n
        = ∫ y : UnitAddTorus (Fin d), UnitAddTorus.mFourier (-n) y • descended (d := d) f y := by
            simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul]
            haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
            simp [show (@volume (UnitAddTorus (Fin d))
                  (@MeasureSpace.pi (Fin d) (Fin.fintype d) (fun _ => UnitAddCircle)
                    (fun _ => instMeasureSpaceUnitAddCircle))) =
                (@volume (UnitAddTorus (Fin d))
                  (@MeasureSpace.pi (Fin d) (Fin.fintype d) (fun _ => UnitAddCircle)
                    (fun _ => AddCircle.measureSpace (1 : ℝ)))) from
              congrArg Measure.pi (funext fun _ => by
                change (AddCircle.haarAddCircle (T := (1 : ℝ)) : Measure UnitAddCircle) =
                  (@volume UnitAddCircle (AddCircle.measureSpace (1 : ℝ)))
                simp [UnitAddCircle, AddCircle.volume_eq_smul_haarAddCircle])]
    _ = ∫ x in iocCube (d := d),
          UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) •
            descended (d := d) f (coeFunE (d := d) x)
            ∂(volume : Measure E) := by
          simpa using hpull
    _ = ∫ x in iocCube (d := d),
          UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
            (∑' ℓ : Λ, f (x + (ℓ : E))) ∂(volume : Measure E) :=
          integral_congr_ae <| ae_restrict_of_forall_mem (measurableSet_iocCube (d := d))
            fun _ _ => by simp [descended_comp (d := d) (f := f),
              periodized_apply (d := d) (f := f), smul_eq_mul]
    _ = ∑' ℓ : Λ,
          ∫ x in iocCube (d := d),
            UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
              f (x + (ℓ : E)) ∂(volume : Measure E) := by
          simpa using hsum_int
    _ = ∫ x : E,
          UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f x
            ∂(volume : Measure E) := by
          simpa using hFD'
    _ = 𝓕 (fun x : E => f x) (intVec (d := d) n) := by
          simp [Real.fourier_eq, Circle.smul_def, smul_eq_mul,
            mFourier_neg_apply_coeFunE (d := d) (n := n)]

lemma summable_mFourierCoeff_descended :
    Summable (UnitAddTorus.mFourierCoeff (descended (d := d) f)) := by
  have hsum_norm : Summable (fun n : Fin d → ℤ =>
      ‖𝓕 (fun x : E => f x) (intVec (d := d) n)‖) := by
    let k : ℕ := d + 1
    have hk : Module.finrank ℤ Λ < k := by
      simp [show Module.finrank ℤ Λ = d from by
        simpa using (ZLattice.rank (K := ℝ) (L := Λ)).trans (by simp), k]
    obtain ⟨C, _, hC⟩ := (FourierTransform.fourierCLE ℂ (SchwartzMap E ℂ) f).decay k 0
    have hC' : ∀ x : E, ‖x‖ ^ k * ‖𝓕 (fun y : E => f y) x‖ ≤ C := by
      simpa [FourierTransform.fourierCLE_apply, fourier_coe, norm_iteratedFDeriv_zero] using hC
    have hsum_lattice : Summable (fun ℓ : Λ => ‖𝓕 (fun y : E => f y) (ℓ : E)‖) := by
      refine Summable.of_norm_bounded_eventually
        ((by simpa [k] using ZLattice.summable_norm_pow_inv (L := Λ) (n := k) hk :
          Summable (fun ℓ : Λ => (‖(ℓ : E)‖⁻¹ ^ k : ℝ))).mul_left C) ?_
      filter_upwards [(finite_norm_le_lattice (d := d) 1).compl_mem_cofinite] with ℓ hℓ
      have hnorm_pos : 0 < ‖(ℓ : E)‖ :=
        lt_trans (by positivity) (lt_of_not_ge (by simpa using hℓ) : (1 : ℝ) < ‖(ℓ : E)‖)
      simpa [Real.norm_of_nonneg (norm_nonneg _), div_eq_mul_inv, inv_pow, one_div] using
        (le_div_iff₀' (pow_pos hnorm_pos _)).2 (hC' (ℓ : E))
    simpa [equivIntVec] using
      hsum_lattice.comp_injective (equivIntVec (d := d)).injective
  exact Summable.of_norm (by simpa [mFourierCoeff_descended (d := d) (f := f)] using hsum_norm)

/-- Poisson summation for Schwartz functions over the standard lattice `ℤ^d`. -/
public theorem poissonSummation_standard (v : E) :
    (∑' ℓ : Λ, f (v + (ℓ : E))) =
      ∑' n : Fin d → ℤ,
        (𝓕 (fun x : E => f x) (intVec (d := d) n)) *
          Complex.exp
            (2 * Real.pi * Complex.I *
              ⟪v, intVec (d := d) n⟫_[ℝ]) := by
  simpa [descended_comp (d := d) (f := f) v, periodized_apply (d := d) (f := f), smul_eq_mul,
    mFourierCoeff_descended (d := d) (f := f), mFourier_apply_coeFunE_exp (d := d), mul_assoc,
    mul_left_comm, mul_comm] using
    (UnitAddTorus.hasSum_mFourier_series_apply_of_summable
        (f := descended (d := d) f)
        (summable_mFourierCoeff_descended (d := d) (f := f))
        (coeFunE (d := d) v)).tsum_eq.symm

end SchwartzMap.PoissonSummation.Standard
