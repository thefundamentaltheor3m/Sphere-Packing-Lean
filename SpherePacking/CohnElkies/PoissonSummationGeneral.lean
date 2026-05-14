module
public import SpherePacking.CohnElkies.PoissonSummationLattices.PoissonSummation
public import SpherePacking.ForMathlib.FourierLinearEquiv
public import Mathlib.Topology.MetricSpace.Bounded

public import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! # Poisson summation for Schwartz functions

Three layers:

* `SchwartzMap.PoissonSummation.Standard` — periodization, descent to the torus, Schwartz decay
  bounds, and Poisson summation over the standard `ℤ^d` lattice.
* `SchwartzMap.PoissonSummationLattices` — Poisson summation over a full-rank `ℤ`-lattice
  `L ⊆ ℝ^d`, obtained from the standard case via a linear equivalence sending `ℤ^d` to `L`.
-/

open scoped BigOperators FourierTransform Real

open MeasureTheory Module UnitAddTorus SchwartzMap.PoissonSummation.Standard

namespace SchwartzMap.PoissonSummation.Standard

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Λ" => SchwartzMap.standardLattice d

/-! ## Basic infrastructure (merged from `PoissonSummationSchwartz.Basic`) -/

/-- Equivalence between integer vectors `Fin d → ℤ` and the standard lattice `Λ = ℤ^d ⊆ ℝ^d`. -/
@[expose] public noncomputable def equivIntVec : (Fin d → ℤ) ≃ Λ :=
  Equiv.ofBijective
    (fun n : Fin d → ℤ => ⟨intVec (d := d) n, intVec_mem_standardLattice (d := d) n⟩)
    ⟨fun a b hab => funext fun i => by
      simpa [intVec_apply] using congrArg (fun x : E => x i) (congrArg Subtype.val hab),
    fun ℓ =>
      let ⟨n, hn⟩ := exists_intVec_eq_of_mem_standardLattice (d := d) (x := (ℓ : E)) ℓ.property
      ⟨n, Subtype.ext hn.symm⟩⟩

variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))

public instance instMeasurableVAdd_standardLattice : MeasurableVAdd Λ E where
  measurable_const_vadd c := by
    simpa [Submodule.vadd_def, vadd_eq_add] using (continuous_const.add continuous_id).measurable
  measurable_vadd_const x := by simpa [Submodule.vadd_def, vadd_eq_add] using
    (continuous_subtype_val.add continuous_const).measurable

public instance instVAddInvariantMeasure_standardLattice :
    MeasureTheory.VAddInvariantMeasure Λ E (volume : Measure E) where
  measure_preimage_vadd c s hs := by
    simp [Submodule.vadd_def, vadd_eq_add, MeasureTheory.measure_preimage_add]

/-- Translate the Schwartz function `f` by a lattice vector, as a continuous map. -/
@[expose] public noncomputable def translate (ℓ : Λ) : C(E, ℂ) :=
  (⟨f, f.continuous⟩ : C(E, ℂ)).comp (ContinuousMap.addRight (ℓ : E))

@[simp] public lemma translate_apply (ℓ : Λ) (x : E) :
    translate (d := d) f ℓ x = f (x + (ℓ : E)) := rfl

/-- Only finitely many standard lattice points lie in a closed ball of radius `r`. -/
public lemma finite_norm_le_lattice (r : ℝ) :
    ( {ℓ : Λ | ‖(ℓ : E)‖ ≤ r} : Set _ ).Finite := by
  haveI : DiscreteTopology ((Λ).toAddSubgroup) := (inferInstance : DiscreteTopology Λ)
  have hfinE : Set.Finite (Metric.closedBall (0 : E) r ∩ ((Λ).toAddSubgroup : Set E)) :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall AddSubgroup.isClosed_of_discrete
  let e : Λ ↪ E := ⟨fun ℓ => (ℓ : E), Subtype.coe_injective⟩
  refine (Set.Finite.preimage_embedding e
    (by simpa [Submodule.coe_toAddSubgroup] using hfinE)).subset fun ℓ hℓ => by
      simpa [e, Metric.mem_closedBall, dist_eq_norm] using hℓ

/-- Schwartz decay: sup norms of translates restricted to a compact `K` are summable. -/
public lemma summable_norm_translate_restrict (K : TopologicalSpace.Compacts E) :
    Summable (fun ℓ : Λ => ‖(translate (d := d) f ℓ).restrict K‖) := by
  let k : ℕ := Module.finrank ℤ Λ + 1
  obtain ⟨C, hCpos, hC⟩ := f.decay k 0
  simp_rw [norm_iteratedFDeriv_zero] at hC
  obtain ⟨r, hrK⟩ := K.isCompact.isBounded.subset_closedBall (0 : E)
  let r0 : ℝ := max r 0
  have hrK0 : (K : Set E) ⊆ Metric.closedBall (0 : E) r0 :=
    fun x hx => Metric.closedBall_subset_closedBall (le_max_left r 0) (hrK hx)
  have h_event : ∀ᶠ ℓ : Λ in Filter.cofinite,
      ‖(translate (d := d) f ℓ).restrict K‖ ≤ (C * (2 ^ k : ℝ)) * (‖(ℓ : E)‖⁻¹ ^ k) := by
    filter_upwards [(finite_norm_le_lattice (d := d) (r := max (2 * r0) 1)
      ).eventually_cofinite_notMem] with ℓ hℓ
    have hRlt : max (2 * r0) 1 < ‖(ℓ : E)‖ := lt_of_not_ge (by simpa using hℓ)
    have hnorm_lt : 2 * r0 < ‖(ℓ : E)‖ := lt_of_le_of_lt (le_max_left _ _) hRlt
    have hnorm_pos : 0 < ‖(ℓ : E)‖ := lt_trans (by positivity) hRlt
    refine (ContinuousMap.norm_le _ (by positivity)).2 ?_
    rintro ⟨x, hxK⟩
    have hxnorm : ‖(x : E)‖ ≤ r0 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hrK0 hxK
    have hnorm_ge : (1 / 2 : ℝ) * ‖(ℓ : E)‖ ≤ ‖(x + (ℓ : E))‖ := by
      have hsub : ‖(ℓ : E)‖ - ‖(x : E)‖ ≤ ‖(ℓ : E) + x‖ := by
        simpa [add_comm] using norm_sub_norm_le (ℓ : E) (-x)
      simpa [add_comm] using (by nlinarith : (1 / 2 : ℝ) * ‖(ℓ : E)‖ ≤ ‖(ℓ : E) + x‖)
    have hpow_pos : 0 < ‖(x + (ℓ : E))‖ ^ k :=
      pow_pos ((by positivity : 0 < (1 / 2 : ℝ) * ‖(ℓ : E)‖).trans_le hnorm_ge) _
    have hinv : (‖(x + (ℓ : E))‖ ^ k)⁻¹ ≤ (2 ^ k : ℝ) * (‖(ℓ : E)‖⁻¹ ^ k) := by
      simpa [one_div, mul_pow, inv_pow, mul_inv_rev, mul_comm] using
        one_div_le_one_div_of_le (pow_pos (mul_pos (by positivity) hnorm_pos) _)
          (pow_le_pow_left₀ (by positivity) hnorm_ge k)
    calc ‖(translate (d := d) f ℓ) (⟨x, hxK⟩ : K)‖
        = ‖f (x + (ℓ : E))‖ := by simp [translate]
      _ ≤ C / (‖(x + (ℓ : E))‖ ^ k) := (le_div_iff₀' hpow_pos).2 (hC (x + (ℓ : E)))
      _ ≤ (C * (2 ^ k : ℝ)) * (‖(ℓ : E)‖⁻¹ ^ k) := by
        simpa [div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_left hinv hCpos.le
  refine Summable.of_norm_bounded_eventually
    (((by simpa [k] using ZLattice.summable_norm_pow_inv (L := Λ) (n := k) (Nat.lt_succ_self _)
        : Summable (fun ℓ : Λ => (‖(ℓ : E)‖⁻¹ ^ k : ℝ))).mul_left (C * (2 ^ k : ℝ)))) ?_
  filter_upwards [h_event] with ℓ hℓ
  simpa [Real.norm_of_nonneg (by positivity)] using hℓ

/-- Periodization of a Schwartz function along the standard lattice. -/
@[expose] public noncomputable def periodized : C(E, ℂ) :=
  ∑' ℓ : Λ, translate (d := d) f ℓ

public lemma periodized_apply (x : E) :
    periodized (d := d) f x = ∑' ℓ : Λ, f (x + (ℓ : E)) := by
  simpa [periodized, translate_apply] using
    (ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm
      (summable_norm_translate_restrict (d := d) f)) x).symm

/-- The quotient map `E = ℝ^d → (ℝ/ℤ)^d`, bundled as a continuous map. -/
@[expose] public noncomputable def coeFunEC : C(E, UnitAddTorus (Fin d)) :=
  ⟨coeFunE (d := d), continuous_coeFunE⟩

/-- The periodization is invariant under lattice translates, so it factors through the torus. -/
public lemma periodized_factorsThrough :
    Function.FactorsThrough (periodized (d := d) f) (coeFunEC (d := d)) := fun x y hxy => by
  obtain ⟨n, hn⟩ := exists_intVec_eq_sub_of_coeFunE_eq (d := d) (x := x) (y := y)
    (by simpa [coeFunEC] using hxy)
  simpa [show x = y + intVec (d := d) n by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      congrArg (fun t => t + y) hn] using
    show periodized (d := d) f (y + (⟨_, intVec_mem_standardLattice (d := d) n⟩ : Λ)) =
        periodized (d := d) f y by
      simpa [periodized_apply (d := d) f, add_assoc] using
        (Equiv.addLeft (⟨_, intVec_mem_standardLattice (d := d) n⟩ : Λ)).tsum_eq
          fun ℓ => f (y + (ℓ : E))

/-- Descend the periodization to the torus `(ℝ/ℤ)^d` via the quotient. -/
@[expose] public noncomputable def descended : C(UnitAddTorus (Fin d), ℂ) :=
  Topology.IsQuotientMap.lift (hf := (show IsOpenQuotientMap (coeFunE (d := d)) by
      simpa [coeFunE] using IsOpenQuotientMap.comp (UnitAddTorus.isOpenQuotientMap_coeFun d)
        (PiLp.homeomorph (p := (2 : ENNReal))
          (β := fun _ : Fin d ↦ ℝ)).isOpenQuotientMap).isQuotientMap)
    (g := periodized (d := d) f) (periodized_factorsThrough (d := d) (f := f))

/-- Compatibility of `descended` with `coeFunE`: pulling back gives `periodized`. -/
public lemma descended_comp (x : E) :
    descended (d := d) f (coeFunE (d := d) x) = periodized (d := d) f x :=
  congrArg (fun g : C(E, ℂ) => g x)
    (by simp [descended] : (descended (d := d) f).comp (coeFunEC (d := d)) = periodized (d := d) f)

public lemma mFourier_neg_apply_coeFunE (n : Fin d → ℤ) (x : E) :
    UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) =
      (𝐞 (-(inner ℝ x (intVec (d := d) n))) : ℂ) := by
  simp [coeFunE, UnitAddTorus.mFourier_apply_coeFun_ofLp,
    Real.fourierChar_apply, intVec, PiLp.inner_apply,
    Finset.sum_neg_distrib, mul_assoc, mul_comm]

@[simp] lemma intVec_neg (n : Fin d → ℤ) :
    intVec (d := d) (-n) = -intVec (d := d) n := by ext i; simp [intVec_apply]

public lemma mFourier_apply_coeFunE_exp (n : Fin d → ℤ) (x : E) :
    UnitAddTorus.mFourier n (coeFunE (d := d) x) =
      Complex.exp (2 * Real.pi * Complex.I * ⟪x, intVec (d := d) n⟫_[ℝ]) := by
  simpa [Real.fourierChar_apply, mul_assoc, mul_comm, inner_neg_right,
    RCLike.inner_eq_wInner_one x (intVec n)] using
    mFourier_neg_apply_coeFunE (d := d) (n := -n) (x := x)

public lemma mFourier_neg_apply_coeFunE_add_standardLattice (n : Fin d → ℤ) (ℓ : Λ) (x : E) :
    UnitAddTorus.mFourier (-n) (coeFunE (d := d) (x + (ℓ : E))) =
      UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) :=
  let ⟨m, hm⟩ := exists_intVec_eq_of_mem_standardLattice (d := d) (x := (ℓ : E)) ℓ.property
  by simp [hm]

public lemma iocCube_subset_closedBall :
    iocCube (d := d) ⊆ Metric.closedBall (0 : E) (Real.sqrt d) := fun x hx => by
  simpa [Metric.mem_closedBall, dist_eq_norm, EuclideanSpace.norm_eq] using
    Real.sqrt_le_sqrt (show (∑ i : Fin d, ‖x i‖ ^ 2) ≤ (d : ℝ) by
      simpa using (Finset.sum_le_sum fun i _ => show ‖x i‖ ^ 2 ≤ (1 : ℝ) by
        nlinarith [norm_nonneg (x i), show ‖x i‖ ≤ (1 : ℝ) by
          simpa [Real.norm_eq_abs, abs_of_nonneg (hx i).1.le] using (hx i).2]).trans_eq (by simp))

public lemma volume_iocCube_lt_top : (volume : Measure E) (iocCube (d := d)) < ⊤ :=
  ((Metric.isBounded_closedBall (x := (0 : E)) (r := Real.sqrt d)).subset
    (iocCube_subset_closedBall (d := d))).measure_lt_top

public lemma integrableOn_mFourier_mul_translate_iocCube (n : Fin d → ℤ) (ℓ : Λ) :
    IntegrableOn
        (fun x : E => UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f (x + (ℓ : E)))
        (iocCube (d := d)) (volume : Measure E) := by
  let K : TopologicalSpace.Compacts E :=
    ⟨Metric.closedBall (0 : E) (Real.sqrt d), isCompact_closedBall (0 : E) (Real.sqrt d)⟩
  refine Measure.integrableOn_of_bounded (μ := (volume : Measure E))
    (s := iocCube (d := d)) (s_finite := (volume_iocCube_lt_top (d := d)).ne)
    (M := ‖(translate (d := d) f ℓ).restrict K‖)
    (((UnitAddTorus.mFourier (-n)).continuous.comp (continuous_coeFunE (d := d))).mul
        (f.continuous.comp (continuous_id.add continuous_const))).aestronglyMeasurable
    (ae_restrict_of_forall_mem (measurableSet_iocCube (d := d)) fun x hx => ?_)
  calc ‖UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f (x + (ℓ : E))‖
      ≤ 1 * ‖f (x + (ℓ : E))‖ := by
        rw [norm_mul]; gcongr
        simpa [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using
          ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n)) _
    _ ≤ ‖(translate (d := d) f ℓ).restrict K‖ := by
      simpa [translate_apply, ContinuousMap.restrict_apply] using
        ContinuousMap.norm_coe_le_norm ((translate (d := d) f ℓ).restrict K)
          ⟨x, iocCube_subset_closedBall (d := d) hx⟩

/-! ## Standard Poisson summation (merged from `PoissonSummationSchwartz.PoissonSummation`) -/

section StandardPoissonSummation

open UnitAddTorus PoissonSummation.Standard

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

end StandardPoissonSummation

end SchwartzMap.PoissonSummation.Standard

namespace SchwartzMap

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The dual `ℤ`-lattice with respect to the Euclidean inner product. -/
public noncomputable abbrev dualLattice (L : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (B := (innerₗ E : LinearMap.BilinForm ℝ E)) L

noncomputable def zBasis (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Basis (Fin d) ℤ L :=
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  (Module.Free.chooseBasis ℤ L).reindex <| Fintype.equivOfCardEq <| by
    simpa [(ZLattice.rank (K := ℝ) (L := L)).trans (by simp : _ = d)] using
      (Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := L)).symm

noncomputable def rBasis (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Basis (Fin d) ℝ E := (zBasis (d := d) L).ofZLatticeBasis ℝ L

noncomputable def stdBasis : Basis (Fin d) ℝ E := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

noncomputable def A (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] : E ≃ₗ[ℝ] E :=
  (stdBasis (d := d)).equiv (rBasis (d := d) L) (Equiv.refl (Fin d))

@[simp] lemma A_apply_stdBasis (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : Fin d) : (A (d := d) L) ((stdBasis (d := d)) i) = (rBasis (d := d) L) i := by
  simpa [A, stdBasis, rBasis] using Basis.equiv_apply
    (b := stdBasis (d := d)) (b' := rBasis (d := d) L) (e := Equiv.refl _) (i := i)

lemma map_standardLattice_eq (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Submodule.map ((A (d := d) L).toLinearMap.restrictScalars ℤ)
        (SchwartzMap.standardLattice d) = L := calc
    Submodule.map ((A (d := d) L).toLinearMap.restrictScalars ℤ) (SchwartzMap.standardLattice d) =
        Submodule.span ℤ ((fun a : E => (A (d := d) L) a) '' Set.range (stdBasis (d := d))) := by
          simp [SchwartzMap.standardLattice, stdBasis, Submodule.map_span]
    _ = Submodule.span ℤ (Set.range (rBasis (d := d) L)) := by
        rw [show (fun a : E => (A (d := d) L) a) '' (Set.range (stdBasis (d := d))) =
            Set.range (rBasis (d := d) L) from by
          simpa [show (fun a : E => (A (d := d) L) a) ∘ stdBasis (d := d) = rBasis (d := d) L from
            by funext i; simp [Function.comp]] using
            (Set.range_comp (g := fun a : E => (A (d := d) L) a) (f := stdBasis (d := d))).symm]
    _ = L := by simpa [rBasis] using
        Module.Basis.ofZLatticeBasis_span (K := ℝ) (L := L) (b := zBasis (d := d) L)

section CovolumeDet

variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]

lemma covolume_eq_abs_det_A :
    ZLattice.covolume L =
      abs ((LinearMap.det : (E →ₗ[ℝ] E) →* ℝ) ((A L).toLinearMap)) := by
  have hvol : (volume : Measure E).real
      (ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis)) = 1 := by
    let f : E ≃L[ℝ] (Fin d → ℝ) := EuclideanSpace.equiv (Fin d) ℝ
    simpa [show f ⁻¹' (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d))) =
        ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis) by
      rw [show ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)) =
          f.toLinearEquiv '' ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
        from by simpa [show ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis).map f.toLinearEquiv =
            Pi.basisFun ℝ (Fin d) from rfl] using
          (ZSpan.map_fundamentalDomain
            (b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis) f.toLinearEquiv).symm]
      exact Set.preimage_image_eq _ f.injective, ZSpan.volume_real_fundamentalDomain,
      show (Matrix.of (Pi.basisFun ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ) = 1 by
        ext; simp [Matrix.of_apply, Matrix.one_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm]]
      using (show MeasurePreserving (fun x : E => (f x)) volume volume by
        simpa [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using
          PiLp.volume_preserving_ofLp (ι := Fin d)).measureReal_preimage
      (ZSpan.fundamentalDomain_measurableSet (b := (Pi.basisFun ℝ (Fin d)))).nullMeasurableSet
  have hr : rBasis (d := d) L = fun i : Fin d => (zBasis (d := d) L i : E) :=
    funext fun i => by simp [rBasis]
  have hcovol : ZLattice.covolume L =
      |(stdBasis (d := d)).det (fun i : Fin d => (zBasis (d := d) L i : E))| := by
    simpa [stdBasis, hvol] using
      ZLattice.covolume_eq_det_mul_measureReal (L := L) (b := zBasis (d := d) L)
        (b₀ := stdBasis (d := d)) (μ := (volume : Measure E))
  rw [hcovol, ← hr]; simp [A, stdBasis]

end CovolumeDet

section PoissonSummationLattices

variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]

noncomputable def Aₗ : E ≃ₗ[ℝ] E := A L
noncomputable def Bₗ : E →ₗ[ℝ] E := (Aₗ L).symm.toLinearMap.adjoint
noncomputable def Aadjₗ : E →ₗ[ℝ] E := (Aₗ L).toLinearMap.adjoint

noncomputable def equivStandardLattice : SchwartzMap.standardLattice d ≃ₗ[ℤ] L :=
  (LinearEquiv.restrictScalars ℤ (Aₗ L)).ofSubmodules (SchwartzMap.standardLattice d) L
    (by simpa [LinearEquiv.restrictScalars_apply] using map_standardLattice_eq (d := d) L)

@[simp] lemma equivStandardLattice_apply (x : SchwartzMap.standardLattice d) :
    ((equivStandardLattice (d := d) L x : L) : E) = (Aₗ L) x := by simp [equivStandardLattice]

lemma Bₗ_comp_Aadjₗ : (Bₗ L ∘ₗ Aadjₗ L) = (LinearMap.id : E →ₗ[ℝ] E) := by
  simp [Bₗ, Aadjₗ, ← LinearMap.adjoint_comp,
    show (Aₗ L).toLinearMap ∘ₗ (Aₗ L).symm.toLinearMap = LinearMap.id from by ext x; simp]

noncomputable def adjointSymmEquiv : E ≃ₗ[ℝ] E where
  toLinearMap := Bₗ L
  invFun := Aadjₗ L
  left_inv x := by
    simpa using congrArg (fun f : E →ₗ[ℝ] E => f x) (show Aadjₗ L ∘ₗ Bₗ L = LinearMap.id by
      simp [Bₗ, Aadjₗ, ← LinearMap.adjoint_comp,
        show (Aₗ L).symm.toLinearMap ∘ₗ (Aₗ L).toLinearMap = LinearMap.id from by ext x; simp])
  right_inv x := by simpa using congrArg (fun f : E →ₗ[ℝ] E => f x) (Bₗ_comp_Aadjₗ L)

lemma map_standardLattice_adjointSymm_eq_dualSubmodule :
    Submodule.map ((Bₗ L).restrictScalars ℤ) (standardLattice d) = dualLattice (d := d) L := by
  ext x
  have hdualStd : dualLattice (d := d) (standardLattice d) = standardLattice d := by
    simpa [dualLattice] using PoissonSummation.Standard.dualSubmodule_standardLattice_eq (d := d)
  refine ⟨?_, fun hx => ⟨(Aadjₗ L) x, ?_, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩ z hz
    obtain ⟨w, hw, rfl⟩ : (z : E) ∈
        Submodule.map ((Aₗ L).toLinearMap.restrictScalars ℤ) (standardLattice d) := by
      simpa [Aₗ, map_standardLattice_eq (d := d) L] using hz
    simpa [dualLattice, innerₗ_apply_apply,
      show inner ℝ ((Bₗ L) y) ((Aₗ L) w) = inner ℝ y w from by
        simpa [Bₗ, Aₗ] using LinearMap.adjoint_inner_left
          ((Aₗ L).symm.toLinearMap) ((Aₗ L) w) y] using
      (by simpa [hdualStd] using hy : y ∈ dualLattice (d := d) (standardLattice d)) w hw
  · suffices hydual : (Aadjₗ L) x ∈ dualLattice (d := d) (standardLattice d) by
      simpa [hdualStd] using hydual
    intro w hw
    have hwL : (Aₗ L) w ∈ L := by
      have : (Aₗ L) w ∈ Submodule.map ((Aₗ L).toLinearMap.restrictScalars ℤ)
          (standardLattice d) := ⟨w, hw, rfl⟩
      simpa [Aₗ, map_standardLattice_eq (d := d) L] using this
    simpa [dualLattice, innerₗ_apply_apply,
      show inner ℝ ((Aadjₗ L) x) w = inner ℝ x ((Aₗ L) w) from by
        simpa [Aadjₗ, Aₗ] using LinearMap.adjoint_inner_left ((Aₗ L).toLinearMap) w x] using
      hx ((Aₗ L) w) hwL
  · simpa using congrArg (fun f : E →ₗ[ℝ] E => f x) (Bₗ_comp_Aadjₗ L)

/-- Poisson summation over a full-rank `ℤ`-lattice `L`. -/
public theorem poissonSummation_lattice (f : SchwartzMap E ℂ) (v : E) :
    (∑' ℓ : L, f (v + (ℓ : E))) =
      (1 / ZLattice.covolume L) *
        ∑' m : dualLattice (d := d) L,
          (𝓕 (fun x : E => f x) m) * Complex.exp (2 * π * Complex.I * ⟪v, m⟫_[ℝ]) := by
  let A : E ≃ₗ[ℝ] E := Aₗ L
  let g : SchwartzMap E ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f
  have hlhs :
      (∑' ℓ : SchwartzMap.standardLattice d, g (A.symm v + (ℓ : E))) =
        ∑' ℓ : L, f (v + (ℓ : E)) := by
    rw [tsum_congr (fun ℓ : SchwartzMap.standardLattice d => by simp [g, map_add] :
      ∀ ℓ : SchwartzMap.standardLattice d, g (A.symm v + (ℓ : E)) = f (v + A (ℓ : E)))]
    simpa [equivStandardLattice_apply] using
      (equivStandardLattice (d := d) L).toEquiv.tsum_eq (f := fun ℓ : L => f (v + (ℓ : E)))
  have hrhs :
      (∑' n : Fin d → ℤ,
          (𝓕 (fun x : E => g x) (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n)) *
            Complex.exp
              (2 * π * Complex.I *
                ⟪A.symm v, SchwartzMap.PoissonSummation.Standard.intVec (d := d) n⟫_[ℝ])) =
        (1 / ZLattice.covolume L) *
          ∑' m : dualLattice (d := d) L,
            (𝓕 (fun x : E => f x) m) * Complex.exp (2 * π * Complex.I * ⟪v, m⟫_[ℝ]) := by
    let F : dualLattice (d := d) L → ℂ :=
      fun m => (𝓕 (fun x : E => f x) m) * Complex.exp (2 * π * Complex.I * ⟪v, m⟫_[ℝ])
    let detA : ℝ := (LinearMap.det : (E →ₗ[ℝ] E) →* ℝ) (A : E →ₗ[ℝ] E)
    let cC : ℂ := ((abs detA)⁻¹ : ℝ)
    let iv : (Fin d → ℤ) → E := SchwartzMap.PoissonSummation.Standard.intVec (d := d)
    have hfourier (w : E) : 𝓕 (fun x : E => g x) w =
        cC * 𝓕 (fun x : E => f x) ((Bₗ L) w) := by
      simpa [g, A, Bₗ, detA, cC, Complex.real_smul] using
        SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv
          (A := A) (f := fun x : E => f x) w
    have hexp (w : E) :
        Complex.exp (2 * π * Complex.I * ⟪A.symm v, w⟫_[ℝ]) =
          Complex.exp (2 * π * Complex.I * ⟪v, (Bₗ L) w⟫_[ℝ]) := by
      simp [show ⟪A.symm v, w⟫_[ℝ] = ⟪v, (Bₗ L) w⟫_[ℝ] by
        simpa [RCLike.inner_eq_wInner_one, A, Bₗ] using
          (LinearMap.adjoint_inner_right ((A.symm : E ≃ₗ[ℝ] E).toLinearMap) v w).symm]
    rw [show (∑' n : Fin d → ℤ, (𝓕 (fun x : E => g x) (iv n)) *
            Complex.exp (2 * π * Complex.I * ⟪A.symm v, iv n⟫_[ℝ])) =
          cC * ∑' m : dualLattice (d := d) L, F m from by
      rw [← (PoissonSummation.Standard.equivIntVec.trans
        ((LinearEquiv.restrictScalars ℤ (adjointSymmEquiv L)).ofSubmodules _ _ <| by
            simpa [LinearEquiv.restrictScalars_apply] using
              map_standardLattice_adjointSymm_eq_dualSubmodule (d := d)
                (L := L)).toEquiv).tsum_eq (f := F), ← tsum_mul_left]
      exact tsum_congr fun n ↦ by
        simpa [F, mul_assoc] using congrArg₂ (· * ·) (hfourier (w := iv n)) (hexp (w := iv n))]
    simp [F, cC, show ZLattice.covolume L = abs detA from by
      simpa [A, Aₗ, detA] using covolume_eq_abs_det_A (d := d) (L := L), one_div]
  simpa [hlhs, hrhs] using SchwartzMap.PoissonSummation.Standard.poissonSummation_standard
    (d := d) (f := g) (v := A.symm v)

end SchwartzMap.PoissonSummationLattices
