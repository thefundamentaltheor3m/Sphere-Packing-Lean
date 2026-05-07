module
public import SpherePacking.CohnElkies.PoissonSummationLattices.PoissonSummation
public import Mathlib.Topology.MetricSpace.Bounded

/-! Poisson summation of Schwartz functions on `ℝ^d` over full-rank `ℤ`-lattices. -/

open scoped BigOperators FourierTransform
open MeasureTheory UnitAddTorus SchwartzMap.PoissonSummation.Standard

namespace SchwartzMap.PoissonSummation.Standard

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Λ" => SchwartzMap.standardLattice d

/-- Equivalence between integer vectors `Fin d → ℤ` and the standard lattice `Λ = ℤ^d ⊆ ℝ^d`. -/
@[expose] public noncomputable def equivIntVec : (Fin d → ℤ) ≃ Λ :=
  Equiv.ofBijective
    (fun n : Fin d → ℤ => ⟨intVec (d := d) n, intVec_mem_standardLattice (d := d) n⟩)
    ⟨fun a b hab => funext fun i => by
      simpa [intVec_apply] using congrArg (fun x : E => x i) (congrArg Subtype.val hab),
    fun ℓ =>
      let ⟨n, hn⟩ := exists_intVec_eq_of_mem_standardLattice (d := d) (x := (ℓ : E)) ℓ.property
      ⟨n, Subtype.ext hn.symm⟩⟩

@[simp] public lemma coe_equivIntVec (n : Fin d → ℤ) :
    ((equivIntVec (d := d) n : Λ) : E) = intVec (d := d) n := rfl

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

@[simp] lemma periodized_vadd_eq (x : E) (ℓ₀ : Λ) :
    periodized (d := d) f (x + ℓ₀) = periodized (d := d) f x := by
  simpa [periodized_apply (d := d) f, add_assoc] using
    (Equiv.addLeft ℓ₀).tsum_eq fun ℓ => f (x + (ℓ : E))

/-- The quotient map `E = ℝ^d → (ℝ/ℤ)^d`, bundled as a continuous map. -/
@[expose] public noncomputable def coeFunEC : C(E, UnitAddTorus (Fin d)) :=
  ⟨coeFunE (d := d), continuous_coeFunE⟩

public lemma isQuotientMap_coeFunEC : Topology.IsQuotientMap (coeFunEC (d := d)) :=
  (isOpenQuotientMap_coeFunE (d := d)).isQuotientMap

/-- The periodization is invariant under lattice translates, so it factors through the torus. -/
public lemma periodized_factorsThrough :
    Function.FactorsThrough (periodized (d := d) f) (coeFunEC (d := d)) := fun x y hxy => by
  obtain ⟨n, hn⟩ := exists_intVec_eq_sub_of_coeFunE_eq (d := d) (x := x) (y := y)
    (by simpa [coeFunEC] using hxy)
  simpa [show x = y + intVec (d := d) n by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      congrArg (fun t => t + y) hn] using periodized_vadd_eq (d := d) (f := f) y
    ⟨_, intVec_mem_standardLattice (d := d) n⟩

/-- Descend the periodization to the torus `(ℝ/ℤ)^d` via the quotient. -/
@[expose] public noncomputable def descended : C(UnitAddTorus (Fin d), ℂ) :=
  Topology.IsQuotientMap.lift (hf := isQuotientMap_coeFunEC (d := d))
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

end SchwartzMap.PoissonSummation.Standard
