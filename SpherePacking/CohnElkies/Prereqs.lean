/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
/-
## THIS FILE SHOULD EVENTUALLY BE REMOVED AND THE REFERENCES IN COHN-ELKIES MUST BE REPLACED WITH
## THE RIGHT ONES (NOT THE ONES FROM HERE). THIS FILE IS JUST A TEMPORARY SOLUTION TO MAKE THE
## COHN-ELKIES FILE WORK.
-/
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.RCLike.Inner
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.MetricSpace.MetricSeparated

import SpherePacking.Basic.SpherePacking
import SpherePacking.Basic.PeriodicPacking
import SpherePacking.ForMathlib.InvPowSummability

open BigOperators Bornology Metric
open scoped FourierTransform SchwartzMap

variable {d : ℕ} [Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

section Euclidean_Space

instance instNonemptyFin : Nonempty (Fin d) := ⟨0, Fact.out⟩

end Euclidean_Space

open scoped FourierTransform

open Complex Real
open LinearMap (BilinForm)

noncomputable section PSF_L

/-
This section defines the Poisson Summation Formula, Lattice Version (`PSF_L`). This is a direct
dependency of the Cohn-Elkies proof.
-/

def PSF_Conditions (f : EuclideanSpace ℝ (Fin d) → ℂ) : Prop :=
  Summable f ∧
  sorry

theorem PSF_L {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : PSF_Conditions f)
    (v : EuclideanSpace ℝ (Fin d)) :
    ∑' ℓ : Λ, f (v + ℓ) = (1 / ZLattice.covolume Λ) *
      ∑' m : BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) Λ,
    (𝓕 f m) * exp (2 * π * I * ⟪v, m⟫_[ℝ]) :=
  sorry

theorem PSF_L' {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : PSF_Conditions f) :
    ∑' ℓ : Λ, f ℓ = (1 / ZLattice.covolume Λ) *
    ∑' m : BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) Λ, (𝓕 f m) := by
  simpa using PSF_L Λ hf 0

namespace SchwartzMap

theorem PoissonSummation_Lattices (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
    (v : EuclideanSpace ℝ (Fin d)) : ∑' ℓ : Λ, f (v + ℓ) = (1 / ZLattice.covolume Λ) *
    ∑' m : BilinForm.dualSubmodule
    (innerₗ (EuclideanSpace ℝ (Fin d))) Λ, (𝓕 ⇑f m) * exp (2 * π * I * ⟪v, m⟫_[ℝ]) := by
  sorry

end SchwartzMap

end PSF_L

open scoped FourierTransform

section FourierSchwartz

namespace SchwartzMap

variable (𝕜 : Type*) [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
    [CompleteSpace E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  (f : 𝓢(V, E))

include 𝕜 in
@[simp]
theorem fourierInversion : 𝓕⁻ (𝓕 ⇑f) = f :=
  f.continuous.fourierInv_fourier_eq f.integrable (fourierTransformCLM 𝕜 f).integrable

end SchwartzMap

end FourierSchwartz

section Positivity_on_Nhd

variable {E : Type*} [TopologicalSpace E]

theorem Continuous.pos_iff_exists_nhd_pos {f : E → ℝ} (hf₁ : Continuous f) (x : E) :
    0 < f x ↔ ∃ U ∈ nhds x, ∀ y ∈ U, 0 < f y :=
  ⟨fun hx => ⟨_, (hf₁.tendsto x).eventually (eventually_gt_nhds hx), fun _ h => h⟩,
   fun ⟨_, hU, h⟩ => h x (mem_of_mem_nhds hU)⟩

open MeasureTheory

variable [MeasureSpace E] [BorelSpace E]

theorem Continuous.pos_iff_exists_measurable_nhd_pos {f : E → ℝ} (hf₁ : Continuous f) (x : E) :
    0 < f x ↔ ∃ U ∈ nhds x, MeasurableSet U ∧ ∀ y ∈ U, 0 < f y :=
  ⟨fun hx => ⟨f ⁻¹' Set.Ioo (f x / 2) (3 * f x / 2),
    hf₁.continuousAt (Ioo_mem_nhds (by linarith) (by linarith)),
    hf₁.measurable measurableSet_Ioo, fun y hy => by linarith [hy.1]⟩,
   fun ⟨U, hU, _, h⟩ => (hf₁.pos_iff_exists_nhd_pos x).mpr ⟨U, hU, h⟩⟩

end Positivity_on_Nhd

section Integration

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [MeasureSpace E] [BorelSpace E]
variable [(volume : Measure E).IsAddLeftInvariant] [(volume : Measure E).Regular]
  [NeZero (volume : Measure E)]

instance : (volume : Measure E).IsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_regular

theorem Continuous.integral_zero_iff_zero_of_nonneg {f : E → ℝ} (hf₁ : Continuous f)
    (hf₂ : Integrable f) (hnn : ∀ x, 0 ≤ f x) : ∫ (v : E), f v = 0 ↔ f = 0 := by
  constructor
  · intro hintf
    by_contra hne
    obtain ⟨x, hneatx⟩ := Function.ne_iff.mp fun a => hne a.symm
    obtain ⟨U, hU₁, hU₃⟩ := (hf₁.pos_iff_exists_nhd_pos x).mp (lt_of_le_of_ne (hnn x) hneatx)
    have : 0 < ∫ (v : E) in U, f v := by
      rw [integral_pos_iff_support_of_nonneg hnn hf₂.restrict]
      calc 0 < volume U := Measure.measure_pos_of_mem_nhds volume hU₁
        _ = (volume.restrict U) (Function.support f) :=
            (Measure.restrict_apply_superset fun y hy => (hU₃ y hy).ne').symm
    linarith [setIntegral_le_integral (s := U) hf₂ (Eventually.of_forall hnn)]
  · intro hf; simp [hf]

example {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf₁ : Continuous f) (hf₂ : Integrable f)
    (hnn : ∀ x, 0 ≤ f x) : ∫ (v : EuclideanSpace ℝ (Fin d)), f v = 0 ↔ f = 0 :=
  hf₁.integral_zero_iff_zero_of_nonneg hf₂ hnn

namespace SchwartzMap

theorem toFun_eq_zero_iff_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : 𝓢(E, F)) : (f : E → F) = 0 ↔ f = 0 :=
  ⟨fun a => SchwartzMap.ext (congrFun a), fun h => by rw [h]; exact coeFn_zero⟩

omit [Fact (0 < d)] in
theorem integral_zero_iff_zero_of_nonneg {f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)}
    (hnn : ∀ x, 0 ≤ f x) : ∫ (v : EuclideanSpace ℝ (Fin d)), f v = 0 ↔ f = 0 := by
  simp [← f.toFun_eq_zero_iff_zero]
  exact f.continuous.integral_zero_iff_zero_of_nonneg f.integrable hnn

end SchwartzMap

end Integration

noncomputable section Misc

instance (v : EuclideanSpace ℝ (Fin d)) : Decidable (v = 0) := Classical.propDecidable (v = 0)

instance : DecidableEq (EuclideanSpace ℝ (Fin d)) :=
  Classical.typeDecidableEq (EuclideanSpace ℝ (Fin d))

omit [Fact (0 < d)]

local notation "conj" => starRingEnd ℂ

theorem Complex.exp_neg_real_I_eq_conj (x m : EuclideanSpace ℝ (Fin d)) :
    cexp (-(2 * ↑π * I * ↑⟪x, m⟫_[ℝ])) = conj (cexp (2 * ↑π * I * ↑⟪x, m⟫_[ℝ])) := by
  calc cexp (-(2 * ↑π * I * ↑⟪x, m⟫_[ℝ]))
      _ = Circle.exp (-2 * π * ⟪x, m⟫_[ℝ]) := by rw [Circle.coe_exp]; push_cast; ring_nf
      _ = conj (Circle.exp (2 * π * ⟪x, m⟫_[ℝ])) := by
          rw [mul_assoc, neg_mul, ← mul_assoc, ← Circle.coe_inv_eq_conj, Circle.exp_neg]
      _ = conj (cexp (2 * ↑π * I * ↑⟪x, m⟫_[ℝ])) := by
          rw [Circle.coe_exp]; congr 1; push_cast; ring_nf

lemma SchwartzMap.summableOn {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : 𝓢(E, V)) (X : Set E)
    (hX : ∃ ε > 0, IsSeparated ε X) : Summable (fun (x : X) => f x) := by
  sorry

theorem Continuous.re {α 𝕜 : Type*} [TopologicalSpace α] [RCLike 𝕜] {f : α → 𝕜}
    (hf : Continuous f) : Continuous (fun x ↦ RCLike.re (f x)) :=
  RCLike.continuous_re.comp hf

theorem Summable.re {α 𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜} (hf : Summable f) :
    Summable (fun x ↦ RCLike.re (f x)) :=
  (hf.norm.of_nonneg_of_le (fun _ => norm_nonneg _) fun _ => RCLike.norm_re_le_norm _).of_norm

lemma ZLattice.isSeparated {K : Type*} [NormedField K] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace K E] [FiniteDimensional K E] (J : Submodule ℤ E) [DiscreteTopology J]
    [_hJ : IsZLattice K J] : ∃ ε > 0, IsSeparated ε (SetLike.coe J) := by
  simp only [IsSeparated]
  obtain ⟨ε, hε_pos, hε_ball⟩ : ∃ ε > 0, ∀ x : E, x ∈ J → ‖x‖ < ε → x = 0 := by
    have h_discrete : ∀ᶠ x in nhds (0 : J), x = 0 := by
      simp +decide
    rw [Metric.eventually_nhds_iff] at h_discrete
    aesop
  refine ⟨ENNReal.ofReal (ε / 2), by positivity, ?_⟩
  simp_all +decide [edist_dist]
  intro x hx y hy hxy
  specialize hε_ball (x - y)
  simp_all +decide [sub_eq_zero]
  simpa only [dist_eq_norm] using
    lt_of_lt_of_le (half_lt_self hε_pos) (hε_ball (J.sub_mem hx hy))

lemma SpherePacking.centers_isSeparated (S : SpherePacking d) :
    IsSeparated ((ENNReal.ofReal S.separation) / 2) S.centers := by
  intro x hx y hy hxy
  have hle := S.centers_dist (Subtype.coe_ne_coe.mp hxy : (⟨x, hx⟩ : S.centers) ≠ ⟨y, hy⟩)
  simp only at hle
  rw [edist_dist]
  calc ENNReal.ofReal S.separation / 2
      < ENNReal.ofReal S.separation :=
        ENNReal.half_lt_self (ENNReal.ofReal_pos.mpr S.separation_pos).ne' ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (dist x y) := ENNReal.ofReal_le_ofReal hle

end Misc
