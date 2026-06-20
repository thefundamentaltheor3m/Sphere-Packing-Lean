/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Auguste Poiroux
-/
module
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Summability of a Schwartz function over a `ℤ`-lattice

A Schwartz function on a finite-dimensional real normed space `E` is summable, in norm, over the
translates of any discrete `ℤ`-submodule `L ⊆ E`. This is the basic summability input to (general)
Poisson summation and to the Cohn–Elkies linear-programming bound.

The proof combines Schwartz decay (`SchwartzMap.decay`) with the convergent dominating series
`ZLattice.summable_norm_pow_inv`. It needs neither an inner-product structure, nor that `L` be a
full lattice (`IsZLattice`): only `[FiniteDimensional ℝ E]` and `[DiscreteTopology L]`.

We record the pointwise summability (`summable_norm_comp_add`) and the locally-uniform version
(`summable_norm_restrict_comp_addRight`): the sup-norms over a fixed compact of the lattice
translates are summable, which is what lets one assemble the periodization `∑' ℓ, f (· + ℓ)` as a
`tsum` of continuous maps. The translate `x ↦ f (x + ℓ)` is written inline as the composite
`(f : C(E, F)).comp (ContinuousMap.addRight ℓ)`, following mathlib's
`Real.fourierCoeff_tsum_comp_add`.

Upstream target: `Mathlib/Analysis/Distribution/SchwartzSpace/ZLattice.lean` (downstream of
`SchwartzSpace.Basic` and `Algebra.Module.ZLattice.Summable`). Imports here are left as
`public import Mathlib`; they are narrowed at upstreaming time.
-/

open MeasureTheory

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
/-- A discrete `ℤ`-submodule of a proper real normed space meets any closed ball in a finite set:
only finitely many lattice points have norm `≤ r`. Strictly more general than
`ZSpan.setFinite_inter` (no basis, no `IsZLattice`). -/
public theorem ZLattice.finite_norm_le [ProperSpace E] (L : Submodule ℤ E) [DiscreteTopology L]
    (r : ℝ) : ({ℓ : L | ‖(ℓ : E)‖ ≤ r} : Set L).Finite := by
  have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  have hfin : (Metric.closedBall (0 : E) r ∩ (L.toAddSubgroup : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall AddSubgroup.isClosed_of_discrete
  refine .of_finite_image (hfin.subset ?_) Subtype.coe_injective.injOn
  rintro _ ⟨ℓ, hℓ, rfl⟩
  exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hℓ, ℓ.2⟩

variable [FiniteDimensional ℝ E]

namespace SchwartzMap

private lemma half_norm_le_norm_add {G : Type*} [SeminormedAddCommGroup G] {x ℓ : G} {r : ℝ}
    (hx : ‖x‖ ≤ r) (hℓ : 2 * r < ‖ℓ‖) : 1 / 2 * ‖ℓ‖ ≤ ‖x + ℓ‖ := by
  have h : ‖ℓ‖ - ‖x‖ ≤ ‖x + ℓ‖ := by simpa [add_comm] using norm_sub_norm_le ℓ (-x)
  linarith

/-- Schwartz decay is locally uniform over a `ℤ`-lattice: the sup-norms over a fixed compact `K`
of the lattice translates `x ↦ f (x + ℓ)` of `f` are summable. This is the engine from which the
pointwise summability `summable_norm_comp_add` follows, by taking `K` a singleton. -/
public theorem summable_norm_restrict_comp_addRight (f : 𝓢(E, F)) (L : Submodule ℤ E)
    [DiscreteTopology L] (K : TopologicalSpace.Compacts E) :
    Summable (fun ℓ : L => ‖((f : C(E, F)).comp (ContinuousMap.addRight (ℓ : E))).restrict K‖) := by
  -- `k` is a decay order exceeding the lattice rank, so that `‖·‖⁻¹ ^ k` is summable over `L`.
  let k : ℕ := Module.finrank ℤ L + 1
  obtain ⟨C, hCpos, hC⟩ := f.decay k 0
  simp_rw [norm_iteratedFDeriv_zero] at hC
  obtain ⟨r, hrK⟩ := K.isCompact.isBounded.subset_closedBall (0 : E)
  have hsum : Summable fun ℓ : L => ‖(ℓ : E)‖⁻¹ ^ k := by
    simpa [k] using ZLattice.summable_norm_pow_inv (L := L) k (Nat.lt_succ_self _)
  refine (hsum.mul_left (C * 2 ^ k)).of_norm_bounded_eventually ?_
  filter_upwards [(ZLattice.finite_norm_le (L := L) (max (2 * r) 1)).eventually_cofinite_notMem]
    with ℓ hℓ
  have hRlt : max (2 * r) 1 < ‖(ℓ : E)‖ := lt_of_not_ge (by simpa using hℓ)
  have hnorm_pos : 0 < ‖(ℓ : E)‖ := one_pos.trans_le ((le_max_right _ _).trans hRlt.le)
  rw [norm_norm]
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun ⟨x, hxK⟩ => ?_
  have hxr : ‖x‖ ≤ r := by simpa using hrK hxK
  have hge : 1 / 2 * ‖(ℓ : E)‖ ≤ ‖x + (ℓ : E)‖ :=
    half_norm_le_norm_add hxr ((le_max_left _ _).trans_lt hRlt)
  have hpos : 0 < ‖x + (ℓ : E)‖ := (by positivity : (0 : ℝ) < 1 / 2 * ‖(ℓ : E)‖).trans_le hge
  have hinv : ‖x + (ℓ : E)‖⁻¹ ≤ 2 * ‖(ℓ : E)‖⁻¹ := by
    have h := inv_anti₀ (by positivity) hge
    rwa [mul_inv, one_div, inv_inv] at h
  calc ‖((f : C(E, F)).comp (ContinuousMap.addRight (ℓ : E))) (⟨x, hxK⟩ : K)‖
      = ‖f (x + (ℓ : E))‖ := rfl
    _ ≤ C / ‖x + (ℓ : E)‖ ^ k := (le_div_iff₀' (pow_pos hpos k)).2 (hC _)
    _ = C * ‖x + (ℓ : E)‖⁻¹ ^ k := by rw [div_eq_mul_inv, inv_pow]
    _ ≤ C * (2 * ‖(ℓ : E)‖⁻¹) ^ k := by gcongr
    _ = C * 2 ^ k * ‖(ℓ : E)‖⁻¹ ^ k := by rw [mul_pow, mul_assoc]

/-- A Schwartz function has summable norms over any translate of a discrete `ℤ`-submodule of a
finite-dimensional real normed space: the singleton-compact case of
`summable_norm_restrict_comp_addRight`, since the sup-norm over `{a}` is the value at `a`. -/
public theorem summable_norm_comp_add (f : 𝓢(E, F)) (L : Submodule ℤ E) [DiscreteTopology L]
    (a : E) : Summable (fun ℓ : L => ‖f (a + (ℓ : E))‖) := by
  refine (f.summable_norm_restrict_comp_addRight L ⟨{a}, isCompact_singleton⟩).congr fun ℓ => ?_
  refine le_antisymm ((ContinuousMap.norm_le _ (norm_nonneg _)).2 ?_)
    ((((f : C(E, F)).comp (ContinuousMap.addRight (ℓ : E))).restrict {a}).norm_coe_le_norm ⟨a, rfl⟩)
  rintro ⟨x, rfl⟩
  exact le_rfl

end SchwartzMap
