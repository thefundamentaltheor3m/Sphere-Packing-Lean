/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Auguste Poiroux
-/
module
public import Mathlib

/-! # Summability of a Schwartz function over a `ℤ`-lattice

A Schwartz function on a finite-dimensional real normed space `E` is summable, in norm, over the
translates of any discrete `ℤ`-submodule `L ⊆ E`. This is the basic summability input to (general)
Poisson summation and to the Cohn–Elkies linear-programming bound.

The proof combines Schwartz decay (`SchwartzMap.decay`) with the convergent dominating series
`ZLattice.summable_norm_sub_inv_pow`. It needs neither an inner-product structure, nor that `L` be a
full lattice (`IsZLattice`): only `[FiniteDimensional ℝ E]` and `[DiscreteTopology L]`.

We record the pointwise summability (`summable_norm_comp_add`, `summable_comp_add`) and the
locally-uniform version (`summable_norm_translateCM_restrict`): the sup-norms over a fixed compact
of the lattice translates are summable, which is what lets one assemble the periodization
`∑' ℓ, f (· + ℓ)` as a `tsum` of continuous maps.

Upstream target: `Mathlib/Analysis/Distribution/SchwartzSpace/ZLattice.lean` (downstream of
`SchwartzSpace.Basic` and `Algebra.Module.ZLattice.Summable`). Imports here are left as
`public import Mathlib`; they are narrowed at upstreaming time.
-/

open MeasureTheory

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SchwartzMap

/-- Translate a Schwartz function `f` by a vector `ℓ`, as a continuous map `x ↦ f (x + ℓ)`. -/
@[expose] public noncomputable def translateCM (f : 𝓢(E, F)) (ℓ : E) : C(E, F) :=
  (f : C(E, F)).comp (ContinuousMap.addRight ℓ)

@[simp] public theorem translateCM_apply (f : 𝓢(E, F)) (ℓ x : E) :
    f.translateCM ℓ x = f (x + ℓ) := rfl

end SchwartzMap

variable [FiniteDimensional ℝ E]

/-- A discrete `ℤ`-submodule of a finite-dimensional real normed space meets any closed ball in a
finite set: only finitely many lattice points have norm `≤ r`. -/
public theorem ZLattice.finite_norm_le (L : Submodule ℤ E) [DiscreteTopology L] (r : ℝ) :
    ({ℓ : L | ‖(ℓ : E)‖ ≤ r} : Set L).Finite := by
  have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  have hfin : (Metric.closedBall (0 : E) r ∩ (L.toAddSubgroup : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall AddSubgroup.isClosed_of_discrete
  refine .of_finite_image (hfin.subset ?_) Subtype.coe_injective.injOn
  rintro _ ⟨ℓ, hℓ, rfl⟩
  exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hℓ, ℓ.2⟩

namespace SchwartzMap

/-- A Schwartz function has summable norms over any translate of a discrete `ℤ`-submodule of a
finite-dimensional real normed space. -/
public theorem summable_norm_comp_add (f : 𝓢(E, F)) (L : Submodule ℤ E) [DiscreteTopology L]
    (a : E) : Summable (fun ℓ : L => ‖f (a + (ℓ : E))‖) := by
  -- `k` is a decay order exceeding the rank, so the comparison series `‖· - b‖⁻¹ ^ k` converges.
  let k : ℕ := Module.finrank ℤ L + 1
  obtain ⟨C, _, hC⟩ := f.decay k 0
  -- `b = -a` is the shift, so that `a + ℓ = ℓ - b`.
  set b : E := -a
  refine Summable.of_norm_bounded_eventually
    (g := fun ℓ : L => (C + 1) * ‖(ℓ : E) - b‖⁻¹ ^ k) ?_ ?_
  · simpa [mul_assoc] using
      (ZLattice.summable_norm_sub_inv_pow (L := L) (n := k) (by simp [k]) b).mul_left (C + 1)
  · -- The bound fails only on the finite set where `‖ℓ - b‖ ≤ 1`.
    have hfin : ({ℓ : L | ‖(ℓ : E) - b‖ ≤ (1 : ℝ)} : Set L).Finite :=
      (ZLattice.finite_norm_le (L := L) (1 + ‖b‖)).subset fun ℓ hℓ => by
        simp only [Set.mem_setOf_eq] at hℓ ⊢
        calc ‖(ℓ : E)‖ = ‖((ℓ : E) - b) + b‖ := by rw [sub_add_cancel]
          _ ≤ ‖(ℓ : E) - b‖ + ‖b‖ := norm_add_le _ _
          _ ≤ 1 + ‖b‖ := by linarith
    refine hfin.subset fun ℓ hfail => ?_
    by_contra hlarge
    have hpos : 0 < ‖(ℓ : E) - b‖ ^ k :=
      pow_pos (lt_of_lt_of_le one_pos (lt_of_not_ge hlarge).le) _
    have hab : ‖a + (ℓ : E)‖ = ‖(ℓ : E) - b‖ := by simp [b, sub_eq_add_neg, add_comm]
    have hdec : ‖(ℓ : E) - b‖ ^ k * ‖f (a + (ℓ : E))‖ ≤ C := by
      simpa [hab, norm_iteratedFDeriv_zero] using hC (a + (ℓ : E))
    have h1 : ‖f (a + (ℓ : E))‖ ≤ C / ‖(ℓ : E) - b‖ ^ k := (le_div_iff₀' hpos).2 hdec
    have h2 : C / ‖(ℓ : E) - b‖ ^ k ≤ (C + 1) * ‖(ℓ : E) - b‖⁻¹ ^ k := by
      simpa [div_eq_mul_inv, inv_pow] using
        mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1)
          (by positivity : 0 ≤ (‖(ℓ : E) - b‖ ^ k)⁻¹)
    exact hfail (by simpa using h1.trans h2)

/-- A Schwartz function is summable over any translate of a discrete `ℤ`-submodule. -/
public theorem summable_comp_add [CompleteSpace F] (f : 𝓢(E, F)) (L : Submodule ℤ E)
    [DiscreteTopology L] (a : E) : Summable (fun ℓ : L => f (a + (ℓ : E))) :=
  Summable.of_norm (f.summable_norm_comp_add L a)

private lemma half_norm_le_norm_add {G : Type*} [SeminormedAddCommGroup G] {x ℓ : G} {r : ℝ}
    (hx : ‖x‖ ≤ r) (hℓ : 2 * r < ‖ℓ‖) : 1 / 2 * ‖ℓ‖ ≤ ‖x + ℓ‖ := by
  have h : ‖ℓ‖ - ‖x‖ ≤ ‖x + ℓ‖ := by simpa [add_comm] using norm_sub_norm_le ℓ (-x)
  linarith

/-- Schwartz decay is locally uniform over a `ℤ`-lattice: the sup-norms over a fixed compact `K`
of the lattice translates of `f` are summable. -/
public theorem summable_norm_translateCM_restrict (f : 𝓢(E, F)) (L : Submodule ℤ E)
    [DiscreteTopology L] (K : TopologicalSpace.Compacts E) :
    Summable (fun ℓ : L => ‖(f.translateCM (ℓ : E)).restrict K‖) := by
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
  calc ‖(f.translateCM (ℓ : E)) (⟨x, hxK⟩ : K)‖
      = ‖f (x + (ℓ : E))‖ := rfl
    _ ≤ C / ‖x + (ℓ : E)‖ ^ k := (le_div_iff₀' (pow_pos hpos k)).2 (hC _)
    _ = C * ‖x + (ℓ : E)‖⁻¹ ^ k := by rw [div_eq_mul_inv, inv_pow]
    _ ≤ C * (2 * ‖(ℓ : E)‖⁻¹) ^ k := by gcongr
    _ = C * 2 ^ k * ‖(ℓ : E)‖⁻¹ ^ k := by rw [mul_pow, mul_assoc]

end SchwartzMap
