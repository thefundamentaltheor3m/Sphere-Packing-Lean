import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.Analysis.RCLike.Inner

open scoped FourierTransform ENNReal SchwartzMap InnerProductSpace
open Metric BigOperators Pointwise Filter MeasureTheory Complex
  Real ZSpan Bornology Summable Module LinearMap SchwartzMap

variable {d : ℕ}

--Let `f : ℝᵈ → ℂ` be a Schwartz function.
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)
-- let `f` to be real-valued:
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
-- let `𝓕 f` be real-valued:
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
-- moreover, impose the Cohn-Elkies conditions:
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)

structure SpherePacking (d : ℕ) where
  centers : Set (EuclideanSpace ℝ (Fin d))
  separation : ℝ
  separation_pos : 0 < separation := by positivity
  centers_dist : Pairwise (separation ≤ dist · · : centers → centers → Prop)

structure PeriodicSpherePacking (d : ℕ) extends SpherePacking d where
  lattice : Submodule ℤ (EuclideanSpace ℝ (Fin d))
  lattice_action : ∀ ⦃x y⦄, x ∈ lattice → y ∈ centers → x + y ∈ centers
  lattice_discrete : DiscreteTopology lattice := by infer_instance
  lattice_isZLattice : IsZLattice ℝ lattice := by infer_instance

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : Bornology.IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)

theorem _root_.Continuous.re {α 𝕜 : Type*} [TopologicalSpace α] [RCLike 𝕜] {f : α → 𝕜}
    (hf : Continuous f) : Continuous (fun x ↦ RCLike.re (f x)) :=
  RCLike.continuous_re.comp hf

theorem _root_.Continuous.im {α 𝕜 : Type*} [TopologicalSpace α] [RCLike 𝕜] {f : α → 𝕜}
    (hf : Continuous f) : Continuous (fun x ↦ RCLike.im (f x)) :=
  RCLike.continuous_im.comp hf

theorem _root_.Continuous.ofReal {α 𝕜 : Type*} [TopologicalSpace α] [RCLike 𝕜]
    {f : α → ℝ} (hf : Continuous f) : Continuous (fun (x : α) => (f x : 𝕜)) :=
  RCLike.continuous_ofReal.comp hf

theorem _root_.LipschitzWith.norm {α 𝕜 : Type*} [PseudoEMetricSpace α] [RCLike 𝕜]
    {K : NNReal} {f : α → 𝕜} (hf : LipschitzWith K f) :
    LipschitzWith K (fun x ↦ ‖f x‖) := by
  simpa using lipschitzWith_one_norm.comp hf

theorem _root_.LipschitzWith.re {α 𝕜 : Type*} [PseudoEMetricSpace α] [RCLike 𝕜]
    {K : NNReal} {f : α → 𝕜} (hf : LipschitzWith K f) :
    LipschitzWith K (fun x ↦ RCLike.re (f x)) := by
  simpa using RCLike.lipschitzWith_re.comp hf

theorem _root_.LipschitzWith.im {α 𝕜 : Type*} [PseudoEMetricSpace α] [RCLike 𝕜]
    {K : NNReal} {f : α → 𝕜} (hf : LipschitzWith K f) :
    LipschitzWith K (fun x ↦ RCLike.im (f x)) := by
  simpa using RCLike.lipschitzWith_im.comp hf

theorem _root_.LipschitzWith.ofReal {α 𝕜 : Type*} [PseudoEMetricSpace α] [RCLike 𝕜]
    {K : NNReal} {f : α → ℝ} (hf : LipschitzWith K f) :
    LipschitzWith K (fun (x : α) => (f x : 𝕜)) := by
  simpa using RCLike.lipschitzWith_ofReal.comp hf

theorem _root_.Memℓp.re {α : Type*} {𝕜 : α → Type*} {p : ENNReal} [(i : α) → RCLike (𝕜 i)]
    {f : ∀ i, 𝕜 i} (hf : Memℓp f p) :
    Memℓp (fun (x : α) => RCLike.re (f x)) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    refine hf.finite_dsupport.subset fun i => ?_
    simp only [ne_eq, Set.mem_setOf_eq]
    intro h
    contrapose! h
    simp [h]
  · apply memℓp_infty
    obtain ⟨A, hA⟩ := hf.bddAbove
    simp[BddAbove, upperBounds] at hA ⊢

    admit
  · apply memℓp_gen


    admit

theorem _root_.Memℓp.im {α : Type*} {𝕜 : α → Type*} {p : ENNReal} [(i : α) → RCLike (𝕜 i)]
    {f : ∀ i, 𝕜 i} (hf : Memℓp f p) :
    Memℓp (fun (x : α) => RCLike.im (f x)) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    refine hf.finite_dsupport.subset fun i => ?_
    simp only [ne_eq, Set.mem_setOf_eq]
    intro h
    contrapose! h
    simp [h]
  · apply memℓp_infty
    obtain ⟨A, hA⟩ := hf.bddAbove
    simp[BddAbove, upperBounds] at hA ⊢

    admit
  · apply memℓp_gen

    admit

theorem _root_.Memℓp.ofReal {α : Type*} {𝕜 : α → Type*} {p : ENNReal}
    [(i : α) → RCLike (𝕜 i)] {f : α → ℝ} (hf : Memℓp f p) :
    Memℓp (fun (x : α) => (f x : 𝕜 x)) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    refine hf.finite_dsupport.subset fun i => by simp
  · apply memℓp_infty
    obtain ⟨A, hA⟩ := hf.bddAbove
    simpa [BddAbove]
  · apply memℓp_gen
    admit

theorem memℓp_one_iff_summable {α : Type*} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : α → E} :
    Memℓp f 1 ↔ Summable f := by
  simpa [Memℓp] using summable_norm_iff

theorem _root_.Summable.re {α 𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜} (hf : Summable f) :
    Summable (fun x ↦ RCLike.re (f x)) := by
  rw [← memℓp_one_iff_summable] at hf ⊢
  exact hf.re

theorem _root_.Summable.im {α 𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜} (hf : Summable f) :
    Summable (fun x ↦ RCLike.im (f x)) := by
  rw [← memℓp_one_iff_summable] at hf ⊢
  exact hf.im





lemma ZLattice.isSeparated (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L]
    [hL : IsZLattice ℝ L] : ∃ ε, IsSeparated ε (L : Set (EuclideanSpace ℝ (Fin d))) := by
  admit

lemma SchwartzMap.summableOn_iff {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : 𝓢(E, V)) (X : Set E) :
    Summable (fun (x : X) ↦ f x) ↔ ∃ ε, IsSeparated ε X := by
  admit

alias ⟨_, SchwartzMap.summableOn⟩ := SchwartzMap.summableOn_iff






















noncomputable def SchwartzMap.translation {d : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (a : EuclideanSpace ℝ (Fin d)) : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
  SchwartzMap.mk
    (fun x ↦ f (x - a))
    sorry
    sorry

lemma SpherePacking.centers_isSeparated (S : SpherePacking d) :
    IsSeparated (ENNReal.ofReal S.separation) S.centers := by
  sorry

lemma hsummable₁ (y : EuclideanSpace ℝ (Fin d))
    (hf : Summable fun (x : P.centers) ↦ f x) :
    Summable fun (b : P.centers) ↦ (f (b.val - y)).re := by
  -- 1. f is Schwartz hence its translation is Schwartz (f.translation (-y))
  -- 2. P.centers is separated (SpherePacking.centers_isSeparated P)
  -- 3. hence by (f.translation (-y)).summableOn (SpherePacking.centers_isSeparated P)
  --    one gets that Summable fun (b : P.centers) ↦ (f (b.val - y))
  -- 4. finally apply Summable.re
  sorry

lemma calc_steps' (x y : EuclideanSpace ℝ (Fin d)) :
    Summable fun (ℓ : ↥P.lattice) ↦ f (x - y + ℓ.val) := by
  -- 1. f is Schwartz hence its translation is Schwartz (f.translation (x - y))
  -- 2. P.lattice is a Z-lattice, hence it is separated
  -- 3. hence by (f.translation (x - y)).summableOn (ZLattice.isSeparated
  --    P.lattice_isZLattice) one gets the result.
  sorry

lemma hsummable₂ : Summable (Function.uncurry fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice))
    (x : ↑(P.centers ∩ D)) ↦
    ∑' (x_1 : ↑(P.centers ∩ D)), (𝓕 f m).re * exp (2 * π * I *
    ⟪(x.val).ofLp - (x_1.val).ofLp, (m.val).ofLp⟫_[ℝ])) := by
  simp [Function.uncurry_def]
  -- 1. the tsum is a finite sum since the intersection P.centers ∩ D is finite
  -- 2. take (𝓕 f p.1).re outside since it does not depend from x_1.
  -- 3. the whole function is summable if its norm is summable
  -- 4. norm of mul is mul of norms
  -- 5. apply triangular inequality
  -- 6. the sum is bounded by (P.centers ∩ D).card * 1
  -- 7. the function m ↦ ‖(𝓕 f m).re ‖ * (P.centers ∩ D).card is
  --    summable since m ↦ ‖(𝓕 f m).re ‖ is summable by Summable.norm
  --    Summable.re and multiplication by a constant is summable.
  sorry

lemma hsummable₃ : Summable (fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) =>
      (𝓕 ⇑f m).re * (Norm.norm (∑' x : ↑(P.centers ∩ D),
        Complex.exp (2 * π * I * ⟪x.val, (m.val).ofLp⟫_[ℝ])) ^ 2)) := by
  -- 1. the tsum is a finite sum since the intersection P.centers ∩ D is finite
  -- 2. apply triangular inequality
  -- 3. the sum is bounded by (P.centers ∩ D).card * 1
  -- 4. the function m ↦ (𝓕 f m).re is summable because the Fourier
  --    transform is Schwartz and then Summable.re
  -- 5. m ↦ (𝓕 f m).re * (P.centers ∩ D).card is summable because
  --    multiplication by a constant is summable.
  sorry
