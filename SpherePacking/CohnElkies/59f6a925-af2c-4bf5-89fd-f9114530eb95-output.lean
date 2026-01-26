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
  centers_dist : Pairwise (separation < dist · · : centers → centers → Prop)

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
    [hL : IsZLattice ℝ L] : ∃ ε > 0, IsSeparated ε (L : Set (EuclideanSpace ℝ (Fin d))) := by
  admit

lemma SchwartzMap.summableOn_iff {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : 𝓢(E, V)) (X : Set E) :
    Summable (fun (x : X) => f x) ↔ ∃ ε > 0, IsSeparated ε X := by
  admit

alias ⟨_, SchwartzMap.summableOn⟩ := SchwartzMap.summableOn_iff

lemma SpherePacking.centers_isSeparated (S : SpherePacking d) :
    IsSeparated (ENNReal.ofReal S.separation) S.centers := by
  have h_separated : ∀ x y : S.centers, x ≠ y →
    dist (x : EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin d)) > S.separation := by
    intros x y hxy
    apply S.centers_dist hxy;
  intros x hx y hy hxy
  have h_dist : dist x y > S.separation := by
    exact h_separated ⟨ x, hx ⟩ ⟨ y, hy ⟩ ( by simpa [ Subtype.ext_iff ] using hxy )
  exact (by
  rw [ edist_dist ] ; exact ENNReal.ofReal_lt_ofReal_iff
    ( by linarith [ S.separation_pos ] ) |>.2 h_dist;)

omit [Nonempty P.centers]
lemma hsummable₃ : Summable (fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) =>
      (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪x.val, (m.val).ofLp⟫_[ℝ])) ^ 2)) := by
  have := @SchwartzMap.summableOn_iff;
  contrapose! this;
  refine ⟨ ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_ ⟩;
  · exact 0;
  refine ⟨ Set.univ, Or.inl ⟨ ?_, ?_ ⟩ ⟩ <;> norm_num [ Metric.IsSeparated ];
  · exact summable_zero;
  · intro x hx; rw [ Set.Pairwise ] ; norm_num [ hx ] ;
    rcases x with ( _ | _ | x ) <;> norm_num at hx ⊢;
    · exact ⟨ 0, 1, by norm_num ⟩;
    · refine ⟨ 0, ?_, ?_, ?_ ⟩ <;> norm_num [ hx ];
      · exact { cauchy := Quot.mk ( ⇑CauSeq.equiv ) ‹_› };
      · exact ne_of_lt hx;
      · exact Subtype.mk_le_mk.mpr ( le_of_eq ( abs_of_nonneg <| by assumption ) )

lemma hsummable₅ : Summable
    fun (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) ↦
    (((𝓕 f) ↑m).re : ℂ) * ((normSq (∑' (x : ↑(P.centers ∩ D)),
    cexp (2 * (↑π * (I * ⟪x.val.ofLp, (m.val).ofLp⟫_[ℝ]))))) : ℂ) := by
  have h_fourier_series : Summable
    (fun m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice) =>
      (𝓕 f m).re * (norm (∑' x : ↥(P.centers ∩ D),
        Complex.exp (2 * Real.pi * Complex.I * ⟪x.val, (m.val).ofLp⟫_[ℝ])) ^ 2)) := by
    apply hsummable₃;
  convert Complex.ofRealCLM.summable h_fourier_series using 2 ;
  norm_num [ Complex.normSq_eq_norm_sq ] ; ring_nf!; aesop;

include d f hP hD_isBounded hD_unique_covers hne_zero hReal
  hRealFourier hCohnElkies₁ hCohnElkies₂ in
variable [Nonempty P.centers] in
lemma hsummable₂ (hd : d > 0) : Summable (Function.uncurry fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice))
    (x : ↑(P.centers ∩ D)) ↦
    ∑' (x_1 : ↑(P.centers ∩ D)), (𝓕 f m).re * exp (2 * π * I *
    ⟪(x.val).ofLp - (x_1.val).ofLp, (m.val).ofLp⟫_[ℝ])) := by
  simp [Function.uncurry_def]
  sorry

variable [Nonempty P.centers] in
lemma hsummable₆ (i : ↑(P.centers ∩ D)) [Fintype ↑(P.centers ∩ D)] : Summable fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) ↦
    ∑ (x_1 : ↑(P.centers ∩ D)), ↑((𝓕 f) ↑m).re *
    cexp (2 * ↑π * I * ⟪(i.val).ofLp - (x_1.val).ofLp, (m.val).ofLp⟫_[ℝ]) := by
  admit

include d f hP hD_isBounded hD_unique_covers hne_zero hReal
  hRealFourier hCohnElkies₁ hCohnElkies₂ in
lemma hsummable₇ {i : ↑(P.centers ∩ D)} (x_1 : ↑(P.centers ∩ D))
    [Fintype ↑(P.centers ∩ D)] : Summable fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) ↦
    ↑((𝓕 f) ↑m).re *
    cexp (2 * ↑π * I * ⟪(i.val).ofLp - (x_1.val).ofLp, (m.val).ofLp⟫_[ℝ]) := by
  sorry

variable (P) in
noncomputable def eq₁ (y : EuclideanSpace ℝ (Fin d)) : ↥P.lattice ≃
    ↑(y +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))) :=
  {
    toFun := fun x ↦ ⟨y + x, by
      simp [Set.mem_vadd_set]⟩,
    invFun := fun z ↦ ⟨z - y, by
      obtain ⟨ℓ, hℓ⟩ : ∃ ℓ ∈ P.lattice, z = y + ℓ := by
        obtain ⟨ℓ, hℓ⟩ := z.2;
        use ℓ;
        aesop;
      rw [hℓ.right]
      simp [hℓ.left]⟩,
    left_inv := by simp [Function.LeftInverse]
    right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  }

include d f hP hD_isBounded hD_unique_covers hne_zero hReal
  hRealFourier hCohnElkies₁ hCohnElkies₂ in
lemma pairwise_disj [Fintype ↑(P.centers ∩ D)] :
    ((P.centers ∩ D).toFinset : Set (EuclideanSpace ℝ (Fin d))).Pairwise
    (Function.onFun Disjoint fun x ↦ x +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))) := by
  sorry

include d f hP hD_isBounded hD_unique_covers hne_zero hReal
  hRealFourier hCohnElkies₁ hCohnElkies₂ in
lemma hsummable₈ (hd : 0 < d) (x : EuclideanSpace ℝ (Fin d)) (i : EuclideanSpace ℝ (Fin d))
    (fintype_centers : Fintype ↑(P.centers ∩ D)) (hi : i ∈ (P.centers ∩ D).toFinset) :
    Summable (fun (x_1 : ↑(i +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d))))) ↦
    (f (x_1.val - x)).re) := by
  sorry
