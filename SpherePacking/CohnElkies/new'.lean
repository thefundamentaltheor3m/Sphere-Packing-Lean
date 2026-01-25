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


noncomputable def SchwartzMap.translation {d : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (a : EuclideanSpace ℝ (Fin d)) : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
  SchwartzMap.mk
    (fun x ↦ f (x - a))
    ((f.smooth ⊤).comp ((contDiff_id).sub contDiff_const))
    (by
    intro k n
    have h_schwartz : ∀ k n : ℕ, ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖^k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
      exact fun k n ↦ f.decay' k n;
    -- By definition of $f(x - a)$, we have $iteratedFDeriv ℝ n (fun x => f (x - a)) x = iteratedFDeriv ℝ n f (x - a)$.
    have h_iteratedFDeriv : ∀ n : ℕ, ∀ x : EuclideanSpace ℝ (Fin d), iteratedFDeriv ℝ n (fun x => f (x - a)) x = iteratedFDeriv ℝ n f (x - a) := by
      exact fun n x ↦ iteratedFDeriv_comp_sub n a x
    generalize_proofs at *; (
    -- By the triangle inequality, we have ‖x‖^k ≤ (‖x - a‖ + ‖a‖)^k.
    have h_triangle : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖^k ≤ (‖x - a‖ + ‖a‖)^k := by
      exact fun x => pow_le_pow_left₀ ( norm_nonneg _ ) ( by simpa using norm_add_le ( x - a ) a ) _;
    generalize_proofs at *; (
    -- By the properties of the Schwartz space, we know that $(‖x - a‖ + ‖a‖)^k * ‖iteratedFDeriv ℝ n f (x - a)‖$ is bounded.
    have h_bounded : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin d), (‖x - a‖ + ‖a‖)^k * ‖iteratedFDeriv ℝ n f (x - a)‖ ≤ C := by
      -- By the binomial theorem, we can expand $(‖x - a‖ + ‖a‖)^k$ into a sum of terms involving $‖x - a‖^m$ and $‖a‖^{k-m}$.
      have h_binom : ∀ x : EuclideanSpace ℝ (Fin d), (‖x - a‖ + ‖a‖)^k = ∑ m ∈ Finset.range (k + 1), Nat.choose k m * ‖x - a‖^m * ‖a‖^(k - m) := by
        exact fun x => by rw [ add_pow ] ; ac_rfl;
      generalize_proofs at *; (
      -- By the properties of the Schwartz space, we know that each term in the sum is bounded.
      have h_term_bounded : ∀ m ∈ Finset.range (k + 1), ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin d), Nat.choose k m * ‖x - a‖^m * ‖a‖^(k - m) * ‖iteratedFDeriv ℝ n f (x - a)‖ ≤ C := by
        intro m hm
        obtain ⟨C, hC⟩ := h_schwartz m n
        use C * Nat.choose k m * ‖a‖^(k - m) ; intros x; specialize hC ( x - a ) ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
        nlinarith [ show 0 ≤ ( k.choose m : ℝ ) * ‖a‖ ^ ( k - m ) by positivity ]
      generalize_proofs at *; (
      choose! C hC using h_term_bounded; use ∑ m ∈ Finset.range ( k + 1 ), C m; intro x; rw [ h_binom x ] ; simp +decide [ Finset.sum_mul _ _ _, hC ] ;
      exact Finset.sum_le_sum fun i hi => hC i hi x))
    generalize_proofs at *; (
    exact ⟨ h_bounded.choose, fun x => by simpa only [ h_iteratedFDeriv ] using le_trans ( mul_le_mul_of_nonneg_right ( h_triangle x ) ( norm_nonneg _ ) ) ( h_bounded.choose_spec x ) ⟩))))

lemma SpherePacking.centers_isSeparated (S : SpherePacking d) :
    IsSeparated (ENNReal.ofReal S.separation) S.centers := by
  -- By definition of `SpherePacking`, the centers are pairwise separated by a positive distance.
  have h_separated : ∀ x y : S.centers, x ≠ y → dist (x : EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin d)) > S.separation := by
    -- By definition of `SpherePacking`, the centers are pairwise separated by a positive distance. Therefore, for any two distinct centers `x` and `y`, we have `dist x y > S.separation`.
    intros x y hxy
    apply S.centers_dist hxy;
  -- By definition of `IsSeparated`, we need to show that for any two distinct points in `S.centers`, their distance is greater than `S.separation`. This follows directly from `h_separated`.
  intros x hx y hy hxy;
  rw [ edist_dist ] ; aesop;

lemma hsummable₁ (y : EuclideanSpace ℝ (Fin d))
    (hf : Summable fun (x : P.centers) ↦ f x) :
    Summable fun (b : P.centers) ↦ (f (b.val - y)).re := by
  -- Since translation by y maps the centers of P to another set of points that are still separated by at least 1 (because the distance between any two points in P.centers - y is the same as the distance between the corresponding points in P.centers), the summability of the translated function should follow from the summability of f over the original set.
  have h_translated_summable : Summable (fun x : P.centers => f (x - y)) := by
    -- Since $P.centers$ is a separated set and $f$ is a Schwartz function, the series $\sum_{x \in P.centers} f(x - y)$ converges absolutely.
    have h_translated_summable : IsSeparated (ENNReal.ofReal P.separation) (P.centers - {y}) := by
      have h_translated_summable : IsSeparated (ENNReal.ofReal P.separation) P.centers := by
        exact SpherePacking.centers_isSeparated P.toSpherePacking
      generalize_proofs at *; (
      intro x hx y hy; aesop;);
    have h_translated_summable : Summable (fun x : (P.centers - {y} : Set (EuclideanSpace ℝ (Fin d))) => f x) := by
      -- Apply the SchwartzMap.summableOn_iff lemma with the separated set P.centers - {y} and the positive ε from h_translated_summable.
      apply (SchwartzMap.summableOn_iff f (P.centers - {y})).mpr;
      -- Since $P.separation$ is positive, we can take $\epsilon = P.separation$.
      use ENNReal.ofReal P.separation;
      exact ⟨ ENNReal.ofReal_pos.mpr P.separation_pos, h_translated_summable ⟩;
    convert h_translated_summable.comp_injective ( show Function.Injective ( fun x : P.centers => ⟨ x - y, by aesop ⟩ : P.centers → ( P.centers - { y } : Set ( EuclideanSpace ℝ ( Fin d ) ) ) ) from fun x y hxy => by aesop ) using 1;
  convert h_translated_summable.re using 1

lemma hsummable₂ : Summable (Function.uncurry fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice))
    (x : ↑(P.centers ∩ D)) ↦
    ∑' (x_1 : ↑(P.centers ∩ D)), (𝓕 f m).re * exp (2 * π * I *
    ⟪(x.val).ofLp - (x_1.val).ofLp, (m.val).ofLp⟫_[ℝ])) := by
  simp [Function.uncurry_def]
  sorry

lemma hsummable₃ : Summable (fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) =>
      (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I * ⟪x.val, (m.val).ofLp⟫_[ℝ])) ^ 2)) := by
  sorry

lemma hsummable₄ (P : PeriodicSpherePacking d) (hf : Summable (fun (x : P.centers) => f x))
    (x y : EuclideanSpace ℝ (Fin d)) :
    Summable fun (ℓ : ↥P.lattice) ↦ f (x - y + ℓ.val) := by
  have := f.summableOn
    ( Set.range ( fun ℓ : P.lattice => ( ℓ : EuclideanSpace ℝ ( Fin d ) ) + ( x - y ) ) ) (by
  have h_separated : ∃ ε > 0, IsSeparated ε (P.lattice : Set (EuclideanSpace ℝ (Fin d))) := by
    convert ZLattice.isSeparated P.lattice;
    · exact P.lattice_discrete;
    · exact P.lattice_isZLattice;
  -- Since addition by a constant preserves the separation property, the range of the
  -- function ℓ ↦ ℓ + (x - y) is also separated.
  obtain ⟨ε, hε_pos, hε_sep⟩ := h_separated;
  use ε, hε_pos;
  intro x hx y hy hxy;
  aesop);
  convert this.comp_injective
    ( show Function.Injective ( fun ℓ : P.lattice =>
      ⟨ ( ℓ : EuclideanSpace ℝ ( Fin d ) ) + ( x - y ), Set.mem_range_self ℓ ⟩ )
        from fun a b h => by simpa using congr_arg Subtype.val h ) using 1;
  exact funext fun _ => by simp +decide [ add_comm ];

lemma hsummable₅ : Summable
    fun (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) ↦
    (((𝓕 f) ↑m).re : ℂ) * ((normSq (∑' (x : ↑(P.centers ∩ D)),
    cexp (2 * (↑π * (I * ⟪x.val.ofLp, (m.val).ofLp⟫_[ℝ]))))) : ℂ) := by
  sorry

lemma hsummable₆ (i : ↑(P.centers ∩ D)) [Fintype ↑(P.centers ∩ D)] : Summable fun
    (m : ↥(BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin d))) P.lattice)) ↦
    ∑ (x_1 : ↑(P.centers ∩ D)), ↑((𝓕 f) ↑m).re *
    cexp (2 * ↑π * I * ⟪(i.val).ofLp - (x_1.val).ofLp, (m.val).ofLp⟫_[ℝ]) := by
  sorry

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
      -- Since $x$ is in the lattice, adding $y$ to $x$ should still be in the lattice
      -- shifted by $y$.
      simp [Set.mem_vadd_set]⟩,
    invFun := fun z ↦ ⟨z - y, by
      -- Since $z$ is in the set $y +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))$, there
      -- exists some $ℓ \in P.lattice$ such that $z = y + ℓ$.
      obtain ⟨ℓ, hℓ⟩ : ∃ ℓ ∈ P.lattice, z = y + ℓ := by
        -- By definition of $y +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))$, if $z \in
        -- y +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))$, then there exists some $ℓ
        -- \in P.lattice$ such that $z = y + ℓ$.
        obtain ⟨ℓ, hℓ⟩ := z.2;
        use ℓ;
        aesop;
      -- Substitute $z = y + ℓ$ into the expression $(z - y)$ and simplify.
      rw [hℓ.right]
      simp [hℓ.left]⟩,
    left_inv := by simp [Function.LeftInverse]
    right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  }

variable (P D) in
lemma hunion [Fintype ↑(P.centers ∩ D)] : P.centers =
    ⋃ (x ∈ (P.centers ∩ D).toFinset), (x +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))) := by
  ext x
  constructor <;> intro h
  · simp
    sorry
  · simp at h
    obtain ⟨i, hi₁, hi₂⟩ := h
    sorry

lemma pairwise_disj [Fintype ↑(P.centers ∩ D)] :
  ((P.centers ∩ D).toFinset : Set (EuclideanSpace ℝ (Fin d))).Pairwise
  (Function.onFun Disjoint fun x ↦ x +ᵥ (P.lattice : Set (EuclideanSpace ℝ (Fin d)))) := by sorry
