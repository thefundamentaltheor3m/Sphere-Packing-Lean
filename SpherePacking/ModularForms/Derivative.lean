import SpherePacking.ModularForms.Eisenstein
import Mathlib.Analysis.Calculus.DiffContOnCl

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap
open Metric Filter Function

open scoped ModularForm MatrixGroups Manifold Topology BigOperators

/-!
Definition of (Serre) derivative of modular forms.
Prove Ramanujan's formulas on derivatives of Eisenstein series.
-/

noncomputable def D (F : ℍ → ℂ) : ℍ → ℂ :=
  fun (z : ℍ) => (2 * π * I)⁻¹ * ((deriv (F ∘ ofComplex)) z)

/--
TODO: Remove this or move this to somewhere more appropriate.
-/
lemma MDifferentiableAt_DifferentiableAt {F : ℍ → ℂ} {z : ℍ}
  (h : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F z) :
  DifferentiableAt ℂ (F ∘ ofComplex) ↑z := by
  have h₁ : DifferentiableWithinAt ℂ (F ∘ ofComplex) Set.univ ↑z :=
    by simpa [writtenInExtChartAt, extChartAt, Set.range_id] using
      MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt h
  exact (differentiableWithinAt_univ.1 h₁)

/--
The converse direction: `DifferentiableAt` on ℂ implies `MDifferentiableAt` on ℍ.
-/
lemma DifferentiableAt_MDifferentiableAt {G : ℂ → ℂ} {z : ℍ}
    (h : DifferentiableAt ℂ G ↑z) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (G ∘ (↑) : ℍ → ℂ) z := by
  rw [mdifferentiableAt_iff]
  -- Goal: DifferentiableAt ℂ ((G ∘ (↑)) ∘ ofComplex) ↑z
  -- The functions ((G ∘ (↑)) ∘ ofComplex) and G agree on the upper half-plane
  -- which is a neighborhood of ↑z
  apply DifferentiableAt.congr_of_eventuallyEq h
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
  exact congrArg G (UpperHalfPlane.coe_mk w hw)

/--
The derivative operator `D` preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `D F` is also MDifferentiable.
-/
theorem D_differentiable {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (D F) := fun z =>
  let hDiffOn : DifferentiableOn ℂ (F ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    fun w hw => (MDifferentiableAt_DifferentiableAt (hF ⟨w, hw⟩)).differentiableWithinAt
  MDifferentiableAt.mul mdifferentiableAt_const <| DifferentiableAt_MDifferentiableAt <|
    (hDiffOn.deriv isOpen_upperHalfPlaneSet).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

/--
TODO: Move this to E2.lean.
-/
theorem E₂_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E₂ := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hη : DifferentiableOn ℂ η _ :=
    fun z hz => (eta_DifferentiableAt_UpperHalfPlane ⟨z, hz⟩).differentiableWithinAt
  have hlog : DifferentiableOn ℂ (logDeriv η) {z | 0 < z.im} :=
    (hη.deriv isOpen_upperHalfPlaneSet).div hη fun _ hz => by
      simpa using eta_nonzero_on_UpperHalfPlane ⟨_, hz⟩
  exact (hlog.const_mul ((↑π * I / 12)⁻¹)).congr fun z hz => by
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz,
      show logDeriv η z = (↑π * I / 12) * E₂ ⟨z, hz⟩ by simpa using eta_logDeriv ⟨z, hz⟩]
    field_simp [Real.pi_ne_zero]

/--
Basic properties of derivatives: linearity, Leibniz rule, etc.
-/
@[simp]
theorem D_add (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) :
    D (F + G) = D F + D G := by
  ext z
  have h : deriv ((F ∘ ofComplex) + (G ∘ ofComplex)) z
      = deriv (F ∘ ofComplex) z + deriv (G ∘ ofComplex) z := by
    refine deriv_add ?_ ?_
    · exact MDifferentiableAt_DifferentiableAt (hF z)
    · exact MDifferentiableAt_DifferentiableAt (hG z)
  calc
    D (F + G) z
    _ = (2 * π * I)⁻¹ * deriv ((F ∘ ofComplex) + (G ∘ ofComplex)) z := by rfl
    _ = (2 * π * I)⁻¹ * (deriv (F ∘ ofComplex) z + deriv (G ∘ ofComplex) z) := by rw [h]
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z + (2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z := by
        rw [mul_add]
    _ = D F z + D G z := by rfl

@[simp]
theorem D_sub (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    : D (F - G) = D F - D G := by
  ext z
  have h : deriv ((F ∘ ofComplex) - (G ∘ ofComplex)) z
      = deriv (F ∘ ofComplex) z - deriv (G ∘ ofComplex) z := by
    refine deriv_sub ?_ ?_
    · exact MDifferentiableAt_DifferentiableAt (hF z)
    · exact MDifferentiableAt_DifferentiableAt (hG z)
  calc
    D (F - G) z
    _ = (2 * π * I)⁻¹ * deriv ((F ∘ ofComplex) - (G ∘ ofComplex)) z := by rfl
    _ = (2 * π * I)⁻¹ * (deriv (F ∘ ofComplex) z - deriv (G ∘ ofComplex) z) := by rw [h]
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z - (2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z := by
        rw [mul_sub]
    _ = D F z - D G z := by rfl

@[simp]
theorem D_smul (c : ℂ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    : D (c • F) = c • D F := by
  ext z
  have h : deriv (c • (F ∘ ofComplex)) z = c • deriv (F ∘ ofComplex) z :=
    deriv_const_mul c (MDifferentiableAt_DifferentiableAt (hF z))
  calc
    D (c • F) z
    _ = (2 * π * I)⁻¹ * deriv (c • (F ∘ ofComplex)) z := by rfl
    _ = (2 * π * I)⁻¹ * (c * deriv (F ∘ ofComplex) z) := by rw [h, smul_eq_mul]
    _ = c * ((2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z) := by ring_nf
    _ = c * D F z := by rfl

@[simp]
theorem D_mul (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    : D (F * G) = D F * G + F * D G := by
  ext z
  have h : deriv ((F ∘ ofComplex) * (G ∘ ofComplex)) z =
      deriv (F ∘ ofComplex) z * G z + F z * deriv (G ∘ ofComplex) z := by
    have hFz := MDifferentiableAt_DifferentiableAt (hF z)
    have hGz := MDifferentiableAt_DifferentiableAt (hG z)
    rw [deriv_mul hFz hGz]
    simp only [Function.comp_apply, ofComplex_apply]
  calc
    D (F * G) z
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex * G ∘ ofComplex) z := by rfl
    _ = (2 * π * I)⁻¹ * (deriv (F ∘ ofComplex) z * G z + F z * deriv (G ∘ ofComplex) z) := by rw [h]
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z * G z
        + F z * ((2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z) := by ring_nf
    _ = D F z * G z + F z * D G z := by rfl

@[simp]
theorem D_sq (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    D (F ^ 2) = 2 * F * D F := by
  calc
    D (F ^ 2) = D (F * F) := by rw [pow_two]
    _ = D F * F + F * D F := by rw [D_mul F F hF hF]
    _ = 2 * F * D F := by ring_nf

@[simp]
theorem D_cube (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    D (F ^ 3) = 3 * F ^ 2 * D F := by
  have hF2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F ^ 2) := by rw [pow_two]; exact MDifferentiable.mul hF hF
  calc
    D (F ^ 3) = D (F * F ^ 2) := by ring_nf
    _ = D F * F ^ 2 + F * D (F ^ 2) := by rw [D_mul F (F ^ 2) hF hF2]
    _ = D F * F ^ 2 + F * (2 * F * D F) := by rw [D_sq F hF]
    _ = 3 * F^2 * D F := by ring_nf

@[simp]
theorem D_const (c : ℂ) (z : ℍ) : D (Function.const _ c) z = 0 := by
  have h : deriv (Function.const _ c ∘ ofComplex) z = 0 := by
    have h' : Function.const _ c ∘ ofComplex = Function.const _ c := by rfl
    rw [h']
    exact deriv_const _ c
  calc
    D (Function.const _ c) z
    _ = (2 * π * I)⁻¹ * deriv (Function.const _ c ∘ ofComplex) z := by rfl
    _ = (2 * π * I)⁻¹ * 0 := by rw [h]
    _ = 0 := by ring_nf

/--
**Lemma 6.45 (Blueprint)**: The Serre derivative D acts as q·d/dq on q-series.
For a single q-power term: D(a·qⁿ) = n·a·qⁿ where q = exp(2πiz).

The key calculation:
- d/dz(exp(2πinz)) = 2πin·exp(2πinz)
- D(exp(2πinz)) = (2πi)⁻¹·(2πin·exp(2πinz)) = n·exp(2πinz)
-/
theorem D_qexp_term (n : ℕ) (a : ℂ) (z : ℍ) :
    D (fun w => a * cexp (2 * π * I * n * w)) z =
      n * a * cexp (2 * π * I * n * z) := by
  simp only [D]
  -- Compute the derivative of a * exp(2πinz)
  have h_deriv : deriv ((fun w : ℍ => a * cexp (2 * π * I * n * w)) ∘ ofComplex) (z : ℂ) =
      a * (2 * π * I * n) * cexp (2 * π * I * n * z) := by
    -- Step 1: Derivative of exp(2πinz) using chain rule
    have h_exp_deriv : HasDerivAt (fun w : ℂ => a * cexp (2 * π * I * n * w))
        (a * (2 * π * I * n) * cexp (2 * π * I * n * z)) (z : ℂ) := by
      have h_at_arg : HasDerivAt cexp (cexp (2 * π * I * n * z)) (2 * π * I * n * z) :=
        Complex.hasDerivAt_exp (2 * π * I * n * z)
      have h_linear : HasDerivAt (fun w : ℂ => 2 * π * I * n * w) (2 * π * I * n) (z : ℂ) := by
        have h := (hasDerivAt_id (z : ℂ)).const_mul (2 * π * I * n)
        simp only [mul_one, id] at h
        exact h
      have h_comp := h_at_arg.scomp (z : ℂ) h_linear
      -- Rewrite the scalar multiplication as multiplication
      simp only [smul_eq_mul] at h_comp
      have h_const_mul := h_comp.const_mul a
      convert h_const_mul using 1; ring
    -- Step 2: The composed function equals the ℂ function in a neighborhood of z
    have h_agree : ((fun w : ℍ => a * cexp (2 * π * I * n * w)) ∘ ofComplex) =ᶠ[nhds (z : ℂ)]
        (fun w : ℂ => a * cexp (2 * π * I * n * w)) := by
      have him : 0 < (z : ℂ).im := z.2
      have h_open : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [h_open.mem_nhds him] with w hw
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, coe_mk_subtype]
    exact h_agree.deriv_eq.trans h_exp_deriv.deriv
  rw [h_deriv]
  -- Simplify: (2πi)⁻¹ * a * (2πin) * exp(...) = n * a * exp(...)
  have h_2piI_ne : (2 : ℂ) * π * I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero, pi_ne_zero, I_ne_zero,
      or_self, not_false_eq_true]
  field_simp [h_2piI_ne]

/--
Variant of `D_qexp_term` for integer exponents, covering negative powers in theta series.
D(a·q^n) = n·a·q^n where q = exp(2πiz) and n ∈ ℤ.
-/
theorem D_qexp_term_int (n : ℤ) (a : ℂ) (z : ℍ) :
    D (fun w => a * cexp (2 * π * I * n * w)) z =
      n * a * cexp (2 * π * I * n * z) := by
  simp only [D]
  have h_deriv : deriv ((fun w : ℍ => a * cexp (2 * π * I * n * w)) ∘ ofComplex) (z : ℂ) =
      a * (2 * π * I * n) * cexp (2 * π * I * n * z) := by
    have h_exp_deriv : HasDerivAt (fun w : ℂ => a * cexp (2 * π * I * n * w))
        (a * (2 * π * I * n) * cexp (2 * π * I * n * z)) (z : ℂ) := by
      have h_at_arg : HasDerivAt cexp (cexp (2 * π * I * n * z)) (2 * π * I * n * z) :=
        Complex.hasDerivAt_exp (2 * π * I * n * z)
      have h_linear : HasDerivAt (fun w : ℂ => 2 * π * I * n * w) (2 * π * I * n) (z : ℂ) := by
        have h := (hasDerivAt_id (z : ℂ)).const_mul (2 * π * I * n)
        simp only [mul_one, id] at h
        exact h
      have h_comp := h_at_arg.scomp (z : ℂ) h_linear
      simp only [smul_eq_mul] at h_comp
      have h_const_mul := h_comp.const_mul a
      convert h_const_mul using 1; ring
    have h_agree : ((fun w : ℍ => a * cexp (2 * π * I * n * w)) ∘ ofComplex) =ᶠ[nhds (z : ℂ)]
        (fun w : ℂ => a * cexp (2 * π * I * n * w)) := by
      have him : 0 < (z : ℂ).im := z.2
      have h_open : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [h_open.mem_nhds him] with w hw
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, coe_mk_subtype]
    exact h_agree.deriv_eq.trans h_exp_deriv.deriv
  rw [h_deriv]
  have h_2piI_ne : (2 : ℂ) * π * I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero, pi_ne_zero, I_ne_zero,
      or_self, not_false_eq_true]
  field_simp [h_2piI_ne]

/--
**Lemma 6.45 (Blueprint)**: D commutes with tsum for q-series.
If F(z) = Σ a(n)·qⁿ where q = exp(2πiz), then D F(z) = Σ n·a(n)·qⁿ.

More precisely, this lemma shows that for a ℕ-indexed q-series with summable coefficients
satisfying appropriate derivative bounds, D acts termwise by multiplying coefficients by n.
-/
theorem D_qexp_tsum (a : ℕ → ℂ) (z : ℍ)
    (_hsum : Summable (fun n => a n * cexp (2 * π * I * n * z)))
    (hsum_deriv : ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
        ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K), ‖a n * (2 * π * I * n) *
          cexp (2 * π * I * n * k.1)‖ ≤ u n) :
    D (fun w => ∑' n, a n * cexp (2 * π * I * n * w)) z =
      ∑' n : ℕ, (n : ℂ) * a n * cexp (2 * π * I * n * z) := by
  simp only [D]
  -- Use hasDerivAt_tsum_fun on the upper half-plane
  have hs : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hx : (z : ℂ) ∈ {w : ℂ | 0 < w.im} := z.2
  -- Each term is differentiable
  have hf_diff : ∀ n (r : {w : ℂ | 0 < w.im}), DifferentiableAt ℂ
      (fun w => a n * cexp (2 * π * I * n * w)) r := fun n r =>
    ((differentiableAt_id.const_mul (2 * π * I * n)).cexp).const_mul (a n)
  -- Summability at each point
  have hf_sum : ∀ y : ℂ, y ∈ {w : ℂ | 0 < w.im} →
      Summable (fun n => a n * cexp (2 * π * I * n * y)) := by
    intro y hy
    -- Singleton {y} is compact
    have hK_compact : IsCompact ({y} : Set ℂ) := isCompact_singleton
    have hK_sub : ({y} : Set ℂ) ⊆ {w : ℂ | 0 < w.im} := Set.singleton_subset_iff.mpr hy
    -- Apply hsum_deriv to get bound on derivative terms
    obtain ⟨u, hu_sum, hu_bound⟩ := hsum_deriv {y} hK_sub hK_compact
    -- For n ≥ 1: ‖a n * exp(...)‖ ≤ u n / ‖2πin‖ ≤ u n / (2π)
    -- For n = 0: term is just a(0), handle via cofinite filter (only finitely many exceptions)
    apply Summable.of_norm_bounded_eventually (g := fun n => u n / (2 * π))
        (hu_sum.div_const (2 * π))
    -- Bound holds eventually (i.e., for all but finitely many n)
    -- In fact, it holds for all n ≥ 1, so the exception set ⊆ {0}
    rw [Filter.eventually_cofinite]
    apply Set.Finite.subset (Set.finite_singleton 0)
    intro n hn
    simp only [Set.mem_setOf_eq, not_le] at hn
    simp only [Set.mem_singleton_iff]
    by_contra h_ne
    -- n ≥ 1, so we can derive the bound and get a contradiction
    have h_deriv_bound := hu_bound n ⟨y, Set.mem_singleton y⟩
    have h_n_ge_1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr h_ne)
    have h_2pi_pos : (0 : ℝ) < 2 * π := by positivity
    have hu_nn : 0 ≤ u n := le_trans (norm_nonneg _) h_deriv_bound
    -- Key bound: ‖a n * exp(2πiny)‖ ≤ u n / (2πn) ≤ u n / (2π)
    have h_bound : ‖a n * cexp (2 * π * I * n * y)‖ ≤ u n / (2 * π) := by
      -- ‖a n * exp(...)‖ ≤ ‖a n * 2πin * exp(...)‖ / ‖2πin‖ ≤ u n / (2πn)
      have h_factor_pos : (0 : ℝ) < 2 * π * n := by positivity
      -- ‖2πin‖ = 2πn
      have h_norm_2pin : ‖(2 : ℂ) * π * I * n‖ = 2 * π * n := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
            Complex.norm_I, mul_one, Complex.norm_natCast, Real.norm_of_nonneg (le_of_lt pi_pos)]
      -- The key algebraic step
      have h_mul_div : ‖a n * cexp (2 * π * I * n * y)‖ * (2 * π * n) =
          ‖a n * (2 * π * I * n) * cexp (2 * π * I * n * y)‖ := by
        rw [← h_norm_2pin]
        simp only [norm_mul]
        ring
      calc ‖a n * cexp (2 * π * I * n * y)‖
          = ‖a n * cexp (2 * π * I * n * y)‖ * (2 * π * n) / (2 * π * n) := by
            field_simp
        _ = ‖a n * (2 * π * I * n) * cexp (2 * π * I * n * y)‖ / (2 * π * n) := by
            rw [h_mul_div]
        _ ≤ u n / (2 * π * n) := by
            apply div_le_div_of_nonneg_right h_deriv_bound (le_of_lt h_factor_pos)
        _ ≤ u n / (2 * π) := by
            apply div_le_div_of_nonneg_left hu_nn h_2pi_pos
            have h2 : 2 * π * 1 ≤ 2 * π * n := by nlinarith
            linarith
    exact hn.not_ge h_bound
  -- Derivative bound for uniform convergence
  have hu : ∀ K ⊆ {w : ℂ | 0 < w.im}, IsCompact K →
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K),
        ‖derivWithin (fun w => a n * cexp (2 * π * I * n * w)) {w : ℂ | 0 < w.im} k‖ ≤ u n := by
    intro K hK1 hK2
    -- Derivative of a_n * exp(2πinz) is a_n * 2πin * exp(2πinz)
    have h_deriv_eq : ∀ n (k : K), derivWithin (fun w => a n * cexp (2 * π * I * n * w))
        {w : ℂ | 0 < w.im} k = a n * (2 * π * I * n) * cexp (2 * π * I * n * k.1) := by
      intro n k
      have h_chain : HasDerivAt (fun w : ℂ => a n * cexp (2 * π * I * n * w))
          (a n * (2 * π * I * n) * cexp (2 * π * I * n * k.1)) k.1 := by
        have h_exp := Complex.hasDerivAt_exp (2 * π * I * n * k.1)
        have h_lin' := (hasDerivAt_id k.1).const_mul (2 * π * I * n)
        simp only [id, mul_one] at h_lin'
        have h_comp := h_exp.scomp k.1 h_lin'
        simp only [smul_eq_mul] at h_comp
        convert h_comp.const_mul (a n) using 1; ring
      exact (h_chain.hasDerivWithinAt (s := {w : ℂ | 0 < w.im})).derivWithin
        (hs.uniqueDiffWithinAt (hK1 k.2))
    obtain ⟨u, hu_sum, hu_bound⟩ := hsum_deriv K hK1 hK2
    refine ⟨u, hu_sum, fun n k => ?_⟩
    rw [h_deriv_eq]
    exact hu_bound n k
  -- Apply termwise differentiation
  have h_tsum_deriv := hasDerivAt_tsum_fun (fun n w => a n * cexp (2 * π * I * n * w))
    hs (z : ℂ) hx hf_sum hu hf_diff
  -- The composed function with ofComplex equals the ℂ function in a neighborhood
  have h_agree : ((fun w : ℍ => ∑' n, a n * cexp (2 * π * I * n * w)) ∘ ofComplex) =ᶠ[nhds (z : ℂ)]
      (fun w => ∑' n, a n * cexp (2 * π * I * n * w)) := by
    filter_upwards [hs.mem_nhds hx] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, coe_mk_subtype]
  rw [h_agree.deriv_eq, h_tsum_deriv.deriv]
  -- Simplify: derivWithin equals 2πin * (term) on open set, factor out (2πi)⁻¹
  have h_deriv_simp : ∀ n, derivWithin (fun w => a n * cexp (2 * π * I * n * w))
      {w : ℂ | 0 < w.im} (z : ℂ) = a n * (2 * π * I * n) * cexp (2 * π * I * n * z) := by
    intro n
    have h_chain : HasDerivAt (fun w : ℂ => a n * cexp (2 * π * I * n * w))
        (a n * (2 * π * I * n) * cexp (2 * π * I * n * z)) (z : ℂ) := by
      have h_exp := Complex.hasDerivAt_exp (2 * π * I * n * z)
      have h_lin' := (hasDerivAt_id (z : ℂ)).const_mul (2 * π * I * n)
      simp only [id, mul_one] at h_lin'
      have h_comp := h_exp.scomp (z : ℂ) h_lin'
      simp only [smul_eq_mul] at h_comp
      convert h_comp.const_mul (a n) using 1; ring
    exact (h_chain.hasDerivWithinAt (s := {w : ℂ | 0 < w.im})).derivWithin
      (hs.uniqueDiffWithinAt hx)
  simp_rw [h_deriv_simp]
  -- Factor out (2πi)⁻¹ from the tsum
  have h_2piI_ne : (2 : ℂ) * π * I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero, pi_ne_zero, I_ne_zero,
      or_self, not_false_eq_true]
  rw [← tsum_mul_left]
  congr 1
  funext n
  field_simp [h_2piI_ne]

/--
Simplified version of `D_qexp_tsum` for ℕ+-indexed series (starting from n=1).
This is the form most commonly used for Eisenstein series q-expansions.
-/
theorem D_qexp_tsum_pnat (a : ℕ+ → ℂ) (z : ℍ)
    (_hsum : Summable (fun n : ℕ+ => a n * cexp (2 * π * I * n * z)))
    (hsum_deriv : ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
        ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ n (k : K), ‖a n * (2 * π * I * n) *
          cexp (2 * π * I * n * k.1)‖ ≤ u n) :
    D (fun w => ∑' n : ℕ+, a n * cexp (2 * π * I * n * w)) z =
      ∑' n : ℕ+, (n : ℂ) * a n * cexp (2 * π * I * n * z) := by
  simp only [D]
  -- Use hasDerivAt_tsum_fun on the upper half-plane
  have hs : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hx : (z : ℂ) ∈ {w : ℂ | 0 < w.im} := z.2
  -- Each term is differentiable
  have hf_diff : ∀ (n : ℕ+) (r : {w : ℂ | 0 < w.im}), DifferentiableAt ℂ
      (fun w => a n * cexp (2 * π * I * n * w)) r := fun n r =>
    ((differentiableAt_id.const_mul (2 * π * I * n)).cexp).const_mul (a n)
  -- Summability at each point - simpler than ℕ case since all n ≥ 1
  have hf_sum : ∀ y : ℂ, y ∈ {w : ℂ | 0 < w.im} →
      Summable (fun n : ℕ+ => a n * cexp (2 * π * I * n * y)) := by
    intro y hy
    have hK_compact : IsCompact ({y} : Set ℂ) := isCompact_singleton
    have hK_sub : ({y} : Set ℂ) ⊆ {w : ℂ | 0 < w.im} := Set.singleton_subset_iff.mpr hy
    obtain ⟨u, hu_sum, hu_bound⟩ := hsum_deriv {y} hK_sub hK_compact
    -- For ℕ+, every n ≥ 1, so bound holds uniformly
    apply Summable.of_norm_bounded (g := fun n => u n / (2 * π)) (hu_sum.div_const (2 * π))
    intro n
    have h_deriv_bound := hu_bound n ⟨y, Set.mem_singleton y⟩
    have h_n_ge_1 : (1 : ℝ) ≤ n := by exact_mod_cast n.one_le
    have h_2pi_pos : (0 : ℝ) < 2 * π := by positivity
    have hu_nn : 0 ≤ u n := le_trans (norm_nonneg _) h_deriv_bound
    -- Key bound: ‖a n * exp(2πiny)‖ ≤ u n / (2πn) ≤ u n / (2π)
    have h_factor_pos : (0 : ℝ) < 2 * π * n := by positivity
    have h_norm_2pin : ‖(2 : ℂ) * π * I * n‖ = 2 * π * n := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
          Complex.norm_I, mul_one, Complex.norm_natCast,
          Real.norm_of_nonneg (le_of_lt pi_pos)]
    have h_mul_div : ‖a n * cexp (2 * π * I * n * y)‖ * (2 * π * n) =
        ‖a n * (2 * π * I * n) * cexp (2 * π * I * n * y)‖ := by
      rw [← h_norm_2pin]
      simp only [norm_mul]
      ring
    calc ‖a n * cexp (2 * π * I * n * y)‖
        = ‖a n * cexp (2 * π * I * n * y)‖ * (2 * π * n) / (2 * π * n) := by field_simp
      _ = ‖a n * (2 * π * I * n) * cexp (2 * π * I * n * y)‖ / (2 * π * n) := by rw [h_mul_div]
      _ ≤ u n / (2 * π * n) := by
          apply div_le_div_of_nonneg_right h_deriv_bound (le_of_lt h_factor_pos)
      _ ≤ u n / (2 * π) := by
          apply div_le_div_of_nonneg_left hu_nn h_2pi_pos
          have h2 : 2 * π * 1 ≤ 2 * π * n := by nlinarith
          linarith
  -- Derivative bound for uniform convergence
  have hu : ∀ K ⊆ {w : ℂ | 0 < w.im}, IsCompact K →
      ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ n (k : K),
        ‖derivWithin (fun w => a n * cexp (2 * π * I * n * w)) {w : ℂ | 0 < w.im} k‖ ≤ u n := by
    intro K hK1 hK2
    have h_deriv_eq : ∀ n (k : K), derivWithin (fun w => a n * cexp (2 * π * I * n * w))
        {w : ℂ | 0 < w.im} k = a n * (2 * π * I * n) * cexp (2 * π * I * n * k.1) := by
      intro n k
      have h_chain : HasDerivAt (fun w : ℂ => a n * cexp (2 * π * I * n * w))
          (a n * (2 * π * I * n) * cexp (2 * π * I * n * k.1)) k.1 := by
        have h_exp := Complex.hasDerivAt_exp (2 * π * I * n * k.1)
        have h_lin' := (hasDerivAt_id k.1).const_mul (2 * π * I * n)
        simp only [id, mul_one] at h_lin'
        have h_comp := h_exp.scomp k.1 h_lin'
        simp only [smul_eq_mul] at h_comp
        convert h_comp.const_mul (a n) using 1; ring
      exact (h_chain.hasDerivWithinAt (s := {w : ℂ | 0 < w.im})).derivWithin
        (hs.uniqueDiffWithinAt (hK1 k.2))
    obtain ⟨u, hu_sum, hu_bound⟩ := hsum_deriv K hK1 hK2
    refine ⟨u, hu_sum, fun n k => ?_⟩
    rw [h_deriv_eq]
    exact hu_bound n k
  -- Apply termwise differentiation
  have h_tsum_deriv := hasDerivAt_tsum_fun (fun n w => a n * cexp (2 * π * I * n * w))
    hs (z : ℂ) hx hf_sum hu hf_diff
  -- The composed function with ofComplex equals the ℂ function in a neighborhood
  have h_agree : ((fun w : ℍ => ∑' n : ℕ+, a n * cexp (2 * π * I * n * w)) ∘ ofComplex)
      =ᶠ[nhds (z : ℂ)] (fun w => ∑' n : ℕ+, a n * cexp (2 * π * I * n * w)) := by
    filter_upwards [hs.mem_nhds hx] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, coe_mk_subtype]
  rw [h_agree.deriv_eq, h_tsum_deriv.deriv]
  -- Simplify: derivWithin equals 2πin * (term) on open set, factor out (2πi)⁻¹
  have h_deriv_simp : ∀ n : ℕ+, derivWithin (fun w => a n * cexp (2 * π * I * n * w))
      {w : ℂ | 0 < w.im} (z : ℂ) = a n * (2 * π * I * n) * cexp (2 * π * I * n * z) := by
    intro n
    have h_chain : HasDerivAt (fun w : ℂ => a n * cexp (2 * π * I * n * w))
        (a n * (2 * π * I * n) * cexp (2 * π * I * n * z)) (z : ℂ) := by
      have h_exp := Complex.hasDerivAt_exp (2 * π * I * n * z)
      have h_lin' := (hasDerivAt_id (z : ℂ)).const_mul (2 * π * I * n)
      simp only [id, mul_one] at h_lin'
      have h_comp := h_exp.scomp (z : ℂ) h_lin'
      simp only [smul_eq_mul] at h_comp
      convert h_comp.const_mul (a n) using 1; ring
    exact (h_chain.hasDerivWithinAt (s := {w : ℂ | 0 < w.im})).derivWithin
      (hs.uniqueDiffWithinAt hx)
  simp_rw [h_deriv_simp]
  -- Factor out (2πi)⁻¹ from the tsum
  have h_2piI_ne : (2 : ℂ) * π * I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero, pi_ne_zero, I_ne_zero,
      or_self, not_false_eq_true]
  rw [← tsum_mul_left]
  congr 1
  funext n
  field_simp [h_2piI_ne]

/--
Serre derivative of weight $k$.
Note that the definition makes sense for any analytic function $F : \mathbb{H} \to \mathbb{C}$.
-/
noncomputable def serre_D (k : ℂ) : (ℍ → ℂ) → (ℍ → ℂ) :=
  fun (F : ℍ → ℂ) => (fun z => D F z - k * 12⁻¹ * E₂ z * F z)

/--
Basic properties of Serre derivative: linearity, Leibniz rule, etc.
-/
theorem serre_D_add (k : ℤ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) : serre_D k (F + G) = serre_D k F + serre_D k G := by
  ext z
  simp only [serre_D, Pi.add_apply, D_add F G hF hG]
  ring_nf

theorem serre_D_sub (k : ℤ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) : serre_D k (F - G) = serre_D k F - serre_D k G := by
  ext z
  simp only [serre_D, Pi.sub_apply, D_sub F G hF hG]
  ring_nf

theorem serre_D_smul (k : ℤ) (c : ℂ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    serre_D k (c • F) = c • (serre_D k F) := by
  calc
    serre_D k (c • F) = D (c • F) - k * 12⁻¹ * E₂ * (c • F) := by rfl
    _ = c • D F - k * 12⁻¹ * E₂ * (c • F) := by rw [D_smul c F hF]
    _ = c • D F - c • (k * 12⁻¹ * E₂ * F) := by simp
    _ = c • (D F - k * 12⁻¹ * E₂ * F) := by rw [←smul_sub]
    _ = c • (serre_D k F) := by rfl

theorem serre_D_mul (k₁ k₂ : ℤ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) :
    serre_D (k₁ + k₂) (F * G) = (serre_D k₁ F) * G + F * (serre_D k₂ G) := by
  calc
    serre_D (k₁ + k₂) (F * G)
    _ = D (F * G) - (k₁ + k₂) * 12⁻¹ * E₂ * (F * G) := by rfl
    _ = (D F * G + F * D G) - (k₁ + k₂) * 12⁻¹ * E₂ * (F * G) := by
        rw [D_mul F G hF hG]
    _ = (D F - k₁ * 12⁻¹ * E₂ * F) * G
        + F * (D G - k₂ * 12⁻¹ * E₂ * G) := by ring_nf
    _ = (serre_D k₁ F) * G + F * (serre_D k₂ G) := by rfl

/--
The Serre derivative preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `serre_D k F` is also MDifferentiable.
-/
theorem serre_D_differentiable {F : ℍ → ℂ} {k : ℂ}
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D k F) := by
  have h_term : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => k * 12⁻¹ * E₂ z * F z) := by
    have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => (k * 12⁻¹) * (E₂ z * F z)) :=
      MDifferentiable.mul mdifferentiable_const (E₂_holo'.mul hF)
    convert h1 using 1; ext z; simp only [mul_assoc]
  exact (D_differentiable hF).sub h_term

/-! ### Helper lemmas for D_slash

These micro-lemmas compute derivatives of the components in the slash action formula.
-/

section DSlashHelpers

open ModularGroup

variable (γ : SL(2, ℤ))

/-- Derivative of the denominator function: d/dz[cz + d] = c. -/
lemma deriv_denom (z : ℂ) :
    deriv (fun w => denom γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) := by
  simp only [denom]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]; simp

/-- Derivative of the numerator function: d/dz[az + b] = a. -/
lemma deriv_num (z : ℂ) :
    deriv (fun w => num γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) := by
  simp only [num]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]; simp

/-- Differentiability of denom. -/
lemma differentiableAt_denom (z : ℂ) :
    DifferentiableAt ℂ (fun w => denom γ w) z := by
  simp only [denom]
  fun_prop

/-- Differentiability of num. -/
lemma differentiableAt_num (z : ℂ) :
    DifferentiableAt ℂ (fun w => num γ w) z := by
  simp only [num]
  fun_prop

/-- Derivative of the Möbius transformation: d/dz[(az+b)/(cz+d)] = 1/(cz+d)².
Uses det(γ) = 1: a(cz+d) - c(az+b) = ad - bc = 1. -/
lemma deriv_moebius (z : ℍ) :
    deriv (fun w => num γ w / denom γ w) z = 1 / (denom γ z) ^ 2 := by
  have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (γ 1 1) -
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * (γ 1 0) = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    simp only [Matrix.det_fin_two, ← Int.cast_mul, ← Int.cast_sub] at this ⊢
    exact_mod_cast this
  rw [deriv_fun_div (differentiableAt_num γ z) (differentiableAt_denom γ z) hz,
      deriv_num, deriv_denom]
  simp only [denom_apply, num, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    Matrix.map_apply, ofReal_intCast] at *
  have hnum_eq : ((γ 0 0 : ℤ) : ℂ) * ((γ 1 0 : ℤ) * z + (γ 1 1 : ℤ)) -
      ((γ 0 0 : ℤ) * z + (γ 0 1 : ℤ)) * (γ 1 0 : ℤ) = 1 := by linear_combination hdet
  simp only [hnum_eq, one_div]

/-- Derivative of denom^(-k): d/dz[(cz+d)^(-k)] = -k * c * (cz+d)^(-k-1). -/
lemma deriv_denom_zpow (k : ℤ) (z : ℍ) :
    deriv (fun w => (denom γ w) ^ (-k)) z =
        (-k : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (denom γ z) ^ (-k - 1) := by
  have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdiff := differentiableAt_denom γ (z : ℂ)
  have hderiv_zpow := hasDerivAt_zpow (-k) (denom γ z) (Or.inl hz)
  have hderiv_denom : HasDerivAt (fun w => denom γ w)
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) (z : ℂ) := by
    rw [← deriv_denom]; exact hdiff.hasDerivAt
  have hcomp := hderiv_zpow.comp (z : ℂ) hderiv_denom
  have heq : (fun w => w ^ (-k)) ∘ (fun w => denom γ w) = (fun w => (denom γ w) ^ (-k)) := rfl
  rw [← heq, hcomp.deriv]; simp only [Int.cast_neg]; ring

end DSlashHelpers

/--
The derivative anomaly: how D interacts with the slash action.
This is the key computation for proving Serre derivative equivariance.
-/
lemma D_slash (k : ℤ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (γ : SL(2, ℤ)) :
    D (F ∣[k] γ) = (D F ∣[k + 2] γ) -
        (fun z : ℍ => (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z) := by
  -- Strategy (all micro-lemmas proven above):
  -- 1. SL_slash_apply: (F ∣[k] γ) z = F(γ•z) * denom(γ,z)^(-k)
  -- 2. coe_smul_of_det_pos: (γ•z : ℂ) = num γ z / denom γ z (since det(SL₂) = 1 > 0)
  -- 3. Product rule: deriv[f*g] = f*deriv[g] + deriv[f]*g
  -- 4. Chain rule: deriv[F ∘ mobius] = deriv[F](mobius z) * deriv_moebius
  -- 5. deriv_moebius: d/dz[num/denom] = 1/denom² (uses det = 1)
  -- 6. deriv_denom_zpow: d/dz[denom^(-k)] = -k * c * denom^(-k-1)
  --
  -- Computation (product rule + chain rule):
  -- D(F ∣[k] γ) = (2πi)⁻¹ * deriv[F(γ•·) * denom^(-k)]
  --   = (2πi)⁻¹ * [F(γ•z)*(-k*c*denom^(-k-1)) + deriv[F](γ•z)*(1/denom²)*denom^(-k)]
  --   = (D F ∣[k+2] γ) - k*(2πi)⁻¹*(c/denom)*(F ∣[k] γ)
  ext z
  unfold D
  simp only [Pi.sub_apply]
  -- Key facts about denom and determinant (used multiple times below)
  have hz_denom_ne : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdet_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
  -- The derivative computation on ℂ using Filter.EventuallyEq.deriv_eq
  -- (F ∣[k] γ) ∘ ofComplex agrees with F(num/denom) * denom^(-k) on ℍ
  have hcomp : deriv (((F ∣[k] γ)) ∘ ofComplex) z =
      deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    rw [ModularForm.SL_slash_apply (f := F) (k := k) γ ⟨w, hw⟩]
    -- Key: (γ • ⟨w, hw⟩ : ℂ) = num γ w / denom γ w
    congr 1
    · -- F (γ • ⟨w, hw⟩) = (F ∘ ofComplex) (num γ w / denom γ w)
      -- Need: γ • ⟨w, hw⟩ = ofComplex (num γ w / denom γ w) as points in ℍ
      -- The smul result as element of ℍ, then coerce to ℂ
      let gz : ℍ := γ • ⟨w, hw⟩
      -- The key: (gz : ℂ) = num/denom (using the lemma for GL coercion)
      have hsmul_coe : (gz : ℂ) = num γ w / denom γ w := by
        have h := UpperHalfPlane.coe_smul_of_det_pos hdet_pos ⟨w, hw⟩
        simp only [gz] at h ⊢
        exact h
      -- im(num/denom) > 0 follows from gz ∈ ℍ
      have hmob_im : (num γ w / denom γ w).im > 0 := by
        rw [← hsmul_coe]; exact gz.im_pos
      -- Now F(gz) = F(ofComplex(num/denom)) = (F ∘ ofComplex)(num/denom)
      -- gz = γ • ⟨w, hw⟩, so F gz = F (γ • ⟨w, hw⟩)
      congr 1
      -- Show gz = ofComplex (num/denom) as points in ℍ
      apply Subtype.ext
      rw [ofComplex_apply_of_im_pos hmob_im]
      exact hsmul_coe
  rw [hcomp]
  -- Now apply product rule: deriv[f * g] = f * deriv[g] + deriv[f] * g
  -- where f(w) = (F ∘ ofComplex)(num w / denom w) and g(w) = denom(w)^(-k)
  --
  -- Setup differentiability for product rule
  have hdenom_ne : ∀ w : ℂ, w.im > 0 → denom γ w ≠ 0 := fun w hw =>
    UpperHalfPlane.denom_ne_zero γ ⟨w, hw⟩
  have hdiff_denom_zpow : DifferentiableAt ℂ (fun w => (denom γ w) ^ (-k)) z :=
    DifferentiableAt.zpow (differentiableAt_denom γ z) (Or.inl (hdenom_ne z z.im_pos))
  -- For the F ∘ (num/denom) term, we need differentiability of the Möbius and F
  have hdiff_mobius : DifferentiableAt ℂ (fun w => num γ w / denom γ w) z :=
    (differentiableAt_num γ z).div (differentiableAt_denom γ z) (hdenom_ne z z.im_pos)
  -- The composition (F ∘ ofComplex) ∘ mobius is differentiable at z
  -- because mobius(z) is in ℍ and F is MDifferentiable
  have hmobius_in_H : (num γ z / denom γ z).im > 0 := by
    rw [← UpperHalfPlane.coe_smul_of_det_pos hdet_pos z]
    exact (γ • z).im_pos
  have hdiff_F_comp : DifferentiableAt ℂ (F ∘ ofComplex) (num γ z / denom γ z) :=
    MDifferentiableAt_DifferentiableAt (hF ⟨num γ z / denom γ z, hmobius_in_H⟩)
  have hcomp_eq : (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) =
      (F ∘ ofComplex) ∘ (fun w => num γ w / denom γ w) := rfl
  have hdiff_F_mobius : DifferentiableAt ℂ (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z := by
    rw [hcomp_eq]
    exact DifferentiableAt.comp (z : ℂ) hdiff_F_comp hdiff_mobius
  -- Apply product rule
  -- Note: need to show the functions are equal to use deriv_mul
  have hfun_eq : (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) =
      ((fun w => (F ∘ ofComplex) (num γ w / denom γ w)) * (fun w => (denom γ w) ^ (-k))) := rfl
  rw [hfun_eq]
  have hprod := deriv_mul hdiff_F_mobius hdiff_denom_zpow
  rw [hprod]
  -- Apply chain rule to (F ∘ ofComplex) ∘ mobius
  have hchain : deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z =
      deriv (F ∘ ofComplex) (num γ z / denom γ z) * deriv (fun w => num γ w / denom γ w) z := by
    rw [hcomp_eq, (hdiff_F_comp.hasDerivAt.comp (z : ℂ) hdiff_mobius.hasDerivAt).deriv]
  -- Substitute the micro-lemmas
  have hderiv_mob := deriv_moebius γ z
  have hderiv_zpow := deriv_denom_zpow γ k z
  rw [hchain, hderiv_mob, hderiv_zpow]
  -- Now we have:
  -- (2πi)⁻¹ * [deriv(F∘ofComplex)(mob z) * (1/denom²) * denom^(-k) +
  --            (F∘ofComplex)(mob z) * (-k * c * denom^(-k-1))]
  -- = (D F ∣[k+2] γ) z - k * (2πi)⁻¹ * (c/denom) * (F ∣[k] γ) z
  --
  -- Key observations:
  -- - (2πi)⁻¹ * deriv(F∘ofComplex)(mob z) = D F (γ • z)  (by def of D)
  -- - denom^(-k) / denom² = denom^(-k-2)
  -- - (D F)(γ • z) * denom^(-k-2) = (D F ∣[k+2] γ) z
  -- - (F∘ofComplex)(mob z) * denom^(-k) = F(γ • z) * denom^(-k) = (F ∣[k] γ) z
  -- - -k * c * denom^(-k-1) * (2πi)⁻¹ = -k * (2πi)⁻¹ * c/denom * denom^(-k)
  --
  -- Relate mobius to γ • z: ↑(γ • z) = num/denom (explicit coercion from ℍ to ℂ)
  have hmob_eq : ↑(γ • z) = num γ z / denom γ z :=
    UpperHalfPlane.coe_smul_of_det_pos hdet_pos z
  -- Relate (F ∘ ofComplex)(mob z) to F(γ • z)
  have hF_mob : (F ∘ ofComplex) (num γ z / denom γ z) = F (γ • z) := by
    simp only [Function.comp_apply, ← hmob_eq, ofComplex_apply]
  -- Final algebraic manipulation
  -- Goal: (2πi)⁻¹ * (deriv(F∘ofComplex)(mob z) * (1/denom²) * denom^(-k) +
  --                   (F∘ofComplex)(mob z) * (-k * c * denom^(-k-1)))
  --      = D F(γ•z) * denom^(-(k+2)) - k * (2πi)⁻¹ * (c/denom) * F(γ•z) * denom^(-k)
  -- This follows from the above lemmas by algebraic manipulation
  --
  -- First expand the slash action on the RHS and normalize denom coercions
  simp only [ModularForm.SL_slash_apply, hF_mob, hmob_eq]
  -- Now both sides should have normalized denom (num/denom arguments and ℂ coercions)
  -- Key identities for zpow:
  -- (1/denom²) * denom^(-k) = denom^(-2) * denom^(-k) = denom^(-k-2) = denom^(-(k+2))
  -- -k * c * denom^(-k-1) = -k * (c/denom) * denom^(-k)
  --
  -- Use zpow identities
  have hpow_combine : 1 / (denom γ z) ^ 2 * (denom γ z) ^ (-k) = (denom γ z) ^ (-(k + 2)) := by
    rw [one_div, ← zpow_natCast (denom γ z) 2, ← zpow_neg, ← zpow_add₀ hz_denom_ne]
    congr 1
    ring
  have hpow_m1 : (denom γ z) ^ (-k - 1) = (denom γ z) ^ (-1 : ℤ) * (denom γ z) ^ (-k) := by
    rw [← zpow_add₀ hz_denom_ne]
    congr 1
    ring
  -- Rewrite powers on LHS
  conv_lhs =>
    rw [mul_assoc (deriv (F ∘ ofComplex) (num γ z / denom γ z)) (1 / denom γ z ^ 2) _]
    rw [hpow_combine, hpow_m1]
  -- Now the goal should be cleaner - distribute and simplify
  simp only [zpow_neg_one]
  ring

/--
Serre derivative is equivariant under the slash action. More precisely, if `F` is invariant
under the slash action of weight `k`, then `serre_D k F` is invariant under the slash action
of weight `k + 2`.
-/
theorem serre_D_slash_equivariant (k : ℤ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    ∀ γ : SL(2, ℤ), serre_D k F ∣[k + 2] γ = serre_D k (F ∣[k] γ) := by sorry

theorem serre_D_slash_invariant (k : ℤ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (γ : SL(2, ℤ)) (h : F ∣[k] γ = F) :
    serre_D k F ∣[k + 2] γ = serre_D k F := by
  rw [serre_D_slash_equivariant, h]
  exact hF

/--
Serre derivative of Eisenstein series. Use `serre_D_slash_invariant` and compare constant terms.
Note that the dimensions of the spaces of modular forms are all 1.
-/
theorem ramanujan_E₂' : serre_D 1 E₂ = - 12⁻¹ * E₄.toFun := by sorry

theorem ramanujan_E₄' : serre_D 4 E₄.toFun = - 3⁻¹ * E₆.toFun := by sorry

theorem ramanujan_E₆' : serre_D 6 E₆.toFun = - 2⁻¹ * E₄.toFun * E₄.toFun := by sorry

@[simp]
theorem ramanujan_E₂ : D E₂ = 12⁻¹ * (E₂ * E₂ - E₄.toFun) := by
  ext z
  have h := ramanujan_E₂'
  unfold serre_D at h
  have h1 := congrFun h z
  simp [field]
  field_simp at h1
  simpa [add_comm, sub_eq_iff_eq_add] using h1

@[simp]
theorem ramanujan_E₄ : D E₄.toFun = 3⁻¹ * (E₂ * E₄.toFun - E₆.toFun) := by
  ext z
  have h := ramanujan_E₄'
  unfold serre_D at h
  have h1 := congrFun h z
  simp [field]
  simp [field] at h1
  ring_nf
  ring_nf at h1
  have hc : (12 : ℂ) ≠ 0 := by norm_num
  apply (mul_right_inj' hc).mp
  ring_nf
  simpa [add_comm, sub_eq_iff_eq_add] using h1

@[simp]
theorem ramanujan_E₆ : D E₆.toFun = 2⁻¹ * (E₂ * E₆.toFun - E₄.toFun * E₄.toFun) := by
  ext z
  have h := ramanujan_E₆'
  unfold serre_D at h
  have h1 := congrFun h z
  simp [field]
  simp [field] at h1
  ring_nf
  ring_nf at h1
  have hc : (12 : ℂ) ≠ 0 := by norm_num
  apply (mul_right_inj' hc).mp
  ring_nf
  simpa [add_comm, sub_eq_iff_eq_add] using h1

/- TODO: remove later -/
example : D (E₄.toFun * E₄.toFun) = 2 * 3⁻¹ * E₄.toFun * (E₂ * E₄.toFun - E₆.toFun) :=
  by
  rw [D_mul E₄.toFun E₄.toFun]
  · simp only [ramanujan_E₄]
    ring_nf
  · exact E₄.holo'
  · exact E₄.holo'

/-
Interaction between (Serre) derivative and restriction to the imaginary axis.
-/
lemma StrictAntiOn.eventuallyPos_Ioi {g : ℝ → ℝ} (hAnti : StrictAntiOn g (Set.Ioi (0 : ℝ)))
    {t₀ : ℝ} (ht₀_pos : 0 < t₀) (hEv : ∀ t : ℝ, t₀ ≤ t → 0 < g t) :
    ∀ t : ℝ, 0 < t → 0 < g t := by
  intro t ht
  by_cases hcase : t₀ ≤ t
  · exact hEv t hcase
  · exact lt_trans (hEv t₀ le_rfl) (hAnti ht ht₀_pos (lt_of_not_ge hcase))

/--
Chain rule for restriction to imaginary axis: `d/dt F(it) = -2π * (D F)(it)`.

This connects the real derivative along the imaginary axis to the normalized derivative D.
The key computation is:
- The imaginary axis is parametrized by g(t) = I * t
- By chain rule: d/dt F(it) = (dF/dz)(it) · (d/dt)(it) = F'(it) · I
- Since D = (2πi)⁻¹ · d/dz, we have F' = 2πi · D F
- So d/dt F(it) = 2πi · D F(it) · I = -2π · D F(it)
-/
theorem deriv_resToImagAxis_eq (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) {t : ℝ} (ht : 0 < t) :
    deriv F.resToImagAxis t = -2 * π * (D F).resToImagAxis t := by
  let z : ℍ := ⟨I * t, by simp [ht]⟩
  let g : ℝ → ℂ := (I * ·)
  have h_eq : F.resToImagAxis =ᶠ[nhds t] ((F ∘ ofComplex) ∘ g) := by
    filter_upwards [lt_mem_nhds ht] with s hs
    have him : 0 < (g s).im := by simp [g, hs]
    simp [Function.resToImagAxis_apply, ResToImagAxis, hs, Function.comp_apply, g,
      ofComplex_apply_of_im_pos him]
  rw [h_eq.deriv_eq]
  have hg : HasDerivAt g I t := by simpa using ofRealCLM.hasDerivAt.const_mul I
  have hF' := (MDifferentiableAt_DifferentiableAt (hF z)).hasDerivAt
  rw [(hF'.scomp t hg).deriv]
  have hD : deriv (F ∘ ofComplex) z = 2 * π * I * D F z := by simp only [D]; field_simp
  simp only [hD, Function.resToImagAxis_apply, ResToImagAxis, dif_pos ht, z, smul_eq_mul]
  ring_nf; simp only [I_sq]; ring

/--
Chain rule for restriction to imaginary axis: `d/dt F(it) = -2π * (D F)(it)`.

This connects the real derivative along the imaginary axis to the normalized derivative D.
The key computation is:
- The imaginary axis is parametrized by g(t) = I * t
- By chain rule: d/dt F(it) = (dF/dz)(it) · (d/dt)(it) = F'(it) · I
- Since D = (2πi)⁻¹ · d/dz, we have F' = 2πi · D F
- So d/dt F(it) = 2πi · D F(it) · I = -2π · D F(it)
-/
theorem deriv_resToImagAxis_eq (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    {t : ℝ} (ht : 0 < t) :
    deriv F.resToImagAxis t = -2 * π * (D F).resToImagAxis t := by
  let z : ℍ := ⟨I * t, by simp [ht]⟩
  let g : ℝ → ℂ := (I * ·)
  have h_eq : F.resToImagAxis =ᶠ[nhds t] ((F ∘ ofComplex) ∘ g) := by
    filter_upwards [lt_mem_nhds ht] with s hs
    have him : 0 < (g s).im := by simp [g, hs]
    simp [Function.resToImagAxis_apply, ResToImagAxis, hs, Function.comp_apply, g,
      ofComplex_apply_of_im_pos him]
  rw [h_eq.deriv_eq]
  have hg : HasDerivAt g I t := by simpa using ofRealCLM.hasDerivAt.const_mul I
  have hF' := (MDifferentiableAt_DifferentiableAt (hF z)).hasDerivAt
  rw [(hF'.scomp t hg).deriv]
  have hD : deriv (F ∘ ofComplex) z = 2 * π * I * D F z := by simp only [D]; field_simp
  simp only [hD, Function.resToImagAxis_apply, ResToImagAxis, dif_pos ht, z, smul_eq_mul]
  ring_nf; simp only [I_sq]; ring

/--
If $F$ is a modular form where $F(it)$ is positive for sufficiently large $t$ (i.e. constant term
is positive) and the derivative is positive, then $F$ is also positive.
-/
theorem antiDerPos {F : ℍ → ℂ} (hFderiv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hFepos : ResToImagAxis.EventuallyPos F) (hDF : ResToImagAxis.Pos (D F)) :
    ResToImagAxis.Pos F := by
  obtain ⟨hF_real, t₀, ht₀_pos, hF_pos⟩ := hFepos
  obtain ⟨-, hDF_pos⟩ := hDF
  let g := fun t => (F.resToImagAxis t).re
  have hg : ∀ t, 0 < t → HasDerivAt g (-2 * π * (ResToImagAxis (D F) t).re) t := fun t ht => by
    have hdiff : DifferentiableAt ℝ F.resToImagAxis t :=
      ResToImagAxis.Differentiable F hFderiv t ht
    have hderivC : HasDerivAt F.resToImagAxis (-2 * π * (D F).resToImagAxis t) t :=
      hdiff.hasDerivAt.congr_deriv (deriv_resToImagAxis_eq F hFderiv ht)
    have hconst : HasDerivAt (fun _ : ℝ => (Complex.reCLM : ℂ →L[ℝ] ℝ)) 0 t := by
      simpa using (hasDerivAt_const (x := t) (c := (Complex.reCLM : ℂ →L[ℝ] ℝ)))
    have hreal := hconst.clm_apply hderivC
    simpa [g] using hreal
  have hn : ∀ t ∈ Set.Ioi (0 : ℝ), deriv g t < 0 := fun t (ht : 0 < t) => by
    rw [(hg t ht).deriv]
    have ht' : 0 < (ResToImagAxis (D F) t).re := hDF_pos t ht
    nlinarith [Real.pi_pos]
  have gpos := fun t ht =>
    StrictAntiOn.eventuallyPos_Ioi (strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
      (by simpa [interior_Ioi] using hn)) ht₀_pos hF_pos t ht
  exact ⟨hF_real, gpos⟩

/--
Let $F : \mathbb{H} \to \mathbb{C}$ be a holomorphic function where $F(it)$ is real for all $t > 0$.
Assume that Serre derivative $\partial_k F$ is positive on the imaginary axis.
If $F(it)$ is positive for sufficiently large $t$, then $F(it)$ is positive for all $t > 0$.
-/
theorem antiSerreDerPos {F : ℍ → ℂ} {k : ℤ} (hSDF : ResToImagAxis.Pos (serre_D k F))
    (hF : ResToImagAxis.EventuallyPos F) : ResToImagAxis.Pos F := by
  sorry

/-! ## Cauchy Estimates for D-derivative

Infrastructure for bounding derivatives using Cauchy estimates on disks in the upper half plane.
-/

/-- If `f : ℍ → ℂ` is `MDifferentiable` and a closed disk in `ℂ` lies in the upper
half-plane, then `f ∘ ofComplex` is `DiffContOnCl` on the corresponding open disk. -/
lemma diffContOnCl_comp_ofComplex_of_mdifferentiable {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {c : ℂ} {R : ℝ}
    (hclosed : Metric.closedBall c R ⊆ {z : ℂ | 0 < z.im}) :
    DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball c R) :=
  ⟨fun z hz => (MDifferentiableAt_DifferentiableAt
      (hf ⟨z, hclosed (Metric.ball_subset_closedBall hz)⟩)).differentiableWithinAt,
   fun z hz => (MDifferentiableAt_DifferentiableAt
      (hf ⟨z, hclosed (Metric.closure_ball_subset_closedBall hz)⟩)).continuousAt.continuousWithinAt⟩

/-- Closed ball centered at z with radius z.im/2 is contained in the upper half plane. -/
lemma closedBall_center_subset_upperHalfPlane (z : ℍ) :
    Metric.closedBall (z : ℂ) (z.im / 2) ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  have hdist : dist w z ≤ z.im / 2 := Metric.mem_closedBall.mp hw
  have habs : |w.im - z.im| ≤ z.im / 2 := calc |w.im - z.im|
    _ = |(w - z).im| := by simp [Complex.sub_im]
    _ ≤ ‖w - z‖ := abs_im_le_norm _
    _ = dist w z := (dist_eq_norm _ _).symm
    _ ≤ z.im / 2 := hdist
  have hlower : z.im / 2 ≤ w.im := by linarith [(abs_le.mp habs).1]
  exact lt_of_lt_of_le (by linarith [z.im_pos] : 0 < z.im / 2) hlower

/-- Cauchy estimate for the D-derivative: if `f ∘ ofComplex` is holomorphic on a disk
of radius `r` around `z` and bounded by `M` on the boundary sphere,
then `‖D f z‖ ≤ M / (2πr)`. -/
lemma norm_D_le_of_sphere_bound {f : ℍ → ℂ} {z : ℍ} {r M : ℝ}
    (hr : 0 < r) (hDiff : DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball (z : ℂ) r))
    (hbdd : ∀ w ∈ Metric.sphere (z : ℂ) r, ‖(f ∘ ofComplex) w‖ ≤ M) :
    ‖D f z‖ ≤ M / (2 * π * r) := calc ‖D f z‖
  _ = ‖(2 * π * I)⁻¹‖ * ‖deriv (f ∘ ofComplex) z‖ := by simp [D]
  _ = (2 * π)⁻¹ * ‖deriv (f ∘ ofComplex) z‖ := by simp [abs_of_pos Real.pi_pos]
  _ ≤ (2 * π)⁻¹ * (M / r) := by
        gcongr; exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hDiff hbdd
  _ = M / (2 * π * r) := by ring

/-- The D-derivative is bounded at infinity for bounded holomorphic functions.

For y large (y ≥ 2·max(A,0) + 1), we use a ball of radius z.im/2 around z.
The ball lies in the upper half plane, f is bounded by M on it, and
`norm_D_le_of_sphere_bound` gives ‖D f z‖ ≤ M/(π·z.im) ≤ M/π. -/
lemma D_isBoundedAtImInfty_of_bounded {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (D f) := by
  rw [isBoundedAtImInfty_iff] at hbdd ⊢
  obtain ⟨M, A, hMA⟩ := hbdd
  use M / π, 2 * max A 0 + 1
  intro z hz
  have hR_pos : 0 < z.im / 2 := by linarith [z.im_pos]
  have hclosed := closedBall_center_subset_upperHalfPlane z
  have hDiff : DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball (z : ℂ) (z.im / 2)) :=
    diffContOnCl_comp_ofComplex_of_mdifferentiable hf hclosed
  have hf_bdd_sphere : ∀ w ∈ Metric.sphere (z : ℂ) (z.im / 2), ‖(f ∘ ofComplex) w‖ ≤ M := by
    intro w hw
    have hw_im_pos : 0 < w.im := hclosed (Metric.sphere_subset_closedBall hw)
    have hdist : dist w z = z.im / 2 := Metric.mem_sphere.mp hw
    have habs : |w.im - z.im| ≤ z.im / 2 := by
      calc |w.im - z.im| = |(w - z).im| := by simp [Complex.sub_im]
        _ ≤ ‖w - z‖ := abs_im_le_norm _
        _ = dist w z := (dist_eq_norm _ _).symm
        _ = z.im / 2 := hdist
    have hw_im_ge_A : A ≤ w.im := by linarith [(abs_le.mp habs).1, le_max_left A 0]
    simpa [ofComplex_apply_of_im_pos hw_im_pos] using hMA ⟨w, hw_im_pos⟩ hw_im_ge_A
  have hz_im_ge_1 : 1 ≤ z.im := by linarith [le_max_right A 0]
  have hM_nonneg : 0 ≤ M := le_trans (norm_nonneg _) (hMA z (by linarith [le_max_left A 0]))
  calc ‖D f z‖ ≤ M / (2 * π * (z.im / 2)) := norm_D_le_of_sphere_bound hR_pos hDiff hf_bdd_sphere
    _ = M / (π * z.im) := by ring
    _ ≤ M / (π * 1) := by gcongr
    _ = M / π := by ring

/-- The Serre derivative of a bounded holomorphic function is bounded at infinity.

serre_D k f = D f - (k/12)·E₂·f. Both terms are bounded:
- D f is bounded by `D_isBoundedAtImInfty_of_bounded`
- (k/12)·E₂·f is bounded since E₂ and f are bounded -/
theorem serre_D_isBoundedAtImInfty {f : ℍ → ℂ} (k : ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) : IsBoundedAtImInfty (serre_D k f) := by
  unfold serre_D
  have hD : IsBoundedAtImInfty (D f) := D_isBoundedAtImInfty_of_bounded hf hbdd
  have hE₂f : IsBoundedAtImInfty (fun z => k * 12⁻¹ * E₂ z * f z) := by
    have hconst : IsBoundedAtImInfty (fun _ : ℍ => k * 12⁻¹) :=
      Filter.const_boundedAtFilter _ _
    convert hconst.mul (E₂_isBoundedAtImInfty.mul hbdd) using 1
    ext z
    simp only [Pi.mul_apply]
    ring
  exact hD.sub hE₂f
