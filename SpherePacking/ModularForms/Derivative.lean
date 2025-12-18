import SpherePacking.ModularForms.Eisenstein

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap

open scoped ModularForm MatrixGroups Manifold

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
theorem E₂_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E₂ := sorry

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
    _ = (2 * π * I)⁻¹ * (deriv (F ∘ ofComplex) z + deriv (G ∘ ofComplex) z)
      := by rw [h]
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z
        + (2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z
      := by simp [mul_add]
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
    _ = (2 * π * I)⁻¹ * (deriv (F ∘ ofComplex) z - deriv (G ∘ ofComplex) z)
      := by rw [h]
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z
        - (2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z
      := by ring_nf
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
    : D (F * G) = F * D G + D F * G := by
  ext z
  have h : deriv ((F ∘ ofComplex) * (G ∘ ofComplex)) z =
      F z * deriv (G ∘ ofComplex) z + deriv (F ∘ ofComplex) z * G z:= by
    have hFz := MDifferentiableAt_DifferentiableAt (hF z)
    have hGz := MDifferentiableAt_DifferentiableAt (hG z)
    rw [deriv_mul hFz hGz]
    simp only [Function.comp_apply, ofComplex_apply]
    group
  calc
    D (F * G) z
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex * G ∘ ofComplex) z := by rfl
    _ = (2 * π * I)⁻¹ * (F z * deriv (G ∘ ofComplex) z + deriv (F ∘ ofComplex) z * G z)
      := by rw [h]
    _ = F z * ((2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z) +
        (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z * G z
      := by ring_nf
    _ = F z * D G z + D F z * G z := by rfl

@[simp]
theorem D_sq (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    D (F ^ 2) = 2 * F * D F := by
  calc
    D (F ^ 2) = D (F * F) := by rw [pow_two]
    _ = F * D F + D F * F := by rw [D_mul F F hF hF]
    _ = 2 * F * D F := by ring_nf

@[simp]
theorem D_cube (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    D (F ^ 3) = 3 * F ^ 2 * D F := by
  have hF2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F ^ 2) := by rw [pow_two]; exact MDifferentiable.mul hF hF
  calc
    D (F ^ 3) = D (F * F ^ 2) := by ring_nf
    _ = F * D (F ^ 2) + D F * F ^ 2 := by rw [D_mul F (F ^ 2) hF hF2]
    _ = F * (2 * F * D F) + D F * F ^ 2 := by rw [D_sq F hF]
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

theorem serre_D_smul (k : ℤ) (c : ℂ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (z : ℍ) :
    serre_D k (c • F) z = c * serre_D k F z := by
  simp only [serre_D, D_smul c F hF]
  simp
  ring_nf

theorem serre_D_mul (k₁ k₂ : ℤ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (z : ℍ) :
    serre_D (k₁ + k₂) (F * G) z = F z * serre_D k₁ G z + G z * serre_D k₂ F z := by
  simp only [serre_D, D_mul F G hF hG]
  simp
  ring_nf

/--
The Serre derivative preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `serre_D k F` is also MDifferentiable.
-/
theorem serre_D_differentiable {F : ℍ → ℂ} {k : ℂ}
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D k F) := by
  -- serre_D k F = D F - k * 12⁻¹ * E₂ * F
  have h_term : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => k * 12⁻¹ * E₂ z * F z) := by
    have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => (k * 12⁻¹) * (E₂ z * F z)) :=
      MDifferentiable.mul mdifferentiable_const (E₂_holo'.mul hF)
    convert h1 using 1; ext z; simp only [mul_assoc]
  exact (D_differentiable hF).sub h_term

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


/--
Prove modular linear differential equation satisfied by $F$.
-/
noncomputable def X₄₂ := 288⁻¹ * (E₄.toFun - E₂ * E₂)

noncomputable def Δ_fun := 1728⁻¹ * (E₄.toFun ^ 3 - E₆.toFun ^ 2)

noncomputable def F := (E₂ * E₄.toFun - E₆.toFun) ^ 2

theorem F_aux : D F = 5 * 6⁻¹ * E₂ ^ 3 * E₄.toFun ^ 2 - 5 * 2⁻¹ * E₂ ^ 2 * E₄.toFun * E₆.toFun
    + 5 * 6⁻¹ * E₂ * E₄.toFun ^ 3 + 5 * 3⁻¹ * E₂ * E₆.toFun ^ 2 - 5 * 6⁻¹ * E₄.toFun^2 * E₆.toFun
    := by
  rw [F, D_sq, D_sub, D_mul]
  · ring_nf
    rw [ramanujan_E₂, ramanujan_E₄, ramanujan_E₆]
    ext z
    simp
    ring_nf
  -- Holomorphicity of the terms
  · exact E₂_holo'
  · exact E₄.holo'
  · exact MDifferentiable.mul E₂_holo' E₄.holo'
  · exact E₆.holo'
  have h24 := MDifferentiable.mul E₂_holo' E₄.holo'
  exact MDifferentiable.sub h24 E₆.holo'


/--
Modular linear differential equation satisfied by `F`.
TODO: Move this to a more appropriate place.
-/
theorem MLDE_F : serre_D 12 (serre_D 10 F) = 5 * 6⁻¹ * F + 172800 * Δ_fun * X₄₂ := by
  ext x
  rw [X₄₂, Δ_fun, serre_D, serre_D, F_aux]
  unfold serre_D
  rw [F_aux]
  sorry

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
theorem antiDerPos {F : ℍ → ℂ} {k : ℤ} (hF : ResToImagAxis.EventuallyPos F)
    (hDF : ResToImagAxis.Pos (D F)) : ResToImagAxis.Pos F := by
  sorry

/--
Let $F : \mathbb{H} \to \mathbb{C}$ be a holomorphic function where $F(it)$ is real for all $t > 0$.
Assume that Serre derivative $\partial_k F$ is positive on the imaginary axis.
If $F(it)$ is positive for sufficiently large $t$, then $F(it)$ is positive for all $t > 0$.
-/
theorem antiSerreDerPos {F : ℍ → ℂ} {k : ℤ} (hSDF : ResToImagAxis.Pos (serre_D k F))
    (hF : ResToImagAxis.EventuallyPos F) : ResToImagAxis.Pos F := by
  sorry
