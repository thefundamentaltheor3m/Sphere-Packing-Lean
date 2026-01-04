import SpherePacking.ModularForms.Eisenstein
import SpherePacking.ModularForms.tsumderivWithin
import Mathlib.Analysis.Calculus.DerivativeTest

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

NOTE: Proof available in PR #213 (gauss-math-inc) using eta function logDeriv.
This PR should wait for #213 to merge first.
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

/-! ### Termwise differentiation of q-series (Lemma 6.45) -/

/-- Helper: HasDerivAt for a·exp(2πicw) with chain rule. -/
private lemma hasDerivAt_qexp (a c w : ℂ) :
    HasDerivAt (fun z => a * cexp (2 * π * I * c * z))
      (a * (2 * π * I * c) * cexp (2 * π * I * c * w)) w := by
  have h := (hasDerivAt_id w).const_mul (2 * π * I * c)
  simp only [mul_one, id] at h
  have := ((Complex.hasDerivAt_exp _).scomp w h).const_mul a
  simp only [smul_eq_mul] at this ⊢
  convert this using 1
  ring

/-- Helper: derivWithin for qexp term on upper half-plane. -/
private lemma derivWithin_qexp (a c : ℂ) (w : ℂ) (hw : 0 < w.im) :
    derivWithin (fun z => a * cexp (2 * π * I * c * z))
      {z : ℂ | 0 < z.im} w = a * (2 * π * I * c) * cexp (2 * π * I * c * w) :=
  ((hasDerivAt_qexp a c w).hasDerivWithinAt).derivWithin
    (isOpen_upperHalfPlaneSet.uniqueDiffWithinAt hw)

/--
**Lemma 6.45 (Blueprint)**: The normalized derivative $D$ acts as $q \frac{d}{dq}$ on $q$-series.
For a single q-power term: D(a·qⁿ) = n·a·qⁿ where q = exp(2πiz) and n ∈ ℤ.

The key calculation:
- d/dz(exp(2πinz)) = 2πin·exp(2πinz)
- D(exp(2πinz)) = (2πi)⁻¹·(2πin·exp(2πinz)) = n·exp(2πinz)
-/
theorem D_qexp_term (n : ℤ) (a : ℂ) (z : ℍ) :
    D (fun w => a * cexp (2 * π * I * n * w)) z =
      n * a * cexp (2 * π * I * n * z) := by
  simp only [D]
  have h_agree : ((fun w : ℍ => a * cexp (2 * π * I * n * w)) ∘ ofComplex) =ᶠ[nhds (z : ℂ)]
      (fun w : ℂ => a * cexp (2 * π * I * n * w)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.2] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, coe_mk_subtype]
  rw [h_agree.deriv_eq, (hasDerivAt_qexp a n z).deriv]
  field_simp [two_pi_I_ne_zero]

/--
**Lemma 6.45 (Blueprint)**: $D$ commutes with tsum for $q$-series.
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
  -- Each term is differentiable
  have hf_diff : ∀ n (r : {w : ℂ | 0 < w.im}), DifferentiableAt ℂ
      (fun w => a n * cexp (2 * π * I * n * w)) r := fun n r =>
    ((differentiableAt_id.const_mul (2 * π * I * n)).cexp).const_mul (a n)
  -- Summability at each point (bound holds for n ≥ 1, exception set ⊆ {0})
  have hf_sum : ∀ y : ℂ, y ∈ {w : ℂ | 0 < w.im} →
      Summable (fun n => a n * cexp (2 * π * I * n * y)) := by
    intro y hy
    obtain ⟨u, hu_sum, hu_bound⟩ :=
      hsum_deriv {y} (Set.singleton_subset_iff.mpr hy) isCompact_singleton
    apply Summable.of_norm_bounded_eventually (g := fun n => u n / (2 * π)) (hu_sum.div_const _)
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (Set.finite_singleton 0) fun n hn => ?_
    simp only [Set.mem_setOf_eq, not_le] at hn
    by_contra h_ne
    have h_deriv_bound := hu_bound n ⟨y, Set.mem_singleton y⟩
    have h_n_ge_1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr h_ne)
    have h_norm_2pin : ‖(2 : ℂ) * π * I * n‖ = 2 * π * n := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
          Complex.norm_I, mul_one, Complex.norm_natCast, Real.norm_of_nonneg pi_pos.le]
    have h_bound : ‖a n * cexp (2 * π * I * n * y)‖ ≤ u n / (2 * π) := by
      have h_pos : (0 : ℝ) < 2 * π * n := by positivity
      have h_key : ‖a n * cexp (2 * π * I * n * y)‖ * (2 * π * n) =
          ‖a n * (2 * π * I * n) * cexp (2 * π * I * n * y)‖ := by
        simp only [norm_mul, h_norm_2pin]; ring
      calc ‖a n * cexp (2 * π * I * n * y)‖
          = ‖a n * cexp (2 * π * I * n * y)‖ * (2 * π * n) / (2 * π * n) := by field_simp
        _ = ‖a n * (2 * π * I * n) * cexp (2 * π * I * n * y)‖ / (2 * π * n) := by rw [h_key]
        _ ≤ u n / (2 * π * n) := div_le_div_of_nonneg_right h_deriv_bound h_pos.le
        _ ≤ u n / (2 * π) := by
            apply div_le_div_of_nonneg_left (le_trans (norm_nonneg _) h_deriv_bound)
              (by positivity); nlinarith
    exact hn.not_ge h_bound
  -- Derivative bound for uniform convergence
  have hu : ∀ K ⊆ {w : ℂ | 0 < w.im}, IsCompact K →
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K),
        ‖derivWithin (fun w => a n * cexp (2 * π * I * n * w)) {w : ℂ | 0 < w.im} k‖ ≤ u n := by
    intro K hK1 hK2
    obtain ⟨u, hu_sum, hu_bound⟩ := hsum_deriv K hK1 hK2
    exact ⟨u, hu_sum, fun n k => by rw [derivWithin_qexp _ _ _ (hK1 k.2)]; exact hu_bound n k⟩
  -- Apply termwise differentiation
  have h_tsum_deriv := hasDerivAt_tsum_fun (fun n w => a n * cexp (2 * π * I * n * w))
    isOpen_upperHalfPlaneSet (z : ℂ) z.2 hf_sum hu hf_diff
  -- The composed function agrees with ℂ → ℂ in a neighborhood
  have h_agree : ((fun w : ℍ => ∑' n, a n * cexp (2 * π * I * n * w)) ∘ ofComplex) =ᶠ[nhds (z : ℂ)]
      (fun w => ∑' n, a n * cexp (2 * π * I * n * w)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.2] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, coe_mk_subtype]
  rw [h_agree.deriv_eq, h_tsum_deriv.deriv]
  -- Simplify derivWithin using helper
  have h_deriv_simp : ∀ n, derivWithin (fun w => a n * cexp (2 * π * I * n * w))
      {w : ℂ | 0 < w.im} z = a n * (2 * π * I * n) * cexp (2 * π * I * n * z) :=
    fun n => derivWithin_qexp _ _ _ z.2
  simp_rw [h_deriv_simp, ← tsum_mul_left]
  congr 1; funext n; field_simp [two_pi_I_ne_zero]

/--
Simplified version of `D_qexp_tsum` for ℕ+-indexed series (starting from n=1).
This is the form most commonly used for Eisenstein series q-expansions.

**Thin layer implementation:** Extends `a : ℕ+ → ℂ` to `ℕ → ℂ` with `a' 0 = 0`,
uses `tsum_pNat` and `nat_pos_tsum2` to convert between sums,
then applies `D_qexp_tsum`.
-/
theorem D_qexp_tsum_pnat (a : ℕ+ → ℂ) (z : ℍ)
    (hsum : Summable (fun n : ℕ+ => a n * cexp (2 * π * I * n * z)))
    (hsum_deriv : ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
        ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ n (k : K), ‖a n * (2 * π * I * n) *
          cexp (2 * π * I * n * k.1)‖ ≤ u n) :
    D (fun w => ∑' n : ℕ+, a n * cexp (2 * π * I * n * w)) z =
      ∑' n : ℕ+, (n : ℂ) * a n * cexp (2 * π * I * n * z) := by
  -- Extend a to ℕ with a' 0 = 0
  let a' : ℕ → ℂ := fun n => if h : 0 < n then a ⟨n, h⟩ else 0
  have ha' : ∀ n : ℕ+, a' n = a n := fun n => dif_pos n.pos
  -- Derivative bounds: extend u using nat_pos_tsum2
  have hsum_deriv' : ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K), ‖a' n * (2 * π * I * n) *
        cexp (2 * π * I * n * k.1)‖ ≤ u n := fun K hK hKc => by
    obtain ⟨u, hu_sum, hu_bound⟩ := hsum_deriv K hK hKc
    let u' : ℕ → ℝ := fun n => if h : 0 < n then u ⟨n, h⟩ else 0
    have hu' : ∀ n : ℕ+, u' n = u n := fun n => dif_pos n.pos
    refine ⟨u', (nat_pos_tsum2 u' (by simp [u'])).mp (hu_sum.congr fun n => by rw [hu']),
      fun n k => ?_⟩
    by_cases hn : 0 < n
    · simp only [a', u', dif_pos hn]; exact hu_bound _ k
    · simp only [Nat.not_lt, Nat.le_zero] at hn; simp [a', u', hn]
  -- Apply D_qexp_tsum and convert sums via tsum_pNat
  have hD := D_qexp_tsum a' z ((nat_pos_tsum2 _ (by simp [a'])).mp
    (hsum.congr fun n => by rw [ha'])) hsum_deriv'
  calc D (fun w => ∑' n : ℕ+, a n * cexp (2 * π * I * n * w)) z
      = D (fun w : ℍ => ∑' n : ℕ, a' n * cexp (2 * π * I * n * (w : ℂ))) z := by
          congr 1; ext w; rw [← tsum_pNat _ (by simp [a'])]; exact tsum_congr fun n => by rw [ha']
    _ = ∑' n : ℕ, (n : ℂ) * a' n * cexp (2 * π * I * n * (z : ℂ)) := hD
    _ = ∑' n : ℕ+, (n : ℂ) * a n * cexp (2 * π * I * n * z) := by
          rw [← tsum_pNat _ (by simp [a'])]; exact tsum_congr fun n => by rw [ha']

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

/-! ### Helper lemmas for D_slash

These micro-lemmas compute derivatives of the components in the slash action formula.
-/

open ModularGroup in
/-- Derivative of the denominator function: d/dz[cz + d] = c. -/
lemma deriv_denom (γ : SL(2, ℤ)) (z : ℂ) :
    deriv (fun w => denom γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) := by
  -- denom γ w = (γ : GL) 1 0 * w + (γ : GL) 1 1
  -- The GL entries come from ℤ via ℤ → ℝ → GL
  have hc : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) := by simp
  have hd : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) := by simp
  simp only [denom]
  have h : (fun w => (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * w +
      (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ)) =
      (fun w => ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * w +
          ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)) := by
    ext w; rw [hc, hd]
  rw [h, deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]

open ModularGroup in
/-- Derivative of the numerator function: d/dz[az + b] = a. -/
lemma deriv_num (γ : SL(2, ℤ)) (z : ℂ) :
    deriv (fun w => num γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) := by
  have ha : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) := by simp
  have hb : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) := by simp
  simp only [num]
  have h : (fun w => (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * w +
      (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ)) =
      (fun w => ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * w +
          ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ)) := by
    ext w; rw [ha, hb]
  rw [h, deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]

open ModularGroup in
/-- Differentiability of denom. -/
lemma differentiableAt_denom (γ : SL(2, ℤ)) (z : ℂ) :
    DifferentiableAt ℂ (fun w => denom γ w) z := by
  simp only [denom]
  fun_prop

open ModularGroup in
/-- Differentiability of num. -/
lemma differentiableAt_num (γ : SL(2, ℤ)) (z : ℂ) :
    DifferentiableAt ℂ (fun w => num γ w) z := by
  simp only [num]
  fun_prop

open ModularGroup in
/-- Derivative of the Möbius transformation: d/dz[(az+b)/(cz+d)] = 1/(cz+d)².
This uses det(γ) = 1, so (a(cz+d) - c(az+b)) = ad - bc = 1. -/
lemma deriv_moebius (γ : SL(2, ℤ)) (z : ℂ) (hz : denom γ z ≠ 0) :
    deriv (fun w => num γ w / denom γ w) z = 1 / (denom γ z) ^ 2 := by
  have hdiff_num : DifferentiableAt ℂ (fun w => num γ w) z := differentiableAt_num γ z
  have hdiff_denom : DifferentiableAt ℂ (fun w => denom γ w) z := differentiableAt_denom γ z
  have hderiv : HasDerivAt (fun w => num γ w / denom γ w)
      ((deriv (fun w => num γ w) z * denom γ z - num γ z * deriv (fun w => denom γ w) z)
        / (denom γ z) ^ 2) z :=
    hdiff_num.hasDerivAt.div hdiff_denom.hasDerivAt hz
  rw [hderiv.deriv, deriv_num, deriv_denom]
  -- Use det γ = 1: γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) *
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) -
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) *
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) = 1 := by
    simp only [← Int.cast_mul, ← Int.cast_sub]
    have hdet' := Matrix.SpecialLinearGroup.det_coe γ
    simp only [Matrix.det_fin_two] at hdet'
    norm_cast
  -- Normalize coercions between GL and Matrix ℤ
  have ha : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) := by simp
  have hb : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) := by simp
  have hc : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) := by simp
  have hd' : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) := by simp
  simp only [num, denom, ha, hb, hc, hd']
  -- Goal: (a * (c*z+d) - (a*z+b) * c) / (c*z+d)^2 = 1 / (c*z+d)^2
  -- Numerator: a*(cz+d) - c*(az+b) = acz + ad - acz - bc = ad - bc = 1 (det)
  have hdenom_eq : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * z +
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) = denom γ z := by simp only [denom, hc, hd']
  rw [hdenom_eq]
  have hdenom_sq_ne : (denom γ z) ^ 2 ≠ 0 := pow_ne_zero 2 hz
  rw [div_eq_div_iff hdenom_sq_ne hdenom_sq_ne, one_mul]
  -- Goal: (a * denom - (az+b) * c) * denom^2 = denom^2
  -- This is 1 * denom^2 = denom^2 if we can show numerator = 1
  have hnum_eq : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * denom γ z -
      (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * z + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ)) *
        ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) = 1 := by
    simp only [denom, hc, hd']
    linear_combination hdet
  rw [hnum_eq, one_mul]

open ModularGroup in
/-- Derivative of denom^(-k): d/dz[(cz+d)^(-k)] = -k * c * (cz+d)^(-k-1). -/
lemma deriv_denom_zpow (γ : SL(2, ℤ)) (k : ℤ) (z : ℂ) (hz : denom γ z ≠ 0) :
    deriv (fun w => (denom γ w) ^ (-k)) z =
        (-k : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (denom γ z) ^ (-k - 1) := by
  have hdiff : DifferentiableAt ℂ (fun w => denom γ w) z := differentiableAt_denom γ z
  -- Use chain rule: d/dz[f(z)^m] = m * f(z)^(m-1) * f'(z)
  have hderiv_zpow : HasDerivAt (fun w => w ^ (-k)) (((-k : ℤ) : ℂ) * (denom γ z) ^ (-k - 1))
      (denom γ z) := hasDerivAt_zpow (-k) (denom γ z) (Or.inl hz)
  have hderiv_denom : HasDerivAt (fun w => denom γ w)
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) z := by
    rw [← deriv_denom]
    exact hdiff.hasDerivAt
  -- Chain rule
  have hcomp := hderiv_zpow.comp z hderiv_denom
  -- The composition equals fun w => (denom γ w) ^ (-k)
  have heq : (fun w => w ^ (-k)) ∘ (fun w => denom γ w) = (fun w => (denom γ w) ^ (-k)) := by
    ext w; simp only [Function.comp_apply]
  rw [← heq, hcomp.deriv]
  simp only [Int.cast_neg]
  ring

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
  -- D(F ∣[k] γ) z = (2πi)⁻¹ * deriv[(F ∣[k] γ) ∘ ofComplex] z
  --   = (2πi)⁻¹ * deriv[w ↦ F(mobius w) * denom(w)^(-k)] z
  --   = (2πi)⁻¹ * [F(mob z)*(-k*c*denom^(-k-1)) + deriv[F](mob z)*(1/d²)*d^(-k)]
  --   = -k*(2πi)⁻¹*(c/d)*(F ∣[k] γ)(z) + (2πi)⁻¹*deriv[F](γ•z)*d^(-k-2)
  --   = (D F ∣[k+2] γ)(z) - k*(2πi)⁻¹*(c/d)*(F ∣[k] γ)(z)
  ext z
  unfold D
  simp only [Pi.sub_apply]
  -- Key facts about denom
  have hz_denom_ne : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  -- Coercion normalization
  have hc : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) =
      (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) := by simp
  -- The derivative computation on ℂ using Filter.EventuallyEq.deriv_eq
  -- (F ∣[k] γ) ∘ ofComplex agrees with F(num/denom) * denom^(-k) on ℍ
  have hcomp : deriv (((F ∣[k] γ)) ∘ ofComplex) z =
      deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    rw [ModularForm.SL_slash_apply (f := F) (k := k) γ ⟨w, hw⟩]
    -- Need: F(γ•⟨w,hw⟩) * denom^(-k) = (F∘ofComplex)(num/denom) * denom^(-k)
    -- Key: (γ•⟨w,hw⟩ : ℂ) = num/denom and denom γ ⟨w,hw⟩ = denom γ w
    congr 1
    · -- F (γ • ⟨w, hw⟩) = (F ∘ ofComplex) (num γ w / denom γ w)
      -- Need: γ • ⟨w, hw⟩ = ofComplex (num γ w / denom γ w) as points in ℍ
      have hdet_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
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
  have hz_im_pos : (z : ℂ).im > 0 := z.im_pos
  have hdiff_denom_zpow : DifferentiableAt ℂ (fun w => (denom γ w) ^ (-k)) z := by
    apply DifferentiableAt.zpow (differentiableAt_denom γ z) (Or.inl (hdenom_ne z hz_im_pos))
  -- For the F ∘ (num/denom) term, we need differentiability of the Möbius and F
  have hdiff_mobius : DifferentiableAt ℂ (fun w => num γ w / denom γ w) z := by
    exact (differentiableAt_num γ z).div (differentiableAt_denom γ z) (hdenom_ne z hz_im_pos)
  -- The composition (F ∘ ofComplex) ∘ mobius is differentiable at z
  -- because mobius(z) is in ℍ and F is MDifferentiable
  have hmobius_in_H : (num γ z / denom γ z).im > 0 := by
    -- γ • z is in ℍ, and (γ • z : ℂ) = num/denom
    have hdet_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
    have hsmul := UpperHalfPlane.coe_smul_of_det_pos hdet_pos z
    rw [← hsmul]
    exact (γ • z).im_pos
  have hdiff_F_comp : DifferentiableAt ℂ (F ∘ ofComplex) (num γ z / denom γ z) :=
    MDifferentiableAt_DifferentiableAt (hF ⟨num γ z / denom γ z, hmobius_in_H⟩)
  have hdiff_F_mobius : DifferentiableAt ℂ (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z := by
    -- The composition (F ∘ ofComplex) ∘ (num/denom) : ℂ → ℂ
    have heq : (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) =
        (F ∘ ofComplex) ∘ (fun w => num γ w / denom γ w) := rfl
    rw [heq]
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
    -- Chain rule: d/dx[f(g(x))] = f'(g(x)) * g'(x)
    have heq : (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) =
        (F ∘ ofComplex) ∘ (fun w => num γ w / denom γ w) := rfl
    have hcomp := hdiff_F_comp.hasDerivAt.comp (z : ℂ) hdiff_mobius.hasDerivAt
    rw [heq, hcomp.deriv]
  -- Substitute the micro-lemmas
  have hderiv_mob := deriv_moebius γ z (hdenom_ne z hz_im_pos)
  have hderiv_zpow := deriv_denom_zpow γ k z (hdenom_ne z hz_im_pos)
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
  -- Relate mobius to γ • z
  have hdet_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
  -- The key: ↑(γ • z) = num/denom (explicit coercion from ℍ to ℂ)
  have hmob_eq : ↑(γ • z) = num γ z / denom γ z :=
    UpperHalfPlane.coe_smul_of_det_pos hdet_pos z
  -- Relate (F ∘ ofComplex)(mob z) to F(γ • z)
  have hF_mob : (F ∘ ofComplex) (num γ z / denom γ z) = F (γ • z) := by
    simp only [Function.comp_apply, ← hmob_eq, ofComplex_apply]
  -- Relate deriv(F∘ofComplex) to D via (2πi)⁻¹
  have hD_eq : (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) (num γ z / denom γ z) = D F (γ • z) := by
    unfold D
    congr 1
    rw [← hmob_eq]
  -- The slash action values
  have hslash_k : (F ∣[k] γ) z = F (γ • z) * (denom γ z) ^ (-k) := by
    rw [ModularForm.SL_slash_apply (f := F) (k := k) γ z]
  have hslash_k2 : (D F ∣[k + 2] γ) z = D F (γ • z) * (denom γ z) ^ (-(k + 2)) := by
    rw [ModularForm.SL_slash_apply (f := D F) (k := k + 2) γ z]
  -- Final algebraic manipulation combining all lemmas
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
E₂ transformation under slash action, derived from G₂_transform.
E₂ = G₂ / (2*ζ(2)), and G₂ ∣[2] γ = G₂ - D₂ γ.
-/
lemma E₂_slash_transform (γ : SL(2, ℤ)) :
    E₂ ∣[(2 : ℤ)] γ = E₂ - (1 / (2 * riemannZeta 2)) • D₂ γ := by
  -- Use G₂_transform and E₂ = (1/(2*ζ(2))) • G₂
  have hG := G₂_transform γ
  rw [E₂]
  -- E₂ ∣[2] γ = (1/(2ζ(2)) • G₂) ∣[2] γ = 1/(2ζ(2)) • (G₂ ∣[2] γ)
  rw [ModularForm.SL_smul_slash (2 : ℤ) γ G₂ (1 / (2 * riemannZeta 2))]
  rw [hG]
  ext z
  simp only [one_div, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- The anomaly coefficient vanishes: `(1/12)*(1/(2ζ(2)))*2πi + (2πi)⁻¹ = 0`.
Using `ζ(2) = π²/6`, this is `i/(2π) + 1/(2πi) = 0`. -/
lemma anomaly_coeff_zero :
    (12 : ℂ)⁻¹ * (2 * riemannZeta 2)⁻¹ * (2 * π * I) + (2 * π * I)⁻¹ = 0 := by
  rw [riemannZeta_two]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have h6 : (6 : ℂ) ≠ 0 := by norm_num
  have h12 : (12 : ℂ) ≠ 0 := by norm_num
  field_simp
  ring_nf
  -- Goal: 12 + I ^ 2 * 12 = 0, which is 12 + (-1) * 12 = 0 since I^2 = -1
  simp only [I_sq, neg_one_mul, add_neg_cancel]

/--
Serre derivative is equivariant under the slash action. More precisely, if `F` is invariant
under the slash action of weight `k`, then `serre_D k F` is invariant under the slash action
of weight `k + 2`.
-/
theorem serre_D_slash_equivariant (k : ℤ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    ∀ γ : SL(2, ℤ), serre_D k F ∣[k + 2] γ = serre_D k (F ∣[k] γ) := by
  intro γ
  ext z
  -- Get key transformations
  have hDslash := congrFun (D_slash k F hF γ) z
  simp only [Pi.sub_apply] at hDslash
  have hE₂slash := congrFun (E₂_slash_transform γ) z
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hE₂slash
  -- Product slash: (E₂ * F) ∣[k+2] γ = (E₂ ∣[2] γ) * (F ∣[k] γ)
  have hmul : ((E₂ * F) ∣[k + 2] γ) z = (E₂ ∣[(2 : ℤ)] γ) z * (F ∣[k] γ) z := by
    have h := congrFun (ModularForm.mul_slash_SL2 (2 : ℤ) k γ E₂ F) z
    simp only [Pi.mul_apply] at h; convert h using 2; ring
  -- D₂ in terms of c/denom
  have hD₂ : D₂ γ z = (2 * π * I) * (↑(γ 1 0) / denom γ z) := by
    simp only [D₂]
    ring
  -- LHS: (serre_D k F ∣[k+2] γ) z = (D F - (k/12) * E₂ * F) ∣[k+2] γ
  -- By linearity of slash: = D F ∣[k+2] γ - (k/12) * (E₂ * F) ∣[k+2] γ
  have hLHS : (serre_D k F ∣[k + 2] γ) z =
      (D F ∣[k + 2] γ) z - (k : ℂ) * (12 : ℂ)⁻¹ * ((E₂ * F) ∣[k + 2] γ) z := by
    simp only [serre_D, ModularForm.SL_slash_apply, Pi.mul_apply]
    ring
  -- RHS: serre_D k (F ∣[k] γ) z = D (F ∣[k] γ) z - (k/12) * E₂ z * (F ∣[k] γ) z
  have hRHS : serre_D k (F ∣[k] γ) z =
      D (F ∣[k] γ) z - (k : ℂ) * (12 : ℂ)⁻¹ * E₂ z * (F ∣[k] γ) z := by
    simp only [serre_D]
  -- Substitute hLHS and hRHS pattern and perform calc
  rw [hLHS, hRHS]
  rw [hmul, hE₂slash, hD₂]
  -- From D_slash: D (F ∣[k] γ) z = (D F ∣[k + 2] γ) z - k*(2πi)⁻¹*(c/denom)*(F ∣[k] γ) z
  -- Rearranging: (D F ∣[k + 2] γ) z = D (F ∣[k] γ) z + k*(2πi)⁻¹*(c/denom)*(F ∣[k] γ) z
  have hDslash' : (D F ∣[k + 2] γ) z = D (F ∣[k] γ) z +
      (k : ℂ) * (2 * π * I)⁻¹ * (↑(γ 1 0) / denom γ z) * (F ∣[k] γ) z := by
    -- hDslash: D (F ∣[k] γ) z = (D F ∣[k + 2] γ) z - X where X = k*(2πi)⁻¹*(c/denom)*(F ∣[k] γ) z
    -- So: (D F ∣[k + 2] γ) z = D (F ∣[k] γ) z + X
    calc (D F ∣[k + 2] γ) z
        = (D F ∣[k + 2] γ) z - (k : ℂ) * (2 * π * I)⁻¹ * (↑(γ 1 0) / denom γ z) * (F ∣[k] γ) z
          + (k : ℂ) * (2 * π * I)⁻¹ * (↑(γ 1 0) / denom γ z) * (F ∣[k] γ) z := by ring
      _ = D (F ∣[k] γ) z + (k : ℂ) * (2 * π * I)⁻¹ * (↑(γ 1 0) / denom γ z) * (F ∣[k] γ) z := by
          rw [← hDslash]
  rw [hDslash']
  -- Now the goal is pure algebra:
  -- D(F∣γ) + k*(2πi)⁻¹*(c/denom)*F∣γ - k/12*(E₂ - (2ζ(2))⁻¹*2πi*(c/denom))*F∣γ
  -- = D(F∣γ) - k/12*E₂*F∣γ
  -- Expanding: D(F∣γ) + k*(2πi)⁻¹*X - k/12*E₂*F∣γ + k/12*(2ζ(2))⁻¹*2πi*X
  -- = D(F∣γ) - k/12*E₂*F∣γ
  -- where X = (c/denom)*F∣γ
  -- So we need: k*(2πi)⁻¹*X + k/12*(2ζ(2))⁻¹*2πi*X = 0
  -- Factor: k*X*[(2πi)⁻¹ + (12)⁻¹*(2ζ(2))⁻¹*2πi] = 0
  -- This is anomaly_coeff_zero!
  have h_cancel := anomaly_coeff_zero
  have h_factored : ∀ (x : ℂ), (12 : ℂ)⁻¹ * (2 * riemannZeta 2)⁻¹ * (2 * π * I) * x +
      (2 * π * I)⁻¹ * x = 0 := fun x => by
    calc (12 : ℂ)⁻¹ * (2 * riemannZeta 2)⁻¹ * (2 * π * I) * x + (2 * π * I)⁻¹ * x
        = ((12 : ℂ)⁻¹ * (2 * riemannZeta 2)⁻¹ * (2 * π * I) + (2 * π * I)⁻¹) * x := by ring
      _ = 0 * x := by rw [h_cancel]
      _ = 0 := by ring
  -- Use abbreviations for readability
  set D' := D (F ∣[k] γ) z with hD'
  set c_div_d := (↑(γ 1 0) : ℂ) / denom γ z with hcd
  set F' := (F ∣[k] γ) z with hF'
  set π2I := (2 * π * I : ℂ) with hπ2I
  set ζ2 := riemannZeta 2 with hζ2
  -- h_factored using abbreviations
  have h_app : (12 : ℂ)⁻¹ * (2 * ζ2)⁻¹ * π2I * ((k : ℂ) * c_div_d * F') +
      π2I⁻¹ * ((k : ℂ) * c_div_d * F') = 0 := h_factored ((k : ℂ) * c_div_d * F')
  -- Goal: D' + k*π2I⁻¹*c_div_d*F' - k/12*(E₂ z - (2ζ2)⁻¹*π2I*c_div_d)*F'
  --     = D' - k/12*E₂ z*F'
  -- Expanding and rearranging:
  -- need k*π2I⁻¹*c_div_d*F' + k/12*(2ζ2)⁻¹*π2I*c_div_d*F' = 0
  -- = k * c_div_d * F' * (π2I⁻¹ + 12⁻¹*(2ζ2)⁻¹*π2I)
  -- = 0 by h_app
  ring_nf
  -- h_goal: the anomaly terms sum to 0
  have h_goal : (k : ℂ) * π2I * c_div_d * F' * ζ2⁻¹ * (1 / 24) +
      (k : ℂ) * π2I⁻¹ * c_div_d * F' = 0 := by
    calc (k : ℂ) * π2I * c_div_d * F' * ζ2⁻¹ * (1 / 24) + (k : ℂ) * π2I⁻¹ * c_div_d * F'
        = (12 : ℂ)⁻¹ * (2 * ζ2)⁻¹ * π2I * ((k : ℂ) * c_div_d * F') +
          π2I⁻¹ * ((k : ℂ) * c_div_d * F') := by ring
      _ = 0 := h_app
  calc D' + ↑k * π2I * c_div_d * F' * ζ2⁻¹ * (1 / 24) + ↑k * π2I⁻¹ * c_div_d * F' +
      ↑k * F' * E₂ z * (-1 / 12)
    _ = D' + ↑k * F' * E₂ z * (-1 / 12) +
        ((k : ℂ) * π2I * c_div_d * F' * ζ2⁻¹ * (1 / 24) + (k : ℂ) * π2I⁻¹ * c_div_d * F') := by ring
    _ = D' + ↑k * F' * E₂ z * (-1 / 12) + 0 := by rw [h_goal]
    _ = D' + ↑k * F' * E₂ z * (-1 / 12) := by ring

theorem serre_D_slash_invariant (k : ℤ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (γ : SL(2, ℤ)) (h : F ∣[k] γ = F) :
    serre_D k F ∣[k + 2] γ = serre_D k F := by
  rw [serre_D_slash_equivariant, h]
  exact hF

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

/-! ## Ramanujan identities (stubs for blueprint) -/

theorem ramanujan_E₂' : serre_D 1 E₂ = - 12⁻¹ * E₄.toFun := by sorry

theorem ramanujan_E₄' : serre_D 4 E₄.toFun = - 3⁻¹ * E₆.toFun := by sorry

theorem ramanujan_E₆' : serre_D 6 E₆.toFun = - 2⁻¹ * E₄.toFun * E₄.toFun := by sorry

@[simp]
theorem ramanujan_E₂ : D E₂ = 12⁻¹ * (E₂ * E₂ - E₄.toFun) := by sorry

theorem ramanujan_E₄ : D E₄.toFun = 3⁻¹ * (E₂ * E₄.toFun - E₆.toFun) := by sorry

theorem ramanujan_E₆ : D E₆.toFun = 2⁻¹ * (E₂ * E₆.toFun - E₄.toFun * E₄.toFun) := by sorry
