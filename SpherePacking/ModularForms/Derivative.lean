module

public import Mathlib.NumberTheory.ModularForms.Derivative
public import SpherePacking.ForMathlib.MDifferentiableFunProp
public import SpherePacking.ModularForms.Eisenstein
public import SpherePacking.ModularForms.tsumderivWithin

/-!
# Derivatives of Modular Forms

The normalized derivative `D = (2πi)⁻¹ d/dz` and the Serre derivative `∂ₖ = D - k/12 E₂` are
Mathlib's `Derivative.normalizedDerivOfComplex` (notation `D`) and `Derivative.serreDerivative`,
including their linearity/Leibniz rules, slash equivariance, and boundedness at `i∞`
(`Derivative.serreDerivativeMF` packages `∂ₖ` of a modular form as a modular form).

This file collects the project-specific complements: termwise differentiation of `q`-series
(`D_qexp_tsum_pnat`), and the interaction of `D` and `∂ₖ` with the restriction to the imaginary
axis (realness, positivity via monotonicity arguments).
-/

@[expose] public section

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap
open Metric Filter Function

open scoped ModularForm MatrixGroups Manifold Topology BigOperators
open Derivative

/-- Constant Pi functions (numeric literals) are MDifferentiable. -/
@[fun_prop]
lemma MDifferentiable.pi_ofNat (n : ℕ) [n.AtLeastTwo] :
    MDiff (@OfNat.ofNat (ℍ → ℂ) n _) := mdifferentiable_const

/-- Inverse of a constant Pi function (e.g. `6⁻¹ : ℍ → ℂ`) is MDifferentiable. -/
@[fun_prop]
lemma MDifferentiable.pi_inv_ofNat (n : ℕ) [n.AtLeastTwo] :
    MDiff (@OfNat.ofNat (ℍ → ℂ) n _)⁻¹ := by
  change MDiff (fun (_ : ℍ) => (OfNat.ofNat n : ℂ)⁻¹)
  exact mdifferentiable_const

/-!
`D` and `∂ₖ` are Mathlib's; register their `MDifferentiable` lemmas, and `E₂`'s, with `fun_prop`.
-/
attribute [fun_prop] normalizedDerivOfComplex_mdifferentiable serreDerivative_mdifferentiable
  E2_mdifferentiable

/-- Normalize a numeric literal `(n : ℍ → ℂ)` to a constant function so
`Derivative.normalizedDerivOfComplex_const` fires. -/
@[simp]
lemma pi_ofNat_eq_const (n : ℕ) [n.AtLeastTwo] :
    (@OfNat.ofNat (ℍ → ℂ) n _) = fun _ ↦ (OfNat.ofNat n : ℂ) := rfl

/-- Normalize `(fun _ ↦ c)⁻¹` to `fun _ ↦ c⁻¹` so `Derivative.normalizedDerivOfComplex_const`
fires. -/
@[simp]
lemma pi_inv_const_eq_const (c : ℂ) : (fun _ : ℍ ↦ c)⁻¹ = fun _ ↦ c⁻¹ := rfl

/-! ### Termwise differentiation of q-series (Lemma 6.45) -/

/-- Helper: HasDerivAt for a·exp(2πicw) with chain rule. -/
private lemma hasDerivAt_qexp (a c w : ℂ) :
    HasDerivAt (fun z => a * cexp (2 * π * I * c * z))
      (a * (2 * π * I * c) * cexp (2 * π * I * c * w)) w := by
  have h := (hasDerivAt_id w).const_mul (2 * π * I * c)
  simp only [mul_one, id] at h
  have := ((Complex.hasDerivAt_exp _).scomp w h).const_mul a
  simp only [smul_eq_mul] at this ⊢
  simpa [Function.comp_def, mul_assoc] using this

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
  simp only [normalizedDerivOfComplex]
  have h_agree : ((fun w : ℍ => a * cexp (2 * π * I * n * w)) ∘ ofComplex) =ᶠ[nhds (z : ℂ)]
      (fun w : ℂ => a * cexp (2 * π * I * n * w)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.2] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, UpperHalfPlane.coe_mk]
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
  simp only [normalizedDerivOfComplex]
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
    simp only [Set.mem_ofPred_eq, not_le] at hn
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
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, UpperHalfPlane.coe_mk]
  rw [h_agree.deriv_eq, h_tsum_deriv.deriv]
  -- Simplify derivWithin using helper
  have h_deriv_simp : ∀ n, derivWithin (fun w => a n * cexp (2 * π * I * n * w))
      {w : ℂ | 0 < w.im} z = a n * (2 * π * I * n) * cexp (2 * π * I * n * z) :=
    fun n => derivWithin_qexp _ _ _ z.2
  simp_rw [h_deriv_simp, ← tsum_mul_left]
  congr 1; funext n; field_simp [two_pi_I_ne_zero]

/-- For `f 0 = 0`, the `ℕ+`- and `ℕ`-indexed sums of `f` agree. Unlike mathlib's
`tsum_zero_pnat_eq_tsum_nat`, this needs no summability hypothesis (both sides are `0` in the
non-summable case). -/
private theorem tsum_pNat {α : Type _} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α]
    [T2Space α] [CompleteSpace α] (f : ℕ → α) (hf : f 0 = 0) : ∑' n : ℕ+, f n = ∑' n, f n := by
  by_cases hf2 : Summable f
  · rw [hf2.tsum_eq_zero_add, hf, zero_add]
    exact tsum_pnat_eq_tsum_succ
  rw [tsum_eq_zero_of_not_summable hf2,
    tsum_eq_zero_of_not_summable (summable_pnat_iff_summable_nat.not.mpr hf2)]

/--
Simplified version of `D_qexp_tsum` for ℕ+-indexed series (starting from n=1).
This is the form most commonly used for Eisenstein series q-expansions.

**Thin layer implementation:** Extends `a : ℕ+ → ℂ` to `ℕ → ℂ` with `a' 0 = 0`,
uses `tsum_pNat` and `summable_pnat_iff_summable_nat` to convert between sums,
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
  have ha' : ∀ n : ℕ+, a' n = a n := fun n => dite_eq_left n.pos
  -- Derivative bounds: extend u using summable_pnat_iff_summable_nat
  have hsum_deriv' : ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K), ‖a' n * (2 * π * I * n) *
        cexp (2 * π * I * n * k.1)‖ ≤ u n := fun K hK hKc => by
    obtain ⟨u, hu_sum, hu_bound⟩ := hsum_deriv K hK hKc
    let u' : ℕ → ℝ := fun n => if h : 0 < n then u ⟨n, h⟩ else 0
    have hu' : ∀ n : ℕ+, u' n = u n := fun n => dite_eq_left n.pos
    refine ⟨u', summable_pnat_iff_summable_nat.mp (hu_sum.congr fun n => by rw [hu']),
      fun n k => ?_⟩
    by_cases hn : 0 < n
    · simp only [a', u', dite_eq_left hn]; exact hu_bound _ k
    · simp only [Nat.not_lt, Nat.le_zero] at hn; simp [a', u', hn]
  -- Apply D_qexp_tsum and convert sums via tsum_pNat
  have hD := D_qexp_tsum a' z (summable_pnat_iff_summable_nat.mp
    (hsum.congr fun n => by rw [ha'])) hsum_deriv'
  calc D (fun w => ∑' n : ℕ+, a n * cexp (2 * π * I * n * w)) z
      = D (fun w : ℍ => ∑' n : ℕ, a' n * cexp (2 * π * I * n * (w : ℂ))) z := by
          congr 1; ext w; rw [← tsum_pNat _ (by simp [a'])]; exact tsum_congr fun n => by rw [ha']
    _ = ∑' n : ℕ, (n : ℂ) * a' n * cexp (2 * π * I * n * (z : ℂ)) := hD
    _ = ∑' n : ℕ+, (n : ℂ) * a n * cexp (2 * π * I * n * z) := by
          rw [← tsum_pNat _ (by simp [a'])]; exact tsum_congr fun n => by rw [ha']

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
theorem deriv_resToImagAxis_eq (F : ℍ → ℂ) (hF : MDiff F) {t : ℝ} (ht : 0 < t) :
    deriv F.resToImagAxis t = -2 * π * (D F).resToImagAxis t := by
  let z : ℍ := ⟨I * t, by simp [ht]⟩
  let h : ℂ → ℂ := fun y => Complex.mulAux (0 : ℝ) 1 y
  let g : ℝ → ℂ := h ∘ fun s : ℝ => (s : ℂ)
  have h_eq : F.resToImagAxis =ᶠ[nhds t] ((F ∘ ofComplex) ∘ g) := by
    filter_upwards [lt_mem_nhds ht] with s hs
    simp only [Function.resToImagAxis_apply, ResToImagAxis, hs, ↓reduceDIte,
      Function.comp_apply]
    change F (⟨I * (s : ℂ), by simp [hs]⟩ : ℍ) = F (ofComplex (g s))
    rw [show g s = I * (s : ℂ) by
      change Complex.mulAux (0 : ℝ) 1 (s : ℂ) = Complex.mulAux (0 : ℝ) 1 (s : ℂ)
      rfl]
    rw [ofComplex_apply_of_im_pos (by simp [hs])]
  rw [show deriv F.resToImagAxis t = deriv (((F ∘ ofComplex) ∘ g)) t from h_eq.deriv_eq]
  rw [show deriv (((F ∘ ofComplex) ∘ g)) t = deriv (F ∘ ofComplex) z * I by
    change deriv (fun y : ℝ => F (ofComplex (Complex.mulAux (0 : ℝ) 1 (y : ℂ)))) t =
      deriv (F ∘ ofComplex) z * I
    have hF' := (mdifferentiableAt_iff.mp (hF z)).hasDerivAt
    have hh : HasDerivAt h I (t : ℂ) := by
      change HasDerivAt (fun y : ℂ => I * y) I (t : ℂ)
      simpa [id, mul_one] using (hasDerivAt_id (t : ℂ)).const_mul I
    simpa [h, Function.comp_def] using (hF'.comp (t : ℂ) hh).comp_ofReal.deriv]
  have hD : deriv (F ∘ ofComplex) z = 2 * π * I * D F z := by
    simp only [normalizedDerivOfComplex]; field_simp
  simp only [hD, Function.resToImagAxis_apply, ResToImagAxis, dite_eq_left ht, z]
  ring_nf; simp only [I_sq]; ring

/-- The derivative of a function with zero imaginary part also has zero imaginary part. -/
lemma im_deriv_eq_zero_of_im_eq_zero {f : ℝ → ℂ} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (him : ∀ s, (f s).im = 0) :
    (deriv f t).im = 0 := by
  simpa [funext him] using ((hasDerivAt_const t Complex.imCLM).clm_apply hf.hasDerivAt).deriv.symm

/-- If F is real on the imaginary axis and MDifferentiable, then D F is also real
on the imaginary axis. -/
@[fun_prop]
theorem D_real_of_real {F : ℍ → ℂ} (hF_real : ResToImagAxis.Real F)
    (hF_diff : MDiff F) : ResToImagAxis.Real (D F) := fun t ht => by
  have him : ∀ s, (F.resToImagAxis s).im = 0 := fun s => by
    by_cases hs : 0 < s
    · exact hF_real s hs
    · simp [ResToImagAxis, hs]
  have h_im_deriv :=
    im_deriv_eq_zero_of_im_eq_zero (ResToImagAxis.Differentiable F hF_diff t ht) him
  have h_im_eq : (deriv F.resToImagAxis t).im = -2 * π * ((D F).resToImagAxis t).im := by
    simpa [mul_assoc, ofReal_mul] using congrArg Complex.im (deriv_resToImagAxis_eq F hF_diff ht)
  exact (mul_eq_zero.mp (h_im_deriv ▸ h_im_eq).symm).resolve_left
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)

/-- If F is real on the imaginary axis and MDifferentiable, then the Serre derivative
(of real weight) is also real on the imaginary axis. -/
@[fun_prop]
theorem serreDerivative_real_of_real {F : ℍ → ℂ} {k : ℝ} (hF_real : ResToImagAxis.Real F)
    (hF_diff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) : ResToImagAxis.Real (serreDerivative k F) := by
  have h : ResToImagAxis.Real (D F - ((k * 12⁻¹ : ℝ) • (E₂ * F))) := by fun_prop
  convert h using 1
  ext z
  simp only [serreDerivative_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, real_smul,
    ofReal_mul, ofReal_inv, ofReal_ofNat, sub_right_inj]
  ring

/-- The real part of F.resToImagAxis has derivative -2π * ((D F).resToImagAxis t).re at t. -/
lemma hasDerivAt_resToImagAxis_re {F : ℍ → ℂ} (hdiff : MDiff F)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => (F.resToImagAxis s).re) (-2 * π * ((D F).resToImagAxis t).re) t := by
  have hdiffAt := ResToImagAxis.Differentiable F hdiff t ht
  have hderivC := hdiffAt.hasDerivAt.congr_deriv (deriv_resToImagAxis_eq F hdiff ht)
  simpa using (hasDerivAt_const t (Complex.reCLM : ℂ →L[ℝ] ℝ)).clm_apply hderivC

/-- If `g(t₀) = 0` and `deriv g t₀ < 0`, then `g` is negative shortly after `t₀`. -/
lemma neg_after_zero_of_deriv_neg {g : ℝ → ℝ} {t₀ : ℝ}
    (hg0 : g t₀ = 0) (hd : deriv g t₀ < 0) :
    ∃ δ > 0, ∀ s, t₀ < s → s < t₀ + δ → g s < 0 := by
  have hdiff : DifferentiableAt ℝ g t₀ := by
    by_contra h; simp [deriv_zero_of_not_differentiableAt h] at hd
  have hda : HasDerivAt g (deriv g t₀) t₀ := hdiff.hasDerivAt
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hda
  have hε : (0 : ℝ) < -deriv g t₀ / 2 := by linarith
  have hio := hda.def hε
  rw [Filter.Eventually, Metric.mem_nhds_iff] at hio
  obtain ⟨δ, hδ, hball⟩ := hio
  refine ⟨δ, hδ, fun s hs1 hs2 => ?_⟩
  have hh_pos : 0 < s - t₀ := sub_pos.mpr hs1
  have hmem : s - t₀ ∈ Metric.ball (0 : ℝ) δ := by
    simpa [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
           abs_of_pos hh_pos] using sub_left_lt_of_lt_add hs2
  have hest := hball hmem
  simp only [Set.mem_ofPred_eq, hg0, sub_zero, smul_eq_mul, norm_eq_abs, abs_of_pos hh_pos] at hest
  have := (abs_le.mp hest).2
  rw [show s = t₀ + (s - t₀) by ring]
  linarith [div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hh_pos hd) (by norm_num : (0 : ℝ) < 2)]

/-- If `g` is continuous on `(0, ∞)`, positive for `t ≥ t₀`, and has strictly negative
derivative at any zero in `(0, t₀)`, then `g` is positive on all of `(0, ∞)`. -/
lemma pos_of_deriv_neg_at_zeros {g : ℝ → ℝ}
    (hcont : ContinuousOn g (Set.Ioi 0))
    {t₀ : ℝ} (_ht₀ : 0 < t₀)
    (hpos : ∀ t, t₀ ≤ t → 0 < g t)
    (hderiv : ∀ t, 0 < t → t < t₀ → g t = 0 → deriv g t < 0) :
    ∀ t, 0 < t → 0 < g t := by
  intro t ht
  by_cases htge : t₀ ≤ t
  · exact hpos t htge
  by_contra hle
  push Not at hle
  let S := Set.Icc t t₀ ∩ g ⁻¹' Set.Iic 0
  have hIcc_sub : Set.Icc t t₀ ⊆ Set.Ioi 0 := fun s hs => lt_of_lt_of_le ht hs.1
  have hS_closed : IsClosed S :=
    (hcont.mono hIcc_sub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hS_bdd : BddAbove S := ⟨t₀, fun s hs => hs.1.2⟩
  have hS_ne : S.Nonempty := ⟨t, ⟨⟨le_refl _, le_of_lt (not_le.mp htge)⟩, hle⟩⟩
  let T := sSup S
  obtain ⟨⟨hT_ge_t, h_sSup⟩, hT_le⟩ := hS_closed.csSup_mem hS_ne hS_bdd
  have hT_lt : T < t₀ := by
    rcases eq_or_lt_of_le h_sSup with h | h
    · exact absurd (h ▸ hT_le) (not_le.mpr (hpos t₀ le_rfl))
    · exact h
  have hT_pos : 0 < T := lt_of_lt_of_le ht hT_ge_t
  have hgT_eq : g T = 0 := by
    by_contra hne
    have hlt' : g T < 0 := lt_of_le_of_ne hT_le hne
    have hcT : ContinuousAt g T :=
      (hcont T (Set.mem_Ioi.mpr hT_pos)).continuousAt (isOpen_Ioi.mem_nhds hT_pos)
    obtain ⟨ε, hε, hball_neg⟩ := show ∃ ε > 0, ball T ε ⊆ {x | g x < 0} by
      simpa [← Metric.mem_nhds_iff, Filter.Eventually] using Tendsto.eventually_lt_const hlt' hcT
    have hd : 0 < min ε (t₀ - T) / 2 := half_pos (lt_min hε (sub_pos.mpr hT_lt))
    have : T + min ε (t₀ - T) / 2 ∈ S :=
      ⟨⟨by linarith, by linarith [min_le_right ε (t₀ - T)]⟩,
       Set.mem_preimage.mpr (Set.mem_Iic.mpr (le_of_lt (hball_neg (by
        rw [Metric.mem_ball, Real.dist_eq]
        have : T + min ε (t₀ - T) / 2 - T = min ε (t₀ - T) / 2 := by ring
        rw [this, abs_of_pos hd]; linarith [min_le_left ε (t₀ - T)]))))⟩
    linarith [le_csSup hS_bdd this]
  obtain ⟨δ, hδ, hneg⟩ := neg_after_zero_of_deriv_neg hgT_eq (hderiv T hT_pos hT_lt hgT_eq)
  have hmin_pos : 0 < min δ (t₀ - T) := lt_min hδ (sub_pos.mpr hT_lt)
  have : T + min δ (t₀ - T) / 2 ∈ S :=
    ⟨⟨by linarith, by linarith [min_le_right δ (t₀ - T)]⟩,
     Set.mem_preimage.mpr (Set.mem_Iic.mpr (le_of_lt (hneg _ (by linarith)
       (by linarith [min_le_left δ (t₀ - T)]))))⟩
  linarith [le_csSup hS_bdd this]

/--
Let $F : \mathbb{H} \to \mathbb{C}$ be a holomorphic function where $F(it)$ is real for all $t > 0$.
Assume that Serre derivative $\partial_k F$ is positive on the imaginary axis.
If $F(it)$ is positive for sufficiently large $t$, then $F(it)$ is positive for all $t > 0$.
-/
theorem antiSerreDerPos {F : ℍ → ℂ} {k : ℤ} (hMD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hSDF : ResToImagAxis.Pos (serreDerivative k F))
    (hF : ResToImagAxis.EventuallyPos F) : ResToImagAxis.Pos F := by
  obtain ⟨_, hSDF_pos⟩ := hSDF
  obtain ⟨hF_real, t₀, ht₀_pos, hF_pos⟩ := hF
  refine ⟨hF_real, fun t ht => ?_⟩
  have key : ∀ s, 0 < s → 0 < (F.resToImagAxis s).re := by
    refine  pos_of_deriv_neg_at_zeros ?_ ht₀_pos hF_pos ?_
    · intro s hs
      exact (continuous_re.continuousAt.comp
        (ResToImagAxis.Differentiable F hMD s hs).continuousAt).continuousWithinAt
    · intro s hs _ hgs
      have hda := hasDerivAt_resToImagAxis_re hMD hs
      rw [hda.deriv]
      have h_ria : F.resToImagAxis s = F ⟨I * s, by simp [hs]⟩ := by
        simp [resToImagAxis, ResToImagAxis, dite_eq_left hs]
      have hz : F (⟨I * s, by simp [hs]⟩ : ℍ) = 0 := by
        apply Complex.ext
        · rw [zero_re, ← h_ria]; exact hgs
        · rw [zero_im, ← h_ria]; exact (hF_real s hs)
      have : 0 < ((D F).resToImagAxis s).re := by
        simpa [resToImagAxis, ResToImagAxis, dite_eq_left hs,
          serreDerivative_apply, hz, mul_zero, sub_zero] using hSDF_pos s hs
      nlinarith [pi_pos]
  exact key t ht
