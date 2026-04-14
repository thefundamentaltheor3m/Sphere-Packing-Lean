module

public import SpherePacking.ForMathlib.MDifferentiableFunProp

public import SpherePacking.ModularForms.Eisenstein
public import SpherePacking.ModularForms.tsumderivWithin
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

/-!
# Serre derivative and Ramanujan identities

This file defines the Serre derivative on modular forms and proves Ramanujan's derivative formulas
for Eisenstein series.
-/

open scoped ModularForm MatrixGroups Manifold Topology BigOperators

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap ModularForm
open ModularFormClass
open Metric Filter Function

/-!
Definition of (Serre) derivative of modular forms.
Prove Ramanujan's formulas on derivatives of Eisenstein series.
-/
@[expose] public noncomputable def D (F : ℍ → ℂ) : ℍ → ℂ :=
  fun (z : ℍ) => (2 * π * I)⁻¹ * ((deriv (F ∘ ofComplex)) z)

/--
TODO: Remove this or move this to somewhere more appropriate.
-/
lemma MDifferentiableAt_DifferentiableAt {F : ℍ → ℂ} {z : ℍ}
  (h : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F z) :
  DifferentiableAt ℂ (F ∘ ofComplex) ↑z := by
  exact UpperHalfPlane.mdifferentiableAt_iff.mp h

/--
The converse direction: `DifferentiableAt` on ℂ implies `MDifferentiableAt` on ℍ.
-/
public lemma DifferentiableAt_MDifferentiableAt {G : ℂ → ℂ} {z : ℍ}
  (h : DifferentiableAt ℂ G ↑z) :
  MDiffAt (G ∘ (↑) : ℍ → ℂ) z := by
  rw [mdifferentiableAt_iff]
  refine h.congr_of_eventuallyEq <| Filter.eventuallyEq_of_mem (isOpen_upperHalfPlaneSet.mem_nhds
    z.im_pos) (by intro w hw; simp [Function.comp, ofComplex_apply_of_im_pos hw])

/--
The derivative operator `D` preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `D F` is also MDifferentiable.
-/
public theorem D_differentiable {F : ℍ → ℂ} (hF : MDiff F) : MDiff (D F) := fun z =>
  MDifferentiableAt.mul mdifferentiableAt_const <| DifferentiableAt_MDifferentiableAt <|
    ((UpperHalfPlane.mdifferentiable_iff.mp hF).deriv isOpen_upperHalfPlaneSet).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

/-- MDifferentiability of `E₂`.
TODO: Move this to E2.lean. -/
public theorem E₂_holo' : MDiff E₂ := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hη : DifferentiableOn ℂ η {z : ℂ | 0 < z.im} := by
    intro z hz
    have hz' : DifferentiableAt ℂ η z := by
      simpa using (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (z := z) hz)
    exact hz'.differentiableWithinAt
  have hlog : DifferentiableOn ℂ (logDeriv η) {z | 0 < z.im} :=
    (hη.deriv isOpen_upperHalfPlaneSet).div hη fun z hz => by
      simpa using (ModularForm.eta_ne_zero (z := z) hz)
  exact (hlog.const_mul ((↑π * I / 12)⁻¹)).congr fun z hz => by
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz,
      show logDeriv η z = (↑π * I / 12) * E₂ ⟨z, hz⟩ by
        simpa [E₂] using (ModularForm.logDeriv_eta_eq_E2 ⟨z, hz⟩)]
    field_simp [Real.pi_ne_zero]

/--
Basic properties of derivatives: linearity, Leibniz rule, etc.
-/
@[simp]
public theorem D_add (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) : D (F + G) = D F + D G := by
  ext z
  simpa [D, mul_add] using congrArg ((2 * π * I)⁻¹ * ·)
    (deriv_add (MDifferentiableAt_DifferentiableAt (hF z))
      (MDifferentiableAt_DifferentiableAt (hG z)))

/-- Compatibility of `D` with negation. -/
@[simp]
public theorem D_neg (F : ℍ → ℂ) (hF : MDiff F) : D (-F) = -D F := by
  ext z
  have hderiv : deriv ((-F) ∘ ofComplex) (z : ℂ) = -deriv (F ∘ ofComplex) (z : ℂ) :=
    (MDifferentiableAt_DifferentiableAt (hF z)).hasDerivAt.neg.deriv
  simp [D, hderiv, mul_assoc]

/-- Compatibility of `D` with subtraction. -/
@[simp]
public theorem D_sub (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) : D (F - G) = D F - D G := by
  simpa [sub_eq_add_neg, D_neg (F := G) hG] using D_add F (-G) hF hG.neg

/-- Compatibility of `D` with scalar multiplication. -/
@[simp]
public theorem D_smul (c : ℂ) (F : ℍ → ℂ) : D (c • F) = c • D F := by
  ext z
  have hderiv : deriv ((c • F) ∘ ofComplex) (z : ℂ) = c • deriv (F ∘ ofComplex) z := by
    simpa [Pi.smul_apply] using (deriv_const_smul_field (x := (z : ℂ)) c (F ∘ ofComplex))
  simp [D, hderiv, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Leibniz rule for `D`. -/
@[simp]
public theorem D_mul (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    D (F * G) = D F * G + F * D G := by
  ext z
  have hderiv : deriv ((F * G) ∘ ofComplex) z =
      deriv (F ∘ ofComplex) z * G z + F z * deriv (G ∘ ofComplex) z := by
    simpa [Function.comp_apply, ofComplex_apply] using
      deriv_mul (MDifferentiableAt_DifferentiableAt (hF z))
        (MDifferentiableAt_DifferentiableAt (hG z))
  simp [D, hderiv, mul_add, mul_assoc, mul_left_comm, mul_comm]

@[simp]
public theorem D_sq (F : ℍ → ℂ) (hF : MDiff F) : D (F ^ 2) = 2 * F * D F := by
  rw [pow_two, D_mul F F hF hF]
  ring_nf

/-- A specialization of the Leibniz rule: `D (F^3)`. -/
@[simp]
public theorem D_cube (F : ℍ → ℂ) (hF : MDiff F) :
    D (F ^ 3) = 3 * F ^ 2 * D F := by
  have hF2 : MDiff (F ^ 2) := by simpa [pow_two] using (MDifferentiable.mul hF hF)
  rw [pow_succ', D_mul F (F ^ 2) hF hF2, D_sq F hF]
  ring_nf

/-- Division of MDifferentiable functions on ℍ is MDifferentiable, when the denominator
is everywhere nonzero. -/
lemma MDifferentiable_div {F G : ℍ → ℂ}
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hG_ne : ∀ z : ℍ, G z ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => F z / G z) := by
  intro τ
  rw [mdifferentiableAt_iff]
  exact ((MDifferentiableAt_DifferentiableAt (hF τ)).div
    (MDifferentiableAt_DifferentiableAt (hG τ))
    (by simp [Function.comp]; exact hG_ne _)).congr_of_eventuallyEq
    (Filter.EventuallyEq.symm (Filter.eventuallyEq_of_mem
      (isOpen_upperHalfPlaneSet.mem_nhds τ.2) (fun w hw => by
        simp [Function.comp, Pi.div_apply, ofComplex_apply_of_im_pos hw])))

/-- The derivative of a constant function is zero. -/
@[simp]
public theorem D_const (c : ℂ) (z : ℍ) : D (Function.const _ c) z = 0 := by
  unfold D
  change (2 * π * I)⁻¹ * deriv (fun _ : ℂ => c) (z : ℂ) = 0
  simp [deriv_const]

/-! ### Termwise differentiation of q-series (Lemma 6.45) -/

/-- Helper: HasDerivAt for a·exp(2πicw) with chain rule. -/
lemma hasDerivAt_qexp (a c w : ℂ) :
    HasDerivAt (fun z => a * cexp (2 * π * I * c * z))
      (a * (2 * π * I * c) * cexp (2 * π * I * c * w)) w := by
  have h := (hasDerivAt_id w).const_mul (2 * π * I * c)
  simp only [mul_one, id] at h
  have := ((Complex.hasDerivAt_exp _).scomp w h).const_mul a
  simp only [smul_eq_mul] at this ⊢
  simpa [Function.comp_def, mul_assoc] using this

/-- Helper: derivWithin for qexp term on upper half-plane. -/
lemma derivWithin_qexp (a c : ℂ) (w : ℂ) (hw : 0 < w.im) :
    derivWithin (fun z => a * cexp (2 * π * I * c * z))
      {z : ℂ | 0 < z.im} w = a * (2 * π * I * c) * cexp (2 * π * I * c * w) :=
  ((hasDerivAt_qexp a c w).hasDerivWithinAt).derivWithin
    (isOpen_upperHalfPlaneSet.uniqueDiffWithinAt hw)

/-- Lemma 6.45 (Blueprint): D acts as q·d/dq on one q-term: D(a·qⁿ) = n·a·qⁿ. -/
public theorem D_qexp_term (n : ℤ) (a : ℂ) (z : ℍ) :
    D (fun w => a * cexp (2 * π * I * n * w)) z =
      n * a * cexp (2 * π * I * n * z) := by
  have h_agree :
      ((fun w : ℍ => a * cexp (2 * π * I * n * w)) ∘ ofComplex)
          =ᶠ[nhds (z : ℂ)] fun w : ℂ => a * cexp (2 * π * I * n * w) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.2] with w hw
    simp [Function.comp_apply, ofComplex_apply_of_im_pos hw]
  rw [D, h_agree.deriv_eq, (hasDerivAt_qexp a n z).deriv]
  field_simp [two_pi_I_ne_zero]

/--
**Lemma 6.45 (Blueprint)**: $D$ commutes with tsum for $q$-series.
If F(z) = Σ a(n)·qⁿ where q = exp(2πiz), then D F(z) = Σ n·a(n)·qⁿ.

More precisely, this lemma shows that for a ℕ-indexed q-series with summable coefficients
satisfying appropriate derivative bounds, D acts termwise by multiplying coefficients by n.
-/
public theorem D_qexp_tsum (a : ℕ → ℂ) (z : ℍ)
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
    apply hn.not_ge
    have hbd := hu_bound n ⟨y, Set.mem_singleton y⟩
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h_ne)
    have h_pos : (0 : ℝ) < 2 * π * n := by positivity
    have h_key : ‖a n * cexp (2 * π * I * n * y)‖ * (2 * π * n) ≤ u n := by
      calc ‖a n * cexp (2 * π * I * n * y)‖ * (2 * π * n)
          = ‖a n * (2 * π * I * n) * cexp (2 * π * I * n * y)‖ := by
            simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real,
              Complex.norm_I, mul_one, Complex.norm_natCast, Real.norm_of_nonneg pi_pos.le]
            ring
        _ ≤ u n := hbd
    have h_n_ge_1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr h_ne)
    calc ‖a n * cexp (2 * π * I * n * y)‖
        ≤ u n / (2 * π * n) := by rwa [le_div_iff₀ h_pos]
      _ ≤ u n / (2 * π) := by
          exact div_le_div_of_nonneg_left ((norm_nonneg _).trans hbd)
            (by positivity) (by nlinarith)
  -- Derivative bound for uniform convergence
  have hu : ∀ K ⊆ {w : ℂ | 0 < w.im}, IsCompact K →
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K),
        ‖derivWithin (fun w => a n * cexp (2 * π * I * n * w))
            {w : ℂ | 0 < w.im} k‖ ≤ u n := by
    intro K hK1 hK2
    obtain ⟨u, hu_sum, hu_bound⟩ := hsum_deriv K hK1 hK2
    exact ⟨u, hu_sum, fun n k => by
      rw [derivWithin_qexp _ _ _ (hK1 k.2)]
      exact hu_bound n k⟩
  -- Apply termwise differentiation
  have h_tsum_deriv := hasDerivAt_tsum_fun (fun n w => a n * cexp (2 * π * I * n * w))
    isOpen_upperHalfPlaneSet (z : ℂ) z.2 hf_sum hu hf_diff
  -- The composed function agrees with ℂ → ℂ in a neighborhood
  have h_agree :
      ((fun w : ℍ => ∑' n, a n * cexp (2 * π * I * n * w)) ∘ ofComplex)
        =ᶠ[nhds (z : ℂ)] fun w => ∑' n, a n * cexp (2 * π * I * n * w) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.2] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, UpperHalfPlane.coe_mk]
  rw [h_agree.deriv_eq, h_tsum_deriv.deriv]
  -- Simplify derivWithin using helper
  simp_rw [derivWithin_qexp _ _ _ z.2, ← tsum_mul_left]
  congr 1
  funext n
  field_simp [two_pi_I_ne_zero]

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
public theorem D_qexp_tsum_pnat (a : ℕ+ → ℂ) (z : ℍ)
    (hsum_deriv : ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
        ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ n (k : K), ‖a n * (2 * π * I * n) *
          cexp (2 * π * I * n * k.1)‖ ≤ u n) :
    D (fun w => ∑' n : ℕ+, a n * cexp (2 * π * I * n * w)) z =
      ∑' n : ℕ+, (n : ℂ) * a n * cexp (2 * π * I * n * z) := by
  -- Extend a to ℕ with a' 0 = 0
  let a' : ℕ → ℂ := fun n => if h : 0 < n then a ⟨n, h⟩ else 0
  have ha' : ∀ n : ℕ+, a' n = a n := fun n => dif_pos n.pos
  -- Derivative bounds: extend u using summable_pnat_iff_summable_nat
  have hsum_deriv' : ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K), ‖a' n * (2 * π * I * n) *
        cexp (2 * π * I * n * k.1)‖ ≤ u n := by
    obtain ⟨u, hu_sum, hu_bound⟩ := hsum_deriv K hK hKc
    let u' : ℕ → ℝ := fun n => if h : 0 < n then u ⟨n, h⟩ else 0
    have hu' : ∀ n : ℕ+, u' n = u n := fun n => dif_pos n.pos
    refine ⟨u', summable_pnat_iff_summable_nat.mp (hu_sum.congr fun n => by rw [hu']),
      fun n k => ?_⟩
    by_cases hn : 0 < n
    · simp only [a', u', dif_pos hn]; exact hu_bound _ k
    · simp only [Nat.not_lt, Nat.le_zero] at hn; simp [a', u', hn]
  -- Apply D_qexp_tsum and convert sums via tsum_pNat
  have hD := D_qexp_tsum a' z (summable_pnat_iff_summable_nat.mp
    (hsum.congr fun n => by rw [ha'])) hsum_deriv'
  calc D (fun w => ∑' n : ℕ+, a n * cexp (2 * π * I * n * w)) z
      = D (fun w : ℍ => ∑' n : ℕ, a' n * cexp (2 * π * I * n * (w : ℂ))) z := by
          congr 1
          ext w
          rw [← tsum_pNat _ (by simp [a'])]
          exact tsum_congr fun n => by rw [ha']
    _ = ∑' n : ℕ, (n : ℂ) * a' n * cexp (2 * π * I * n * (z : ℂ)) := hD
    _ = ∑' n : ℕ+, (n : ℂ) * a n * cexp (2 * π * I * n * z) := by
          rw [← tsum_pNat _ (by simp [a'])]
          exact tsum_congr fun n => by rw [ha']

/-- Serre derivative of weight `k` for functions `F : ℍ → ℂ`. -/
@[expose] public noncomputable def serre_D (k : ℂ) : (ℍ → ℂ) → (ℍ → ℂ) :=
  fun (F : ℍ → ℂ) => (fun z => D F z - k * 12⁻¹ * E₂ z * F z)

@[simp]
lemma serre_D_apply (k : ℂ) (F : ℍ → ℂ) (z : ℍ) :
    serre_D k F z = D F z - k * 12⁻¹ * E₂ z * F z := rfl

public lemma serre_D_eq (k : ℂ) (F : ℍ → ℂ) :
    serre_D k F = fun z => D F z - k * 12⁻¹ * E₂ z * F z := rfl

/-- Basic properties of Serre derivative. -/
public theorem serre_D_add (k : ℤ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serre_D k (F + G) = serre_D k F + serre_D k G := by
  ext z
  simp [serre_D, D_add F G hF hG]
  ring

/-- Compatibility of `serre_D` with subtraction. -/
public theorem serre_D_sub (k : ℤ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serre_D k (F - G) = serre_D k F - serre_D k G := by
  ext z
  simp [serre_D, D_sub F G hF hG]
  ring

/-- Compatibility of `serre_D` with scalar multiplication. -/
public theorem serre_D_smul (k : ℤ) (c : ℂ) (F : ℍ → ℂ) :
    serre_D k (c • F) = c • serre_D k F := by
  ext z
  simp [serre_D, D_smul c F]
  ring

/-- Leibniz rule for the Serre derivative, with weights `k₁` and `k₂`. -/
public theorem serre_D_mul (k₁ k₂ : ℤ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serre_D (k₁ + k₂) (F * G) = (serre_D k₁ F) * G + F * (serre_D k₂ G) := by
  ext z
  simp [serre_D, D_mul F G hF hG]
  ring

/-- The Serre derivative preserves MDifferentiability. -/
public theorem serre_D_differentiable {F : ℍ → ℂ} {k : ℂ}
    (hF : MDiff F) : MDiff (serre_D k F) := by
  refine (D_differentiable hF).sub ?_
  have hterm0 : MDiff (fun z => (k * 12⁻¹) * (E₂ z * F z)) :=
    (mdifferentiable_const : MDiff fun _ : ℍ => k * 12⁻¹).mul (E₂_holo'.mul hF)
  simpa [mul_assoc] using hterm0

/-! ### Helper lemmas for D_slash

These micro-lemmas compute derivatives of the components in the slash action formula.-/

section DSlashHelpers

open ModularGroup

variable (γ : SL(2, ℤ))

/-- Derivative of the denominator function: d/dz[cz + d] = c. -/
lemma deriv_denom (z : ℂ) :
    deriv (fun w => denom γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) := by
  simp only [denom]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]
  simp

/-- Derivative of the numerator function: d/dz[az + b] = a. -/
lemma deriv_num (z : ℂ) :
    deriv (fun w => num γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) := by
  simp only [num]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]
  simp

/-- Differentiability of denom. -/
public lemma differentiableAt_denom (z : ℂ) :
    DifferentiableAt ℂ (fun w => denom γ w) z := by
  simp only [denom]
  fun_prop

/-- Differentiability of num. -/
public lemma differentiableAt_num (z : ℂ) :
    DifferentiableAt ℂ (fun w => num γ w) z := by
  simp only [num]
  fun_prop

/-- Derivative of the Möbius transformation: d/dz[(az+b)/(cz+d)] = 1/(cz+d)².
Uses det(γ) = 1: a(cz+d) - c(az+b) = ad - bc = 1. -/
public lemma deriv_moebius (z : ℍ) :
    deriv (fun w => num γ w / denom γ w) z = 1 / (denom γ z) ^ 2 := by
  have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdet :
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (γ 1 1) -
        ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * (γ 1 0) = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    simp only [Matrix.det_fin_two, ← Int.cast_mul, ← Int.cast_sub] at this ⊢
    exact_mod_cast this
  rw [deriv_fun_div (differentiableAt_num γ z) (differentiableAt_denom γ z) hz,
      deriv_num, deriv_denom]
  -- The numerator collapses to `ad - bc = 1` by the determinant condition.
  have hnum_eq :
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * denom γ z -
          num γ z * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) = 1 := by
    -- expand `num/denom` and cancel the `z` terms
    simp [num, denom, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, hdet]
  simp [hnum_eq, one_div]

/-- Derivative of denom^(-k): d/dz[(cz+d)^(-k)] = -k * c * (cz+d)^(-k-1). -/
public lemma deriv_denom_zpow (k : ℤ) (z : ℍ) :
    deriv (fun w => (denom γ w) ^ (-k)) z =
        (-k : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (denom γ z) ^ (-k - 1) := by
  have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hderiv_denom :
      HasDerivAt (fun w => denom γ w) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) (z : ℂ) := by
    simpa [deriv_denom (γ := γ)] using (differentiableAt_denom γ (z : ℂ)).hasDerivAt
  have hcomp := (hasDerivAt_zpow (-k) (denom γ z) (Or.inl hz)).comp (z : ℂ) hderiv_denom
  simpa [Function.comp, Int.cast_neg, mul_assoc, mul_left_comm, mul_comm] using hcomp.deriv

end DSlashHelpers

/-- Derivative anomaly: `D` and the slash action. -/
public lemma D_slash (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) (γ : SL(2, ℤ)) :
    D (F ∣[k] γ) =
      (D F ∣[k + 2] γ) -
        fun z : ℍ =>
          (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z := by
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
    · have hsmul := UpperHalfPlane.coe_smul_of_det_pos hdet_pos ⟨w, hw⟩
      have hmob_im : 0 < (num γ w / denom γ w).im := by
        simpa [← hsmul] using (γ • (⟨w, hw⟩ : ℍ)).im_pos
      congr 1
      ext
      simpa [ofComplex_apply_of_im_pos hmob_im] using hsmul
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
  have hdiff_F_mobius :
      DifferentiableAt ℂ (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z :=
    (hdiff_F_comp.comp (z : ℂ) hdiff_mobius :
      DifferentiableAt ℂ ((F ∘ ofComplex) ∘ (fun w => num γ w / denom γ w)) z)
  have hprod_eq : (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) =
      ((fun w => (F ∘ ofComplex) (num γ w / denom γ w)) * fun w => (denom γ w) ^ (-k)) := rfl
  rw [hprod_eq, deriv_mul hdiff_F_mobius hdiff_denom_zpow]
  -- Apply chain rule to (F ∘ ofComplex) ∘ mobius
  have hchain :
      deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z =
        deriv (F ∘ ofComplex) (num γ z / denom γ z) *
          deriv (fun w => num γ w / denom γ w) z :=
    (hdiff_F_comp.hasDerivAt.comp (z : ℂ) hdiff_mobius.hasDerivAt).deriv
  -- Substitute the micro-lemmas
  have hderiv_mob := deriv_moebius γ z
  have hderiv_zpow := deriv_denom_zpow γ k z
  rw [hchain, hderiv_mob, hderiv_zpow]
  have hmob_eq : ↑(γ • z) = num γ z / denom γ z :=
    UpperHalfPlane.coe_smul_of_det_pos hdet_pos z
  -- Relate (F ∘ ofComplex)(mob z) to F(γ • z)
  have hF_mob : (F ∘ ofComplex) (num γ z / denom γ z) = F (γ • z) := by
    simp only [Function.comp_apply, ← hmob_eq, ofComplex_apply]
  simp only [ModularForm.SL_slash_apply, hF_mob, hmob_eq]
  have hpow_combine : 1 / (denom γ z) ^ 2 * (denom γ z) ^ (-k) = (denom γ z) ^ (-(k + 2)) := by
    rw [one_div, ← zpow_natCast (denom γ z) 2, ← zpow_neg, ← zpow_add₀ hz_denom_ne]
    ring_nf
  have hpow_m1 : (denom γ z) ^ (-k - 1) = (denom γ z) ^ (-1 : ℤ) * (denom γ z) ^ (-k) := by
    rw [← zpow_add₀ hz_denom_ne]
    ring_nf
  -- Rewrite powers on LHS
  conv_lhs =>
    rw [mul_assoc (deriv (F ∘ ofComplex) (num γ z / denom γ z)) (1 / denom γ z ^ 2) _,
      hpow_combine, hpow_m1]
  -- Now the goal should be cleaner - distribute and simplify
  simp only [zpow_neg_one]
  ring

/-- Transformation law for `E₂` under the weight-2 slash action. -/
public lemma E₂_slash (γ : SL(2, ℤ)) :
    (E₂ ∣[(2 : ℤ)] γ) =
      E₂ + fun z : ℍ => (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) := by
  ext z
  let a : ℂ := (1 / (2 * riemannZeta 2) : ℂ)
  have hG : (G₂ ∣[(2 : ℤ)] γ) z = G₂ z - D₂ γ z := by simpa using congrFun (G₂_transform γ) z
  have hcoeff : (-(a) * (2 * π * I)) = (12 : ℂ) * (2 * π * I)⁻¹ := by
    -- Multiply both sides by 2πi; reduces to 4aπ² = 12 since a = 3/π²
    have hpi : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    apply (mul_right_inj' two_pi_I_ne_zero).1
    simp only [a, riemannZeta_two]
    field_simp [hpi]
    norm_num [I_sq]
  have hcorr : a * (-D₂ γ z) = (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) := by
    have hcoeff' : a * (-(2 * π * I)) = (12 : ℂ) * (2 * π * I)⁻¹ := by
      simpa [a, mul_assoc, mul_left_comm, mul_comm, neg_mul, mul_neg] using hcoeff
    rw [← hcoeff']
    simp [D₂, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, a, EisensteinSeries.D2]
  unfold G₂ at hG
  calc
    (E₂ ∣[(2 : ℤ)] γ) z = a * (G₂ z - D₂ γ z) := by
      simp [E₂, EisensteinSeries.E2, G₂, a, hG, Pi.smul_apply, smul_eq_mul, mul_assoc]
    _ = a * G₂ z + (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) := by
      simpa [sub_eq_add_neg, mul_add, add_assoc, add_left_comm, add_comm] using
        congrArg (fun t => a * G₂ z + t) hcorr
    _ = E₂ z + (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) := by
      simp [E₂, EisensteinSeries.E2, G₂, Pi.smul_apply, smul_eq_mul, mul_assoc, a]

/-- Serre derivative is equivariant under the slash action. -/
public theorem serre_D_slash_equivariant (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) :
    ∀ γ : SL(2, ℤ), serre_D k F ∣[k + 2] γ = serre_D k (F ∣[k] γ) := by
  intro γ
  ext z
  let c : ℂ := (k : ℂ) * 12⁻¹
  let corr : ℍ → ℂ := fun w : ℍ => (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ w)
  have hD := congrFun (D_slash k F hF γ) z
  have hE : (E₂ ∣[(2 : ℤ)] γ) z = E₂ z + corr z := by simpa [corr] using congrFun (E₂_slash γ) z
  have hmul : (E₂ * F) ∣[k + 2] γ = (E₂ ∣[(2 : ℤ)] γ) * (F ∣[k] γ) := by
    -- Mathlib's lemma is stated for weight `2 + k`; rewrite to `k + 2`.
    simpa [add_comm, add_left_comm, add_assoc] using
      (ModularForm.mul_slash_SL2 (k1 := (2 : ℤ)) (k2 := k) (A := γ) (f := E₂) (g := F))
  have hserre : serre_D k F = D F - c • (E₂ * F) := by
    ext w
    simp [serre_D, c, smul_eq_mul, mul_assoc]
  have hLHS : (serre_D k F ∣[k + 2] γ) z =
      (D F ∣[k + 2] γ) z - c * ((E₂ z + corr z) * (F ∣[k] γ) z) := by
    simp [hserre, sub_eq_add_neg, SlashAction.neg_slash, Pi.smul_apply, smul_eq_mul,
      hmul, Pi.mul_apply, hE]
  have hD' : D (F ∣[k] γ) z = (D F ∣[k + 2] γ) z -
      (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z := by
    simpa [Pi.sub_apply] using hD
  simp only [hLHS, serre_D_apply, hD', c, corr]
  ring

public theorem serre_D_slash_invariant (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) (γ : SL(2, ℤ))
    (h : F ∣[k] γ = F) : serre_D k F ∣[k + 2] γ = serre_D k F := by
  simpa [h] using serre_D_slash_equivariant (k := k) (F := F) hF γ

/-
Interaction between (Serre) derivative and restriction to the imaginary axis.
-/
lemma StrictAntiOn.eventuallyPos_Ioi {g : ℝ → ℝ} (hAnti : StrictAntiOn g (Set.Ioi (0 : ℝ)))
    {t₀ : ℝ} (ht₀_pos : 0 < t₀) (hEv : ∀ t : ℝ, t₀ ≤ t → 0 < g t) :
    ∀ t : ℝ, 0 < t → 0 < g t := by
  intro t ht
  by_cases hcase : t₀ ≤ t
  · exact hEv t hcase
  · exact (hEv t₀ le_rfl).trans (hAnti ht ht₀_pos (lt_of_not_ge hcase))

/--
Chain rule on the imaginary axis: `d/dt F(it) = -2π * (D F)(it)`.
Equivalently, `deriv F.resToImagAxis t = -2π * (D F).resToImagAxis t`.
-/
public theorem deriv_resToImagAxis_eq (F : ℍ → ℂ) (hF : MDiff F) {t : ℝ} (ht : 0 < t) :
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
    have hF' := (MDifferentiableAt_DifferentiableAt (hF z)).hasDerivAt
    have hh : HasDerivAt h I (t : ℂ) := by
      change HasDerivAt (fun y : ℂ => I * y) I (t : ℂ)
      simpa [id, mul_one] using (hasDerivAt_id (t : ℂ)).const_mul I
    simpa [h, Function.comp_def] using (hF'.comp (t : ℂ) hh).comp_ofReal.deriv]
  have hD : deriv (F ∘ ofComplex) z = 2 * π * I * D F z := by simp only [D]; field_simp
  simp only [hD, Function.resToImagAxis_apply, ResToImagAxis, dif_pos ht, z]
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
    (hF_diff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) : ResToImagAxis.Real (D F) := fun t ht => by
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
theorem serre_D_real_of_real {F : ℍ → ℂ} {k : ℝ} (hF_real : ResToImagAxis.Real F)
    (hF_diff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) : ResToImagAxis.Real (serre_D k F) := by
  unfold serre_D
  have h : ResToImagAxis.Real (D F - ((k * 12⁻¹ : ℝ) • (E₂ * F))) := by fun_prop
  convert h using 1
  ext z
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, real_smul, ofReal_mul, ofReal_inv,
    ofReal_ofNat, sub_right_inj]
  ring

/-- The real part of F.resToImagAxis has derivative -2π * ((D F).resToImagAxis t).re at t. -/
lemma hasDerivAt_resToImagAxis_re {F : ℍ → ℂ} (hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => (F.resToImagAxis s).re) (-2 * π * ((D F).resToImagAxis t).re) t := by
  have hdiffAt := ResToImagAxis.Differentiable F hdiff t ht
  have hderivC := hdiffAt.hasDerivAt.congr_deriv (deriv_resToImagAxis_eq F hdiff ht)
  simpa using (hasDerivAt_const t (Complex.reCLM : ℂ →L[ℝ] ℝ)).clm_apply hderivC

/-- If F is MDifferentiable and antitone on the imaginary axis,
then D F has non-negative real part on the imaginary axis. -/
theorem D_nonneg_from_antitone {F : ℍ → ℂ}
    (hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hanti : AntitoneOn (fun t => (F.resToImagAxis t).re) (Set.Ioi 0)) :
    ∀ t, 0 < t → 0 ≤ ((D F).resToImagAxis t).re := by
  intro t ht
  have hderiv_nonpos : deriv (fun s => (F.resToImagAxis s).re) t ≤ 0 :=
    (derivWithin_of_isOpen isOpen_Ioi ht).symm.trans_le hanti.derivWithin_nonpos
  rw [(hasDerivAt_resToImagAxis_re hdiff ht).deriv] at hderiv_nonpos
  nlinarith [Real.pi_pos]

/-- If F is real on the imaginary axis, MDifferentiable, and has strictly negative derivative
on the imaginary axis, then D F is positive on the imaginary axis.

Note: `StrictAntiOn` is NOT sufficient - a strictly decreasing function can have deriv = 0
at isolated points (e.g., -x³ at x=0). Use this theorem when you can prove the derivative
is strictly negative, typically from q-expansion analysis. -/
theorem D_pos_from_deriv_neg {F : ℍ → ℂ}
    (hreal : ResToImagAxis.Real F)
    (hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hderiv_neg : ∀ t, 0 < t → deriv (fun s => (F.resToImagAxis s).re) t < 0) :
    ResToImagAxis.Pos (D F) := by
  refine ⟨D_real_of_real hreal hdiff, fun t ht => ?_⟩
  have hderiv := hderiv_neg t ht
  rw [(hasDerivAt_resToImagAxis_re hdiff ht).deriv] at hderiv
  nlinarith [Real.pi_pos]

public theorem hasDerivAt_re_resToImagAxis (F : ℍ → ℂ) (hF : MDiff F) :
    ∀ t,
      0 < t →
        HasDerivAt (fun t => (F.resToImagAxis t).re) (-2 * π * (ResToImagAxis (D F) t).re) t :=
  fun _ ht => hasDerivAt_resToImagAxis_re hF ht

public lemma mul_re_of_im_eq_zero {x y : ℂ} (hx : x.im = 0) (hy : y.im = 0) :
    (x * y).re = x.re * y.re := by simp [Complex.mul_re, hx, hy]

lemma strictAntiOn_Ioi_zero_of_deriv_neg {f : ℝ → ℝ}
    (hcont : ∀ x : ℝ, 0 < x → ContinuousWithinAt f (Set.Ioi (0 : ℝ)) x)
    (hn : ∀ x ∈ Set.Ioi (0 : ℝ), deriv f x < 0) : StrictAntiOn f (Set.Ioi (0 : ℝ)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ)) (fun x hx => hcont x hx) ?_
  simpa [interior_Ioi] using hn

/--
If $F$ is a modular form where $F(it)$ is positive for sufficiently large $t$ (i.e. constant term
is positive) and the derivative is positive, then $F$ is also positive.
-/
theorem antiDerPos {F : ℍ → ℂ} (hFderiv : MDiff F)
    (hFepos : ResToImagAxis.EventuallyPos F) (hDF : ResToImagAxis.Pos (D F)) :
    ResToImagAxis.Pos F := by
  obtain ⟨hF_real, t₀, ht₀_pos, hF_pos⟩ := hFepos
  obtain ⟨-, hDF_pos⟩ := hDF
  let g := fun t => (F.resToImagAxis t).re
  have hg (t : ℝ) (ht : 0 < t) : HasDerivAt g (-2 * π * (ResToImagAxis (D F) t).re) t := by
    simpa [g] using hasDerivAt_re_resToImagAxis F hFderiv t ht
  have hn : ∀ t ∈ Set.Ioi (0 : ℝ), deriv g t < 0 := fun t (ht : 0 < t) => by
    rw [(hg t ht).deriv]
    have : 0 < (ResToImagAxis (D F) t).re := hDF_pos t ht
    nlinarith [Real.pi_pos]
  have hAnti : StrictAntiOn g (Set.Ioi (0 : ℝ)) :=
    strictAntiOn_Ioi_zero_of_deriv_neg (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hn
  exact ⟨hF_real, fun t ht => StrictAntiOn.eventuallyPos_Ioi hAnti ht₀_pos hF_pos t ht⟩

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
  simp only [Set.mem_setOf_eq, hg0, sub_zero, smul_eq_mul, norm_eq_abs, abs_of_pos hh_pos] at hest
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
Logarithmic derivative of the discriminant: `D Δ = E₂ * Δ` (used in `antiSerreDerPos`).
-/
theorem antiSerreDerPos {F : ℍ → ℂ} {k : ℤ} (hMD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hSDF : ResToImagAxis.Pos (serre_D k F))
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
        simp [resToImagAxis, ResToImagAxis, dif_pos hs]
      have hz : F (⟨I * s, by simp [hs]⟩ : ℍ) = 0 := by
        apply Complex.ext
        · rw [zero_re, ← h_ria]; exact hgs
        · rw [zero_im, ← h_ria]; exact (hF_real s hs)
      have : 0 < ((D F).resToImagAxis s).re := by
        simpa [resToImagAxis, ResToImagAxis, dif_pos hs,
          serre_D_apply, hz, mul_zero, sub_zero] using hSDF_pos s hs
      nlinarith [pi_pos]
  exact key t ht

/--
Let $F : \mathbb{H} \to \mathbb{C}$ be holomorphic with $F(it)$ real for all $t > 0$.
Assume $\partial_k F$ is positive on the imaginary axis and $F(it)$ is positive for large $t$.
Then $F(it)$ is positive for all $t > 0$.
-/
public theorem antiSerreDerPos {F : ℍ → ℂ} {k : ℤ} (hFderiv : MDiff F)
    (hSDF : ResToImagAxis.Pos (serre_D k F)) (hF : ResToImagAxis.EventuallyPos F) :
    ResToImagAxis.Pos F := by
  -- Blueprint proof: integrating factor `Δ(it)^{-k/12}` makes the Serre
  -- derivative into an `D`-derivative.
  have hF_real : ResToImagAxis.Real F := hF.1
  obtain ⟨-, t₀, ht₀_pos, hF_pos⟩ := hF
  have hΔpos : ResToImagAxis.Pos Δ := Delta_imag_axis_pos
  have hΔreal : ResToImagAxis.Real Δ := hΔpos.1
  have hΔre_pos : ∀ t : ℝ, 0 < t → 0 < (Δ.resToImagAxis t).re := hΔpos.2
  let a : ℝ := (((k : ℂ) * 12⁻¹) : ℂ).re
  let g : ℝ → ℝ := fun t => (F.resToImagAxis t).re
  let d : ℝ → ℝ := fun t => (Δ.resToImagAxis t).re
  let h : ℝ → ℝ := fun t => g t * (d t) ^ (-a)
  have hE₂real : ResToImagAxis.Real E₂ := E₂_imag_axis_real
  have hg (t : ℝ) (ht : 0 < t) : HasDerivAt g (-2 * π * (ResToImagAxis (D F) t).re) t := by
    simpa [g] using hasDerivAt_re_resToImagAxis F hFderiv t ht
  have hΔholo : MDiff Δ := by simpa [Delta_apply] using (Delta.holo' : MDiff Δ)
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt d (-2 * π * (ResToImagAxis (D Δ) t).re) t := by
    simpa [d] using hasDerivAt_re_resToImagAxis Δ hΔholo t ht
  have hh (t : ℝ) (ht : 0 < t) :
      HasDerivAt h
        ((-2 * π * (ResToImagAxis (D F) t).re) * (d t) ^ (-a) +
            (g t) * ((-a) * (d t) ^ (-a - 1) * (-2 * π * (ResToImagAxis (D Δ) t).re))) t := by
      have hdne : d t ≠ 0 := ne_of_gt (hΔre_pos t ht)
      have hpow0 : HasDerivAt (fun x : ℝ => x ^ (-a)) ((-a) * (d t) ^ (-a - 1)) (d t) := by
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc] using
          Real.hasDerivAt_rpow_const (x := d t) (p := -a) (Or.inl hdne)
      have hpow : HasDerivAt (fun t => (d t) ^ (-a))
          ((-a) * (d t) ^ (-a - 1) * (-2 * π * (ResToImagAxis (D Δ) t).re)) t := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hpow0.comp t (hd t ht)
      simpa [h, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using
        (hg t ht).mul hpow
  have hn : ∀ t ∈ Set.Ioi (0 : ℝ), deriv h t < 0 := fun t (ht : 0 < t) => by
    have hdpos : 0 < d t := hΔre_pos t ht
    have hdpowpos : 0 < (d t) ^ (-a) := Real.rpow_pos_of_pos hdpos (-a)
    have hSpos : 0 < ((serre_D k F).resToImagAxis t).re := hSDF.2 t ht
    have hk_im : ((((k : ℂ) * 12⁻¹) : ℂ).im = 0) := by simp
    have hE₂im : (E₂.resToImagAxis t).im = 0 := hE₂real t ht
    have hFim : (F.resToImagAxis t).im = 0 := hF_real t ht
    have hΔim : (Δ.resToImagAxis t).im = 0 := hΔreal t ht
    have hDΔre : (ResToImagAxis (D Δ) t).re = (E₂.resToImagAxis t).re * d t := by
      simpa [D_Delta_eq_E₂_mul_Delta, ResToImagAxis, Function.resToImagAxis, ht, d] using
        mul_re_of_im_eq_zero (x := E₂.resToImagAxis t) (y := Δ.resToImagAxis t) hE₂im hΔim
    have hSerre_re :
        ((serre_D k F).resToImagAxis t).re =
          (ResToImagAxis (D F) t).re - a * (E₂.resToImagAxis t).re * g t := by
      have hRes :
          (serre_D k F).resToImagAxis t =
            (D F).resToImagAxis t -
              (((k : ℂ) * 12⁻¹) : ℂ) * (E₂.resToImagAxis t * F.resToImagAxis t) := by
        simp [serre_D, Function.resToImagAxis, ResToImagAxis, ht, mul_assoc]
      simpa [a, g, Complex.sub_re, Complex.mul_re, hk_im,
        mul_re_of_im_eq_zero (x := ResToImagAxis E₂ t) (y := ResToImagAxis F t) hE₂im hFim,
        mul_assoc] using congrArg Complex.re hRes
    -- Rewrite `deriv h t` as `(-2π) * (d t)^(-a) * ((serre_D k F)(it)).re`.
    have hderiv :
        deriv h t = -2 * (π * (d t) ^ (-a) * ((serre_D k F).resToImagAxis t).re) := by
      -- Start from the explicit derivative formula provided by `hh`.
      rw [(hh t ht).deriv]
      -- Rewrite the Serre-derivative term.
      rw [hSerre_re]
      have hx : d t ≠ 0 := (ne_of_gt hdpos)
      have hrpow : (d t) ^ (-a - 1) * d t = (d t) ^ (-a) := by
        have h := Real.rpow_add_one (x := d t) hx (-a - 1)
        -- `d^( (-a-1)+1 ) = d^(-a-1) * d`.
        -- Rearranged, this is exactly `d^(-a-1) * d = d^(-a)`.
        simpa [add_assoc, add_left_comm, add_comm] using h.symm
      grind only
    -- Combine signs.
    rw [hderiv]
    exact mul_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hAnti : StrictAntiOn h (Set.Ioi (0 : ℝ)) :=
    strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
      (fun x hx => (hh x hx).continuousAt.continuousWithinAt)
      (by simpa [interior_Ioi] using hn)
  have hEv : ∀ t : ℝ, t₀ ≤ t → 0 < h t := fun t ht => by
    simpa [h, g, d, mul_assoc] using
      mul_pos (hF_pos t ht) (Real.rpow_pos_of_pos (hΔre_pos t (ht₀_pos.trans_le ht)) (-a))
  have hall := StrictAntiOn.eventuallyPos_Ioi hAnti ht₀_pos hEv
  refine ⟨hF_real, fun t ht => ?_⟩
  exact pos_of_mul_pos_left (hall t ht) (Real.rpow_pos_of_pos (hΔre_pos t ht) _).le

/-! ## Cauchy estimates for `D` -/

/-- If `f : ℍ → ℂ` is `MDifferentiable` and a closed disk in `ℂ` lies in the upper
half-plane, then `f ∘ ofComplex` is `DiffContOnCl` on the corresponding open disk. -/
public lemma diffContOnCl_comp_ofComplex_of_mdifferentiable {f : ℍ → ℂ}
    (hf : MDiff f) {c : ℂ} {R : ℝ}
    (hclosed : Metric.closedBall c R ⊆ {z : ℂ | 0 < z.im}) :
    DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball c R) :=
  ⟨fun z hz =>
      (MDifferentiableAt_DifferentiableAt
        (hf ⟨z, hclosed (Metric.ball_subset_closedBall hz)⟩)).differentiableWithinAt,
    fun z hz =>
      (MDifferentiableAt_DifferentiableAt
        (hf ⟨z, hclosed (Metric.closure_ball_subset_closedBall hz)⟩)).continuousAt
        |>.continuousWithinAt⟩

/-- Closed ball centered at z with radius z.im/2 is contained in the upper half plane. -/
public lemma closedBall_center_subset_upperHalfPlane (z : ℍ) :
    Metric.closedBall (z : ℂ) (z.im / 2) ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  have hdist : dist w z ≤ z.im / 2 := Metric.mem_closedBall.mp hw
  have habs : |w.im - z.im| ≤ z.im / 2 := by
    simpa [Complex.sub_im] using
      (le_trans (by simpa [dist_eq_norm] using (abs_im_le_norm (w - z))) hdist)
  simp only [Set.mem_setOf_eq]
  linarith [(abs_le.mp habs).1, z.im_pos]

/-- Cauchy estimate for the D-derivative: if `f ∘ ofComplex` is holomorphic on a disk
of radius `r` around `z` and bounded by `M` on the boundary sphere,
then `‖D f z‖ ≤ M / (2πr)`. -/
public lemma norm_D_le_of_sphere_bound {f : ℍ → ℂ} {z : ℍ} {r M : ℝ}
    (hr : 0 < r) (hDiff : DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball (z : ℂ) r))
    (hbdd : ∀ w ∈ Metric.sphere (z : ℂ) r, ‖(f ∘ ofComplex) w‖ ≤ M) :
    ‖D f z‖ ≤ M / (2 * π * r) := calc ‖D f z‖
  _ = (2 * π)⁻¹ * ‖deriv (f ∘ ofComplex) z‖ := by simp [D, abs_of_pos Real.pi_pos]
  _ ≤ (2 * π)⁻¹ * (M / r) := by
        gcongr; exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hDiff hbdd
  _ = M / (2 * π * r) := by ring

lemma norm_D_le_div_pi_im_of_bounded {f : ℍ → ℂ} (hf : MDiff f) {M A : ℝ}
    (hMA : ∀ z : ℍ, A ≤ z.im → ‖f z‖ ≤ M) {z : ℍ} (hz : 2 * max A 0 + 1 ≤ z.im) :
    ‖D f z‖ ≤ M / (π * z.im) := by
  have hR_pos : 0 < z.im / 2 := by linarith [z.im_pos]
  have hclosed := closedBall_center_subset_upperHalfPlane z
  have hDiff : DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball (z : ℂ) (z.im / 2)) :=
    diffContOnCl_comp_ofComplex_of_mdifferentiable hf hclosed
  have hf_bdd_sphere :
      ∀ w ∈ Metric.sphere (z : ℂ) (z.im / 2), ‖(f ∘ ofComplex) w‖ ≤ M := by
    intro w hw
    have hw_im_pos : 0 < w.im := hclosed (Metric.sphere_subset_closedBall hw)
    have hdist : dist w z = z.im / 2 := Metric.mem_sphere.mp hw
    have him : |(w - z).im| ≤ dist w z := by simpa [dist_eq_norm] using abs_im_le_norm (w - z)
    have habs : |w.im - z.im| ≤ z.im / 2 := by simpa [Complex.sub_im, hdist] using him
    have hw_im_ge_A : A ≤ w.im := by linarith [(abs_le.mp habs).1, le_max_left A (0 : ℝ)]
    simpa [ofComplex_apply_of_im_pos hw_im_pos] using hMA ⟨w, hw_im_pos⟩ hw_im_ge_A
  have hDz : ‖D f z‖ ≤ M / (2 * π * (z.im / 2)) :=
    norm_D_le_of_sphere_bound hR_pos hDiff hf_bdd_sphere
  simpa [div_eq_mul_inv] using (hDz.trans_eq (by ring))

/-- The D-derivative is bounded at infinity for bounded holomorphic functions.

For y large (y ≥ 2·max(A,0) + 1), we use a ball of radius z.im/2 around z.
The ball lies in the upper half plane, f is bounded by M on it, and
`norm_D_le_of_sphere_bound` gives ‖D f z‖ ≤ M/(π·z.im) ≤ M/π. -/
public lemma D_isBoundedAtImInfty_of_bounded {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (D f) := by
  rw [isBoundedAtImInfty_iff] at hbdd ⊢
  obtain ⟨M, A, hMA⟩ := hbdd
  refine ⟨M / π, 2 * max A 0 + 1, ?_⟩
  intro z hz
  have hz_im_ge_1 : 1 ≤ z.im := by linarith [le_max_right A 0, hz]
  have hM_nonneg : 0 ≤ M :=
    (norm_nonneg _).trans (hMA z (by linarith [le_max_left A 0, hz]))
  calc
    ‖D f z‖ ≤ M / (π * z.im) := norm_D_le_div_pi_im_of_bounded hf hMA hz
    _ ≤ M / (π * 1) := by gcongr
    _ = M / π := by ring

/-- The D-derivative of a bounded holomorphic function tends to zero at infinity.

For z with im(z) = y, a Cauchy estimate on a ball of radius y/2 gives
‖D f z‖ ≤ M / (π · y), which tends to zero as y → ∞. -/
theorem D_tendsto_zero_of_isBoundedAtImInfty {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) :
    Filter.Tendsto (D f) atImInfty (nhds 0) := by
  obtain ⟨M, A, hMA⟩ := isBoundedAtImInfty_iff.mp hbdd
  -- ‖D f z‖ ≤ M / (π · z.im) by Cauchy estimate; the bound → 0 since z.im → ∞.
  suffices h : ∀ᶠ z : ℍ in atImInfty, ‖D f z‖ ≤ M / (π * z.im) by
    apply squeeze_zero_norm' h
    have := Filter.tendsto_im_atImInfty.inv_tendsto_atTop.const_mul (M / π)
    simp only [Pi.inv_apply, mul_zero] at this
    exact this.congr fun z => by field_simp
  rw [Filter.eventually_iff_exists_mem]
  exact ⟨{z : ℍ | 2 * max A 0 + 1 ≤ z.im},
    (atImInfty_mem _).mpr ⟨_, fun _ h => h⟩,
    fun z hz => norm_D_le_div_pi_im_of_bounded hf hMA hz⟩

-- TODO: The following lemma from Gauss overlaps with
-- `D_tendsto_zero_of_isBoundedAtImInfty` above. We will probably want to drop it.
/-- The D-derivative tends to 0 at infinity for bounded holomorphic functions. -/
public lemma D_isZeroAtImInfty_of_bounded {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) :
    IsZeroAtImInfty (D f) :=
  D_tendsto_zero_of_isBoundedAtImInfty hf hbdd

/-- The Serre derivative of a bounded holomorphic function is bounded at infinity.

serre_D k f = D f - (k/12)·E₂·f. Both terms are bounded:
- D f is bounded by `D_isBoundedAtImInfty_of_bounded`
- (k/12)·E₂·f is bounded since E₂ and f are bounded -/
public theorem serre_D_isBoundedAtImInfty {f : ℍ → ℂ} (k : ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) : IsBoundedAtImInfty (serre_D k f) := by
  unfold serre_D
  have hD : IsBoundedAtImInfty (D f) := D_isBoundedAtImInfty_of_bounded hf hbdd
  have hE₂f : IsBoundedAtImInfty (fun z => k * 12⁻¹ * E₂ z * f z) := by
    have hconst : IsBoundedAtImInfty (fun _ : ℍ => k * 12⁻¹) :=
      Filter.const_boundedAtFilter _ _
    have hmul : IsBoundedAtImInfty (fun z => (k * 12⁻¹) * (E₂ z * f z)) :=
      hconst.mul (E₂_isBoundedAtImInfty.mul hbdd)
    rw [isBoundedAtImInfty_iff] at hmul ⊢
    obtain ⟨M, A, hMA⟩ := hmul
    refine ⟨M, A, ?_⟩
    intro z hz
    simpa [mul_assoc] using hMA z hz
  exact hD.sub hE₂f

/-- A level-1 modular form is invariant under slash action by any element of SL(2,ℤ). -/
lemma ModularForm.slash_eq_self {k : ℤ} (f : ModularForm (Gamma 1) k) (γ : SL(2, ℤ)) :
    (f : ℍ → ℂ) ∣[k] γ = f := by
  change (f : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ) γ = f
  exact f.slash_action_eq' _ ⟨γ, mem_Gamma_one γ, rfl⟩

/-- The Serre derivative of a weight-k level-1 modular form is a weight-(k+2) modular form. -/
@[expose] public noncomputable def serre_D_ModularForm (k : ℤ) (f : ModularForm (Gamma 1) k) :
    ModularForm (Gamma 1) (k + 2) where
  toSlashInvariantForm := {
    toFun := serre_D k f
    slash_action_eq' := fun _ hγ => by
      obtain ⟨γ', -, rfl⟩ := Subgroup.mem_map.mp hγ
      change serre_D k f ∣[k + 2] γ' = serre_D k f
      exact serre_D_slash_invariant k f f.holo' γ' (f.slash_eq_self γ')
  }
  holo' := serre_D_differentiable f.holo'
  bdd_at_cusps' := fun hc => by
    refine bounded_at_cusps_of_bounded_at_infty hc fun _ hA => ?_
    obtain ⟨A', rfl⟩ := MonoidHom.mem_range.mp hA
    have hslash : serre_D k f ∣[k + 2] (Matrix.SpecialLinearGroup.mapGL ℝ) A' =
        serre_D k f := by
      change serre_D k f ∣[k + 2] A' = serre_D k f
      exact serre_D_slash_invariant k f f.holo' A' (f.slash_eq_self A')
    exact hslash.symm ▸
      serre_D_isBoundedAtImInfty_of_bounded k f.holo' (ModularFormClass.bdd_at_infty f)
