module
public import SpherePacking.ModularForms.EisensteinBase
public import SpherePacking.ModularForms.CuspFormIsoModforms
public import SpherePacking.ModularForms.Delta
public import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Complex.Liouville
import SpherePacking.ModularForms.Lv1Lv2Identities
import SpherePacking.Tactic.NormNumI
public import Mathlib.NumberTheory.ModularForms.SlashActions
public import SpherePacking.ForMathlib.Cusps


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

local notation "Iℂ" => 𝓘(ℂ)
local notation "MDiff" => MDifferentiable Iℂ Iℂ
local notation "MDiffAt" => MDifferentiableAt Iℂ Iℂ

/-!
Definition of (Serre) derivative of modular forms.
Prove Ramanujan's formulas on derivatives of Eisenstein series.
-/
@[expose] public noncomputable def D (F : ℍ → ℂ) : ℍ → ℂ :=
  fun (z : ℍ) => (2 * π * I)⁻¹ * ((deriv (F ∘ ofComplex)) z)

/-- Bridge lemma: MDifferentiability on `ℍ` gives differentiability of `F ∘ ofComplex`. -/
public lemma MDifferentiableAt_DifferentiableAt {F : ℍ → ℂ} {z : ℍ}
  (h : MDiffAt F z) :
  DifferentiableAt ℂ (F ∘ ofComplex) ↑z :=
  mdifferentiableAt_iff.mp h

/--
The converse direction: `DifferentiableAt` on ℂ implies `MDifferentiableAt` on ℍ.
-/
public lemma DifferentiableAt_MDifferentiableAt {G : ℂ → ℂ} {z : ℍ}
  (h : DifferentiableAt ℂ G ↑z) :
  MDiffAt (G ∘ (↑) : ℍ → ℂ) z := by
  rw [mdifferentiableAt_iff]
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [(UpperHalfPlane.isOpen_upperHalfPlaneSet).mem_nhds z.im_pos] with w hw
  simp [Function.comp, ofComplex_apply_of_im_pos hw]

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
  have hη : DifferentiableOn ℂ η _ :=
    fun z hz => (eta_DifferentiableAt_UpperHalfPlane ⟨z, hz⟩).differentiableWithinAt
  have hlog : DifferentiableOn ℂ (logDeriv η) {z | 0 < z.im} :=
    (hη.deriv isOpen_upperHalfPlaneSet).div hη fun _ hz => by
      simpa using eta_nonzero_on_UpperHalfPlane ⟨_, hz⟩
  exact (hlog.const_mul ((↑π * I / 12)⁻¹)).congr fun z hz => by
    simp [Function.comp_apply, ofComplex_apply_of_im_pos hz, eta_logDeriv ⟨z, hz⟩]
    field_simp [Real.pi_ne_zero]

/--
Basic properties of derivatives: linearity, Leibniz rule, etc.
-/
@[simp]
public theorem D_add (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    D (F + G) = D F + D G := by
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
public theorem D_sub (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G)
    : D (F - G) = D F - D G := by
  simpa [sub_eq_add_neg, D_neg (F := G) hG] using
    (D_add F (-G) hF (by simpa using hG.neg))


/-- Compatibility of `D` with scalar multiplication. -/
@[simp]
public theorem D_smul (c : ℂ) (F : ℍ → ℂ) (hF : MDiff F)
    : D (c • F) = c • D F := by
  ext z
  have hderiv :
      deriv ((c • F) ∘ ofComplex) (z : ℂ) = c • deriv (F ∘ ofComplex) z := by
    simpa [Function.comp, Pi.smul_apply] using
      deriv_const_smul (c := c) (f := F ∘ ofComplex) (MDifferentiableAt_DifferentiableAt (hF z))
  simp [D, hderiv, Pi.smul_apply, smul_eq_mul]
  ring_nf


/-- Leibniz rule for `D`. -/
@[simp]
public theorem D_mul (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G)
    : D (F * G) = D F * G + F * D G := by
  ext z
  have hderiv :
      deriv ((F * G) ∘ ofComplex) z =
        deriv (F ∘ ofComplex) z * G z + F z * deriv (G ∘ ofComplex) z := by
    simpa [Function.comp_apply, ofComplex_apply] using
      deriv_mul (MDifferentiableAt_DifferentiableAt (hF z))
        (MDifferentiableAt_DifferentiableAt (hG z))
  simp [D, hderiv, mul_add, mul_assoc, mul_left_comm, mul_comm]

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

/-! ### Termwise differentiation of q-series (Lemma 6.45) -/

/-- Helper: HasDerivAt for a·exp(2πicw) with chain rule. -/
lemma hasDerivAt_qexp (a c w : ℂ) :
    HasDerivAt (fun z => a * cexp (2 * π * I * c * z))
      (a * (2 * π * I * c) * cexp (2 * π * I * c * w)) w := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    ((Complex.hasDerivAt_exp (2 * π * I * c * w)).scomp w
      ((hasDerivAt_id w).const_mul (2 * π * I * c))).const_mul a

/-- Helper: derivWithin for qexp term on upper half-plane. -/
lemma derivWithin_qexp (a c : ℂ) (w : ℂ) (hw : 0 < w.im) :
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
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, UpperHalfPlane.coe_mk]
  rw [h_agree.deriv_eq, (hasDerivAt_qexp a n z).deriv]
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
        _ = ‖a n * (2 * π * I * n) * cexp (2 * π * I * n * y)‖ / (2 * π * n) := by
            rw [h_key]
        _ ≤ u n / (2 * π * n) := div_le_div_of_nonneg_right h_deriv_bound h_pos.le
        _ ≤ u n / (2 * π) := by
            apply div_le_div_of_nonneg_left (le_trans (norm_nonneg _) h_deriv_bound)
              (by positivity); nlinarith
    exact hn.not_ge h_bound
  -- Derivative bound for uniform convergence
  have hu : ∀ K ⊆ {w : ℂ | 0 < w.im}, IsCompact K →
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K),
        ‖derivWithin (fun w => a n * cexp (2 * π * I * n * w))
            {w : ℂ | 0 < w.im} k‖ ≤ u n := by
    intro K hK1 hK2
    obtain ⟨u, hu_sum, hu_bound⟩ := hsum_deriv K hK1 hK2
    exact ⟨u, hu_sum, fun n k => by rw [derivWithin_qexp _ _ _ (hK1 k.2)]; exact hu_bound n k⟩
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
  have h_deriv_simp : ∀ n, derivWithin (fun w => a n * cexp (2 * π * I * n * w))
      {w : ℂ | 0 < w.im} z = a n * (2 * π * I * n) * cexp (2 * π * I * n * z) :=
    fun n => derivWithin_qexp _ _ _ z.2
  simp_rw [h_deriv_simp, ← tsum_mul_left]
  congr 1; funext n; field_simp [two_pi_I_ne_zero]

/-
/--
Simplified version of `D_qexp_tsum` for ℕ+-indexed series (starting from n=1).
This is the form most commonly used for Eisenstein series q-expansions.

**Thin layer implementation:** Extends `a : ℕ+ → ℂ` to `ℕ → ℂ` with `a' 0 = 0`,
uses `tsum_pNat` and `nat_pos_tsum2` to convert between sums,
then applies `D_qexp_tsum`.
-/
public theorem D_qexp_tsum_pnat (a : ℕ+ → ℂ) (z : ℍ)
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
-/

/--
Serre derivative of weight $k$.
Note that the definition makes sense for any analytic function $F : \mathbb{H} \to \mathbb{C}$.
-/
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
public theorem serre_D_smul (k : ℤ) (c : ℂ) (F : ℍ → ℂ) (hF : MDiff F) :
    serre_D k (c • F) = c • serre_D k F := by
  ext z
  simp [serre_D, D_smul c F hF]
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
  have hterm0 : MDiff (fun z => (k * 12⁻¹) * (E₂ z * F z)) :=
    (mdifferentiable_const : MDiff fun _ : ℍ => k * 12⁻¹).mul (E₂_holo'.mul hF)
  have h_term : MDiff (fun z => k * 12⁻¹ * E₂ z * F z) := by
    simpa [mul_assoc] using hterm0
  exact (D_differentiable hF).sub h_term

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
  have hcomp :=
    (hasDerivAt_zpow (-k) (denom γ z) (Or.inl hz)).comp (z : ℂ) hderiv_denom
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
      ext
      · rw [ofComplex_apply_of_im_pos hmob_im]
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
  have hdiff_F_mobius :
      DifferentiableAt ℂ (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z := by
    rw [hcomp_eq]
    exact DifferentiableAt.comp (z : ℂ) hdiff_F_comp hdiff_mobius
  rw [show (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) =
      ((fun w => (F ∘ ofComplex) (num γ w / denom γ w)) * fun w => (denom γ w) ^ (-k)) by rfl]
  rw [deriv_mul hdiff_F_mobius hdiff_denom_zpow]
  -- Apply chain rule to (F ∘ ofComplex) ∘ mobius
  have hchain :
      deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z =
        deriv (F ∘ ofComplex) (num γ z / denom γ z) *
          deriv (fun w => num γ w / denom γ w) z := by
    rw [hcomp_eq, (hdiff_F_comp.hasDerivAt.comp (z : ℂ) hdiff_mobius.hasDerivAt).deriv]
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

/-- Transformation law for `E₂` under the weight-2 slash action. -/
public lemma E₂_slash (γ : SL(2, ℤ)) :
    (E₂ ∣[(2 : ℤ)] γ) =
      E₂ + fun z : ℍ => (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) := by
  ext z
  let a : ℂ := (1 / (2 * riemannZeta 2) : ℂ)
  have hG : (G₂ ∣[(2 : ℤ)] γ) z = G₂ z - D₂ γ z := by
    simpa using congrFun (G₂_transform γ) z
  have hcoeff : (-(a) * (2 * π * I)) = (12 : ℂ) * (2 * π * I)⁻¹ := by
    apply (mul_right_inj' two_pi_I_ne_zero).1
    dsimp [a]
    rw [riemannZeta_two]
    ring_nf
    have hpi : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp [hpi]
    ring_nf
    simp
  have hcorr : a * (-D₂ γ z) = (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) := by
    have hcoeff' : a * (-(2 * π * I)) = (12 : ℂ) * (2 * π * I)⁻¹ := by
      simpa [a, mul_assoc, mul_left_comm, mul_comm, neg_mul, mul_neg] using hcoeff
    rw [← hcoeff']
    simp [D₂, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, a]
  calc
    (E₂ ∣[(2 : ℤ)] γ) z = a * (G₂ z - D₂ γ z) := by
      simp [E₂, a, hG, Pi.smul_apply, smul_eq_mul, mul_assoc]
    _ = a * G₂ z + (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) := by
      simpa [sub_eq_add_neg, mul_add, add_assoc, add_left_comm, add_comm] using
        congrArg (fun t => a * G₂ z + t) hcorr
    _ = E₂ z + (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) := by
      simp [E₂, Pi.smul_apply, smul_eq_mul, mul_assoc, a]

/-- Serre derivative is equivariant under the slash action. -/
public theorem serre_D_slash_equivariant (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) :
    ∀ γ : SL(2, ℤ), serre_D k F ∣[k + 2] γ = serre_D k (F ∣[k] γ) := by
  intro γ
  ext z
  let c : ℂ := (k : ℂ) * 12⁻¹
  let corr : ℍ → ℂ := fun w : ℍ => (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ w)
  have h12 : (12 : ℂ) ≠ 0 := by norm_num
  have hD := congrFun (D_slash k F hF γ) z
  have hE : (E₂ ∣[(2 : ℤ)] γ) z = E₂ z + corr z := by
    simpa [corr] using congrFun (E₂_slash γ) z
  have hserre : serre_D k F = D F - c • (E₂ * F) := by
    ext w
    simp [serre_D, c, smul_eq_mul, mul_assoc]
  have hmul : (E₂ * F) ∣[k + 2] γ = (E₂ ∣[(2 : ℤ)] γ) * (F ∣[k] γ) := by
    -- Mathlib's lemma is stated for weight `2 + k`; rewrite to `k + 2`.
    simpa [add_comm, add_left_comm, add_assoc] using
      (ModularForm.mul_slash_SL2 (k1 := (2 : ℤ)) (k2 := k) (A := γ) (f := E₂) (g := F))
  -- Main computation, pointwise at `z`.
  calc
    (serre_D k F ∣[k + 2] γ) z
        = ((D F - c • (E₂ * F)) ∣[k + 2] γ) z := by simp [hserre]
    _ = (D F ∣[k + 2] γ) z - (c • ((E₂ * F) ∣[k + 2] γ)) z := by
          simp [sub_eq_add_neg, SlashAction.neg_slash]
    _ = (D F ∣[k + 2] γ) z - c * ((E₂ * F) ∣[k + 2] γ) z := by
          simp [Pi.smul_apply, smul_eq_mul]
    _ = (D F ∣[k + 2] γ) z - c * ((E₂ ∣[(2 : ℤ)] γ) z * (F ∣[k] γ) z) := by
          simp [hmul, Pi.mul_apply]
    _ = (D F ∣[k + 2] γ) z - c * ((E₂ z + corr z) * (F ∣[k] γ) z) := by
          rw [hE]
    _ = (D F ∣[k + 2] γ) z
          - c * (corr z * (F ∣[k] γ) z)
          - c * (E₂ z * (F ∣[k] γ) z) := by
          ring
    _ = (D F ∣[k + 2] γ) z
          - (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z
          - c * (E₂ z * (F ∣[k] γ) z) := by
          have hcorr : c * corr z = (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) := by
            dsimp [c, corr]
            simp [mul_assoc, mul_left_comm, mul_comm, h12]
          have hcorr' :
              c * (corr z * (F ∣[k] γ) z) =
                (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z := by
            simpa [mul_assoc] using congrArg (fun t => t * (F ∣[k] γ) z) hcorr
          simp [hcorr']
    _ = serre_D k (F ∣[k] γ) z := by
          -- Substitute the `D_slash` anomaly and unfold the Serre derivative.
          have hD' :
              D (F ∣[k] γ) z =
                (D F ∣[k + 2] γ) z -
                  (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z := by
            simpa [Pi.sub_apply] using hD
          -- Unfold `serre_D`, rewrite `D (F ∣[k] γ) z` using `hD'`, and reassociate.
          simp [serre_D, c, hD', mul_assoc]

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
  ring_nf
  simp only [I_sq]
  ring

/-- The derivative of a function with zero imaginary part also has zero imaginary part. -/
lemma im_deriv_eq_zero_of_im_eq_zero {f : ℝ → ℂ} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (him : ∀ s, (f s).im = 0) :
    (deriv f t).im = 0 := by
  simpa [funext him] using ((hasDerivAt_const t Complex.imCLM).clm_apply hf.hasDerivAt).deriv.symm

/-- If F is real on the imaginary axis and MDifferentiable, then D F is also real
on the imaginary axis. -/
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
  fun t ht => by
    have hdiff : DifferentiableAt ℝ F.resToImagAxis t := ResToImagAxis.Differentiable F hF t ht
    have hderivC : HasDerivAt F.resToImagAxis (-2 * π * (D F).resToImagAxis t) t :=
      hdiff.hasDerivAt.congr_deriv (deriv_resToImagAxis_eq F hF ht)
    simpa using
      (hasDerivAt_const (x := t) (c := (Complex.reCLM : ℂ →L[ℝ] ℝ))).clm_apply hderivC

public lemma mul_re_of_im_eq_zero {x y : ℂ} (hx : x.im = 0) (hy : y.im = 0) :
    (x * y).re = x.re * y.re := by
  simp [Complex.mul_re, hx, hy]

/--
Logarithmic derivative of the discriminant: `D Δ = E₂ * Δ` (used in `antiSerreDerPos`).
-/
public theorem D_Delta_eq_E₂_mul_Delta : D Δ = E₂ * Δ := by
  funext z
  have h_eq :
      (fun w : ℂ => Δ (ofComplex w)) =ᶠ[nhds (z : ℂ)] fun w => (η w) ^ (24 : ℕ) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simpa [ofComplex_apply_of_im_pos hw] using (Delta_eq_eta_pow (ofComplex w))
  have hηnz : η (z : ℂ) ≠ 0 := eta_nonzero_on_UpperHalfPlane z
  have hlog :
      logDeriv (fun w : ℂ => (η w) ^ (24 : ℕ)) (z : ℂ) = (2 * π * I) * E₂ z := by
    have hpowdiff : DifferentiableAt ℂ (fun x : ℂ => x ^ (24 : ℕ)) (η (z : ℂ)) := by
      fun_prop
    calc
      logDeriv (fun w : ℂ => (η w) ^ (24 : ℕ)) (z : ℂ) =
          logDeriv (fun x : ℂ => x ^ (24 : ℕ)) (η (z : ℂ)) * deriv η (z : ℂ) := by
            simpa [Function.comp] using
              (logDeriv_comp (x := (z : ℂ)) hpowdiff (eta_DifferentiableAt_UpperHalfPlane z))
      _ = ((24 : ℂ) / η (z : ℂ)) * deriv η (z : ℂ) := by
            simp [logDeriv_pow]
      _ = (24 : ℂ) * logDeriv η (z : ℂ) := by
            simp [logDeriv, div_eq_mul_inv, mul_assoc, mul_comm]
      _ = (2 * π * I) * E₂ z := by
            rw [eta_logDeriv z]
            have h12 : (12 : ℂ) ≠ 0 := by norm_num
            field_simp [h12]
            ring
  have hderiv_eta_pow :
      deriv (fun w : ℂ => (η w) ^ (24 : ℕ)) (z : ℂ) =
        (2 * π * I) * E₂ z * (η (z : ℂ) ^ (24 : ℕ)) := by
    have :
        deriv (fun w : ℂ => (η w) ^ (24 : ℕ)) (z : ℂ) =
          logDeriv (fun w : ℂ => (η w) ^ (24 : ℕ)) (z : ℂ) *
            (η (z : ℂ) ^ (24 : ℕ)) := by
      simp [logDeriv, div_mul_eq_mul_div, mul_div_cancel_right₀ _ (pow_ne_zero _ hηnz)]
    simpa [hlog, mul_assoc, mul_left_comm, mul_comm] using this
  have h2piI : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
  have hηpow : η (z : ℂ) ^ (24 : ℕ) = Δ z := (Delta_eq_eta_pow z).symm
  calc
    D Δ z = (2 * π * I)⁻¹ * deriv (fun w : ℂ => Δ (ofComplex w)) (z : ℂ) := rfl
    _ = (2 * π * I)⁻¹ * deriv (fun w : ℂ => (η w) ^ (24 : ℕ)) (z : ℂ) := by
          simp [h_eq.deriv_eq]
    _ = (2 * π * I)⁻¹ * ((2 * π * I) * E₂ z * (η (z : ℂ) ^ (24 : ℕ))) := by
          simp [hderiv_eta_pow]
    _ = E₂ z * (η (z : ℂ) ^ (24 : ℕ)) := by
          field_simp [h2piI]
    _ = E₂ z * Δ z := by simp [hηpow]

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
  have hg : ∀ t, 0 < t → HasDerivAt g (-2 * π * (ResToImagAxis (D F) t).re) t :=
    fun t ht => hasDerivAt_resToImagAxis_re hFderiv ht
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
  have hg :
      ∀ t, 0 < t → HasDerivAt g (-2 * π * (ResToImagAxis (D F) t).re) t :=
    fun t ht => by
      simpa [g] using hasDerivAt_re_resToImagAxis F hFderiv t ht
  have hΔholo : MDiff Δ := by
    simpa [Delta_apply] using (Delta.holo' : MDiff Δ)
  have hd :
      ∀ t, 0 < t → HasDerivAt d (-2 * π * (ResToImagAxis (D Δ) t).re) t :=
    fun t ht => by
      simpa [d] using hasDerivAt_re_resToImagAxis Δ hΔholo t ht
  have hh : ∀ t, 0 < t →
      HasDerivAt h
        ((-2 * π * (ResToImagAxis (D F) t).re) * (d t) ^ (-a) +
            (g t) * ((-a) * (d t) ^ (-a - 1) * (-2 * π * (ResToImagAxis (D Δ) t).re))) t :=
    fun t ht => by
      have hdpos : 0 < d t := hΔre_pos t ht
      have hdne : d t ≠ 0 := ne_of_gt hdpos
      have hpow :
          HasDerivAt (fun t => (d t) ^ (-a))
            ((-a) * (d t) ^ (-a - 1) * (-2 * π * (ResToImagAxis (D Δ) t).re)) t := by
        have hpow0 :
            HasDerivAt (fun x : ℝ => x ^ (-a)) ((-a) * (d t) ^ (-a - 1)) (d t) := by
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc] using
            (Real.hasDerivAt_rpow_const (x := d t) (p := -a) (Or.inl hdne))
        simpa [mul_assoc, mul_left_comm, mul_comm] using hpow0.comp t (hd t ht)
      have := (hg t ht).mul hpow
      simpa [h, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using this
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
      have h' := congrArg Complex.re hRes
      have houter :
          (((((k : ℂ) * 12⁻¹) : ℂ) * (E₂.resToImagAxis t * F.resToImagAxis t))).re =
            a * (E₂.resToImagAxis t * F.resToImagAxis t).re := by
        rw [Complex.mul_re]
        simp [a, hk_im]
      have hE₂im0 : (ResToImagAxis E₂ t).im = 0 := by
        simpa [Function.resToImagAxis_apply] using hE₂im
      have hFim0 : (ResToImagAxis F t).im = 0 := by
        simpa [Function.resToImagAxis_apply] using hFim
      simpa [a, g, Complex.sub_re, houter,
        mul_re_of_im_eq_zero (x := ResToImagAxis E₂ t) (y := ResToImagAxis F t) hE₂im0 hFim0,
        mul_assoc] using h'
    -- Rewrite `deriv h t` as `(-2π) * (d t)^(-a) * ((serre_D k F)(it)).re`.
    have hderiv :
        deriv h t = (-2 * π) * (d t) ^ (-a) * ((serre_D k F).resToImagAxis t).re := by
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
      have hshift : d t ^ (-1 - a) * d t = d t ^ (-a) := by
        simpa [show (-1 - a : ℝ) = (-a - 1) by grind] using hrpow
      -- Replace `(D Δ)(it)` and simplify the resulting expression.
      simp [hDΔre]
      ring_nf
      rw [show
          π * a * g t * d t ^ (-1 - a) * (ResToImagAxis E₂ t).re * d t * 2 =
            π * a * g t * (ResToImagAxis E₂ t).re * (d t ^ (-1 - a) * d t) * 2 by
          ac_rfl, hshift]
      ac_rfl
    have hneg : (-2 * π : ℝ) < 0 := by nlinarith [Real.pi_pos]
    -- Combine signs.
    rw [hderiv, mul_assoc]
    have hpos : 0 < (d t) ^ (-a) * ((serre_D k F).resToImagAxis t).re := mul_pos hdpowpos hSpos
    have hmul : (-2 * π : ℝ) * ((d t) ^ (-a) * ((serre_D k F).resToImagAxis t).re) < 0 :=
      mul_neg_of_neg_of_pos hneg hpos
    simpa [mul_assoc] using hmul
  have hAnti : StrictAntiOn h (Set.Ioi (0 : ℝ)) :=
    strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
      (fun x hx => (hh x hx).continuousAt.continuousWithinAt)
      (by simpa [interior_Ioi] using hn)
  have hEv : ∀ t : ℝ, t₀ ≤ t → 0 < h t := fun t ht => by
    have htpos : 0 < t := lt_of_lt_of_le ht₀_pos ht
    have hgpos : 0 < g t := hF_pos t ht
    have hdpos : 0 < d t := hΔre_pos t htpos
    have hdpowpos : 0 < (d t) ^ (-a) := Real.rpow_pos_of_pos hdpos (-a)
    simpa [h, g, d, mul_assoc] using mul_pos hgpos hdpowpos
  have hall : ∀ t : ℝ, 0 < t → 0 < h t :=
    StrictAntiOn.eventuallyPos_Ioi hAnti ht₀_pos hEv
  refine ⟨hF_real, fun t ht => ?_⟩
  have hdpos : 0 < d t := hΔre_pos t ht
  have hdpowpos : 0 < (d t) ^ (-a) := Real.rpow_pos_of_pos hdpos (-a)
  have : 0 < g t := by
    have htpos : 0 < h t := hall t ht
    exact pos_of_mul_pos_left htpos (le_of_lt hdpowpos)
  simpa [g] using this

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
  have habs : |w.im - z.im| ≤ z.im / 2 := calc |w.im - z.im|
    _ = |(w - z).im| := by simp [Complex.sub_im]
    _ ≤ dist w z := by simpa [dist_eq_norm] using (abs_im_le_norm (w - z))
    _ ≤ z.im / 2 := hdist
  have hlower : z.im / 2 ≤ w.im := by linarith [(abs_le.mp habs).1]
  exact lt_of_lt_of_le (by linarith [z.im_pos] : 0 < z.im / 2) hlower

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

lemma norm_D_le_div_pi_im_of_bounded {f : ℍ → ℂ}
    (hf : MDiff f) {M A : ℝ}
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
    have habs : |w.im - z.im| ≤ z.im / 2 := by
      calc |w.im - z.im| = |(w - z).im| := by simp [Complex.sub_im]
        _ ≤ dist w z := by simpa [dist_eq_norm] using (abs_im_le_norm (w - z))
        _ = z.im / 2 := hdist
    have hmax : max A 0 ≤ z.im / 2 := by linarith [hz]
    have hw_im_ge : z.im / 2 ≤ w.im := by
      have hlow := (abs_le.mp habs).1
      linarith
    have hw_im_ge_A : A ≤ w.im := le_trans (le_trans (le_max_left A 0) hmax) hw_im_ge
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
  have hDz : ‖D f z‖ ≤ M / (π * z.im) := norm_D_le_div_pi_im_of_bounded hf hMA hz
  have hz_im_ge_1 : 1 ≤ z.im := by linarith [le_max_right A 0, hz]
  have hM_nonneg : 0 ≤ M :=
    (norm_nonneg _).trans (hMA z (by linarith [le_max_left A 0, hz]))
  calc
    ‖D f z‖ ≤ M / (π * z.im) := hDz
    _ ≤ M / (π * 1) := by gcongr
    _ = M / π := by ring

/-- The D-derivative tends to 0 at infinity for bounded holomorphic functions. -/
public lemma D_isZeroAtImInfty_of_bounded {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) :
    IsZeroAtImInfty (D f) := by
  rw [UpperHalfPlane.isZeroAtImInfty_iff]
  intro ε hε
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hbdd
  obtain ⟨M, A, hMA⟩ := hbdd
  refine ⟨max (2 * max A 0 + 1) (M / (Real.pi * ε)), fun z hz => ?_⟩
  have hz' : 2 * max A 0 + 1 ≤ z.im := le_trans (le_max_left _ _) hz
  have hDz : ‖D f z‖ ≤ M / (π * z.im) := norm_D_le_div_pi_im_of_bounded hf hMA hz'
  have hz_im : M / (Real.pi * ε) ≤ z.im := le_trans (le_max_right _ _) hz
  have hpiε : 0 < (Real.pi * ε) := mul_pos Real.pi_pos hε
  have hpiIm : 0 < (Real.pi * z.im) := mul_pos Real.pi_pos z.im_pos
  have hMle : M ≤ ε * (Real.pi * z.im) := by
    have hMle' : M ≤ z.im * (Real.pi * ε) := (div_le_iff₀ hpiε).1 hz_im
    simpa [mul_assoc, mul_left_comm, mul_comm] using hMle'
  have hbound : M / (π * z.im) ≤ ε :=
    (div_le_iff₀ hpiIm).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hMle)
  exact hDz.trans hbound

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
    convert hconst.mul (E₂_isBoundedAtImInfty.mul hbdd) using 1
    ext z
    simp only [Pi.mul_apply]
    ring
  exact hD.sub hE₂f

/-- A level-1 modular form is invariant under slash action by any element of SL(2,ℤ). -/
lemma ModularForm.slash_eq_self {k : ℤ} (f : ModularForm (Gamma 1) k) (γ : SL(2, ℤ)) :
    (f : ℍ → ℂ) ∣[k] γ = f := by
  simpa using f.slash_action_eq' _ ⟨γ, mem_Gamma_one γ, rfl⟩

/-- The Serre derivative of a weight-k level-1 modular form is a weight-(k+2) modular form. -/
@[expose] public noncomputable def serre_D_ModularForm (k : ℤ) (f : ModularForm (Gamma 1) k) :
    ModularForm (Gamma 1) (k + 2) where
  toSlashInvariantForm := {
    toFun := serre_D k f
    slash_action_eq' := fun _ hγ => by
      obtain ⟨γ', -, rfl⟩ := Subgroup.mem_map.mp hγ
      simpa using serre_D_slash_invariant k f f.holo' γ' (f.slash_eq_self γ')
  }
  holo' := serre_D_differentiable f.holo'
  bdd_at_cusps' := fun hc => bounded_at_cusps_of_bounded_at_infty hc fun _ hA => by
    obtain ⟨A', rfl⟩ := MonoidHom.mem_range.mp hA
    exact (serre_D_slash_invariant k f f.holo' A' (f.slash_eq_self A')).symm ▸
      serre_D_isBoundedAtImInfty k f.holo' (ModularFormClass.bdd_at_infty f)

/-!
## Ramanujan formulas (level 1)

We prove the weight-`k` Ramanujan identities for `E₄` and `E₆` by:
- showing the Serre derivatives are (level 1) modular forms of weight `k+2`,
- choosing the scalar so that the constant term vanishes,
- concluding the difference is a cusp form of weight `< 12`, hence zero.

The `E₂` identity is handled separately (since `E₂` is not modular).
-/

section Ramanujan

open scoped MatrixGroups

private lemma tendsto_serre_D_of_bounded_tendsto_one {f : ℍ → ℂ} (k : ℂ)
     (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : IsBoundedAtImInfty f)
     (h1 : Tendsto f atImInfty (𝓝 (1 : ℂ))) :
     Tendsto (fun z : ℍ => serre_D k f z) atImInfty (𝓝 (-(k * 12⁻¹))) := by
  have hD : Tendsto (fun z : ℍ => D f z) atImInfty (𝓝 (0 : ℂ)) :=
    D_isZeroAtImInfty_of_bounded hf hbdd
  have hE₂ : Tendsto E₂ atImInfty (𝓝 (1 : ℂ)) := tendsto_E₂_atImInfty
  have hconst : Tendsto (fun _ : ℍ => k * 12⁻¹) atImInfty (𝓝 (k * 12⁻¹)) :=
    tendsto_const_nhds
  have hterm :
      Tendsto (fun z : ℍ => k * 12⁻¹ * E₂ z * f z) atImInfty (𝓝 (k * 12⁻¹)) := by
    simpa [mul_assoc, mul_one, one_mul] using (hconst.mul hE₂).mul h1
  simpa [serre_D, mul_assoc] using (hD.sub hterm)

private lemma tendsto_E₄_atImInfty : Tendsto (fun z : ℍ => E₄ z) atImInfty (𝓝 (1 : ℂ)) := by
  simpa using (SpherePacking.ModularForms.tendsto_E₄_atImInfty :
    Tendsto (fun z : ℍ => E₄ z) atImInfty (𝓝 (1 : ℂ)))

private lemma tendsto_E₆_atImInfty : Tendsto (fun z : ℍ => E₆ z) atImInfty (𝓝 (1 : ℂ)) := by
  simpa using (SpherePacking.ModularForms.tendsto_E₆_atImInfty :
    Tendsto (fun z : ℍ => E₆ z) atImInfty (𝓝 (1 : ℂ)))

lemma tendsto_serre_D_E₄_atImInfty :
    Tendsto (fun z : ℍ => serre_D 4 E₄.toFun z) atImInfty (𝓝 (-(3⁻¹ : ℂ))) := by
  have hmain :
      Tendsto (fun z : ℍ => serre_D 4 E₄.toFun z) atImInfty (𝓝 (-( (4 : ℂ) * 12⁻¹))) :=
    tendsto_serre_D_of_bounded_tendsto_one (k := (4 : ℂ))
      (f := E₄.toFun) E₄.holo' (ModularFormClass.bdd_at_infty E₄)
      (by simpa using tendsto_E₄_atImInfty)
  have hconst : ((4 : ℂ) * 12⁻¹) = (3⁻¹ : ℂ) := by norm_num
  simpa [hconst] using hmain

lemma tendsto_serre_D_E₆_atImInfty :
    Tendsto (fun z : ℍ => serre_D 6 E₆.toFun z) atImInfty (𝓝 (-(2⁻¹ : ℂ))) := by
  have hmain :
      Tendsto (fun z : ℍ => serre_D 6 E₆.toFun z) atImInfty (𝓝 (-( (6 : ℂ) * 12⁻¹))) :=
    tendsto_serre_D_of_bounded_tendsto_one (k := (6 : ℂ))
      (f := E₆.toFun) E₆.holo' (ModularFormClass.bdd_at_infty E₆)
      (by simpa using tendsto_E₆_atImInfty)
  have hconst : ((6 : ℂ) * 12⁻¹) = (2⁻¹ : ℂ) := by norm_num
  simpa [hconst] using hmain

noncomputable def serreD_modularForm (k : ℤ) (F : ModularForm Γ(1) k) :
    ModularForm Γ(1) (k + 2) :=
  { toFun := serre_D k F.toFun
    slash_action_eq' := by
      intro γ hγ
      rcases (Subgroup.mem_map.1 hγ) with ⟨γ', hγ', rfl⟩
      have hγ'GL :
          (γ' : GL (Fin 2) ℝ) ∈ (Γ(1) : Subgroup (GL (Fin 2) ℝ)) :=
        ⟨γ', hγ', rfl⟩
      have hF : F.toFun ∣[(k : ℤ)] γ' = F.toFun := by
        have hFGL := F.slash_action_eq' (γ' : GL (Fin 2) ℝ) hγ'GL
        simpa [ModularForm.SL_slash] using hFGL
      have hSerre := serre_D_slash_invariant k F.toFun F.holo' γ' hF
      simpa [ModularForm.SL_slash] using hSerre
    holo' := serre_D_differentiable (k := (k : ℂ)) F.holo'
    bdd_at_cusps' := by
      intro c hc
      have hbdd : IsBoundedAtImInfty (serre_D k F.toFun) :=
        serre_D_isBoundedAtImInfty (k := (k : ℂ)) F.holo' (ModularFormClass.bdd_at_infty F)
      refine bounded_at_cusps_of_bounded_at_infty
        (f := serre_D k F.toFun) (k := (k + 2 : ℤ)) hc ?_
      intro A hA
      rcases hA with ⟨γ, rfl⟩
      have hγmem : (γ : GL (Fin 2) ℝ) ∈ (Γ(1) : Subgroup (GL (Fin 2) ℝ)) :=
        ⟨γ, CongruenceSubgroup.mem_Gamma_one γ, rfl⟩
      have hF : F.toFun ∣[(k : ℤ)] γ = F.toFun := by
        have hFGL := F.slash_action_eq' (γ : GL (Fin 2) ℝ) hγmem
        simpa [ModularForm.SL_slash] using hFGL
      have hSerre : serre_D k F.toFun ∣[(k + 2 : ℤ)] γ = serre_D k F.toFun :=
        serre_D_slash_invariant k F.toFun F.holo' γ hF
      have hSerreGL :
          serre_D k F.toFun ∣[(k + 2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ) =
            serre_D k F.toFun := by
        calc
          serre_D k F.toFun ∣[(k + 2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ) =
              serre_D k F.toFun ∣[(k + 2 : ℤ)] γ := by
                simpa using
                  (ModularForm.SL_slash (f := serre_D k F.toFun) (k := (k + 2 : ℤ)) γ).symm
          _ = serre_D k F.toFun := hSerre
      rw [hSerreGL]
      exact hbdd }

lemma eq_zero_of_tendsto_zero_atImInfty {k : ℤ} (hk : k < 12) (G : ModularForm Γ(1) k)
    (hGlim : Tendsto (fun z : ℍ => G z) atImInfty (𝓝 (0 : ℂ))) : G = 0 := by
  refine IsCuspForm_weight_lt_eq_zero k hk G <|
    (IsCuspForm_iff_coeffZero_eq_zero k G).2 ?_
  have hGval : UpperHalfPlane.valueAtInfty (G : ℍ → ℂ) = 0 :=
    UpperHalfPlane.IsZeroAtImInfty.valueAtInfty_eq_zero (f := (G : ℍ → ℂ)) hGlim
  have hq :
      (qExpansion (1 : ℝ) G).coeff 0 = UpperHalfPlane.valueAtInfty (G : ℍ → ℂ) :=
    qExpansion_coeff_zero (f := G) (h := (1 : ℝ)) (by positivity) (by simp)
  simp [hq, hGval]

/--
Serre derivative of Eisenstein series. We compare constant terms via the limit at infinity,
then use the fact that there are no nonzero level-one cusp forms of weight `< 12`.
-/
public theorem ramanujan_E₂' : serre_D 1 E₂ = - 12⁻¹ * E₄.toFun := by
  let corr : SL(2, ℤ) → ℍ → ℂ := fun γ z =>
    (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z)
  have hcorr_holo (γ : SL(2, ℤ)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (corr γ) := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    -- Reduce to a holomorphic rational function on `{z : ℂ | 0 < z.im}`.
    have hG :
        DifferentiableOn ℂ
          (fun z : ℂ => (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z))
          {z : ℂ | 0 < z.im} := by
      intro z hz
      have hz0 : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ ⟨z, hz⟩
      have hdenom : DifferentiableAt ℂ (fun w : ℂ => denom γ w) z := by
        simpa using (differentiableAt_denom (γ := γ) z)
      have hdiv : DifferentiableAt ℂ (fun w : ℂ => (γ 1 0 : ℂ) / denom γ w) z :=
        (differentiableAt_const _).div hdenom hz0
      exact (hdiv.const_mul ((12 : ℂ) * (2 * π * I)⁻¹)).differentiableWithinAt
    refine hG.congr ?_
    intro z hz
    simp [corr, Function.comp_apply, ofComplex_apply_of_im_pos hz]
  have hcorr_D (γ : SL(2, ℤ)) :
      D (corr γ) = - 12⁻¹ * (corr γ) * (corr γ) := by
    funext z
    -- Compute via the complex derivative of the rational function `c / (cz + d)`.
    have h_eq :
        ((corr γ) ∘ ofComplex) =ᶠ[nhds (z : ℂ)]
          (fun w : ℂ => (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ w)) := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.2] with w hw
      simp [corr, Function.comp_apply, ofComplex_apply_of_im_pos hw]
    have hz0 : denom γ (z : ℂ) ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
    have hderiv_div :
        deriv (fun w : ℂ => (γ 1 0 : ℂ) / denom γ w) (z : ℂ) =
          -((γ 1 0 : ℂ) * (γ 1 0 : ℂ)) / (denom γ (z : ℂ)) ^ 2 := by
      rw [deriv_fun_div (differentiableAt_const _)
        (differentiableAt_denom (γ := γ) (z : ℂ)) hz0]
      simp [deriv_denom (γ := γ) (z := (z : ℂ))]
    -- Now rewrite `D` using `h_eq` and compute directly.
    simp only [D, neg_mul, Pi.mul_apply, Pi.neg_apply, Pi.inv_apply, Pi.ofNat_apply]
    rw [h_eq.deriv_eq]
    have htwoPiI : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
    -- `D` applies an extra factor `(2πi)⁻¹`; `corr` itself already contains `(2πi)⁻¹`.
    simp [mul_assoc, mul_left_comm, mul_comm, hderiv_div]
    dsimp [corr]
    field_simp [htwoPiI, hz0]
    ring_nf
    simp
  have hE₂slash (γ : SL(2, ℤ)) :
      (E₂ ∣[(2 : ℤ)] γ) = E₂ + corr γ := by
    simpa [corr] using (E₂_slash γ)
  have hDE₂_slash (γ : SL(2, ℤ)) :
      D E₂ ∣[(4 : ℤ)] γ =
        D E₂
          + (6⁻¹ : ℂ) • (E₂ * corr γ)
          + (12⁻¹ : ℂ) • (corr γ * corr γ) := by
    have hDslash := D_slash (k := (2 : ℤ)) (F := E₂) E₂_holo' γ
    ext z
    have hD := congrFun hDslash z
    have hE := congrFun (hE₂slash γ) z
    have hcorr_h := hcorr_holo γ
    let anom : ℂ :=
      (2 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (E₂ ∣[(2 : ℤ)] γ) z
    have hsolve : (D E₂ ∣[(4 : ℤ)] γ) z = D (E₂ ∣[(2 : ℤ)] γ) z + anom := by
      have h0 : D (E₂ ∣[(2 : ℤ)] γ) z = (D E₂ ∣[(4 : ℤ)] γ) z - anom := by
        simpa [anom, Pi.sub_apply, Pi.mul_apply] using hD
      exact (sub_eq_iff_eq_add).1 h0.symm
    have hDadd : D (E₂ ∣[(2 : ℤ)] γ) z = (D E₂ + D (corr γ)) z := by
      rw [hE₂slash]
      simp [D_add _ _ E₂_holo' hcorr_h]
    have hcorrD : D (corr γ) z = (-12⁻¹ : ℂ) * (corr γ z * corr γ z) := by
      simpa [Pi.mul_apply, Pi.neg_apply, mul_assoc] using congrFun (hcorr_D γ) z
    have hA :
        (2 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) =
          (6⁻¹ : ℂ) * corr γ z := by
      dsimp [corr]
      have h12 : (12 : ℂ) ≠ 0 := by norm_num
      field_simp [h12]
      ring
    have hEeval : (E₂ ∣[(2 : ℤ)] γ) z = E₂ z + corr γ z := by
      simpa [Pi.add_apply] using hE
    have hanom : anom = (6⁻¹ : ℂ) * corr γ z * (E₂ z + corr γ z) := by
      -- rewrite the slashed `E₂` and then use `hA` for the prefactor
      dsimp [anom]
      rw [hEeval]
      have hA' := congrArg (fun t => t * (E₂ z + corr γ z)) hA
      simpa [mul_assoc] using hA'
    rw [hsolve, hDadd]
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    -- `D(corr) = -(1/12)·corr²`, and `anom = (1/6)·corr·(E₂+corr)`.
    rw [hcorrD, hanom]
    simp [mul_add, mul_left_comm, mul_comm]
    ring_nf
  have hSerre_slash (γ : SL(2, ℤ)) :
      serre_D 1 E₂ ∣[(4 : ℤ)] γ = serre_D 1 E₂ := by
    ext z
    -- Expand the slash, then rewrite `D E₂` and `E₂` under slash.
    have hE := congrFun (hE₂slash γ) z
    have hD := congrFun (hDE₂_slash γ) z
    -- `E₂(γ·z)` term in the square simplifies via the weight-2 slash.
    have hE_sq :
        (E₂ (γ • z)) ^ (2 : ℕ) * (denom γ z) ^ (-(4 : ℤ)) =
          (E₂ z + corr γ z) ^ (2 : ℕ) := by
      -- Rewrite the transformation law `E₂ ∣[2] γ = E₂ + corr γ` at `z`.
      have hmain : E₂ (γ • z) * (denom γ z) ^ (-(2 : ℤ)) = E₂ z + corr γ z := by
        simpa [ModularForm.SL_slash_apply (f := E₂) (k := (2 : ℤ)) γ z, Pi.add_apply] using hE
      have hden :
          ((denom γ z) ^ (-(2 : ℤ))) ^ (2 : ℕ) = (denom γ z) ^ (-(4 : ℤ)) := by
        calc
          ((denom γ z) ^ (-(2 : ℤ))) ^ (2 : ℕ)
              = ((denom γ z) ^ (-(2 : ℤ))) ^ ((2 : ℤ)) := by
                  simpa using (zpow_natCast ((denom γ z) ^ (-(2 : ℤ))) 2).symm
          _ = (denom γ z) ^ (-(2 : ℤ) * (2 : ℤ)) := by
                  simpa using (zpow_mul (denom γ z) (-(2 : ℤ)) (2 : ℤ)).symm
          _ = (denom γ z) ^ (-(4 : ℤ)) := by norm_num
      have hpow :
          (E₂ (γ • z) * (denom γ z) ^ (-(2 : ℤ))) ^ (2 : ℕ) =
            (E₂ z + corr γ z) ^ (2 : ℕ) := by
        simpa using congrArg (fun w : ℂ => w ^ (2 : ℕ)) hmain
      have hpow' := hpow
      rw [mul_pow] at hpow'
      rw [hden] at hpow'
      exact hpow'
    -- Now compute `serre_D 1 E₂` under slash.
    -- `(serre_D 1 E₂ ∣[4] γ) z = (denom γ z)^(-4) * serre_D 1 E₂(γ•z)`.
    simp only [serre_D, SL_slash_apply, Pi.add_apply] at *
    -- Use the explicit slash formulas for `D E₂` and `E₂`.
    -- For `D E₂`: use `hD` (already evaluated at `z`).
    -- For `E₂(γ•z)`: use the rewritten square identity `hE_sq`.
    -- Everything cancels by expanding the square.
    -- First, rewrite the `D E₂` term.
    -- `hD` is about `(D E₂ ∣[4] γ) z`.
    -- Replace it by `D E₂ (γ•z) * (denom γ z)^(-4)`.
    have hD' :
        D E₂ (γ • z) * (denom γ z) ^ (-(4 : ℤ)) =
          D E₂ z +
            (6⁻¹ : ℂ) * (E₂ z * corr γ z) +
            (12⁻¹ : ℂ) * (corr γ z * corr γ z) := by
      simpa [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] using hD
    have hEexp :
        E₂ (γ • z) * E₂ (γ • z) * (denom γ z) ^ (-(4 : ℤ)) =
          (E₂ z + corr γ z) ^ (2 : ℕ) := by
      simpa [pow_two, mul_assoc] using hE_sq
    -- Expand the product by the weight factor, then rewrite using `hDexp` and `hEexp`.
    rw [sub_mul]
    rw [hD']
    have hb :
        (1 * 12⁻¹ * E₂ (γ • z) * E₂ (γ • z)) * (denom γ z) ^ (-(4 : ℤ)) =
          (12⁻¹ : ℂ) * (E₂ (γ • z) * E₂ (γ • z) * (denom γ z) ^ (-(4 : ℤ))) := by
      ring_nf
    rw [hb]
    rw [hEexp]
    ring_nf
  -- Package `serre_D 1 E₂` as a weight-4 level-1 modular form.
  let F₄ : ModularForm Γ(1) 4 :=
    { toFun := serre_D 1 E₂
      slash_action_eq' := by
        intro γ hγ
        rcases (Subgroup.mem_map.1 hγ) with ⟨γ', hγ', rfl⟩
        have hSerre := hSerre_slash γ'
        simpa [ModularForm.SL_slash] using hSerre
      holo' := serre_D_differentiable (k := (1 : ℂ)) E₂_holo'
      bdd_at_cusps' := by
        intro c hc
        -- Bounded at infinity: both terms in `serre_D` are bounded.
        have hbdd : IsBoundedAtImInfty (serre_D 1 E₂) :=
          serre_D_isBoundedAtImInfty (k := (1 : ℂ)) E₂_holo' E₂_isBoundedAtImInfty
        refine bounded_at_cusps_of_bounded_at_infty
          (f := serre_D 1 E₂) (k := (4 : ℤ)) hc ?_
        intro A hA
        rcases hA with ⟨γ, rfl⟩
        have hcast :
            serre_D 1 E₂ ∣[(4 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ) =
              serre_D 1 E₂ ∣[(4 : ℤ)] γ := by
          simpa using (ModularForm.SL_slash (f := serre_D 1 E₂) (k := (4 : ℤ)) γ).symm
        have hSerreSL : serre_D 1 E₂ ∣[(4 : ℤ)] γ = serre_D 1 E₂ := hSerre_slash γ
        have hSerreGL :
            serre_D 1 E₂ ∣[(4 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ) =
              serre_D 1 E₂ := by
          simpa [hcast] using hSerreSL
        rw [hSerreGL]
        exact hbdd }
  -- Identify `F₄` by its constant term at infinity: it is `-(1/12)·E₄`.
  let G : ModularForm Γ(1) 4 := F₄ + (12⁻¹ : ℂ) • E₄
  have hbddE₂ : IsBoundedAtImInfty E₂ := E₂_isBoundedAtImInfty
  have hDlim : Tendsto (fun z : ℍ => D E₂ z) atImInfty (𝓝 (0 : ℂ)) :=
    D_isZeroAtImInfty_of_bounded E₂_holo' hbddE₂
  have hE₂lim : Tendsto E₂ atImInfty (𝓝 (1 : ℂ)) := tendsto_E₂_atImInfty
  have hF₄lim : Tendsto (fun z : ℍ => F₄ z) atImInfty (𝓝 (-(12⁻¹ : ℂ))) := by
    -- `F₄ = D E₂ - (1/12) E₂^2`.
    have hterm :
        Tendsto (fun z => 12⁻¹ * E₂ z * E₂ z) atImInfty (𝓝 (12⁻¹ : ℂ)) := by
      have hE₂' :
          Tendsto (fun z => (12⁻¹ : ℂ) * E₂ z) atImInfty (𝓝 (12⁻¹ : ℂ)) := by
        simpa [mul_one] using (tendsto_const_nhds.mul hE₂lim)
      simpa [mul_assoc, mul_one] using (hE₂'.mul hE₂lim)
    have hmain :
        Tendsto (fun z : ℍ => serre_D 1 E₂ z) atImInfty (𝓝 (-(12⁻¹ : ℂ))) := by
      simpa [serre_D, mul_assoc, mul_one] using (hDlim.sub hterm)
    have : Tendsto (fun z : ℍ => F₄.toFun z) atImInfty (𝓝 (-(12⁻¹ : ℂ))) := by
      simpa [F₄] using hmain
    simpa using this
  have hGlim : Tendsto (fun z : ℍ => G z) atImInfty (𝓝 (0 : ℂ)) := by
    have hE₄lim :
        Tendsto (fun z : ℍ => (12⁻¹ : ℂ) * E₄ z) atImInfty
          (𝓝 ((12⁻¹ : ℂ) * (1 : ℂ))) :=
      by
        simpa [mul_one] using (tendsto_const_nhds.mul tendsto_E₄_atImInfty)
    have hsum := hF₄lim.add hE₄lim
    simpa [G, mul_one] using hsum
  have hG0 : G = 0 := eq_zero_of_tendsto_zero_atImInfty (k := 4) (by norm_num) G hGlim
  funext z
  have hz : F₄ z + (12⁻¹ : ℂ) * E₄ z = 0 := by
    simpa [G] using congrArg (fun f : ModularForm Γ(1) 4 => f z) hG0
  have hz' : F₄ z = (-12⁻¹ : ℂ) * E₄ z := by
    have : F₄ z = -((12⁻¹ : ℂ) * E₄ z) := (eq_neg_iff_add_eq_zero).2 (by simpa using hz)
    simpa [neg_mul] using this
  have hz'' : F₄.toFun z = (-12⁻¹ : ℂ) * E₄ z := by
    simpa [ModularForm.toFun_eq_coe] using hz'
  simpa [F₄, mul_assoc] using hz''

public theorem ramanujan_E₄' : serre_D 4 E₄.toFun = - 3⁻¹ * E₆.toFun := by
  let F₆ : ModularForm Γ(1) 6 := serreD_modularForm 4 E₄
  let G : ModularForm Γ(1) 6 := F₆ + (3⁻¹ : ℂ) • E₆
  have hGlim : Tendsto (fun z : ℍ => G z) atImInfty (𝓝 (0 : ℂ)) := by
    have hF : Tendsto (fun z : ℍ => F₆ z) atImInfty (𝓝 (-(3⁻¹ : ℂ))) := by
      simpa [F₆, serreD_modularForm] using tendsto_serre_D_E₄_atImInfty
    have hE6 :
        Tendsto (fun z : ℍ => (3⁻¹ : ℂ) * E₆ z) atImInfty
          (𝓝 ((3⁻¹ : ℂ) * (1 : ℂ))) :=
      by
        simpa [mul_one] using (tendsto_const_nhds.mul tendsto_E₆_atImInfty)
    simpa [G, mul_one] using hF.add hE6
  have hG0 : G = 0 := eq_zero_of_tendsto_zero_atImInfty (k := (6 : ℤ)) (by norm_num) G hGlim
  funext z
  have hz : F₆ z + (3⁻¹ : ℂ) * E₆ z = 0 := by
    simpa [G] using congrArg (fun f : ModularForm Γ(1) 6 => f z) hG0
  have hz' : F₆ z = -((3⁻¹ : ℂ) * E₆ z) :=
    (eq_neg_iff_add_eq_zero).2 (by simpa using hz)
  have hz'' : F₆.toFun z = -((3⁻¹ : ℂ) * E₆ z) := by
    simpa [ModularForm.toFun_eq_coe] using hz'
  simpa [F₆, serreD_modularForm, neg_mul, mul_assoc] using hz''

public theorem ramanujan_E₆' : serre_D 6 E₆.toFun = - 2⁻¹ * E₄.toFun * E₄.toFun := by
  let F₈ : ModularForm Γ(1) 8 := serreD_modularForm 6 E₆
  let E4sq : ModularForm Γ(1) 8 := E₄.mul E₄
  let G : ModularForm Γ(1) 8 := F₈ + (2⁻¹ : ℂ) • E4sq
  have hGlim : Tendsto (fun z : ℍ => G z) atImInfty (𝓝 (0 : ℂ)) := by
    have hF : Tendsto (fun z : ℍ => F₈ z) atImInfty (𝓝 (-(2⁻¹ : ℂ))) := by
      simpa [F₈, serreD_modularForm] using tendsto_serre_D_E₆_atImInfty
    have hE4 : Tendsto (fun z : ℍ => E₄ z) atImInfty (𝓝 (1 : ℂ)) :=
      tendsto_E₄_atImInfty
    have hE4sq :
        Tendsto (fun z : ℍ => E4sq z) atImInfty (𝓝 ((1 : ℂ) * (1 : ℂ))) := by
      simpa [E4sq] using hE4.mul hE4
    have hE4sq' :
        Tendsto (fun z : ℍ =>
          (2⁻¹ : ℂ) * E4sq z) atImInfty (𝓝 ((2⁻¹ : ℂ) * ((1 : ℂ) * (1 : ℂ)))) :=
      tendsto_const_nhds.mul hE4sq
    simpa [G, mul_one] using hF.add hE4sq'
  have hG0 : G = 0 := eq_zero_of_tendsto_zero_atImInfty (k := (8 : ℤ)) (by norm_num) G hGlim
  funext z
  have hz : F₈ z + (2⁻¹ : ℂ) * E4sq z = 0 := by
    simpa [G] using congrArg (fun f : ModularForm Γ(1) 8 => f z) hG0
  have hz' : F₈ z = -((2⁻¹ : ℂ) * E4sq z) :=
    (eq_neg_iff_add_eq_zero).2 (by simpa using hz)
  have hz'' : F₈.toFun z = -((2⁻¹ : ℂ) * E4sq z) := by
    simpa [ModularForm.toFun_eq_coe] using hz'
  simpa [F₈, serreD_modularForm, E4sq, neg_mul, mul_assoc, mul_left_comm, mul_comm] using hz''

/-- Ramanujan's differential equation for `E₂`. -/
@[simp]
public theorem ramanujan_E₂ : D E₂ = 12⁻¹ * (E₂ * E₂ - E₄.toFun) := by
  ext z
  have h := ramanujan_E₂'
  unfold serre_D at h
  have h1 := congrFun h z
  simp [field]
  field_simp at h1
  simpa [add_comm, sub_eq_iff_eq_add] using h1

/-- Ramanujan's differential equation for `E₄`. -/
@[simp]
public theorem ramanujan_E₄ : D E₄.toFun = 3⁻¹ * (E₂ * E₄.toFun - E₆.toFun) := by
  ext z
  have h := congrFun ramanujan_E₄' z
  have h' : D E₄.toFun z = (-(3⁻¹ : ℂ) * E₆ z) + (4 : ℂ) * 12⁻¹ * E₂ z * E₄ z :=
    (sub_eq_iff_eq_add).1 (by simpa [serre_D, mul_assoc, mul_left_comm, mul_comm] using h)
  have hconst : ((4 : ℂ) * 12⁻¹) = (3⁻¹ : ℂ) := by norm_num1
  rw [h']
  simp [hconst, sub_eq_add_neg]
  ring_nf

/-- Ramanujan's differential equation for `E₆`. -/
@[simp]
public theorem ramanujan_E₆ :
    D E₆.toFun = 2⁻¹ * (E₂ * E₆.toFun - E₄.toFun * E₄.toFun) := by
  ext z
  have h := congrFun ramanujan_E₆' z
  have h' :
      D E₆.toFun z =
        (-(2⁻¹ : ℂ) * (E₄ z * E₄ z)) + (6 : ℂ) * 12⁻¹ * E₂ z * E₆ z :=
    (sub_eq_iff_eq_add).1 (by simpa [serre_D, mul_assoc, mul_left_comm, mul_comm] using h)
  have hconst : ((6 : ℂ) * 12⁻¹) = (2⁻¹ : ℂ) := by norm_num1
  rw [h']
  simp [hconst, sub_eq_add_neg]
  ring_nf

end Ramanujan
