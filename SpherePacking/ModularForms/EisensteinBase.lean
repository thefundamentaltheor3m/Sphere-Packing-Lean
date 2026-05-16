module
public import SpherePacking.ModularForms.E2
public import SpherePacking.ModularForms.EisensteinQExpansions
public import SpherePacking.ModularForms.IsCuspForm
public import SpherePacking.ModularForms.QExpansionLemmas
public import SpherePacking.ModularForms.SummableLemmas.Basic
public import SpherePacking.ModularForms.SummableLemmas.QExpansion
import SpherePacking.Tactic.NormNumI


/-!
# Level-one Eisenstein series and auxiliary ratios

This file packages the level-one Eisenstein series `E₄` and `E₆`, defines the auxiliary ratios
`φ₀`, `φ₂'`, `φ₄'` (and their extensions to `ℂ`), and proves the basic `q`-expansion and
imaginary-axis lemmas needed later in the sphere packing argument.
-/
open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
open scoped ArithmeticFunction.sigma

open ModularForm hiding E₄ E₆
open EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex Real MatrixGroups

noncomputable section

section Definitions

/-! ## Level-one Eisenstein series -/

/-- The normalized level-one Eisenstein series of weight `4` as a modular form. -/
@[expose] public def E₄ : ModularForm (CongruenceSubgroup.Gamma ↑1) 4 :=
  (1/2 : ℂ) • eisensteinSeriesMF (by decide) standardcongruencecondition -- normalization

/-- The normalized level-one Eisenstein series of weight `6` as a modular form. -/
@[expose] public def E₆ : ModularForm (CongruenceSubgroup.Gamma ↑1) 6 :=
  (1/2 : ℂ) • eisensteinSeriesMF (by decide) standardcongruencecondition

/-- `E₄` is definitionally the Eisenstein series `E 4`. -/
public lemma E4_eq : E₄ = E 4 (by decide) := rfl

/-- `E₆` is definitionally the Eisenstein series `E 6`. -/
public lemma E6_eq : E₆ = E 6 (by decide) := rfl

/-- Evaluation of `E₄` agrees with `E 4` pointwise. -/
@[simp] public lemma E4_apply (z : ℍ) : E₄ z = E 4 (by decide) z := rfl

/-- Evaluation of `E₆` agrees with `E 6` pointwise. -/
@[simp] public lemma E6_apply (z : ℍ) : E₆ z = E 6 (by decide) z := rfl

/-- E₄ is 1-periodic: E₄(z + 1) = E₄(z). This follows from E₄ being a modular form for Γ(1). -/
public lemma E₄_periodic (z : ℍ) : E₄ ((1 : ℝ) +ᵥ z) = E₄ z :=
  by simpa using SlashInvariantForm.vAdd_width_periodic 1 4 1 E₄.toSlashInvariantForm z

/-- E₆ is 1-periodic: E₆(z + 1) = E₆(z). This follows from E₆ being a modular form for Γ(1). -/
public lemma E₆_periodic (z : ℍ) : E₆ ((1 : ℝ) +ᵥ z) = E₆ z :=
  by simpa using SlashInvariantForm.vAdd_width_periodic 1 6 1 E₆.toSlashInvariantForm z

/-- E₄ transforms under S as: E₄(-1/z) = z⁴ · E₄(z) -/
private lemma ModularForm.S_transform_of_level_one (m : ℕ)
    (F : ModularForm (CongruenceSubgroup.Gamma ↑1) (m : ℤ)) (z : ℍ) :
    F (ModularGroup.S • z) = z ^ m * F z := by
  have h : (F.toFun ∣[(m : ℤ)] ModularGroup.S) z = F.toFun z := by
    simpa using congrFun (by
      apply F.slash_action_eq'
      simp only [Subgroup.mem_map, CongruenceSubgroup.mem_Gamma_one]
      use ModularGroup.S) z
  simp [SL_slash_apply, ModularGroup.denom_S, zpow_neg] at h
  field_simp [ne_zero z] at h
  exact h

/-- The `S`-transformation formula for `E₄`. -/
public lemma E₄_S_transform (z : ℍ) : E₄ (ModularGroup.S • z) = z ^ (4 : ℕ) * E₄ z := by
  simpa using (ModularForm.S_transform_of_level_one 4 E₄ z)

/-- E₆ transforms under S as: E₆(-1/z) = z⁶ · E₆(z) -/
public lemma E₆_S_transform (z : ℍ) : E₆ (ModularGroup.S • z) = z ^ (6 : ℕ) * E₆ z := by
  simpa using (ModularForm.S_transform_of_level_one 6 E₆ z)

variable (f : ℍ → ℂ) (k : ℤ) (z : ℍ)

end Definitions

/-! ## Auxiliary ratios `φ` -/

/-- The ratio `φ₀ = (E₂ * E₄ - E₆)^2 / Δ` on `ℍ`. -/
@[expose] public def φ₀ (z : ℍ) := (((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) / (Δ z)

/-- The ratio `φ₂' = E₄ * (E₂ * E₄ - E₆) / Δ` on `ℍ`. -/
@[expose] public def φ₂' (z : ℍ) := (E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)

/-- The ratio `φ₄' = E₄^2 / Δ` on `ℍ`. -/
@[expose] public def φ₄' (z : ℍ) := ((E₄ z) ^ 2) / (Δ z)

/-- Extend `φ₀` to a function `ℂ → ℂ` by setting it to `0` outside the upper half-plane. -/
@[expose] public def φ₀'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₀ ⟨z, hz⟩ else 0

/-- Extend `φ₂'` to a function `ℂ → ℂ` by setting it to `0` outside the upper half-plane. -/
@[expose] public def φ₂'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₂' ⟨z, hz⟩ else 0

/-- Extend `φ₄'` to a function `ℂ → ℂ` by setting it to `0` outside the upper half-plane. -/
@[expose] public def φ₄'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₄' ⟨z, hz⟩ else 0

/-- Unfold `φ₀''` on the upper half-plane. -/
@[simp] public lemma φ₀''_def {z : ℂ} (hz : 0 < z.im) : φ₀'' z = φ₀ ⟨z, hz⟩ := by
  simp [φ₀'', hz]

/-- Unfold `φ₀''` when `z` is in `upperHalfPlaneSet`. -/
@[simp] public lemma φ₀''_mem_upperHalfPlane {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    φ₀'' z = φ₀ ⟨z, hz⟩ :=
  φ₀''_def hz

/-- Unfold `φ₀''` on an upper-half-plane point `z : ℍ`. -/
@[simp] public lemma φ₀''_coe_upperHalfPlane (z : ℍ) : φ₀'' (z : ℂ) = φ₀ z := by
  simp [φ₀'', UpperHalfPlane.im_pos z]

open SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

open scoped Real MatrixGroups CongruenceSubgroup

local notation "𝕢" => Periodic.qParam

/-- A crude upper bound on the divisor sum `σ k n`. -/
public lemma sigma_bound (k n : ℕ) : σ k n ≤ n ^ (k + 1) :=
  ArithmeticFunction.sigma_le_pow_succ k n

/-- Explicit `q`-coefficients for `E₄`. -/
public lemma E4_q_exp : (fun m ↦ (qExpansion 1 E₄).coeff m) =
    fun m ↦ if m = 0 then 1 else (240 : ℂ) * (σ 3 m) := by
  funext m
  have h := EisensteinSeries.E_qExpansion_coeff (k := 4) (by norm_num) (by decide) m
  rw [show (qExpansion 1 ((ModularForm.E (show 3 ≤ 4 by norm_num)) : ℍ → ℂ)).coeff m =
      (qExpansion 1 (E₄ : ℍ → ℂ)).coeff m from rfl] at h
  rw [h]
  by_cases hm : m = 0
  · simp [hm]
  · simp only [hm, ↓reduceIte, Nat.cast_ofNat]
    have hb : bernoulli 4 = (-1/30 : ℚ) := by decide +kernel
    push_cast [hb]; ring

/-- The constant `q`-coefficient of `E₄` is `1`. -/
public lemma E4_q_exp_zero : (qExpansion 1 E₄).coeff 0 = 1 :=
  EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) (by decide)

/-- Explicit `q`-coefficients for `E₆`. -/
public lemma E6_q_exp : (fun m ↦ (qExpansion 1 E₆).coeff m) =
    fun m ↦ if m = 0 then 1 else -(504 : ℂ) * (σ 5 m) := by
  funext m
  have h := EisensteinSeries.E_qExpansion_coeff (k := 6) (by norm_num) (by decide) m
  rw [show (qExpansion 1 ((ModularForm.E (show 3 ≤ 6 by norm_num)) : ℍ → ℂ)).coeff m =
      (qExpansion 1 (E₆ : ℍ → ℂ)).coeff m from rfl] at h
  rw [h]
  by_cases hm : m = 0
  · simp [hm]
  · simp only [hm, ↓reduceIte, Nat.cast_ofNat]
    have hb : bernoulli 6 = (1/42 : ℚ) := by decide +kernel
    push_cast [hb]; ring

/-- The constant `q`-coefficient of `E₆` is `1`. -/
public lemma E6_q_exp_zero : (qExpansion 1 E₆).coeff 0 = 1 :=
  EisensteinSeries.E_qExpansion_coeff_zero (k := 6) (by norm_num) (by decide)

/-- The constant coefficient of `(1/1728) * (E₄^3 - E₆^2)` vanishes, hence it is a cusp form. -/
public theorem E4E6_coeff_zero_eq_zero :
  (PowerSeries.coeff 0)
      (qExpansion 1
        ((1 / 1728 : ℂ) • ((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3 - (DirectSum.of (ModularForm
          Γ(1)) 6) E₆ ^ 2) 12)) =
    0 := by
  simp only [one_div, DirectSum.sub_apply]
  rw [← Nat.cast_one (R := ℝ), ← qExpansion_smul2, Nat.cast_one (R := ℝ)]
  rw [coe_sub]
  rw [qExpansion_sub1]
  simp only [map_smul, map_sub, smul_eq_mul,
    mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
  have hds : (((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3) 12) = E₄.mul (E₄.mul E₄) := by
    ext z; rw [pow_three, @DirectSum.of_mul_of, DirectSum.of_mul_of]; rfl
  have hd6 : ((DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12 = E₆.mul E₆ := by
    ext z; rw [pow_two, @DirectSum.of_mul_of]; rfl
  rw [hds, hd6]
  have he4 : qExpansion (1 : ℝ) (E₄.mul (E₄.mul E₄)) =
      qExpansion (1 : ℝ) E₄ * (qExpansion (1 : ℝ) E₄ * qExpansion (1 : ℝ) E₄) := by
    rw [(by simpa using qExpansion_mul_coeff (n := 1) 4 8 E₄ (E₄.mul E₄) :
      qExpansion (1 : ℝ) (E₄.mul (E₄.mul E₄)) =
        qExpansion (1 : ℝ) E₄ * qExpansion (1 : ℝ) (E₄.mul E₄))]
    congr 1
    simpa using qExpansion_mul_coeff (n := 1) 4 4 E₄ E₄
  have he6 : qExpansion (1 : ℝ) (E₆.mul E₆) =
      qExpansion (1 : ℝ) E₆ * qExpansion (1 : ℝ) E₆ := by
    simpa using qExpansion_mul_coeff (n := 1) 6 6 E₆ E₆
  calc (PowerSeries.coeff 0) (qExpansion 1 ⇑(E₄.mul (E₄.mul E₄))) -
        (PowerSeries.coeff 0) (qExpansion 1 ⇑(E₆.mul E₆))
      = (PowerSeries.coeff 0) (qExpansion (1 : ℝ) E₄ *
          (qExpansion (1 : ℝ) E₄ * qExpansion (1 : ℝ) E₄)) -
        (PowerSeries.coeff 0) (qExpansion (1 : ℝ) E₆ * qExpansion (1 : ℝ) E₆) := by
          rw [he4, he6]
    _ = 0 := by
        simp [PowerSeries.coeff_mul, Finset.antidiagonal_zero, Prod.mk_zero_zero,
          Finset.sum_singleton, Prod.fst_zero, Prod.snd_zero, E4_q_exp_zero, E6_q_exp_zero,
          mul_one]

/-- The cusp form `(1/1728) * (E₄^3 - E₆^2)` of weight `12`. -/
@[expose] public def Delta_E4_E6_aux : CuspForm (CongruenceSubgroup.Gamma 1) 12 :=
  let F := DirectSum.of _ 4 E₄
  let G := DirectSum.of _ 6 E₆
  cuspFormOfCoeffZero ((1 / 1728 : ℂ) • (F ^ 3 - G ^ 2) 12) E4E6_coeff_zero_eq_zero

/-- The first nontrivial `q`-coefficient of `Delta` is `1`. -/
public lemma Delta_q_one_term : (qExpansion 1 Delta).coeff 1 = 1 :=
  ModularForm.discriminant_qExpansion_coeff_one

variable {α β γ : Type*}

variable [CommMonoid α] [TopologicalSpace α] [UniformSpace α]

/-- The `q`-coefficient of `E₄` at `n = 1` is `240`. -/
public lemma E4_q_exp_one : (qExpansion 1 E₄).coeff 1 = 240 :=
  ModularForm.E₄_qExpansion_coeff_one

/-- The `q`-coefficient of `E₆` at `n = 1` is `-504`. -/
public lemma E6_q_exp_one : (qExpansion 1 E₆).coeff 1 = -504 :=
  ModularForm.E₆_qExpansion_coeff_one

/-- Normalize a non-cusp modular form so that its constant `q`-coefficient becomes `1`. -/
public lemma modularForm_normalise (f : ModularForm Γ(1) k) (hf : ¬ IsCuspForm Γ(1) k f) :
    (qExpansion 1 (((qExpansion 1 f).coeff 0)⁻¹ • f)).coeff 0 = 1 := by
  rw [← Nat.cast_one (R := ℝ), ← qExpansion_smul2, Nat.cast_one]
  exact inv_mul_cancel₀ (by intro h; exact hf ((IsCuspForm_iff_coeffZero_eq_zero k f).2 h))

open ArithmeticFunction

section Ramanujan_Formula

-- In this section, we state some simplifications that are used in Cor 7.5-7.7 of the blueprint

end Ramanujan_Formula


section ImagAxisProperties

open _root_.Complex hiding I

/-- `(-2πi)^k` is real for even k. -/
lemma neg_two_pi_I_pow_even_real (k : ℕ) (hk : Even k) :
    ((-2 * Real.pi * Complex.I) ^ k : ℂ).im = 0 := by
  have h : (-2 * Real.pi * Complex.I) ^ k = (-(2 * Real.pi) : ℂ) ^ k * Complex.I ^ k := by ring
  rw [h]
  obtain ⟨m, rfl⟩ := hk
  simp only [Complex.mul_im, ← two_mul, pow_mul, I_sq]
  rcases m.even_or_odd with hm | hm <;> simp [hm.neg_one_pow] <;> norm_cast

/-- On imaginary axis z = I*t, the q-expansion exponent 2πi·n·z reduces to -(2πnt).
This is useful for reusing the same algebraic simplification across `E₂`, `E₄`, `E₆`. -/
lemma exp_imag_axis_arg (t : ℝ) (ht : 0 < t) (n : ℕ+) :
    2 * Real.pi * Complex.I * (⟨Complex.I * t, by simp [ht]⟩ : ℍ) * n =
    (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
  push_cast
  ring_nf
  simp [I_sq]

/-- `ζ(2k)` is real for all `k ≥ 1`. -/
public lemma riemannZeta_even_im_eq_zero (k : ℕ) (hk : k ≠ 0) :
    (riemannZeta (2 * k : ℕ)).im = 0 :=
  riemannZeta_im_eq_zero_of_one_lt (show (1 : ℝ) < ((2 * k : ℕ) : ℝ) by
    exact_mod_cast (show 1 < 2 * k from by omega))

/-- `E_k(it)` is real for all `t > 0` when `k` is even and `k ≥ 4`.
This is the generalized theorem from which `E₄_imag_axis_real` and `E₆_imag_axis_real` follow. -/
theorem E_even_imag_axis_real (k : ℕ) (hk : (3 : ℤ) ≤ k) (hk2 : Even k) :
    ResToImagAxis.Real (E k hk).toFun := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  change (E k hk z).im = 0
  have hq := E_k_q_expansion k hk hk2 z
  simp only at hq ⊢
  rw [hq]
  simp only [add_im, one_im, zero_add]
  -- Step 1: Show each term in the sum is real on the imaginary axis
  have hterm_im : ∀ n : ℕ+, (↑((ArithmeticFunction.sigma (k - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n)).im = 0 := by
    intro n
    have hexp_arg : 2 * ↑Real.pi * Complex.I * z * n = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
      simpa [z] using exp_imag_axis_arg (t := t) ht n
    rw [hexp_arg]
    -- Using simp only: `simp` gives false positive linter warning but args are needed
    simp only [mul_im, exp_ofReal_im, natCast_im, mul_zero, zero_mul, add_zero]
  -- Summability of the series
  have hsum : Summable fun n : ℕ+ ↦ ↑((ArithmeticFunction.sigma (k - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n) := by
    refine .of_norm (.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
      (summable_norm_iff.mpr (by have := a33 k 1 z; simpa using this)))
    simp only [norm_mul, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [Complex.norm_pow, Complex.norm_natCast]
    have := sigma_bound (k - 1) n
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at this
    exact_mod_cast this
  -- The sum has zero imaginary part
  have hsum_im : (∑' (n : ℕ+), ↑((ArithmeticFunction.sigma (k - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n)).im = 0 := by
    rw [im_tsum hsum]
    simp [hterm_im]
  obtain ⟨m, hm⟩ := hk2
  have hk2m : k = 2 * m := by omega
  have hzeta_im : (riemannZeta k).im = 0 := by
    rw [hk2m]; exact riemannZeta_even_im_eq_zero m (by omega)
  have hinv_zeta_im : (1 / riemannZeta k).im = 0 := by simp [hzeta_im]
  have hfact_im : ((k - 1).factorial : ℂ).im = 0 := by simp
  simp only [mul_im, div_im, hinv_zeta_im, hsum_im, neg_two_pi_I_pow_even_real k ⟨m, hm⟩, hfact_im]
  ring

/-- `E₄(it)` is real for all `t > 0`. -/
public theorem E₄_imag_axis_real : ResToImagAxis.Real E₄.toFun :=
  E_even_imag_axis_real 4 (by decide) (by decide)

/-- `E₆(it)` is real for all `t > 0`. -/
public theorem E₆_imag_axis_real : ResToImagAxis.Real E₆.toFun :=
  E_even_imag_axis_real 6 (by decide) (by decide)

/-- `E₂(it)` is real for all `t > 0`. -/
public theorem E₂_imag_axis_real : ResToImagAxis.Real E₂ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  change (E₂ z).im = 0
  have hq := E₂_eq z
  rw [hq]
  simp only [sub_im, one_im, zero_sub]
  -- Step 1: Show each term in the sum is real on the imaginary axis
  have hterm_im : ∀ n : ℕ+, (↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z))).im = 0 := by
    intro n
    have hexp_arg : 2 * ↑Real.pi * Complex.I * n * z = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm, z] using exp_imag_axis_arg (t := t) ht n
    have h1 : (1 - cexp (2 * ↑Real.pi * Complex.I * ↑↑n * ↑z)).im = 0 := by
      simp only [Complex.sub_im, Complex.one_im, hexp_arg, exp_ofReal_im, sub_zero]
    have h2 : (↑n * cexp (2 * ↑Real.pi * Complex.I * n * z)).im = 0 := by
      simp only [mul_im, natCast_im, hexp_arg, exp_ofReal_im, mul_zero, zero_mul, add_zero]
    simp [Complex.div_im, h2, h1]
  -- Step 2: Summability of the series
  have hsum : Summable fun n : ℕ+ ↦ ↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z)) := by
    set r : ℂ := cexp (2 * ↑Real.pi * Complex.I * z) with hr
    have hr_norm : ‖r‖ < 1 := by
      simpa [hr] using exp_upperHalfPlane_lt_one z
    have hs : Summable fun n : ℕ ↦ (n : ℂ) * r ^ n / (1 - r ^ n) := by
      simpa [pow_one] using
        (summable_norm_pow_mul_geometric_div_one_sub (𝕜 := ℂ) 1 (r := r) hr_norm)
    refine (hs.comp_injective PNat.coe_injective).congr ?_
    intro n
    have hpow : r ^ (n : ℕ) = cexp (2 * ↑Real.pi * Complex.I * (↑n : ℂ) * z) := by
      rw [hr]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.exp_nat_mul (2 * ↑Real.pi * Complex.I * z) (n : ℕ)).symm
    simp [hpow]
  -- Step 3: The sum has zero imaginary part
  have hsum_im : (∑' (n : ℕ+), ↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z))).im = 0 := by
    rw [Complex.im_tsum hsum]
    simp [hterm_im]
  -- 24 * sum is real, so its imaginary part is 0
  simp [Complex.mul_im, hsum_im]

end ImagAxisProperties

/-! ## Boundedness of E₂. -/

/-- For im(z) ≥ 1, ‖exp(2πiz)‖ ≤ exp(-2π); useful for q-expansion bounds. -/
public lemma norm_exp_two_pi_I_le_exp_neg_two_pi (z : ℍ) (hz : 1 ≤ z.im) :
    ‖cexp (2 * π * Complex.I * z)‖ ≤ Real.exp (-2 * π) := by
  have h : (2 * ↑π * Complex.I * (z : ℂ)).re = -2 * π * z.im := by
    simp [mul_assoc, mul_left_comm, mul_comm, Complex.mul_re, Complex.mul_im]
  simpa [Complex.norm_exp, h] using (Real.exp_le_exp.2 (by nlinarith [hz, Real.pi_pos]))

/-- For ‖q‖ < 1, ‖∑ n·qⁿ/(1-qⁿ)‖ ≤ ‖q‖/(1-‖q‖)³. -/
public lemma norm_tsum_logDeriv_expo_le {q : ℂ} (hq : ‖q‖ < 1) :
    ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤ ‖q‖ / (1 - ‖q‖) ^ 3 := by
  set r : ℝ := ‖q‖
  have hr_norm_lt_one : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg (norm_nonneg q)]
  have hsumm_nat : Summable (fun n : ℕ ↦ (n : ℝ) * r ^ n) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr_norm_lt_one
  have hsumm_majorant : Summable (fun n : ℕ+ ↦ (n : ℝ) * r ^ (n : ℕ) / (1 - r)) := by
    simpa [div_eq_mul_inv] using (hsumm_nat.subtype _).mul_right (1 - r)⁻¹
  have hterm_bound (n : ℕ+) : ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤
      n * r ^ (n : ℕ) / (1 - r) := by
    rw [norm_div, norm_mul, Complex.norm_natCast]
    have hdenom_lower : 1 - r ≤ ‖1 - q ^ (n : ℕ)‖ := by
      have h1 : r ^ (n : ℕ) ≤ r := by
        have := pow_le_pow_of_le_one (norm_nonneg q) hq.le
          (m := 1) (n := (n : ℕ)) (Nat.one_le_iff_ne_zero.mpr n.pos.ne')
        simpa using this
      have h2 := norm_sub_norm_le (1 : ℂ) (q ^ (n : ℕ))
      simp only [norm_one, norm_pow] at h2; linarith
    calc ↑n * ‖q ^ (n : ℕ)‖ / ‖1 - q ^ (n : ℕ)‖
        ≤ ↑n * ‖q ^ (n : ℕ)‖ / (1 - r) := div_le_div_of_nonneg_left
          (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (sub_pos.mpr hq) hdenom_lower
      _ = ↑n * r ^ (n : ℕ) / (1 - r) := by rw [norm_pow]
  have hsumm_norms : Summable (fun n : ℕ+ ↦ ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖) :=
    .of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm_bound hsumm_majorant
  calc ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
      ≤ ∑' n : ℕ+, ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ := norm_tsum_le_tsum_norm hsumm_norms
    _ ≤ ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r) :=
        hsumm_norms.tsum_le_tsum hterm_bound hsumm_majorant
    _ = r / (1 - r) ^ 3 := by
        simp only [div_eq_mul_inv, tsum_mul_right, tsum_pnat_coe_mul_geometric hr_norm_lt_one,
          pow_succ]
        field_simp

/-- Monotone version of `norm_tsum_logDeriv_expo_le`: if ‖q‖ ≤ r < 1, then
‖∑ n·qⁿ/(1-qⁿ)‖ ≤ r/(1-r)³. Useful when we have a uniform bound on ‖q‖. -/
public lemma norm_tsum_logDeriv_expo_le_of_norm_le {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (hr : r < 1) :
    ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤ r / (1 - r) ^ 3 := by
  have hq : ‖q‖ < 1 := lt_of_le_of_lt hqr hr
  have hr_nonneg : 0 ≤ r := le_trans (norm_nonneg q) hqr
  calc ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
      ≤ ‖q‖ / (1 - ‖q‖) ^ 3 := norm_tsum_logDeriv_expo_le hq
    _ ≤ r / (1 - r) ^ 3 := by
        have := sub_pos.mpr hr
        have := sub_pos.mpr hq
        gcongr

/-!
## Boundedness and limit at infinity

We use `E₂_eq` to bound the tail series in terms of `q = exp(2π i z)` when `Im z ≥ 1`.
-/

/-- `E₂` is bounded at `Im z → ∞`. -/
public lemma E₂_isBoundedAtImInfty : IsBoundedAtImInfty E₂ := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  set r₀ : ℝ := Real.exp (-2 * π)
  have hr₀_lt_one : r₀ < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  refine ⟨1 + 24 * (r₀ / (1 - r₀) ^ 3), 1, fun z hz ↦ ?_⟩
  rw [E₂_eq]
  set q : ℂ := cexp (2 * π * Complex.I * z)
  have hq_bound : ‖q‖ ≤ r₀ := norm_exp_two_pi_I_le_exp_neg_two_pi z hz
  -- Rewrite sum in terms of q^n
  set S := ∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))
  have hS_eq : ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
      (1 - cexp (2 * π * Complex.I * ↑n * ↑z)) = S := by
    congr 1
    ext n
    have : cexp (2 * π * Complex.I * n * z) = q ^ (n : ℕ) := exp_aux z ↑n
    simp [this]
  calc ‖1 - 24 * ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
          (1 - cexp (2 * π * Complex.I * ↑n * ↑z))‖
      = ‖1 - 24 * S‖ := by rw [hS_eq]
    _ ≤ 1 + 24 * ‖S‖ := by
        have := norm_sub_le (1 : ℂ) (24 * S); simp at this; linarith
    _ ≤ 1 + 24 * (r₀ / (1 - r₀) ^ 3) := by
        gcongr; exact norm_tsum_logDeriv_expo_le_of_norm_le hq_bound hr₀_lt_one

lemma E₂_isZeroAtImInfty_sub_one : IsZeroAtImInfty (fun z : ℍ ↦ E₂ z - 1) := by
  rw [UpperHalfPlane.isZeroAtImInfty_iff]
  intro ε hε
  set δ : ℝ := min (1 / 2) (ε / 192)
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by nlinarith)
  have hδ_event : ∀ᶠ x : ℝ in atTop, Real.exp (-((2 * Real.pi) * x)) < δ := by
    refine (tendsto_exp_neg_atTop_nhds_zero.comp ?_).eventually (Iio_mem_nhds hδ_pos)
    exact tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < (2 * Real.pi))
  rcases (Filter.eventually_atTop.1 hδ_event) with ⟨A₀, hA₀⟩
  refine ⟨max A₀ 1, fun z hz ↦ ?_⟩
  have hzA₀ : A₀ ≤ z.im := le_trans (le_max_left A₀ 1) hz
  set q : ℂ := cexp (2 * π * Complex.I * z)
  set S : ℂ := ∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))
  have hT_eq :
      (∑' n : ℕ+, (n : ℂ) * cexp (2 * π * Complex.I * n * z) /
          (1 - cexp (2 * π * Complex.I * n * z))) = S := by
    congr 1
    ext n
    have : cexp (2 * π * Complex.I * n * z) = q ^ (n : ℕ) := exp_aux z ↑n
    simp [this]
  have hq_norm : ‖q‖ = Real.exp (-((2 * Real.pi) * z.im)) := by
    simp [q, Complex.norm_exp, mul_assoc, mul_left_comm, mul_comm, mul_re]
  have hqδ : ‖q‖ ≤ δ := by
    refine le_trans ?_ (le_of_lt (hA₀ A₀ le_rfl))
    simpa [hq_norm] using Real.exp_le_exp.2 (by nlinarith [hzA₀, Real.pi_pos])
  have hq_half : ‖q‖ ≤ (1 / 2 : ℝ) := hqδ.trans (min_le_left _ _)
  have hq_lt_one : ‖q‖ < 1 := lt_of_le_of_lt hq_half (by norm_num)
  have hS_bound : ‖S‖ ≤ 8 * ‖q‖ := calc
    ‖S‖ ≤ ‖q‖ / (1 - ‖q‖) ^ 3 := norm_tsum_logDeriv_expo_le hq_lt_one
    _ ≤ ‖q‖ / ((1 / 2 : ℝ) ^ 3) := by
        apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        gcongr; linarith
    _ = 8 * ‖q‖ := by ring_nf
  have hE₂_sub_one : E₂ z - 1 = -24 * S := by grind [E₂_eq z]
  calc ‖E₂ z - 1‖ = 24 * ‖S‖ := by simp [hE₂_sub_one]
    _ ≤ 24 * (8 * ‖q‖) := by gcongr
    _ ≤ 24 * (8 * (ε / 192)) := by gcongr; exact hqδ.trans (min_le_right _ _)
    _ = ε := by nlinarith

/-- `E₂ z` tends to `1` as `Im z → ∞`. -/
public theorem tendsto_E₂_atImInfty : Tendsto E₂ atImInfty (𝓝 (1 : ℂ)) :=
  tendsto_sub_nhds_zero_iff.mp E₂_isZeroAtImInfty_sub_one

end
