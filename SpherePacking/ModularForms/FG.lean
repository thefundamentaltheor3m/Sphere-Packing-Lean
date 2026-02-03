import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Monotone.Defs

import SpherePacking.ModularForms.RamanujanIdentities
import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.Eisenstein
import SpherePacking.ModularForms.JacobiTheta
import SpherePacking.ModularForms.EisensteinAsymptotics

open UpperHalfPlane hiding I
open Filter Complex ModularGroup ModularForm SlashAction
open scoped Real Manifold SlashAction ArithmeticFunction.sigma UpperHalfPlane


/--
Definition of $F$ and $G$ and auxiliary functions for the inequality between them
on the imaginary axis.
-/
noncomputable def F := (E₂ * E₄.toFun - E₆.toFun) ^ 2

/-- F₁ = E₂ * E₄ - E₆, the square root of F. -/
noncomputable def F₁ := E₂ * E₄.toFun - E₆.toFun

noncomputable def G := H₂ ^ 3 * ((2 : ℝ) • H₂ ^ 2 + (5 : ℝ) • H₂ * H₄ + (5 : ℝ) • H₄ ^ 2)

noncomputable def negDE₂ := - (D E₂)

noncomputable def Δ_fun := 1728⁻¹ * (E₄.toFun ^ 3 - E₆.toFun ^ 2)

noncomputable def L₁₀ := (D F) * G - F * (D G)

noncomputable def SerreDer_22_L₁₀ := serre_D 22 L₁₀

noncomputable def FReal (t : ℝ) : ℝ := (F.resToImagAxis t).re

noncomputable def GReal (t : ℝ) : ℝ := (G.resToImagAxis t).re

noncomputable def FmodGReal (t : ℝ) : ℝ := (FReal t) / (GReal t)

theorem F_eq_FReal {t : ℝ} (ht : 0 < t) : F.resToImagAxis t = FReal t := by sorry

theorem G_eq_GReal {t : ℝ} (ht : 0 < t) : G.resToImagAxis t = GReal t := by sorry

theorem FmodG_eq_FmodGReal {t : ℝ} (ht : 0 < t) :
    FmodGReal t = (F.resToImagAxis t) / (G.resToImagAxis t) := by sorry

/--
`F = 9 * (D E₄)²` by Ramanujan's formula.
From `ramanujan_E₄`: `D E₄ = (1/3) * (E₂ * E₄ - E₆)`
Hence: `E₂ * E₄ - E₆ = 3 * D E₄`, so `F = (E₂ * E₄ - E₆)² = 9 * (D E₄)²`.
-/
theorem F_eq_nine_DE₄_sq : F = (9 : ℂ) • (D E₄.toFun) ^ 2 := by
  have h : E₂ * E₄.toFun - E₆.toFun = 3 • D E₄.toFun := by
    rw [ramanujan_E₄]; ext z; simp
  ext z
  simp only [F, h, Pi.smul_apply, smul_eq_mul, Pi.pow_apply]
  ring

/- Some basic facts -/

theorem F_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
  have h : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₂ * E₄.toFun - E₆.toFun) := by
    exact MDifferentiable.sub (MDifferentiable.mul E₂_holo' E₄.holo') E₆.holo'
  rw [F, pow_two]
  exact MDifferentiable.mul h h

theorem G_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
  have hH₂ := H₂_SIF_MDifferentiable
  have hH₄ := H₄_SIF_MDifferentiable
  unfold G
  have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 2 * H₂ z ^ 2) :=
    (MDifferentiable.pow hH₂ 2).const_smul (2 : ℂ)
  have h2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 5 * H₂ z * H₄ z) := by
    have : (fun z => 5 * H₂ z * H₄ z) = (fun z => (5 : ℂ) * (H₂ z * H₄ z)) := by ext z; ring
    rw [this]; exact (hH₂.mul hH₄).const_smul (5 : ℂ)
  have h3 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 5 * H₄ z ^ 2) :=
    (MDifferentiable.pow hH₄ 2).const_smul (5 : ℂ)
  exact (MDifferentiable.pow hH₂ 3).mul ((h1.add h2).add h3)

theorem SerreF_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D 10 F) := by
  exact serre_D_differentiable F_holo

theorem SerreG_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D 10 G) := by
  exact serre_D_differentiable G_holo

theorem FReal_Differentiable {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ FReal t := by
  sorry

theorem GReal_Differentiable {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ GReal t := by
  sorry

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
  · exact MDifferentiable.sub (MDifferentiable.mul E₂_holo' E₄.holo') E₆.holo'

/--
Modular linear differential equation satisfied by $F$.
-/
theorem MLDE_F : serre_D 12 (serre_D 10 F) = 5 * 6⁻¹ * F + 7200 * Δ_fun * negDE₂ := by
  ext x
  rw [negDE₂, Δ_fun, serre_D, serre_D, F_aux]
  unfold serre_D
  rw [F_aux]
  sorry

/--
Modular linear differential equation satisfied by $G$.
-/
theorem MLDE_G : serre_D 12 (serre_D 10 G) = 5 * 6⁻¹ * G - 640 * Δ_fun * H₂ := by
  sorry

/- Positivity of (quasi)modular forms on the imaginary axis. -/

lemma Δ_fun_imag_axis_pos : ResToImagAxis.Pos Δ_fun := by
  -- Δ_fun = 1728⁻¹ * (E₄³ - E₆²) = Δ by Delta_E4_eqn + Delta_apply
  have hΔ_eq : Δ_fun = Δ := by
    ext z
    -- Δ_fun z = (1728)⁻¹ * (E₄ z^3 - E₆ z^2) by definition
    have hLHS : Δ_fun z = (1728 : ℂ)⁻¹ * (E₄ z ^ 3 - E₆ z ^ 2) := rfl
    -- Δ z = Delta_E4_E6_aux z = (1/1728) * (E₄ z^3 - E₆ z^2)
    have hRHS : Δ z = (1 / 1728 : ℂ) * (E₄ z ^ 3 - E₆ z ^ 2) := by
      rw [← Delta_apply z, Delta_E4_eqn]
      have hAux := CuspForm_to_ModularForm_Fun_coe (CongruenceSubgroup.Gamma 1) 12
        ((1 / 1728 : ℂ) • (((DirectSum.of _ 4 E₄) ^ 3 - (DirectSum.of _ 6 E₆) ^ 2) 12))
        (by rw [IsCuspForm_iff_coeffZero_eq_zero]; exact E4E6_coeff_zero_eq_zero)
      simp only [Delta_E4_E6_aux, pow_two, pow_three, DirectSum.of_mul_of, DirectSum.sub_apply,
        Int.reduceAdd, DirectSum.of_eq_same, one_div] at hAux ⊢
      exact congrFun hAux z
    rw [hLHS, hRHS]; ring
  rw [hΔ_eq]
  exact Delta_imag_axis_pos

/-- The q-expansion exponent argument on imaginary axis z=it with ℕ+ index.
Simplifies `2πi * n * z` where z=it to `-2πnt`. -/
lemma qexp_arg_imag_axis_pnat (t : ℝ) (ht : 0 < t) (n : ℕ+) :
    2 * ↑Real.pi * Complex.I * ↑n * ↑(⟨Complex.I * t, by simp [ht]⟩ : UpperHalfPlane) =
    (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
  have h1 : 2 * ↑Real.pi * Complex.I * (⟨Complex.I * t, by simp [ht]⟩ : UpperHalfPlane) * n =
      (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
    simpa using exp_imag_axis_arg (t := t) ht n
  simp only [mul_assoc, mul_left_comm, mul_comm] at h1 ⊢
  convert h1 using 2

/-- Generic summability for n^a * σ_b(n) * exp(2πinz) series.
Uses σ_b(n) ≤ n^(b+1) (sigma_bound) and a33 (a+b+1) for exponential summability. -/
lemma sigma_qexp_summable_generic (a b : ℕ) (z : UpperHalfPlane) :
    Summable (fun n : ℕ+ => (n : ℂ)^a * (ArithmeticFunction.sigma b n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * n * z)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
  · intro n
    calc ‖(n : ℂ)^a * (ArithmeticFunction.sigma b n : ℂ) * Complex.exp (2 * π * Complex.I * n * z)‖
        = ‖(n : ℂ)^a * (ArithmeticFunction.sigma b n : ℂ)‖ *
            ‖Complex.exp (2 * π * Complex.I * n * z)‖ := norm_mul _ _
      _ ≤ (n : ℝ)^(a + b + 1) * ‖Complex.exp (2 * π * Complex.I * n * z)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [Complex.norm_mul, Complex.norm_pow, Complex.norm_natCast, Complex.norm_natCast]
          have hbound := sigma_bound b n
          calc (n : ℝ)^a * (ArithmeticFunction.sigma b n : ℝ)
              ≤ (n : ℝ)^a * (n : ℝ)^(b + 1) := by
                exact_mod_cast mul_le_mul_of_nonneg_left hbound (pow_nonneg (Nat.cast_nonneg n) a)
            _ = (n : ℝ)^(a + b + 1) := by ring
      _ = ‖(n : ℂ)^(a + b + 1) * Complex.exp (2 * π * Complex.I * n * z)‖ := by
          rw [norm_mul, Complex.norm_pow, Complex.norm_natCast]
  · have ha33 := a33 (a + b + 1) 1 z
    simp only [PNat.val_ofNat, Nat.cast_one, mul_one] at ha33
    have heq : (fun n : ℕ+ => ‖(n : ℂ)^(a + b + 1) * Complex.exp (2 * π * Complex.I * n * z)‖) =
        (fun n : ℕ+ => ‖(n : ℂ)^(a + b + 1) * Complex.exp (2 * π * Complex.I * z * n)‖) := by
      ext n; ring_nf
    rw [heq]
    exact summable_norm_iff.mpr ha33

/-- E₂ q-expansion in sigma form: E₂ = 1 - 24 * ∑ σ₁(n) * q^n.
This follows from G2_q_exp and the definition E₂ = (1/(2*ζ(2))) • G₂.
The proof expands the definitions and simplifies using ζ(2) = π²/6. -/
lemma E₂_sigma_qexp (z : UpperHalfPlane) :
    E₂ z = 1 - 24 * ∑' (n : ℕ+), (ArithmeticFunction.sigma 1 n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * n * z) := by
  -- Use E₂_eq and tsum_eq_tsum_sigma to convert n*q^n/(1-q^n) → σ₁(n)*q^n
  rw [E₂_eq z]
  congr 2
  -- Convert between ℕ+ and ℕ indexing using tsum_pnat_eq_tsum_succ3
  have hl := tsum_pnat_eq_tsum_succ3
    (fun n => ArithmeticFunction.sigma 1 n * Complex.exp (2 * π * Complex.I * n * z))
  have hr := tsum_pnat_eq_tsum_succ3
    (fun n => n * Complex.exp (2 * π * Complex.I * n * z) /
      (1 - Complex.exp (2 * π * Complex.I * n * z)))
  rw [hl, hr]
  have ht := tsum_eq_tsum_sigma z
  simp at *
  rw [ht]

/-- Summability of σ₁ q-series (for D_qexp_tsum_pnat hypothesis). -/
lemma sigma1_qexp_summable (z : UpperHalfPlane) :
    Summable (fun n : ℕ+ => (ArithmeticFunction.sigma 1 n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * n * z)) := by
  have h := sigma_qexp_summable_generic 0 1 z
  simp only [pow_zero, one_mul] at h
  exact h

/-- Generic derivative bound for σ_k q-series on compact sets.
Uses σ_k(n) ≤ n^(k+1) (sigma_bound) and iter_deriv_comp_bound3 for exponential decay. -/
lemma sigma_qexp_deriv_bound_generic (k : ℕ) :
    ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ (n : ℕ+) (z : K),
        ‖(ArithmeticFunction.sigma k n : ℂ) * (2 * Real.pi * Complex.I * n) *
          Complex.exp (2 * Real.pi * Complex.I * n * z.1)‖ ≤ u n := by
  intro K hK hKc
  obtain ⟨u₀, hu₀_sum, hu₀_bound⟩ := iter_deriv_comp_bound3 K hK hKc (k + 2)
  refine ⟨fun n => u₀ n, hu₀_sum.subtype _, fun n z => ?_⟩
  have hpow : (2 * π * n) ^ (k + 2) * ‖Complex.exp (2 * π * Complex.I * n * z.1)‖ ≤ u₀ n := by
    simpa [abs_of_pos Real.pi_pos] using hu₀_bound n z
  calc ‖(ArithmeticFunction.sigma k n : ℂ) * (2 * π * Complex.I * n) *
          Complex.exp (2 * π * Complex.I * n * z.1)‖
      = ‖(ArithmeticFunction.sigma k n : ℂ)‖ * ‖(2 * π * Complex.I * n : ℂ)‖ *
          ‖Complex.exp (2 * π * Complex.I * n * z.1)‖ := by rw [norm_mul, norm_mul]
    _ ≤ (n : ℝ) ^ (k + 1) * (2 * π * n) * ‖Complex.exp (2 * π * Complex.I * n * z.1)‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        have hs : ‖(ArithmeticFunction.sigma k n : ℂ)‖ ≤ (n : ℝ) ^ (k + 1) := by
          simp only [Complex.norm_natCast]; exact_mod_cast sigma_bound k n
        have hn : ‖(2 * π * Complex.I * n : ℂ)‖ = 2 * π * n := by
          simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, Complex.norm_natCast]
        rw [hn]; exact mul_le_mul hs le_rfl (by positivity) (by positivity)
    _ ≤ (2 * π * n) ^ (k + 2) * ‖Complex.exp (2 * π * Complex.I * n * z.1)‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc (n : ℝ) ^ (k + 1) * (2 * π * ↑↑n) = (2 * π) * (n : ℝ) ^ (k + 2) := by ring
          _ ≤ (2 * π) ^ (k + 2) * (n : ℝ) ^ (k + 2) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              calc (2 * π) = (2 * π) ^ 1 := (pow_one _).symm
                _ ≤ (2 * π) ^ (k + 2) :=
                    pow_le_pow_right₀ (by linarith [Real.two_le_pi]) (by omega : 1 ≤ k + 2)
          _ = (2 * π * ↑↑n) ^ (k + 2) := by ring
    _ ≤ u₀ n := hpow

/-- Derivative bound for σ₁ q-series on compact sets (for D_qexp_tsum_pnat hypothesis).
The bound uses σ₁(n) ≤ n² (sigma_bound) and iter_deriv_comp_bound3 for exponential decay. -/
lemma sigma1_qexp_deriv_bound :
    ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ (n : ℕ+) (k : K),
        ‖(ArithmeticFunction.sigma 1 n : ℂ) * (2 * Real.pi * Complex.I * n) *
          Complex.exp (2 * Real.pi * Complex.I * n * k.1)‖ ≤ u n :=
  sigma_qexp_deriv_bound_generic 1

/-- Summability of σ₃ q-series (for E₄ derivative). -/
lemma sigma3_qexp_summable (z : UpperHalfPlane) :
    Summable (fun n : ℕ+ => (ArithmeticFunction.sigma 3 n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * n * z)) := by
  simpa [pow_zero, one_mul] using sigma_qexp_summable_generic 0 3 z

/-- Derivative bound for σ₃ q-series on compact sets (for D_qexp_tsum_pnat hypothesis).
The bound uses σ₃(n) ≤ n⁴ (sigma_bound) and iter_deriv_comp_bound3 for exponential decay. -/
lemma sigma3_qexp_deriv_bound :
    ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ (n : ℕ+) (k : K),
        ‖(ArithmeticFunction.sigma 3 n : ℂ) * (2 * Real.pi * Complex.I * n) *
          Complex.exp (2 * Real.pi * Complex.I * n * k.1)‖ ≤ u n :=
  sigma_qexp_deriv_bound_generic 3

/-- E₄ as explicit tsum (from E4_q_exp PowerSeries coefficients).
Uses hasSum_qExpansion to convert from PowerSeries to tsum form. -/
lemma E₄_sigma_qexp (z : UpperHalfPlane) :
    E₄ z = 1 + 240 * ∑' (n : ℕ+), (ArithmeticFunction.sigma 3 n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * n * z) := by
  -- Use hasSum_qExpansion to get E₄ z = ∑ (qExpansion 1 E₄).coeff m * q^m
  have hsum := ModularFormClass.hasSum_qExpansion (h := 1) E₄ (by norm_num) (by simp) z
  -- Convert HasSum to tsum equation
  have heq : E₄ z = ∑' m : ℕ, (ModularFormClass.qExpansion 1 E₄).coeff m *
      (Function.Periodic.qParam 1 z) ^ m := by
    rw [← hsum.tsum_eq]
    simp [smul_eq_mul]
  rw [heq]
  -- Split off the m=0 term
  have hsum_smul : Summable fun m => (ModularFormClass.qExpansion 1 E₄).coeff m *
      (Function.Periodic.qParam 1 z) ^ m :=
    hsum.summable.congr (fun m => by simp [smul_eq_mul])
  have hsplit : ∑' m : ℕ, (ModularFormClass.qExpansion 1 E₄).coeff m *
      (Function.Periodic.qParam 1 z) ^ m =
      (ModularFormClass.qExpansion 1 E₄).coeff 0 * (Function.Periodic.qParam 1 z) ^ 0 +
      ∑' m : ℕ, (ModularFormClass.qExpansion 1 E₄).coeff (m + 1) *
        (Function.Periodic.qParam 1 z) ^ (m + 1) :=
    hsum_smul.tsum_eq_zero_add
  rw [hsplit]
  simp only [pow_zero, mul_one]
  -- Use E4_q_exp to substitute coefficients
  have hcoeff0 : (ModularFormClass.qExpansion 1 E₄).coeff 0 = 1 := E4_q_exp_zero
  have hcoeffn : ∀ n : ℕ, 0 < n → (ModularFormClass.qExpansion 1 E₄).coeff n = 240 * (σ 3 n) := by
    intro n hn
    have h := congr_fun E4_q_exp n
    simp only [hn.ne', ↓reduceIte] at h
    exact h
  rw [hcoeff0]
  congr 1
  -- Convert sum over ℕ to sum over ℕ+
  have hconv : ∑' m : ℕ, (ModularFormClass.qExpansion 1 E₄).coeff (m + 1) *
      (Function.Periodic.qParam 1 z) ^ (m + 1) =
      ∑' n : ℕ+, (ModularFormClass.qExpansion 1 E₄).coeff n *
        (Function.Periodic.qParam 1 z) ^ (n : ℕ) := by
    rw [← tsum_pnat_eq_tsum_succ3 (fun n => (ModularFormClass.qExpansion 1 E₄).coeff n *
        (Function.Periodic.qParam 1 z) ^ n)]
  rw [hconv]
  -- Now substitute the coefficients for n ≥ 1
  have hterm : ∀ n : ℕ+, (ModularFormClass.qExpansion 1 E₄).coeff n *
      (Function.Periodic.qParam 1 z) ^ (n : ℕ) =
      240 * ((σ 3 n : ℂ) * Complex.exp (2 * π * Complex.I * n * z)) := by
    intro n
    rw [hcoeffn n n.pos]
    -- Function.Periodic.qParam 1 z = exp(2πiz)
    have hq : Function.Periodic.qParam 1 z = Complex.exp (2 * π * Complex.I * z) := by
      simp only [Function.Periodic.qParam, UpperHalfPlane.coe]
      congr 1
      ring_nf
      simp
    rw [hq]
    -- exp(2πiz)^n = exp(2πinz)
    have hpow : Complex.exp (2 * π * Complex.I * z) ^ (n : ℕ) =
        Complex.exp (2 * π * Complex.I * n * z) := by
      rw [← Complex.exp_nat_mul]
      congr 1; ring
    rw [hpow]
    ring
  rw [tsum_congr hterm, tsum_mul_left]

/-- D E₄ q-expansion via termwise differentiation.
D E₄ = 240 * ∑ n * σ₃(n) * qⁿ from differentiating E₄ = 1 + 240 * ∑ σ₃(n) * qⁿ. -/
theorem DE₄_qexp (z : UpperHalfPlane) :
    D E₄.toFun z = 240 * ∑' (n : ℕ+), (n : ℂ) * (ArithmeticFunction.sigma 3 n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * n * z) := by
  let f : UpperHalfPlane → ℂ := fun w => ∑' n : ℕ+, (ArithmeticFunction.sigma 3 n : ℂ) *
    Complex.exp (2 * π * Complex.I * (n : ℂ) * (w : ℂ))
  have hE4_eq : E₄.toFun = (fun _ => 1) + (240 : ℂ) • f := by
    ext w; simp only [ModularForm.toFun_eq_coe, f, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact E₄_sigma_qexp w
  have hDf : D f z = ∑' n : ℕ+, (n : ℂ) * (ArithmeticFunction.sigma 3 n : ℂ) *
      Complex.exp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
    apply D_qexp_tsum_pnat _ z (sigma3_qexp_summable z) sigma3_qexp_deriv_bound
  have hf_mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
    have h : f = (240 : ℂ)⁻¹ • (fun w => E₄ w - 1) := by
      ext w; simp only [f, Pi.smul_apply, smul_eq_mul]; rw [E₄_sigma_qexp w]; ring
    rw [h]; exact (E₄.holo'.sub mdifferentiable_const).const_smul _
  have hD_smul : D ((240 : ℂ) • f) z = (240 : ℂ) * D f z := by
    rw [congrFun (D_smul 240 f hf_mdiff) z, Pi.smul_apply, smul_eq_mul]
  have hD_one : D (fun _ : UpperHalfPlane => (1 : ℂ)) z = 0 := D_const 1 z
  calc D E₄.toFun z
      = D ((fun _ => 1) + (240 : ℂ) • f) z := by rw [hE4_eq]
    _ = D (fun _ => 1) z + D ((240 : ℂ) • f) z :=
        congrFun (D_add _ _ mdifferentiable_const (hf_mdiff.const_smul _)) z
    _ = 0 + (240 : ℂ) * D f z := by rw [hD_one, hD_smul]
    _ = _ := by rw [zero_add, hDf]

/--
The q-expansion identity E₂E₄ - E₆ = 720·Σn·σ₃(n)·qⁿ.
This follows from Ramanujan's formula: E₂E₄ - E₆ = 3·D(E₄),
combined with D(E₄) = 240·Σn·σ₃(n)·qⁿ (since D multiplies q-coefficients by n).
-/
theorem E₂_mul_E₄_sub_E₆ (z : ℍ) :
    (E₂ z) * (E₄ z) - (E₆ z) = 720 * ∑' (n : ℕ+), n * (σ 3 n) * cexp (2 * π * Complex.I * n * z)
    := by
  -- From ramanujan_E₄: D E₄ = (1/3) * (E₂ * E₄ - E₆)
  -- So: E₂ * E₄ - E₆ = 3 * D E₄
  have hRam : (E₂ z) * (E₄ z) - (E₆ z) = 3 * D E₄.toFun z := by
    have h := congrFun ramanujan_E₄ z
    simp only [Pi.mul_apply, Pi.sub_apply, show (3⁻¹ : ℍ → ℂ) z = 3⁻¹ from rfl] at h
    field_simp at h ⊢
    ring_nf at h ⊢
    exact h.symm
  -- Substitute D(E₄) = 240 * ∑' n, n * σ₃(n) * q^n
  rw [hRam, DE₄_qexp]
  ring

/-- Each term n*σ₃(n)*exp(-2πnt) in D E₄ q-expansion has positive real part on imaginary axis. -/
lemma DE₄_term_re_pos (t : ℝ) (ht : 0 < t) (n : ℕ+) :
    0 < ((n : ℂ) * (ArithmeticFunction.sigma 3 n : ℂ) *
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑n *
        ↑(⟨Complex.I * t, by simp [ht]⟩ : UpperHalfPlane))).re := by
  rw [qexp_arg_imag_axis_pnat t ht n]
  simp only [Complex.mul_re, Complex.exp_ofReal_re, Complex.exp_ofReal_im, mul_zero,
    sub_zero, Complex.natCast_re, Complex.natCast_im]
  refine mul_pos (mul_pos ?_ ?_) (Real.exp_pos _)
  · exact_mod_cast n.pos
  · exact_mod_cast ArithmeticFunction.sigma_pos 3 n n.ne_zero

/-- D E₄ q-expansion series is summable on imaginary axis. -/
lemma DE₄_summable (t : ℝ) (ht : 0 < t) :
    Summable fun n : ℕ+ => (n : ℂ) * (ArithmeticFunction.sigma 3 n : ℂ) *
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑n *
        ↑(⟨Complex.I * t, by simp [ht]⟩ : UpperHalfPlane)) := by
  simpa [pow_one] using sigma_qexp_summable_generic 1 3 ⟨Complex.I * t, by simp [ht]⟩

/-- D E₄ is real on the imaginary axis. -/
lemma DE₄_imag_axis_real : ResToImagAxis.Real (D E₄.toFun) := by
  exact D_real_of_real E₄_imag_axis_real E₄.holo'

/-- The real part of (D E₄)(it) is positive for t > 0. -/
lemma DE₄_imag_axis_re_pos (t : ℝ) (ht : 0 < t) :
    0 < ((D E₄.toFun).resToImagAxis t).re := by
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set z : UpperHalfPlane := ⟨Complex.I * t, by simp [ht]⟩ with hz
  rw [DE₄_qexp z]
  have hsum : Summable fun n : ℕ+ => (n : ℂ) * (ArithmeticFunction.sigma 3 n : ℂ) *
      Complex.exp (2 * ↑Real.pi * Complex.I * n * z) := by
    simp only [hz]; exact DE₄_summable t ht
  have hsum_re : Summable fun n : ℕ+ =>
      ((n : ℂ) * (ArithmeticFunction.sigma 3 n : ℂ) *
        Complex.exp (2 * ↑Real.pi * Complex.I * n * z)).re := ⟨_, Complex.hasSum_re hsum.hasSum⟩
  have hpos : ∀ n : ℕ+, 0 < ((n : ℂ) * (ArithmeticFunction.sigma 3 n : ℂ) *
      Complex.exp (2 * ↑Real.pi * Complex.I * n * z)).re := by
    intro n; simp only [hz]; exact DE₄_term_re_pos t ht n
  have htsum_pos := Summable.tsum_pos hsum_re (fun n => le_of_lt (hpos n)) 1 (hpos 1)
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  rw [Complex.re_tsum hsum]
  exact mul_pos (by norm_num : (0 : ℝ) < 240) htsum_pos

/--
`D E₄` is positive on the imaginary axis.
Direct proof via q-expansion: D E₄ = 240 * ∑ n*σ₃(n)*qⁿ (DE₄_qexp).
On z = it, each term n*σ₃(n)*e^(-2πnt) > 0, so the sum is positive.
-/
lemma DE₄_imag_axis_pos : ResToImagAxis.Pos (D E₄.toFun) :=
  ⟨DE₄_imag_axis_real, DE₄_imag_axis_re_pos⟩

/-- Q-expansion identity: negDE₂ = 24 * ∑ n * σ₁(n) * q^n
From Ramanujan's formula: D E₂ = (E₂² - E₄)/12, so -D E₂ = (E₄ - E₂²)/12.
And the derivative of E₂ = 1 - 24∑ σ₁(n) q^n gives -D E₂ = 24 ∑ n σ₁(n) q^n.
See blueprint equation at line 136 of modform-ineq.tex.
Proof outline:
1. E₂_sigma_qexp: E₂ = 1 - 24 * ∑ σ₁(n) * q^n
2. D_qexp_tsum_pnat: D(∑ a(n) * q^n) = ∑ n * a(n) * q^n
3. negDE₂ = -D E₂ = -D(1 - 24∑...) = 24 * ∑ n * σ₁(n) * q^n -/
theorem negDE₂_qexp (z : UpperHalfPlane) :
    negDE₂ z = 24 * ∑' (n : ℕ+), (n : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * n * z) := by
  simp only [negDE₂]
  let f : UpperHalfPlane → ℂ := fun w => ∑' n : ℕ+, (ArithmeticFunction.sigma 1 n : ℂ) *
    Complex.exp (2 * π * Complex.I * (n : ℂ) * (w : ℂ))
  have hE2_eq : E₂ = (fun _ => 1) - (24 : ℂ) • f := by
    ext w; simp only [f, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; exact E₂_sigma_qexp w
  have hDf : D f z = ∑' n : ℕ+, (n : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) *
      Complex.exp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
    apply D_qexp_tsum_pnat _ z (sigma1_qexp_summable z) sigma1_qexp_deriv_bound
  have hf_mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
    have h : f = (24 : ℂ)⁻¹ • (fun w => 1 - E₂ w) := by
      ext w; simp only [f, Pi.smul_apply, smul_eq_mul]; rw [E₂_sigma_qexp w]; ring
    rw [h]; exact (mdifferentiable_const.sub E₂_holo').const_smul _
  have hD_smul : D ((24 : ℂ) • f) z = (24 : ℂ) * D f z := by
    rw [congrFun (D_smul 24 f hf_mdiff) z, Pi.smul_apply, smul_eq_mul]
  have hD_one : D (fun _ : UpperHalfPlane => (1 : ℂ)) z = 0 := D_const 1 z
  calc -(D E₂) z
      = -(D ((fun _ => 1) - (24 : ℂ) • f)) z := by rw [hE2_eq]
    _ = -((D (fun _ => 1) - D ((24 : ℂ) • f)) z) := by
        rw [congrFun (D_sub _ _ mdifferentiable_const (hf_mdiff.const_smul _)) z]
    _ = -(D (fun _ => 1) z - D ((24 : ℂ) • f) z) := by rfl
    _ = -(0 - (24 : ℂ) * D f z) := by rw [hD_one, hD_smul]
    _ = _ := by rw [hDf]; ring

/-- The q-expansion series for negDE₂ is summable. -/
lemma negDE₂_summable (t : ℝ) (ht : 0 < t) :
    Summable fun n : ℕ+ => (n : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) *
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑n *
        ↑(⟨Complex.I * t, by simp [ht]⟩ : UpperHalfPlane)) := by
  simpa [pow_one] using sigma_qexp_summable_generic 1 1 ⟨Complex.I * t, by simp [ht]⟩

/-- Each term n*σ₁(n)*exp(-2πnt) in the q-expansion of negDE₂ has positive real part. -/
lemma negDE₂_term_re_pos (t : ℝ) (ht : 0 < t) (n : ℕ+) :
    0 < ((n : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) *
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑n *
        ↑(⟨Complex.I * t, by simp [ht]⟩ : UpperHalfPlane))).re := by
  rw [qexp_arg_imag_axis_pnat t ht n]
  simp only [Complex.mul_re, Complex.exp_ofReal_re, Complex.exp_ofReal_im, mul_zero,
    sub_zero, Complex.natCast_re, Complex.natCast_im]
  refine mul_pos (mul_pos ?_ ?_) (Real.exp_pos _)
  · exact_mod_cast n.pos
  · exact_mod_cast ArithmeticFunction.sigma_pos 1 n n.ne_zero

/-- `negDE₂` is real on the imaginary axis. -/
lemma negDE₂_imag_axis_real : ResToImagAxis.Real negDE₂ := by
  exact ResToImagAxis.Real.neg (D_real_of_real E₂_imag_axis_real E₂_holo')

/-- The real part of negDE₂(it) is positive for t > 0. -/
lemma negDE₂_imag_axis_re_pos (t : ℝ) (ht : 0 < t) :
    0 < (negDE₂.resToImagAxis t).re := by
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set z : UpperHalfPlane := ⟨Complex.I * t, by simp [ht]⟩ with hz
  rw [negDE₂_qexp z]
  have hsum : Summable fun n : ℕ+ => (n : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) *
      Complex.exp (2 * ↑Real.pi * Complex.I * n * z) := negDE₂_summable t ht
  have hsum_re : Summable fun n : ℕ+ =>
      ((n : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) *
        Complex.exp (2 * ↑Real.pi * Complex.I * n * z)).re := ⟨_, Complex.hasSum_re hsum.hasSum⟩
  have hpos : ∀ n : ℕ+, 0 < ((n : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) *
      Complex.exp (2 * ↑Real.pi * Complex.I * n * z)).re := negDE₂_term_re_pos t ht
  have htsum_pos := Summable.tsum_pos hsum_re (fun n => le_of_lt (hpos n)) 1 (hpos 1)
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  rw [Complex.re_tsum hsum]
  exact mul_pos (by norm_num : (0 : ℝ) < 24) htsum_pos

lemma negDE₂_imag_axis_pos : ResToImagAxis.Pos negDE₂ :=
  ⟨negDE₂_imag_axis_real, negDE₂_imag_axis_re_pos⟩

/-!
## Imaginary Axis Properties

Properties of G and F when restricted to the positive imaginary axis z = I*t.
-/

section ImagAxisProperties

/--
`G(it) > 0` for all `t > 0`.
Blueprint: Lemma 8.6 - follows from H₂(it) > 0 and H₄(it) > 0.
G = H₂³ (2H₂² + 5H₂H₄ + 5H₄²) is positive since all factors are positive.
-/
theorem G_imag_axis_pos : ResToImagAxis.Pos G := by unfold G; fun_prop (disch := positivity)

/--
`G(it)` is real for all `t > 0`.
Blueprint: G = H₂³ (2H₂² + 5H₂H₄ + 5H₄²), product of real functions.
-/
theorem G_imag_axis_real : ResToImagAxis.Real G := G_imag_axis_pos.1

/--
`F(it) > 0` for all `t > 0`.
Blueprint: F = 9*(D E₄)² and D E₄ > 0 on imaginary axis.
-/
theorem F_imag_axis_pos : ResToImagAxis.Pos F := by
  rw [F_eq_nine_DE₄_sq]
  have _ := DE₄_imag_axis_pos
  fun_prop (disch := positivity)

/--
`F(it)` is real for all `t > 0`.
Blueprint: Follows from E₂, E₄, E₆ having real values on the imaginary axis.
-/
theorem F_imag_axis_real : ResToImagAxis.Real F := F_imag_axis_pos.1

theorem F₁_imag_axis_real : ResToImagAxis.Real F₁ := by unfold F₁; fun_prop

end ImagAxisProperties

lemma L₁₀_SerreDer : L₁₀ = (serre_D 10 F) * G - F * (serre_D 10 G) := by
  calc
    L₁₀ = (D F) * G - F * (D G) := rfl
    _ = (D F - 10 * 12⁻¹ * E₂ * F) * G - F * (D G - 10 * 12⁻¹ * E₂ * G) := by ring_nf
    _ = (serre_D 10 F) * G - F * (serre_D 10 G) := by ext z; simp [serre_D]

lemma SerreDer_22_L₁₀_SerreDer :
    SerreDer_22_L₁₀ = (serre_D 12 (serre_D 10 F)) * G - F * (serre_D 12 (serre_D 10 G)) := by
  have SF_holo := @serre_D_differentiable F 10 F_holo
  have SG_holo := @serre_D_differentiable G 10 G_holo
  calc
    SerreDer_22_L₁₀ = serre_D 22 L₁₀ := rfl
    _ = serre_D 22 (serre_D 10 F * G - F * serre_D 10 G) := by rw [L₁₀_SerreDer]
    _ = serre_D 22 (serre_D 10 F * G) - serre_D 22 (F * serre_D 10 G) := by
        apply serre_D_sub _ _ _
        · exact MDifferentiable.mul SF_holo G_holo
        · exact MDifferentiable.mul F_holo SG_holo
    _ = serre_D (12 + 10) ((serre_D 10 F) * G) - serre_D (10 + 12) (F * serre_D 10 G) := by ring_nf
    _ = serre_D 12 (serre_D 10 F) * G + (serre_D 10 F) * (serre_D 10 G)
        - serre_D (10 + 12) (F * serre_D 10 G) := by
          simpa using (serre_D_mul 12 10 (serre_D 10 F) G SF_holo G_holo)
    _ = serre_D 12 (serre_D 10 F) * G + (serre_D 10 F) * (serre_D 10 G)
        - ((serre_D 10 F) * (serre_D 10 G) + F * (serre_D 12 (serre_D 10 G))) := by
          simpa using (serre_D_mul 10 12 F (serre_D 10 G) F_holo SG_holo)
    _ = (serre_D 12 (serre_D 10 F)) * G - F * (serre_D 12 (serre_D 10 G)) := by ring_nf

/- $\partial_{22} \mathcal{L}_{1, 0}$ is positive on the imaginary axis. -/
-- TODO: prove this with `fun_prop` after registering relevant `ResToImagAxis.Real` lemmas
lemma SerreDer_22_L₁₀_real : ResToImagAxis.Real SerreDer_22_L₁₀ := by
  rw [SerreDer_22_L₁₀_SerreDer, MLDE_F, MLDE_G, ResToImagAxis.Real]
  intro t ht
  ring_nf
  simp only [Function.resToImagAxis_apply]
  sorry

-- TODO: prove this with `fun_prop` after finishing the proof of `MLDE_F` and `MLDE_G`
lemma SerreDer_22_L₁₀_pos : ResToImagAxis.Pos SerreDer_22_L₁₀ := by
  refine And.intro SerreDer_22_L₁₀_real ?_
  intro t ht
  rw [SerreDer_22_L₁₀_SerreDer, MLDE_F, MLDE_G]
  ring_nf
  sorry

/- $\mathcal{L}_{1, 0}$ is eventually positive on the imaginary axis. -/
lemma L₁₀_eventuallyPos : ResToImagAxis.EventuallyPos L₁₀ := by
  sorry

/- $\mathcal{L}_{1, 0}$ is positive on the imaginary axis. -/
lemma L₁₀_pos : ResToImagAxis.Pos L₁₀ := antiSerreDerPos SerreDer_22_L₁₀_pos L₁₀_eventuallyPos

/--
$t \mapsto F(it) / G(it)$ is monotone decreasing.
-/
theorem FmodG_antitone : AntitoneOn FmodGReal (Set.Ioi 0) := by
  sorry

lemma I_mul_t_pow_nat (t : ℝ) (n : ℕ) : (I * t) ^ n =
    match n % 4 with
    | 0 => (t : ℂ) ^ n
    | 1 => I * (t : ℂ) ^ n
    | 2 => -((t : ℂ) ^ n)
    | 3 => -I * (t : ℂ) ^ n
    | _ => 0  -- unreachable
    := by
  have hmod : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  rw [mul_pow, Complex.I_pow_eq_pow_mod]
  interval_cases n % 4 <;> simp

-- /-- For any function F : ℍ → ℂ and t > 0, F.resToImagAxis (1/t) = F(S • (I*t)). -/
-- lemma resToImagAxis_one_div_eq_S_smul (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
--     let z : ℍ := ⟨I * t, by simp [ht]⟩
--     F.resToImagAxis (1 / t) = F (S • z) := by
--   have ht_inv : 0 < 1 / t := one_div_pos.mpr ht
--   set z : ℍ := ⟨I * t, by simp [ht]⟩ with hz_def
--   have hS_z : S • z = ⟨I / t, by simp [ht]⟩ := by
--     apply UpperHalfPlane.ext
--     simp only [UpperHalfPlane.modular_S_smul, hz_def, div_eq_mul_inv]
--     change (-(I * ↑t))⁻¹ = I * (↑t)⁻¹
--     have hne : (I : ℂ) * t ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr ht.ne')
--     field_simp [hne]
--     simp only [I_sq]
--     ring
--   simp only [Function.resToImagAxis, ResToImagAxis, ht_inv, ↓reduceDIte, hS_z]
--   congr 1; apply UpperHalfPlane.ext
--   simp only [coe_mk_subtype, div_eq_mul_inv, mul_comm I, one_mul, ofReal_inv]

/- Functional equation of $F$ -/
theorem F_functional_equation (z : ℍ) :
    F (S • z) = z ^ 12 * F z - 12 * I * π ^ (-1 : ℤ) * z ^ 11 * (F₁ * E₄.toFun) z
      - 36 * π ^ (-2 : ℤ) * z ^ 10 * (E₄.toFun z) ^ 2 := by
  -- Expand F, F₁ and apply S-transformation formulas
  have hLHS : F (S • z) = (E₂ (S • z) * E₄ (S • z) - E₆ (S • z)) ^ 2 := rfl
  have hRHS : F z = (E₂ z * E₄ z - E₆ z) ^ 2 := rfl
  have hF₁E₄ : (F₁ * E₄.toFun) z = (E₂ z * E₄ z - E₆ z) * E₄ z := rfl
  rw [hLHS, hRHS, hF₁E₄, E₂_S_transform, E₄_S_transform, E₆_S_transform]
  simp only [zpow_neg, zpow_one, ModularForm.toFun_eq_coe]
  have hI3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  field_simp; ring_nf; simp only [I_sq, hI3]; field_simp; ring

theorem F_functional_equation' {t : ℝ} (ht : 0 < t) :
    FReal (1 / t) = t ^ 12 * FReal t - 12 * π ^ (-1 : ℤ) * t ^ 11 * (F₁ * E₄.toFun).resToImagAxis t
      + 36 * π ^ (-2 : ℤ) * t ^ 10 * (E₄.toFun.resToImagAxis t) ^ 2 := by
  -- Define z = I * t on the imaginary axis
  set z : ℍ := ⟨I * t, by simp [ht]⟩ with hz_def
  -- F.resToImagAxis (1/t) = F(S • z)
  have hF_res : F.resToImagAxis (1 / t) = F (S • z) := ResToImagAxis.one_div_eq_S_smul F ht
  -- Apply F_functional_equation
  have hF_eq := F_functional_equation z
  have hz_pow12 : (z : ℂ) ^ 12 = t ^ 12 := by simp only [hz_def, coe_mk_subtype, I_mul_t_pow_nat]
  have hz_pow11 : (z : ℂ) ^ 11 = -I * t ^ 11 := by
    simp only [hz_def, coe_mk_subtype, I_mul_t_pow_nat]
  have hz_pow10 : (z : ℂ) ^ 10 = -t ^ 10 := by simp only [hz_def, coe_mk_subtype, I_mul_t_pow_nat]
  -- Compute F(S • z) using the functional equation
  have hF_val : F.resToImagAxis (1 / t) = (t : ℂ) ^ 12 * F z
      - 12 * π ^ (-1 : ℤ) * t ^ 11 * (F₁ * E₄.toFun) z
      + 36 * π ^ (-2 : ℤ) * t ^ 10 * (E₄.toFun z) ^ 2 := by
    rw [hF_res, hF_eq, hz_pow12, hz_pow11, hz_pow10]
    have hI2 : (I : ℂ) ^ 2 = -1 := I_sq
    ring_nf
    rw [hI2]
    ring
  -- Relate F z, (F₁ * E₄) z, E₄ z to resToImagAxis values
  have hF_z : F z = F.resToImagAxis t := by rw [hz_def]; exact ResToImagAxis.I_mul_t_eq F t ht
  have hF₁E₄_z : (F₁ * E₄.toFun) z = (F₁ * E₄.toFun).resToImagAxis t := by
    rw [hz_def]; exact ResToImagAxis.I_mul_t_eq (F₁ * E₄.toFun) t ht
  have hE₄_z : E₄.toFun z = E₄.toFun.resToImagAxis t := by
    rw [hz_def]; exact ResToImagAxis.I_mul_t_eq E₄.toFun t ht
  -- Use that F, F₁*E₄, E₄² are real on the imaginary axis
  have hF_im : (F.resToImagAxis t).im = 0 := F_imag_axis_real t ht
  have hF₁E₄_im : ((F₁ * E₄.toFun).resToImagAxis t).im = 0 :=
    ResToImagAxis.Real.mul F₁_imag_axis_real E₄_imag_axis_real t ht
  have hE₄_im : (E₄.toFun.resToImagAxis t).im = 0 := E₄_imag_axis_real t ht
  -- Express complex values as real coercions
  have hF_eq_re : F.resToImagAxis t = (FReal t : ℂ) := by
    unfold FReal
    exact Complex.ext rfl (by simp only [ofReal_im]; exact hF_im)
  have hF₁E₄_eq_re : (F₁ * E₄.toFun).resToImagAxis t =
      (((F₁ * E₄.toFun).resToImagAxis t).re : ℂ) :=
    Complex.ext rfl (by simp only [ofReal_im]; exact hF₁E₄_im)
  have hE₄_eq_re : E₄.toFun.resToImagAxis t = ((E₄.toFun.resToImagAxis t).re : ℂ) :=
    Complex.ext rfl (by simp only [ofReal_im]; exact hE₄_im)
  -- Final computation: show LHS equals RHS by working in ℂ then taking .re
  rw [FReal, hF_val, hF_z, hF₁E₄_z, hE₄_z, hF_eq_re, hF₁E₄_eq_re, hE₄_eq_re]
  set a : ℝ := FReal t with ha_def
  set b : ℝ := ((F₁ * E₄.toFun).resToImagAxis t).re with hb_def
  set c : ℝ := (E₄.toFun.resToImagAxis t).re with hc_def
  -- Show the expression has imaginary part 0, noting π is real
  have him : ((t : ℂ) ^ 12 * (a : ℂ) - 12 * π ^ (-1 : ℤ) * t ^ 11 * (b : ℂ)
      + 36 * π ^ (-2 : ℤ) * t ^ 10 * (c : ℂ) ^ 2).im = 0 := by
    simp only [sub_im, add_im, mul_im, ofReal_re, ofReal_im, pow_succ, pow_zero,
               mul_zero, zero_mul, add_zero, one_mul, zpow_neg, zpow_ofNat,
               inv_im, normSq_ofReal]
    ring
  conv_rhs => rw [← Complex.re_add_im ((t : ℂ) ^ 12 * (a : ℂ) - 12 * π ^ (-1 : ℤ) * t ^ 11 * (b : ℂ)
      + 36 * π ^ (-2 : ℤ) * t ^ 10 * (c : ℂ) ^ 2)]
  simp only [him, ofReal_zero, zero_mul, add_zero]

/- Functional equation of $G$ -/
theorem G_functional_equation (z : ℍ) :
    G (S • z) = -z ^ 10 * H₄ z ^ 3 * (2 * H₄ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₂ z ^ 2) := by
  have hG_expand : G (S • z) = H₂ (S • z) ^ 3 *
      ((2 : ℝ) * H₂ (S • z) ^ 2 + (5 : ℝ) * H₂ (S • z) * H₄ (S • z) +
       (5 : ℝ) * H₄ (S • z) ^ 2) := rfl
  simp only [hG_expand, H₂_S_action', H₄_S_action', ofReal_ofNat]
  ring

theorem G_functional_equation' {t : ℝ} (ht : 0 < t) :
    GReal (1 / t) = t ^ 10 * H₄.resToImagAxis t ^ 3
      * (2 * H₄.resToImagAxis t ^ 2 + 5 * H₂.resToImagAxis t * H₄.resToImagAxis t
        + 5 * H₂.resToImagAxis t ^ 2) := by
  -- Define z = I * t on the imaginary axis
  set z : ℍ := ⟨I * t, by simp [ht]⟩ with hz_def
  -- G.resToImagAxis (1/t) = G(S • z)
  have hG_res : G.resToImagAxis (1 / t) = G (S • z) := ResToImagAxis.one_div_eq_S_smul G ht
  have hG_eq := G_functional_equation z
  -- Power of (I * t): (I*t)^10 = -t^10
  have hz_pow10 : (z : ℂ) ^ 10 = -t ^ 10 := by simp only [hz_def, coe_mk_subtype, I_mul_t_pow_nat]
  -- Compute G(S • z) using the functional equation
  have hG_val : G.resToImagAxis (1 / t) = (t : ℂ) ^ 10 * H₄.resToImagAxis t ^ 3 *
      (2 * H₄.resToImagAxis t ^ 2 + 5 * H₂.resToImagAxis t * H₄.resToImagAxis t +
       5 * H₂.resToImagAxis t ^ 2) := by
    rw [hG_res, hG_eq, hz_pow10]
    -- Relate H₂ z, H₄ z to resToImagAxis values
    have hH₂_z : H₂ z = H₂.resToImagAxis t := by
      rw [hz_def]; exact ResToImagAxis.I_mul_t_eq H₂ t ht
    have hH₄_z : H₄ z = H₄.resToImagAxis t := by
      rw [hz_def]; exact ResToImagAxis.I_mul_t_eq H₄ t ht
    rw [hH₂_z, hH₄_z]
    ring
  -- Use that H₂ and H₄ are real on the imaginary axis
  have hH₂_eq := ResToImagAxis.Real.eq_real_part H₂_imag_axis_real t
  have hH₄_eq := ResToImagAxis.Real.eq_real_part H₄_imag_axis_real t
  -- Final computation
  rw [GReal, hG_val, hH₂_eq, hH₄_eq]
  set x : ℝ := (H₄.resToImagAxis t).re with hx_def
  set y : ℝ := (H₂.resToImagAxis t).re with hy_def
  -- Show the expression has imaginary part 0
  have him : ((t : ℂ) ^ 10 * (x : ℂ) ^ 3 *
      (2 * (x : ℂ) ^ 2 + 5 * (y : ℂ) * (x : ℂ) + 5 * (y : ℂ) ^ 2)).im = 0 := by
    simp only [mul_im, add_im, ofReal_re, ofReal_im, pow_succ, pow_zero, mul_zero,
               zero_mul, add_zero, one_mul]
    ring
  conv_rhs => rw [← Complex.re_add_im ((t : ℂ) ^ 10 * (x : ℂ) ^ 3 *
      (2 * (x : ℂ) ^ 2 + 5 * (y : ℂ) * (x : ℂ) + 5 * (y : ℂ) ^ 2))]
  simp only [him, ofReal_zero, zero_mul, add_zero]

/-!
### Helper lemmas for the limit computation

The following lemmas establish the asymptotic behavior needed for computing
the limit of F/G as t → 0⁺.
-/

/-- F₁ has a Fourier expansion starting at index 1 (it's a cusp form).
F₁ = E₂*E₄ - E₆ = 720 * ∑_{n≥1} n*σ₃(n)*q^n -/
lemma F₁_fourier_expansion (z : ℍ) :
    F₁ z = 720 * ∑' (n : ℕ+), n * (σ 3 n) * cexp (2 * π * Complex.I * n * z) := by
  unfold F₁
  exact E₂_mul_E₄_sub_E₆ z

/-- E₄.resToImagAxis tends to 1 at atTop. -/
lemma E₄_resToImagAxis_tendsto_one :
    Tendsto E₄.toFun.resToImagAxis atTop (nhds 1) :=
  tendsto_resToImagAxis_of_tendsto_atImInfty E₄_tendsto_one_atImInfty

/-- H₂.resToImagAxis tends to 0 at atTop. -/
lemma H₂_resToImagAxis_tendsto_zero :
    Tendsto H₂.resToImagAxis atTop (nhds 0) :=
  tendsto_resToImagAxis_of_tendsto_atImInfty H₂_tendsto_atImInfty

/-- H₄.resToImagAxis tends to 1 at atTop. -/
lemma H₄_resToImagAxis_tendsto_one :
    Tendsto H₄.resToImagAxis atTop (nhds 1) :=
  tendsto_resToImagAxis_of_tendsto_atImInfty H₄_tendsto_atImInfty

/-- F₁ * E₄ is bounded at infinity (needed for the decay argument). -/
lemma F₁_mul_E₄_isBoundedAtImInfty : IsBoundedAtImInfty (F₁ * E₄.toFun) :=
  BoundedAtFilter.mul (E₂_mul_E₄_isBoundedAtImInfty.sub E₆_isBoundedAtImInfty) E₄_isBoundedAtImInfty

/-- F₁ has exponential decay at infinity (it's essentially D E₄ which decays). -/
lemma F₁_isBigO_exp_atImInfty :
    F₁ =O[atImInfty] fun τ => Real.exp (-(2 * π) * τ.im) := by
  -- F₁ = E₂*E₄ - E₆ = (E₂ - 1)*E₄ + (E₄ - 1) - (E₆ - 1)
  -- Each of (E₂ - 1), (E₄ - 1), (E₆ - 1) is O(exp(-2πy))
  -- valueAtInfty E₄ = 1 since E₄ → 1 at infinity
  have hE₄_val : valueAtInfty (⇑E₄) = 1 := E₄_tendsto_one_atImInfty.limUnder_eq
  have hE₄ : (fun z : ℍ => E₄ z - 1) =O[atImInfty] fun z => Real.exp (-(2 * π) * z.im) := by
    have h := ModularFormClass.exp_decay_sub_atImInfty E₄ (by norm_num : (0 : ℝ) < 1)
      ModularFormClass.one_mem_strictPeriods_SL2Z
    simp only [div_one] at h
    convert h using 2 with z
    · rw [hE₄_val]
    · congr 1; ring
  -- valueAtInfty E₆ = 1 since E₆ → 1 at infinity
  have hE₆_val : valueAtInfty (⇑E₆) = 1 := E₆_tendsto_one_atImInfty.limUnder_eq
  have hE₆ : (fun z : ℍ => E₆ z - 1) =O[atImInfty] fun z => Real.exp (-(2 * π) * z.im) := by
    have h := ModularFormClass.exp_decay_sub_atImInfty E₆ (by norm_num : (0 : ℝ) < 1)
      ModularFormClass.one_mem_strictPeriods_SL2Z
    simp only [div_one] at h
    convert h using 2 with z
    · rw [hE₆_val]
    · congr 1; ring
  -- F₁ = (E₂ - 1)*E₄ + (E₄ - 1) - (E₆ - 1)
  have heq : F₁ = fun z => (E₂ z - 1) * E₄ z + (E₄ z - 1) - (E₆ z - 1) := by
    ext z; simp only [F₁, Pi.sub_apply, Pi.mul_apply, ModularForm.toFun_eq_coe]; ring
  rw [heq]
  -- (E₂ - 1) * E₄ = O(exp(-2πy)) since (E₂ - 1) = O(exp(-2πy)) and E₄ is bounded
  have hprod : (fun z => (E₂ z - 1) * E₄ z) =O[atImInfty]
      fun z => Real.exp (-(2 * π) * z.im) := by
    calc (fun z => (E₂ z - 1) * E₄ z) =O[atImInfty]
        fun z => Real.exp (-(2 * π) * z.im) * 1 := E₂_sub_one_isBigO_exp.mul E₄_isBoundedAtImInfty
      _ = fun z => Real.exp (-(2 * π) * z.im) := by simp
  exact (hprod.add hE₄).sub hE₆

/-- s * F₁.resToImagAxis s → 0 as s → ∞. -/
lemma rpow_mul_F₁_resToImagAxis_tendsto_zero :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (1 : ℂ) * F₁.resToImagAxis t) atTop (nhds 0) :=
  tendsto_rpow_mul_resToImagAxis_of_isBigO_exp (by positivity) (F₁_isBigO_exp_atImInfty) 1

/-- s² * FReal s → 0 as s → ∞. -/
lemma rpow_sq_mul_FReal_resToImagAxis_tendsto_zero :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (2 : ℂ) * F.resToImagAxis t) atTop (nhds 0) := by
  -- F = F₁², so F = O(exp(-4π*y)) (double the decay rate)
  have hF_bigO : F =O[atImInfty] fun τ => Real.exp (-(4 * π) * τ.im) := by
    calc F = F₁ ^ 2 := rfl
      _ =O[atImInfty] fun τ => (Real.exp (-(2 * π) * τ.im)) ^ 2 := F₁_isBigO_exp_atImInfty.pow 2
      _ = fun τ => Real.exp (-(4 * π) * τ.im) := by
          ext τ; rw [← Real.exp_nat_mul]; ring_nf
  exact tendsto_rpow_mul_resToImagAxis_of_isBigO_exp (by positivity) hF_bigO 2

/-- s * (F₁ * E₄).resToImagAxis s → 0 as s → ∞.
This follows from F₁ decaying and E₄ → 1. -/
lemma rpow_mul_F₁E₄_resToImagAxis_tendsto_zero :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (1 : ℂ) * (F₁ * E₄.toFun).resToImagAxis t) atTop (nhds 0) := by
  -- F₁ * E₄ is bounded by F₁ (since E₄ is bounded), and F₁ = O(exp(-2πy))
  have hprod_bigO : (F₁ * E₄.toFun) =O[atImInfty] fun τ => Real.exp (-(2 * π) * τ.im) := by
    calc (F₁ * E₄.toFun) =O[atImInfty] fun τ => Real.exp (-(2 * π) * τ.im) * 1 :=
      F₁_isBigO_exp_atImInfty.mul E₄_isBoundedAtImInfty
      _ = fun τ => Real.exp (-(2 * π) * τ.im) := by simp
  exact tendsto_rpow_mul_resToImagAxis_of_isBigO_exp (by positivity) hprod_bigO 1

/-- s² * FReal s → 0 as s → ∞. -/
lemma sq_mul_FReal_tendsto_zero :
    Tendsto (fun s : ℝ => s ^ 2 * FReal s) atTop (nhds 0) := by
  refine ((continuous_re.tendsto 0).comp rpow_sq_mul_FReal_resToImagAxis_tendsto_zero).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  unfold FReal
  simp only [Function.comp_apply, Function.resToImagAxis, ResToImagAxis, hs, ↓reduceDIte]
  -- (s : ℂ) ^ (2 : ℂ) = (s ^ 2 : ℂ) for s > 0
  have h_cpow : (s : ℂ) ^ (2 : ℂ) = ((s ^ 2 : ℝ) : ℂ) := by
    rw [show (s ^ 2 : ℝ) = s ^ (2 : ℝ) from (Real.rpow_natCast s 2).symm]
    exact (Complex.ofReal_cpow (le_of_lt hs) 2).symm
  simp only [Complex.mul_re, h_cpow, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- s * (F₁*E₄).resToImagAxis s (real part) → 0 as s → ∞. -/
lemma mul_F₁E₄_re_tendsto_zero :
    Tendsto (fun s : ℝ => s * ((F₁ * E₄.toFun).resToImagAxis s).re) atTop (nhds 0) := by
  refine ((continuous_re.tendsto 0).comp rpow_mul_F₁E₄_resToImagAxis_tendsto_zero).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  simp only [Function.comp_apply, Function.resToImagAxis, ResToImagAxis, hs, ↓reduceDIte,
    Complex.cpow_one, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- E₄.resToImagAxis s (real part) → 1 as s → ∞. -/
lemma E₄_re_resToImagAxis_tendsto_one :
    Tendsto (fun s : ℝ => (E₄.toFun.resToImagAxis s).re) atTop (nhds 1) :=
  (continuous_re.tendsto 1).comp E₄_resToImagAxis_tendsto_one

/-- The numerator expression N(s) = s² * FReal s - 12/π * s * (F₁*E₄)(is) + 36/π² * E₄(is)²
tends to 36/π² as s → ∞. -/
lemma numerator_tendsto_at_infty :
    Tendsto (fun s : ℝ =>
      s ^ 2 * FReal s - 12 * π ^ (-1 : ℤ) * s * ((F₁ * E₄.toFun).resToImagAxis s).re
        + 36 * π ^ (-2 : ℤ) * (E₄.toFun.resToImagAxis s).re ^ 2)
      atTop (nhds (36 * π ^ (-2 : ℤ))) := by
  -- 0 - 12/π * 0 + 36/π² * 1 = 36/π²
  convert (sq_mul_FReal_tendsto_zero.sub
      (mul_F₁E₄_re_tendsto_zero.const_mul (12 * π ^ (-1 : ℤ)))).add
    (E₄_re_resToImagAxis_tendsto_one.pow 2 |>.const_mul (36 * π ^ (-2 : ℤ))) using 1
  · ext s; ring
  · simp only [sq, mul_one, sub_zero, mul_zero, zero_add]

/-- H₂.resToImagAxis s (real part) tends to 0 as s → ∞. -/
lemma H₂_re_resToImagAxis_tendsto_zero :
    Tendsto (fun s : ℝ => (H₂.resToImagAxis s).re) atTop (nhds 0) :=
  (continuous_re.tendsto 0).comp H₂_resToImagAxis_tendsto_zero

/-- H₄.resToImagAxis s (real part) tends to 1 as s → ∞. -/
lemma H₄_re_resToImagAxis_tendsto_one :
    Tendsto (fun s : ℝ => (H₄.resToImagAxis s).re) atTop (nhds 1) :=
  (continuous_re.tendsto 1).comp H₄_resToImagAxis_tendsto_one

/-- The denominator expression D(s) = H₄(is)³ * (2*H₄(is)² + 5*H₂(is)*H₄(is) + 5*H₂(is)²)
tends to 2 as s → ∞. -/
lemma denominator_tendsto_at_infty :
    Tendsto (fun s : ℝ => (H₄.resToImagAxis s).re ^ 3 *
      (2 * (H₄.resToImagAxis s).re ^ 2 + 5 * (H₂.resToImagAxis s).re * (H₄.resToImagAxis s).re
        + 5 * (H₂.resToImagAxis s).re ^ 2)) atTop (nhds 2) := by
  -- H₄ → 1, H₂ → 0, so 1³ * (2*1² + 5*0*1 + 5*0²) = 2
  convert (H₄_re_resToImagAxis_tendsto_one.pow 3).mul
    ((H₄_re_resToImagAxis_tendsto_one.pow 2).const_mul 2 |>.add
      ((H₂_re_resToImagAxis_tendsto_zero.mul H₄_re_resToImagAxis_tendsto_one).const_mul 5 |>.add
        (H₂_re_resToImagAxis_tendsto_zero.pow 2 |>.const_mul 5))) using 1
  · ext; ring
  · norm_num

/-- G(1/s) = s^10 * (H₄(is))³ * (2(H₄(is))² + 5H₂(is)H₄(is) + 5(H₂(is))²) -/
lemma G_functional_eq_real {s : ℝ} (hs : 0 < s) :
    GReal (1 / s) = s ^ 10 * (H₄.resToImagAxis s).re ^ 3 *
      (2 * (H₄.resToImagAxis s).re ^ 2 + 5 * (H₂.resToImagAxis s).re * (H₄.resToImagAxis s).re
        + 5 * (H₂.resToImagAxis s).re ^ 2) := by
  -- From G_functional_equation' and the fact that H₂, H₄ are real on imaginary axis
  have hG := G_functional_equation' hs
  have hH₂_eq := ResToImagAxis.Real.eq_real_part H₂_imag_axis_real s
  have hH₄_eq := ResToImagAxis.Real.eq_real_part H₄_imag_axis_real s
  rw [hH₂_eq, hH₄_eq] at hG
  apply Complex.ofReal_injective
  convert hG using 1
  push_cast
  ring

/--
$\lim_{t \to 0^+} F(it) / G(it) = 18 / \pi^2$.

Proof outline (following blueprint Lemma 8.8):
1. Change of variables: lim_{t→0⁺} F(it)/G(it) = lim_{s→∞} F(i/s)/G(i/s)
2. Apply functional equations:
   - F(i/s) = s^12*F(is) - 12s^11/π*F₁(is)*E₄(is) + 36s^10/π²*E₄(is)²
   - G(i/s) = s^10*H₄(is)³*(2H₄(is)² + 5H₄(is)*H₂(is) + 5H₂(is)²)
3. Divide to get:
   F(i/s)/G(i/s) = [s²*F(is) - 12s/π*F₁(is)*E₄(is) + 36/π²*E₄(is)²] /
                   [H₄(is)³*(2H₄(is)² + 5H₄(is)*H₂(is) + 5H₂(is)²)]
4. As s→∞: F, F₁ are cusp forms (decay to 0), E₄(is)→1, H₂(is)→0, H₄(is)→1
5. Numerator → 36/π², denominator → 2, so limit = 18/π²
-/
theorem FmodG_rightLimitAt_zero :
    Tendsto FmodGReal (nhdsWithin 0 (Set.Ioi 0)) (nhds (18 * (π ^ (-2 : ℤ)))) := by
  -- Step 1: Establish the limit of numerator and denominator expressions
  have hNum := numerator_tendsto_at_infty
  have hDen := denominator_tendsto_at_infty
  -- Step 2: The denominator is eventually nonzero (since it tends to 2)
  have hDen_ne : ∀ᶠ s in atTop, (H₄.resToImagAxis s).re ^ 3 *
      (2 * (H₄.resToImagAxis s).re ^ 2 + 5 * (H₂.resToImagAxis s).re * (H₄.resToImagAxis s).re
        + 5 * (H₂.resToImagAxis s).re ^ 2) ≠ 0 := by
    have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
    exact hDen.eventually_ne h2_ne
  -- Step 3: Show FmodGReal(1/s) equals Num(s)/Den(s) for large s
  have hEq : ∀ᶠ s in atTop, FmodGReal (1/s) =
      (s ^ 2 * FReal s - 12 * π ^ (-1 : ℤ) * s * ((F₁ * E₄.toFun).resToImagAxis s).re
        + 36 * π ^ (-2 : ℤ) * (E₄.toFun.resToImagAxis s).re ^ 2) /
      ((H₄.resToImagAxis s).re ^ 3 *
        (2 * (H₄.resToImagAxis s).re ^ 2 + 5 * (H₂.resToImagAxis s).re * (H₄.resToImagAxis s).re
          + 5 * (H₂.resToImagAxis s).re ^ 2)) := by
    filter_upwards [eventually_gt_atTop 0, hDen_ne] with s hs hne
    have hF := F_functional_equation' hs
    have hG := G_functional_eq_real hs
    unfold FmodGReal
    rw [hG]
    have hs10_ne : s ^ 10 ≠ 0 := pow_ne_zero 10 (ne_of_gt hs)
    -- Convert complex values to real parts using the fact they're real on imaginary axis
    rw [ResToImagAxis.Real.eq_real_part
        (ResToImagAxis.Real.mul F₁_imag_axis_real E₄_imag_axis_real) s,
      ResToImagAxis.Real.eq_real_part E₄_imag_axis_real s] at hF
    -- Extract real equality from complex equality using ofReal_injective
    have hF_real_eq : FReal (1 / s) = s ^ 12 * FReal s
        - 12 * π ^ (-1 : ℤ) * s ^ 11 * ((F₁ * E₄.toFun).resToImagAxis s).re
        + 36 * π ^ (-2 : ℤ) * s ^ 10 * (E₄.toFun.resToImagAxis s).re ^ 2 := by
      apply Complex.ofReal_injective
      simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_zpow π]
      convert hF using 1
    rw [hF_real_eq]
    -- Factor out s^10 and cancel
    calc _ = s ^ 10 * (s ^ 2 * FReal s - 12 * π ^ (-1 : ℤ) * s *
          ((F₁ * E₄.toFun).resToImagAxis s).re +
        36 * π ^ (-2 : ℤ) * (E₄.toFun.resToImagAxis s).re ^ 2) /
        (s ^ 10 * ((H₄.resToImagAxis s).re ^ 3 *
        (2 * (H₄.resToImagAxis s).re ^ 2 + 5 * (H₂.resToImagAxis s).re * (H₄.resToImagAxis s).re
          + 5 * (H₂.resToImagAxis s).re ^ 2))) := by ring_nf
      _ = _ := mul_div_mul_left _ _ hs10_ne
  -- Step 4: Compute the limit using Tendsto.div
  have hlim := hNum.div hDen (by norm_num : (2 : ℝ) ≠ 0)
  -- Step 5: Convert limit at atTop for FmodGReal(1/s) to limit at nhdsWithin 0 for FmodGReal
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim ε hε
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hEq
  use 1 / max (max N M) 1
  refine ⟨one_div_pos.mpr (lt_of_lt_of_le one_pos (le_max_right _ _)), ?_⟩
  intro t ht_mem ht_dist
  simp only [Set.mem_Ioi] at ht_mem
  simp only [dist_zero_right, Real.norm_eq_abs, abs_of_pos ht_mem] at ht_dist
  -- t < 1/max(N, M, 1) implies 1/t > max(N, M, 1)
  have h1t : 1 / t > max (max N M) 1 := by
    rw [one_div, gt_iff_lt, ← one_div]
    calc max (max N M) 1 = 1 / (1 / max (max N M) 1) := by field_simp
      _ < 1 / t := one_div_lt_one_div_of_lt ht_mem ht_dist
  have h1t_N : 1 / t > N := lt_of_le_of_lt (le_max_left _ _) (lt_of_le_of_lt (le_max_left _ _) h1t)
  have h1t_M : 1 / t ≥ M :=
    le_of_lt (lt_of_le_of_lt (le_max_right N M) (lt_of_le_of_lt (le_max_left _ _) h1t))
  rw [show FmodGReal t = FmodGReal (1 / (1 / t)) by field_simp, hM (1 / t) h1t_M]
  simp only [Pi.div_apply] at hN
  convert hN (1 / t) (le_of_lt h1t_N) using 2
  field_simp [Real.pi_ne_zero]
  ring

/--
Main inequalities between $F$ and $G$ on the imaginary axis.
-/
theorem FG_inequality_1 {t : ℝ} (ht : 0 < t) :
    FReal t + 18 * (π ^ (-2 : ℤ)) * GReal t > 0 := by
  sorry

theorem FG_inequality_2 {t : ℝ} (ht : 0 < t) :
    FReal t - 18 * (π ^ (-2 : ℤ)) * GReal t < 0 := by
  sorry
