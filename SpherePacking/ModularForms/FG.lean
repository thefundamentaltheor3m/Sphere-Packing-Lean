import Architect
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Monotone.Defs

import SpherePacking.ModularForms.RamanujanIdentities
import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.Eisenstein
import SpherePacking.ModularForms.JacobiTheta

open Filter Complex
open scoped Real Manifold ArithmeticFunction.sigma UpperHalfPlane


/--
Definition of $F$ and $G$ and auxiliary functions for the inequality between them
on the imaginary axis.
-/
@[blueprint
  "def:FG-definition"
  (statement := /--
  Define two (quasi) modular forms as
  \begin{align}
      F(z) &= (E_2(z) E_4(z) - E_6(z))^2 \label{eqn:defF} \\
      G(z) &= H_2(z)^{3} (2 H_{2}(z)^{2} + 5 H_{2}(z) H_{4}(z) + 5 H_{4}(z)^{2}). \label{eqn:defG}
  \end{align}
  -/)]
noncomputable def F := (E₂ * E₄.toFun - E₆.toFun) ^ 2

@[blueprint
  "def:FG-definition"
  (statement := /--
  Define two (quasi) modular forms as
  \begin{align}
      F(z) &= (E_2(z) E_4(z) - E_6(z))^2 \label{eqn:defF} \\
      G(z) &= H_2(z)^{3} (2 H_{2}(z)^{2} + 5 H_{2}(z) H_{4}(z) + 5 H_{4}(z)^{2}). \label{eqn:defG}
  \end{align}
  -/)]
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
@[blueprint
  "lemma:FG-de"
  (statement := /--
  $F$ and $G$ satisfy the following differential equations:
  \begin{align}
      \partial_{12}\partial_{10} F - \frac{5}{6} E_{4} F &= 7200 \Delta (-E_{2}') \label{eqn:ddf} \\
      \partial_{12}\partial_{10} G - \frac{5}{6} E_{4} G &= -640 \Delta H_{2} \label{eqn:ddg}
  \end{align}
  -/)
  (proof := /--
  Both can be shown by direct computations.
  By Ramanujan's identities (Theorem \ref{thm:ramanujan-formula}) and the product rule of Serre
  derivatives (Theorem \ref{thm:serre-der-prod-rule}), we have
  \begin{align}
      \partial_{5} (E_2 E_4 - E_6) &= (E_2 E_4 - E_6)' - \frac{5}{12} E_2 (E_2 E_4 - E_6) \\
      &= \frac{E_2^2 - E_4}{12} \cdot E_4 + E_2 \cdot \frac{E_2 E_4 - E_6}{3} - \frac{E_2 E_6 -
      E_4^2}{2} - \frac{5}{12}E_2 (E_2 E_4 - E_6) \\
      &= -\frac{5}{12} (E_2 E_6 - E_4^2) \label{eqn:S5} \\
      \partial_{7} (E_2 E_6 - E_4^2) &= (E_2 E_6 - E_4^2)' - \frac{7}{12} E_2 (E_2 E_6 - E_4^2) \\
      &= \frac{E_2^2 - E_4}{12} \cdot E_6 + E_2 \cdot \frac{E_2 E_6 - E_4^2}{2} - 2 E_4 \cdot
      \frac{E_2 E_4 - E_6}{3} - \frac{7}{12} E_2 (E_2 E_6 - E_4^2) \\
      &= -\frac{7}{12} E_4 (E_2 E_4 - E_6) \label{eqn:S7}
  \end{align}
  and using these we can compute
  \begin{align}
      \partial_{10} F &= \partial_{10} (E_2 E_4 - E_6)^2 \\
      &= 2 (E_2 E_4 - E_6) \partial_{5} (E_2 E_4 - E_6) \\
      &= -\frac{6}{5} (E_2 E_4 - E_6) (E_2 E_6 - E_4^2), \\
      \partial_{12}\partial_{10} F &= -\frac{5}{6} \partial_{12} ((E_2 E_4 - E_6) (E_2 E_6 - E_4))
      \\
      &= -\frac{5}{6} (\partial_{5}(E_2 E_4 - E_6)) (E_2 E_6 - E_4^2) - \frac{5}{6} (E_2 E_4 - E_6)
      (\partial_{7} (E_2 E_6 - E_4)) \\
      &= \frac{25}{72} (E_2 E_6 - E_4^2)^2 + \frac{35}{72} E_4 (E_2 E_4 - E_6)^2, \\
      \partial_{12}\partial_{10}F - \frac{5}{6} E_4 F &= \frac{25}{72}(E_2 E_6 - E_4^2)^2 +
      \frac{35}{72} E_4 (E_2 E_4 - E_6)^2 - \frac{5}{6} E_4 (E_2 E_4 - E_6)^2 \\
      &= \frac{25}{72} ((E_2 E_6 - E_4^2)^2 - E_4 (E_2 E_4 - E_6)^2) \\
      &= \frac{25}{72} (- E_2^2 E_4^3 + E_2^2 E_6^2 + E_4^4 - E_4 E_6^3) \\
      &= -\frac{25}{72} (E_4^3 - E_6^2) (E_2^2 - E_4) \\
      &= 7200 \cdot \frac{E_4^3 - E_6^2}{1728} \cdot \frac{-E_2^2 + E_4}{12}\\
      &= 7200 \Delta (-E_2')
  \end{align}
  which proves \eqref{eqn:ddf}.
  Similarly, \eqref{eqn:ddg} can be proved using Proposition \ref{prop:theta-der} and Lemma
  \ref{lemma:lv1-lv2-identities}.
  -/)
  (latexEnv := "lemma")]
theorem MLDE_F : serre_D 12 (serre_D 10 F) = 5 * 6⁻¹ * F + 7200 * Δ_fun * negDE₂ := by
  ext x
  rw [negDE₂, Δ_fun, serre_D, serre_D, F_aux]
  unfold serre_D
  rw [F_aux]
  sorry

/--
Modular linear differential equation satisfied by $G$.
-/
@[blueprint "lemma:FG-de"]
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
@[blueprint
  "lemma:F-G-pos"
  (statement := /-- For all $t > 0$, we have $F(it) > 0$ and $G(it) > 0$. -/)
  (proof := /--
  By Ramanujan's identity \eqref{eqn:DE4}, we have $F(z) = 9 E_4'(z)^2$ and
  \begin{equation}
      F(it) = 9E_4'(it)^2 = 9 \left(240\sum_{n \geq 1} n \sigma_3(n) e^{-2 \pi n t} \right)^{2} > 0.
  \end{equation}
  $G(it) > 0$ follows from positivity of $H_2(it)$ and $H_4(it)$ (Lemma \ref{cor:theta-pos}).
  -/)
  (latexEnv := "lemma")]
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
@[blueprint
  "lemma:F-G-pos"
  (statement := /-- For all $t > 0$, we have $F(it) > 0$ and $G(it) > 0$. -/)
  (proof := /--
  By Ramanujan's identity \eqref{eqn:DE4}, we have $F(z) = 9 E_4'(z)^2$ and
  \begin{equation}
      F(it) = 9E_4'(it)^2 = 9 \left(240\sum_{n \geq 1} n \sigma_3(n) e^{-2 \pi n t} \right)^{2} > 0.
  \end{equation}
  $G(it) > 0$ follows from positivity of $H_2(it)$ and $H_4(it)$ (Lemma \ref{cor:theta-pos}).
  -/)
  (latexEnv := "lemma")]
theorem F_imag_axis_pos : ResToImagAxis.Pos F := by
  rw [F_eq_nine_DE₄_sq]
  have _ := DE₄_imag_axis_pos
  fun_prop (disch := positivity)

/--
`F(it)` is real for all `t > 0`.
Blueprint: Follows from E₂, E₄, E₆ having real values on the imaginary axis.
-/
theorem F_imag_axis_real : ResToImagAxis.Real F := F_imag_axis_pos.1

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
@[blueprint
  "cor:MLDE-pos"
  (statement := /--
  \eqref{eqn:ddf} (resp. \eqref{eqn:ddg}) is positive (resp. negative) on the (positive) imaginary
  axis.
  -/)
  (proof := /--
  From \eqref{eqn:E2} and Lemma \ref{cor:disc-pos},
  \ifplastex
  \begin{equation*}
      7200 (-E_2'(it)) \Delta(it) = 7200 \cdot 24 \left(\sum_{n \ge 1} n \sigma_1(n) e^{-2 \pi n
      t}\right) \cdot \Delta(it) > 0.
  \end{equation*}
  \else
  \begin{equation}
      7200 (-E_2'(it)) \Delta(it) = 7200 \cdot 24 \left(\sum_{n \ge 1} n \sigma_1(n) e^{-2 \pi n
      t}\right) \cdot \Delta(it) > 0. \notag
  \end{equation}
  \fi
  Negativity of \eqref{eqn:ddg}, i.e. $-640 \Delta(it) H_2(it) < 0$ follows from Corollary
  \ref{cor:theta-pos} and \ref{cor:disc-pos}.
  -/)
  (proofUses := ["cor:disc-pos", "cor:theta-pos"])
  (latexEnv := "corollary")]
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
@[blueprint
  "prop:Qdec"
  (statement := /-- The function $t \mapsto Q(t)$ is monotone decreasing. -/)
  (proof := /--
  It is enough to show that
  \begin{align}
      \frac{\dd}{\dd t} \left(\frac{F(it)}{G(it)}\right) < 0 &\Leftrightarrow (- 2\pi)
      \frac{F'(it)G(it) - F(it) G'(it)}{G(it)^{2}} < 0 \\
      &\Leftrightarrow F'(it) G(it) - F(it) G'(it) > 0 \\
      &\Leftrightarrow (\partial_{10}F)(it) G(it) - F(it) (\partial_{10}G)(it) > 0.
  \end{align}
  Let $\mathcal{L}_{1, 0} := (\partial_{10}F) G - F (\partial_{10} G) = F'G - FG'$.
  Then
  \begin{align}
  \frac{\mathcal{L}_{1, 0}}{FG} = \frac{F'G - FG'}{FG} = \frac{F'}{F} - \frac{G'}{G}
  \end{align}
  The vanishing order of $F$ and $G$ at the infinity are $2$ and $\frac{3}{2}$ respectively, so by
  Lemma \ref{lemma:log-der-inf}, we have
  \begin{align}
      \lim_{t \to \infty} \frac{\mathcal{L}_{1, 0}(it)}{F(it) G(it)} = \lim_{t \to \infty}
      \left(\frac{F'(it)}{F(it)} - \frac{G'(it)}{G(it)}\right) = 2 - \frac{3}{2} = \frac{1}{2} > 0
  \end{align}
  so $\mathcal{L}_{1, 0}(it) > 0$ for sufficiently large $t$.
  Its Serre derivative $\partial_{22} \mathcal{L}_{1, 0}$ is positive by Corollary
  \ref{cor:MLDE-pos}:
  \begin{align}
      \partial_{22} \mathcal{L}_{1, 0} = (\partial_{12} \partial_{10} F) G - F
      (\partial_{12}\partial_{10} G)
      = \Delta (7200 (-E_{2}') G + 640 H_2 F) > 0.
  \end{align}
  Hence $\mathcal{L}_{1, 0}(it) > 0$ by Theorem \ref{thm:anti-serre-der-pos}, and the monotonicity
  follows.
  -/)
  (proofUses := ["cor:MLDE-pos", "thm:anti-serre-der-pos", "lemma:log-der-inf"])
  (latexEnv := "proposition")]
theorem FmodG_antitone : AntitoneOn FmodGReal (Set.Ioi 0) := by
  sorry

/--
$\lim_{t \to 0^+} F(it) / G(it) = 18 / \pi^2$.
-/
@[blueprint
  "lemma:Qlim"
  (statement := /--
  We have
  \begin{equation}
      \lim_{t \to 0^+} Q(t) = \frac{18}{\pi^2}.
  \end{equation}
  -/)
  (proof := /--
  We have
  \begin{equation}
      \lim_{t \to 0^+} Q(t) = \lim_{t \to 0^+} \frac{F(it)}{G(it)} = \lim_{t \to \infty}
      \frac{F(i/t)}{G(i/t)}.
  \end{equation}
  By using the transformation laws of Eisenstein series \eqref{eqn:E2-S-transform},
  \eqref{eqn:Ek-trans-S} (for $k = 4, 6$) and the thetanull functions, \eqref{eqn:H2-transform-S},
  \eqref{eqn:H4-transform-S}, we get
  \begin{align}
      F\left(\frac{i}{t}\right) &= t^{12} F(it) - \frac{12t^{11}}{\pi} (E_2(it)E_4(it) -
      E_6(it))E_4(it) + \frac{36t^{10}}{\pi^2}E_4(it)^2, \\
      G\left(\frac{i}{t}\right) &= t^{10} H_{4}(it)^{3}(2H_{4}(it)^{2} + 5 H_{4}(it)H_{2}(it) + 5
      H_{2}(it)^{2}).
  \end{align}
  Since $F$, $E_2 E_4 - E_6$ and $H_2$ are cusp forms, we have $\lim_{t \to \infty}t^k A(it) = 0$
  when $A(z)$ is one of these forms and $k \geq 0$.
  From $\lim_{t \to \infty} E_4(it) = 1 = \lim_{t \to \infty}H_{4}(it)$, we get
  \begin{align}
      \lim_{t \to \infty} \frac{F(i/t)}{G(i/t)}
      &= \lim_{t \to \infty} \frac{t^{12} F(it) - \frac{12t^{11}}{\pi} (E_2(it)E_4(it) -
      E_6(it))E_4(it) + \frac{36t^{10}}{\pi^2}E_4(it)^2}{t^{10} H_{4}(it)^{3}(2H_{4}(it)^{2} + 5
      H_{4}(it)H_{2}(it) + 5 H_{2}(it)^{2})} \\
      &= \lim_{t \to \infty} \frac{t^{2} F(it) - \frac{12t}{\pi} (E_2(it)E_4(it) - E_6(it))E_4(it) +
      \frac{36}{\pi^2}E_4(it)^2}{H_{4}(it)^{3}(2H_{4}(it)^{2} + 5 H_{4}(it)H_{2}(it) + 5
      H_{2}(it)^{2})} \\
      &= \frac{18}{\pi^2}.
  \end{align}
  -/)
  (proofUses := ["lemma:E2-transform-S", "lemma:theta-transform-S-T", "lemma:Ek-is-modular-form"])
  (latexEnv := "lemma")]
theorem FmodG_rightLimitAt_zero :
    Tendsto FmodGReal (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin (18 * (π ^ (-2 : ℤ))) Set.univ) := by
  sorry

/--
Main inequalities between $F$ and $G$ on the imaginary axis.
-/
@[blueprint
  "cor:ineqAnew"
  (statement := /-- \eqref{eqn:ineqAnew} holds. -/)
  (proof := /-- This directly follows from Lemma \ref{lemma:F-G-pos}. -/)
  (proofUses := ["lemma:F-G-pos"])
  (latexEnv := "corollary")]
theorem FG_inequality_1 {t : ℝ} (ht : 0 < t) :
    FReal t + 18 * (π ^ (-2 : ℤ)) * GReal t > 0 := by
  sorry

@[blueprint
  "cor:ineqBnew"
  (statement := /-- \eqref{eqn:ineqBnew} holds. -/)
  (proof := /--
  \begin{equation}
      \frac{F(it)}{G(it)} = Q(t) < \lim_{u \to 0^+} Q(u) = \frac{18}{\pi^2}
  \end{equation}
  and by Lemma \ref{lemma:F-G-pos}, \eqref{eqn:ineqBnew} follows.
  -/)
  (proofUses := [FmodG_rightLimitAt_zero, FmodG_antitone, "lemma:F-G-pos"])
  (latexEnv := "corollary")]
theorem FG_inequality_2 {t : ℝ} (ht : 0 < t) :
    FReal t - 18 * (π ^ (-2 : ℤ)) * GReal t < 0 := by
  sorry
