import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Monotone.Defs

import SpherePacking.ModularForms.RamanujanIdentities
import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.Eisenstein
import SpherePacking.ModularForms.JacobiTheta
import SpherePacking.ModularForms.DimensionFormulas
import SpherePacking.ModularForms.QExpansion
import SpherePacking.ModularForms.summable_lems

open Filter Complex
open UpperHalfPlane (atImInfty ofComplex ofComplex_apply ofComplex_apply_of_im_pos coe_mk_subtype
  eventuallyEq_coe_comp_ofComplex isOpen_upperHalfPlaneSet)
open scoped Real Manifold CongruenceSubgroup ArithmeticFunction.sigma UpperHalfPlane


/--
Definition of $F$ and $G$ and auxiliary functions for the inequality between them
on the imaginary axis.
-/
noncomputable def F := (E₂ * E₄.toFun - E₆.toFun) ^ 2

noncomputable def G := H₂ ^ 3 * ((2 : ℝ) • H₂ ^ 2 + (5 : ℝ) • H₂ * H₄ + (5 : ℝ) • H₄ ^ 2)

noncomputable def negDE₂ := - (D E₂)

noncomputable def Δ_fun := 1728⁻¹ * (E₄.toFun ^ 3 - E₆.toFun ^ 2)

/-- The discriminant Δ_fun = 1728⁻¹(E₄³ - E₆²) equals the standard discriminant Δ. -/
lemma Δ_fun_eq_Δ : Δ_fun = Δ := by
  funext z
  have hds : (((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3) 12) = E₄.mul (E₄.mul E₄) := by
    ext w
    rw [pow_three, @DirectSum.of_mul_of, DirectSum.of_mul_of]
    simp
    rw [DFunLike.congr_arg (GradedMonoid.GMul.mul E₄ (GradedMonoid.GMul.mul E₄ E₄)) rfl]
    rfl
  have hd6 : (((DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12) = E₆.mul E₆ := by
    ext w
    rw [pow_two, @DirectSum.of_mul_of]
    simp
    rw [DFunLike.congr_arg (GradedMonoid.GMul.mul E₆ E₆) rfl]
    rfl
  have h := congr_fun (congr_arg (fun f => f.toFun) Delta_E4_E6_eq) z
  have hE4E6 : Delta_E4_E6_aux z = 1728⁻¹ * (E₄ z ^ 3 - E₆ z ^ 2) := by
    simp only [ModForm_mk, ModularForm.toFun_eq_coe, one_div, DirectSum.sub_apply] at h
    simp only [hds, hd6] at h
    simp only [pow_three, pow_two] at h ⊢
    convert h using 2
  calc
    Δ_fun z = 1728⁻¹ * (E₄ z ^ 3 - E₆ z ^ 2) := by
      simp [Δ_fun, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    _ = Δ z := by simp [← hE4E6, ← Delta_E4_eqn, Delta_apply]

noncomputable def L₁₀ := (D F) * G - F * (D G)

lemma L₁₀_eq_FD_G_sub_F_DG (z : ℍ) : L₁₀ z = D F z * G z - F z * D G z := rfl

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
  have h : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₂ * E₄.toFun - E₆.toFun) :=
    MDifferentiable.sub (MDifferentiable.mul E₂_holo' E₄.holo') E₆.holo'
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

theorem SerreF_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D 10 F) :=
  serre_D_differentiable F_holo

theorem SerreG_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D 10 G) :=
  serre_D_differentiable G_holo

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

/-- `D(f⁴) = 4f³·Df`, using `D_sq` twice through the `(f²)²` factorization. -/
private lemma D_pow4_eq (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (z : ℍ) :
    D (fun w => f w ^ 4) z = 4 * (f z) ^ 3 * D f z := by
  have hfsq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ^ 2) := by rw [pow_two]; exact hf.mul hf
  have h_eq : (fun w => f w ^ 4) = (f ^ 2) ^ 2 := by ext w; simp only [Pi.pow_apply]; ring
  have h1 : D ((f ^ 2) ^ 2) z = 2 * (f z) ^ 2 * D (f ^ 2) z := by
    simpa [Pi.mul_apply, Pi.pow_apply] using congrFun (D_sq (f ^ 2) hfsq) z
  have h2 : D (f ^ 2) z = 2 * f z * D f z := by
    simpa [Pi.mul_apply] using congrFun (D_sq f hf) z
  rw [h_eq, h1, h2]; ring

/-- Pointwise log-derivative of a product: `D(f·h)/(f·h) = Df/f + Dh/h`. -/
private lemma logderiv_mul_eq (f h : ℍ → ℂ)
    (hf_md : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hh_md : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h)
    (z : ℍ) (hf_ne : f z ≠ 0) (hh_ne : h z ≠ 0) :
    D (f * h) z / (f z * h z) = D f z / f z + D h z / h z := by
  rw [congrFun (D_mul f h hf_md hh_md) z]
  simp only [Pi.mul_apply, Pi.add_apply]
  field_simp [hf_ne, hh_ne]

/-- `(a / b).re = a.re / b.re` when both `a` and `b` are real-valued complex numbers. -/
private lemma div_re_of_im_eq_zero {a b : ℂ} (ha : a.im = 0) (hb : b.im = 0) :
    (a / b).re = a.re / b.re := by
  conv_lhs => rw [show a = ↑a.re from Complex.ext rfl (by simp [ha]),
    show b = ↑b.re from Complex.ext rfl (by simp [hb]), ← Complex.ofReal_div]
  exact Complex.ofReal_re _

/- Positivity of (quasi)modular forms on the imaginary axis. -/

lemma Δ_fun_imag_axis_pos : ResToImagAxis.Pos Δ_fun := Δ_fun_eq_Δ ▸ Delta_imag_axis_pos

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
  simpa [pow_zero, one_mul] using sigma_qexp_summable_generic 0 1 z

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
    _ = _ := by rw [hD_one, hD_smul, zero_add, hDf]

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
lemma DE₄_imag_axis_real : ResToImagAxis.Real (D E₄.toFun) :=
  D_real_of_real E₄_imag_axis_real E₄.holo'

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
  have htsum_pos := Summable.tsum_pos hsum_re (fun n => (hpos n).le) 1 (hpos 1)
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
lemma negDE₂_imag_axis_real : ResToImagAxis.Real negDE₂ :=
  ResToImagAxis.Real.neg (D_real_of_real E₂_imag_axis_real E₂_holo')

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
  have htsum_pos := Summable.tsum_pos hsum_re (fun n => (hpos n).le) 1 (hpos 1)
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

/-!
### Serre Derivative Positivity of L₁,₀

We compute `∂₂₂ L₁,₀` explicitly via the modular linear differential equations for F and G,
and show it is positive on the imaginary axis.
-/

/-- `∂₂₂ L₁,₀ = Δ(7200(-E₂')G + 640H₂F)` on the upper half-plane.
Blueprint: Follows from differential equations (65) and (66). -/
private theorem serre_D_L₁₀_eq (z : ℍ) :
    SerreDer_22_L₁₀ z = Δ z * (7200 * (-(D E₂ z)) * G z + 640 * H₂ z * F z) := by
  have hF_z := congrFun MLDE_F z
  have hG_z := congrFun MLDE_G z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, negDE₂, Pi.neg_apply, Δ_fun_eq_Δ,
    Pi.ofNat_apply, Pi.inv_apply] at hF_z hG_z
  have h := congrFun SerreDer_22_L₁₀_SerreDer z
  simp only [Pi.mul_apply, Pi.sub_apply] at h
  rw [h, hF_z, hG_z]
  ring

/-- `∂₂₂ L₁,₀(it) > 0` for all `t > 0`.
Blueprint: Corollary 8.9 - both terms in the expression are positive. -/
private theorem serre_D_L₁₀_pos_imag_axis : ResToImagAxis.Pos SerreDer_22_L₁₀ := by
  have h_eq : SerreDer_22_L₁₀ = Δ * ((7200 : ℝ) • (negDE₂ * G) + (640 : ℝ) • (H₂ * F)) := by
    ext z; simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
      Complex.real_smul, serre_D_L₁₀_eq z, negDE₂]; push_cast; ring
  rw [h_eq]
  have := Delta_imag_axis_pos
  have := negDE₂_imag_axis_pos
  have := G_imag_axis_pos
  have := H₂_imag_axis_pos
  have := F_imag_axis_pos
  fun_prop (disch := positivity)

lemma SerreDer_22_L₁₀_real : ResToImagAxis.Real SerreDer_22_L₁₀ :=
  serre_D_L₁₀_pos_imag_axis.1

lemma SerreDer_22_L₁₀_pos : ResToImagAxis.Pos SerreDer_22_L₁₀ :=
  serre_D_L₁₀_pos_imag_axis

/-!
## Asymptotic Analysis of F at Infinity

Vanishing orders and log-derivative limits for the F-side analysis.
These are used to establish `L₁₀_eventuallyPos` (large-t positivity of L₁,₀).
-/

section AsymptoticAnalysis

/-- If `‖a m‖ ≤ (m+1)^p` then `∑ a(m) q^m → a(0)` as `im(z) → ∞`. -/
private theorem qexp_tendsto_of_poly_bound {a : ℕ → ℂ} {p : ℕ}
    (hbound : ∀ m, ‖a m‖ ≤ ((m + 1 : ℕ) : ℝ) ^ p) :
    Filter.Tendsto (fun z : ℍ => ∑' m : ℕ, a m * cexp (2 * π * I * z * m))
      atImInfty (nhds (a 0)) := by
  simpa using (QExp.tendsto_nat a (Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun m => mul_le_mul_of_nonneg_right (hbound m) (Real.exp_nonneg _))
    (by
      push_cast [Nat.cast_add, Nat.cast_one] at hbound ⊢
      exact summable_pow_shift p)))

/-- Reindex σ₃ q-expansion from ℕ+ to ℕ using n ↦ m+1. -/
private lemma sigma3_qexp_reindex_pnat_nat (z : ℍ) :
    ∑' n : ℕ+, ↑n * ↑(ArithmeticFunction.sigma 3 n) *
      cexp (2 * π * Complex.I * (n - 1) * z) =
    ∑' m : ℕ, ↑(m + 1) * ↑(ArithmeticFunction.sigma 3 (m + 1)) *
      cexp (2 * π * Complex.I * m * z) := by
  simpa [tsum_pnat_eq_tsum_succ3] using
    (tsum_pnat_eq_tsum_succ3 (f := fun n : ℕ => (n : ℂ) * (↑(ArithmeticFunction.sigma 3 n) : ℂ) *
      cexp (2 * π * Complex.I * ((n : ℂ) - 1) * z)))

/-- If f/g → c ≠ 0, then eventually f ≠ 0. -/
private lemma eventually_ne_zero_of_tendsto_div {f g : ℍ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (h : Filter.Tendsto (fun z => f z / g z) atImInfty (nhds c)) :
    ∀ᶠ z : ℍ in atImInfty, f z ≠ 0 := by
  filter_upwards [h.eventually_ne hc] with z hz hf
  exact hz (by simp [hf])

/-- (E₂E₄ - E₆) / q → 720 as im(z) → ∞. -/
theorem E₂E₄_sub_E₆_div_q_tendsto :
    Filter.Tendsto (fun z : ℍ => (E₂ z * E₄ z - E₆ z) / cexp (2 * π * I * z))
      atImInfty (nhds (720 : ℂ)) := by
  have h_rw : ∀ z : ℍ, E₂ z * E₄ z - E₆ z =
      720 * ∑' n : ℕ+, ↑n * ↑(ArithmeticFunction.sigma 3 n) *
        cexp (2 * π * Complex.I * n * z) := E₂_mul_E₄_sub_E₆
  have h_eq : ∀ z : ℍ,
      (E₂ z * E₄ z - E₆ z) / cexp (2 * π * Complex.I * z) =
      720 * (∑' n : ℕ+, ↑n * ↑(ArithmeticFunction.sigma 3 n) *
        cexp (2 * π * Complex.I * (n - 1) * z)) := by
    intro z
    rw [h_rw z, mul_div_assoc, ← tsum_div_const]
    congr 1; apply tsum_congr; intro n
    rw [mul_div_assoc, ← Complex.exp_sub]; congr 2; ring
  simp_rw [h_eq, sigma3_qexp_reindex_pnat_nat]
  set a : ℕ → ℂ := fun m => ↑(m + 1) * ↑(ArithmeticFunction.sigma 3 (m + 1)) with ha
  have ha0 : a 0 = 1 := by simp [ha, ArithmeticFunction.sigma_one]
  have hbound : ∀ m, ‖a m‖ ≤ ((m + 1 : ℕ) : ℝ) ^ 5 := fun m => by
    simp only [ha, norm_mul, Complex.norm_natCast]
    calc (↑(m + 1) : ℝ) * ↑(ArithmeticFunction.sigma 3 (m + 1))
        ≤ (↑(m + 1) : ℝ) * (↑(m + 1) : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast sigma_bound 3 (m + 1))
            (Nat.cast_nonneg _)
      _ = _ := by ring
  have h_eq2 : ∀ z : ℍ,
      ∑' m : ℕ, ↑(m + 1) * ↑(ArithmeticFunction.sigma 3 (m + 1)) *
        cexp (2 * π * Complex.I * m * z) =
      ∑' m : ℕ, a m * cexp (2 * π * Complex.I * z * m) := by
    intro z; apply tsum_congr; intro m; simp only [ha]; ring_nf
  simp_rw [h_eq2]
  simpa [ha0] using (qexp_tendsto_of_poly_bound hbound).const_mul (720 : ℂ)

/-- `Θ₂(z) / exp(πiz/4) → 2` as `im(z) → ∞`. -/
private theorem Θ₂_div_exp_tendsto :
    Filter.Tendsto (fun z : ℍ => Θ₂ z / cexp (π * Complex.I * z / 4))
      atImInfty (nhds (2 : ℂ)) := by
  convert jacobiTheta₂_half_mul_apply_tendsto_atImInfty using 1
  ext z
  rw [Θ₂_as_jacobiTheta₂]
  field_simp [Complex.exp_ne_zero]

/-- `H₂(z) / exp(πiz) → 16` as `im(z) → ∞`. -/
private theorem H₂_div_exp_tendsto :
    Filter.Tendsto (fun z : ℍ => H₂ z / cexp (π * Complex.I * z))
      atImInfty (nhds (16 : ℂ)) := by
  have h_eq : ∀ z : ℍ, H₂ z / cexp (π * I * z) =
      (Θ₂ z / cexp (π * I * z / 4)) ^ 4 := fun z => by
    simp only [H₂, div_pow, ← Complex.exp_nat_mul]; congr 2; ring
  simp_rw [h_eq]; convert Θ₂_div_exp_tendsto.pow 4; norm_num

private lemma Θ₂_eventually_ne_zero : ∀ᶠ z : ℍ in atImInfty, Θ₂ z ≠ 0 :=
  eventually_ne_zero_of_tendsto_div (by norm_num : (2 : ℂ) ≠ 0) Θ₂_div_exp_tendsto

private lemma H₂_eventually_ne_zero : ∀ᶠ z : ℍ in atImInfty, H₂ z ≠ 0 :=
  eventually_ne_zero_of_tendsto_div (by norm_num : (16 : ℂ) ≠ 0) H₂_div_exp_tendsto

/-- The vanishing order of F at infinity is 2.
Blueprint: F = 720² * q² * (1 + O(q)), so F / q² → 720² as im(z) → ∞. -/
theorem F_vanishing_order :
    Filter.Tendsto (fun z : ℍ => F z / cexp (2 * π * Complex.I * 2 * z))
      atImInfty (nhds (720 ^ 2 : ℂ)) := by
  have h_exp_eq : ∀ z : ℍ, cexp (2 * π * I * 2 * z) = cexp (2 * π * I * z) ^ 2 := by
    intro z; rw [← Complex.exp_nat_mul]; congr 1; ring
  have h_F_eq : ∀ z : ℍ, F z / cexp (2 * π * I * 2 * z) =
      ((E₂ z * E₄ z - E₆ z) / cexp (2 * π * I * z)) ^ 2 := by
    intro z
    simp only [F, h_exp_eq, sq, div_mul_div_comm, Pi.mul_apply, Pi.sub_apply,
      ModularForm.toFun_eq_coe]
  simp_rw [h_F_eq]
  exact E₂E₄_sub_E₆_div_q_tendsto.pow 2

/-- D(E₂E₄ - E₆) = 720 * ∑ n²·σ₃(n)·qⁿ.
Key for the log-derivative limit: `(D F)/F → 2` as `z → i∞`. -/
theorem D_diff_qexp (z : ℍ) :
    D (fun w => E₂ w * E₄ w - E₆ w) z =
      720 * ∑' n : ℕ+, (↑↑n : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) ↑n) *
        cexp (2 * ↑Real.pi * Complex.I * ↑n * z) := by
  have h_eq : ∀ w : ℍ, E₂ w * E₄ w - E₆ w =
      720 * ∑' (n : ℕ+), ↑n * ↑(σ 3 n) * cexp (2 * π * I * ↑n * w) := E₂_mul_E₄_sub_E₆
  let a : ℕ+ → ℂ := fun n => ↑n * ↑(σ 3 n)
  have norm_a_le : ∀ n : ℕ+, ‖a n‖ ≤ (n : ℝ)^5 := fun n => by
    simp only [a, Complex.norm_mul, Complex.norm_natCast]
    calc (n : ℝ) * ↑(σ 3 ↑n) ≤ (n : ℝ) * (n : ℝ)^4 := by
           gcongr; exact_mod_cast sigma_bound 3 n
       _ = (n : ℝ)^5 := by ring
  have hsum : Summable (fun n : ℕ+ => a n * cexp (2 * π * I * ↑n * ↑z)) := by
    simpa [pow_one] using sigma_qexp_summable_generic 1 3 z
  have hsum_deriv := qexp_deriv_bound_of_coeff_bound norm_a_le
  let b : ℕ+ → ℂ := fun n => 720 * (↑n * ↑(σ 3 n))
  have h_eq' : ∀ w : ℍ, E₂ w * E₄ w - E₆ w =
      ∑' (n : ℕ+), b n * cexp (2 * π * I * ↑n * w) :=
    fun w => by rw [h_eq]; simp only [b, ← tsum_mul_left]; congr 1; funext n; ring
  have hsum' : Summable (fun n : ℕ+ => b n * cexp (2 * π * I * ↑n * ↑z)) := by
    convert hsum.mul_left 720 using 1; funext n; simp only [b]; ring
  have hsum_deriv' : ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ (n : ℕ+) (k : K), ‖b n * (2 * π * I * ↑n) *
        cexp (2 * π * I * ↑n * k.1)‖ ≤ u n := by
    intro K hK_sub hK_compact
    obtain ⟨u, hu_sum, hu_bound⟩ := hsum_deriv K hK_sub hK_compact
    refine ⟨fun n => 720 * u n, hu_sum.mul_left 720, fun n k => ?_⟩
    calc ‖b n * (2 * π * I * ↑n) * cexp (2 * π * I * ↑n * k.1)‖
        = 720 * ‖a n * (2 * π * I * ↑n) * cexp (2 * π * I * ↑n * k.1)‖ := by
          simp only [b, a, norm_mul, Complex.norm_ofNat]; ring
      _ ≤ 720 * u n := mul_le_mul_of_nonneg_left (hu_bound n k) (by norm_num)
  have hD := D_qexp_tsum_pnat b z hsum' hsum_deriv'
  calc D (fun w => E₂ w * E₄ w - E₆ w) z
      = D (fun w => ∑' (n : ℕ+), b n * cexp (2 * π * I * ↑n * w)) z := by
        congr 1; ext w; exact h_eq' w
    _ = ∑' (n : ℕ+), (n : ℂ) * b n * cexp (2 * π * I * ↑n * z) := hD
    _ = 720 * ∑' (n : ℕ+), (n : ℂ) ^ 2 * ↑(σ 3 n) * cexp (2 * π * I * ↑n * z) := by
        simp only [b, ← tsum_mul_left, sq]; congr 1; funext n; ring

/-- D(E₂E₄ - E₆) / q → 720. -/
private theorem D_diff_div_q_tendsto :
    Filter.Tendsto (fun z : ℍ => D (fun w => E₂ w * E₄ w - E₆ w) z /
      cexp (2 * π * Complex.I * z))
      atImInfty (nhds (720 : ℂ)) := by
  have h_rw : ∀ z : ℍ, D (fun w => E₂ w * E₄ w - E₆ w) z =
      720 * ∑' n : ℕ+, (↑↑n : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) ↑n) *
        cexp (2 * ↑Real.pi * Complex.I * ↑n * z) := D_diff_qexp
  simp_rw [h_rw]
  have h_eq : ∀ z : ℍ,
      (720 * ∑' n : ℕ+, (↑↑n : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) ↑n) *
        cexp (2 * ↑Real.pi * Complex.I * ↑n * z)) / cexp (2 * π * I * z) =
      720 * (∑' n : ℕ+, (↑↑n : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) ↑n) *
        cexp (2 * π * I * (↑n - 1) * z)) := by
    intro z
    rw [mul_div_assoc, ← tsum_div_const]
    congr 1; apply tsum_congr; intro n
    rw [mul_div_assoc, ← Complex.exp_sub]
    congr 2; ring
  simp_rw [h_eq]
  have h_reindex : ∀ z : ℍ,
      ∑' n : ℕ+, (↑↑n : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) ↑n) *
        cexp (2 * π * I * (↑n - 1) * z) =
      ∑' m : ℕ, (↑(m + 1) : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) (m + 1)) *
        cexp (2 * π * I * m * z) := by
    intro z
    rw [← Equiv.tsum_eq (Equiv.pnatEquivNat)]
    apply tsum_congr; intro m
    simp only [Equiv.pnatEquivNat_apply, PNat.natPred_add_one]
    congr 2
    simp only [← PNat.natPred_add_one m, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  simp_rw [h_reindex]
  set a : ℕ → ℂ := fun m =>
    (↑(m + 1) : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) (m + 1)) with ha_def
  have ha0 : a 0 = 1 := by simp [ha_def, ArithmeticFunction.sigma_one]
  have hbound : ∀ m, ‖a m‖ ≤ ((m + 1 : ℕ) : ℝ) ^ 6 := fun m => by
    simp only [ha_def, norm_mul, Complex.norm_natCast, Complex.norm_pow]
    calc (↑(m + 1) : ℝ) ^ 2 * ↑(ArithmeticFunction.sigma 3 (m + 1))
        ≤ (↑(m + 1) : ℝ) ^ 2 * (↑(m + 1) : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast sigma_bound 3 (m + 1))
            (pow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by ring
  have h_eq2 : ∀ z : ℍ,
      ∑' m : ℕ, (↑(m + 1) : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) (m + 1)) *
        cexp (2 * π * I * m * z) =
      ∑' m : ℕ, a m * cexp (2 * π * I * z * m) := fun z => by
    simpa [ha_def] using tsum_congr (fun m => by ring_nf)
  simp_rw [h_eq2]
  simpa [ha0] using (qexp_tendsto_of_poly_bound hbound).const_mul (720 : ℂ)

/-- `(D F)/F → 2` as `im(z) → ∞`.
The log-derivative limit, following from F having vanishing order 2. -/
theorem D_F_div_F_tendsto :
    Filter.Tendsto (fun z : ℍ => D F z / F z) atImInfty (nhds (2 : ℂ)) := by
  set f : ℍ → ℂ := fun z => E₂ z * E₄.toFun z - E₆.toFun z with hf_def
  have hF_eq : ∀ z, F z = (f z) ^ 2 := fun z => by
    simp only [F, hf_def, sq, Pi.mul_apply, Pi.sub_apply, ModularForm.toFun_eq_coe]
  have hf_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
    apply MDifferentiable.sub
    · exact MDifferentiable.mul E₂_holo' E₄.holo'
    · exact E₆.holo'
  have hDF_eq : ∀ z, D F z = 2 * f z * D f z := fun z => by
    have hF_eq' : F = f ^ 2 := funext fun w => by simp [F, hf_def, sq]
    rw [hF_eq']
    exact congr_fun (D_sq f hf_holo) z
  have hDF_div_eq : ∀ z, F z ≠ 0 → D F z / F z = 2 * (D f z / f z) := fun z hFz => by
    have hfz : f z ≠ 0 := fun h => hFz (by simp [hF_eq, h])
    rw [hDF_eq z, hF_eq z, sq]; field_simp [hfz]
  have hf_div_q : Filter.Tendsto (fun z : ℍ => f z / cexp (2 * π * Complex.I * z))
      atImInfty (nhds (720 : ℂ)) :=
    E₂E₄_sub_E₆_div_q_tendsto.congr fun z => by simp only [hf_def, ModularForm.toFun_eq_coe]
  have hDf_div_q : Filter.Tendsto (fun z : ℍ => D f z / cexp (2 * π * Complex.I * z))
      atImInfty (nhds (720 : ℂ)) := D_diff_div_q_tendsto
  have h_720_ne : (720 : ℂ) ≠ 0 := by norm_num
  have hDf_div_f : Filter.Tendsto (fun z : ℍ => D f z / f z) atImInfty (nhds 1) := by
    have h_eq : ∀ z : ℍ, D f z / f z = (D f z / cexp (2 * π * Complex.I * z)) /
        (f z / cexp (2 * π * Complex.I * z)) := fun z => by field_simp [Complex.exp_ne_zero]
    simp_rw [h_eq, show (1 : ℂ) = 720 / 720 from by norm_num]
    exact hDf_div_q.div hf_div_q h_720_ne
  have h_F_ne := eventually_ne_zero_of_tendsto_div
    (by norm_num : (720^2 : ℂ) ≠ 0) F_vanishing_order
  simpa using (hDf_div_f.const_mul (2 : ℂ)).congr' (by
    filter_upwards [h_F_ne] with z hFz; exact (hDF_div_eq z hFz).symm)

/-!
### G-Side Asymptotic Analysis

Vanishing order and log-derivative limits for G, leading to eventual positivity of L₁,₀.
-/

/-- G / q^(3/2) → 20480 as im(z) → ∞. Here q^(3/2) = exp(2πi · (3/2) · z). -/
theorem G_vanishing_order :
    Filter.Tendsto (fun z : ℍ => G z / cexp (2 * π * I * (3/2) * z))
      atImInfty (nhds (20480 : ℂ)) := by
  simp only [show ∀ z : ℍ, cexp (2 * π * I * (3 / 2) * z) = cexp (3 * π * I * z) from
    fun z => by ring_nf]
  have h_exp_pow : ∀ z : ℍ, cexp (π * I * z) ^ 3 = cexp (3 * π * I * z) := fun z => by
    simp only [← Complex.exp_nat_mul]; ring_nf
  have h_eq : ∀ z : ℍ, G z / cexp (3 * π * I * z) =
      (H₂ z / cexp (π * I * z)) ^ 3 * (2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2) := fun z => by
    simp only [G, Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Pi.smul_apply,
      Complex.real_smul, div_pow, h_exp_pow]
    push_cast
    field_simp [Complex.exp_ne_zero]
  simp_rw [h_eq]
  have h_poly : Filter.Tendsto (fun z : ℍ => 2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2)
      atImInfty (nhds 5) := by
    have hpair := H₂_tendsto_atImInfty.prodMk_nhds H₄_tendsto_atImInfty
    have hcont : Continuous (fun p : ℂ × ℂ => 2 * p.1 ^ 2 + 5 * p.1 * p.2 + 5 * p.2 ^ 2) := by
      fun_prop
    simpa using hcont.continuousAt.tendsto.comp hpair
  convert (H₂_div_exp_tendsto.pow 3).mul h_poly
  norm_num

/-- D(exp(c*z))/exp(c*z) = c/(2πi) for any coefficient c. -/
theorem D_cexp_div (c : ℂ) (z : ℍ) :
    D (fun w => cexp (c * w)) z / cexp (c * z) = c / (2 * π * I) := by
  simp only [D]
  have h_deriv : deriv ((fun w : ℍ => cexp (c * w)) ∘ ⇑ofComplex) (z : ℂ) =
      c * cexp (c * z) := by
    have h_exp_deriv : HasDerivAt (fun w : ℂ => cexp (c * w)) (c * cexp (c * z)) (z : ℂ) :=
      (Complex.hasDerivAt_exp (c * z)).scomp (z : ℂ)
        (by simpa using (hasDerivAt_id (z : ℂ)).const_mul c)
    exact ((UpperHalfPlane.eventuallyEq_coe_comp_ofComplex z.2).fun_comp
      (fun w => cexp (c * w))).deriv_eq.trans h_exp_deriv.deriv
  rw [h_deriv]
  field_simp [Complex.exp_ne_zero]

private theorem D_exp_pi_div_exp_pi (z : ℍ) :
    D (fun w => cexp (π * Complex.I * w)) z / cexp (π * Complex.I * z) = 1 / 2 := by
  simpa [show π * I / (2 * π * I) = (1 : ℂ) / 2 by field_simp] using D_cexp_div (π * I) z

private lemma deriv_jacobiTheta₂_half_mul_eq (z : ℍ) :
    deriv (fun t => jacobiTheta₂ (t / 2) t) (z : ℂ) =
      (jacobiTheta₂_fderiv ((z : ℂ) / 2) z) ((1 : ℂ) / 2, 1) := by
  set f : ℂ → ℂ × ℂ := fun t => (t / 2, t)
  set g : ℂ × ℂ → ℂ := fun p => jacobiTheta₂ p.1 p.2
  let f' : ℂ →L[ℂ] ℂ × ℂ := {
    toFun := fun h => (h / 2, h)
    map_add' := by intro x y; simp only [add_div, Prod.mk_add_mk]
    map_smul' := by
      intro c x
      simp only [RingHom.id_apply, Prod.smul_mk, smul_eq_mul, mul_div_assoc]
    cont := by continuity }
  have hf_1 : f' 1 = ((1 : ℂ) / 2, 1) := by simp only [f', ContinuousLinearMap.coe_mk',
    LinearMap.coe_mk, AddHom.coe_mk, one_div]
  have hf : HasFDerivAt f f' (z : ℂ) := by
    have h1 : HasDerivAt (fun t : ℂ => t / 2) (1 / 2 : ℂ) (z : ℂ) :=
      (hasDerivAt_id _).div_const 2
    have h2 : HasDerivAt (fun t : ℂ => t) 1 (z : ℂ) := hasDerivAt_id _
    have hprod := h1.prodMk h2
    convert hprod.hasFDerivAt using 1
    ext : 1
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, hf_1]
  have hf_val : f (z : ℂ) = ((z : ℂ) / 2, (z : ℂ)) := by simp [f]
  have hg : HasFDerivAt g (jacobiTheta₂_fderiv ((z : ℂ) / 2) z) (f (z : ℂ)) := by
    rw [hf_val]; exact hasFDerivAt_jacobiTheta₂ ((z : ℂ) / 2) z.2
  have h_comp := hg.comp (z : ℂ) hf
  simp only [Function.comp_def, g, f] at h_comp
  rw [h_comp.hasDerivAt.deriv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hf_1]

private lemma D_jacobiTheta₂_half_mul_eq_tsum (z : ℍ) :
    D (fun w : ℍ => jacobiTheta₂ (w / 2) w) z = (2 * π * I)⁻¹ *
      ∑' n : ℤ, (jacobiTheta₂_term_fderiv n (z / 2) z) ((1 : ℂ) / 2, 1) := by
  simp only [D, Function.comp_def]
  congr 1
  have h_eq : (fun x => jacobiTheta₂ (↑(ofComplex x) / 2) (↑(ofComplex x) : ℂ)) =ᶠ[nhds (z : ℂ)]
      (fun x => jacobiTheta₂ (x / 2) x) := by
    filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex z.2] with w hw
    simp [Function.comp_apply, id_eq] at hw ⊢
    simp [hw]
  rw [h_eq.deriv_eq, deriv_jacobiTheta₂_half_mul_eq z]
  exact ((hasSum_jacobiTheta₂_term_fderiv ((z : ℂ) / 2) z.2).mapL
    (ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ) / 2, 1))).tsum_eq.symm

private lemma jacobiTheta₂_half_mul_term_tendsto_zero (n : ℤ) :
    Filter.Tendsto (fun z : ℍ => (jacobiTheta₂_term_fderiv n ((z : ℂ) / 2) z) ((1 : ℂ) / 2, 1))
      atImInfty (nhds 0) := by
  by_cases hn0 : n = 0
  · set_option linter.unusedSimpArgs false in
    simp only [hn0, jacobiTheta₂_term_fderiv, Int.cast_zero, mul_zero, sq,
      zero_mul, zero_smul, add_zero, Complex.exp_zero, one_smul]
    have h_eq : (fun _ : ℍ => ((0 : ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (0 : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) ((1 : ℂ) / 2, 1)) = fun _ => 0 := by
      ext x
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        smul_eq_mul, mul_one]
      ring
    rw [h_eq]
    exact tendsto_const_nhds
  by_cases hn1 : n = -1
  · simp only [hn1, jacobiTheta₂_term_fderiv]
    simp only [Int.cast_neg, Int.cast_one, sq, neg_mul, neg_neg,
      mul_neg, mul_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    have h_sum : -(2 * ↑π * I * ((1 : ℂ) / 2)) + ↑π * I = 0 := by ring
    simp only [h_sum, mul_zero]
    exact tendsto_const_nhds
  · have hnn : n * (1 + n) > 0 := by
      rcases Int.lt_or_gt_of_ne hn0 with hn_neg | hn_pos
      · have h1n : 1 + n < 0 := by omega
        exact Int.mul_pos_of_neg_of_neg hn_neg h1n
      · have h1n : 1 + n > 0 := by omega
        exact Int.mul_pos hn_pos h1n
    simp only [jacobiTheta₂_term_fderiv, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul]
    have h_exp_eq : ∀ x : ℍ, 2 * ↑π * I * ↑n * (↑x / 2) + ↑π * I * ↑n ^ 2 * ↑x =
        ↑π * I * ↑n * (1 + n) * ↑x := by intro x; ring
    have h_coeff_eq : 2 * ↑π * I * ↑n * (1 / 2) + ↑π * I * ↑n ^ 2 * 1 =
        ↑π * I * ↑n * (1 + n) := by ring
    simp_rw [h_exp_eq, h_coeff_eq]
    have h_exp_tendsto : Filter.Tendsto (fun x : ℍ => cexp (↑π * I * ↑n * (1 + ↑n) * ↑x))
        atImInfty (nhds 0) := by
      rw [Complex.tendsto_exp_nhds_zero_iff]
      have h_re_eq : ∀ x : ℍ, (↑π * I * ↑n * (1 + ↑n) * ↑x).re =
          -π * (↑n * (1 + ↑n)) * x.im := by
        intro x
        simp only [mul_re, ofReal_re, ofReal_im, Complex.I_re, Complex.I_im,
          intCast_re, intCast_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
          add_re, add_im, one_re, one_im, mul_im]
        ring
      simp_rw [h_re_eq]
      have h_const_neg : -π * (↑n * (1 + ↑n)) < (0 : ℝ) := by
        have hnn' : (0 : ℝ) < ↑n * (1 + ↑n) := by exact_mod_cast hnn
        nlinarith [Real.pi_pos]
      rw [Filter.tendsto_const_mul_atBot_of_neg h_const_neg]
      exact Filter.tendsto_im_atImInfty
    convert h_exp_tendsto.mul tendsto_const_nhds using 1
    simp

private lemma jacobiTheta₂_half_mul_term_bound :
    ∀ᶠ z : ℍ in atImInfty, ∀ k : ℤ,
      ‖(jacobiTheta₂_term_fderiv k (↑z / 2) ↑z) ((1 : ℂ) / 2, 1)‖ ≤
        3 * π * ↑|k| ^ 2 * Real.exp (-π * (1 * ↑k ^ 2 - 1 * ↑|k|)) := by
  apply Filter.eventually_atImInfty.mpr
  use 1
  intro z hz k
  have h_opnorm := ContinuousLinearMap.le_opNorm
    (jacobiTheta₂_term_fderiv k (↑z / 2) ↑z) ((1 : ℂ) / 2, 1)
  have h_v_norm : ‖((1 : ℂ) / 2, (1 : ℂ))‖ = 1 := by
    simp only [Prod.norm_def]
    norm_num
  rw [h_v_norm, mul_one] at h_opnorm
  have h_fderiv_bound := norm_jacobiTheta₂_term_fderiv_le k (↑z / 2) ↑z
  have h_imz_pos : (0 : ℝ) < z.im := z.im_pos
  have h_imz_div2 : |(↑z / 2 : ℂ).im| ≤ z.im / 2 := by
    have h1 : (↑z / 2 : ℂ).im = z.im / 2 := by
      have h2 : (2 : ℂ) = (2 : ℝ) := by norm_cast
      rw [h2]
      simp only [Complex.div_ofReal_im, UpperHalfPlane.coe_im]
    rw [h1, abs_of_pos (by linarith : z.im / 2 > 0)]
  have h_term_bound := norm_jacobiTheta₂_term_le h_imz_pos h_imz_div2 (le_refl z.im) k
  calc ‖(jacobiTheta₂_term_fderiv k (↑z / 2) ↑z) (1 / 2, 1)‖
      ≤ ‖jacobiTheta₂_term_fderiv k (↑z / 2) ↑z‖ := h_opnorm
    _ ≤ 3 * π * ↑|k| ^ 2 * ‖jacobiTheta₂_term k (↑z / 2) ↑z‖ := h_fderiv_bound
    _ ≤ 3 * π * ↑|k| ^ 2 * rexp (-π * (z.im * ↑k ^ 2 - 2 * (z.im / 2) * ↑|k|)) := by
        apply mul_le_mul_of_nonneg_left h_term_bound
        positivity
    _ = 3 * π * ↑|k| ^ 2 * rexp (-π * z.im * (↑k ^ 2 - ↑|k|)) := by ring_nf
    _ ≤ 3 * π * ↑|k| ^ 2 * rexp (-π * 1 * (↑k ^ 2 - ↑|k|)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp_of_le
        have hk_ge : (↑|k| : ℝ) ^ 2 - ↑|k| ≥ 0 := by
          rcases eq_or_ne k 0 with rfl | hk0
          · simp
          · nlinarith [show (1 : ℝ) ≤ ↑|k| from by exact_mod_cast Int.one_le_abs hk0]
        rw [show (k : ℝ) ^ 2 = (↑|k| : ℝ) ^ 2 from by rw [Int.cast_abs, sq_abs]]
        nlinarith [mul_nonneg (mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.mpr hz)) hk_ge]
    _ = 3 * π * ↑|k| ^ 2 * rexp (-π * (1 * ↑k ^ 2 - 1 * ↑|k|)) := by ring_nf

private theorem D_jacobiTheta₂_half_mul_tendsto_zero :
    Filter.Tendsto (fun z : ℍ => D (fun w : ℍ => jacobiTheta₂ (w / 2) w) z)
      atImInfty (nhds 0) := by
  simp_rw [D_jacobiTheta₂_half_mul_eq_tsum]
  have h_tsum_tendsto : Filter.Tendsto
      (fun z : ℍ => ∑' n : ℤ, (jacobiTheta₂_term_fderiv n (z / 2) z) ((1 : ℂ) / 2, 1))
      atImInfty (nhds 0) := by
    rw [show (0 : ℂ) = ∑' (k : ℤ), (0 : ℂ) from tsum_zero.symm]
    exact tendsto_tsum_of_dominated_convergence (α := ℍ) (𝓕 := atImInfty)
      (f := fun z n => (jacobiTheta₂_term_fderiv n ((z : ℂ) / 2) z) ((1 : ℂ) / 2, 1))
      (g := fun _ => 0)
      (bound := fun n => 3 * π * |n| ^ 2 * Real.exp (-π * (1 * n ^ 2 - 1 * |n|)))
      (by simpa [mul_assoc] using
        (summable_pow_mul_jacobiTheta₂_term_bound (1/2) one_pos 2).mul_left (3 * π))
      (fun n => jacobiTheta₂_half_mul_term_tendsto_zero n)
      jacobiTheta₂_half_mul_term_bound
  simpa using tendsto_const_nhds (x := (2 * π * I)⁻¹).mul h_tsum_tendsto

private theorem D_exp_pi_quarter_div_exp_pi_quarter (z : ℍ) :
    D (fun w => cexp (π * Complex.I * w / 4)) z / cexp (π * Complex.I * z / 4) = 1 / 8 := by
  simpa only [show ∀ w : ℍ, (π * I / 4 : ℂ) * w = π * I * w / 4 from fun w => by ring,
    show π * I / 4 / (2 * π * I) = (1 : ℂ) / 8 by field_simp; ring] using D_cexp_div (π * I / 4) z

/-- Differentiability of t ↦ jacobiTheta₂(t/2, t) at points in the upper half-plane. -/
lemma differentiableAt_jacobiTheta₂_half (τ : ℍ) :
    DifferentiableAt ℂ (fun t : ℂ => jacobiTheta₂ (t / 2) t) τ.val := by
  let f : ℂ → ℂ × ℂ := fun t => (t / 2, t)
  have hf : DifferentiableAt ℂ f τ.val :=
    (differentiableAt_id.mul_const ((2 : ℂ)⁻¹)).prodMk differentiableAt_id
  have hg : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (f τ.val) := by
    simpa [f] using (hasFDerivAt_jacobiTheta₂ (τ.1 / 2) τ.2).differentiableAt
  simpa [f] using hg.comp τ.val hf

private lemma Θ₂_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Θ₂ := by
  intro τ
  have hΘ₂_diff : DifferentiableAt ℂ (Θ₂ ∘ ofComplex) τ.val := by
    have hU : {z : ℂ | 0 < z.im} ∈ nhds τ.val := isOpen_upperHalfPlaneSet.mem_nhds τ.2
    have hF : DifferentiableAt ℂ
        (fun t => cexp ((π * I / 4) * t) * jacobiTheta₂ (t / 2) t) τ.val :=
      ((differentiableAt_id.const_mul ((π : ℂ) * I / 4)).cexp).mul
        (differentiableAt_jacobiTheta₂_half τ)
    have h_ev : (fun t => cexp ((π * I / 4) * t) * jacobiTheta₂ (t / 2) t) =ᶠ[nhds τ.val]
        (Θ₂ ∘ ofComplex) := by
      refine Filter.eventually_of_mem hU fun z hz => ?_
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, Θ₂_as_jacobiTheta₂,
        coe_mk_subtype]; ring_nf
    exact hF.congr_of_eventuallyEq h_ev.symm
  have h_eq : (Θ₂ ∘ ofComplex) ∘ UpperHalfPlane.coe = Θ₂ := by
    ext x; simp [Function.comp, ofComplex_apply]
  rw [← h_eq]; exact DifferentiableAt_MDifferentiableAt hΘ₂_diff

private theorem D_Θ₂_div_Θ₂_tendsto :
    Filter.Tendsto (fun z : ℍ => D Θ₂ z / Θ₂ z) atImInfty (nhds ((1 : ℂ) / 8)) := by
  let f : ℍ → ℂ := fun w => cexp (π * Complex.I * w / 4)
  let h : ℍ → ℂ := fun w => Θ₂ w / f w
  have hf_logderiv : ∀ z : ℍ, D f z / f z = 1 / 8 := D_exp_pi_quarter_div_exp_pi_quarter
  have hh_tendsto : Filter.Tendsto h atImInfty (nhds (2 : ℂ)) := Θ₂_div_exp_tendsto
  have hDh_tendsto : Filter.Tendsto (fun z => D h z) atImInfty (nhds (0 : ℂ)) := by
    have : (fun z => D h z) = fun z => D (fun w : ℍ => jacobiTheta₂ (w / 2) w) z := by
      ext z; congr 1; ext w; simp only [h, f, Θ₂_as_jacobiTheta₂]; field_simp [Complex.exp_ne_zero]
    rw [this]; exact D_jacobiTheta₂_half_mul_tendsto_zero
  have h_ne_zero : ∀ᶠ z : ℍ in atImInfty, h z ≠ 0 :=
    hh_tendsto.eventually_ne (by norm_num : (2 : ℂ) ≠ 0)
  have hDh_div_h_tendsto : Filter.Tendsto (fun z => D h z / h z) atImInfty (nhds (0 : ℂ)) := by
    simpa using hDh_tendsto.div hh_tendsto (by norm_num : (2 : ℂ) ≠ 0)
  have hf_ne : ∀ z : ℍ, f z ≠ 0 := fun z => Complex.exp_ne_zero _
  have hf_md : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
    intro τ
    have h_diff : DifferentiableAt ℂ (fun t : ℂ => cexp (π * I * t / 4)) (τ : ℂ) :=
      ((differentiableAt_id.const_mul (π * I)).div_const 4).cexp
    simpa [f, Function.comp] using
      (DifferentiableAt_MDifferentiableAt
        (G := fun t : ℂ => cexp (π * I * t / 4)) (z := τ) h_diff)
  have hh_md : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    intro τ
    suffices h_diff : DifferentiableAt ℂ (h ∘ ofComplex) τ.val by
      have h_eq : (h ∘ ofComplex) ∘ UpperHalfPlane.coe = h := by
        ext x; simp [Function.comp, ofComplex_apply, h]
      rw [← h_eq]
      exact DifferentiableAt_MDifferentiableAt (G := h ∘ ofComplex) (z := τ) h_diff
    have hΘ₂_diff : DifferentiableAt ℂ (Θ₂ ∘ ofComplex) τ.val :=
      MDifferentiableAt_DifferentiableAt (Θ₂_MDifferentiable τ)
    have hf_diff : DifferentiableAt ℂ (f ∘ ofComplex) τ.val :=
      MDifferentiableAt_DifferentiableAt (hf_md τ)
    have hf_ne' : (f ∘ ofComplex) τ.val ≠ 0 := by
      simp only [Function.comp_apply, f]; exact Complex.exp_ne_zero _
    have h_eq' : (h ∘ ofComplex) =ᶠ[nhds τ.val] (Θ₂ ∘ ofComplex) / (f ∘ ofComplex) := by
      have hU : {z : ℂ | 0 < z.im} ∈ nhds τ.val := isOpen_upperHalfPlaneSet.mem_nhds τ.2
      filter_upwards [hU] with w hw
      simp only [Function.comp_apply, h, Pi.div_apply, ofComplex_apply_of_im_pos hw]
    exact (hΘ₂_diff.div hf_diff hf_ne').congr_of_eventuallyEq h_eq'.symm
  have h_logderiv_eq : ∀ᶠ z : ℍ in atImInfty, D Θ₂ z / Θ₂ z = D f z / f z + D h z / h z := by
    have h_Θ₂_fn : Θ₂ = f * h := by
      ext w; simp only [h, Pi.mul_apply, mul_div_cancel₀ _ (hf_ne w)]
    filter_upwards [h_ne_zero] with z hz
    rw [h_Θ₂_fn]; exact logderiv_mul_eq f h hf_md hh_md z (hf_ne z) hz
  have h_sum_limit : Filter.Tendsto (fun z => D f z / f z + D h z / h z) atImInfty
      (nhds ((1 : ℂ) / 8)) := by
    have hf_const : Filter.Tendsto (fun z => D f z / f z) atImInfty (nhds ((1 : ℂ) / 8)) := by
      simp_rw [hf_logderiv]; exact tendsto_const_nhds
    simpa using hf_const.add hDh_div_h_tendsto
  exact h_sum_limit.congr' (by filter_upwards [h_logderiv_eq] with z hz; exact hz.symm)

private theorem D_H₂_div_H₂_tendsto :
    Filter.Tendsto (fun z : ℍ => D H₂ z / H₂ z) atImInfty (nhds ((1 : ℂ) / 2)) := by
  have hH₂_eq : ∀ z : ℍ, H₂ z = (Θ₂ z) ^ 4 := fun z => rfl
  have h_logderiv : ∀ z : ℍ, Θ₂ z ≠ 0 → D H₂ z / H₂ z = 4 * (D Θ₂ z / Θ₂ z) := by
    intro z hΘ₂
    rw [hH₂_eq]
    have h_pow4 : D (fun w => (Θ₂ w) ^ 4) z = 4 * (Θ₂ z) ^ 3 * D Θ₂ z :=
      D_pow4_eq Θ₂ Θ₂_MDifferentiable z
    have h_H₂_eq_fn : H₂ = fun w => (Θ₂ w) ^ 4 := by ext w; rfl
    rw [h_H₂_eq_fn, h_pow4]
    have h_pow4_ne : (Θ₂ z) ^ 4 ≠ 0 := pow_ne_zero 4 hΘ₂
    field_simp [hΘ₂, h_pow4_ne]
  have hΘ₂_ne := Θ₂_eventually_ne_zero
  rw [← show (4 : ℂ) * (1 / 8) = 1 / 2 from by norm_num]
  apply (D_Θ₂_div_Θ₂_tendsto.const_mul (4 : ℂ)).congr'
  filter_upwards [hΘ₂_ne] with z hz
  exact (h_logderiv z hz).symm

private theorem D_H₂_tendsto_zero :
    Filter.Tendsto (fun z : ℍ => D H₂ z) atImInfty (nhds 0) := by
  have hH₂_ne := H₂_eventually_ne_zero
  have h_eq : (fun z => D H₂ z) =ᶠ[atImInfty] fun z => (D H₂ z / H₂ z) * H₂ z := by
    filter_upwards [hH₂_ne] with z hz
    exact (div_mul_cancel₀ (D H₂ z) hz).symm
  have hlim := D_H₂_div_H₂_tendsto.mul H₂_tendsto_atImInfty
  simp only [mul_zero] at hlim
  exact hlim.congr' h_eq.symm

private lemma summable_sq_mul_exp_neg_pi_sq :
    Summable fun n : ℤ ↦ (n : ℝ) ^ 2 * rexp (-π * n ^ 2) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0 (by norm_num : (0 : ℝ) < 1) 2
  simp only [mul_zero, one_mul] at h
  convert h using 1
  ext n
  congr 1
  · rw [← sq_abs, Int.cast_abs]
  · ring_nf

private theorem D_Θ₄_tendsto_zero :
    Filter.Tendsto (fun z : ℍ => D Θ₄ z) atImInfty (nhds 0) := by
  have h_D_eq_tsum : ∀ z : ℍ, D Θ₄ z = (2 * π * I)⁻¹ *
      ∑' n : ℤ, (jacobiTheta₂_term_fderiv n (1/2) z) (0, 1) := by
    intro z
    simp only [D, Θ₄_as_jacobiTheta₂, Function.comp_def]
    congr 1
    have h_eq : (fun x => jacobiTheta₂ (1/2) (↑(ofComplex x) : ℂ)) =ᶠ[nhds (z : ℂ)]
        (fun x => jacobiTheta₂ (1/2) x) :=
      (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex z.2).fun_comp (jacobiTheta₂ (1/2))
    rw [h_eq.deriv_eq]
    have hFD := hasFDerivAt_jacobiTheta₂ (1/2 : ℂ) z.2
    have h_embed : HasDerivAt (fun t : ℂ => ((1 : ℂ)/2, t)) (0, 1) (z : ℂ) :=
      (hasDerivAt_const (z : ℂ) (1/2)).prodMk (hasDerivAt_id (z : ℂ))
    have h_chain := hFD.comp_hasDerivAt (z : ℂ) h_embed
    simp only [Function.comp_def] at h_chain
    rw [h_chain.deriv]
    exact ((hasSum_jacobiTheta₂_term_fderiv (1/2 : ℂ) z.2).mapL
      (ContinuousLinearMap.apply ℂ ℂ (0, 1))).tsum_eq.symm
  simp_rw [h_D_eq_tsum]
  have h_tsum_tendsto : Filter.Tendsto
      (fun z : ℍ => ∑' n : ℤ, (jacobiTheta₂_term_fderiv n (1/2) z) (0, 1)) atImInfty (nhds 0) := by
    conv => rhs; rw [show (0 : ℂ) = ∑' (k : ℤ), (0 : ℂ) from tsum_zero.symm]
    apply tendsto_tsum_of_dominated_convergence (α := ℍ) (𝓕 := atImInfty)
      (f := fun z n => (jacobiTheta₂_term_fderiv n (1/2) z) ((0 : ℂ), 1))
      (g := fun _ => 0)
      (bound := fun n => 3 * π * |n| ^ 2 * Real.exp (-π * n ^ 2))
    · simpa [mul_assoc] using summable_sq_mul_exp_neg_pi_sq.mul_left (3 * π)
    · intro n
      by_cases hn0 : n = 0
      · subst hn0
        set_option linter.unusedSimpArgs false in
        simp only [jacobiTheta₂_term_fderiv, Int.cast_zero, mul_zero, sq,
          zero_mul, zero_smul, add_zero, Complex.exp_zero, one_smul,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
        exact tendsto_const_nhds
      · simp only [jacobiTheta₂_term_fderiv, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_fst',
          ContinuousLinearMap.coe_snd', smul_eq_mul]
        have h_simp : ∀ z : ℍ,
            cexp (2 * ↑π * I * ↑n * (1/2 : ℂ) + ↑π * I * ↑n ^ 2 * ↑z) *
            (2 * ↑π * I * ↑n * 0 + ↑π * I * ↑n ^ 2 * 1) =
            cexp (↑π * I * ↑n + ↑π * I * ↑n ^ 2 * ↑z) * (↑π * I * ↑n ^ 2) := fun z => by ring_nf
        simp_rw [h_simp]
        have hnsq_pos : n ^ 2 > 0 := sq_pos_of_ne_zero hn0
        have h_exp_tendsto : Filter.Tendsto
            (fun z : ℍ => cexp ((π : ℂ) * I * n + (π : ℂ) * I * (n : ℂ) ^ 2 * z))
            atImInfty (nhds 0) := by
          rw [Complex.tendsto_exp_nhds_zero_iff]
          have h_re_eq : ∀ z : ℍ,
              ((π : ℂ) * I * n + (π : ℂ) * I * (n : ℂ) ^ 2 * z).re = -π * (n : ℝ) ^ 2 * z.im := by
            intro z
            simp only [add_re, mul_re, ofReal_re, ofReal_im, Complex.I_re, Complex.I_im,
              intCast_re, intCast_im, sq, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, mul_im]
            ring
          simp_rw [h_re_eq]
          have h_const_neg : -π * (n : ℝ) ^ 2 < 0 := by
            have hnsq' : (0 : ℝ) < (n : ℝ) ^ 2 := by exact_mod_cast hnsq_pos
            nlinarith [Real.pi_pos]
          rw [Filter.tendsto_const_mul_atBot_of_neg h_const_neg]
          exact Filter.tendsto_im_atImInfty
        convert h_exp_tendsto.mul tendsto_const_nhds using 1; simp
    · apply Filter.eventually_atImInfty.mpr
      use 1
      intro z hz k
      have h_opnorm := ContinuousLinearMap.le_opNorm
        (jacobiTheta₂_term_fderiv k (1/2) ↑z) ((0 : ℂ), 1)
      have h_v_norm : ‖((0 : ℂ), (1 : ℂ))‖ = 1 := by simp [Prod.norm_def]
      rw [h_v_norm, mul_one] at h_opnorm
      have h_fderiv_bound := norm_jacobiTheta₂_term_fderiv_le k (1/2 : ℂ) ↑z
      have h_half_im : |(1/2 : ℂ).im| ≤ 0 := by simp
      have h_term_bound := norm_jacobiTheta₂_term_le z.im_pos h_half_im (le_refl z.im) k
      calc ‖(jacobiTheta₂_term_fderiv k (1/2) ↑z) (0, 1)‖
          ≤ ‖jacobiTheta₂_term_fderiv k (1/2) ↑z‖ := h_opnorm
        _ ≤ 3 * π * ↑|k| ^ 2 * ‖jacobiTheta₂_term k (1/2) ↑z‖ := h_fderiv_bound
        _ ≤ 3 * π * ↑|k| ^ 2 * rexp (-π * (z.im * ↑k ^ 2 - 2 * 0 * ↑|k|)) := by
            exact mul_le_mul_of_nonneg_left h_term_bound (by positivity)
        _ = 3 * π * ↑|k| ^ 2 * rexp (-π * z.im * ↑k ^ 2) := by ring_nf
        _ ≤ 3 * π * ↑|k| ^ 2 * rexp (-π * 1 * ↑k ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.exp_le_exp_of_le
            nlinarith [mul_nonneg (sub_nonneg.mpr hz) (sq_nonneg (k : ℝ)), Real.pi_pos]
        _ = 3 * π * ↑|k| ^ 2 * rexp (-π * ↑k ^ 2) := by ring_nf
  simpa using tendsto_const_nhds (x := (2 * π * I)⁻¹).mul h_tsum_tendsto

private theorem D_H₄_tendsto_zero :
    Filter.Tendsto (fun z : ℍ => D H₄ z) atImInfty (nhds 0) := by
  have hΘ₄_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Θ₄ := by
    intro τ
    have hθ : DifferentiableAt ℂ (fun z : ℂ => jacobiTheta₂ (1 / 2 : ℂ) z) (τ : ℂ) :=
      differentiableAt_jacobiTheta₂_snd (1 / 2 : ℂ) τ.2
    have hMD : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
        ((fun z : ℂ => jacobiTheta₂ (1 / 2 : ℂ) z) ∘ UpperHalfPlane.coe) τ :=
      DifferentiableAt_MDifferentiableAt (G := fun z : ℂ => jacobiTheta₂ (1 / 2 : ℂ) z) hθ
    convert hMD using 1
    ext x; simp [Θ₄_as_jacobiTheta₂, Function.comp]
  have h_D_H₄_pt : ∀ z, D H₄ z = (4 : ℂ) * (Θ₄ z) ^ 3 * D Θ₄ z := by
    intro z
    have : D H₄ z = D (fun w => Θ₄ w ^ 4) z := by congr 1
    rw [this, D_pow4_eq Θ₄ hΘ₄_holo z]
  simp_rw [h_D_H₄_pt]
  have h_lim := (tendsto_const_nhds (x := (4 : ℂ))).mul
    ((Θ₄_tendsto_atImInfty.pow 3).mul D_Θ₄_tendsto_zero)
  simp only [mul_zero] at h_lim
  exact h_lim.congr fun z => by ring

/-- `D(2H₂² + 5H₂H₄ + 5H₄²) → 0` as `im(z) → ∞`. -/
private theorem D_B_tendsto_zero :
    Filter.Tendsto (fun z : ℍ =>
      D (fun w => 2 * H₂ w ^ 2 + 5 * H₂ w * H₄ w + 5 * H₄ w ^ 2) z)
      atImInfty (nhds 0) := by
  have hH₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂ := H₂_SIF_MDifferentiable
  have hH₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄ := H₄_SIF_MDifferentiable
  have hH₂sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 2) := by rw [pow_two]; exact hH₂.mul hH₂
  have hH₄sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₄ ^ 2) := by rw [pow_two]; exact hH₄.mul hH₄
  have h_2H₂sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 2 * H₂ z ^ 2) := by
    have : (fun z => 2 * H₂ z ^ 2) = (2 : ℂ) • (H₂ ^ 2) := by ext z; simp [smul_eq_mul]
    rw [this]; exact hH₂sq.const_smul 2
  have h_5H₂H₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 5 * H₂ z * H₄ z) := by
    have : (fun z => 5 * H₂ z * H₄ z) = (5 : ℂ) • (H₂ * H₄) := by
      ext z; simp [smul_eq_mul, mul_assoc]
    rw [this]; exact (hH₂.mul hH₄).const_smul 5
  have h_5H₄sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 5 * H₄ z ^ 2) := by
    have : (fun z => 5 * H₄ z ^ 2) = (5 : ℂ) • (H₄ ^ 2) := by ext z; simp [smul_eq_mul]
    rw [this]; exact hH₄sq.const_smul 5
  have h_2H₂sq_5H₂H₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z => 2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z) := h_2H₂sq.add h_5H₂H₄
  have h_D_B : ∀ z, D (fun w => 2 * H₂ w ^ 2 + 5 * H₂ w * H₄ w + 5 * H₄ w ^ 2) z =
      4 * H₂ z * D H₂ z + 5 * (H₂ z * D H₄ z + D H₂ z * H₄ z) + 10 * H₄ z * D H₄ z := by
    intro z
    have h_term1 : D (fun w => 2 * H₂ w ^ 2) z = 4 * H₂ z * D H₂ z := by
      have h1 : (fun w => 2 * H₂ w ^ 2) = (2 : ℂ) • (H₂ ^ 2) := by ext w; simp [smul_eq_mul]
      have h2 : D ((2 : ℂ) • (H₂ ^ 2)) z = 2 * D (H₂ ^ 2) z := by
        rw [D_smul 2 (H₂ ^ 2) hH₂sq]; simp
      have h3 : D (H₂ ^ 2) z = 2 * H₂ z * D H₂ z := by
        simpa using congrFun (D_sq H₂ hH₂) z
      rw [h1, h2, h3]; ring
    have h_term2 : D (fun w => 5 * H₂ w * H₄ w) z =
        5 * (H₂ z * D H₄ z + D H₂ z * H₄ z) := by
      have h1 : (fun w => 5 * H₂ w * H₄ w) = (5 : ℂ) • (H₂ * H₄) := by
        ext w; simp [smul_eq_mul, mul_assoc]
      have h2 : D ((5 : ℂ) • (H₂ * H₄)) z = 5 * D (H₂ * H₄) z := by
        rw [D_smul 5 (H₂ * H₄) (hH₂.mul hH₄)]; simp
      have h3 : D (H₂ * H₄) z = D H₂ z * H₄ z + H₂ z * D H₄ z := by
        simpa using congrFun (D_mul H₂ H₄ hH₂ hH₄) z
      rw [h1, h2, h3]; ring
    have h_term3 : D (fun w => 5 * H₄ w ^ 2) z = 10 * H₄ z * D H₄ z := by
      have h1 : (fun w => 5 * H₄ w ^ 2) = (5 : ℂ) • (H₄ ^ 2) := by ext w; simp [smul_eq_mul]
      have h2 : D ((5 : ℂ) • (H₄ ^ 2)) z = 5 * D (H₄ ^ 2) z := by
        rw [D_smul 5 (H₄ ^ 2) hH₄sq]; simp
      have h3 : D (H₄ ^ 2) z = 2 * H₄ z * D H₄ z := by
        simpa using congrFun (D_sq H₄ hH₄) z
      rw [h1, h2, h3]; ring
    have h_add1 : D (fun w => 2 * H₂ w ^ 2 + 5 * H₂ w * H₄ w) z =
        D (fun w => 2 * H₂ w ^ 2) z + D (fun w => 5 * H₂ w * H₄ w) z := by
      simpa using congrFun (D_add _ _ h_2H₂sq h_5H₂H₄) z
    have h_add2 : D (fun w => 2 * H₂ w ^ 2 + 5 * H₂ w * H₄ w + 5 * H₄ w ^ 2) z =
        D (fun w => 2 * H₂ w ^ 2 + 5 * H₂ w * H₄ w) z +
        D (fun w => 5 * H₄ w ^ 2) z := by
      simpa using congrFun (D_add _ _ h_2H₂sq_5H₂H₄ h_5H₄sq) z
    rw [h_add2, h_add1, h_term1, h_term2, h_term3]
  simp_rw [h_D_B]
  have h_t1 : Filter.Tendsto (fun z => 4 * H₂ z * D H₂ z) atImInfty (nhds 0) := by
    simpa [mul_zero] using ((tendsto_const_nhds (x := (4 : ℂ))).mul
      (H₂_tendsto_atImInfty.mul D_H₂_tendsto_zero)).congr fun z => by ring
  have h_t2 : Filter.Tendsto (fun z => 5 * (H₂ z * D H₄ z + D H₂ z * H₄ z))
      atImInfty (nhds 0) := by
    have h_sub1 := H₂_tendsto_atImInfty.mul D_H₄_tendsto_zero
    have h_sub2 := D_H₂_tendsto_zero.mul H₄_tendsto_atImInfty
    simp only [zero_mul, mul_zero] at h_sub1 h_sub2
    simpa using (tendsto_const_nhds (x := (5 : ℂ))).mul (h_sub1.add h_sub2)
  have h_t3 : Filter.Tendsto (fun z => 10 * H₄ z * D H₄ z) atImInfty (nhds 0) := by
    simpa [mul_zero] using ((tendsto_const_nhds (x := (10 : ℂ))).mul
      (H₄_tendsto_atImInfty.mul D_H₄_tendsto_zero)).congr fun z => by ring
  convert (h_t1.add h_t2).add h_t3 using 1
  simp

/-- `(D G)/G → 3/2` as `im(z) → ∞`. -/
theorem D_G_div_G_tendsto :
    Filter.Tendsto (fun z : ℍ => D G z / G z) atImInfty (nhds ((3 : ℂ) / 2)) := by
  have hH₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂ := H₂_SIF_MDifferentiable
  have hH₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄ := H₄_SIF_MDifferentiable
  let A : ℍ → ℂ := fun z => H₂ z ^ 3
  let B : ℍ → ℂ := fun z => 2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2
  have hG_eq : ∀ z, G z = A z * B z := fun z => rfl
  have hH₂sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 2) := by rw [pow_two]; exact hH₂.mul hH₂
  have hH₄sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₄ ^ 2) := by rw [pow_two]; exact hH₄.mul hH₄
  have hA : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) A := hH₂sq.mul hH₂
  have h_2H₂sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 2 * H₂ z ^ 2) := by
    have : (fun z => 2 * H₂ z ^ 2) = (2 : ℂ) • (H₂ ^ 2) := by ext z; simp [smul_eq_mul]
    rw [this]; exact hH₂sq.const_smul 2
  have h_5H₂H₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 5 * H₂ z * H₄ z) := by
    have : (fun z => 5 * H₂ z * H₄ z) = (5 : ℂ) • (H₂ * H₄) := by
      ext z; simp [smul_eq_mul, mul_assoc]
    rw [this]; exact (hH₂.mul hH₄).const_smul 5
  have h_5H₄sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 5 * H₄ z ^ 2) := by
    have : (fun z => 5 * H₄ z ^ 2) = (5 : ℂ) • (H₄ ^ 2) := by ext z; simp [smul_eq_mul]
    rw [this]; exact hH₄sq.const_smul 5
  have h_2H₂sq_5H₂H₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z) :=
    h_2H₂sq.add h_5H₂H₄
  have hB : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) B := (h_2H₂sq.add h_5H₂H₄).add h_5H₄sq
  have h_DA_A : ∀ z, H₂ z ≠ 0 → D A z / A z = 3 * (D H₂ z / H₂ z) := by
    intro z hH₂_ne
    have h_cube : D (fun w => H₂ w ^ 3) z = 3 * H₂ z ^ 2 * D H₂ z := by
      simpa [Pi.mul_apply, Pi.pow_apply] using congrFun (D_cube H₂ hH₂) z
    simp only [A]
    rw [h_cube]
    field_simp [pow_ne_zero 3 hH₂_ne, pow_ne_zero 2 hH₂_ne]
  have h_DA_A_tendsto : Filter.Tendsto (fun z => D A z / A z) atImInfty (nhds ((3 : ℂ) / 2)) := by
    have h_eq : (3 : ℂ) / 2 = 3 * (1 / 2) := by norm_num
    rw [h_eq]
    have hH₂_ne := H₂_eventually_ne_zero
    apply (D_H₂_div_H₂_tendsto.const_mul 3).congr'
    filter_upwards [hH₂_ne] with z hz
    exact (h_DA_A z hz).symm
  have h_B_tendsto : Filter.Tendsto B atImInfty (nhds 5) := by
    have h := ((H₂_tendsto_atImInfty.pow 2).const_mul 2).add
      (((H₂_tendsto_atImInfty.mul H₄_tendsto_atImInfty).const_mul 5).add
        ((H₄_tendsto_atImInfty.pow 2).const_mul 5))
    simp only [zero_pow two_ne_zero, one_pow, mul_zero, mul_one, zero_add] at h
    refine h.congr' ?_
    filter_upwards with z
    simp only [B, pow_two]; ring
  have h_DB_tendsto : Filter.Tendsto (fun z => D B z) atImInfty (nhds 0) := D_B_tendsto_zero
  have h_DB_B_tendsto : Filter.Tendsto (fun z => D B z / B z) atImInfty (nhds 0) := by
    simpa using h_DB_tendsto.div h_B_tendsto (by norm_num : (5 : ℂ) ≠ 0)
  have h_DG_G : ∀ z, A z ≠ 0 → B z ≠ 0 → D G z / G z = D A z / A z + D B z / B z := by
    intro z hA_ne hB_ne
    rw [show G = A * B from funext hG_eq]
    exact logderiv_mul_eq A B hA hB z hA_ne hB_ne
  have hA_ne : ∀ᶠ z in atImInfty, A z ≠ 0 := by
    have hH₂_ne := H₂_div_exp_tendsto.eventually_ne (by norm_num : (16 : ℂ) ≠ 0)
    filter_upwards [hH₂_ne] with z hz hzero
    simp only [A] at hzero
    have := eq_zero_of_pow_eq_zero hzero
    exact hz (by simp [this])
  have hB_ne : ∀ᶠ z in atImInfty, B z ≠ 0 :=
    h_B_tendsto.eventually_ne (by norm_num : (5 : ℂ) ≠ 0)
  rw [show (3 : ℂ) / 2 = 3 / 2 + 0 from by norm_num]
  apply (h_DA_A_tendsto.add h_DB_B_tendsto).congr'
  filter_upwards [hA_ne, hB_ne] with z hA hB
  exact (h_DG_G z hA hB).symm

/-- `L₁,₀(it)` is real for all `t > 0`. -/
theorem L₁₀_imag_axis_real : ResToImagAxis.Real L₁₀ := by
  intro t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, L₁₀_eq_FD_G_sub_F_DG]
  have hF := F_imag_axis_real t ht
  have hG := G_imag_axis_real t ht
  have hDF := D_real_of_real F_imag_axis_real F_holo t ht
  have hDG := D_real_of_real G_imag_axis_real G_holo t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte] at hF hG hDF hDG
  simp [sub_im, mul_im, hF, hG, hDF, hDG]

/-- `lim_{t→∞} L₁,₀(it)/(F(it)G(it)) = 1/2`. -/
theorem L₁₀_div_FG_tendsto :
    Filter.Tendsto (fun t : ℝ => (L₁₀.resToImagAxis t).re /
      ((F.resToImagAxis t).re * (G.resToImagAxis t).re))
      Filter.atTop (nhds (1/2)) := by
  have h_wronskian : ∀ z : ℍ, F z ≠ 0 → G z ≠ 0 →
      L₁₀ z / (F z * G z) = D F z / F z - D G z / G z := by
    intro z hF hG
    rw [L₁₀_eq_FD_G_sub_F_DG]
    field_simp [hF, hG]
  have hF_ne := eventually_ne_zero_of_tendsto_div (by norm_num : (720^2 : ℂ) ≠ 0) F_vanishing_order
  have hG_ne := eventually_ne_zero_of_tendsto_div (by norm_num : (20480 : ℂ) ≠ 0) G_vanishing_order
  have h_L_over_FG : Filter.Tendsto (fun z : ℍ => L₁₀ z / (F z * G z))
      atImInfty (nhds (1 / 2 : ℂ)) := by
    have h := (D_F_div_F_tendsto.sub D_G_div_G_tendsto).congr' (by
      filter_upwards [hF_ne, hG_ne] with z hF hG using (h_wronskian z hF hG).symm)
    convert h using 2; norm_num
  have h_axis := tendsto_resToImagAxis_of_tendsto_atImInfty h_L_over_FG
  have h_re := Complex.continuous_re.continuousAt.tendsto.comp h_axis
  simp only [show (1 / 2 : ℂ).re = (1 / 2 : ℝ) by norm_num] at h_re
  refine h_re.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with t ht_pos
  simp only [Function.comp_apply, Function.resToImagAxis_apply, ResToImagAxis, ht_pos, ↓reduceDIte]
  set z : ℍ := ⟨Complex.I * t, by simp [ht_pos]⟩ with hz
  have hL := L₁₀_imag_axis_real t ht_pos
  have hF := F_imag_axis_real t ht_pos
  have hG := G_imag_axis_real t ht_pos
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht_pos, ↓reduceDIte] at hL hF hG
  rw [← hz] at hL hF hG
  have hFG_im : (F z * G z).im = 0 := by rw [Complex.mul_im, hF, hG]; ring
  have hFG_re : (F z * G z).re = (F z).re * (G z).re := by rw [Complex.mul_re, hF, hG]; ring
  rw [div_re_of_im_eq_zero hL hFG_im, hFG_re]

theorem L₁₀_eventually_pos_imag_axis : ResToImagAxis.EventuallyPos L₁₀ := by
  refine ⟨L₁₀_imag_axis_real, ?_⟩
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp
    (L₁₀_div_FG_tendsto.eventually (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1/2)))
  refine ⟨max t₀ 1, by positivity, fun t ht => ?_⟩
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  have hFG_pos := mul_pos (F_imag_axis_pos.2 t ht_pos) (G_imag_axis_pos.2 t ht_pos)
  have h := mul_pos (ht₀ t (le_trans (le_max_left _ _) ht)) hFG_pos
  rwa [div_mul_cancel₀ _ (ne_of_gt hFG_pos)] at h

end AsymptoticAnalysis

/- $\mathcal{L}_{1, 0}$ is eventually positive on the imaginary axis. -/
lemma L₁₀_eventuallyPos : ResToImagAxis.EventuallyPos L₁₀ := L₁₀_eventually_pos_imag_axis

/- $\mathcal{L}_{1, 0}$ is positive on the imaginary axis. -/
lemma L₁₀_pos : ResToImagAxis.Pos L₁₀ := antiSerreDerPos SerreDer_22_L₁₀_pos L₁₀_eventuallyPos

/-!
## Monotonicity of Q = F/G on the Imaginary Axis

Proposition 8.12 from the blueprint: the function `Q(t) = F(it)/G(it)` is strictly
decreasing on `(0, ∞)`.
-/

/-- `L₁,₀(it) > 0` for all `t > 0`. -/
theorem L₁₀_pos_imag_axis : ResToImagAxis.Pos L₁₀ := L₁₀_pos

/-- The function `Q(t) = Re(F(it)/G(it))` for `t > 0`. -/
noncomputable def Q (t : ℝ) : ℝ :=
  if ht : 0 < t then
    (F ⟨Complex.I * t, by simp [ht]⟩).re / (G ⟨Complex.I * t, by simp [ht]⟩).re
  else 0

/-- `Q(t) = F(it)/G(it)` equals the real quotient for `t > 0`. -/
theorem Q_eq_F_div_G (t : ℝ) (ht : 0 < t) :
    Q t = (F ⟨Complex.I * t, by simp [ht]⟩).re / (G ⟨Complex.I * t, by simp [ht]⟩).re := by
  simp [Q, ht]

/-- `Q` is differentiable on `(0, ∞)`. -/
theorem Q_differentiableOn : DifferentiableOn ℝ Q (Set.Ioi 0) := by
  intro t ht
  simp only [Set.mem_Ioi] at ht
  have hF_re_diff := (hasDerivAt_resToImagAxis_re F_holo ht).differentiableAt
  have hG_re_diff := (hasDerivAt_resToImagAxis_re G_holo ht).differentiableAt
  have hG_ne : (G.resToImagAxis t).re ≠ 0 :=
    ne_of_gt (G_imag_axis_pos.2 t ht)
  apply (hF_re_diff.div hG_re_diff hG_ne).differentiableWithinAt.congr_of_eventuallyEq_of_mem
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_Ioi] at hs
    simp [Q, hs, ResToImagAxis]
  · simp only [Set.mem_Ioi, ht]

/-- The derivative of Q is `(-2π) * L₁,₀(it) / G(it)²`. -/
theorem deriv_Q (t : ℝ) (ht : 0 < t) :
    deriv Q t = (-2 * π) * (L₁₀ ⟨Complex.I * t, by simp [ht]⟩).re /
      (G ⟨Complex.I * t, by simp [ht]⟩).re ^ 2 := by
  set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩ with hz_def
  have hF_deriv := hasDerivAt_resToImagAxis_re F_holo ht
  have hG_deriv := hasDerivAt_resToImagAxis_re G_holo ht
  have hG_pos : 0 < (G z).re := by simpa [ResToImagAxis, ht] using G_imag_axis_pos.2 t ht
  have hG_ne : (G.resToImagAxis t).re ≠ 0 := by
    simpa [ResToImagAxis, ht, hz_def] using ne_of_gt hG_pos
  have hQ_eq : Q =ᶠ[nhds t] (fun s => (F.resToImagAxis s).re / (G.resToImagAxis s).re) := by
    filter_upwards [lt_mem_nhds ht] with s hs
    simp only [Q, hs, ↓reduceDIte, Function.resToImagAxis_apply, ResToImagAxis]
  rw [hQ_eq.deriv_eq]
  have hdiv : deriv (fun s => (F.resToImagAxis s).re / (G.resToImagAxis s).re) t =
      (deriv (fun s => (F.resToImagAxis s).re) t * (G.resToImagAxis t).re -
       (F.resToImagAxis t).re * deriv (fun s => (G.resToImagAxis s).re) t) /
      (G.resToImagAxis t).re ^ 2 :=
    deriv_div hF_deriv.differentiableAt hG_deriv.differentiableAt hG_ne
  rw [hdiv, hF_deriv.deriv, hG_deriv.deriv]
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, hz_def]
  have hF_real := F_imag_axis_real t ht
  have hG_real := G_imag_axis_real t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte] at hF_real hG_real
  have hL₁₀ := L₁₀_eq_FD_G_sub_F_DG z
  simp only [hz_def] at hL₁₀ hF_real hG_real
  rw [hL₁₀]
  simp only [mul_re, sub_re, hF_real, hG_real, mul_zero, sub_zero, zero_mul]
  ring

/-- `deriv Q t < 0` for all `t > 0`. -/
theorem deriv_Q_neg (t : ℝ) (ht : 0 < t) : deriv Q t < 0 := by
  rw [deriv_Q t ht]
  have hL := L₁₀_pos.2 t ht
  have hG := G_imag_axis_pos.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hL hG
  exact div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) (by positivity)

/-- **Proposition 8.12**: `Q` is strictly decreasing on `(0, ∞)`. -/
theorem Q_strictAntiOn : StrictAntiOn Q (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg
  · exact convex_Ioi 0
  · exact Q_differentiableOn.continuousOn
  · intro t ht
    rw [interior_Ioi] at ht
    exact deriv_Q_neg t ht

/-- Corollary: `Q` is strictly anti-monotone (decreasing) as a function on positive reals. -/
theorem Q_strictAnti : ∀ {t₁ t₂ : ℝ}, 0 < t₁ → t₁ < t₂ → Q t₂ < Q t₁ := by
  intro t₁ t₂ ht₁ ht₁₂
  exact Q_strictAntiOn (Set.mem_Ioi.mpr ht₁) (Set.mem_Ioi.mpr (lt_trans ht₁ ht₁₂)) ht₁₂

/--
$t \mapsto F(it) / G(it)$ is monotone decreasing.
-/
theorem FmodG_antitone : AntitoneOn FmodGReal (Set.Ioi 0) := by
  sorry

/--
$\lim_{t \to 0^+} F(it) / G(it) = 18 / \pi^2$.
-/
theorem FmodG_rightLimitAt_zero :
    Tendsto FmodGReal (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin (18 * (π ^ (-2 : ℤ))) Set.univ) := by
  sorry

/--
Main inequalities between $F$ and $G$ on the imaginary axis.
-/
theorem FG_inequality_1 {t : ℝ} (ht : 0 < t) :
    FReal t + 18 * (π ^ (-2 : ℤ)) * GReal t > 0 := by
  sorry

theorem FG_inequality_2 {t : ℝ} (ht : 0 < t) :
    FReal t - 18 * (π ^ (-2 : ℤ)) * GReal t < 0 := by
  sorry
