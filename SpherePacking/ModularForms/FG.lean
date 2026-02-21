import SpherePacking.ModularForms.QExpansion
import SpherePacking.ModularForms.RamanujanIdentities

open UpperHalfPlane hiding I
open Filter Complex ModularGroup ModularForm SlashAction
open scoped Real Manifold CongruenceSubgroup SlashAction ArithmeticFunction.sigma UpperHalfPlane


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

/- $\mathcal{L}_{1, 0}$ is eventually positive on the imaginary axis. -/
lemma L₁₀_eventuallyPos : ResToImagAxis.EventuallyPos L₁₀ := by
  sorry

/- $\mathcal{L}_{1, 0}$ is positive on the imaginary axis. -/
lemma L₁₀_pos : ResToImagAxis.Pos L₁₀ := antiSerreDerPos SerreDer_22_L₁₀_pos L₁₀_eventuallyPos

/-!
## Asymptotic Analysis of F at Infinity

Vanishing orders and log-derivative limits for the F-side analysis.
These are used to establish `L₁₀_eventuallyPos` (large-t positivity of L₁,₀).
-/

section AsymptoticAnalysis

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
  have h_tendsto : Filter.Tendsto
      (fun z : ℍ => ∑' m : ℕ, a m * cexp (2 * π * Complex.I * z * m))
      atImInfty (nhds (a 0)) := by
    apply QExp.tendsto_nat a
    have hbound : ∀ m : ℕ, ‖a m‖ ≤ ((m + 1 : ℕ) : ℝ) ^ 5 := by
      intro m
      simp only [ha, norm_mul, Complex.norm_natCast]
      have h1 : (ArithmeticFunction.sigma 3 (m + 1) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 4 := by
        exact_mod_cast (sigma_bound 3 (m + 1))
      calc (↑(m + 1) : ℝ) * (ArithmeticFunction.sigma 3 (m + 1) : ℝ)
          ≤ (↑(m + 1) : ℝ) * (↑(m + 1) : ℝ) ^ 4 :=
            mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        _ = (↑(m + 1) : ℝ) ^ 5 := by ring
    apply Summable.of_nonneg_of_le
    · intro m; positivity
    · intro m
      calc ‖a m‖ * rexp (-2 * π * m)
          ≤ ((m + 1 : ℕ) : ℝ) ^ 5 * rexp (-2 * π * m) :=
            mul_le_mul_of_nonneg_right (hbound m) (Real.exp_nonneg _)
        _ = (m + 1 : ℝ) ^ 5 * rexp (-2 * π * m) := by simp
    · exact summable_pow_shift 5
  have h_eq2 : ∀ z : ℍ,
      ∑' m : ℕ, ↑(m + 1) * ↑(ArithmeticFunction.sigma 3 (m + 1)) *
        cexp (2 * π * Complex.I * m * z) =
      ∑' m : ℕ, a m * cexp (2 * π * Complex.I * z * m) := by
    intro z; apply tsum_congr; intro m; simp only [ha]; ring_nf
  simp_rw [h_eq2, ha0] at h_tendsto ⊢
  convert h_tendsto.const_mul (720 : ℂ) using 2; ring

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
  have h_tendsto : Filter.Tendsto
      (fun z : ℍ => ∑' m : ℕ, a m * cexp (2 * π * I * z * m))
      atImInfty (nhds (a 0)) := by
    apply QExp.tendsto_nat a
    have hbound : ∀ m : ℕ, ‖a m‖ ≤ ((m + 1 : ℕ) : ℝ) ^ 6 := by
      intro m
      simp only [ha_def, norm_mul, Complex.norm_natCast, Complex.norm_pow]
      have h1 : (ArithmeticFunction.sigma 3 (m + 1) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 4 := by
        exact_mod_cast (sigma_bound 3 (m + 1))
      calc (↑(m + 1) : ℝ) ^ 2 * (ArithmeticFunction.sigma 3 (m + 1) : ℝ)
          ≤ (↑(m + 1) : ℝ) ^ 2 * (↑(m + 1) : ℝ) ^ 4 :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg (Nat.cast_nonneg _) _)
        _ = (↑(m + 1) : ℝ) ^ 6 := by ring
    apply Summable.of_nonneg_of_le
    · intro m; positivity
    · intro m
      calc ‖a m‖ * rexp (-2 * π * m)
          ≤ ((m + 1 : ℕ) : ℝ) ^ 6 * rexp (-2 * π * m) :=
            mul_le_mul_of_nonneg_right (hbound m) (Real.exp_nonneg _)
        _ = (m + 1 : ℝ) ^ 6 * rexp (-2 * π * m) := by simp
    · exact summable_pow_shift 6
  have h_eq2 : ∀ z : ℍ,
      ∑' m : ℕ, (↑(m + 1) : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) (m + 1)) *
        cexp (2 * π * I * m * z) =
      ∑' m : ℕ, a m * cexp (2 * π * I * z * m) := fun z => by
    simpa [ha_def] using tsum_congr (fun m => by ring_nf)
  simp_rw [h_eq2, ha0] at h_tendsto ⊢
  convert h_tendsto.const_mul (720 : ℂ) using 2; ring

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

end AsymptoticAnalysis

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

/- Functional equation of $F$ -/
theorem F_functional_equation (z : ℍ) :
    F (S • z) = z ^ 12 * F z - 12 * I * π ^ (-1 : ℤ) * z ^ 11 * (F₁ * E₄.toFun) z
      - 36 * π ^ (-2 : ℤ) * z ^ 10 * (E₄.toFun z) ^ 2 := by
  have hLHS : F (S • z) = (E₂ (S • z) * E₄ (S • z) - E₆ (S • z)) ^ 2 := rfl
  have hRHS : F z = (E₂ z * E₄ z - E₆ z) ^ 2 := rfl
  have hF₁E₄ : (F₁ * E₄.toFun) z = (E₂ z * E₄ z - E₆ z) * E₄ z := rfl
  rw [hLHS, hRHS, hF₁E₄, E₂_S_transform, E₄_S_transform, E₆_S_transform]
  simp only [ModularForm.toFun_eq_coe, zpow_neg, zpow_one]
  field_simp
  ring_nf
  simp only [I_sq, I_pow_three]
  field_simp
  ring

theorem F_functional_equation' {t : ℝ} (ht : 0 < t) :
    FReal (1 / t) = t ^ 12 * FReal t - 12 * π ^ (-1 : ℤ) * t ^ 11 * (F₁ * E₄.toFun).resToImagAxis t
      + 36 * π ^ (-2 : ℤ) * t ^ 10 * (E₄.toFun.resToImagAxis t) ^ 2 := by
  let z : ℍ := ⟨I * t, by simp [ht]⟩
  have hF :
      F.resToImagAxis (1 / t) = (t : ℂ) ^ 12 * F z
        - 12 * π ^ (-1 : ℤ) * t ^ 11 * (F₁ * E₄.toFun) z
        + 36 * π ^ (-2 : ℤ) * t ^ 10 * (E₄.toFun z) ^ 2 := by
    rw [ResToImagAxis.one_div_eq_S_smul F ht, F_functional_equation z]
    simp only [z, UpperHalfPlane.coe_mk_subtype, I_mul_t_pow_nat]
    ring_nf
    simp only [I_sq]
    ring
  have hFz : F z = F.resToImagAxis t := by
    simpa [z] using (ResToImagAxis.I_mul_t_eq F t ht)
  have hF₁E₄z : (F₁ * E₄.toFun) z = (F₁ * E₄.toFun).resToImagAxis t := by
    simpa [z] using (ResToImagAxis.I_mul_t_eq (F₁ * E₄.toFun) t ht)
  have hE₄z : E₄.toFun z = E₄.toFun.resToImagAxis t := by
    simpa [z] using (ResToImagAxis.I_mul_t_eq E₄.toFun t ht)
  rw [hFz, hF₁E₄z, hE₄z] at hF
  rw [F_eq_FReal ht, F_eq_FReal (one_div_pos.mpr ht)] at hF
  exact hF

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
  let z : ℍ := ⟨I * t, by simp [ht]⟩
  have hG :
      G.resToImagAxis (1 / t) = (t : ℂ) ^ 10 * H₄.resToImagAxis t ^ 3 *
      (2 * H₄.resToImagAxis t ^ 2 + 5 * H₂.resToImagAxis t * H₄.resToImagAxis t +
       5 * H₂.resToImagAxis t ^ 2) := by
    rw [ResToImagAxis.one_div_eq_S_smul G ht, G_functional_equation z]
    simp only [z, UpperHalfPlane.coe_mk_subtype, I_mul_t_pow_nat,
      ResToImagAxis.I_mul_t_eq H₂ t ht, ResToImagAxis.I_mul_t_eq H₄ t ht]
    ring
  rw [G_eq_GReal (one_div_pos.mpr ht)] at hG
  exact hG

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
  have h_cpow : (s : ℂ) ^ (2 : ℂ) = ((s ^ 2 : ℝ) : ℂ) := by norm_cast
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
  have hNum := numerator_tendsto_at_infty
  have hDen := denominator_tendsto_at_infty
  have hEq : ∀ᶠ s in atTop, FmodGReal (1 / s) =
      (s ^ 2 * FReal s - 12 * π ^ (-1 : ℤ) * s * ((F₁ * E₄.toFun).resToImagAxis s).re
        + 36 * π ^ (-2 : ℤ) * (E₄.toFun.resToImagAxis s).re ^ 2) /
      ((H₄.resToImagAxis s).re ^ 3 *
        (2 * (H₄.resToImagAxis s).re ^ 2 + 5 * (H₂.resToImagAxis s).re * (H₄.resToImagAxis s).re
          + 5 * (H₂.resToImagAxis s).re ^ 2)) := by
    filter_upwards [eventually_gt_atTop 0] with s hs
    have hF := F_functional_equation' hs
    have hG := G_functional_eq_real hs
    have hs10_ne : s ^ 10 ≠ 0 := pow_ne_zero 10 (ne_of_gt hs)
    rw [ResToImagAxis.Real.eq_real_part
        (ResToImagAxis.Real.mul F₁_imag_axis_real E₄_imag_axis_real) s,
      ResToImagAxis.Real.eq_real_part E₄_imag_axis_real s] at hF
    have hF_real_eq : FReal (1 / s) = s ^ 12 * FReal s
        - 12 * π ^ (-1 : ℤ) * s ^ 11 * ((F₁ * E₄.toFun).resToImagAxis s).re
        + 36 * π ^ (-2 : ℤ) * s ^ 10 * (E₄.toFun.resToImagAxis s).re ^ 2 := by
      apply Complex.ofReal_injective
      simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_zpow π]
      convert hF using 1
    unfold FmodGReal
    rw [hG, hF_real_eq]
    calc _ = s ^ 10 * (s ^ 2 * FReal s - 12 * π ^ (-1 : ℤ) * s *
          ((F₁ * E₄.toFun).resToImagAxis s).re +
        36 * π ^ (-2 : ℤ) * (E₄.toFun.resToImagAxis s).re ^ 2) /
        (s ^ 10 * ((H₄.resToImagAxis s).re ^ 3 *
        (2 * (H₄.resToImagAxis s).re ^ 2 + 5 * (H₂.resToImagAxis s).re * (H₄.resToImagAxis s).re
          + 5 * (H₂.resToImagAxis s).re ^ 2))) := by ring_nf
      _ = _ := mul_div_mul_left _ _ hs10_ne
  have hlim := hNum.div hDen (by norm_num : (2 : ℝ) ≠ 0)
  have hComp : Tendsto (fun t => (t⁻¹ ^ 2 * FReal t⁻¹ - 12 * π ^ (-1 : ℤ) * t⁻¹ *
        ((F₁ * E₄.toFun).resToImagAxis t⁻¹).re + 36 * π ^ (-2 : ℤ) *
        (E₄.toFun.resToImagAxis t⁻¹).re ^ 2) / ((H₄.resToImagAxis t⁻¹).re ^ 3 *
        (2 * (H₄.resToImagAxis t⁻¹).re ^ 2 + 5 * (H₂.resToImagAxis t⁻¹).re *
        (H₄.resToImagAxis t⁻¹).re + 5 * (H₂.resToImagAxis t⁻¹).re ^ 2)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (18 * π ^ (-2 : ℤ))) := by
    convert hlim.comp tendsto_inv_nhdsGT_zero using 2; ring
  have hEq' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), FmodGReal t =
      (t⁻¹ ^ 2 * FReal t⁻¹ - 12 * π ^ (-1 : ℤ) * t⁻¹ * ((F₁ * E₄.toFun).resToImagAxis t⁻¹).re
        + 36 * π ^ (-2 : ℤ) * (E₄.toFun.resToImagAxis t⁻¹).re ^ 2) /
      ((H₄.resToImagAxis t⁻¹).re ^ 3 *
        (2 * (H₄.resToImagAxis t⁻¹).re ^ 2 +
          5 * (H₂.resToImagAxis t⁻¹).re * (H₄.resToImagAxis t⁻¹).re +
          5 * (H₂.resToImagAxis t⁻¹).re ^ 2)) := by
    filter_upwards [tendsto_inv_nhdsGT_zero.eventually hEq, self_mem_nhdsWithin] with t ht ht_pos
    simp only [Set.mem_Ioi] at ht_pos
    simpa [one_div, inv_inv] using ht
  exact hComp.congr' (hEq'.mono fun _ ht => ht.symm)

/--
Main inequalities between $F$ and $G$ on the imaginary axis.
-/
theorem FG_inequality_1 {t : ℝ} (ht : 0 < t) :
    FReal t + 18 * (π ^ (-2 : ℤ)) * GReal t > 0 := by
  sorry

theorem FG_inequality_2 {t : ℝ} (ht : 0 < t) :
    FReal t - 18 * (π ^ (-2 : ℤ)) * GReal t < 0 := by
  sorry
