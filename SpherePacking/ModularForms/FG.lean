import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Monotone.Defs

import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.Eisenstein
import SpherePacking.ModularForms.JacobiTheta

open Filter Complex
open scoped Real Manifold UpperHalfPlane


/--
Definition of $F$ and $G$ and auxiliary functions for the inequality between them
on the imaginary axis.
-/
noncomputable def F := (E₂ * E₄.toFun - E₆.toFun) ^ 2

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

/- Some basic facts -/
/-- Helper until MDifferentiable.pow is upstreamed to mathlib -/
lemma MDifferentiable.pow {f : UpperHalfPlane → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (n : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => f z ^ n) := by
  induction n with
  | zero => exact fun _ => mdifferentiableAt_const
  | succ n ih =>
    have : (fun z => f z ^ (n + 1)) = (fun z => f z ^ n * f z) := by ext z; ring
    rw [this]; exact ih.mul hf

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

/- Positivity of (quasi)modular forms. $F, G, H_2$ are all (sum of) squares. -/
lemma negDE₂_pos : ResToImagAxis.Pos negDE₂ := by
  sorry

lemma Δ_fun_pos : ResToImagAxis.Pos Δ_fun := by
  sorry

lemma F_imag_axis_real : ResToImagAxis.Real F := by unfold F; fun_prop

theorem F_imag_axis_pos : ResToImagAxis.Pos F := by
  refine ⟨F_imag_axis_real, fun t ht => ?_⟩
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, F]
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  -- F = (E₂E₄ - E₆)² and we need to show its real part is positive
  -- Since F_imag_axis_real shows F(it).im = 0, we have F(it) = F(it).re
  have hF_real_pre := F_imag_axis_real t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, F] at hF_real_pre
  have hF_real : ((E₂ z * E₄ z - E₆ z) ^ 2).im = 0 := hF_real_pre
  -- The real part of (...)² equals (...)².re
  -- Since the base (E₂E₄ - E₆) is real on imaginary axis, we have (real)² > 0 if base ≠ 0
  -- Use the q-expansion: E₂E₄ - E₆ = 720 * ∑ n * σ₃(n) * q^n
  have hq_exp := E₂_mul_E₄_sub_E₆ z
  -- E₂E₄ - E₆ is real on imaginary axis
  have hE₂_real := E₂_imag_axis_real t ht
  have hE₄_real := E₄_imag_axis_real t ht
  have hE₆_real := E₆_imag_axis_real t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht,
    ↓reduceDIte] at hE₂_real hE₄_real hE₆_real
  -- The hypotheses have E₄.toFun, E₆.toFun but we need E₄, E₆
  -- They're definitionally equal, so use change to match
  have hE₄_real' : (E₄ z).im = 0 := hE₄_real
  have hE₆_real' : (E₆ z).im = 0 := hE₆_real
  have hE₂_real' : (E₂ z).im = 0 := hE₂_real
  have hdiff_real : (E₂ z * E₄ z - E₆ z).im = 0 := by
    simp only [Complex.sub_im, Complex.mul_im, hE₂_real', hE₄_real', hE₆_real', mul_zero, zero_mul,
      add_zero, sub_zero]
  -- For a real number r (im = 0), r² > 0 iff r.re ≠ 0
  -- (E₂E₄ - E₆)² = (E₂E₄ - E₆).re²  since im = 0
  have hsq_eq : ((E₂ z * E₄ z - E₆ z) ^ 2).re = (E₂ z * E₄ z - E₆ z).re ^ 2 := by
    -- (a + 0i)² = a² + 0i, so ((a + 0i)²).re = a²
    have hpow : (E₂ z * E₄ z - E₆ z) ^ 2 =
        (E₂ z * E₄ z - E₆ z) * (E₂ z * E₄ z - E₆ z) := sq _
    rw [hpow, Complex.mul_re]
    simp only [hdiff_real, mul_zero, sub_zero]
    ring
  -- Convert function application to pointwise form
  have hgoal_eq : (((E₂ * E₄.toFun - E₆.toFun) ^ 2) z).re =
      ((E₂ z * E₄ z - E₆ z) ^ 2).re := rfl
  rw [hgoal_eq, hsq_eq]
  -- Now show (E₂E₄ - E₆).re ≠ 0 using the q-expansion
  -- From hq_exp: E₂E₄ - E₆ = 720 * ∑ n*σ₃(n)*q^n
  -- On z = it: q = exp(-2πt) > 0, and the sum has positive terms
  apply sq_pos_of_pos
  -- Goal: 0 < (E₂ z * E₄ z - E₆ z).re
  rw [hq_exp]
  -- Show the sum is positive on imaginary axis
  -- For z = it, exp(2πinz) = exp(-2πnt) which is positive real
  have hz_eq : (z : ℂ) = Complex.I * t := rfl
  -- The real part of 720 * (positive sum) is positive
  -- 720 is real, so (720 * x).re = 720 * x.re
  have h720_real : (720 : ℂ).im = 0 := by norm_num
  rw [Complex.mul_re, h720_real, zero_mul, sub_zero]
  apply mul_pos (by norm_num : (0 : ℝ) < 720)
  -- Show the sum has positive real part
  -- On z = it, each term n * σ₃(n) * exp(2πinz) = n * σ₃(n) * exp(-2πnt) is positive real
  -- For n : ℕ+: n > 0, σ₃(n) ≥ 1, exp(-2πnt) > 0
  -- So each term > 0, and their sum > 0
  -- Step 1: Summability of the series
  have hsum : Summable fun n : ℕ+ => (↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 3) ↑n) *
      exp (2 * ↑Real.pi * I * z * n) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le
    · intro n; exact norm_nonneg _
    · intro n
      calc ‖(↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 3) ↑n) *
              exp (2 * ↑Real.pi * I * z * n)‖
          = ‖(↑↑n : ℂ)‖ * ‖(↑((ArithmeticFunction.sigma 3) ↑n) : ℂ)‖ *
              ‖exp (2 * ↑Real.pi * I * z * n)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ (↑n : ℝ) * (↑n : ℝ)^4 * ‖exp (2 * ↑Real.pi * I * z * n)‖ := by
            gcongr
            · rw [Complex.norm_natCast]
            · rw [Complex.norm_natCast]
              have hbound := sigma_bound 3 n
              exact_mod_cast hbound
        _ = ‖(↑n : ℂ) ^ 5 * exp (2 * ↑Real.pi * I * z * n)‖ := by
            rw [norm_mul, Complex.norm_pow, Complex.norm_natCast]
            ring
    · have := a33 5 1 z
      simp only [PNat.val_ofNat, Nat.cast_one, mul_one] at this
      exact summable_norm_iff.mpr this
  -- Adjust the exponent form to match the goal
  have hsum' : Summable fun n : ℕ+ => (↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 3) ↑n) *
      exp (2 * ↑Real.pi * I * ↑n * z) := by
    simp_rw [show ∀ n : ℕ+, (2 : ℂ) * ↑Real.pi * I * ↑n * z =
        2 * ↑Real.pi * I * z * n by intro n; ring]
    exact hsum
  -- Key simplification: on z = I*t, the exponential becomes real
  have hexp_simpl : ∀ n : ℕ+, exp (2 * ↑Real.pi * I * ↑n * z) =
      Real.exp (-(2 * Real.pi * n * t)) := by
    intro n
    rw [hz_eq]
    have harg : (2 : ℂ) * ↑Real.pi * I * ↑n * (I * ↑t) =
        ↑(-(2 * Real.pi * (n : ℕ) * t)) := by
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [harg, ofReal_exp]
  -- Step 2: Each term is real on imaginary axis: n * σ(3,n) * exp(-2πnt)
  have hterm_real : ∀ n : ℕ+, ((↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 3) ↑n) *
      exp (2 * ↑Real.pi * I * ↑n * z)).im = 0 := by
    intro n
    rw [hexp_simpl]
    simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero,
      ofReal_re, ofReal_im, mul_zero]
  -- Step 3: Each term is positive
  have hterm_pos : ∀ n : ℕ+, 0 < ((↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 3) ↑n) *
      exp (2 * ↑Real.pi * I * ↑n * z)).re := by
    intro n
    rw [hexp_simpl]
    simp only [mul_re, natCast_re, natCast_im, sub_zero,
      ofReal_re, ofReal_im, mul_zero]
    -- Term is n * σ(3,n) * exp(-2πnt), all factors positive
    apply mul_pos
    · apply mul_pos
      · exact_mod_cast n.pos
      · exact_mod_cast ArithmeticFunction.sigma_pos 3 n n.ne_zero
    · exact Real.exp_pos _
  -- Step 4: Sum of positive terms is positive
  have hsum_re : Summable fun n : ℕ+ => ((↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 3) ↑n) *
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * z)).re := by
    obtain ⟨x, hx⟩ := hsum'
    exact ⟨x.re, Complex.hasSum_re hx⟩
  rw [Complex.re_tsum hsum']
  exact Summable.tsum_pos hsum_re (fun n => le_of_lt (hterm_pos n)) 1 (hterm_pos 1)

lemma G_imag_axis_real : ResToImagAxis.Real G := by unfold G; fun_prop

lemma G_imag_axis_pos : ResToImagAxis.Pos G := by unfold G; fun_prop (disch := positivity)

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
lemma SerreDer_22_L₁₀_real : ResToImagAxis.Real SerreDer_22_L₁₀ := by
  rw [SerreDer_22_L₁₀_SerreDer, MLDE_F, MLDE_G, ResToImagAxis.Real]
  intro t ht
  ring_nf
  simp only [Function.resToImagAxis_apply]
  sorry

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
