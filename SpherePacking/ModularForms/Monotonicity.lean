/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.JacobiTheta
import SpherePacking.ModularForms.ResToImagAxis
import SpherePacking.ModularForms.Delta

/-!
# Monotonicity of Q = F/G on the Imaginary Axis

This file proves Proposition 8.12 from the blueprint: the function
`Q(t) = F(it)/G(it)` is strictly decreasing on `(0, ∞)`.

## Main definitions

* `MonotoneFG.G` : The function `G(z) = H₂(z)³` (Definition 8.3)
* `MonotoneFG.L₁₀` : The function `L₁,₀ = (∂₁₀F)G - F(∂₁₀G)` (Proposition 8.12)
* `MonotoneFG.Q` : The function `Q(t) = F(it)/G(it)` restricted to `t > 0`

## Main results

* `MonotoneFG.L₁₀_pos_imag_axis` : `L₁,₀(it) > 0` for all `t > 0`
* `MonotoneFG.Q_strictAntiOn` : `Q` is strictly decreasing on `(0, ∞)`

## Blueprint references

* Definition 8.3: Definitions of F and G
* Lemma 8.8: Differential equations (65) and (66)
* Corollary 8.9: Positivity of RHS of (65) and (66) on imaginary axis
* Proposition 8.12: Monotonicity of Q
-/

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap

open scoped ModularForm MatrixGroups Manifold

namespace MonotoneFG

/-!
## Section 0: Helper Lemmas for Imaginary Axis Properties
-/

/-- `im` distributes over tsum when each term has zero imaginary part. -/
lemma Complex.im_tsum_eq_zero_of_im_eq_zero (f : ℤ → ℂ)
    (hf : Summable f) (him : ∀ n, (f n).im = 0) :
    (∑' n : ℤ, f n).im = 0 := by
  rw [Complex.im_tsum hf]
  simp [him]

/-- `(-1 : ℂ)^n` has zero imaginary part for any integer n. -/
lemma neg_one_zpow_im_eq_zero (n : ℤ) : ((-1 : ℂ) ^ n).im = 0 := by
  rcases Int.even_or_odd n with hn | hn
  · rw [hn.neg_one_zpow]; simp
  · rw [hn.neg_one_zpow]; simp

/-- For even k, `I^k = (-1)^(k/2)`. -/
lemma I_pow_even (k : ℕ) (hk : Even k) : Complex.I ^ k = (-1 : ℂ) ^ (k / 2) := by
  obtain ⟨m, rfl⟩ := hk
  have h1 : (m + m) / 2 = m := by omega
  rw [h1]
  rw [show m + m = 2 * m by ring, pow_mul, I_sq]

/-- `I^k` is real for even k (since `(-1)^m` is `±1`). -/
lemma I_pow_even_real (k : ℕ) (hk : Even k) : (Complex.I ^ k).im = 0 := by
  rw [I_pow_even k hk]
  have : ((-1 : ℂ) ^ (k / 2)).im = 0 := by
    induction k / 2 with
    | zero => simp
    | succ n ih => simp [pow_succ, ih]
  exact this

/-- `(-2πi)^k` is real for even k. -/
lemma neg_two_pi_I_pow_even_real (k : ℕ) (hk : Even k) :
    ((-2 * Real.pi * Complex.I) ^ k : ℂ).im = 0 := by
  have h : (-2 * Real.pi * Complex.I) ^ k = ((-2 * Real.pi) ^ k : ℂ) * Complex.I ^ k := by ring
  rw [h]
  have h1 : ((-(2 * Real.pi)) ^ k : ℂ).im = 0 := by
    have hcast : ((-(2 * Real.pi)) ^ k : ℂ) = (((-2 * Real.pi) ^ k : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    exact Complex.ofReal_im _
  have h2 : (Complex.I ^ k : ℂ).im = 0 := I_pow_even_real k hk
  have heq : (-2 * Real.pi : ℂ) ^ k = (-(2 * Real.pi)) ^ k := by ring
  rw [heq]
  simp [Complex.mul_im, h1, h2]

/-- Each term Θ₂_term n (I*t) has zero imaginary part for t > 0. -/
lemma Θ₂_term_imag_axis_im (n : ℤ) (t : ℝ) (ht : 0 < t) :
    (Θ₂_term n ⟨Complex.I * t, by simp [ht]⟩).im = 0 := by
  unfold Θ₂_term
  change (cexp (Real.pi * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * (Complex.I * t))).im = 0
  have hexpr : Real.pi * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * (Complex.I * ↑t) =
      (-(Real.pi * ((n : ℝ) + 1/2) ^ 2 * t) : ℝ) := by
    have hI : Complex.I ^ 2 = -1 := I_sq
    push_cast
    ring_nf
    simp only [hI]
    ring
  rw [hexpr]
  exact exp_ofReal_im _

/-- Θ₂(I*t) has zero imaginary part for t > 0. -/
lemma Θ₂_imag_axis_im (t : ℝ) (ht : 0 < t) :
    (Θ₂ ⟨Complex.I * t, by simp [ht]⟩).im = 0 := by
  unfold Θ₂
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hsum : Summable fun n : ℤ => Θ₂_term n z := by
    -- Use Θ₂_term_as_jacobiTheta₂_term and summable_jacobiTheta₂_term_iff
    simp_rw [Θ₂_term_as_jacobiTheta₂_term]
    apply Summable.mul_left
    rw [summable_jacobiTheta₂_term_iff]
    exact z.im_pos
  apply Complex.im_tsum_eq_zero_of_im_eq_zero _ hsum
  intro n
  exact Θ₂_term_imag_axis_im n t ht

/-!
## Section 1: Definitions of F, G, and Q

Note: `F = (E₂ * E₄ - E₆)²` is already defined in `Derivative.lean`.
We define `G = H₂³ (2H₂² + 5H₂H₄ + 5H₄²)` here per Definition 8.3 of the blueprint.

TODO: After PR #193 merges, these definitions should be imported from
`SpherePacking.ModularForms.FG` instead of being defined here.
-/

/--
The function `G(z) = H₂(z)³ (2 H₂(z)² + 5 H₂(z) H₄(z) + 5 H₄(z)²)` from Definition 8.3 of the blueprint.

TODO: After PR #193 merges, import this definition from `SpherePacking.ModularForms.FG`
instead of defining it here.
-/
noncomputable def G (z : ℍ) : ℂ := H₂ z ^ 3 * (2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2)

/--
`G` is holomorphic on the upper half-plane.
Blueprint: G = H₂³ (2H₂² + 5H₂H₄ + 5H₄²) is holomorphic since H₂ and H₄ are holomorphic.

TODO: After PR #193 merges, this should follow from the holomorphicity results there.
-/
theorem G_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
  -- G = H₂³ * (2H₂² + 5H₂H₄ + 5H₄²), composition of holomorphic functions
  have hH₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂ := H₂_SIF_MDifferentiable
  have hH₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄ := H₄_SIF_MDifferentiable
  unfold G
  have hH₂_sq' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => H₂ z ^ 2) := by
    have : (fun z => H₂ z ^ 2) = (fun z => H₂ z * H₂ z) := by ext z; ring
    rw [this]; exact hH₂.mul hH₂
  have hH₂_cube : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => H₂ z ^ 3) := by
    have : (fun z => H₂ z ^ 3) = (fun z => H₂ z ^ 2 * H₂ z) := by ext z; ring
    rw [this]; exact hH₂_sq'.mul hH₂
  have hH₄_sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => H₄ z ^ 2) := by
    have : (fun z => H₄ z ^ 2) = (fun z => H₄ z * H₄ z) := by ext z; ring
    rw [this]; exact hH₄.mul hH₄
  have hH₂H₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => H₂ z * H₄ z) := hH₂.mul hH₄
  have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 2 * H₂ z ^ 2) := by
    have : (fun z => 2 * H₂ z ^ 2) = (fun z => (2 : ℂ) • H₂ z ^ 2) := by ext z; simp [smul_eq_mul]
    rw [this]; exact hH₂_sq'.const_smul (2 : ℂ)
  have h2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 5 * H₂ z * H₄ z) := by
    have : (fun z => 5 * H₂ z * H₄ z) = (fun z => (5 : ℂ) • (H₂ z * H₄ z)) := by
      ext z; simp [smul_eq_mul]; ring
    rw [this]; exact hH₂H₄.const_smul (5 : ℂ)
  have h3 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 5 * H₄ z ^ 2) := by
    have : (fun z => 5 * H₄ z ^ 2) = (fun z => (5 : ℂ) • H₄ z ^ 2) := by ext z; simp [smul_eq_mul]
    rw [this]; exact hH₄_sq.const_smul (5 : ℂ)
  have hquad : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z => 2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2) := (h1.add h2).add h3
  exact hH₂_cube.mul hquad

/-!
## Section 2: Positivity of F and G on the Imaginary Axis
-/

/--
`H₂(it)` is real for all `t > 0`.
Blueprint: Follows from the q-expansion having real coefficients.
Proof strategy: H₂ = Θ₂^4 where Θ₂(it) = ∑ₙ exp(-π(n+1/2)²t) is a sum of real exponentials.
-/
theorem H₂_imag_axis_real : ResToImagAxis.Real H₂ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, H₂]
  -- H₂ = Θ₂^4, and Θ₂(I*t) has zero imaginary part, so H₂(I*t) = Θ₂(I*t)^4 has zero imaginary part
  have hΘ₂_im := Θ₂_imag_axis_im t ht
  exact Complex.im_pow_eq_zero_of_im_eq_zero hΘ₂_im 4

/-- Each term Θ₂_term n (I*t) has positive real part equal to exp(-π(n+1/2)²t) for t > 0. -/
lemma Θ₂_term_imag_axis_re (n : ℤ) (t : ℝ) (ht : 0 < t) :
    (Θ₂_term n ⟨Complex.I * t, by simp [ht]⟩).re =
      Real.exp (-Real.pi * ((n : ℝ) + 1/2) ^ 2 * t) := by
  unfold Θ₂_term
  change (cexp (Real.pi * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * (Complex.I * t))).re = _
  have hexpr : Real.pi * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * (Complex.I * ↑t) =
      (-(Real.pi * ((n : ℝ) + 1/2) ^ 2 * t) : ℝ) := by
    have hI : Complex.I ^ 2 = -1 := I_sq
    push_cast
    ring_nf
    simp only [hI]
    ring
  rw [hexpr]
  rw [Complex.exp_ofReal_re]
  ring_nf

/-- Each term Θ₂_term n (I*t) has positive real part for t > 0. -/
lemma Θ₂_term_imag_axis_re_pos (n : ℤ) (t : ℝ) (ht : 0 < t) :
    0 < (Θ₂_term n ⟨Complex.I * t, by simp [ht]⟩).re := by
  rw [Θ₂_term_imag_axis_re n t ht]
  exact Real.exp_pos _

/-- Θ₂(I*t) has positive real part for t > 0.
Proof: Each term Θ₂_term n (I*t) = exp(-π(n+1/2)²t) is a positive real.
The sum of positive reals is positive. -/
lemma Θ₂_imag_axis_re_pos (t : ℝ) (ht : 0 < t) :
    0 < (Θ₂ ⟨Complex.I * t, by simp [ht]⟩).re := by
  -- Θ₂(it) = ∑ₙ exp(-π(n+1/2)²t) where each term is positive real
  -- The sum of positive terms (at least one nonzero) is positive
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  -- Summability of the complex series
  have hsum : Summable fun n : ℤ => Θ₂_term n z := by
    simp_rw [Θ₂_term_as_jacobiTheta₂_term]
    apply Summable.mul_left
    rw [summable_jacobiTheta₂_term_iff]
    exact z.im_pos
  -- Convert complex tsum to real part of tsum
  unfold Θ₂
  rw [Complex.re_tsum hsum]
  -- Summability of the real series
  have hsum_re : Summable fun n : ℤ => (Θ₂_term n z).re := by
    obtain ⟨x, hx⟩ := hsum
    exact ⟨x.re, Complex.hasSum_re hx⟩
  -- Each term is positive
  have hpos : ∀ n : ℤ, 0 < (Θ₂_term n z).re := fun n => Θ₂_term_imag_axis_re_pos n t ht
  -- Use that sum of positive terms is positive
  exact Summable.tsum_pos hsum_re (fun n => le_of_lt (hpos n)) 0 (hpos 0)

/--
`H₂(it) > 0` for all `t > 0`.
Blueprint: Lemma 6.43 - H₂ is positive on the imaginary axis.
Proof strategy: Each term exp(-π(n+1/2)²t) > 0, so Θ₂(it) > 0, hence H₂ = Θ₂^4 > 0.
-/
theorem H₂_imag_axis_pos : ResToImagAxis.Pos H₂ := by
  constructor
  · exact H₂_imag_axis_real
  · intro t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, H₂]
    -- H₂ = Θ₂^4 where Θ₂(it) is real and positive
    -- For z with z.im = 0 and z.re > 0, (z^4).re = (z.re)^4 > 0
    have hΘ₂_im := Θ₂_imag_axis_im t ht
    have hΘ₂_re_pos := Θ₂_imag_axis_re_pos t ht
    -- z^4 for z real equals z.re^4
    have hpow : (Θ₂ ⟨Complex.I * t, by simp [ht]⟩ ^ 4).re =
        (Θ₂ ⟨Complex.I * t, by simp [ht]⟩).re ^ 4 := by
      set z := Θ₂ ⟨Complex.I * t, by simp [ht]⟩ with hz_def
      have hz_real : z.im = 0 := hΘ₂_im
      -- When im = 0, z = z.re (as complex), so z^4 = (z.re)^4
      have hz_eq : z = (z.re : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hz_real]
      rw [hz_eq]
      norm_cast
    rw [hpow]
    exact pow_pos hΘ₂_re_pos 4

/-!
### H₄ imaginary axis properties

Similar to H₂, we prove H₄ = Θ₄⁴ is real and positive on the imaginary axis.
Θ₄_term n (it) = (-1)^n * exp(-π n² t) is real for each n.
-/

/-- Each term Θ₄_term n (I*t) has zero imaginary part for t > 0. -/
lemma Θ₄_term_imag_axis_im (n : ℤ) (t : ℝ) (ht : 0 < t) :
    (Θ₄_term n ⟨Complex.I * t, by simp [ht]⟩).im = 0 := by
  unfold Θ₄_term
  change ((-1 : ℂ) ^ n * cexp (Real.pi * Complex.I * (n : ℂ) ^ 2 * (Complex.I * t))).im = 0
  -- Simplify the exponent: π * I * n² * (I*t) = -π * n² * t
  have hexpr : Real.pi * Complex.I * (n : ℂ) ^ 2 * (Complex.I * t) =
      (-(Real.pi * (n : ℝ) ^ 2 * t) : ℝ) := by
    have hI : Complex.I ^ 2 = -1 := I_sq
    push_cast
    ring_nf
    simp only [hI]
    ring
  rw [hexpr]
  -- Now we have (-1)^n * exp(real), both are real
  have hexp_real : (cexp (-(Real.pi * (n : ℝ) ^ 2 * t) : ℝ)).im = 0 := exp_ofReal_im _
  have hneg_one_real : ((-1 : ℂ) ^ n).im = 0 := neg_one_zpow_im_eq_zero n
  simp only [Complex.mul_im, hneg_one_real, hexp_real, mul_zero, zero_mul, add_zero]

/-- Θ₄(I*t) has zero imaginary part for t > 0. -/
lemma Θ₄_imag_axis_im (t : ℝ) (ht : 0 < t) :
    (Θ₄ ⟨Complex.I * t, by simp [ht]⟩).im = 0 := by
  unfold Θ₄
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hsum : Summable fun n : ℤ => Θ₄_term n z := by
    simp_rw [Θ₄_term_as_jacobiTheta₂_term]
    rw [summable_jacobiTheta₂_term_iff]
    exact z.im_pos
  apply Complex.im_tsum_eq_zero_of_im_eq_zero _ hsum
  intro n
  exact Θ₄_term_imag_axis_im n t ht

/--
`H₄(it)` is real for all `t > 0`.
Blueprint: Corollary 6.43 - follows from Θ₄ being real on the imaginary axis.
-/
theorem H₄_imag_axis_real : ResToImagAxis.Real H₄ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, H₄]
  have hΘ₄_im := Θ₄_imag_axis_im t ht
  exact Complex.im_pow_eq_zero_of_im_eq_zero hΘ₄_im 4

/--
`H₄(it) > 0` for all `t > 0`.
Blueprint: Corollary 6.43 - H₄ is positive on the imaginary axis.

TODO: The full proof requires showing Θ₄(it) ≠ 0, which follows from theta function
theory (Θ₄ has no zeros on the imaginary axis). For now we use sorry.
After PR #193 merges, use the H₄_pos lemma from FG.lean.
-/
theorem H₄_imag_axis_pos : ResToImagAxis.Pos H₄ := by
  constructor
  · exact H₄_imag_axis_real
  · intro t ht
    -- Strategy: Use H₄_S_action and ResToImagAxis.SlashActionS to relate
    -- H₄ positivity to H₂ positivity via the modular S-transformation
    -- From H₄_S_action: (H₄ ∣[2] S) = -H₂
    -- From SlashActionS: (H₄ ∣[2] S).resToImagAxis (1/t) = I^(-2) * (1/t)^(-2) * H₄.resToImagAxis t
    -- Since I^(-2) = -1 and (1/t)^(-2) = t^2, we get:
    -- -H₂.resToImagAxis (1/t) = -t^2 * H₄.resToImagAxis t
    -- Thus: H₂.resToImagAxis (1/t) = t^2 * H₄.resToImagAxis t
    -- Since H₂.resToImagAxis (1/t).re > 0 and t^2 > 0, we get H₄.resToImagAxis t.re > 0
    --
    -- The type coercion details are complex; using sorry for now.
    -- TODO: Complete the S-transform proof or use PR #193's FG.lean lemmas
    sorry

/--
`G(it)` is real for all `t > 0`.
Blueprint: G = H₂³ (2H₂² + 5H₂H₄ + 5H₄²), product of real functions.

TODO: After PR #193 merges, this follows from the G_pos lemma structure in FG.lean.
-/
theorem G_imag_axis_real : ResToImagAxis.Real G := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, G]
  -- H₂ and H₄ are real on the imaginary axis
  have hH₂_real := H₂_imag_axis_real t ht
  have hH₄_real := H₄_imag_axis_real t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hH₂_real hH₄_real
  set h₂ := H₂ ⟨Complex.I * t, by simp [ht]⟩ with hh₂_def
  set h₄ := H₄ ⟨Complex.I * t, by simp [ht]⟩ with hh₄_def
  -- Products and sums of real complex numbers are real
  have h_prod_real : ∀ a b : ℂ, a.im = 0 → b.im = 0 → (a * b).im = 0 := by
    intros a b ha hb; simp [Complex.mul_im, ha, hb]
  have h_add_real : ∀ a b : ℂ, a.im = 0 → b.im = 0 → (a + b).im = 0 := by
    intros a b ha hb; simp [ha, hb]
  have h_pow_real : ∀ a : ℂ, a.im = 0 → ∀ n : ℕ, (a ^ n).im = 0 := by
    intros a ha n; exact Complex.im_pow_eq_zero_of_im_eq_zero ha n
  have h_const_real : ∀ c : ℕ, ((c : ℂ)).im = 0 := by simp
  -- Build up: 2H₂² + 5H₂H₄ + 5H₄² is real
  have hterm1 : (2 * h₂ ^ 2).im = 0 := h_prod_real _ _ (h_const_real 2) (h_pow_real h₂ hH₂_real 2)
  have hterm2 : (5 * h₂ * h₄).im = 0 := by
    apply h_prod_real; apply h_prod_real; exact h_const_real 5; exact hH₂_real; exact hH₄_real
  have hterm3 : (5 * h₄ ^ 2).im = 0 := h_prod_real _ _ (h_const_real 5) (h_pow_real h₄ hH₄_real 2)
  have hquad : (2 * h₂ ^ 2 + 5 * h₂ * h₄ + 5 * h₄ ^ 2).im = 0 :=
    h_add_real _ _ (h_add_real _ _ hterm1 hterm2) hterm3
  have hcube : (h₂ ^ 3).im = 0 := h_pow_real h₂ hH₂_real 3
  exact h_prod_real _ _ hcube hquad

/--
`G(it) > 0` for all `t > 0`.
Blueprint: Lemma 8.6 - follows from H₂(it) > 0 and H₄(it) > 0.
G = H₂³ (2H₂² + 5H₂H₄ + 5H₄²) is positive since all factors are positive.

TODO: After PR #193 merges, use the G_pos lemma from FG.lean.
-/
theorem G_imag_axis_pos : ResToImagAxis.Pos G := by
  constructor
  · exact G_imag_axis_real
  · intro t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, G]
    -- Get positivity and realness of H₂ and H₄
    have hH₂_pos := H₂_imag_axis_pos.2 t ht
    have hH₂_real := H₂_imag_axis_pos.1 t ht
    have hH₄_pos := H₄_imag_axis_pos.2 t ht
    have hH₄_real := H₄_imag_axis_pos.1 t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hH₂_pos hH₂_real
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hH₄_pos hH₄_real
    set h₂ := H₂ ⟨Complex.I * t, by simp [ht]⟩ with hh₂_def
    set h₄ := H₄ ⟨Complex.I * t, by simp [ht]⟩ with hh₄_def
    -- For real positive complex numbers, products preserve positivity
    -- h₂³ > 0 and (2h₂² + 5h₂h₄ + 5h₄²) > 0
    -- Product of positives is positive
    -- Convert h₂, h₄ to real form since they have zero imaginary part
    have h₂_eq : h₂ = (h₂.re : ℂ) := by
      apply Complex.ext <;> simp [hH₂_real]
    have h₄_eq : h₄ = (h₄.re : ℂ) := by
      apply Complex.ext <;> simp [hH₄_real]
    -- Express G in terms of real values
    rw [h₂_eq, h₄_eq]
    -- The expression is now purely real; simplify and extract real part
    simp only [← Complex.ofReal_pow]
    -- Combine into single ofReal
    have h_goal_eq : (↑(h₂.re ^ 3) * (2 * ↑(h₂.re ^ 2) + 5 * ↑h₂.re * ↑h₄.re +
        5 * ↑(h₄.re ^ 2)) : ℂ).re =
        h₂.re ^ 3 * (2 * h₂.re ^ 2 + 5 * h₂.re * h₄.re + 5 * h₄.re ^ 2) := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, zero_mul, add_zero]
      ring
    rw [h_goal_eq]
    apply mul_pos
    · exact pow_pos hH₂_pos 3
    · have hterm1 : 0 < 2 * h₂.re ^ 2 := by positivity
      have hterm2 : 0 < 5 * h₂.re * h₄.re := by positivity
      have hterm3 : 0 < 5 * h₄.re ^ 2 := by positivity
      linarith

/-!
### Helper lemmas for Eisenstein series on imaginary axis
-/

/-- exp(2πinz) is real when z = it (on the imaginary axis). -/
lemma exp_2pi_I_mul_n_imag_axis_im (n : ℕ+) (t : ℝ) (ht : 0 < t) :
    (cexp (2 * π * Complex.I * n * (Complex.I * t))).im = 0 := by
  -- 2πi·n·(it) = 2πi·n·it = -2πnt (real number)
  have h : 2 * π * Complex.I * n * (Complex.I * t) = (-(2 * π * n * t) : ℝ) := by
    have hI : Complex.I ^ 2 = -1 := I_sq
    push_cast
    ring_nf
    simp only [hI]
    ring
  rw [h]
  exact exp_ofReal_im _

/-- exp(2πinz) is real and positive when z = it (on the imaginary axis). -/
lemma exp_2pi_I_mul_n_imag_axis_re_pos (n : ℕ+) (t : ℝ) (ht : 0 < t) :
    0 < (cexp (2 * π * Complex.I * n * (Complex.I * t))).re := by
  have h : 2 * π * Complex.I * n * (Complex.I * t) = (-(2 * π * n * t) : ℝ) := by
    have hI : Complex.I ^ 2 = -1 := I_sq
    push_cast
    ring_nf
    simp only [hI]
    ring
  rw [h, Complex.exp_ofReal_re]
  exact Real.exp_pos _

/-- `E₄(it)` is real for all `t > 0`. -/
theorem E₄_imag_axis_real : ResToImagAxis.Real E₄.toFun := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  -- E₄ = 1 + 240 * ∑ σ₃(n) * q^n where q = exp(2πiz) is real on z = it
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  change (E₄ z).im = 0
  -- Use the q-expansion formula for E₄
  -- E₄(z) = 1 + 240 * ∑ σ₃(n) * q^n where q = exp(2πiz)
  -- For z = it on the imaginary axis:
  -- q = exp(2πi·it) = exp(-2πt) which is real and positive
  -- Since all coefficients (1, 240, σ₃(n)) are real and q^n is real, E₄(it) is real.
  have hk : (3 : ℤ) ≤ 4 := by norm_num
  have hk2 : Even (4 : ℕ) := by exact Nat.even_iff.mpr rfl
  -- Use E_k_q_expansion with explicit proof terms matching E₄'s definition
  have hq := E_k_q_expansion 4 hk hk2 z
  -- E₄ z = E 4 hk z by proof irrelevance (both proofs are for 3 ≤ 4)
  have hE4 : E₄ z = E 4 hk z := rfl
  -- Note: E_k_q_expansion uses (4 : ℕ) → ℤ coercion, but E₄ uses (4 : ℤ) directly
  -- Both are definitionally equal since (4 : ℕ) : ℤ = (4 : ℤ)
  simp only [hE4, Nat.cast_ofNat] at hq ⊢
  rw [hq]
  -- Now show the RHS has zero imaginary part
  simp only [add_im, one_im, zero_add]
  -- The coefficient (1/ζ(4)) * ((-2πi)^4 / 3!) is real:
  -- (-2πi)^4 = (2π)^4 * i^4 = (2π)^4 (real)
  -- ζ(4) = π^4/90 (real)
  -- So the coefficient is real.
  -- Each term σ₃(n) * exp(2πinz) for z = it:
  -- exp(2πin·it) = exp(-2πnt) (real)
  -- σ₃(n) is a natural number (real)
  -- Product of reals is real
  -- Sum of reals is real
  -- The coefficient (1/ζ(4)) * ((-2πi)^4 / 3!) is real since:
  -- (-2πi)^4 = (2π)^4 (because i^4 = 1)
  -- ζ(4) is real
  -- So the product is real.
  -- Each term σ₃(n) * exp(2πinz) for z = it:
  -- exp(2πin·it) = exp(-2πnt) (real)
  -- σ₃(n) is a natural number (real)
  -- We will show each component has zero imaginary part.

  -- Step 1: Show exp(2πinz) is real when z = it
  have hterm_im : ∀ n : ℕ+, (↑((ArithmeticFunction.sigma (4 - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n)).im = 0 := by
    intro n
    -- z = I * t, so 2πi·z·n = 2πi·(I*t)·n = -2πnt
    have hz_eq : (z : ℂ) = Complex.I * t := rfl
    have hexp_arg : 2 * ↑Real.pi * Complex.I * z * n = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
      rw [hz_eq]
      have hI : Complex.I ^ 2 = -1 := I_sq
      push_cast
      ring_nf
      simp only [hI]
      ring
    rw [hexp_arg]
    -- exp of a real number is real
    have hexp_real : (cexp (-(2 * Real.pi * (n : ℝ) * t) : ℝ)).im = 0 := exp_ofReal_im _
    -- σ_3(n) is a natural number, so its cast to ℂ is real
    have hsigma_real : (↑((ArithmeticFunction.sigma 3) ↑n) : ℂ).im = 0 := by simp
    -- Product of reals is real: (a + 0i) * (b + 0i) has im = a*0 + 0*b = 0
    simp only [Complex.mul_im, hsigma_real, hexp_real, mul_zero, zero_mul, add_zero]

  -- Step 2: Summability of the series
  have hsum : Summable fun n : ℕ+ => ↑((ArithmeticFunction.sigma 3) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n) := by
    -- Use that σ_k(n) ≤ n^(k+1) via sigma_bound, and a33 for n^k * q^n summability
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le
    · intro n
      exact norm_nonneg _
    · intro n
      calc ‖↑((ArithmeticFunction.sigma 3) ↑n) * cexp (2 * ↑Real.pi * Complex.I * z * n)‖
          = ‖(↑((ArithmeticFunction.sigma 3) ↑n) : ℂ)‖ *
            ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := norm_mul _ _
        _ ≤ ‖(↑n : ℂ) ^ 4‖ * ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := by
          apply mul_le_mul_of_nonneg_right
          · rw [Complex.norm_natCast, Complex.norm_pow, Complex.norm_natCast]
            -- Use sigma_bound: σ k n ≤ n ^ (k + 1)
            have hbound := sigma_bound 3 n
            exact_mod_cast hbound
          · exact norm_nonneg _
        _ = ‖(↑n : ℂ) ^ 4 * cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := (norm_mul _ _).symm
    · -- The bound n^4 * exp(...) is summable via a33
      have := a33 4 1 z
      simp only [PNat.val_ofNat, Nat.cast_one, mul_one] at this
      exact summable_norm_iff.mpr this

  -- Step 3: The sum has zero imaginary part
  have hsum_im : (∑' (n : ℕ+), ↑((ArithmeticFunction.sigma (4 - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n)).im = 0 := by
    rw [Complex.im_tsum hsum]
    simp only [hterm_im, tsum_zero]

  -- Step 4: Show the coefficient is real and product with sum is real
  -- The coefficient is (1/ζ(4)) * ((-2πi)^4 / 3!)
  -- (-2πi)^4 is real (proved in neg_two_pi_I_pow_even_real)
  -- ζ(4) is real (it's π^4/90)
  -- So the coefficient is real, and product with real sum is real

  -- Show (-2πi)^4 is real
  have hpow_im : ((-2 * Real.pi * Complex.I) ^ 4 : ℂ).im = 0 :=
    neg_two_pi_I_pow_even_real 4 (by norm_num)

  -- Show the factorial term is real
  have hfact_im : ((4 - 1).factorial : ℂ).im = 0 := by simp

  -- Show 1/ζ(4) is real (ζ(4) = π^4/90 is real)
  have hzeta_im : (riemannZeta 4).im = 0 := by
    rw [riemannZeta_four]
    have h : (↑Real.pi ^ 4 / 90 : ℂ) = ((Real.pi ^ 4 / 90 : ℝ) : ℂ) := by push_cast; ring
    rw [h]
    exact ofReal_im _

  have hinv_zeta_im : (1 / riemannZeta 4).im = 0 := by
    rw [Complex.div_im, Complex.one_im, Complex.one_re, hzeta_im]
    ring

  -- Now build up: show each factor is real, then product is real
  have h_prod_im : ∀ a b : ℂ, a.im = 0 → b.im = 0 → (a * b).im = 0 := by
    intros a b ha hb; simp [Complex.mul_im, ha, hb]
  have h_div_im : ∀ a b : ℂ, a.im = 0 → b.im = 0 → (a / b).im = 0 := by
    intros a b ha hb; simp [Complex.div_im, ha, hb]

  -- (-2πi)^4 / 3! is real
  have hcoeff2_im : ((-2 * Real.pi * Complex.I) ^ 4 / ((4 - 1).factorial : ℂ)).im = 0 :=
    h_div_im _ _ hpow_im hfact_im

  -- Full product with sum is real (combine all three factors directly)
  simp only [Complex.mul_im, Complex.div_im, hinv_zeta_im, hsum_im, hpow_im, hfact_im]
  ring

/-- `E₆(it)` is real for all `t > 0`. -/
theorem E₆_imag_axis_real : ResToImagAxis.Real E₆.toFun := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  -- E₆ = 1 + coeff * ∑ σ₅(n) * q^n where q = exp(2πiz) is real on z = it
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  change (E₆ z).im = 0
  have hk : (3 : ℤ) ≤ 6 := by norm_num
  have hk2 : Even (6 : ℕ) := by exact Nat.even_iff.mpr rfl
  have hq := E_k_q_expansion 6 hk hk2 z
  have hE6 : E₆ z = E 6 hk z := rfl
  simp only [hE6, Nat.cast_ofNat] at hq ⊢
  rw [hq]
  simp only [add_im, one_im, zero_add]

  -- Step 1: Show each term in the sum is real on the imaginary axis
  have hterm_im : ∀ n : ℕ+, (↑((ArithmeticFunction.sigma (6 - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n)).im = 0 := by
    intro n
    have hz_eq : (z : ℂ) = Complex.I * t := rfl
    have hexp_arg : 2 * ↑Real.pi * Complex.I * z * n = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
      rw [hz_eq]
      have hI : Complex.I ^ 2 = -1 := I_sq
      push_cast
      ring_nf
      simp only [hI]
      ring
    rw [hexp_arg]
    have hexp_real : (cexp (-(2 * Real.pi * (n : ℝ) * t) : ℝ)).im = 0 := exp_ofReal_im _
    have hsigma_real : (↑((ArithmeticFunction.sigma 5) ↑n) : ℂ).im = 0 := by simp
    simp only [Complex.mul_im, hsigma_real, hexp_real, mul_zero, zero_mul, add_zero]

  -- Step 2: Summability of the series
  have hsum : Summable fun n : ℕ+ => ↑((ArithmeticFunction.sigma 5) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le
    · intro n
      exact norm_nonneg _
    · intro n
      calc ‖↑((ArithmeticFunction.sigma 5) ↑n) * cexp (2 * ↑Real.pi * Complex.I * z * n)‖
          = ‖(↑((ArithmeticFunction.sigma 5) ↑n) : ℂ)‖ *
            ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := norm_mul _ _
        _ ≤ ‖(↑n : ℂ) ^ 6‖ * ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := by
          apply mul_le_mul_of_nonneg_right
          · rw [Complex.norm_natCast, Complex.norm_pow, Complex.norm_natCast]
            have hbound := sigma_bound 5 n
            exact_mod_cast hbound
          · exact norm_nonneg _
        _ = ‖(↑n : ℂ) ^ 6 * cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := (norm_mul _ _).symm
    · have := a33 6 1 z
      simp only [PNat.val_ofNat, Nat.cast_one, mul_one] at this
      exact summable_norm_iff.mpr this

  -- Step 3: The sum has zero imaginary part
  have hsum_im : (∑' (n : ℕ+), ↑((ArithmeticFunction.sigma (6 - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n)).im = 0 := by
    rw [Complex.im_tsum hsum]
    simp only [hterm_im, tsum_zero]

  -- Step 4: Coefficient is real, product with real sum is real
  -- Show (-2πi)^6 is real
  have hpow_im : ((-2 * Real.pi * Complex.I) ^ 6 : ℂ).im = 0 :=
    neg_two_pi_I_pow_even_real 6 (by norm_num)

  -- Show the factorial term is real
  have hfact_im : ((6 - 1).factorial : ℂ).im = 0 := by simp

  -- Show 1/ζ(6) is real (ζ(6) = π^6/945 is real)
  -- Use riemannZeta_two_mul_nat: ζ(2k) is a real multiple of π^(2k)
  have hzeta_im : (riemannZeta 6).im = 0 := by
    rw [show (6 : ℂ) = 2 * (3 : ℕ) by norm_num]
    rw [riemannZeta_two_mul_nat (by norm_num : (3 : ℕ) ≠ 0)]
    -- Normalize: (3 + 1) = 4, (2 * 3) = 6, (2 * 3).factorial = 720
    simp only [Nat.add_one_sub_one, show 3 + 1 = 4 by rfl, show 2 * 3 = 6 by rfl]
    -- All components are real: (-1)^4 = 1, 2^5 = 32, ↑π^6, ↑(bernoulli 6), ↑6!
    have h1 : ((-1 : ℂ) ^ 4).im = 0 := by norm_num
    have h2 : ((2 : ℂ) ^ 5).im = 0 := by norm_num
    have h3 : ((↑Real.pi : ℂ) ^ 6).im = 0 := by
      have : ((↑Real.pi : ℂ) ^ 6) = ↑(Real.pi ^ 6) := by push_cast; ring
      rw [this]; exact Complex.ofReal_im _
    have h4 : (↑(bernoulli 6) : ℂ).im = 0 := Complex.ofReal_im _
    have h5 : (↑(6 : ℕ).factorial : ℂ).im = 0 := Complex.ofReal_im _
    simp only [Complex.mul_im, Complex.div_im, h1, h2, h3, h4, h5]
    ring

  have hinv_zeta_im : (1 / riemannZeta 6).im = 0 := by
    rw [Complex.div_im, Complex.one_im, Complex.one_re, hzeta_im]
    ring

  -- (-2πi)^6 / 5! is real
  have hcoeff2_im : ((-2 * Real.pi * Complex.I) ^ 6 / ((6 - 1).factorial : ℂ)).im = 0 := by
    -- (-2πi)^6 = -64π^6 is real, and 5! is real, so the quotient is real
    rw [Complex.div_im, hfact_im]
    have h6 : Complex.I ^ 6 = -1 := by
      have : Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by ring
      rw [this, Complex.I_sq]; norm_num
    have hpi_im : ((↑Real.pi : ℂ) ^ 6 * Complex.I ^ 6 * 64 : ℂ).im = 0 := by
      rw [h6]
      have heq : ((↑Real.pi : ℂ) ^ 6 * (-1 : ℂ) * 64 : ℂ) = ↑((-64 : ℝ) * Real.pi ^ 6) := by
        push_cast; ring
      rw [heq]
      exact Complex.ofReal_im _
    -- The goal has ((-↑2 * ↑π * I) ^ 6).im; show this equals 0 using hpi_im
    have h_eq : ((-↑(2 : ℕ) * ↑Real.pi * Complex.I) ^ 6 : ℂ) =
        (↑Real.pi : ℂ) ^ 6 * Complex.I ^ 6 * 64 := by push_cast; ring
    rw [h_eq, hpi_im]
    ring

  -- Full product with sum is real (combine all three factors directly)
  simp only [Complex.mul_im, Complex.div_im, hinv_zeta_im, hsum_im, hpow_im, hfact_im]
  ring

/-- `E₂(it)` is real for all `t > 0`. -/
theorem E₂_imag_axis_real : ResToImagAxis.Real E₂ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  -- E₂ = 1 - 24 * ∑ n * q^n / (1 - q^n) where q = exp(2πiz) is real on z = it
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  change (E₂ z).im = 0
  have hq := E₂_eq z
  rw [hq]
  simp only [sub_im, one_im, zero_sub]

  -- Step 1: Show each term in the sum is real on the imaginary axis
  have hterm_im : ∀ n : ℕ+, (↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z))).im = 0 := by
    intro n
    have hz_eq : (z : ℂ) = Complex.I * t := rfl
    -- exp(2πinz) = exp(2πin·it) = exp(-2πnt) is real
    have hexp_arg : 2 * ↑Real.pi * Complex.I * n * z = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
      rw [hz_eq]
      have hI : Complex.I ^ 2 = -1 := I_sq
      push_cast
      ring_nf
      simp only [hI]
      ring
    have hexp_real : (cexp (-(2 * Real.pi * (n : ℝ) * t) : ℝ)).im = 0 := exp_ofReal_im _
    have hone_sub_real : (1 - cexp (2 * ↑Real.pi * Complex.I * ↑↑n * ↑z)).im = 0 := by
      simp only [Complex.sub_im, Complex.one_im]
      rw [hexp_arg, hexp_real]
      ring
    -- numerator n * exp is real (im = 0)
    have hn_real : (↑n : ℂ).im = 0 := by simp
    have hnum_real : (↑n * cexp (2 * ↑Real.pi * Complex.I * n * z)).im = 0 := by
      rw [Complex.mul_im, hn_real, hexp_arg, hexp_real]
      ring
    -- division of two real numbers is real
    rw [Complex.div_im]
    rw [hnum_real, hone_sub_real]
    ring

  -- Step 2: Summability of the series
  -- Key bound: |n * q^n / (1 - q^n)| ≤ C * |n² * q^n| where C = (1 - |q|)⁻¹
  have hsum : Summable fun n : ℕ+ => ↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z)) := by
    -- Setup: q = exp(2πiz), |q| < 1
    set q := cexp (2 * ↑Real.pi * Complex.I * z) with hq_def
    have hq_norm : ‖q‖ < 1 := exp_upperHalfPlane_lt_one z
    have hq_pos : 0 < 1 - ‖q‖ := by linarith
    -- The majorant series n² * q^n is summable (from a33)
    have ha33 := a33 2 1 z
    simp only [PNat.val_ofNat, Nat.cast_one, mul_one] at ha33
    -- Define the bound function explicitly
    let bound : ℕ+ → ℝ := fun n => (1 - ‖q‖)⁻¹ * ‖(↑↑n : ℂ) ^ 2 *
        cexp (2 * ↑Real.pi * Complex.I * n * z)‖
    -- Apply comparison test with constant factor (1 - ‖q‖)⁻¹
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (f := bound) (fun n => norm_nonneg _)
    case hf.hgf =>
      -- The bound: ‖n * qⁿ / (1 - qⁿ)‖ ≤ (1 - ‖q‖)⁻¹ * ‖n² * qⁿ‖
      intro n
      -- qⁿ = q^n in our notation
      set qn := cexp (2 * ↑Real.pi * Complex.I * n * z) with hqn_def
      -- Show qn = q^n
      have hqn_eq : qn = q ^ (n : ℕ) := by
        simp only [hqn_def, hq_def]
        rw [← Complex.exp_nat_mul]
        congr 1; ring
      -- Norm of qⁿ
      have hqn_norm : ‖qn‖ = ‖q‖ ^ (n : ℕ) := by rw [hqn_eq, norm_pow]
      -- Key: ‖qⁿ‖ ≤ ‖q‖ since ‖q‖ < 1 and n ≥ 1
      have hqn_le_q : ‖qn‖ ≤ ‖q‖ := by
        rw [hqn_norm]
        have hn_pos : 1 ≤ (n : ℕ) := n.one_le
        calc ‖q‖ ^ (n : ℕ) ≤ ‖q‖ ^ 1 := by
              apply pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt hq_norm) hn_pos
          _ = ‖q‖ := pow_one _
      -- Lower bound: ‖1 - qⁿ‖ ≥ 1 - ‖qⁿ‖ ≥ 1 - ‖q‖
      have hdenom_pos : 0 < ‖1 - qn‖ := by
        apply norm_pos_iff.mpr
        intro h
        -- h : 1 - qn = 0, so qn = 1
        have heq : qn = 1 := by simp only [sub_eq_zero] at h; exact h.symm
        rw [hqn_eq] at heq
        have hnorm_one : ‖q ^ (n : ℕ)‖ = 1 := by rw [heq]; simp
        rw [norm_pow] at hnorm_one
        have hlt : ‖q‖ ^ (n : ℕ) < 1 := by
          calc ‖q‖ ^ (n : ℕ) ≤ ‖q‖ ^ 1 := by
                apply pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt hq_norm) n.one_le
            _ = ‖q‖ := pow_one _
            _ < 1 := hq_norm
        linarith
      have hdenom_lower : 1 - ‖q‖ ≤ ‖1 - qn‖ := by
        have h1 : ‖(1 : ℂ)‖ - ‖qn‖ ≤ ‖1 - qn‖ := norm_sub_norm_le 1 qn
        simp only [norm_one] at h1
        calc 1 - ‖q‖ ≤ 1 - ‖qn‖ := by linarith [hqn_le_q]
          _ ≤ ‖1 - qn‖ := h1
      -- Now bound the quotient
      show ‖↑↑n * qn / (1 - qn)‖ ≤ bound n
      calc ‖↑↑n * qn / (1 - qn)‖
          = ‖↑↑n * qn‖ / ‖1 - qn‖ := norm_div _ _
        _ ≤ ‖↑↑n * qn‖ / (1 - ‖q‖) := by
            apply div_le_div_of_nonneg_left (norm_nonneg _) hq_pos hdenom_lower
        _ = (1 - ‖q‖)⁻¹ * ‖↑↑n * qn‖ := by rw [div_eq_inv_mul]
        _ ≤ (1 - ‖q‖)⁻¹ * ‖(↑↑n : ℂ) ^ 2 * qn‖ := by
            apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hq_pos))
            -- Simplify norms: ‖a * b‖ = ‖a‖ * ‖b‖
            have hlhs : ‖↑↑n * qn‖ = (↑↑n : ℝ) * ‖qn‖ := by
              rw [norm_mul, Complex.norm_natCast]
            have hrhs : ‖(↑↑n : ℂ) ^ 2 * qn‖ = (↑↑n : ℝ) ^ 2 * ‖qn‖ := by
              rw [norm_mul, norm_pow, Complex.norm_natCast]
            rw [hlhs, hrhs]
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            have : (↑↑n : ℝ) ≤ (↑↑n : ℝ) ^ 2 := by
              have hn : 1 ≤ (↑↑n : ℝ) := by exact_mod_cast n.one_le
              nlinarith
            exact this
    case hf.hf =>
      -- The majorant is summable
      -- ha33 : Summable (fun c => c^2 * exp(2πi z c))
      -- We need: Summable (fun n => (1-‖q‖)⁻¹ * ‖n^2 * exp(2πi n z)‖)
      -- Reorder arguments: 2π*I*n*z = 2π*I*z*n (by commutativity)
      have ha33' : Summable fun n : ℕ+ => (↑↑n : ℂ) ^ 2 *
          cexp (2 * ↑Real.pi * Complex.I * n * z) := by
        convert ha33 using 2 with n
        ring_nf
      have ha33_norm : Summable fun n : ℕ+ => ‖(↑↑n : ℂ) ^ 2 *
          cexp (2 * ↑Real.pi * Complex.I * n * z)‖ :=
        ha33'.norm
      exact ha33_norm.mul_left (1 - ‖q‖)⁻¹

  -- Step 3: The sum has zero imaginary part
  have hsum_im : (∑' (n : ℕ+), ↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z))).im = 0 := by
    rw [Complex.im_tsum hsum]
    simp only [hterm_im, tsum_zero]

  -- Step 4: 24 * sum is real, so -(24 * sum).im = 0
  have h24_im : (24 : ℂ).im = 0 := by norm_num
  simp only [Complex.mul_im, hsum_im, h24_im, mul_zero, add_zero, neg_zero, zero_mul]

/--
`F(it)` is real for all `t > 0`.
Blueprint: Follows from E₂, E₄, E₆ having real values on the imaginary axis.
-/
theorem F_imag_axis_real : ResToImagAxis.Real F := by
  -- F = (E₂ * E₄ - E₆)² is real if E₂ * E₄ - E₆ is real
  -- which follows from E₂, E₄, E₆ being real on the imaginary axis
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, F]
  -- Get realness of E₂, E₄, E₆
  have hE₂_real := E₂_imag_axis_real t ht
  have hE₄_real := E₄_imag_axis_real t ht
  have hE₆_real := E₆_imag_axis_real t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hE₂_real hE₄_real hE₆_real
  -- If a, b, c are real (im = 0), then (a*b - c)² is real
  set z₂ := E₂ ⟨Complex.I * t, by simp [ht]⟩ with hz₂_def
  set z₄ := E₄ ⟨Complex.I * t, by simp [ht]⟩ with hz₄_def
  set z₆ := E₆ ⟨Complex.I * t, by simp [ht]⟩ with hz₆_def
  -- Need to establish z₄.im = 0 and z₆.im = 0 from hE₄_real and hE₆_real
  have hz₄_im : z₄.im = 0 := hE₄_real
  have hz₆_im : z₆.im = 0 := hE₆_real
  -- (z₂ * z₄ - z₆)² has zero imaginary part when each has zero imaginary part
  have h_prod_im : (z₂ * z₄).im = 0 := by
    simp only [Complex.mul_im]
    rw [hE₂_real, hz₄_im]
    ring
  have h_diff_im : (z₂ * z₄ - z₆).im = 0 := by
    simp only [Complex.sub_im]
    rw [h_prod_im, hz₆_im]
    ring
  exact Complex.im_pow_eq_zero_of_im_eq_zero h_diff_im 2

/--
`F(it) > 0` for all `t > 0`.
Blueprint: Follows from the q-expansion (E₂E₄ - E₆ = 720 * ...) and positivity.

Note: This depends on `E₂_mul_E₄_sub_E₆` which currently has a sorry in Eisenstein.lean.
Once that lemma is proved, this proof can be completed.
-/
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
  -- NOTE: E₂_mul_E₄_sub_E₆ has a sorry in Eisenstein.lean - this proof depends on it
  have hq_exp := E₂_mul_E₄_sub_E₆ z
  -- Strategy once E₂_mul_E₄_sub_E₆ is proved:
  -- On z = it: q^n = exp(-2πnt) is real and positive
  -- Each term n * σ₃(n) * exp(-2πnt) > 0 for n ≥ 1
  -- Sum of positive terms is positive
  -- So E₂E₄ - E₆ = 720 * (positive) > 0
  -- Therefore F = (positive)² > 0
  sorry

/-!
## Section 3: Definition and Properties of L₁,₀

The key object in proving monotonicity is:
  `L₁,₀ = (∂₁₀F)G - F(∂₁₀G)`

By the quotient rule for derivatives:
  `d/dt (F(it)/G(it)) = (-2π) * L₁,₀(it) / G(it)²`

So proving L₁,₀(it) > 0 implies Q is decreasing.
-/

/--
The function `L₁,₀ = (∂₁₀F)G - F(∂₁₀G)`.
Blueprint: Proposition 8.12.
-/
noncomputable def L₁₀ (z : ℍ) : ℂ :=
  serre_D 10 F z * G z - F z * serre_D 10 G z

/--
Alternative form: `L₁,₀ = F'G - FG'` where `'` denotes the normalized derivative.
This follows from the fact that ∂₀ = D (the E₂ term cancels in the difference).
-/
theorem L₁₀_eq_FD_G_sub_F_DG (z : ℍ) :
    L₁₀ z = D F z * G z - F z * D G z := by
  simp only [L₁₀, serre_D]
  ring

/-!
## Section 4: Serre Derivative of L₁,₀

We need to compute `∂₂₂ L₁,₀` and show it's positive on the imaginary axis.
-/

/--
The Serre derivative `∂₂₂ L₁,₀`.
Blueprint: Using the product rule (Theorem 6.53) twice.
-/
theorem serre_D_L₁₀ (z : ℍ) :
    serre_D 22 L₁₀ z = serre_D 12 (serre_D 10 F) z * G z
      - F z * serre_D 12 (serre_D 10 G) z := by
  sorry

/--
`∂₂₂ L₁,₀ = Δ(7200(-E₂')G + 640H₂F)` on the upper half-plane.
Blueprint: Follows from differential equations (65) and (66).
-/
theorem serre_D_L₁₀_eq (z : ℍ) :
    serre_D 22 L₁₀ z = Δ z * (7200 * (-(D E₂ z)) * G z + 640 * H₂ z * F z) := by
  sorry

/--
`∂₂₂ L₁,₀(it) > 0` for all `t > 0`.
Blueprint: Corollary 8.9 - both terms in the expression are positive.
- `-E₂'(it) > 0` (from Ramanujan formula: E₂' = (E₂² - E₄)/12)
- `Δ(it) > 0` (Delta_imag_axis_pos)
- `G(it) > 0` and `H₂(it) > 0` and `F(it) > 0`
-/
theorem serre_D_L₁₀_pos_imag_axis : ResToImagAxis.Pos (serre_D 22 L₁₀) := by
  sorry

/-!
## Section 5: Large-t Positivity of L₁,₀

Using Lemma 8.11 (vanishing orders), we show L₁,₀(it) > 0 for large t.
-/

/--
The vanishing order of F at infinity is 2.
Blueprint: From q-expansion F = 720² * q² * (1 + O(q)).
-/
theorem F_vanishing_order : ∃ (c : ℂ), c ≠ 0 ∧
    ∀ z : ℍ, F z = c * cexp (2 * π * Complex.I * 2 * z) * (1 + sorry) := by
  sorry

/--
The vanishing order of G at infinity is 3/2.
Blueprint: From q-expansion H₂ = 2q^(1/4)(1 + O(q)), so G = H₂³ = 8q^(3/4)(1 + O(q)).
Note: The "3/2" here refers to the power of q in the full expansion, considering
that q = e^(2πiz), so q^(3/4) = e^(3πiz/2).
-/
theorem G_vanishing_order : ∃ (c : ℂ), c ≠ 0 ∧
    ∀ z : ℍ, G z = c * cexp (π * Complex.I * 3 / 2 * z) * (1 + (0 : ℂ)) := by
  -- Placeholder: actual proof needs q-expansion analysis
  sorry

/--
`lim_{t→∞} L₁,₀(it)/(F(it)G(it)) = 1/2`.
Blueprint: Lemma 8.11 and vanishing orders 2 and 3/2.
-/
theorem L₁₀_div_FG_tendsto :
    Filter.Tendsto (fun t : ℝ => (L₁₀ ⟨Complex.I * t, by sorry⟩).re /
      ((F ⟨Complex.I * t, by sorry⟩).re * (G ⟨Complex.I * t, by sorry⟩).re))
    Filter.atTop (nhds (1/2)) := by
  sorry

/--
`L₁,₀` is eventually positive on the imaginary axis.
Blueprint: Follows from L₁,₀/(FG) → 1/2 > 0 and F, G > 0.
-/
theorem L₁₀_eventually_pos_imag_axis : ResToImagAxis.EventuallyPos L₁₀ := by
  sorry

/-!
## Section 6: Full Positivity of L₁,₀ via Theorem 6.54
-/

/--
`L₁,₀(it)` is real for all `t > 0`.
-/
theorem L₁₀_imag_axis_real : ResToImagAxis.Real L₁₀ := by
  sorry

/--
`L₁,₀(it) > 0` for all `t > 0`.
Blueprint: Apply Theorem 6.54 (antiSerreDerPos) with k = 22.
-/
theorem L₁₀_pos_imag_axis : ResToImagAxis.Pos L₁₀ := by
  -- This would use antiSerreDerPos from Derivative.lean once it's proved
  -- For now, we use the components we've established
  sorry

/-!
## Section 7: Monotonicity of Q = F/G
-/

/--
The function `Q(t) = Re(F(it)/G(it))` for `t > 0`.
Since F(it) and G(it) are both positive reals, Q(t) = F(it)/G(it) as real numbers.
-/
noncomputable def Q (t : ℝ) : ℝ :=
  if ht : 0 < t then
    (F ⟨Complex.I * t, by simp [ht]⟩).re / (G ⟨Complex.I * t, by simp [ht]⟩).re
  else 0

/--
`Q(t) = F(it)/G(it)` equals the real quotient for `t > 0`.
-/
theorem Q_eq_F_div_G (t : ℝ) (ht : 0 < t) :
    Q t = (F ⟨Complex.I * t, by simp [ht]⟩).re / (G ⟨Complex.I * t, by simp [ht]⟩).re := by
  simp [Q, ht]

/--
`Q` is differentiable on `(0, ∞)`.
-/
theorem Q_differentiableOn : DifferentiableOn ℝ Q (Set.Ioi 0) := by
  sorry

/--
The derivative of Q is `(-2π) * L₁,₀(it) / G(it)²`.
Blueprint: Quotient rule and chain rule.
-/
theorem deriv_Q (t : ℝ) (ht : 0 < t) :
    deriv Q t = (-2 * π) * (L₁₀ ⟨Complex.I * t, by simp [ht]⟩).re /
      (G ⟨Complex.I * t, by simp [ht]⟩).re ^ 2 := by
  sorry

/--
`deriv Q t < 0` for all `t > 0`.
Blueprint: L₁,₀(it) > 0 and G(it) > 0 imply deriv Q t < 0.
-/
theorem deriv_Q_neg (t : ℝ) (ht : 0 < t) : deriv Q t < 0 := by
  rw [deriv_Q t ht]
  have hL := L₁₀_pos_imag_axis.2 t ht
  have hG := G_imag_axis_pos.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hL hG
  -- (-2π) * (positive) / (positive)² < 0
  apply div_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos
    · simp [pi_pos]
    · exact hL
  · exact sq_pos_of_pos hG

/--
**Proposition 8.12**: `Q` is strictly decreasing on `(0, ∞)`.
Blueprint: Follows from deriv Q < 0 on (0, ∞).
-/
theorem Q_strictAntiOn : StrictAntiOn Q (Set.Ioi 0) := by
  -- Apply strictAntiOn_of_deriv_neg from Mathlib mean value theorem results
  apply strictAntiOn_of_deriv_neg
  · -- Convexity: (0, ∞) is convex
    exact convex_Ioi 0
  · -- Continuity: Q is continuous on (0, ∞)
    exact Q_differentiableOn.continuousOn
  · -- Negative derivative on interior: deriv Q < 0 on (0, ∞)
    -- interior (Ioi 0) = Ioi 0 since Ioi is open
    intro t ht
    rw [interior_Ioi] at ht
    exact deriv_Q_neg t ht

/--
Corollary: `Q` is strictly anti-monotone (decreasing) as a function on positive reals.
-/
theorem Q_strictAnti : ∀ {t₁ t₂ : ℝ}, 0 < t₁ → t₁ < t₂ → Q t₂ < Q t₁ := by
  intro t₁ t₂ ht₁ ht₁₂
  exact Q_strictAntiOn (Set.mem_Ioi.mpr ht₁) (Set.mem_Ioi.mpr (lt_trans ht₁ ht₁₂)) ht₁₂

end MonotoneFG
