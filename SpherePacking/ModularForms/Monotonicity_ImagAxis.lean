/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.ModularForms.AtImInfty
import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.FG
import SpherePacking.ModularForms.JacobiTheta
import SpherePacking.ModularForms.QExpansion
import SpherePacking.ModularForms.ResToImagAxis
import SpherePacking.ModularForms.Delta
import SpherePacking.ModularForms.logDeriv_lems

/-!
Auxiliary lemmas for `SpherePacking.ModularForms.Monotonicity`.

This file contains Sections 1–3: helper lemmas, holomorphicity facts, and imaginary-axis
realness/positivity results.
-/

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap

open scoped ModularForm MatrixGroups Manifold ArithmeticFunction.sigma

namespace MonotoneFG

/-!
## Section 1: Helper Lemmas for Imaginary Axis Properties
-/

/-- `im` distributes over tsum when each term has zero imaginary part. -/
lemma Complex.im_tsum_eq_zero_of_im_eq_zero (f : ℤ → ℂ)
    (hf : Summable f) (him : ∀ n, (f n).im = 0) :
    (∑' n : ℤ, f n).im = 0 := by
  rw [Complex.im_tsum hf]
  simp [him]

/-- `(-1 : ℂ)^n` has zero imaginary part for any integer n. -/
lemma neg_one_zpow_im_eq_zero (n : ℤ) : ((-1 : ℂ) ^ n).im = 0 := by
  rcases Int.even_or_odd n with hn | hn <;> (rw [hn.neg_one_zpow]; simp)

/-- For even k, `I^k = (-1)^(k/2)`. -/
lemma I_pow_even (k : ℕ) (hk : Even k) : Complex.I ^ k = (-1 : ℂ) ^ (k / 2) := by
  obtain ⟨m, rfl⟩ := hk
  rw [show (m + m) / 2 = m by omega, show m + m = 2 * m by ring, pow_mul, I_sq]

/-- `I^k` is real for even k (since `(-1)^m` is `±1`). -/
lemma I_pow_even_real (k : ℕ) (hk : Even k) : (Complex.I ^ k).im = 0 := by
  rw [I_pow_even k hk]
  induction k / 2 with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- `(-2πi)^k` is real for even k. -/
lemma neg_two_pi_I_pow_even_real (k : ℕ) (hk : Even k) :
    ((-2 * Real.pi * Complex.I) ^ k : ℂ).im = 0 := by
  have h : (-2 * Real.pi * Complex.I) ^ k = ((-2 * Real.pi) ^ k : ℂ) * Complex.I ^ k := by ring
  rw [h]
  have h1 : ((-(2 * Real.pi)) ^ k : ℂ).im = 0 := by
    have hcast : ((-(2 * Real.pi)) ^ k : ℂ) = (((-2 * Real.pi) ^ k : ℝ) : ℂ) := by
      push_cast; ring
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

/-- If `f/g → c ≠ 0`, then `f ≠ 0` eventually. -/
lemma eventually_ne_zero_of_tendsto_div {f g : ℍ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (h : Filter.Tendsto (fun z => f z / g z) atImInfty (nhds c)) :
    ∀ᶠ z : ℍ in atImInfty, f z ≠ 0 := by
  have h_quot_ne := h.eventually_ne hc
  filter_upwards [h_quot_ne] with z hz hf
  exact hz (by simp [hf])

/-- On imaginary axis z = I*t, the q-expansion exponent 2πi·n·z reduces to -(2πnt).
This is useful for reusing the same algebraic simplification across `E₂`, `E₄`, `E₆`. -/
lemma exp_imag_axis_arg (t : ℝ) (ht : 0 < t) (n : ℕ+) :
    2 * Real.pi * Complex.I * (⟨Complex.I * t, by simp [ht]⟩ : ℍ) * n =
    (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
  have hI : Complex.I ^ 2 = -1 := I_sq
  push_cast
  ring_nf
  simp only [hI]
  ring

/-- Product of complex numbers with zero imaginary part has zero imaginary part. -/
lemma Complex.im_mul_eq_zero' (a b : ℂ) (ha : a.im = 0) (hb : b.im = 0) : (a * b).im = 0 := by
  simp [Complex.mul_im, ha, hb]

/-- Quotient of complex numbers with zero imaginary part has zero imaginary part. -/
lemma Complex.im_div_eq_zero' (a b : ℂ) (ha : a.im = 0) (hb : b.im = 0) : (a / b).im = 0 := by
  rw [div_eq_mul_inv]
  apply Complex.im_mul_eq_zero'
  · exact ha
  · simp [Complex.inv_im, hb]
/-!
## Section 2: Properties of F, G, and Q

`F` and `G` are defined in `SpherePacking.ModularForms.FG`:
- `F = (E₂ * E₄ - E₆)²`
- `G = H₂³ (2H₂² + 5H₂H₄ + 5H₄²)` (Definition 8.3 of the blueprint)
-/

/--
`G` is holomorphic on the upper half-plane.
Blueprint: G = H₂³ (2H₂² + 5H₂H₄ + 5H₄²) is holomorphic since H₂ and H₄ are
holomorphic.
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
    have : (fun z => 2 * H₂ z ^ 2) = (fun z => (2 : ℂ) • H₂ z ^ 2) := by
      ext z; simp [smul_eq_mul]
    rw [this]; exact hH₂_sq'.const_smul (2 : ℂ)
  have h2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 5 * H₂ z * H₄ z) := by
    have : (fun z => 5 * H₂ z * H₄ z) = (fun z => (5 : ℂ) • (H₂ z * H₄ z)) := by
      ext z; simp [smul_eq_mul]; ring
    rw [this]; exact hH₂H₄.const_smul (5 : ℂ)
  have h3 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 5 * H₄ z ^ 2) := by
    have : (fun z => 5 * H₄ z ^ 2) = (fun z => (5 : ℂ) • H₄ z ^ 2) := by
      ext z; simp [smul_eq_mul]
    rw [this]; exact hH₄_sq.const_smul (5 : ℂ)
  have hquad : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z => 2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2) := (h1.add h2).add h3
  exact hH₂_cube.mul hquad

/--
`F` is holomorphic on the upper half-plane.
F = (E₂ * E₄ - E₆)² is composed from holomorphic functions.
-/
theorem F_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
  unfold F
  have h_E₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E₂ := E₂_holo'
  have h_E₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E₄.toFun := E₄.holo'
  have h_E₆ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E₆.toFun := E₆.holo'
  have h_prod : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₂ * E₄.toFun) := h_E₂.mul h_E₄
  have h_sub : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₂ * E₄.toFun - E₆.toFun) :=
    h_prod.sub h_E₆
  rw [pow_two]
  exact h_sub.mul h_sub

/-!
## Section 3: Positivity of F and G on the Imaginary Axis
-/

/--
`H₂(it)` is real for all `t > 0`.
Blueprint: Follows from the q-expansion having real coefficients.
Proof strategy: H₂ = Θ₂^4 where Θ₂(it) = ∑ₙ exp(-π(n+1/2)²t) is a sum of real
exponentials.
-/
theorem H₂_imag_axis_real : ResToImagAxis.Real H₂ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, H₂]
  -- H₂ = Θ₂^4, and Θ₂(I*t) has zero imaginary part,
  -- so H₂(I*t) = Θ₂(I*t)^4 has zero imaginary part
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
    --
    -- From SlashActionS at 1/t:
    -- (H₄ ∣[2] S).resToImagAxis (1/t) = I^(-2) * (1/t)^(-2) * H₄.resToImagAxis t
    --
    -- From H₄_S_action: (H₄ ∣[2] S) = -H₂
    -- So: (-H₂).resToImagAxis (1/t) = I^(-2) * (1/t)^(-2) * H₄.resToImagAxis t
    --
    -- Since I^(-2) = -1 and (1/t)^(-2) = t^2:
    -- -H₂.resToImagAxis (1/t) = -t^2 * H₄.resToImagAxis t
    -- Thus: H₂.resToImagAxis (1/t) = t^2 * H₄.resToImagAxis t
    --
    -- Since H₂.resToImagAxis (1/t).re > 0 and t^2 > 0, and H₄.resToImagAxis t is real,
    -- we get H₄.resToImagAxis t.re > 0
    have h1t_pos : 0 < 1 / t := one_div_pos.mpr ht
    -- Apply SlashActionS at 1/t
    have hSlash := ResToImagAxis.SlashActionS H₄ 2 h1t_pos
    -- Use H₄_S_action: (H₄ ∣[2] S) = -H₂
    rw [H₄_S_action] at hSlash
    -- Now hSlash : (-H₂).resToImagAxis (1/t) = I^(-2) * (1/t)^(-2) * H₄.resToImagAxis t
    -- Simplify: I^(-2) = -1
    have hI_neg2 : (Complex.I : ℂ) ^ (-2 : ℤ) = -1 := by
      change (I ^ 2)⁻¹ = -1
      rw [I_sq]
      norm_num
    -- Simplify: (1/t)^(-2) = t^2
    have h1t_neg2 : ((1 / t : ℝ) : ℂ) ^ (-2 : ℤ) = (t : ℂ) ^ 2 := by
      change (((1 / t : ℝ) : ℂ) ^ 2)⁻¹ = (t : ℂ) ^ 2
      simp only [one_div, ofReal_inv, sq, mul_inv_rev, inv_inv]
    -- Simplify 1/(1/t) = t
    have h1_div_1t : 1 / (1 / t) = t := by field_simp
    -- The negation of resToImagAxis
    have hNeg : (-H₂).resToImagAxis (1 / t) = -(H₂.resToImagAxis (1 / t)) := by
      simp only [Function.resToImagAxis_apply, ResToImagAxis, h1t_pos, ↓reduceDIte, Pi.neg_apply]
    -- Substitute into hSlash
    rw [hNeg, hI_neg2, h1t_neg2, h1_div_1t] at hSlash
    -- hSlash : -(H₂.resToImagAxis (1/t)) = -1 * t^2 * H₄.resToImagAxis t
    -- Simplify: H₂.resToImagAxis (1/t) = t^2 * H₄.resToImagAxis t
    have hEq : H₂.resToImagAxis (1 / t) = (t : ℂ) ^ 2 * H₄.resToImagAxis t := by
      have h : -H₂.resToImagAxis (1 / t) = -(↑t ^ 2 * H₄.resToImagAxis t) := by
        simp only [neg_mul, one_mul] at hSlash ⊢
        exact hSlash
      exact neg_inj.mp h
    -- H₂.resToImagAxis (1/t).re > 0 from H₂_imag_axis_pos
    have hH₂_pos := H₂_imag_axis_pos.2 (1 / t) h1t_pos
    -- H₄.resToImagAxis t is real (im = 0)
    have hH₄_real := H₄_imag_axis_real t ht
    -- From hEq, extract real parts
    have hRe : (H₂.resToImagAxis (1 / t)).re = ((t : ℂ) ^ 2 * H₄.resToImagAxis t).re := by
      rw [hEq]
    -- Since t^2 is real positive and H₄.resToImagAxis t is real:
    -- (t^2 * H₄.resToImagAxis t).re = t^2 * (H₄.resToImagAxis t).re
    have hProd_re : ((t : ℂ) ^ 2 * H₄.resToImagAxis t).re =
        (t : ℝ) ^ 2 * (H₄.resToImagAxis t).re := by
      simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte] at hH₄_real ⊢
      simp only [sq, Complex.mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      ring_nf
      simp only [hH₄_real, mul_zero, sub_zero]
    -- Combine: t^2 * (H₄.resToImagAxis t).re > 0 and t^2 > 0 imply (H₄.resToImagAxis t).re > 0
    rw [hRe, hProd_re] at hH₂_pos
    have ht2_pos : 0 < (t : ℝ) ^ 2 := sq_pos_of_pos ht
    rw [mul_comm] at hH₂_pos
    exact pos_of_mul_pos_left hH₂_pos (le_of_lt ht2_pos)

/--
`G(it) > 0` for all `t > 0`.
Blueprint: Lemma 8.6 - follows from H₂(it) > 0 and H₄(it) > 0.
G = H₂³ (2H₂² + 5H₂H₄ + 5H₄²) is positive since all factors are positive.

TODO: Use the G_pos lemma from FG.lean once it's complete.
-/
theorem G_imag_axis_pos : ResToImagAxis.Pos G := by
  unfold G
  have hH₂ : ResToImagAxis.Pos H₂ := H₂_imag_axis_pos
  have hH₄ : ResToImagAxis.Pos H₄ := H₄_imag_axis_pos
  have hH₂_sq : ResToImagAxis.Pos (fun z : ℍ => H₂ z ^ 2) := by
    have hmul : ResToImagAxis.Pos (fun z : ℍ => H₂ z * H₂ z) := ResToImagAxis.Pos.mul hH₂ hH₂
    simpa [pow_two] using hmul
  have hH₂_cube : ResToImagAxis.Pos (fun z : ℍ => H₂ z ^ 3) := by
    have hmul : ResToImagAxis.Pos (fun z : ℍ => (H₂ z ^ 2) * H₂ z) :=
      ResToImagAxis.Pos.mul hH₂_sq hH₂
    simpa [pow_succ, pow_two, mul_assoc] using hmul
  have hH₄_sq : ResToImagAxis.Pos (fun z : ℍ => H₄ z ^ 2) := by
    have hmul : ResToImagAxis.Pos (fun z : ℍ => H₄ z * H₄ z) := ResToImagAxis.Pos.mul hH₄ hH₄
    simpa [pow_two] using hmul
  have hterm1 : ResToImagAxis.Pos (fun z : ℍ => 2 * H₂ z ^ 2) := by
    simpa using (ResToImagAxis.Pos.smul (F := fun z : ℍ => H₂ z ^ 2) hH₂_sq (by norm_num))
  have hterm2 : ResToImagAxis.Pos (fun z : ℍ => 5 * H₂ z * H₄ z) := by
    have h5H₂ : ResToImagAxis.Pos (fun z : ℍ => (5 : ℝ) * H₂ z) :=
      ResToImagAxis.Pos.smul (F := H₂) hH₂ (by norm_num)
    have hmul : ResToImagAxis.Pos (fun z : ℍ => ((5 : ℝ) * H₂ z) * H₄ z) :=
      ResToImagAxis.Pos.mul h5H₂ hH₄
    simpa [mul_assoc] using hmul
  have hterm3 : ResToImagAxis.Pos (fun z : ℍ => 5 * H₄ z ^ 2) := by
    simpa using (ResToImagAxis.Pos.smul (F := fun z : ℍ => H₄ z ^ 2) hH₄_sq (by norm_num))
  have hquad :
      ResToImagAxis.Pos
        (fun z : ℍ => 2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2) :=
    ResToImagAxis.Pos.add (ResToImagAxis.Pos.add hterm1 hterm2) hterm3
  have hmul :
      ResToImagAxis.Pos
        (fun z : ℍ =>
          H₂ z ^ 3 * (2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2)) :=
    ResToImagAxis.Pos.mul hH₂_cube hquad
  simpa using hmul

/--
`G(it)` is real for all `t > 0`.
Blueprint: G = H₂³ (2H₂² + 5H₂H₄ + 5H₄²), product of real functions.

TODO: After PR #193 merges, this should follow from the corresponding lemma in FG.lean.
-/
theorem G_imag_axis_real : ResToImagAxis.Real G :=
  G_imag_axis_pos.1

/-!
### Helper lemmas for Eisenstein series on imaginary axis
-/

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
    have hexp_arg : 2 * ↑Real.pi * Complex.I * z * n = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
      simpa [z] using exp_imag_axis_arg (t := t) ht n
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
  -- (-2πi)^4 / 3! is real (using global helper)
  have hcoeff2_im := Complex.im_div_eq_zero' _ _ hpow_im hfact_im
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
    have hexp_arg : 2 * ↑Real.pi * Complex.I * z * n = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
      simpa [z] using exp_imag_axis_arg (t := t) ht n
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
    -- exp(2πinz) = exp(2πin·it) = exp(-2πnt) is real
    have hexp_arg : 2 * ↑Real.pi * Complex.I * n * z = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
      have h1 : 2 * ↑Real.pi * Complex.I * z * n = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
        simpa [z] using exp_imag_axis_arg (t := t) ht n
      simpa [mul_assoc, mul_left_comm, mul_comm] using h1
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
  have hsum : Summable fun n : ℕ+ => ↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z)) := by
    -- Rewrite in the `n * r^n / (1 - r^n)` form and use `logDeriv_q_expo_summable`.
    set r : ℂ := cexp (2 * ↑Real.pi * Complex.I * z) with hr
    have hr_norm : ‖r‖ < 1 := by
      simpa [hr] using exp_upperHalfPlane_lt_one z
    have hs : Summable fun n : ℕ => (n : ℂ) * r ^ n / (1 - r ^ n) :=
      logDeriv_q_expo_summable r hr_norm
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
    simp only [hterm_im, tsum_zero]
  -- Step 4: 24 * sum is real, so -(24 * sum).im = 0
  have h24_im : (24 : ℂ).im = 0 := by norm_num
  simp only [Complex.mul_im, hsum_im, h24_im, mul_zero, add_zero, neg_zero, zero_mul]

/--
`F(it)` is real for all `t > 0`.
Blueprint: Follows from E₂, E₄, E₆ having real values on the imaginary axis.
-/
theorem F_imag_axis_real : ResToImagAxis.Real F := by
  unfold F
  have hProd : ResToImagAxis.Real (E₂ * E₄.toFun) :=
    ResToImagAxis.Real.mul E₂_imag_axis_real E₄_imag_axis_real
  have hNeg : ResToImagAxis.Real ((-1 : ℝ) • E₆.toFun) :=
    ResToImagAxis.Real.smul E₆_imag_axis_real
  have hSub : ResToImagAxis.Real (E₂ * E₄.toFun - E₆.toFun) := by
    have hEq : E₂ * E₄.toFun - E₆.toFun = E₂ * E₄.toFun + (-1 : ℝ) • E₆.toFun := by
      ext z
      simp [sub_eq_add_neg]
    simpa [hEq] using ResToImagAxis.Real.add hProd hNeg
  simpa [pow_two] using ResToImagAxis.Real.mul hSub hSub

/--
`F(it) > 0` for all `t > 0`.
Blueprint: Follows from the q-expansion (E₂E₄ - E₆ = 720 * ...) and positivity.
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
    simp only [sub_im, mul_im, hE₂_real', hE₄_real', hE₆_real', mul_zero, zero_mul, add_zero,
      sub_zero]
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
  have hz_eq : (z : ℂ) = I * t := rfl
  -- The real part of 720 * (positive sum) is positive
  -- 720 is real, so (720 * x).re = 720 * x.re
  have h720_real : (720 : ℂ).im = 0 := by norm_num
  rw [mul_re, h720_real, zero_mul, sub_zero]
  apply mul_pos (by norm_num : (0 : ℝ) < 720)
  -- Show the sum has positive real part
  -- On z = it, each term n * σ₃(n) * exp(2πinz) = n * σ₃(n) * exp(-2πnt) is positive real
  -- For n : ℕ+: n > 0, σ₃(n) ≥ 1, exp(-2πnt) > 0
  -- So each term > 0, and their sum > 0
  -- Step 1: Summability of the series
  have hsum : Summable fun n : ℕ+ => (↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 3) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le
    · intro n; exact norm_nonneg _
    · intro n
      calc ‖(↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 3) ↑n) *
              cexp (2 * ↑Real.pi * Complex.I * z * n)‖
          = ‖(↑↑n : ℂ)‖ * ‖(↑((ArithmeticFunction.sigma 3) ↑n) : ℂ)‖ *
              ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ (↑n : ℝ) * (↑n : ℝ)^4 * ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := by
            gcongr
            · rw [Complex.norm_natCast]
            · rw [Complex.norm_natCast]
              have hbound := sigma_bound 3 n
              exact_mod_cast hbound
        _ = ‖(↑n : ℂ) ^ 5 * cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := by
            rw [norm_mul, Complex.norm_pow, Complex.norm_natCast]
            ring
    · have := a33 5 1 z
      simp only [PNat.val_ofNat, Nat.cast_one, mul_one] at this
      exact summable_norm_iff.mpr this
  -- Adjust the exponent form to match the goal
  have hsum' : Summable fun n : ℕ+ => (↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 3) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * ↑n * z) := by
    simp_rw [show ∀ n : ℕ+, (2 : ℂ) * ↑Real.pi * Complex.I * ↑n * z =
        2 * ↑Real.pi * Complex.I * z * n by intro n; ring]
    exact hsum
  -- Key simplification: on z = I*t, the exponential becomes real
  have hexp_simpl : ∀ n : ℕ+, cexp (2 * ↑Real.pi * Complex.I * ↑n * z) =
      Real.exp (-(2 * π * n * t)) := by
    intro n
    rw [hz_eq]
    have harg : (2 : ℂ) * ↑Real.pi * Complex.I * ↑n * (Complex.I * ↑t) =
        ↑(-(2 * π * (n : ℕ) * t)) := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [harg, Complex.ofReal_exp]
  -- Step 2: Each term is real on imaginary axis: n * σ(3,n) * exp(-2πnt)
  have hterm_real : ∀ n : ℕ+, ((↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 3) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * ↑n * z)).im = 0 := by
    intro n
    rw [hexp_simpl]
    simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero]
  -- Step 3: Each term is positive
  have hterm_pos : ∀ n : ℕ+, 0 < ((↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 3) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * ↑n * z)).re := by
    intro n
    rw [hexp_simpl]
    simp only [mul_re, natCast_re, natCast_im, sub_zero,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero]
    -- Term is n * σ(3,n) * exp(-2πnt), all factors positive
    apply mul_pos
    · apply mul_pos
      · exact_mod_cast n.pos
      · exact_mod_cast ArithmeticFunction.sigma_pos 3 n n.ne_zero
    · exact Real.exp_pos _
  -- Step 4: Sum of positive terms is positive
  have hsum_re : Summable fun n : ℕ+ => ((↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 3) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * ↑n * z)).re := by
    obtain ⟨x, hx⟩ := hsum'
    exact ⟨x.re, Complex.hasSum_re hx⟩
  rw [Complex.re_tsum hsum']
  exact Summable.tsum_pos hsum_re (fun n => le_of_lt (hterm_pos n)) 1 (hterm_pos 1)

end MonotoneFG
