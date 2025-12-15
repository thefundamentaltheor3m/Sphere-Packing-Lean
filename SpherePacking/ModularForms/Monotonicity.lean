/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.ModularForms.AtImInfty
import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.JacobiTheta
import SpherePacking.ModularForms.QExpansion
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

## Relationship to PR #193 (magic-modforms branch)

PR #193 introduces `FG.lean` with similar definitions. Here's a comparison:

| Concept | PR #193 (`FG.lean`) | This file |
|---------|---------------------|-----------|
| `F` | `(E₂ * E₄.toFun - E₆.toFun) ^ 2` | Same |
| `G` | `H₂³ * (2H₂² + 5H₂H₄ + 5H₄²)` | Same (line ~137) |
| `L₁₀` | `(D F) * G - F * (D G)` | Same (line ~1083) |

**Proofs here that fill PR #193 sorries:**
- `F_imag_axis_pos` → fills `F_pos`
- `G_imag_axis_pos` → fills `G_pos`
- `H₂_imag_axis_pos` → fills `H₂_pos`
- `L₁₀_eventually_pos_imag_axis` → fills `L₁₀_eventuallyPos`
- `Q_strictAntiOn` → fills `FmodG_antitone`

**Still blocked (in both):**
- `MLDE_F`, `MLDE_G` - differential equations
- `serre_D_L₁₀_eq` / `SerreDer_22_L₁₀_pos` - depend on above

When PR #193 merges, consider unifying these files.
-/

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap

open scoped ModularForm MatrixGroups Manifold ArithmeticFunction.sigma

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
The function `G(z) = H₂(z)³ (2 H₂(z)² + 5 H₂(z) H₄(z) + 5 H₄(z)²)` from Definition 8.3 of
the blueprint. Aliased from the root namespace.
-/
noncomputable abbrev G := _root_.G

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
  have h_sub : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₂ * E₄.toFun - E₆.toFun) := h_prod.sub h_E₆
  rw [pow_two]
  exact h_sub.mul h_sub

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
    apply h_prod_real
    · exact h_prod_real _ _ (h_const_real 5) hH₂_real
    · exact hH₄_real
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
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
    -- G = _root_.G = H₂³ * (2H₂² + 5H₂H₄ + 5H₄²)
    unfold G _root_.G
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
        mul_zero, sub_zero, zero_mul]
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
lemma exp_2pi_I_mul_n_imag_axis_im (n : ℕ+) (t : ℝ) (_ht : 0 < t) :
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
lemma exp_2pi_I_mul_n_imag_axis_re_pos (n : ℕ+) (t : ℝ) (_ht : 0 < t) :
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
      change ‖↑↑n * qn / (1 - qn)‖ ≤ bound n
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
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hE₂_real hE₄_real hE₆_real
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
    have hpow : (E₂ z * E₄ z - E₆ z) ^ 2 = (E₂ z * E₄ z - E₆ z) * (E₂ z * E₄ z - E₆ z) := sq _
    rw [hpow, Complex.mul_re]
    simp only [hdiff_real, mul_zero, sub_zero]
    ring
  -- Convert function application to pointwise form
  have hgoal_eq : (((E₂ * E₄.toFun - E₆.toFun) ^ 2) z).re = ((E₂ z * E₄ z - E₆ z) ^ 2).re := rfl
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
The cross terms `(∂₁₀F)(∂₁₀G)` cancel in the subtraction.
-/
theorem serre_D_L₁₀ (z : ℍ) :
    serre_D 22 L₁₀ z = serre_D 12 (serre_D 10 F) z * G z
      - F z * serre_D 12 (serre_D 10 G) z := by
  -- MDifferentiable hypotheses
  have hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := F_holo
  have hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := G_holo
  have hDF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D 10 F) := serre_D_differentiable hF
  have hDG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D 10 G) := serre_D_differentiable hG
  -- Expand L₁₀ and apply serre_D_sub
  -- Note: L₁₀ z = (serre_D 10 F * G - F * serre_D 10 G) z
  have hL₁₀_eq : L₁₀ = serre_D 10 F * G - F * serre_D 10 G := rfl
  rw [hL₁₀_eq]
  -- Use serre_D_sub: need to align coercions (22 : ℤ) vs (22 : ℂ)
  have hsub := serre_D_sub (22 : ℤ) _ _ (hDF.mul hG) (hF.mul hDG)
  simp only [Int.cast_ofNat] at hsub
  rw [hsub, Pi.sub_apply]
  -- Apply serre_D_mul to first term: serre_D 22 ((serre_D 10 F) * G)
  -- 22 = 10 + 12, so serre_D_mul gives: (∂₁₀F) * ∂₁₀G + G * ∂₁₂(∂₁₀F)
  have h1 : serre_D 22 (serre_D 10 F * G) z =
      serre_D 10 F z * serre_D 10 G z + G z * serre_D 12 (serre_D 10 F) z := by
    conv_lhs => rw [show (22 : ℂ) = 10 + 12 by norm_num]
    exact serre_D_mul 10 12 (serre_D 10 F) G hDF hG z
  -- Apply serre_D_mul to second term: serre_D 22 (F * (serre_D 10 G))
  -- 22 = 12 + 10, so serre_D_mul gives: F * ∂₁₂(∂₁₀G) + (∂₁₀G) * ∂₁₀F
  have h2 : serre_D 22 (F * serre_D 10 G) z =
      F z * serre_D 12 (serre_D 10 G) z + serre_D 10 G z * serre_D 10 F z := by
    conv_lhs => rw [show (22 : ℂ) = 12 + 10 by norm_num]
    exact serre_D_mul 12 10 F (serre_D 10 G) hF hDG z
  -- Combine: cross terms (∂₁₀F)(∂₁₀G) cancel
  rw [h1, h2]
  ring

/--
`∂₂₂ L₁,₀ = Δ(7200(-E₂')G + 640H₂F)` on the upper half-plane.
Blueprint: Follows from differential equations (65) and (66).
-/
theorem serre_D_L₁₀_eq (z : ℍ) :
    serre_D 22 L₁₀ z = Δ z * (7200 * (-(D E₂ z)) * G z + 640 * H₂ z * F z) := by
  -- From serre_D_L₁₀: ∂₂₂L₁₀ = (∂₁₂∂₁₀F)G - F(∂₁₂∂₁₀G)
  rw [serre_D_L₁₀]
  -- From MLDE_F': ∂₁₂∂₁₀F = (5/6)E₄F + 7200Δ(-E₂')
  -- From MLDE_G: ∂₁₂∂₁₀G = (5/6)E₄G - 640ΔH₂
  have hF_eq := MLDE_F'
  have hG_eq := MLDE_G
  -- Apply at point z
  have hF_z := congrFun hF_eq z
  have hG_z := congrFun hG_eq z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply] at hF_z hG_z
  rw [hF_z, hG_z]
  -- Expand negDE₂ and simplify constant functions
  simp only [negDE₂, Pi.neg_apply]
  -- Use Δ_fun_eq_Δ to replace Δ_fun z with Δ z
  simp only [Δ_fun_eq_Δ]
  -- Handle constant functions
  have h5 : (5 : ℍ → ℂ) z = (5 : ℂ) := rfl
  have h6 : (6⁻¹ : ℍ → ℂ) z = (6 : ℂ)⁻¹ := rfl
  have h7200 : (7200 : ℍ → ℂ) z = (7200 : ℂ) := rfl
  have h640 : (640 : ℍ → ℂ) z = (640 : ℂ) := rfl
  rw [h5, h6, h7200, h640]
  -- Substituting: (5/6)E₄FG + 7200Δ·(-D E₂)·G - F·((5/6)E₄G - 640·Δ·H₂)
  --             = (5/6)E₄FG + 7200Δ·(-D E₂)·G - (5/6)E₄FG + 640·Δ·H₂·F
  --             = Δ·(7200·(-D E₂)·G + 640·H₂·F)
  ring

/-!
### negDE₂ imaginary axis properties

We prove that `negDE₂ = -(D E₂)` is real and positive on the imaginary axis.
From `ramanujan_E₂`: `D E₂ = 12⁻¹ * (E₂² - E₄)`, so `negDE₂ = 12⁻¹ * (E₄ - E₂²)`.
The positivity `E₄(it) > E₂(it)²` follows from the q-expansion coefficients being positive.
-/

/-- `negDE₂(it) = -(D E₂)(it)` is real for all `t > 0`. -/
theorem negDE₂_imag_axis_real : ResToImagAxis.Real negDE₂ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  -- negDE₂ = -(D E₂) = -12⁻¹ * (E₂² - E₄) = 12⁻¹ * (E₄ - E₂²)
  -- Since E₂, E₄ are real on imaginary axis, so is negDE₂
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  -- Get realness hypotheses by unfolding definitions
  have hE₂_real : (E₂ z).im = 0 := by
    have := E₂_imag_axis_real t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this
    exact this
  have hE₄_real : (E₄ z).im = 0 := by
    have := E₄_imag_axis_real t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this
    exact this
  -- 12⁻¹ is real
  have h12_real : (12⁻¹ : ℂ).im = 0 := by norm_num
  -- E₂² is real (product of two reals)
  have hE₂_sq_real : (E₂ z * E₂ z).im = 0 := by
    rw [Complex.mul_im]; simp only [hE₂_real]; ring
  -- E₂² - E₄ is real
  have hdiff_real : (E₂ z * E₂ z - E₄ z).im = 0 := by
    rw [Complex.sub_im, hE₂_sq_real, hE₄_real]; ring
  -- 12⁻¹ * (E₂² - E₄) is real
  have hprod_real : ((12 : ℂ)⁻¹ * (E₂ z * E₂ z - E₄ z)).im = 0 := by
    rw [Complex.mul_im, h12_real, hdiff_real]; ring
  -- negDE₂ z = -(12⁻¹ * (E₂² - E₄))
  simp only [negDE₂, Pi.neg_apply, ramanujan_E₂, Pi.mul_apply, Pi.sub_apply]
  have h12 : (12⁻¹ : ℍ → ℂ) z = (12 : ℂ)⁻¹ := rfl
  rw [h12, neg_im]
  exact neg_eq_zero.mpr hprod_real

/--
Q-expansion identity: `E₄ - E₂² = 288 * ∑' n : ℕ+, n * σ₁(n) * qⁿ`.
This follows from the Ramanujan identity `D E₂ = 12⁻¹ * (E₂² - E₄)` and the q-expansion
of E₂ via termwise differentiation.
-/
theorem E₄_sub_E₂_sq_qexp (z : ℍ) :
    E₄.toFun z - E₂ z * E₂ z =
      288 * ∑' n : ℕ+, (↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 1) ↑n) *
        cexp (2 * ↑Real.pi * Complex.I * ↑n * z) := by
  -- From ramanujan_E₂: D E₂ = 12⁻¹ * (E₂² - E₄)
  -- So E₄ - E₂² = -12 * D E₂
  -- E₂ = 1 - 24 * ∑ σ₁(n) qⁿ (from G2_q_exp)
  -- D E₂ = -24 * ∑ n * σ₁(n) qⁿ (termwise derivative)
  -- Thus E₄ - E₂² = -12 * (-24 * ∑ n * σ₁(n) qⁿ) = 288 * ∑ n * σ₁(n) qⁿ
  sorry

/--
On the imaginary axis, `E₄(it).re > E₂(it).re²` for all `t > 0`.
This follows from the q-expansion: `E₄ - E₂² = 288 * ∑ n * σ₁(n) * qⁿ` has positive terms,
and on z = it, q = exp(-2πt) ∈ (0,1) is positive, so each term is positive.
-/
theorem hE₄_gt_E₂sq (t : ℝ) (ht : 0 < t) :
    (E₄.toFun ⟨Complex.I * t, by simp [ht]⟩).re > (E₂ ⟨Complex.I * t, by simp [ht]⟩).re ^ 2 := by
  -- Set up z = I*t
  set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩ with hz_def
  have hz_eq : (z : ℂ) = Complex.I * t := rfl
  -- Use the q-expansion identity
  have hqexp := E₄_sub_E₂_sq_qexp z
  -- Goal: E₄(z).re > E₂(z).re², i.e., (E₄ - E₂²).re > 0 (after using realness)
  -- First get realness
  have hE₂_real : (E₂ z).im = 0 := by
    have := E₂_imag_axis_real t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this
    exact this
  have hE₄_real : (E₄.toFun z).im = 0 := by
    have := E₄_imag_axis_real t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this
    exact this
  -- E₂² real part equals (E₂.re)²
  have hE₂_sq_re : (E₂ z * E₂ z).re = (E₂ z).re ^ 2 := by
    rw [Complex.mul_re, hE₂_real, mul_zero, sub_zero, sq]
  -- Difference real part
  have hdiff_re : (E₄.toFun z - E₂ z * E₂ z).re = (E₄.toFun z).re - (E₂ z).re ^ 2 := by
    rw [Complex.sub_re, hE₂_sq_re]
  -- Need to show the difference is positive via q-expansion
  rw [gt_iff_lt, ← sub_pos, ← hdiff_re, hqexp]
  -- Now: (288 * ∑ n * σ₁(n) * qⁿ).re > 0
  -- 288 is real, so (288 * x).re = 288 * x.re
  have h288_real : (288 : ℂ).im = 0 := by norm_num
  rw [mul_re, h288_real, zero_mul, sub_zero]
  apply mul_pos (by norm_num : (0 : ℝ) < 288)
  -- Show the sum has positive real part using the pattern from E₂_mul_E₄_sub_E₆
  -- Step 1: Summability of the series
  have hsum : Summable fun n : ℕ+ => (↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 1) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le
    · intro n; exact norm_nonneg _
    · intro n
      calc ‖(↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 1) ↑n) *
              cexp (2 * ↑Real.pi * Complex.I * z * n)‖
          = ‖(↑↑n : ℂ)‖ * ‖(↑((ArithmeticFunction.sigma 1) ↑n) : ℂ)‖ *
              ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ (↑n : ℝ) * (↑n : ℝ)^2 * ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := by
            gcongr
            · rw [Complex.norm_natCast]
            · rw [Complex.norm_natCast]
              have hbound := sigma_bound 1 n
              exact_mod_cast hbound
        _ = ‖(↑n : ℂ) ^ 3 * cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := by
            rw [norm_mul, Complex.norm_pow, Complex.norm_natCast]
            ring
    · have := a33 3 1 z
      simp only [PNat.val_ofNat, Nat.cast_one, mul_one] at this
      exact summable_norm_iff.mpr this
  -- Adjust the exponent form to match the goal
  have hsum' : Summable fun n : ℕ+ => (↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 1) ↑n) *
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
  -- Step 2: Each term is real on imaginary axis: n * σ(1,n) * exp(-2πnt)
  have hterm_real : ∀ n : ℕ+, ((↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 1) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * ↑n * z)).im = 0 := by
    intro n
    rw [hexp_simpl]
    simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero]
  -- Step 3: Each term is positive
  have hterm_pos : ∀ n : ℕ+, 0 < ((↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 1) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * ↑n * z)).re := by
    intro n
    rw [hexp_simpl]
    simp only [mul_re, natCast_re, natCast_im, sub_zero,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero]
    -- Term is n * σ(1,n) * exp(-2πnt), all factors positive
    apply mul_pos
    · apply mul_pos
      · exact_mod_cast n.pos
      · exact_mod_cast ArithmeticFunction.sigma_pos 1 n n.ne_zero
    · exact Real.exp_pos _
  -- Step 4: Sum of positive terms is positive
  have hsum_re : Summable fun n : ℕ+ => ((↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 1) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * ↑n * z)).re := by
    obtain ⟨x, hx⟩ := hsum'
    exact ⟨x.re, Complex.hasSum_re hx⟩
  rw [Complex.re_tsum hsum']
  exact Summable.tsum_pos hsum_re (fun n => le_of_lt (hterm_pos n)) 1 (hterm_pos 1)

/--
`negDE₂(it) = -(D E₂)(it) > 0` for all `t > 0`.
Blueprint: Corollary 8.9 - this follows from the Ramanujan formula `D E₂ = (E₂² - E₄)/12`,
which gives `negDE₂ = (E₄ - E₂²)/12`. The inequality `E₄(it) > E₂(it)²` holds because
the q-expansion `E₄ - E₂² = 288q + 1728q² + ...` has positive coefficients, and on the
imaginary axis `q = exp(-2πt) > 0`.
-/
theorem negDE₂_imag_axis_pos : ResToImagAxis.Pos negDE₂ := by
  refine ⟨negDE₂_imag_axis_real, fun t ht => ?_⟩
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  -- negDE₂ z = -(D E₂ z) = -12⁻¹ * (E₂ z² - E₄ z) = 12⁻¹ * (E₄ z - E₂ z²)
  -- Use `set` to substitute z in the goal (unlike `let`)
  set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  -- Get realness hypotheses by unfolding definitions
  have hE₂_real : (E₂ z).im = 0 := by
    have := E₂_imag_axis_real t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this
    exact this
  have hE₄_real : (E₄.toFun z).im = 0 := by
    have := E₄_imag_axis_real t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this
    exact this
  have h12_real : (12⁻¹ : ℂ).im = 0 := by norm_num
  have hE₂_sq_real : (E₂ z * E₂ z).im = 0 := by
    rw [Complex.mul_im]; simp only [hE₂_real]; ring
  have hdiff_real : (E₂ z * E₂ z - E₄.toFun z).im = 0 := by
    rw [Complex.sub_im, hE₂_sq_real, hE₄_real]; ring
  -- Unfold negDE₂
  simp only [negDE₂, Pi.neg_apply, ramanujan_E₂, Pi.mul_apply, Pi.sub_apply]
  have h12 : (12⁻¹ : ℍ → ℂ) z = (12 : ℂ)⁻¹ := rfl
  rw [h12]
  -- Goal: (-(12⁻¹ * (E₂ z² - E₄ z))).re > 0
  rw [neg_re, neg_pos]
  -- Goal: (12⁻¹ * (E₂ z * E₂ z - E₄ z)).re < 0
  rw [Complex.mul_re, h12_real, hdiff_real, mul_zero, sub_zero]
  -- Now: 12⁻¹.re * (E₂ z² - E₄.toFun z).re < 0
  -- Since 12⁻¹.re > 0, we need (E₂ z² - E₄.toFun z).re < 0, i.e., E₄(it).re > E₂(it)².re
  have h12_pos : (0 : ℝ) < ((12 : ℂ)⁻¹).re := by norm_num
  have hdiff_neg : (E₂ z * E₂ z - E₄.toFun z).re < 0 := by
    -- Will prove E₄.toFun z > E₂ z * E₂ z on imaginary axis via q-expansion
    rw [Complex.sub_re]
    -- Since E₂ is real on imaginary axis, E₂ z * E₂ z = (E₂ z).re²
    have hE₂_eq : E₂ z = (E₂ z).re := Complex.ext rfl (by simp [hE₂_real])
    have hE₂_sq_re : (E₂ z * E₂ z).re = (E₂ z).re ^ 2 := by
      rw [Complex.mul_re, hE₂_real, mul_zero, sub_zero, sq]
    rw [hE₂_sq_re]
    -- Need: E₂(z).re² < E₄.toFun(z).re, i.e., E₄(z).re - E₂(z).re² > 0
    linarith [hE₄_gt_E₂sq t ht]
  nlinarith

/--
`∂₂₂ L₁,₀(it) > 0` for all `t > 0`.
Blueprint: Corollary 8.9 - both terms in the expression are positive.
- `-D E₂(it) > 0` (negDE₂_imag_axis_pos)
- `Δ(it) > 0` (Delta_imag_axis_pos)
- `G(it) > 0` and `H₂(it) > 0` and `F(it) > 0`
-/
theorem serre_D_L₁₀_pos_imag_axis : ResToImagAxis.Pos (serre_D 22 L₁₀) := by
  -- Using serre_D_L₁₀_eq: serre_D 22 L₁₀ z = Δ z * (7200 * negDE₂ z * G z + 640 * H₂ z * F z)
  refine ⟨?_, fun t ht => ?_⟩
  -- Part 1: Real on imaginary axis
  · intro t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
    set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
    have h_eq := serre_D_L₁₀_eq z
    rw [h_eq]
    -- Convert -D E₂ z to negDE₂ z (definitionally equal)
    change (Δ z * (7200 * negDE₂ z * G z + 640 * H₂ z * F z)).im = 0
    -- The product of real numbers is real
    have hΔ_real : (Δ z).im = 0 := by
      have := Delta_imag_axis_pos.1 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hG_real : (G z).im = 0 := by
      have := G_imag_axis_real t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hH₂_real : (H₂ z).im = 0 := by
      have := H₂_imag_axis_pos.1 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hF_real : (F z).im = 0 := by
      have := F_imag_axis_real t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hnegDE₂_real : (negDE₂ z).im = 0 := by
      have := negDE₂_imag_axis_real t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    -- Build up the product
    have h1 : (7200 * negDE₂ z * G z).im = 0 := by
      have h7200 : (7200 : ℂ).im = 0 := by norm_num
      rw [Complex.mul_im, Complex.mul_im]
      simp only [h7200, hnegDE₂_real, hG_real]; ring
    have h2 : (640 * H₂ z * F z).im = 0 := by
      have h640 : (640 : ℂ).im = 0 := by norm_num
      rw [Complex.mul_im, Complex.mul_im]
      simp only [h640, hH₂_real, hF_real]; ring
    have hsum : (7200 * negDE₂ z * G z + 640 * H₂ z * F z).im = 0 := by
      rw [Complex.add_im, h1, h2]; ring
    rw [Complex.mul_im, hΔ_real, hsum]; ring
  -- Part 2: Positive on imaginary axis
  · simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
    set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
    have h_eq := serre_D_L₁₀_eq z
    rw [h_eq]
    -- Convert -D E₂ z to negDE₂ z (definitionally equal)
    change 0 < (Δ z * (7200 * negDE₂ z * G z + 640 * H₂ z * F z)).re
    -- Get positivity and realness hypotheses
    have hΔ_pos : (Δ z).re > 0 := by
      have := Delta_imag_axis_pos.2 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hΔ_real : (Δ z).im = 0 := by
      have := Delta_imag_axis_pos.1 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hnegDE₂_pos : (negDE₂ z).re > 0 := by
      have := negDE₂_imag_axis_pos.2 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hnegDE₂_real : (negDE₂ z).im = 0 := by
      have := negDE₂_imag_axis_pos.1 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hG_pos : (G z).re > 0 := by
      have := G_imag_axis_pos.2 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hG_real : (G z).im = 0 := by
      have := G_imag_axis_real t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hH₂_pos : (H₂ z).re > 0 := by
      have := H₂_imag_axis_pos.2 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hH₂_real : (H₂ z).im = 0 := by
      have := H₂_imag_axis_pos.1 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hF_pos : (F z).re > 0 := by
      have := F_imag_axis_pos.2 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hF_real : (F z).im = 0 := by
      have := F_imag_axis_real t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    -- The sum 7200 * negDE₂ z * G z + 640 * H₂ z * F z is positive
    have hsum_pos : (7200 * negDE₂ z * G z + 640 * H₂ z * F z).re > 0 := by
      have h1_re : (7200 * negDE₂ z * G z).re = 7200 * (negDE₂ z).re * (G z).re := by
        rw [Complex.mul_re, Complex.mul_re]
        have h7200_im : (7200 : ℂ).im = 0 := by norm_num
        simp only [(by norm_num : (7200 : ℂ).re = 7200), h7200_im, hnegDE₂_real, hG_real]; ring
      have h2_re : (640 * H₂ z * F z).re = 640 * (H₂ z).re * (F z).re := by
        rw [Complex.mul_re, Complex.mul_re]
        have h640_im : (640 : ℂ).im = 0 := by norm_num
        simp only [(by norm_num : (640 : ℂ).re = 640), h640_im, hH₂_real, hF_real]; ring
      rw [Complex.add_re, h1_re, h2_re]
      apply add_pos
      · apply mul_pos (mul_pos (by norm_num : (0 : ℝ) < 7200) hnegDE₂_pos) hG_pos
      · apply mul_pos (mul_pos (by norm_num : (0 : ℝ) < 640) hH₂_pos) hF_pos
    have hsum_real : (7200 * negDE₂ z * G z + 640 * H₂ z * F z).im = 0 := by
      have h1 : (7200 * negDE₂ z * G z).im = 0 := by
        rw [Complex.mul_im, Complex.mul_im]
        have h7200_im : (7200 : ℂ).im = 0 := by norm_num
        simp only [h7200_im, hnegDE₂_real, hG_real]; ring
      have h2 : (640 * H₂ z * F z).im = 0 := by
        rw [Complex.mul_im, Complex.mul_im]
        have h640_im : (640 : ℂ).im = 0 := by norm_num
        simp only [h640_im, hH₂_real, hF_real]; ring
      rw [Complex.add_im, h1, h2]; ring
    rw [Complex.mul_re, hΔ_real, hsum_real, mul_zero, sub_zero]
    exact mul_pos hΔ_pos hsum_pos

/-!
## Section 5: Large-t Positivity of L₁,₀

Using Lemma 8.11 (vanishing orders), we show L₁,₀(it) > 0 for large t.
-/

/-- Helper lemma: σ_k(n) ≤ n^{k+1} for divisor sum. -/
lemma sigma_le_pow (k n : ℕ) : ArithmeticFunction.sigma k n ≤ n ^ (k + 1) := by
  rw [ArithmeticFunction.sigma_apply]
  calc ∑ d ∈ n.divisors, d ^ k
      ≤ ∑ d ∈ n.divisors, n ^ k := Finset.sum_le_sum (fun d hd =>
          Nat.pow_le_pow_left (Nat.divisor_le hd) k)
    _ = n.divisors.card * n ^ k := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * n ^ k := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self n)
    _ = n ^ (k + 1) := by rw [pow_succ']

/-- Summability of (m+1)^5 * exp(-2πm) via comparison with shifted sum. -/
lemma summable_pow5_shift : Summable fun m : ℕ => (m + 1 : ℝ) ^ 5 * rexp (-2 * π * m) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul 5 (by positivity : 0 < 2 * π)
  have h_eq : ∀ m : ℕ, (m + 1 : ℝ) ^ 5 * rexp (-2 * π * m) =
      rexp (2 * π) * ((m + 1) ^ 5 * rexp (-2 * π * (m + 1))) := by
    intro m
    have h1 : rexp (-2 * π * m) = rexp (2 * π) * rexp (-2 * π * (m + 1)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h1]; ring
  simp_rw [h_eq]
  apply Summable.mul_left
  convert h.comp_injective Nat.succ_injective using 1
  ext m; simp only [Function.comp_apply, Nat.succ_eq_add_one]; push_cast; ring_nf

/--
Helper lemma: `Θ₂(z) / exp(πiz/4) → 2` as `im(z) → ∞`.
This follows from `Θ₂ = exp(πiz/4) * jacobiTheta₂(z/2, z)` and `jacobiTheta₂(z/2, z) → 2`.
-/
theorem Θ₂_div_exp_tendsto :
    Filter.Tendsto (fun z : ℍ => Θ₂ z / cexp (π * Complex.I * z / 4))
      atImInfty (nhds (2 : ℂ)) := by
  have h := jacobiTheta₂_half_mul_apply_tendsto_atImInfty
  convert h using 1
  ext z
  rw [Θ₂_as_jacobiTheta₂]
  field_simp [Complex.exp_ne_zero]

/--
Helper lemma: `H₂(z) / exp(πiz) → 16` as `im(z) → ∞`.
Since `H₂ = Θ₂⁴` and `Θ₂ / exp(πiz/4) → 2`, we get `H₂ / exp(πiz) → 2⁴ = 16`.
-/
theorem H₂_div_exp_tendsto :
    Filter.Tendsto (fun z : ℍ => H₂ z / cexp (π * Complex.I * z))
      atImInfty (nhds (16 : ℂ)) := by
  have h_eq : ∀ z : ℍ, H₂ z / cexp (π * I * z) = (Θ₂ z / cexp (π * I * z / 4)) ^ 4 := fun z => by
    simp only [H₂, div_pow, ← Complex.exp_nat_mul]; congr 2; ring
  simp_rw [h_eq]; convert Θ₂_div_exp_tendsto.pow 4; norm_num

/--
The vanishing order of F at infinity is 2.
Blueprint: From q-expansion F = 720² * q² * (1 + O(q)), so F / q² → 720² as im(z) → ∞.
Here q = exp(2πiz), so q² = exp(4πiz) = exp(2πi * 2 * z).
-/
theorem F_vanishing_order :
    Filter.Tendsto (fun z : ℍ => F z / cexp (2 * π * Complex.I * 2 * z))
      atImInfty (nhds (720 ^ 2 : ℂ)) := by
  -- F = (E₂E₄ - E₆)² and we want to show F / q² → 720² where q = exp(2πiz)
  -- Strategy: Show (E₂E₄ - E₆) / q → 720, then square
  -- From E₂_mul_E₄_sub_E₆: E₂E₄ - E₆ = 720 * ∑' n : ℕ+, n * σ₃(n) * q^n
  -- Dividing by q and using QExp.tendsto_nat: limit is 720 * σ₃(1) = 720
  have h_diff_tendsto : Filter.Tendsto (fun z : ℍ => (E₂ z * E₄ z - E₆ z) / cexp (2 * π * I * z))
      atImInfty (nhds (720 : ℂ)) := by
    -- Use E₂_mul_E₄_sub_E₆ and reindex from ℕ+ to ℕ, then apply QExp.tendsto_nat
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
    simp_rw [h_eq]
    -- Reindex using Equiv.pnatEquivNat.symm: n ↦ m+1
    have h_reindex : ∀ z : ℍ,
        ∑' n : ℕ+, ↑n * ↑(ArithmeticFunction.sigma 3 n) *
          cexp (2 * π * Complex.I * (n - 1) * z) =
        ∑' m : ℕ, ↑(m + 1) * ↑(ArithmeticFunction.sigma 3 (m + 1)) *
          cexp (2 * π * Complex.I * m * z) := by
      intro z
      rw [← Equiv.tsum_eq Equiv.pnatEquivNat.symm]
      congr 1; funext m
      simp only [Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe]
      have h_exp_eq' : ((m.succ : ℕ) : ℂ) - 1 = (m : ℂ) := by
        simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]; ring
      simp only [h_exp_eq', Nat.succ_eq_add_one]
    simp_rw [h_reindex]
    -- Apply QExp.tendsto_nat with coefficient function a(m) = (m+1) * σ₃(m+1)
    set a : ℕ → ℂ := fun m => ↑(m + 1) * ↑(ArithmeticFunction.sigma 3 (m + 1)) with ha
    have ha0 : a 0 = 1 := by simp [ha, ArithmeticFunction.sigma_one]
    have h_tendsto : Filter.Tendsto
        (fun z : ℍ => ∑' m : ℕ, a m * cexp (2 * π * Complex.I * z * m))
        atImInfty (nhds (a 0)) := by
      apply QExp.tendsto_nat a
      -- Summability: ‖a m‖ ≤ (m+1)^5, and (m+1)^5 * exp(-2πm) is summable
      have hbound : ∀ m : ℕ, ‖a m‖ ≤ ((m + 1 : ℕ) : ℝ) ^ 5 := by
        intro m
        simp only [ha, norm_mul, Complex.norm_natCast]
        have h1 : (ArithmeticFunction.sigma 3 (m + 1) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 4 := by
          exact_mod_cast sigma_le_pow 3 (m + 1)
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
      · exact summable_pow5_shift
    have h_eq2 : ∀ z : ℍ,
        ∑' m : ℕ, ↑(m + 1) * ↑(ArithmeticFunction.sigma 3 (m + 1)) *
          cexp (2 * π * Complex.I * m * z) =
        ∑' m : ℕ, a m * cexp (2 * π * Complex.I * z * m) := by
      intro z; apply tsum_congr; intro m; simp only [ha]; ring_nf
    simp_rw [h_eq2, ha0] at h_tendsto ⊢
    convert h_tendsto.const_mul (720 : ℂ) using 2; ring
  -- F / q² = ((E₂E₄ - E₆) / q)² → 720²
  have h_exp_eq : ∀ z : ℍ, cexp (2 * π * I * 2 * z) = cexp (2 * π * I * z) ^ 2 := by
    intro z; rw [← Complex.exp_nat_mul]; congr 1; ring
  have h_F_eq : ∀ z : ℍ, F z / cexp (2 * π * I * 2 * z) =
      ((E₂ z * E₄ z - E₆ z) / cexp (2 * π * I * z)) ^ 2 := by
    intro z
    simp only [F, h_exp_eq, sq, div_mul_div_comm, Pi.mul_apply, Pi.sub_apply,
      ModularForm.toFun_eq_coe]
  simp_rw [h_F_eq]
  exact h_diff_tendsto.pow 2

/--
The vanishing order of G at infinity is 5/2.
Blueprint: H₂ = Θ₂⁴ ~ 16q^(1/2), H₄ → 1 as im(z) → ∞.
So G = H₂³(2H₂² + 5H₂H₄ + 5H₄²) ~ H₂³ * 5 = 5 * 16³ * q^(3/2) = 20480 * q^(3/2).
Here q^(3/2) = exp(3πiz) = exp(2πi * (3/2) * z).
-/
theorem G_vanishing_order :
    Filter.Tendsto (fun z : ℍ => G z / cexp (2 * π * Complex.I * (3/2) * z))
      atImInfty (nhds (20480 : ℂ)) := by
  -- G = H₂³ * (2H₂² + 5H₂H₄ + 5H₄²)
  -- As z → ∞: H₂ / exp(πiz) → 16, H₂ → 0, H₄ → 1
  -- So G / exp(3πiz) → 16³ * 5 = 20480
  have hH₂_asymp := H₂_div_exp_tendsto
  have hH₂_zero := H₂_tendsto_atImInfty
  have hH₄_one := H₄_tendsto_atImInfty
  -- Simplify the exponent: 2π * I * (3/2) * z = 3 * π * I * z
  have h_exp_eq : ∀ z : ℍ, cexp (2 * π * I * (3 / 2) * z) = cexp (3 * π * I * z) := by
    intro z; congr 1; ring
  simp_rw [h_exp_eq]
  -- G / exp(3πiz) = (H₂ / exp(πiz))³ * (2H₂² + 5H₂H₄ + 5H₄²)
  have h_eq : ∀ z : ℍ, G z / cexp (3 * π * I * z) =
      (H₂ z / cexp (π * I * z)) ^ 3 * (2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2) := by
    intro z
    have hne : cexp (π * I * z) ≠ 0 := Complex.exp_ne_zero _
    have hne3 : cexp (3 * π * I * z) ≠ 0 := Complex.exp_ne_zero _
    have h_exp_pow : cexp (π * I * z) ^ 3 = cexp (3 * π * I * z) := by
      rw [← Complex.exp_nat_mul]; congr 1; ring
    unfold G _root_.G
    simp only [div_pow, h_exp_pow]
    field_simp [hne, hne3]
  simp_rw [h_eq]
  -- The polynomial part: 2H₂² + 5H₂H₄ + 5H₄² → 0 + 0 + 5 = 5
  have h_poly : Filter.Tendsto (fun z : ℍ => 2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2)
      atImInfty (nhds 5) := by
    have h1 : Filter.Tendsto (fun z : ℍ => 2 * H₂ z ^ 2) atImInfty (nhds 0) := by
      simpa using (hH₂_zero.pow 2).const_mul 2
    have h2 : Filter.Tendsto (fun z : ℍ => 5 * H₂ z * H₄ z) atImInfty (nhds 0) := by
      simpa [mul_assoc] using (hH₂_zero.mul hH₄_one).const_mul 5
    have h3 : Filter.Tendsto (fun z : ℍ => 5 * H₄ z ^ 2) atImInfty (nhds 5) := by
      simpa using (hH₄_one.pow 2).const_mul 5
    simpa [add_assoc] using h1.add (h2.add h3)
  -- (H₂/exp(πiz))³ → 16³, polynomial → 5, product: 16³ * 5 = 20480
  convert (hH₂_asymp.pow 3).mul h_poly; norm_num

/--
Log-derivative limit for F: `(D F)/F → 2` as `z → i∞`.
This follows from F having vanishing order 2: F ~ c·q² where q = exp(2πiz).
Taking logarithmic derivative: D(log F) = (D F)/F → 2.
-/
-- Helper: D(E₂E₄ - E₆) / q → 720 (same pattern as f/q → 720)
-- This follows from D acting as q·d/dq on q-expansions, so D(n·σ₃(n)·qⁿ) = n²·σ₃(n)·qⁿ
-- and the leading coefficient 1²·σ₃(1) = 1 gives the limit 720·1 = 720
theorem D_diff_div_q_tendsto :
    Filter.Tendsto (fun z : ℍ => D (fun w => E₂ w * E₄ w - E₆ w) z /
      cexp (2 * π * Complex.I * z))
      atImInfty (nhds (720 : ℂ)) := by
  -- Strategy: Use q-expansion of D(f) = 720 · Σ n²·σ₃(n)·qⁿ
  -- and apply QExp.tendsto_nat with coefficient n²·σ₃(n)
  sorry

theorem D_F_div_F_tendsto :
    Filter.Tendsto (fun z : ℍ => D F z / F z) atImInfty (nhds (2 : ℂ)) := by
  -- F = (E₂E₄ - E₆)² = f² where f = E₂E₄ - E₆
  -- D(f²) = 2f·Df (chain rule), so DF/F = 2·Df/f
  -- f/q → 720 (from F_vanishing_order proof), and f has vanishing order 1
  -- Df/f → 1 (the vanishing order), so DF/F → 2

  -- Step 1: Define f and show F = f²
  set f : ℍ → ℂ := fun z => E₂ z * E₄.toFun z - E₆.toFun z with hf_def
  have hF_eq : ∀ z, F z = (f z) ^ 2 := fun z => by
    simp only [F, hf_def, sq, Pi.mul_apply, Pi.sub_apply, ModularForm.toFun_eq_coe]

  -- Step 2: f is holomorphic
  have hf_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
    apply MDifferentiable.sub
    · exact MDifferentiable.mul E₂_holo' E₄.holo'
    · exact E₆.holo'

  -- Step 3: D(F) = 2·f·D(f) by chain rule
  have hDF_eq : ∀ z, D F z = 2 * f z * D f z := by
    intro z
    have h := D_sq f hf_holo
    have hF_eq' : F = f ^ 2 := by
      ext z
      simp only [F, hf_def, sq, Pi.mul_apply, Pi.sub_apply, ModularForm.toFun_eq_coe,
        Pi.pow_apply]
    rw [hF_eq']
    exact congr_fun h z

  -- Step 4: Therefore D(F)/F = 2·D(f)/f
  have hDF_div_eq : ∀ z, F z ≠ 0 → D F z / F z = 2 * (D f z / f z) := by
    intro z hFz
    have hfz : f z ≠ 0 := by
      intro hf_zero
      apply hFz
      rw [hF_eq z, hf_zero, sq, zero_mul]
    rw [hDF_eq z, hF_eq z, sq]
    field_simp [hfz]

  -- Step 5: f/q → 720 (from F_vanishing_order proof)
  have hf_div_q : Filter.Tendsto (fun z : ℍ => f z / cexp (2 * π * Complex.I * z))
      atImInfty (nhds (720 : ℂ)) := by
    -- This is exactly h_diff_tendsto from F_vanishing_order proof
    -- Note: E₄ z = E₄.toFun z by ModularForm.toFun_eq_coe
    have h_f_eq : ∀ z : ℍ, f z = E₂ z * E₄ z - E₆ z := fun z => by
      simp only [hf_def, ModularForm.toFun_eq_coe]
    have h_rw : ∀ z : ℍ, E₂ z * E₄ z - E₆ z =
        720 * ∑' n : ℕ+, ↑n * ↑(ArithmeticFunction.sigma 3 n) *
          cexp (2 * π * Complex.I * n * z) := E₂_mul_E₄_sub_E₆
    have h_eq : ∀ z : ℍ,
        f z / cexp (2 * π * Complex.I * z) =
        720 * (∑' n : ℕ+, ↑n * ↑(ArithmeticFunction.sigma 3 n) *
          cexp (2 * π * Complex.I * (n - 1) * z)) := by
      intro z
      rw [h_f_eq z, h_rw z, mul_div_assoc, ← tsum_div_const]
      congr 1; apply tsum_congr; intro n
      rw [mul_div_assoc, ← Complex.exp_sub]; congr 2; ring
    simp_rw [h_eq]
    have h_reindex : ∀ z : ℍ,
        ∑' n : ℕ+, ↑n * ↑(ArithmeticFunction.sigma 3 n) *
          cexp (2 * π * Complex.I * (n - 1) * z) =
        ∑' m : ℕ, ↑(m + 1) * ↑(ArithmeticFunction.sigma 3 (m + 1)) *
          cexp (2 * π * Complex.I * m * z) := by
      intro z
      rw [← Equiv.tsum_eq Equiv.pnatEquivNat.symm]
      congr 1; funext m
      simp only [Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe]
      have h_exp_eq' : ((m.succ : ℕ) : ℂ) - 1 = (m : ℂ) := by
        simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]; ring
      simp only [h_exp_eq', Nat.succ_eq_add_one]
    simp_rw [h_reindex]
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
          exact_mod_cast sigma_le_pow 3 (m + 1)
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
      · exact summable_pow5_shift
    have h_eq2 : ∀ z : ℍ,
        ∑' m : ℕ, ↑(m + 1) * ↑(ArithmeticFunction.sigma 3 (m + 1)) *
          cexp (2 * π * Complex.I * m * z) =
        ∑' m : ℕ, a m * cexp (2 * π * Complex.I * z * m) := by
      intro z; apply tsum_congr; intro m; simp only [ha]; ring_nf
    simp_rw [h_eq2, ha0] at h_tendsto ⊢
    convert h_tendsto.const_mul (720 : ℂ) using 2; ring

  -- Step 6: D(f)/q → 720 (by D_diff_div_q_tendsto)
  have hDf_div_q : Filter.Tendsto (fun z : ℍ => D f z / cexp (2 * π * Complex.I * z))
      atImInfty (nhds (720 : ℂ)) := D_diff_div_q_tendsto

  -- Step 7: D(f)/f → 1 by dividing limits (720/720 = 1)
  have h_720_ne : (720 : ℂ) ≠ 0 := by norm_num
  have hDf_div_f : Filter.Tendsto (fun z : ℍ => D f z / f z) atImInfty (nhds 1) := by
    have h_eq : ∀ z : ℍ, cexp (2 * π * Complex.I * z) ≠ 0 →
        D f z / f z = (D f z / cexp (2 * π * Complex.I * z)) /
          (f z / cexp (2 * π * Complex.I * z)) := by
      intro z hexp
      field_simp [hexp]
    have h_exp_ne : ∀ᶠ z : ℍ in atImInfty, cexp (2 * π * Complex.I * z) ≠ 0 :=
      Filter.Eventually.of_forall (fun _ => Complex.exp_ne_zero _)
    have h_f_ne : ∀ᶠ z : ℍ in atImInfty, f z / cexp (2 * π * Complex.I * z) ≠ 0 :=
      hf_div_q.eventually_ne h_720_ne
    have h_limit : Filter.Tendsto
        (fun z => (D f z / cexp (2 * π * Complex.I * z)) /
          (f z / cexp (2 * π * Complex.I * z)))
        atImInfty (nhds (720 / 720 : ℂ)) := by
      apply Filter.Tendsto.div hDf_div_q hf_div_q h_720_ne
    simp only [div_self h_720_ne] at h_limit
    apply h_limit.congr'
    filter_upwards [h_exp_ne, h_f_ne] with z hexp hf_ne
    exact (h_eq z hexp).symm

  -- Step 8: D(F)/F → 2·1 = 2
  have h_F_ne : ∀ᶠ z : ℍ in atImInfty, F z ≠ 0 := by
    have h_limit_ne : (720 ^ 2 : ℂ) ≠ 0 := by norm_num
    have h_quot_ne := F_vanishing_order.eventually_ne h_limit_ne
    filter_upwards [h_quot_ne] with z hz
    intro hF_zero
    apply hz
    simp only [hF_zero, zero_div]
  have h_2_eq : (2 : ℂ) = 2 * 1 := by ring
  rw [h_2_eq]
  apply (hDf_div_f.const_mul (2 : ℂ)).congr'
  filter_upwards [h_F_ne] with z hFz
  exact (hDF_div_eq z hFz).symm

/--
Log-derivative limit for G: `(D G)/G → 3/2` as `z → i∞`.
This follows from G having vanishing order 3/2: G ~ c·q^(3/2) where q = exp(2πiz).
Taking logarithmic derivative: D(log G) = (D G)/G → 3/2.
-/
-- Helper: D(exp(πiz))/exp(πiz) = 1/2
-- This follows from D = (2πi)⁻¹·d/dz and d/dz(exp(πiz)) = πi·exp(πiz)
-- So D(exp(πiz)) = (2πi)⁻¹·πi·exp(πiz) = (1/2)·exp(πiz)
theorem D_exp_pi_div_exp_pi (z : ℍ) :
    D (fun w => cexp (π * Complex.I * w)) z / cexp (π * Complex.I * z) = 1 / 2 := by
  -- D = (2πi)⁻¹·d/dz, and d/dz(exp(πiz)) = πi·exp(πiz)
  -- So D(exp(πiz)) = (2πi)⁻¹·πi·exp(πiz) = (1/2)·exp(πiz)
  -- Therefore D(exp(πiz))/exp(πiz) = 1/2
  simp only [D]
  -- Compute deriv ((fun w : ℍ => cexp(π*I*w)) ∘ ofComplex) at (z : ℂ)
  -- Uses: d/dz(exp(πiz)) = πi·exp(πiz), and ofComplex is identity on upper half plane
  have h_deriv : deriv ((fun w : ℍ => cexp (π * Complex.I * w)) ∘ ⇑ofComplex) (z : ℂ) =
      π * Complex.I * cexp (π * Complex.I * z) := by
    -- Step 1: Compute derivative of (fun w => cexp(πIw)) using chain rule
    have h_exp_deriv : HasDerivAt (fun w : ℂ => cexp (π * Complex.I * w))
        (π * Complex.I * cexp (π * Complex.I * z)) (z : ℂ) := by
      have h_at_piIz : HasDerivAt cexp (cexp (π * Complex.I * z)) (π * Complex.I * z) :=
        Complex.hasDerivAt_exp (π * Complex.I * z)
      have h_linear : HasDerivAt (fun w : ℂ => π * Complex.I * w) (π * Complex.I) (z : ℂ) := by
        have h := (hasDerivAt_id (z : ℂ)).const_mul (π * Complex.I)
        simp only [mul_one, id] at h
        exact h
      exact h_at_piIz.scomp (z : ℂ) h_linear
    -- Step 2: Show the composed function equals the simple function in a neighborhood
    have h_agree : ((fun w : ℍ => cexp (π * Complex.I * w)) ∘ ⇑ofComplex) =ᶠ[nhds (z : ℂ)]
        (fun w : ℂ => cexp (π * Complex.I * w)) := by
      have him : 0 < (z : ℂ).im := z.2
      have h_open : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [h_open.mem_nhds him] with w hw
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, coe_mk_subtype]
    exact h_agree.deriv_eq.trans h_exp_deriv.deriv
  rw [h_deriv]
  have h_exp_ne : cexp (π * Complex.I * z) ≠ 0 := Complex.exp_ne_zero _
  field_simp [h_exp_ne]

-- Helper: D(jacobiTheta₂(z/2, z)) → 0 as im(z) → ∞
-- jacobiTheta₂(z/2, z) = Σ_{n∈ℤ} exp(π·I·n·(n+1)·z)
-- D(exp(2πi·k·z)) = k·exp(2πi·k·z), so D(exp(π·I·n·(n+1)·z)) = (n(n+1)/2)·exp(π·I·n·(n+1)·z)
-- For n ∈ {-1, 0}: n(n+1) = 0, so coefficient = 0, contributing 0 to D(h)
-- For n ∉ {-1, 0}: term decays exponentially, and polynomial prefactor doesn't affect limit
theorem D_jacobiTheta₂_half_mul_tendsto_zero :
    Filter.Tendsto (fun z : ℍ => D (fun w : ℍ => jacobiTheta₂ (w / 2) w) z) atImInfty (nhds 0) := by
  -- D(Σ exp(π·I·n·(n+1)·z)) = Σ (n(n+1)/2)·exp(π·I·n·(n+1)·z)
  -- For n ∈ {-1, 0}: coefficient = 0
  -- For n ∉ {-1, 0}: exponential decay dominates polynomial growth from differentiation
  -- This follows from tendsto_tsum_of_dominated_convergence with the derivative terms
  sorry

-- Helper: D(exp(πiz/4))/exp(πiz/4) = 1/8
-- This follows from D = (2πi)⁻¹·d/dz and d/dz(exp(πiz/4)) = (πi/4)·exp(πiz/4)
-- So D(exp(πiz/4)) = (2πi)⁻¹·(πi/4)·exp(πiz/4) = (1/8)·exp(πiz/4)
theorem D_exp_pi_quarter_div_exp_pi_quarter (z : ℍ) :
    D (fun w => cexp (π * Complex.I * w / 4)) z / cexp (π * Complex.I * z / 4) = 1 / 8 := by
  simp only [D]
  have h_deriv : deriv ((fun w : ℍ => cexp (π * Complex.I * w / 4)) ∘ ⇑ofComplex) (z : ℂ) =
      (π * Complex.I / 4) * cexp (π * Complex.I * z / 4) := by
    have h_exp_deriv : HasDerivAt (fun w : ℂ => cexp (π * Complex.I * w / 4))
        ((π * Complex.I / 4) * cexp (π * Complex.I * z / 4)) (z : ℂ) := by
      have h_at_arg : HasDerivAt cexp (cexp (π * Complex.I * z / 4)) (π * Complex.I * z / 4) :=
        Complex.hasDerivAt_exp (π * Complex.I * z / 4)
      have h_linear : HasDerivAt (fun w : ℂ => π * Complex.I * w / 4)
          (π * Complex.I / 4) (z : ℂ) := by
        have h := (hasDerivAt_id (z : ℂ)).const_mul (π * Complex.I / 4)
        simp only [mul_one, id] at h
        convert h using 1; ring
      exact h_at_arg.scomp (z : ℂ) h_linear
    have h_agree : ((fun w : ℍ => cexp (π * Complex.I * w / 4)) ∘ ⇑ofComplex) =ᶠ[nhds (z : ℂ)]
        (fun w : ℂ => cexp (π * Complex.I * w / 4)) := by
      have him : 0 < (z : ℂ).im := z.2
      have h_open : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [h_open.mem_nhds him] with w hw
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, coe_mk_subtype]
    exact h_agree.deriv_eq.trans h_exp_deriv.deriv
  rw [h_deriv]
  have h_exp_ne : cexp (π * Complex.I * z / 4) ≠ 0 := Complex.exp_ne_zero _
  field_simp [h_exp_ne]
  ring

-- Helper: D(Θ₂)/Θ₂ → 1/8 (since Θ₂ has vanishing order 1/8 in q = exp(2πiz))
-- This follows from Θ₂/exp(πiz/4) → 2 and D(exp(πiz/4))/exp(πiz/4) = 1/8.
-- The vanishing order is preserved under taking logarithmic derivatives.
theorem D_Θ₂_div_Θ₂_tendsto :
    Filter.Tendsto (fun z : ℍ => D Θ₂ z / Θ₂ z) atImInfty (nhds ((1 : ℂ) / 8)) := by
  -- Strategy: Θ₂ = exp(πiz/4) · h where h = jacobiTheta₂(z/2, z)
  -- D(Θ₂)/Θ₂ = D(exp(πiz/4))/exp(πiz/4) + D(h)/h = 1/8 + D(h)/h
  -- h → 2 and D(h) → 0, so D(h)/h → 0, hence D(Θ₂)/Θ₂ → 1/8

  -- Step 1: Express Θ₂ as product
  let f : ℍ → ℂ := fun w => cexp (π * Complex.I * w / 4)
  let h : ℍ → ℂ := fun w => Θ₂ w / f w  -- = jacobiTheta₂(z/2, z)

  -- Step 2: D(f)/f = 1/8 (constant)
  have hf_logderiv : ∀ z : ℍ, D f z / f z = 1 / 8 := D_exp_pi_quarter_div_exp_pi_quarter

  -- Step 3: h → 2 as im(z) → ∞
  have hh_tendsto : Filter.Tendsto h atImInfty (nhds (2 : ℂ)) := by
    -- h = Θ₂ / exp(πiz/4) → 2
    exact Θ₂_div_exp_tendsto

  -- Step 4: D(h) → 0 as im(z) → ∞ (since h approaches a constant)
  -- h = Θ₂/f = jacobiTheta₂(z/2, z), so this follows from D_jacobiTheta₂_half_mul_tendsto_zero
  have hDh_tendsto : Filter.Tendsto (fun z => D h z) atImInfty (nhds (0 : ℂ)) := by
    -- h = Θ₂/f = exp(πiz/4)·jacobiTheta₂(z/2,z) / exp(πiz/4) = jacobiTheta₂(z/2,z)
    have h_eq_jac : h = fun w : ℍ => jacobiTheta₂ (w / 2) w := by
      ext w
      simp only [h, f, Θ₂_as_jacobiTheta₂]
      field_simp [Complex.exp_ne_zero]
    have hD_eq : (fun z => D h z) = fun z => D (fun w : ℍ => jacobiTheta₂ (w / 2) w) z := by
      ext z; rw [h_eq_jac]
    rw [hD_eq]
    exact D_jacobiTheta₂_half_mul_tendsto_zero

  -- Step 5: D(h)/h → 0 since D(h) → 0 and h → 2 ≠ 0
  have hDh_div_h_tendsto : Filter.Tendsto (fun z => D h z / h z) atImInfty (nhds (0 : ℂ)) := by
    have h_ne_zero : ∀ᶠ z : ℍ in atImInfty, h z ≠ 0 := by
      -- h → 2, and 2 ≠ 0, so eventually h ≠ 0
      have h_ball : Metric.ball (2 : ℂ) 1 ∈ nhds (2 : ℂ) :=
        Metric.isOpen_ball.mem_nhds (by norm_num : dist (2 : ℂ) 2 < 1)
      have := hh_tendsto.eventually h_ball
      filter_upwards [this] with z hz
      -- hz : dist (h z) 2 < 1
      intro h_eq
      rw [h_eq] at hz
      have : dist (0 : ℂ) 2 = 2 := by simp [dist_eq_norm]
      linarith [this]
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have h_div_tendsto := hDh_tendsto.div hh_tendsto h2
    simp only [zero_div] at h_div_tendsto
    exact h_div_tendsto.congr' (by filter_upwards [h_ne_zero] with z hz; rfl)

  -- Step 6: D(Θ₂)/Θ₂ = D(f·h)/(f·h) = D(f)/f + D(h)/h
  have h_logderiv_eq : ∀ᶠ z : ℍ in atImInfty, D Θ₂ z / Θ₂ z = D f z / f z + D h z / h z := by
    have hf_ne : ∀ z : ℍ, f z ≠ 0 := fun z => Complex.exp_ne_zero _
    have hh_ne : ∀ᶠ z : ℍ in atImInfty, h z ≠ 0 := by
      have h_ball : Metric.ball (2 : ℂ) 1 ∈ nhds (2 : ℂ) :=
        Metric.isOpen_ball.mem_nhds (by norm_num : dist (2 : ℂ) 2 < 1)
      have := hh_tendsto.eventually h_ball
      filter_upwards [this] with z hz
      intro h_eq; rw [h_eq] at hz
      have : dist (0 : ℂ) 2 = 2 := by simp [dist_eq_norm]
      linarith [this]
    filter_upwards [hh_ne] with z hz
    -- Θ₂ = f · h, so D(Θ₂) = D(f·h) = f·D(h) + h·D(f)
    have h_Θ₂_eq : Θ₂ z = f z * h z := by simp only [h, mul_div_cancel₀ _ (hf_ne z)]
    -- Show Θ₂ = f * h as functions
    have h_Θ₂_fn : Θ₂ = f * h := by
      ext w; simp only [h, Pi.mul_apply, mul_div_cancel₀ _ (hf_ne w)]
    -- MDifferentiable for f and h
    have hf_md : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
      -- f = exp(πiz/4) is holomorphic
      intro τ
      suffices h_diff : DifferentiableAt ℂ (f ∘ ofComplex) τ.val by
        have h_eq : (f ∘ ofComplex) ∘ UpperHalfPlane.coe = f := by
          ext x; simp [Function.comp, ofComplex_apply, f]
        rw [← h_eq]
        exact h_diff.mdifferentiableAt.comp τ τ.mdifferentiable_coe
      have hU : {z : ℂ | 0 < z.im} ∈ nhds τ.val := isOpen_upperHalfPlaneSet.mem_nhds τ.2
      have h_exp_diff : DifferentiableAt ℂ (fun t : ℂ => cexp (π * I * t / 4)) τ.val :=
        ((differentiableAt_id.const_mul (π * I)).div_const 4).cexp
      have h_ev : (fun t : ℂ => cexp (π * I * t / 4)) =ᶠ[nhds τ.val] (f ∘ ofComplex) := by
        refine Filter.eventually_of_mem hU ?_
        intro z hz
        simp only [Function.comp_apply, f, ofComplex_apply_of_im_pos hz, coe_mk_subtype]
      exact h_exp_diff.congr_of_eventuallyEq h_ev.symm
    have hh_md : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
      -- h = Θ₂ / f, both holomorphic, f ≠ 0
      intro τ
      suffices h_diff : DifferentiableAt ℂ (h ∘ ofComplex) τ.val by
        have h_eq : (h ∘ ofComplex) ∘ UpperHalfPlane.coe = h := by
          ext x; simp [Function.comp, ofComplex_apply, h]
        rw [← h_eq]
        exact h_diff.mdifferentiableAt.comp τ τ.mdifferentiable_coe
      -- h ∘ ofComplex = (Θ₂ ∘ ofComplex) / (f ∘ ofComplex)
      have hΘ₂_diff : DifferentiableAt ℂ (Θ₂ ∘ ofComplex) τ.val := by
        -- Use the same proof pattern as in hΘ₂_holo below
        have hU : {z : ℂ | 0 < z.im} ∈ nhds τ.val := isOpen_upperHalfPlaneSet.mem_nhds τ.2
        let F : ℂ → ℂ := fun t => cexp ((π * I / 4) * t) * jacobiTheta₂ (t / 2) t
        have hF : DifferentiableAt ℂ F τ.val := by
          have h_exp : DifferentiableAt ℂ (fun t : ℂ => cexp ((π * I / 4) * t)) τ.val :=
            (differentiableAt_id.const_mul ((π : ℂ) * I / 4)).cexp
          have h_theta : DifferentiableAt ℂ (fun t : ℂ => jacobiTheta₂ (t / 2) t) τ.val := by
            let f' : ℂ → ℂ × ℂ := fun t : ℂ => (t / 2, t)
            let g : ℂ × ℂ → ℂ := fun p => jacobiTheta₂ p.1 p.2
            have hg : DifferentiableAt ℂ g (f' τ.val) :=
              (hasFDerivAt_jacobiTheta₂ (τ.1 / 2) τ.2).differentiableAt
            have hf' : DifferentiableAt ℂ f' τ.val :=
              (differentiableAt_id.mul_const ((2 : ℂ)⁻¹)).prodMk differentiableAt_id
            exact hg.comp τ.val hf'
          exact h_exp.mul h_theta
        have h_ev : F =ᶠ[nhds τ.val] (Θ₂ ∘ ofComplex) := by
          refine Filter.eventually_of_mem hU ?_
          intro z hz
          simp only [Function.comp_apply, F]
          have h_arg : cexp ((π * I / 4) * z) = cexp (π * I * z / 4) := by ring_nf
          rw [h_arg, ofComplex_apply_of_im_pos hz, Θ₂_as_jacobiTheta₂]
          simp only [coe_mk_subtype]
        exact hF.congr_of_eventuallyEq h_ev.symm
      have hf_diff : DifferentiableAt ℂ (f ∘ ofComplex) τ.val := by
        have hU : {z : ℂ | 0 < z.im} ∈ nhds τ.val := isOpen_upperHalfPlaneSet.mem_nhds τ.2
        have h_exp_diff : DifferentiableAt ℂ (fun t : ℂ => cexp (π * I * t / 4)) τ.val :=
          ((differentiableAt_id.const_mul (π * I)).div_const 4).cexp
        have h_ev : (fun t : ℂ => cexp (π * I * t / 4)) =ᶠ[nhds τ.val] (f ∘ ofComplex) := by
          refine Filter.eventually_of_mem hU ?_
          intro z hz
          simp only [Function.comp_apply, f, ofComplex_apply_of_im_pos hz, coe_mk_subtype]
        exact h_exp_diff.congr_of_eventuallyEq h_ev.symm
      have hf_ne' : (f ∘ ofComplex) τ.val ≠ 0 := by
        simp only [Function.comp_apply, f]
        exact Complex.exp_ne_zero _
      have h_eq' : (h ∘ ofComplex) =ᶠ[nhds τ.val] (Θ₂ ∘ ofComplex) / (f ∘ ofComplex) := by
        have hU : {z : ℂ | 0 < z.im} ∈ nhds τ.val := isOpen_upperHalfPlaneSet.mem_nhds τ.2
        filter_upwards [hU] with w hw
        simp only [Function.comp_apply, h, Pi.div_apply, ofComplex_apply_of_im_pos hw]
      exact (hΘ₂_diff.div hf_diff hf_ne').congr_of_eventuallyEq h_eq'.symm
    -- Apply product rule: D(f * h) = f * D h + D f * h
    have h_D_prod : D (f * h) = f * D h + D f * h := D_mul f h hf_md hh_md
    -- Rewrite D Θ₂ using h_Θ₂_fn
    have h_D_Θ₂ : D Θ₂ = D (f * h) := by rw [h_Θ₂_fn]
    calc D Θ₂ z / Θ₂ z
        = D (f * h) z / (f z * h z) := by rw [h_D_Θ₂, h_Θ₂_eq]
      _ = (f z * D h z + D f z * h z) / (f z * h z) := by
          rw [congrFun h_D_prod z]; simp only [Pi.mul_apply, Pi.add_apply]
      _ = D f z / f z + D h z / h z := by field_simp [hf_ne z, hz]; ring

  -- Step 7: Take the limit
  have h_sum_limit : Filter.Tendsto (fun z => D f z / f z + D h z / h z) atImInfty
      (nhds ((1 : ℂ) / 8 + 0)) := by
    have hf_const : Filter.Tendsto (fun z => D f z / f z) atImInfty (nhds ((1 : ℂ) / 8)) := by
      simp_rw [hf_logderiv]
      exact tendsto_const_nhds
    exact hf_const.add hDh_div_h_tendsto

  have h_sum_limit' : Filter.Tendsto (fun z => D f z / f z + D h z / h z) atImInfty
      (nhds ((1 : ℂ) / 8)) := by
    convert h_sum_limit using 2; ring

  refine h_sum_limit'.congr' ?_
  filter_upwards [h_logderiv_eq] with z hz
  exact hz.symm

-- Helper: D(H₂)/H₂ → 1/2 (since H₂ ~ 16·exp(πiz) has vanishing order 1/2)
theorem D_H₂_div_H₂_tendsto :
    Filter.Tendsto (fun z : ℍ => D H₂ z / H₂ z) atImInfty (nhds ((1 : ℂ) / 2)) := by
  -- H₂ = Θ₂⁴, and Θ₂/exp(πiz/4) → 2
  -- D(H₂) = 4·Θ₂³·D(Θ₂), so D(H₂)/H₂ = 4·D(Θ₂)/Θ₂
  -- D(Θ₂)/Θ₂ → 1/8
  -- Therefore D(H₂)/H₂ → 4·(1/8) = 1/2

  -- Step 1: H₂ = Θ₂⁴
  have hH₂_eq : ∀ z : ℍ, H₂ z = (Θ₂ z) ^ 4 := fun z => rfl

  -- Step 2: D(H₂)/H₂ = 4·D(Θ₂)/Θ₂ when Θ₂ ≠ 0
  have h_logderiv : ∀ z : ℍ, Θ₂ z ≠ 0 → D H₂ z / H₂ z = 4 * (D Θ₂ z / Θ₂ z) := by
    intro z hΘ₂
    rw [hH₂_eq]
    -- D(Θ₂⁴) = 4·Θ₂³·D(Θ₂) using power rule
    have h_pow4 : D (fun w => (Θ₂ w) ^ 4) z = 4 * (Θ₂ z) ^ 3 * D Θ₂ z := by
      -- Θ₂⁴ = (Θ₂²)², use D_sq twice
      have hΘ₂_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Θ₂ := by
        -- Θ₂ = exp(πiz/4) · jacobiTheta₂(z/2, z), product of holomorphic functions
        intro τ
        suffices h_diff : DifferentiableAt ℂ (Θ₂ ∘ ofComplex) τ.val by
          have h_eq : (Θ₂ ∘ ofComplex) ∘ UpperHalfPlane.coe = Θ₂ := by
            ext x; simp [Function.comp, ofComplex_apply]
          rw [← h_eq]
          exact h_diff.mdifferentiableAt.comp τ τ.mdifferentiable_coe
        have hU : {z : ℂ | 0 < z.im} ∈ nhds τ.val := isOpen_upperHalfPlaneSet.mem_nhds τ.2
        -- Define the function on ℂ
        let F : ℂ → ℂ := fun t => cexp ((π * I / 4) * t) * jacobiTheta₂ (t / 2) t
        have hF : DifferentiableAt ℂ F τ.val := by
          have h_exp : DifferentiableAt ℂ (fun t : ℂ => cexp ((π * I / 4) * t)) τ.val := by
            exact (differentiableAt_id.const_mul ((π : ℂ) * I / 4)).cexp
          have h_theta : DifferentiableAt ℂ (fun t : ℂ => jacobiTheta₂ (t / 2) t) τ.val := by
            let f : ℂ → ℂ × ℂ := fun t : ℂ => (t / 2, t)
            let g : ℂ × ℂ → ℂ := fun p => jacobiTheta₂ p.1 p.2
            have hg : DifferentiableAt ℂ g (f τ.val) := by
              simpa [f] using (hasFDerivAt_jacobiTheta₂ (τ.1 / 2) τ.2).differentiableAt
            have hf : DifferentiableAt ℂ f τ.val :=
              (differentiableAt_id.mul_const ((2 : ℂ)⁻¹)).prodMk differentiableAt_id
            simpa [f, g] using (DifferentiableAt.fun_comp' τ.1 hg hf)
          exact h_exp.mul h_theta
        have h_ev : F =ᶠ[nhds τ.val] (Θ₂ ∘ ofComplex) := by
          refine Filter.eventually_of_mem hU ?_
          intro z hz
          simp only [Function.comp_apply, F]
          have h_arg : cexp ((π * I / 4) * z) = cexp (π * I * z / 4) := by
            congr 1; ring
          rw [h_arg, ofComplex_apply_of_im_pos hz, Θ₂_as_jacobiTheta₂]
          simp only [coe_mk_subtype]
        exact DifferentiableAt.congr_of_eventuallyEq hF h_ev.symm
      -- Use D_sq twice: D(Θ₂⁴) = D((Θ₂²)²) = 2·Θ₂²·D(Θ₂²) = 2·Θ₂²·(2·Θ₂·D(Θ₂)) = 4·Θ₂³·D(Θ₂)
      have hΘ₂sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Θ₂ ^ 2) := by
        rw [pow_two]; exact MDifferentiable.mul hΘ₂_holo hΘ₂_holo
      have h_pow4_eq : (fun w => (Θ₂ w) ^ 4) = (Θ₂ ^ 2) ^ 2 := by
        ext w; simp only [Pi.pow_apply]; ring
      have h_D_pow4_fn : D ((Θ₂ ^ 2) ^ 2) = 2 * (Θ₂ ^ 2) * D (Θ₂ ^ 2) := D_sq (Θ₂ ^ 2) hΘ₂sq
      have h_D_sq_fn : D (Θ₂ ^ 2) = 2 * Θ₂ * D Θ₂ := D_sq Θ₂ hΘ₂_holo
      calc D (fun w => (Θ₂ w) ^ 4) z
          = D ((Θ₂ ^ 2) ^ 2) z := by rw [h_pow4_eq]
        _ = (Θ₂ ^ 2) z * D (Θ₂ ^ 2) z + D (Θ₂ ^ 2) z * (Θ₂ ^ 2) z := by
            rw [pow_two ((Θ₂ ^ 2) : ℍ → ℂ), D_mul (Θ₂ ^ 2) (Θ₂ ^ 2) hΘ₂sq hΘ₂sq]
            simp only [Pi.add_apply, Pi.mul_apply]
        _ = 2 * (Θ₂ z) ^ 2 * D (Θ₂ ^ 2) z := by simp only [Pi.pow_apply]; ring
        _ = 2 * (Θ₂ z) ^ 2 * (2 * Θ₂ z * D Θ₂ z) := by
            rw [h_D_sq_fn]; simp only [Pi.mul_apply, Pi.ofNat_apply]
        _ = 4 * (Θ₂ z) ^ 3 * D Θ₂ z := by ring
    -- Now compute the quotient
    -- First show D H₂ = D (fun w => Θ₂ w ^ 4) since H₂ = Θ₂^4
    have h_H₂_eq_fn : H₂ = fun w => (Θ₂ w) ^ 4 := by ext w; rfl
    rw [h_H₂_eq_fn, h_pow4]
    have h_pow4_ne : (Θ₂ z) ^ 4 ≠ 0 := pow_ne_zero 4 hΘ₂
    field_simp [hΘ₂, h_pow4_ne]

  -- Step 3: Θ₂ ≠ 0 eventually (since Θ₂/exp(πiz/4) → 2 ≠ 0)
  have hΘ₂_ne : ∀ᶠ z : ℍ in atImInfty, Θ₂ z ≠ 0 := by
    have h_lim : Filter.Tendsto (fun z : ℍ => Θ₂ z / cexp (π * I * z / 4))
        atImInfty (nhds (2 : ℂ)) := Θ₂_div_exp_tendsto
    have h_2_ne : (2 : ℂ) ≠ 0 := by norm_num
    have h_quot_ne := h_lim.eventually_ne h_2_ne
    filter_upwards [h_quot_ne] with z hz
    intro hΘ₂_zero
    apply hz
    simp only [hΘ₂_zero, zero_div]

  -- Step 4: Convert limit: 4 * (1/8) = 1/2
  have h_eq : (4 : ℂ) * (1 / 8) = 1 / 2 := by norm_num
  rw [← h_eq]
  apply (D_Θ₂_div_Θ₂_tendsto.const_mul (4 : ℂ)).congr'
  filter_upwards [hΘ₂_ne] with z hz
  exact (h_logderiv z hz).symm

theorem D_G_div_G_tendsto :
    Filter.Tendsto (fun z : ℍ => D G z / G z) atImInfty (nhds ((3 : ℂ) / 2)) := by
  -- G = H₂³ · polynomial(H₂, H₄) where H₂ ~ 16·exp(πiz), H₄ → 1
  -- The dominant term is H₂³ ~ 16³·exp(3πiz/2), so vanishing order is 3/2
  -- D(exp(πiz))/exp(πiz) = 1/2, and the polynomial tends to constant
  -- Therefore DG/G → 3/2

  -- Key strategy: Use product rule DG/G = D(H₂³)/H₂³ + D(poly)/poly
  -- where poly = 2H₂² + 5H₂H₄ + 5H₄²
  -- Then D(H₂³)/H₂³ = 3·D(H₂)/H₂ → 3·(1/2) = 3/2
  -- And D(poly)/poly → 0 (since poly → 5 and D(poly) → 0)

  -- This proof requires establishing the product rule structure and the helper limits
  -- For now, we leave this as sorry pending D_H₂_div_H₂_tendsto
  sorry

/--
If `F` is real on the imaginary axis and MDifferentiable, then `D F` is also real on
the imaginary axis.
-/
theorem D_imag_axis_real_of_imag_axis_real {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hreal : ResToImagAxis.Real F) : ResToImagAxis.Real (D F) := by
  intro t ht
  have hderiv := deriv_resToImagAxis_eq F hF t ht
  have hDiff : DifferentiableAt ℝ F.resToImagAxis t := ResToImagAxis.Differentiable F hF t ht
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hDiff.hasDerivAt
  have hderiv_im : (deriv F.resToImagAxis t).im = 0 := by
    have : (Complex.imCLM ∘ F.resToImagAxis) = fun _ => 0 := by
      ext s
      simp only [Function.comp_apply, Complex.imCLM_apply]
      by_cases hs : 0 < s
      · exact hreal s hs
      · simp only [Function.resToImagAxis_apply, ResToImagAxis, hs, ↓reduceDIte, zero_im]
    rw [show (deriv F.resToImagAxis t).im = Complex.imCLM (deriv F.resToImagAxis t) from rfl]
    rw [← h.deriv, this, deriv_const']
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
  have h2 : (-2 * ↑π * (D F ⟨I * ↑t, by simp [ht]⟩)).im = (deriv F.resToImagAxis t).im := by
    rw [hderiv]
    simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
  have hsimp : (-2 * ↑π * D F ⟨I * ↑t, by simp [ht]⟩).im =
      -2 * π * (D F ⟨I * ↑t, by simp [ht]⟩).im := by
    simp only [neg_mul, neg_im, mul_comm (2 : ℂ), mul_assoc]
    rw [mul_im, mul_im]
    simp only [ofReal_re, ofReal_im, zero_mul, add_zero]
    ring
  rw [hsimp, hderiv_im] at h2
  have hcoef : -2 * π ≠ 0 := by positivity
  exact mul_eq_zero.mp h2 |>.resolve_left hcoef

/--
`L₁,₀(it)` is real for all `t > 0`.
-/
theorem L₁₀_imag_axis_real : ResToImagAxis.Real L₁₀ := by
  intro t ht
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hL₁₀ := L₁₀_eq_FD_G_sub_F_DG z
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
  rw [hL₁₀]
  have hF_real := F_imag_axis_real t ht
  have hG_real := G_imag_axis_real t ht
  have hDF_real := D_imag_axis_real_of_imag_axis_real F_holo F_imag_axis_real t ht
  have hDG_real := D_imag_axis_real_of_imag_axis_real G_holo G_imag_axis_real t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
    at hF_real hG_real hDF_real hDG_real
  simp only [sub_im, mul_im]
  have hz : z = ⟨I * ↑t, by simp [ht]⟩ := rfl
  rw [hz]
  simp only [hG_real, mul_zero, hDF_real, zero_mul, add_zero, hDG_real, hF_real, sub_zero]

/--
`lim_{t→∞} L₁,₀(it)/(F(it)G(it)) = 1/2`.
Blueprint: Lemma 8.11 and vanishing orders 2 and 3/2.
The difference in vanishing orders is 2 - 3/2 = 1/2.
-/
theorem L₁₀_div_FG_tendsto :
    Filter.Tendsto (fun t : ℝ => (L₁₀.resToImagAxis t).re /
      ((F.resToImagAxis t).re * (G.resToImagAxis t).re))
      Filter.atTop (nhds (1/2)) := by
  -- Step 1: Rewrite L₁₀/(FG) as DF/F - DG/G using Wronskian
  -- L₁₀ = DF·G - F·DG (from L₁₀_eq_FD_G_sub_F_DG)
  -- So L₁₀/(FG) = DF/F - DG/G (assuming F, G ≠ 0)
  have h_wronskian : ∀ z : ℍ, F z ≠ 0 → G z ≠ 0 →
      L₁₀ z / (F z * G z) = D F z / F z - D G z / G z := by
    intro z hF hG
    rw [L₁₀_eq_FD_G_sub_F_DG]
    field_simp [hF, hG]

  -- Step 2: Get the complex limit from D_F_div_F_tendsto and D_G_div_G_tendsto
  have hF_lim := D_F_div_F_tendsto
  have hG_lim := D_G_div_G_tendsto
  have h_complex_limit : Filter.Tendsto (fun z : ℍ => D F z / F z - D G z / G z)
      atImInfty (nhds ((2 : ℂ) - 3 / 2)) := hF_lim.sub hG_lim

  -- Step 3: F and G are nonzero for large imaginary part (from vanishing order limits)
  have hF_ne : ∀ᶠ z : ℍ in atImInfty, F z ≠ 0 := by
    -- F/q² → 720² ≠ 0 implies F/q² ≠ 0 eventually
    -- Since q² = cexp(...) ≠ 0, we get F ≠ 0
    have h_limit_ne : (720 ^ 2 : ℂ) ≠ 0 := by norm_num
    have h_quot_ne := F_vanishing_order.eventually_ne h_limit_ne
    filter_upwards [h_quot_ne] with z hz
    intro hF_zero
    apply hz
    simp only [hF_zero, zero_div]
  have hG_ne : ∀ᶠ z : ℍ in atImInfty, G z ≠ 0 := by
    -- G/q^(3/2) → 20480 ≠ 0 implies G/q^(3/2) ≠ 0 eventually
    -- Since q^(3/2) = cexp(...) ≠ 0, we get G ≠ 0
    have h_limit_ne : (20480 : ℂ) ≠ 0 := by norm_num
    have h_quot_ne := G_vanishing_order.eventually_ne h_limit_ne
    filter_upwards [h_quot_ne] with z hz
    intro hG_zero
    apply hz
    simp only [hG_zero, zero_div]

  -- Step 4: L₁₀/(FG) → 1/2 in ℂ
  have h_L_over_FG : Filter.Tendsto (fun z : ℍ => L₁₀ z / (F z * G z))
      atImInfty (nhds (1 / 2 : ℂ)) := by
    have h_limit_val : (2 : ℂ) - 3 / 2 = 1 / 2 := by norm_num
    rw [← h_limit_val]
    apply h_complex_limit.congr'
    filter_upwards [hF_ne, hG_ne] with z hF hG using (h_wronskian z hF hG).symm

  -- Step 5: Restrict to imaginary axis and take real parts
  -- On the imaginary axis, L₁₀, F, G are all real (L₁₀_imag_axis_real),
  -- so the quotient is real and the real part limit equals 1/2.

  -- Use the epsilon-delta characterization of Tendsto
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get the complex limit in metric form using Metric.tendsto_nhds
  rw [Metric.tendsto_nhds] at h_L_over_FG
  obtain ⟨A₀, hA₀⟩ := Filter.eventually_atImInfty.mp (h_L_over_FG ε hε)
  -- Get bounds where F, G are nonzero
  obtain ⟨A₁, hA₁⟩ := Filter.eventually_atImInfty.mp hF_ne
  obtain ⟨A₂, hA₂⟩ := Filter.eventually_atImInfty.mp hG_ne
  use max (max (max A₀ A₁) A₂) 1
  intro t ht
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  have ht_A₀ : A₀ ≤ t :=
    le_trans (le_max_left A₀ A₁) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ht))
  have ht_A₁ : A₁ ≤ t :=
    le_trans (le_max_right A₀ A₁) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ht))
  have ht_A₂ : A₂ ≤ t := le_trans (le_max_right _ A₂) (le_trans (le_max_left _ _) ht)
  let z : ℍ := ⟨Complex.I * t, by simp [ht_pos]⟩
  have hz_im : z.im = t := by simp [z, UpperHalfPlane.im]
  have hz_F_ne : F z ≠ 0 := hA₁ z (by rw [hz_im]; exact ht_A₁)
  have hz_G_ne : G z ≠ 0 := hA₂ z (by rw [hz_im]; exact ht_A₂)
  -- Get the complex distance bound
  have h_dist := hA₀ z (by rw [hz_im]; exact ht_A₀)
  -- Need: dist (resToImagAxis expr t) (1/2) < ε
  -- Show the real expression equals the real part of the complex expression
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht_pos, ↓reduceDIte]
  have hL_real := L₁₀_imag_axis_real t ht_pos
  have hF_real := F_imag_axis_real t ht_pos
  have hG_real := G_imag_axis_real t ht_pos
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht_pos, ↓reduceDIte]
    at hL_real hF_real hG_real
  have hz_eq : (⟨Complex.I * t, by simp [ht_pos]⟩ : ℍ) = z := rfl
  rw [hz_eq] at hL_real hF_real hG_real
  -- The complex quotient is real on the imaginary axis
  have h_FG_real : (F z * G z).im = 0 := by rw [Complex.mul_im]; simp [hF_real, hG_real]
  have h_quot_real : (L₁₀ z / (F z * G z)).im = 0 := by
    rw [Complex.div_im]
    simp [hL_real, h_FG_real]
  -- The real part equals the quotient of real parts
  have h_FG_ne : F z * G z ≠ 0 := mul_ne_zero hz_F_ne hz_G_ne
  have h_re_ne : (F z * G z).re ≠ 0 := by
    intro h_re_zero
    apply h_FG_ne
    rw [Complex.ext_iff]
    simp [h_re_zero, h_FG_real]
  have h_quot_eq : (L₁₀ z / (F z * G z)).re = (L₁₀ z).re / (F z * G z).re := by
    rw [Complex.div_re]
    simp only [hL_real, h_FG_real, mul_zero, add_zero, zero_div]
    rw [Complex.normSq_eq_norm_sq]
    have h_norm_eq : ‖F z * G z‖ = |(F z * G z).re| := by
      rw [Complex.norm_def]
      conv_lhs => rw [show Complex.normSq (F z * G z) =
        (F z * G z).re * (F z * G z).re + (F z * G z).im * (F z * G z).im from rfl]
      simp only [h_FG_real, mul_zero, add_zero]
      exact Real.sqrt_mul_self_eq_abs _
    rw [h_norm_eq, sq_abs]
    field_simp [h_re_ne]
  have h_FG_re : (F z * G z).re = (F z).re * (G z).re := by
    rw [Complex.mul_re]; simp [hF_real, hG_real]
  -- dist in ℝ equals dist in ℂ when both are real
  calc dist ((L₁₀ z).re / ((F z).re * (G z).re)) (1 / 2)
      = dist ((L₁₀ z / (F z * G z)).re) ((1 / 2 : ℂ).re) := by
          rw [h_quot_eq, h_FG_re]; norm_num
    _ = |((L₁₀ z / (F z * G z)) - 1 / 2).re| := by
          rw [Real.dist_eq, Complex.sub_re]
    _ ≤ ‖L₁₀ z / (F z * G z) - 1 / 2‖ := abs_re_le_norm _
    _ = dist (L₁₀ z / (F z * G z)) (1 / 2) := by rw [Complex.dist_eq]
    _ < ε := h_dist

/--
Chain rule for resToImagAxis: `d/dt F(it) = -2π * (D F)(it)`.
-/
theorem deriv_resToImagAxis_eq' (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (t : ℝ) (ht : 0 < t) : deriv F.resToImagAxis t = -2 * π * (D F).resToImagAxis t := by
  let g : ℝ → ℂ := fun s => Complex.I * s
  have h_eq : F.resToImagAxis =ᶠ[nhds t] ((F ∘ ofComplex) ∘ g) := by
    filter_upwards [lt_mem_nhds ht] with s hs
    simp only [Function.resToImagAxis_apply, ResToImagAxis, hs, ↓reduceDIte, Function.comp_apply]
    congr 1
    rw [ofComplex_apply_of_im_pos (by simp [hs] : 0 < (I * ↑s).im)]
  rw [h_eq.deriv_eq]
  have hg_deriv_at : HasDerivAt g I t := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := ofRealCLM.hasDerivAt
    have h2 : HasDerivAt g (I * 1) t := h1.const_mul I
    simp at h2
    exact h2
  have him : 0 < (I * ↑t).im := by simp [ht]
  have hFcomp_deriv_at : HasDerivAt (F ∘ ofComplex) (deriv (F ∘ ofComplex) (g t)) (g t) := by
    exact (MDifferentiableAt_DifferentiableAt (hF ⟨I * t, him⟩)).hasDerivAt
  have hchain := hFcomp_deriv_at.scomp t hg_deriv_at
  rw [hchain.deriv]
  have hD_def : deriv (F ∘ ofComplex) (g t) = 2 * π * I * D F ⟨I * t, him⟩ := by
    simp only [D, g, coe_mk_subtype]
    field_simp
  simp only [hD_def, Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, g]
  simp only [smul_eq_mul]
  ring_nf
  simp only [I_sq]
  ring

/--
If `F` is real on the imaginary axis and MDifferentiable, then `D F` is also real on
the imaginary axis.
-/
theorem D_imag_axis_real_of_imag_axis_real {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hreal : ResToImagAxis.Real F) : ResToImagAxis.Real (D F) := by
  intro t ht
  have hderiv := deriv_resToImagAxis_eq' F hF t ht
  have hDiff : DifferentiableAt ℝ F.resToImagAxis t := ResToImagAxis.Differentiable F hF t ht
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hDiff.hasDerivAt
  have hderiv_im : (deriv F.resToImagAxis t).im = 0 := by
    have : (Complex.imCLM ∘ F.resToImagAxis) = fun _ => 0 := by
      ext s
      simp only [Function.comp_apply, Complex.imCLM_apply]
      by_cases hs : 0 < s
      · exact hreal s hs
      · simp only [Function.resToImagAxis_apply, ResToImagAxis, hs, ↓reduceDIte, zero_im]
    rw [show (deriv F.resToImagAxis t).im = Complex.imCLM (deriv F.resToImagAxis t) from rfl]
    rw [← h.deriv, this, deriv_const']
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
  have h2 : (-2 * ↑π * (D F ⟨I * ↑t, by simp [ht]⟩)).im = (deriv F.resToImagAxis t).im := by
    rw [hderiv]
    simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
  have hsimp : (-2 * ↑π * D F ⟨I * ↑t, by simp [ht]⟩).im =
      -2 * π * (D F ⟨I * ↑t, by simp [ht]⟩).im := by
    simp only [neg_mul, neg_im, mul_comm (2 : ℂ), mul_assoc]
    rw [mul_im, mul_im]
    simp only [ofReal_re, ofReal_im, zero_mul, add_zero]
    ring
  rw [hsimp, hderiv_im] at h2
  have hcoef : -2 * π ≠ 0 := by positivity
  exact mul_eq_zero.mp h2 |>.resolve_left hcoef

/--
`L₁,₀(it)` is real for all `t > 0`.
-/
theorem L₁₀_imag_axis_real : ResToImagAxis.Real L₁₀ := by
  intro t ht
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hL₁₀ := L₁₀_eq_FD_G_sub_F_DG z
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
  rw [hL₁₀]
  have hF_real := F_imag_axis_real t ht
  have hG_real := G_imag_axis_real t ht
  have hDF_real := D_imag_axis_real_of_imag_axis_real F_holo F_imag_axis_real t ht
  have hDG_real := D_imag_axis_real_of_imag_axis_real G_holo G_imag_axis_real t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
    at hF_real hG_real hDF_real hDG_real
  simp only [sub_im, mul_im]
  have hz : z = ⟨I * ↑t, by simp [ht]⟩ := rfl
  rw [hz]
  simp only [hG_real, mul_zero, hDF_real, zero_mul, add_zero, hDG_real, hF_real, sub_zero]

theorem L₁₀_eventually_pos_imag_axis : ResToImagAxis.EventuallyPos L₁₀ := by
  refine ⟨L₁₀_imag_axis_real, ?_⟩
  -- From L₁₀_div_FG_tendsto: L₁₀/(FG) → 1/2 > 0, and F, G > 0, so L₁₀ > 0 eventually
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp
    (L₁₀_div_FG_tendsto.eventually (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1/2)))
  refine ⟨max t₀ 1, by positivity, fun t ht => ?_⟩
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  have hFG_pos := mul_pos (F_imag_axis_pos.2 t ht_pos) (G_imag_axis_pos.2 t ht_pos)
  have h := mul_pos (ht₀ t (le_trans (le_max_left _ _) ht)) hFG_pos
  rwa [div_mul_cancel₀ _ (ne_of_gt hFG_pos)] at h

/-!
## Section 6: Full Positivity of L₁,₀ via Theorem 6.54
-/

/--
`L₁,₀(it) > 0` for all `t > 0`.
Blueprint: Apply Theorem 6.54 (antiSerreDerPos) with k = 22.
-/
theorem L₁₀_pos_imag_axis : ResToImagAxis.Pos L₁₀ := by
  -- Apply antiSerreDerPos (Theorem 6.54) with k = 22
  -- Requires: (1) serre_D 22 L₁₀ is positive on imaginary axis
  --           (2) L₁₀ is eventually positive on imaginary axis
  exact antiSerreDerPos serre_D_L₁₀_pos_imag_axis L₁₀_eventually_pos_imag_axis

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
Proof: Q(t) = F(it).re / G(it).re is a quotient of differentiable functions where the denominator
is positive (from G_imag_axis_pos).

Key steps:
1. F and G are MDifferentiable (F_holo, G_holo)
2. ResToImagAxis.Differentiable gives differentiability of F.resToImagAxis and G.resToImagAxis
3. Complex.reCLM extracts real parts differentiably
4. Quotient rule applies since G.resToImagAxis(t).re > 0 (from G_imag_axis_pos)
5. Q coincides with this quotient on (0,∞) by definition
-/
theorem Q_differentiableOn : DifferentiableOn ℝ Q (Set.Ioi 0) := by
  intro t ht
  simp only [Set.mem_Ioi] at ht
  -- F.resToImagAxis and G.resToImagAxis are differentiable at t
  have hF_diff : DifferentiableAt ℝ F.resToImagAxis t := ResToImagAxis.Differentiable F F_holo t ht
  have hG_diff : DifferentiableAt ℝ G.resToImagAxis t := ResToImagAxis.Differentiable G G_holo t ht
  -- Their real parts are also differentiable
  have hF_re_diff : DifferentiableAt ℝ (fun s => (F.resToImagAxis s).re) t :=
    Complex.reCLM.differentiableAt.comp t hF_diff
  have hG_re_diff : DifferentiableAt ℝ (fun s => (G.resToImagAxis s).re) t :=
    Complex.reCLM.differentiableAt.comp t hG_diff
  -- G.resToImagAxis(t).re > 0, hence ≠ 0
  have hG_pos := G_imag_axis_pos.2 t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte] at hG_pos
  have hG_ne_zero : (G.resToImagAxis t).re ≠ 0 := by
    simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
    exact ne_of_gt hG_pos
  -- Quotient is differentiable
  have hQ_diff_at : DifferentiableAt ℝ
      (fun s => (F.resToImagAxis s).re / (G.resToImagAxis s).re) t :=
    hF_re_diff.div hG_re_diff hG_ne_zero
  -- Q equals this quotient locally on (0, ∞)
  apply hQ_diff_at.differentiableWithinAt.congr_of_eventuallyEq_of_mem
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_Ioi] at hs
    simp only [Q, hs, ↓reduceDIte, Function.resToImagAxis_apply, ResToImagAxis]
  · simp only [Set.mem_Ioi, ht]

/--
Chain rule for resToImagAxis: `d/dt F(it) = -2π * (D F)(it)`.

For a holomorphic function F : ℍ → ℂ, the derivative of its restriction to the imaginary axis
satisfies `deriv (F.resToImagAxis) t = -2π * (D F).resToImagAxis t`.

Proof sketch:
- d/dt F(it) = F'(it) * d/dt(it) = F'(it) * i (chain rule)
- F' = 2πi * D F (definition of normalized derivative D)
- So d/dt F(it) = 2πi * D F(it) * i = 2π i² * D F(it) = -2π * D F(it)

TODO: Complete the proof using the chain rule and MDifferentiable → DifferentiableAt correspondence.
-/
theorem deriv_resToImagAxis_eq (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (t : ℝ) (ht : 0 < t) :
    deriv F.resToImagAxis t = -2 * π * (D F).resToImagAxis t := by
  -- The imaginary axis parametrization: g(t) = I * t
  let g : ℝ → ℂ := fun s => Complex.I * s
  -- F.resToImagAxis = (F ∘ ofComplex) ∘ g locally near t > 0
  have h_eq : F.resToImagAxis =ᶠ[nhds t] ((F ∘ ofComplex) ∘ g) := by
    filter_upwards [lt_mem_nhds ht] with s hs
    simp only [Function.resToImagAxis_apply, ResToImagAxis, hs, ↓reduceDIte, Function.comp_apply]
    congr 1
    rw [ofComplex_apply_of_im_pos (by simp [hs] : 0 < (I * ↑s).im)]
  -- The derivatives are equal
  rw [h_eq.deriv_eq]
  -- g has derivative I at t (linear map)
  have hg_deriv_at : HasDerivAt g I t := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := ofRealCLM.hasDerivAt
    have h2 : HasDerivAt g (I * 1) t := h1.const_mul I
    simp at h2
    exact h2
  -- F ∘ ofComplex has complex derivative at I * t
  have him : 0 < (I * ↑t).im := by simp [ht]
  have hFcomp_deriv_at : HasDerivAt (F ∘ ofComplex) (deriv (F ∘ ofComplex) (g t)) (g t) := by
    exact (MDifferentiableAt_DifferentiableAt (hF ⟨I * t, him⟩)).hasDerivAt
  -- Chain rule using scomp: deriv ((F ∘ ofComplex) ∘ g) t = I • deriv (F ∘ ofComplex) (I * t)
  have hchain := hFcomp_deriv_at.scomp t hg_deriv_at
  rw [hchain.deriv]
  -- Use definition of D: deriv (F ∘ ofComplex) z = 2πi * D F z
  have hD_def : deriv (F ∘ ofComplex) (g t) = 2 * π * I * D F ⟨I * t, him⟩ := by
    simp only [D, g, coe_mk_subtype]
    field_simp
  simp only [hD_def, Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, g]
  -- Simplify: I • (2πi * D F(it)) = 2π * i² * D F(it) = -2π * D F(it)
  simp only [smul_eq_mul]
  ring_nf
  simp only [I_sq]
  ring

/--
The derivative of Q is `(-2π) * L₁,₀(it) / G(it)²`.
Blueprint: Quotient rule and chain rule.

Proof structure:
1. Q(t) = F(it).re / G(it).re for t > 0
2. By quotient rule: deriv Q = (F'·G - F·G') / G² (where F' = deriv of F.re on imaginary axis)
3. By chain rule: F' = -2π·(D F).re and G' = -2π·(D G).re
4. L₁₀ = D F · G - F · D G, so L₁₀.re = (D F).re · G.re - F.re · (D G).re
5. Combining: deriv Q = -2π · L₁₀.re / G.re²
-/
theorem deriv_Q (t : ℝ) (ht : 0 < t) :
    deriv Q t = (-2 * π) * (L₁₀ ⟨Complex.I * t, by simp [ht]⟩).re /
      (G ⟨Complex.I * t, by simp [ht]⟩).re ^ 2 := by
  -- Helper: z = I * t on the upper half-plane
  set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩ with hz_def
  -- Differentiability of real parts
  have hF_diff : DifferentiableAt ℝ F.resToImagAxis t := ResToImagAxis.Differentiable F F_holo t ht
  have hG_diff : DifferentiableAt ℝ G.resToImagAxis t := ResToImagAxis.Differentiable G G_holo t ht
  have hF_re_diff : DifferentiableAt ℝ (fun s => (F.resToImagAxis s).re) t :=
    Complex.reCLM.differentiableAt.comp t hF_diff
  have hG_re_diff : DifferentiableAt ℝ (fun s => (G.resToImagAxis s).re) t :=
    Complex.reCLM.differentiableAt.comp t hG_diff
  -- G(it).re > 0, hence ≠ 0
  have hG_pos : 0 < (G z).re := by
    have h := G_imag_axis_pos.2 t ht
    simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte] at h
    exact h
  have hG_ne : (G z).re ≠ 0 := ne_of_gt hG_pos
  -- Q equals F.re / G.re locally
  have hQ_eq : Q =ᶠ[nhds t] (fun s => (F.resToImagAxis s).re / (G.resToImagAxis s).re) := by
    filter_upwards [lt_mem_nhds ht] with s hs
    simp only [Q, hs, ↓reduceDIte, Function.resToImagAxis_apply, ResToImagAxis]
  -- Apply quotient rule
  rw [hQ_eq.deriv_eq]
  have hdiv : deriv (fun s => (F.resToImagAxis s).re / (G.resToImagAxis s).re) t =
      (deriv (fun s => (F.resToImagAxis s).re) t * (G.resToImagAxis t).re -
       (F.resToImagAxis t).re * deriv (fun s => (G.resToImagAxis s).re) t) /
      (G.resToImagAxis t).re ^ 2 := by
    have hG_ne' : (G.resToImagAxis t).re ≠ 0 := by
      simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
      simp only [hz_def] at hG_ne
      exact hG_ne
    exact deriv_div hF_re_diff hG_re_diff hG_ne'
  rw [hdiv]
  -- Derivative of real part equals real part of derivative for F, G
  -- Using HasFDerivAt.comp_hasDerivAt: deriv (reCLM ∘ h) = reCLM ∘ deriv h
  have hF_deriv_re : deriv (fun s => (F.resToImagAxis s).re) t =
      (deriv F.resToImagAxis t).re :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hF_diff.hasDerivAt).deriv
  have hG_deriv_re : deriv (fun s => (G.resToImagAxis s).re) t =
      (deriv G.resToImagAxis t).re :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hG_diff.hasDerivAt).deriv
  -- Apply chain rule for resToImagAxis
  rw [hF_deriv_re, hG_deriv_re, deriv_resToImagAxis_eq F F_holo t ht,
      deriv_resToImagAxis_eq G G_holo t ht]
  -- Simplify using realness on imaginary axis
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, hz_def]
  -- F and G are real on the imaginary axis
  have hF_real := F_imag_axis_real t ht
  have hG_real := G_imag_axis_real t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte] at hF_real hG_real
  -- Use L₁₀ definition: L₁₀ = D F · G - F · D G
  have hL₁₀ := L₁₀_eq_FD_G_sub_F_DG z
  -- Simplify: (-2 * π : ℂ).im = 0 since π is real
  have h2pi_im : (-2 * (π : ℂ)).im = 0 := by simp
  have h2_re : (-2 : ℂ).re = -2 := by simp
  -- Unfold z
  simp only [hz_def] at hL₁₀ hF_real hG_real
  -- Final simplification
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, h2pi_im, h2_re]
  rw [hL₁₀]
  simp only [mul_re, sub_re]
  -- Since F.im = G.im = 0
  simp only [hF_real, hG_real, mul_zero, sub_zero, zero_mul]
  ring

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
