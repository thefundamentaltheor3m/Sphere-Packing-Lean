module
public import SpherePacking.ModularForms.FG.Basic
import SpherePacking.ModularForms.DimensionFormulas
import SpherePacking.ForMathlib.ExpPiIMulMulI


/-!
# Positivity results for `F` and `G`

This file proves positivity statements on the imaginary axis for the key functions `F` and `G`,
and for the Serre derivative `SerreDer_22_L₁₀`.

## Main declarations
* `F_pos`, `G_pos`
* `SerreDer_22_L₁₀_pos`
-/


open scoped Real Manifold Topology ArithmeticFunction.sigma ModularForm MatrixGroups
open Filter Complex UpperHalfPlane ModularForm

-- Ensure the `SL(2,ℤ)` Möbius action on `ℍ` is available below.
noncomputable local instance : MulAction SL(2, ℤ) ℍ := UpperHalfPlane.SLAction (R := ℤ)

/-!
## Positivity on the imaginary axis
-/

/-- The function `F` is positive on the imaginary axis. -/
public lemma F_pos : ResToImagAxis.Pos F := by
  have hE2 : ResToImagAxis.Real E₂ := E₂_imag_axis_real
  have hE4 : ResToImagAxis.Real E₄.toFun := E₄_imag_axis_real
  have hE6 : ResToImagAxis.Real E₆.toFun := E₆_imag_axis_real
  have hbase : ResToImagAxis.Real (E₂ * E₄.toFun - E₆.toFun) :=
    ResToImagAxis.Real.sub (ResToImagAxis.Real.mul hE2 hE4) hE6
  refine ⟨?_, ?_⟩
  · simpa [F, pow_two] using ResToImagAxis.Real.mul hbase hbase
  · intro t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, F]
    set τ : UpperHalfPlane := ⟨Complex.I * t, by simp [ht]⟩
    set A : ℂ := A_E τ
    have hA_im : A.im = 0 := by
      simpa [A, A_E, τ, Function.resToImagAxis, ResToImagAxis, ht] using hbase t ht
    let term : ℕ+ → ℂ :=
      fun n => (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (τ : ℂ))
    have hseries : A = (720 : ℂ) * ∑' n : ℕ+, term n := by
      simpa [A, A_E, term, mul_assoc, mul_left_comm, mul_comm] using (E₂_mul_E₄_sub_E₆ τ)
    set r : ℝ := Real.exp (-2 * Real.pi * t) with hr
    have hτ : (τ : ℂ) = Complex.I * t := rfl
    have hIImul (x : ℂ) : Complex.I * (Complex.I * x) = -x := by simpa using I_mul_I_mul x
    have exp_neg_two_pi_mul_eq (n : ℕ) :
        Real.exp (-(2 * Real.pi * (n : ℝ) * t)) = r ^ n := by
      have hn : (-(2 * Real.pi * (n : ℝ) * t)) = (n : ℝ) * (-2 * Real.pi * t) := by ring
      calc
        Real.exp (-(2 * Real.pi * (n : ℝ) * t)) = Real.exp ((n : ℝ) * (-2 * Real.pi * t)) := by
          simp [hn]
        _ = Real.exp (-2 * Real.pi * t) ^ n := by
          simpa using (Real.exp_nat_mul (-2 * Real.pi * t) n)
        _ = r ^ n := by simp [hr]
    have hr_pos : 0 < r := by
      simpa [hr] using Real.exp_pos (-2 * Real.pi * t)
    have hr_lt_one : r < 1 := by
      have : (-2 * Real.pi * t) < 0 := by nlinarith [Real.pi_pos, ht]
      simpa [hr] using (Real.exp_lt_one_iff.2 this)
    have hr_norm : ‖r‖ < 1 := by
      simpa [Real.norm_of_nonneg hr_pos.le] using hr_lt_one
    have hsum_g : Summable (fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5 hr_norm
    have hsum_g' : Summable (fun n : ℕ+ => ((n : ℝ) ^ 5 : ℝ) * r ^ (n : ℕ)) := by
      have hf0 : ((0 : ℕ) : ℝ) ^ 5 * r ^ (0 : ℕ) = (0 : ℝ) := by simp
      exact (nat_pos_tsum2 (f := fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * r ^ n) hf0).2 hsum_g
    have hsum_term : Summable term := by
      refine Summable.of_norm_bounded (g := fun n : ℕ+ => ((n : ℝ) ^ 5 : ℝ) * r ^ (n : ℕ))
        hsum_g' ?_
      intro n
      have harg :
          (2 * π * Complex.I * (n : ℂ) * (τ : ℂ) : ℂ) =
            ((-(2 * Real.pi * (n : ℝ) * t) : ℝ) : ℂ) := by
        simp [hτ, mul_assoc, mul_left_comm, mul_comm, hIImul]
      have hnorm_exp : ‖cexp (2 * π * Complex.I * (n : ℂ) * (τ : ℂ))‖ = r ^ (n : ℕ) := by
        have hexp :
            cexp (2 * π * Complex.I * (n : ℂ) * (τ : ℂ)) =
              (Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℂ) := by
          rw [harg]
          simp
        -- Take norms.
        rw [hexp]
        -- `‖(a : ℂ)‖ = |a|` for `a : ℝ`, and `Real.exp _` is positive.
        have hnorm :
            ‖(Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℂ)‖ =
              Real.exp (-(2 * Real.pi * (n : ℝ) * t)) := by
          have h' :
              ‖(Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℂ)‖ =
                |Real.exp (-(2 * Real.pi * (n : ℝ) * t))| :=
            RCLike.norm_ofReal (K := ℂ) (Real.exp (-(2 * Real.pi * (n : ℝ) * t)))
          -- Rewrite the absolute value using positivity of `Real.exp`.
          rw [h']
          exact abs_of_nonneg (Real.exp_pos _).le
        -- Rewrite `Real.exp` in terms of `r ^ n`.
        rw [hnorm, exp_neg_two_pi_mul_eq (n : ℕ)]
      -- Bound the coefficient `n * σ 3 n` by `n^5`.
      have hσ : (σ 3 n : ℝ) ≤ (n : ℝ) ^ 4 := by
        exact_mod_cast (sigma_bound 3 (n : ℕ))
      have hcoeff :
          (n : ℝ) * (σ 3 n : ℝ) ≤ (n : ℝ) ^ 5 := by
        have hn0 : 0 ≤ (n : ℝ) := by positivity
        have := mul_le_mul_of_nonneg_left hσ hn0
        -- `n * n^4 = n^5`.
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using this
      -- Put the pieces together.
      calc
        ‖term n‖
            = ‖(n : ℂ) * (σ 3 n : ℂ)‖ * ‖cexp (2 * π * Complex.I * (n : ℂ) * (τ : ℂ))‖ := by
              simp [term, mul_assoc]
        _ ≤ ((n : ℝ) * (σ 3 n : ℝ)) * (r ^ (n : ℕ)) := by
              -- `‖(n : ℂ) * (σ 3 n : ℂ)‖ = (n : ℝ) * (σ 3 n : ℝ)`.
              have hN : ‖(n : ℂ) * (σ 3 n : ℂ)‖ = (n : ℝ) * (σ 3 n : ℝ) := by
                simp
              simp [hnorm_exp]
        _ ≤ ((n : ℝ) ^ 5 : ℝ) * r ^ (n : ℕ) := by
              gcongr
        _ = ((n : ℝ) ^ 5 : ℝ) * r ^ (n : ℕ) := by rfl
    have hsum_re : Summable (fun n : ℕ+ => (term n).re) := hsum_term.mapL Complex.reCLM
    have hterm_re (n : ℕ+) :
        (term n).re = (n : ℝ) * (σ 3 n : ℝ) * r ^ (n : ℕ) := by
      have harg :
          (2 * π * Complex.I * (n : ℂ) * (τ : ℂ) : ℂ) =
            ((-(2 * Real.pi * (n : ℝ) * t) : ℝ) : ℂ) := by
        simp [hτ, mul_assoc, mul_left_comm, mul_comm, hIImul]
      have hexp :
          cexp (2 * π * Complex.I * (n : ℂ) * (τ : ℂ)) =
            (Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℂ) := by
        rw [harg]
        simp
      -- Rewrite the exponential term as a real number in `ℂ`, then compute real parts.
      have hexp' :
          cexp (2 * π * Complex.I * (n : ℂ) * (τ : ℂ)) = (r ^ (n : ℕ) : ℂ) := by
        have : (Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℂ) = (r ^ (n : ℕ) : ℂ) := by
          exact_mod_cast exp_neg_two_pi_mul_eq (n : ℕ)
        exact hexp.trans this
      have hterm :
          term n = ((n : ℂ) * (σ 3 n : ℂ)) * (r ^ (n : ℕ) : ℂ) := by
        dsimp [term]
        rw [hexp']
      have hcoeff_re : ((n : ℂ) * (σ 3 n : ℂ)).re = (n : ℝ) * (σ 3 n : ℝ) := by
        simp [Complex.mul_re]
      have hcoeff_im : ((n : ℂ) * (σ 3 n : ℂ)).im = 0 := by
        simp [Complex.mul_im]
      have hr_re : ((r : ℂ) ^ (n : ℕ)).re = r ^ (n : ℕ) := by
        have hpow : ((r : ℂ) ^ (n : ℕ)) = ((r ^ (n : ℕ) : ℝ) : ℂ) := by
          simp
        rw [hpow]
        rfl
      have hr_im : ((r : ℂ) ^ (n : ℕ)).im = 0 := by
        have hpow : ((r : ℂ) ^ (n : ℕ)) = ((r ^ (n : ℕ) : ℝ) : ℂ) := by
          simp
        rw [hpow]
        rfl
      calc
        (term n).re = (((n : ℂ) * (σ 3 n : ℂ)) * (r ^ (n : ℕ) : ℂ)).re := by
          simp [hterm]
        _ = ((n : ℂ) * (σ 3 n : ℂ)).re * ((r ^ (n : ℕ) : ℂ)).re
              - ((n : ℂ) * (σ 3 n : ℂ)).im * ((r ^ (n : ℕ) : ℂ)).im := by
          simp [Complex.mul_re]
        _ = (n : ℝ) * (σ 3 n : ℝ) * r ^ (n : ℕ) := by
          simp [hcoeff_re, hcoeff_im, hr_re, hr_im, mul_left_comm, mul_comm]
    have hterm_nonneg (n : ℕ+) : 0 ≤ (term n).re := by
      rw [hterm_re]
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)
    have hterm_pos1 : 0 < (term 1).re := by
      rw [hterm_re]
      have hσ : 0 < (σ 3 (1 : ℕ+) : ℝ) := by
        have : (0 : ℕ) < σ 3 (1 : ℕ) := by
          simp
        exact_mod_cast this
      have : 0 < r ^ (1 : ℕ) := by
        simpa using pow_pos hr_pos 1
      exact mul_pos (mul_pos (by norm_num) hσ) this
    have htsum_pos : 0 < ∑' n : ℕ+, (term n).re :=
      hsum_re.tsum_pos hterm_nonneg 1 hterm_pos1
    have hA_re : A.re = 720 * ∑' n : ℕ+, (term n).re := by
      have h := congrArg Complex.re hseries
      -- `re` commutes with `tsum`.
      have hre_tsum : (∑' n : ℕ+, term n).re = ∑' n : ℕ+, (term n).re := by
        simpa using (Complex.reCLM.map_tsum hsum_term)
      -- Simplify `re` of the scalar multiplication by `720`.
      simpa [hre_tsum, Complex.mul_re, mul_assoc] using h
    have hA_pos : 0 < A.re := by
      rw [hA_re]
      have : (0 : ℝ) < (720 : ℝ) := by norm_num
      exact mul_pos this htsum_pos
    -- Finally, `F(it) = A(it)^2` has positive real part.
    have hF_re : (A ^ 2).re = A.re ^ 2 := by
      simp [pow_two, Complex.mul_re, hA_im]
    have hposA : 0 < (A ^ 2).re := by
      rw [hF_re]
      exact pow_pos hA_pos 2
    simpa [A] using hposA

/-- The function `G` is positive on the imaginary axis. -/
public lemma G_pos : ResToImagAxis.Pos G := by
  have hH2 : ResToImagAxis.Pos H₂ := H₂_imag_axis_pos
  have hH4 : ResToImagAxis.Pos H₄ := H₄_imag_axis_pos
  have hconst {c : ℝ} (hc : 0 < c) : ResToImagAxis.Pos (fun _ : ℍ => (c : ℂ)) := by
    refine ⟨?_, ?_⟩ <;> intro t ht <;> simp [Function.resToImagAxis, ResToImagAxis, ht, hc]
  have hH2sq : ResToImagAxis.Pos (H₂ ^ 2) := by
    simpa [pow_two] using ResToImagAxis.Pos.mul hH2 hH2
  have hH2cube : ResToImagAxis.Pos (H₂ ^ 3) := by
    simpa [pow_succ, pow_two, Nat.succ_eq_add_one, mul_assoc] using ResToImagAxis.Pos.mul hH2sq hH2
  have hH4sq : ResToImagAxis.Pos (H₄ ^ 2) := by
    simpa [pow_two] using ResToImagAxis.Pos.mul hH4 hH4
  have hpoly : ResToImagAxis.Pos (2 * H₂ ^ 2 + 5 * H₂ * H₄ + 5 * H₄ ^ 2) := by
    have h1 : ResToImagAxis.Pos (2 * H₂ ^ 2) :=
      by simpa [mul_assoc] using ResToImagAxis.Pos.mul (hconst (c := 2) (by positivity)) hH2sq
    have h2 : ResToImagAxis.Pos (5 * H₂ * H₄) := by
      have h :=
        ResToImagAxis.Pos.mul (hconst (c := 5) (by positivity)) (ResToImagAxis.Pos.mul hH2 hH4)
      simpa [mul_assoc] using h
    have h3 : ResToImagAxis.Pos (5 * H₄ ^ 2) :=
      by simpa [mul_assoc] using ResToImagAxis.Pos.mul (hconst (c := 5) (by positivity)) hH4sq
    simpa [add_assoc] using ResToImagAxis.Pos.add (ResToImagAxis.Pos.add h1 h2) h3
  simpa [G, mul_assoc] using ResToImagAxis.Pos.mul hH2cube hpoly

/-- q-expansion of `E₂` in sigma form: `E₂(z) = 1 - 24 * ∑ σ₁(n) q^n`. -/
public lemma E₂_eq_sigma_qexp (z : UpperHalfPlane) :
    E₂ z =
      1 - 24 * ∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
  have hE := E₂_eq z
  have hLambert :
      (∑' n : ℕ+,
          (n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) /
            (1 - cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)))) =
        ∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
    have hNat :
        (∑' n : ℕ,
            ((n + 1 : ℕ) : ℂ) * cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)) /
              (1 - cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)))) =
          ∑' n : ℕ, (σ 1 (n + 1) : ℂ) * cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)) := by
      simpa using (tsum_eq_tsum_sigma z)
    simpa using
      (tsum_pnat_eq_tsum_succ3 (f := fun n : ℕ =>
        (n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) /
          (1 - cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))))).trans
        (hNat.trans
          (tsum_pnat_eq_tsum_succ3 (f := fun n : ℕ =>
            (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)))).symm)
  simpa [hLambert] using hE

/-- A `ℕ`-indexed q-expansion of `E₂` (including the constant term). -/
public lemma E₂_eq_qexp (z : UpperHalfPlane) :
    E₂ z =
      ∑' n : ℕ,
        (if n = 0 then (1 : ℂ) else (-24 : ℂ) * (σ 1 n : ℂ)) *
          cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
  -- First rewrite `E₂` as `1 - 24 * ∑_{n≥1} σ₁(n) q^n`.
  have hEσ := E₂_eq_sigma_qexp z
  -- Now express the RHS as a single `ℕ`-indexed tsum by splitting off the `n = 0` term.
  let a : ℕ → ℂ := fun n => (if n = 0 then (1 : ℂ) else (-24 : ℂ) * (σ 1 n : ℂ))
  have hsum :
      Summable (fun n : ℕ => a n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))) := by
    -- Bound the coefficients by a polynomial times a geometric sequence.
    set r : ℝ := ‖cexp (2 * π * Complex.I * (z : ℂ))‖ with hr
    have hr_nonneg : 0 ≤ r := by simp [hr]
    have hr_norm : ‖r‖ < 1 := by
      have hr_lt_one : r < 1 := by simpa [hr] using exp_upperHalfPlane_lt_one z
      simpa [Real.norm_eq_abs, abs_of_nonneg hr_nonneg] using hr_lt_one
    have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2 : ℝ) * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr_norm
    -- Use the bound `σ₁(n) ≤ n^2`.
    have hσ (n : ℕ) : (σ 1 n : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (sigma_bound 1 n)
    -- Build a global bound (also valid at `n = 0`).
    have hbound :
        ∀ n : ℕ, ‖a n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))‖ ≤
          1 * r ^ n + (24 : ℝ) * ((n : ℝ) ^ 2 * r ^ n) := by
      intro n
      by_cases hn : n = 0
      · subst hn
        simp [a, r]
      · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
        have hqpow :
            ‖cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))‖ = r ^ n := by
          -- `exp(2πinz) = (exp(2πiz))^n`
          have hexp :
              cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) =
                cexp (2 * π * Complex.I * (z : ℂ)) ^ n := by
            -- Rewrite `exp(2π i n z)` as `(exp(2π i z))^n`.
            simpa using (exp_aux z n)
          simp [r, hr, hexp, norm_pow]
        have ha_norm :
            ‖a n‖ ≤ (24 : ℝ) * (n : ℝ) ^ 2 := by
          -- For `n ≠ 0`, `a n = -24 * σ₁(n)`.
          have : a n = (-24 : ℂ) * (σ 1 n : ℂ) := by simp [a, hn]
          -- Convert norms to reals and apply `σ₁(n) ≤ n^2`.
          calc
            ‖a n‖ = ‖(-24 : ℂ) * (σ 1 n : ℂ)‖ := by simp [this]
            _ = ‖(-24 : ℂ)‖ * ‖(σ 1 n : ℂ)‖ := by simp
            _ ≤ (24 : ℝ) * (n : ℝ) ^ 2 := by
              have hσnorm : ‖(σ 1 n : ℂ)‖ = (σ 1 n : ℝ) := by simp
              have h24 : ‖(-24 : ℂ)‖ = (24 : ℝ) := by norm_num
              have hσ' : (24 : ℝ) * (σ 1 n : ℝ) ≤ (24 : ℝ) * (n : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_left (hσ n) (by positivity)
              simpa [h24, hσnorm, mul_assoc, mul_left_comm, mul_comm] using hσ'
        -- Bound the term using `‖a n‖ ≤ 24*n^2` and `‖exp(...)‖ = r^n`.
        calc
          ‖a n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))‖
              = ‖a n‖ * ‖cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))‖ := by
                  simp
          _ ≤ ((24 : ℝ) * (n : ℝ) ^ 2) * ‖cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))‖ := by
                  exact mul_le_mul_of_nonneg_right ha_norm (norm_nonneg _)
          _ = ((24 : ℝ) * (n : ℝ) ^ 2) * (r ^ n) := by simp [hqpow]
          _ ≤ 1 * r ^ n + (24 : ℝ) * ((n : ℝ) ^ 2 * r ^ n) := by
                  nlinarith [hr_nonneg, pow_nonneg hr_nonneg n]
    -- Summability follows from the bound by a sum of two summable series.
    have hs1 : Summable (fun n : ℕ => (1 : ℝ) * r ^ n) :=
      (summable_geometric_of_norm_lt_one hr_norm).mul_left 1
    have hs2 : Summable (fun n : ℕ => (24 : ℝ) * ((n : ℝ) ^ 2 * r ^ n)) :=
      hs.mul_left 24
    refine Summable.of_norm_bounded (g := fun n : ℕ =>
      (1 : ℝ) * r ^ n + (24 : ℝ) * ((n : ℝ) ^ 2 * r ^ n))
      (hs1.add hs2) (fun n => hbound n)
  have htsum_split :
      (∑' n : ℕ, a n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))) =
        (a 0 * cexp (2 * π * Complex.I * (0 : ℂ) * (z : ℂ))) +
          ∑' n : ℕ, ite (n = 0) 0 (a n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))) := by
    simpa using (hsum.tsum_eq_add_tsum_ite (b := 0))
  -- Identify the split pieces and rewrite the complement sum as an `ℕ+`-indexed sum.
  have hcompl :
      (∑' n : ℕ, ite (n = 0) 0 (a n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)))) =
        (-24 : ℂ) * ∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
    -- Convert the `ℕ`-indexed sum with a zero term into an `ℕ+`-indexed sum.
    have hpnat :
        (∑' n : ℕ, ite (n = 0) 0 (a n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)))) =
          ∑' n : ℕ+,
            ite ((n : ℕ) = 0) 0
              (a (n : ℕ) * cexp (2 * π * Complex.I * ((n : ℕ) : ℂ) * (z : ℂ))) := by
      -- Use `tsum_pNat` with a function that vanishes at `0`.
      have :
          (fun n : ℕ => ite (n = 0) 0 (a n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)))) 0 =
            0 := by
        simp
      simpa using (tsum_pNat
        (f := fun n : ℕ => ite (n = 0) 0 (a n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))))
        (hf := this)).symm
    -- Simplify the `ite` on `ℕ+` and factor out `-24`.
    rw [hpnat]
    -- The `ite` is always false on `ℕ+`.
    have hite :
        (fun n : ℕ+ =>
            ite ((n : ℕ) = 0) 0
              (a (n : ℕ) * cexp (2 * π * Complex.I * ((n : ℕ) : ℂ) * (z : ℂ)))) =
          fun n : ℕ+ => (-24 : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
      funext n
      have hn0 : (n : ℕ) ≠ 0 := Nat.ne_of_gt n.pos
      simp [a, hn0, mul_assoc]
    -- Turn the pointwise equality `hite` into an equality of sums, then factor out `-24`.
    have hsum' :
        (∑' n : ℕ+,
            ite ((n : ℕ) = 0) 0
              (a (n : ℕ) * cexp (2 * π * Complex.I * ((n : ℕ) : ℂ) * (z : ℂ)))) =
          ∑' n : ℕ+, (-24 : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
      simpa using congrArg (fun f : ℕ+ → ℂ => ∑' n : ℕ+, f n) hite
    rw [hsum']
    -- Rewrite the summand as `(-24) * (...)` and apply `tsum_mul_left`.
    simpa [mul_assoc] using
      (tsum_mul_left (a := (-24 : ℂ))
        (f := fun n : ℕ+ => (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))))
  -- Assemble everything.
  -- `a 0 * exp(0) = 1`.
  have ha0 : a 0 * cexp (2 * π * Complex.I * (0 : ℂ) * (z : ℂ)) = (1 : ℂ) := by
    simp [a]
  -- Substitute into the sigma q-expansion.
  calc
    E₂ z = 1 - 24 * ∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := hEσ
    _ = (a 0 * cexp (2 * π * Complex.I * (0 : ℂ) * (z : ℂ))) +
          (-24 : ℂ) * ∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
          simp [a, sub_eq_add_neg, mul_assoc]
    _ = (∑' n : ℕ, a n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))) := by
          -- Use the split formula and `hcompl`.
          simp [htsum_split, hcompl]

lemma cexp_two_pi_I_nat_mul_I_mul (t : ℝ) (n : ℕ) :
    cexp (2 * π * Complex.I * n * (Complex.I * t)) = (rexp (-(2 * π * n * t)) : ℂ) := by
  ring_nf; simp

lemma negDE₂_pos : ResToImagAxis.Pos negDE₂ := by
  -- We use the q-expansion of `E₂` together with termwise differentiation of q-series.
  let a : ℕ → ℂ := fun n => if n = 0 then (1 : ℂ) else (-24 : ℂ) * (σ 1 n : ℂ)
  have hE2fun :
      (E₂ : UpperHalfPlane → ℂ) =
        fun z : UpperHalfPlane =>
          ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
    funext z
    simpa [a, mul_assoc] using (E₂_eq_qexp z)
  -- Derivative bounds on compact subsets of the upper half-plane for this q-series.
  have hsum_deriv :
      ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
        ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K),
          ‖a n * (2 * π * Complex.I * n) * cexp (2 * π * Complex.I * n * k.1)‖ ≤ u n := by
    intro K hK hKc
    have him_cont : ContinuousOn (fun w : ℂ => w.im) K := Complex.continuous_im.continuousOn
    have him_pos : ∀ z ∈ K, (0 : ℝ) < z.im := fun z hz => hK hz
    obtain ⟨δ, hδ_pos, hδ_le⟩ :=
      IsCompact.exists_forall_le' (s := K) hKc him_cont (a := (0 : ℝ)) him_pos
    let r : ℝ := Real.exp (-2 * Real.pi * δ)
    have hr_norm : ‖r‖ < 1 := by
      have hr_nonneg : 0 ≤ r := by simpa [r] using (Real.exp_pos (-2 * Real.pi * δ)).le
      have hr_lt_one : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, hδ_pos])
      simpa [Real.norm_of_nonneg hr_nonneg] using hr_lt_one
    let u : ℕ → ℝ := fun n => (48 * Real.pi) * (((n : ℝ) ^ 3 : ℝ) * r ^ n)
    have hu : Summable u := by
      have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 3 : ℝ) * r ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hr_norm
      exact hs.mul_left (48 * Real.pi)
    refine ⟨u, hu, ?_⟩
    intro n k
    by_cases hn0 : n = 0
    · subst hn0
      simp [a, u]
    have hk_im : δ ≤ k.1.im := hδ_le k.1 k.2
    have hnorm_exp :
        ‖cexp (2 * π * Complex.I * (n : ℂ) * k.1)‖ ≤ r ^ n := by
      simpa [r] using
        (SpherePacking.ForMathlib.norm_cexp_two_pi_I_mul_nat_mul_le_pow_of_le_im
          (n := n) (δ := δ) (z := k.1) hk_im)
    have hσ : (σ 1 n : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (sigma_bound 1 n)
    have ha_norm : ‖a n‖ ≤ (24 : ℝ) * (n : ℝ) ^ 2 := by
      have : a n = (-24 : ℂ) * (σ 1 n : ℂ) := by simp [a, hn0]
      have hσnorm : ‖(σ 1 n : ℂ)‖ = (σ 1 n : ℝ) := by simp
      have h24 : ‖(-24 : ℂ)‖ = (24 : ℝ) := by norm_num
      calc
        ‖a n‖ = ‖(-24 : ℂ) * (σ 1 n : ℂ)‖ := by simp [this]
        _ = ‖(-24 : ℂ)‖ * ‖(σ 1 n : ℂ)‖ := by simp
        _ ≤ (24 : ℝ) * (n : ℝ) ^ 2 := by
          -- Use `σ₁(n) ≤ n^2`.
          have : ‖(-24 : ℂ)‖ * ‖(σ 1 n : ℂ)‖ = (24 : ℝ) * (σ 1 n : ℝ) := by
            simp [h24]
          -- Multiply the bound `σ₁(n) ≤ n^2` by the positive constant `24`.
          have hσ' : (24 : ℝ) * (σ 1 n : ℝ) ≤ (24 : ℝ) * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hσ (by positivity)
          simpa [this] using hσ'
    have hnorm_2pin : ‖(2 * π * Complex.I * (n : ℂ) : ℂ)‖ = 2 * Real.pi * (n : ℝ) := by
      simp [Real.norm_of_nonneg Real.pi_pos.le, mul_left_comm, mul_comm]
    calc
      ‖a n * (2 * π * Complex.I * n) * cexp (2 * π * Complex.I * n * k.1)‖
          = ‖a n‖ * ‖(2 * π * Complex.I * (n : ℂ) : ℂ)‖ *
              ‖cexp (2 * π * Complex.I * (n : ℂ) * k.1)‖ := by
                simp [mul_assoc]
      _ ≤ ((24 : ℝ) * (n : ℝ) ^ 2) * (2 * Real.pi * (n : ℝ)) * (r ^ n) := by
            gcongr
            · simpa [hnorm_2pin] using (le_of_eq hnorm_2pin)
      _ ≤ u n := by
            have hA :
                ((24 : ℝ) * (n : ℝ) ^ 2) * (2 * Real.pi * (n : ℝ)) =
                  (48 * Real.pi) * ((n : ℝ) ^ 3) := by ring_nf
            have hA' := congrArg (fun x : ℝ => x * (r ^ n)) hA
            -- `u n = (48π) * (n^3 * r^n)`.
            have hu' : (48 * Real.pi) * ((n : ℝ) ^ 3) * (r ^ n) = u n := by
              simp [u, mul_assoc, mul_left_comm, mul_comm]
            exact le_of_eq (by simpa [mul_assoc] using (hA'.trans hu'))
  have hneg (τ : UpperHalfPlane) :
      negDE₂ τ =
        ∑' n : ℕ, (24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * n * τ) := by
    have hD :
        D E₂ τ =
          ∑' n : ℕ, (n : ℂ) * a n * cexp (2 * π * Complex.I * n * τ) := by
      have hD' := D_qexp_tsum a τ hsum_deriv
      simpa [hE2fun] using hD'
    have hterm (n : ℕ) :
        -((n : ℂ) * a n * cexp (2 * π * Complex.I * n * τ)) =
          (24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * n * τ) := by
      by_cases hn : n = 0
      · subst hn; simp [a]
      · have ha : a n = (-24 : ℂ) * (σ 1 n : ℂ) := by simp [a, hn]
        rw [ha]
        ring
    have hnegDE₂ : negDE₂ τ = -(D E₂ τ) := by simp [negDE₂, Pi.neg_apply]
    calc
      negDE₂ τ = -(D E₂ τ) := hnegDE₂
      _ = -(∑' n : ℕ, (n : ℂ) * a n * cexp (2 * π * Complex.I * n * τ)) := by rw [hD]
      _ = ∑' n : ℕ, -((n : ℂ) * a n * cexp (2 * π * Complex.I * n * τ)) := by
            simpa using
              (tsum_neg (f := fun n : ℕ => (n : ℂ) * a n * cexp (2 * π * Complex.I * n * τ))).symm
      _ = ∑' n : ℕ, (24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * n * τ) := by
            refine tsum_congr ?_
            intro n
            exact hterm n
  have hsum_term (τ : UpperHalfPlane) :
      Summable (fun n : ℕ =>
        (24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * n * τ)) := by
    set r : ℝ := ‖cexp (2 * π * Complex.I * τ)‖ with hr
    have hr_nonneg : 0 ≤ r := norm_nonneg _
    have hr_lt_one : r < 1 := by
      simpa [r, hr] using (exp_upperHalfPlane_lt_one τ)
    have hr_norm : ‖(r : ℝ)‖ < 1 := by
      simpa [Real.norm_of_nonneg hr_nonneg] using hr_lt_one
    have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 3 : ℝ) * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hr_norm
    have hσ (n : ℕ) : (σ 1 n : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (sigma_bound 1 n)
    have hbound :
        ∀ n : ℕ, ‖(24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * n * τ)‖ ≤
          (24 : ℝ) * ((n : ℝ) ^ 3 * r ^ n) := by
      intro n
      by_cases hn : n = 0
      · subst hn; simp [r]
      · have hqpow :
            ‖cexp (2 * π * Complex.I * n * τ)‖ = r ^ n := by
          have hexp :
              cexp (2 * π * Complex.I * n * τ) = cexp (2 * π * Complex.I * τ) ^ n := by
            simpa using (exp_aux τ n)
          simp [r, hr, hexp, norm_pow]
        have hσ' : (σ 1 n : ℝ) ≤ (n : ℝ) ^ 2 := hσ n
        calc
          ‖(24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * n * τ)‖
              = (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * ‖cexp (2 * π * Complex.I * n * τ)‖ := by
                  have h1 :
                      ‖(24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * n * τ)‖ =
                        ‖(24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ)‖ *
                          ‖cexp (2 * π * Complex.I * n * τ)‖ := by
                    simp [mul_assoc]
                  calc
                    ‖(24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * n * τ)‖ =
                        ‖(24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ)‖ *
                          ‖cexp (2 * π * Complex.I * n * τ)‖ := h1
                    _ = ((24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ)) *
                          ‖cexp (2 * π * Complex.I * n * τ)‖ := by
                          simp [mul_assoc, mul_comm]
                    _ = (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) *
                          ‖cexp (2 * π * Complex.I * n * τ)‖ := by
                          simp [mul_assoc]
          _ = (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * (r ^ n) := by simp [hqpow]
          _ ≤ (24 : ℝ) * ((n : ℝ) ^ 3 * r ^ n) := by
                have hn0 : 0 ≤ (n : ℝ) := by positivity
                have hrn : 0 ≤ r ^ n := pow_nonneg hr_nonneg _
                have hσmul :
                    (n : ℝ) * (σ 1 n : ℝ) ≤ (n : ℝ) * (n : ℝ) ^ 2 :=
                  mul_le_mul_of_nonneg_left hσ' hn0
                have hσmul' :
                    (n : ℝ) * (σ 1 n : ℝ) * (r ^ n) ≤ (n : ℝ) * (n : ℝ) ^ 2 * (r ^ n) :=
                  mul_le_mul_of_nonneg_right hσmul hrn
                have hσmul'' :
                    (24 : ℝ) * ((n : ℝ) * (σ 1 n : ℝ) * (r ^ n)) ≤
                      (24 : ℝ) * ((n : ℝ) * (n : ℝ) ^ 2 * (r ^ n)) :=
                  mul_le_mul_of_nonneg_left hσmul' (by norm_num)
                have hn3 : (n : ℝ) * (n : ℝ) ^ 2 = (n : ℝ) ^ 3 := by
                  simp [pow_succ, mul_comm]
                simpa [mul_assoc, hn3, pow_succ] using hσmul''
    refine Summable.of_norm_bounded (g := fun n : ℕ => (24 : ℝ) * ((n : ℝ) ^ 3 * r ^ n))
      (hs.mul_left 24) (fun n => hbound n)
  refine ⟨?_, ?_⟩
  · intro t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
    set τ : UpperHalfPlane := ⟨Complex.I * t, by simp [ht]⟩
    rw [hneg τ, im_tsum (hsum_term τ)]
    have hterm_im (n : ℕ) :
        ((24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * n * τ)).im = 0 := by
      have hq :
          cexp (2 * π * Complex.I * n * τ) = (rexp (-(2 * π * n * t)) : ℂ) := by
        simpa [τ] using (cexp_two_pi_I_nat_mul_I_mul (t := t) (n := n))
      rw [hq]
      set x : ℂ := (24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ)
      set y : ℂ := (rexp (-(2 * π * n * t)) : ℂ)
      have hx : x.im = 0 := by simp [x]
      have hy : y.im = 0 := by
        simpa [y] using (Complex.ofReal_im (rexp (-(2 * π * n * t))))
      have : (x * y).im = 0 := by simp [Complex.mul_im, hx, hy]
      simpa [x, y, mul_assoc] using this
    have hsum_im :
        (∑' n : ℕ,
            ((24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * n * τ)).im) = 0 := by
      calc
        (∑' n : ℕ,
            ((24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * n * τ)).im) =
            ∑' _n : ℕ, (0 : ℝ) := by
              refine tsum_congr ?_
              intro n
              simpa using hterm_im n
        _ = 0 := by simp
    simpa using hsum_im
  · intro t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
    set τ : UpperHalfPlane := ⟨Complex.I * t, by simp [ht]⟩
    -- Compute termwise real parts: on the imaginary axis the exponential is real and positive.
    have hterm_re (n : ℕ) :
        ((24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * n * τ)).re =
          (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * Real.exp (-2 * Real.pi * (n : ℝ) * t) := by
      have hq :
          cexp (2 * π * Complex.I * n * τ) = (rexp (-(2 * π * n * t)) : ℂ) := by
        simpa [τ] using (cexp_two_pi_I_nat_mul_I_mul (t := t) (n := n))
      have harg : (-(2 * π * n * t)) = (-2 * Real.pi * (n : ℝ) * t) := by ring
      rw [hq]
      set x : ℂ := (24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ)
      set y : ℂ := (rexp (-(2 * π * n * t)) : ℂ)
      have hx : x.im = 0 := by simp [x]
      have hy : y.im = 0 := by
        simpa [y] using (Complex.ofReal_im (rexp (-(2 * π * n * t))))
      have hxre : x.re = (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) := by
        simp [x, mul_assoc, mul_comm, mul_left_comm]
      have hyre : y.re = rexp (-(2 * π * n * t)) := by
        simpa [y] using (Complex.ofReal_re (rexp (-(2 * π * n * t))))
      have : (x * y).re = (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * rexp (-(2 * π * n * t)) := by
        simp [Complex.mul_re, hx, hy, hxre, hyre, mul_assoc, mul_comm, mul_left_comm]
      simpa [x, y, mul_assoc, harg] using this
    have hsumRe :
        Summable (fun n : ℕ =>
          (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * Real.exp (-2 * Real.pi * (n : ℝ) * t)) := by
      -- Bound by `n^3 * r^n` with `r = exp(-2πt)`.
      set r : ℝ := Real.exp (-2 * Real.pi * t)
      have hr_nonneg : 0 ≤ r := (Real.exp_pos _).le
      have hr_lt_one : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, ht])
      have hr_norm : ‖(r : ℝ)‖ < 1 := by
        simpa [Real.norm_of_nonneg hr_nonneg] using hr_lt_one
      have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 3 : ℝ) * r ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hr_norm
      have hσ (n : ℕ) : (σ 1 n : ℝ) ≤ (n : ℝ) ^ 2 := by
        exact_mod_cast (sigma_bound 1 n)
      have hbound :
          ∀ n : ℕ,
            ‖(24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * Real.exp (-2 * Real.pi * (n : ℝ) * t)‖ ≤
              (24 : ℝ) * ((n : ℝ) ^ 3 * r ^ n) := by
        intro n
        by_cases hn : n = 0
        · subst hn
          simp [r]
        · have hexp :
              Real.exp (-2 * Real.pi * (n : ℝ) * t) = r ^ n := by
            -- `exp(-2πnt) = (exp(-2πt))^n`.
            have hmul : (-2 * Real.pi * (n : ℝ) * t) = n * (-2 * Real.pi * t) := by
              calc
                (-2 * Real.pi * (n : ℝ) * t) = (n : ℝ) * (-2 * Real.pi * t) := by ring
                _ = n * (-2 * Real.pi * t) := by simp
            calc
              Real.exp (-2 * Real.pi * (n : ℝ) * t) = Real.exp (n * (-2 * Real.pi * t)) := by
                rw [hmul]
              _ = Real.exp (-2 * Real.pi * t) ^ n := by
                simpa using (Real.exp_nat_mul (-2 * Real.pi * t) n)
              _ = r ^ n := by simp [r]
          have hn0 : 0 ≤ (n : ℝ) := by positivity
          have hrn : 0 ≤ r ^ n := pow_nonneg hr_nonneg _
          have hσ' : (σ 1 n : ℝ) ≤ (n : ℝ) ^ 2 := hσ n
          -- For real terms, `‖x‖ = |x|`, and everything is nonnegative.
          have hx_nonneg :
              0 ≤ (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * Real.exp (-2 * Real.pi * (n : ℝ) * t) := by
            have h24 : 0 ≤ (24 : ℝ) := by norm_num
            have hn0 : 0 ≤ (n : ℝ) := by positivity
            have hσ0 : 0 ≤ (σ 1 n : ℝ) := by exact_mod_cast (Nat.zero_le _)
            have hexp0 : 0 ≤ Real.exp (-2 * Real.pi * (n : ℝ) * t) := (Real.exp_pos _).le
            -- Product of nonnegative terms.
            have : 0 ≤ (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) :=
              mul_nonneg (mul_nonneg h24 hn0) hσ0
            exact mul_nonneg this hexp0
          rw [Real.norm_of_nonneg hx_nonneg]
          -- Replace the exponential by `r ^ n`.
          rw [hexp]
          -- Reduce to `σ₁(n) ≤ n^2` and multiply by nonnegative factors.
          have hσmul :
              (n : ℝ) * (σ 1 n : ℝ) ≤ (n : ℝ) * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hσ' hn0
          have hσmul' :
              (n : ℝ) * (σ 1 n : ℝ) * (r ^ n) ≤ (n : ℝ) * (n : ℝ) ^ 2 * (r ^ n) :=
            mul_le_mul_of_nonneg_right hσmul hrn
          have hσmul'' :
              (24 : ℝ) * ((n : ℝ) * (σ 1 n : ℝ) * (r ^ n)) ≤
                (24 : ℝ) * ((n : ℝ) * (n : ℝ) ^ 2 * (r ^ n)) :=
            mul_le_mul_of_nonneg_left hσmul' (by norm_num)
          have hn3 : (n : ℝ) * (n : ℝ) ^ 2 = (n : ℝ) ^ 3 := by
            simp [pow_succ, mul_comm]
          -- Rewrite `n * n^2` as `n^3` and reassociate.
          have hineq :
              (24 : ℝ) * ((n : ℝ) * (σ 1 n : ℝ) * (r ^ n)) ≤
                (24 : ℝ) * ((n : ℝ) ^ 3 * (r ^ n)) := by
            calc
              (24 : ℝ) * ((n : ℝ) * (σ 1 n : ℝ) * (r ^ n)) ≤
                  (24 : ℝ) * ((n : ℝ) * (n : ℝ) ^ 2 * (r ^ n)) := hσmul''
              _ = (24 : ℝ) * ((n : ℝ) ^ 3 * (r ^ n)) := by
                    simp [hn3]
          simpa [mul_assoc] using hineq
      refine Summable.of_norm_bounded (g := fun n : ℕ => (24 : ℝ) * ((n : ℝ) ^ 3 * r ^ n))
        (hs.mul_left 24) (fun n => hbound n)
    have hpos :
        0 < ∑' n : ℕ,
          (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * Real.exp (-2 * Real.pi * (n : ℝ) * t) := by
      have hnonneg (n : ℕ) :
          0 ≤ (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * Real.exp (-2 * Real.pi * (n : ℝ) * t) := by
        have h24 : 0 ≤ (24 : ℝ) := by norm_num
        have hn0 : 0 ≤ (n : ℝ) := by positivity
        have hσ0 : 0 ≤ (σ 1 n : ℝ) := by exact_mod_cast (Nat.zero_le _)
        have hexp0 : 0 ≤ Real.exp (-2 * Real.pi * (n : ℝ) * t) := (Real.exp_pos _).le
        have : 0 ≤ (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) :=
          mul_nonneg (mul_nonneg h24 hn0) hσ0
        exact mul_nonneg this hexp0
      have hpos1 :
          0 <
            (24 : ℝ) * ((1 : ℕ) : ℝ) * (σ 1 1 : ℝ) *
            Real.exp (-2 * Real.pi * ((1 : ℕ) : ℝ) * t) := by
        have hσ11 : (σ 1 1 : ℝ) = 1 := by
          norm_cast
        have h24 : (0 : ℝ) < 24 := by norm_num
        have hone : (0 : ℝ) < ((1 : ℕ) : ℝ) := by norm_num
        have hσpos : (0 : ℝ) < (σ 1 1 : ℝ) := by simp
        have hexp : 0 < Real.exp (-2 * Real.pi * ((1 : ℕ) : ℝ) * t) := Real.exp_pos _
        -- A product of positive terms is positive.
        simpa [mul_assoc] using (mul_pos (mul_pos (mul_pos h24 hone) hσpos) hexp)
      -- One strictly positive term implies the whole sum is positive.
      simpa using hsumRe.tsum_pos hnonneg 1 hpos1
    have hre_tsum :
        (negDE₂ τ).re =
          ∑' n : ℕ,
            (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * Real.exp (-2 * Real.pi * (n : ℝ) * t) := by
      have hre' :
          (negDE₂ τ).re =
            ∑' n : ℕ,
              ((24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * n * τ)).re := by
        simpa [hneg τ] using (Complex.reCLM.map_tsum (hsum_term τ))
      simp [hre', hterm_re]
    simpa [hre_tsum] using hpos

lemma Δ_fun_pos : ResToImagAxis.Pos Δ_fun := by
  have hΔfun : Δ_fun = fun z : ℍ => (Delta z : ℂ) := by
    funext z
    simpa [Δ_fun, one_div] using (Delta_apply_eq_one_div_1728_mul_E4_pow_three_sub_E6_sq z).symm
  simpa [hΔfun, Delta_apply] using (Delta_imag_axis_pos : ResToImagAxis.Pos Δ)

lemma L₁₀_SerreDer : L₁₀ = (serre_D 10 F) * G - F * (serre_D 10 G) := by
  ext z; simp [L₁₀, serre_D]; ring_nf

lemma SerreDer_22_L₁₀_SerreDer :
    SerreDer_22_L₁₀ = (serre_D 12 (serre_D 10 F)) * G - F * (serre_D 12 (serre_D 10 G)) := by
  have SF_holo := @serre_D_differentiable F 10 F_holo
  have SG_holo := @serre_D_differentiable G 10 G_holo
  calc
    SerreDer_22_L₁₀ = serre_D 22 (serre_D 10 F * G - F * serre_D 10 G) := by
      simpa [SerreDer_22_L₁₀] using congrArg (serre_D 22) L₁₀_SerreDer
    _ = serre_D 22 (serre_D 10 F * G) - serre_D 22 (F * serre_D 10 G) := by
        simpa using
          (serre_D_sub 22 (serre_D 10 F * G) (F * serre_D 10 G)
            (MDifferentiable.mul SF_holo G_holo) (MDifferentiable.mul F_holo SG_holo))
    _ = serre_D (12 + 10) ((serre_D 10 F) * G) - serre_D (10 + 12) (F * serre_D 10 G) := by ring_nf
    _ = serre_D 12 (serre_D 10 F) * G + (serre_D 10 F) * (serre_D 10 G)
        - serre_D (10 + 12) (F * serre_D 10 G) := by
          simpa using (serre_D_mul 12 10 (serre_D 10 F) G SF_holo G_holo)
    _ = serre_D 12 (serre_D 10 F) * G + (serre_D 10 F) * (serre_D 10 G)
        - ((serre_D 10 F) * (serre_D 10 G) + F * (serre_D 12 (serre_D 10 G))) := by
          simpa using (serre_D_mul 10 12 F (serre_D 10 G) F_holo SG_holo)
    _ = (serre_D 12 (serre_D 10 F)) * G - F * (serre_D 12 (serre_D 10 G)) := by ring_nf

private lemma SerreDer_22_L₁₀_form :
    SerreDer_22_L₁₀ =
      (7200 : ℝ) • (Δ_fun * negDE₂ * G) + (640 : ℝ) • (Δ_fun * H₂ * F) := by
  ext z; simp [SerreDer_22_L₁₀_SerreDer, MLDE_F, MLDE_G, mul_assoc, mul_comm]; ring_nf

/-!
## Positivity of the Serre derivative of `L₁₀`
-/

/-- The Serre derivative `serre_D 22 L₁₀` is positive on the imaginary axis. -/
public lemma SerreDer_22_L₁₀_pos : ResToImagAxis.Pos SerreDer_22_L₁₀ := by
  have hΔ : ResToImagAxis.Pos Δ_fun := Δ_fun_pos
  have hneg : ResToImagAxis.Pos negDE₂ := negDE₂_pos
  have hG : ResToImagAxis.Pos G := G_pos
  have hH2 : ResToImagAxis.Pos H₂ := H₂_imag_axis_pos
  have hF : ResToImagAxis.Pos F := F_pos
  have hterm1 : ResToImagAxis.Pos (Δ_fun * negDE₂ * G) :=
    (ResToImagAxis.Pos.mul (ResToImagAxis.Pos.mul hΔ hneg) hG)
  have hterm2 : ResToImagAxis.Pos (Δ_fun * H₂ * F) :=
    (ResToImagAxis.Pos.mul (ResToImagAxis.Pos.mul hΔ hH2) hF)
  have hterm1' : ResToImagAxis.Pos ((7200 : ℝ) • (Δ_fun * negDE₂ * G)) := by
    exact ResToImagAxis.Pos.smul (c := (7200 : ℝ)) hterm1 (by positivity)
  have hterm2' : ResToImagAxis.Pos ((640 : ℝ) • (Δ_fun * H₂ * F)) := by
    exact ResToImagAxis.Pos.smul (c := (640 : ℝ)) hterm2 (by positivity)
  have hsum :
      ResToImagAxis.Pos
        (((7200 : ℝ) • (Δ_fun * negDE₂ * G)) + ((640 : ℝ) • (Δ_fun * H₂ * F))) :=
    ResToImagAxis.Pos.add hterm1' hterm2'
  simpa [SerreDer_22_L₁₀_form] using hsum
