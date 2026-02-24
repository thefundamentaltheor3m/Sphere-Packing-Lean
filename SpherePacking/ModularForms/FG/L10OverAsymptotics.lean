module
public import SpherePacking.ModularForms.FG.Basic
public import SpherePacking.ModularForms.ResToImagAxis
import SpherePacking.ModularForms.FG.Positivity
import SpherePacking.ModularForms.FG.AsymptoticsTools

/-!
# Eventual positivity of `L₁₀` on the imaginary axis

This file proves `L₁₀_eventuallyPos`, a performance-sensitive lemma used later in the `FG/`
development. The proof is split into several private steps to help compilation.

## Main declaration
* `L₁₀_eventuallyPos`
-/

open scoped Real Manifold Topology ArithmeticFunction.sigma ModularForm MatrixGroups
open Filter Complex UpperHalfPlane ModularForm

-- Ensure the `SL(2,ℤ)` Möbius action on `ℍ` is available below.
noncomputable local instance : MulAction SL(2, ℤ) ℍ := UpperHalfPlane.SLAction (R := ℤ)

section

-- Prevent `whnf` from unfolding `H₂` in the long asymptotics proof.
attribute [local irreducible] H₂

private noncomputable def q₁ : UpperHalfPlane → ℂ :=
  fun z => cexp ((2 * π * Complex.I) * (z : ℂ))

private noncomputable def q₂ : UpperHalfPlane → ℂ :=
  fun z => cexp ((4 * π * Complex.I) * (z : ℂ))

private noncomputable def q₃ : UpperHalfPlane → ℂ :=
  fun z => cexp ((3 * π * Complex.I) * (z : ℂ))

private noncomputable def L₁₀_over : UpperHalfPlane → ℂ :=
  fun z => L₁₀ z / (q₂ z * q₃ z)

private lemma coeff_4piI_div_2piI : ((4 * π * Complex.I) / (2 * π * Complex.I) : ℂ) = (2 : ℂ) := by
  exact (div_eq_iff Complex.two_pi_I_ne_zero).2 (by ring)

private lemma coeff_3piI_div_2piI :
    ((3 * π * Complex.I) / (2 * π * Complex.I) : ℂ) = (3 / 2 : ℂ) := by
  exact (div_eq_iff Complex.two_pi_I_ne_zero).2 (by ring)

private lemma L₁₀_real_resToImagAxis : ResToImagAxis.Real L₁₀ := by
  have hFreal : ResToImagAxis.Real F := F_pos.1
  have hGreal : ResToImagAxis.Real G := G_pos.1
  have hDFreal : ResToImagAxis.Real (D F) := ResToImagAxis.Real.D_of_real hFreal F_holo
  have hDGreal : ResToImagAxis.Real (D G) := ResToImagAxis.Real.D_of_real hGreal G_holo
  simpa [L₁₀] using
    ResToImagAxis.Real.sub (ResToImagAxis.Real.mul hDFreal hGreal)
      (ResToImagAxis.Real.mul hFreal hDGreal)

private lemma L₁₀_over_tendsto_atImInfty :
    Tendsto L₁₀_over UpperHalfPlane.atImInfty (nhds (5308416000 : ℂ)) := by
  -- Asymptotics at infinity via `F = q₂ * F₀` and `G = q₃ * G₀`.
  have hq₁_ne : ∀ z : UpperHalfPlane, q₁ z ≠ 0 := by simp [q₁]
  have hq₂_ne : ∀ z : UpperHalfPlane, q₂ z ≠ 0 := by simp [q₂]
  have hq₃_ne : ∀ z : UpperHalfPlane, q₃ z ≠ 0 := by simp [q₃]
  have hq₁_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q₁ := by
    simpa [q₁] using mdifferentiable_cexp_mul (2 * π * Complex.I)
  have hq₂_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q₂ := by
    simpa [q₂] using mdifferentiable_cexp_mul (4 * π * Complex.I)
  have hq₃_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q₃ := by
    simpa [q₃] using mdifferentiable_cexp_mul (3 * π * Complex.I)
  let A : UpperHalfPlane → ℂ := A_E
  let B : UpperHalfPlane → ℂ := fun z => A z / q₁ z
  let F₀ : UpperHalfPlane → ℂ := fun z => (B z) ^ 2
  have hA_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) A :=
    (MDifferentiable.mul E₂_holo' E₄.holo').sub E₆.holo'
  have hB_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) B := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    have hA' := (UpperHalfPlane.mdifferentiable_iff).1 hA_holo
    have hq₁' := (UpperHalfPlane.mdifferentiable_iff).1 hq₁_holo
    simpa [B, Function.comp] using
      hA'.div hq₁'
        (by intro w hw; simpa using hq₁_ne (UpperHalfPlane.ofComplex w))
  have hF0_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F₀ := by
    -- `F₀ = B^2`.
    simpa [F₀, pow_two] using (hB_holo.mul hB_holo)
  have hB_eq_series (z : UpperHalfPlane) :
      B z =
        (720 : ℂ) * ∑' n : ℕ,
          ((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
    have hA : A z =
        (720 : ℂ) * ∑' (n : ℕ+),
          (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
      -- Rearrange the exponential term to match our `q₁`.
      simpa [A, mul_assoc, mul_left_comm, mul_comm] using (E₂_mul_E₄_sub_E₆ z)
    -- Shift the ℕ+ sum to an ℕ sum and cancel one `q₁` factor in each exponential.
    have hshift :
        (∑' (n : ℕ+),
            (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))) =
          ∑' n : ℕ,
            ((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) *
              cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)) := by
      -- `∑_{n≥1} f n = ∑_{m≥0} f(m+1)`.
      simpa [mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm, add_assoc] using
        (tsum_pnat_eq_tsum_succ3 (f := fun n : ℕ =>
          (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))))
    -- Now divide by `q₁ z = exp(2πiz)`.
    have hexp_cancel (n : ℕ) :
        cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)) / q₁ z =
          cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
      -- Use `exp(x)/exp(y) = exp(x-y)` and simplify the difference.
      have hq1 : q₁ z = cexp (2 * π * Complex.I * (z : ℂ)) := by simp [q₁, mul_assoc]
      calc
        cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)) / q₁ z
            = cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)) /
                cexp (2 * π * Complex.I * (z : ℂ)) := by simp [hq1]
        _ = cexp
              ((2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)) -
                (2 * π * Complex.I * (z : ℂ))) := by
              simpa [div_eq_mul_inv] using
                (Complex.exp_sub (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))
                  (2 * π * Complex.I * (z : ℂ))).symm
        _ = cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
              -- Simplify the exponent using `(n+1) = n+1`.
              have hn1 : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 := by
                norm_cast
              have hsub :
                  ((n + 1 : ℕ) : ℂ) * (z : ℂ) - (z : ℂ) = (n : ℂ) * (z : ℂ) := by
                calc
                  ((n + 1 : ℕ) : ℂ) * (z : ℂ) - (z : ℂ) =
                      (((n : ℂ) + 1) * (z : ℂ)) - (z : ℂ) := by simp [hn1]
                  _ = ((n : ℂ) * (z : ℂ) + (z : ℂ)) - (z : ℂ) := by
                        simp [add_mul]
                  _ = (n : ℂ) * (z : ℂ) := by ring
              have hexp2 :
                  (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ) -
                        (2 * π * Complex.I * (z : ℂ))) =
                      (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
                calc
                  (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ) -
                        (2 * π * Complex.I * (z : ℂ))) =
                      (2 * π * Complex.I) * (((n + 1 : ℕ) : ℂ) * (z : ℂ) - (z : ℂ)) := by
                        simp [mul_assoc, mul_sub]
                  _ = (2 * π * Complex.I) * ((n : ℂ) * (z : ℂ)) := by
                        simpa [mul_assoc] using congrArg (fun w : ℂ => (2 * π * Complex.I) * w) hsub
                  _ = (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
                        simp [mul_assoc, mul_left_comm, mul_comm]
              exact congrArg cexp hexp2
    have hq1 : q₁ z = cexp (2 * π * Complex.I * (z : ℂ)) := by simp [q₁]
    -- Combine everything.
    have hA' : A z = (720 : ℂ) * ∑' n : ℕ,
          ((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) *
            cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)) := by
      simpa [hshift] using hA
    have hB' : B z = A z / q₁ z := rfl
    -- Substitute series for `A` and cancel `q₁`.
    calc
      B z = A z / q₁ z := hB'
      _ = ((720 : ℂ) * ∑' n : ℕ,
            ((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) *
              cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))) / q₁ z := by
            simp [hA']
      _ = (720 : ℂ) * (∑' n : ℕ,
            ((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) *
              cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))) / q₁ z := by
            ring_nf
      _ = (720 : ℂ) * ((∑' n : ℕ,
              ((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) *
                cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))) * (q₁ z)⁻¹) := by
            simp [div_eq_mul_inv, mul_assoc]
      _ = (720 : ℂ) * ∑' n : ℕ,
            (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) *
              cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))) * (q₁ z)⁻¹ := by
            refine congrArg (fun s => (720 : ℂ) * s) ?_
            exact tsum_mul_right.symm
      _ = (720 : ℂ) * ∑' n : ℕ,
            (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) *
              cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))) / q₁ z := by
            simp [div_eq_mul_inv, mul_assoc]
      _ = (720 : ℂ) * ∑' n : ℕ,
            ((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) *
              (cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)) / q₁ z) := by
            refine congrArg (fun s => (720 : ℂ) * s) ?_
            refine tsum_congr ?_
            intro n
            simpa [mul_assoc] using
              (mul_div_assoc
                  (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))
                  (cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)))
                  (q₁ z))
      _ = (720 : ℂ) * ∑' n : ℕ,
            ((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) *
              cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
            refine congrArg (fun s => (720 : ℂ) * s) ?_
            refine tsum_congr ?_
            intro n
            have :=
              congrArg
                (fun x =>
                  ((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) * x)
                (hexp_cancel n)
            simpa [mul_assoc] using this
      _ = (720 : ℂ) * ∑' n : ℕ,
            ((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) *
              cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
            ring_nf
  -- Summability needed for `QExp.tendsto_nat`.
  have hsum_coeff :
      Summable (fun n : ℕ =>
        ‖(((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))‖ * Real.exp (-2 * π * n)) := by
    -- Compare with `n^5 * r^n` for `r = exp(-2π)`.
    set r : ℝ := Real.exp (-2 * π) with hr
    have hr_nonneg : 0 ≤ r := (Real.exp_pos _).le
    have hr_lt_one : r < 1 := by
      have : (-2 * π : ℝ) < 0 := by nlinarith [Real.pi_pos]
      simpa [hr] using (Real.exp_lt_one_iff.2 this)
    have hr_norm : ‖r‖ < 1 := by
      simpa [Real.norm_of_nonneg hr_nonneg] using hr_lt_one
    have hsumm_pow : Summable (fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5 hr_norm
    -- Bound coefficients using `σ₃(n+1) ≤ (n+1)^4` and `(n+1)^5 ≤ 32*n^5` for `n ≥ 1`.
    have hbound : ∀ n : ℕ,
        ‖(((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))‖ * Real.exp (-2 * π * n) ≤
          (if n = 0 then 1 else 32 * ((n : ℝ) ^ 5 * r ^ n)) := by
      intro n
      by_cases hn : n = 0
      · subst hn
        simp
      · have hn1 : 1 ≤ n := Nat.succ_le_iff.1 (Nat.pos_of_ne_zero hn)
        have hσ : (σ 3 (n + 1) : ℝ) ≤ (n + 1 : ℝ) ^ 4 := by
          exact_mod_cast (sigma_bound 3 (n + 1))
        have hcoeff :
            (n + 1 : ℝ) * (σ 3 (n + 1) : ℝ) ≤ (n + 1 : ℝ) ^ 5 := by
          have hn0 : 0 ≤ (n + 1 : ℝ) := by positivity
          have := mul_le_mul_of_nonneg_left hσ hn0
          simpa [pow_succ, mul_assoc] using this
        have hn_add : (n + 1 : ℝ) ≤ 2 * (n : ℝ) := by
          have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
          linarith
        have hpow_le : (n + 1 : ℝ) ^ 5 ≤ 32 * (n : ℝ) ^ 5 := by
          have : (n + 1 : ℝ) ≤ (2 : ℝ) * (n : ℝ) := hn_add
          calc
            (n + 1 : ℝ) ^ 5 ≤ ((2 : ℝ) * (n : ℝ)) ^ 5 := by
              exact pow_le_pow_left₀ (by positivity) this 5
            _ = 32 * (n : ℝ) ^ 5 := by ring_nf
        have hterm :
            ‖(((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))‖ ≤ 32 * (n : ℝ) ^ 5 := by
          have :
              ‖(((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))‖ =
                (n + 1 : ℝ) * (σ 3 (n + 1) : ℝ) := by
            have hn0 : 0 ≤ (n : ℝ) + 1 := by positivity
            have hσ0 : 0 ≤ (σ 3 (n + 1) : ℝ) := by positivity
            calc
              ‖(((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))‖ =
                  ‖((n + 1 : ℕ) : ℂ)‖ * ‖(σ 3 (n + 1) : ℂ)‖ := by
                    simp
                  _ = (n + 1 : ℝ) * (σ 3 (n + 1) : ℝ) := by
                      -- `simp` reduces the goal to a norm statement about a natural number.
                      simp
                      have hcast : (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) := by
                        norm_cast
                      have hnNorm : ‖(n : ℂ) + 1‖ = (n + 1 : ℝ) := by
                        calc
                          ‖(n : ℂ) + 1‖ = ‖((n + 1 : ℕ) : ℂ)‖ := by
                            simp
                          _ = (n + 1 : ℝ) := by
                            simpa using (Complex.norm_natCast (n + 1))
                      -- rewrite the RHS `(n+1)` as `n+1`
                      simpa using hnNorm
          rw [this]
          exact le_trans hcoeff hpow_le
        have hexp : Real.exp (-2 * π * n) = r ^ n := by
          have hmul : (-2 * π * n : ℝ) = (n : ℝ) * (-2 * π) := by
            simpa [mul_assoc] using (mul_comm (-2 * π) (n : ℝ))
          calc
            Real.exp (-2 * π * n) = Real.exp ((n : ℝ) * (-2 * π)) := by
              simpa using congrArg Real.exp hmul
            _ = Real.exp (-2 * π) ^ n := by simpa using (Real.exp_nat_mul (-2 * π) n)
            _ = r ^ n := by simp [hr]
        have :
            ‖(((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))‖ * Real.exp (-2 * π * n) ≤
              (32 * (n : ℝ) ^ 5) * (r ^ n) := by
          have hnexp' : 0 ≤ Real.exp (-2 * π * n) := (Real.exp_pos _).le
          have hmul :=
            (mul_le_mul_of_nonneg_right hterm hnexp' : _)
          have hexp_form : Real.exp (-(2 * (π * (n : ℝ)))) = r ^ n := by
            have harg : (-(2 * (π * (n : ℝ))) : ℝ) = (-2 * π * n : ℝ) := by ring
            simpa [harg] using hexp
          -- `hmul` is phrased with `Real.exp (-2πn)`; rewrite it as `r^n`.
          simpa [mul_assoc, hexp_form] using hmul
        simpa [hn, mul_assoc, mul_left_comm, mul_comm] using this
    -- Use `Summable.of_nonneg_of_le` with a summable majorant.
    have hsumm_major :
        Summable (fun n : ℕ => (if n = 0 then (1 : ℝ) else 32 * ((n : ℝ) ^ 5 * r ^ n))) := by
      have hsumm1 : Summable (fun n : ℕ => (32 : ℝ) * ((n : ℝ) ^ 5 * r ^ n)) :=
        (hsumm_pow.mul_left 32)
      have hsumm0 : Summable (fun n : ℕ => (if n = 0 then (1 : ℝ) else 0)) := by
        refine summable_of_finite_support ((Set.finite_singleton (0 : ℕ)).subset ?_)
        intro n hn
        have hn0 : (if n = 0 then (1 : ℝ) else 0) ≠ 0 := by simpa [Function.support] using hn
        have : n = 0 := by
          by_contra h
          exact hn0 (by simp [h])
        simp [this]
      have hdecomp :
          (fun n : ℕ => (if n = 0 then (1 : ℝ) else 32 * ((n : ℝ) ^ 5 * r ^ n))) =
            (fun n : ℕ => (if n = 0 then (1 : ℝ) else 0) + (32 : ℝ) * ((n : ℝ) ^ 5 * r ^ n)) := by
        funext n; by_cases hn : n = 0 <;> simp [hn]
      simpa [hdecomp] using (hsumm0.add hsumm1)
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsumm_major
    · exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    · exact hbound n
  have hBlim : Tendsto B UpperHalfPlane.atImInfty (nhds (720 : ℂ)) := by
    -- `B` is a `q`-series with constant term `720`.
    let a : ℕ → ℂ := fun n => (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))
    have ha : Summable (fun n : ℕ => ‖a n‖ * Real.exp (-2 * π * n)) := by
      simpa [a] using hsum_coeff
    have hseries :
        Tendsto (fun z : UpperHalfPlane => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n))
          UpperHalfPlane.atImInfty (nhds (a 0)) :=
      QExp.tendsto_nat (a := a) (ha := ha)
    have hseries' :
        Tendsto (fun z : UpperHalfPlane =>
            (720 : ℂ) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n))
          UpperHalfPlane.atImInfty (nhds ((720 : ℂ) * (a 0))) :=
      (tendsto_const_nhds.mul hseries)
    have hEq :
        (fun z : UpperHalfPlane =>
            (720 : ℂ) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n)) = B := by
      funext z
      simpa [a, mul_assoc, mul_left_comm, mul_comm] using (hB_eq_series z).symm
    have ha0 : a 0 = (1 : ℂ) := by simp [a]
    simpa [hEq, ha0] using hseries'
  have hF0lim' : Tendsto F₀ UpperHalfPlane.atImInfty (nhds (518400 : ℂ)) := by
    have h := (hBlim.pow 2)
    have hconst : (720 : ℂ) ^ 2 = (518400 : ℂ) := by norm_num
    simpa [F₀, hconst] using h
  have hF0_bdd : IsBoundedAtImInfty F₀ := by
    have hzero : Tendsto (fun z : UpperHalfPlane =>
      F₀ z - (518400 : ℂ)) UpperHalfPlane.atImInfty (nhds 0) := by
      have hconst :
          Tendsto (fun _ : UpperHalfPlane =>
            (518400 : ℂ)) UpperHalfPlane.atImInfty (nhds (518400 : ℂ)) :=
        tendsto_const_nhds
      simpa using hF0lim'.sub hconst
    have hbdd_diff : IsBoundedAtImInfty (fun z : UpperHalfPlane => F₀ z - (518400 : ℂ)) :=
      UpperHalfPlane.IsZeroAtImInfty.isBoundedAtImInfty hzero
    have hbdd_const : IsBoundedAtImInfty (fun _ : UpperHalfPlane => (518400 : ℂ)) :=
      Filter.const_boundedAtFilter _ _
    have hbdd_sum :
        IsBoundedAtImInfty (fun z : UpperHalfPlane => (F₀ z - (518400 : ℂ)) + (518400 : ℂ)) := by
      dsimp [UpperHalfPlane.IsBoundedAtImInfty] at hbdd_diff hbdd_const ⊢
      exact BoundedAtFilter.add hbdd_diff hbdd_const
    have hEq : (fun z : UpperHalfPlane => (F₀ z - (518400 : ℂ)) + (518400 : ℂ)) = F₀ := by
      funext z; ring
    simpa [hEq] using hbdd_sum
  have hDF0_zero : UpperHalfPlane.IsZeroAtImInfty (D F₀) :=
    D_isZeroAtImInfty_of_bounded hF0_holo hF0_bdd
  have hDF0lim : Tendsto (D F₀) UpperHalfPlane.atImInfty (nhds (0 : ℂ)) := by
    simpa [UpperHalfPlane.IsZeroAtImInfty] using hDF0_zero
  -- Now handle `G`: factor out `exp(3πiz)` using the leading exponential term of `H₂`.
  let qπ : UpperHalfPlane → ℂ := fun z => cexp (π * Complex.I * (z : ℂ))
  have hqπ_ne : ∀ z : UpperHalfPlane, qπ z ≠ 0 := by intro z; simp [qπ]
  have hqπ_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) qπ := by
    simpa [qπ, mul_assoc, mul_left_comm, mul_comm] using mdifferentiable_cexp_mul (π * Complex.I)
  -- Make `H₂'` a genuine local constant (not a reducible `let`) to avoid `whnf` unfolding the huge
  -- definition of `H₂` in later algebraic manipulations.
  set H₂' : UpperHalfPlane → ℂ := fun z => H₂ z / qπ z with hH2'_def
  have hH2'_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    have hH2_on : DifferentiableOn ℂ (H₂ ∘ UpperHalfPlane.ofComplex) {w : ℂ | 0 < w.im} :=
      (UpperHalfPlane.mdifferentiable_iff).1 H₂_SIF_MDifferentiable
    have hq_on : DifferentiableOn ℂ (qπ ∘ UpperHalfPlane.ofComplex) {w : ℂ | 0 < w.im} :=
      (UpperHalfPlane.mdifferentiable_iff).1 hqπ_holo
    have hq_ne' : ∀ w : ℂ, w ∈ {w : ℂ | 0 < w.im} → (qπ (UpperHalfPlane.ofComplex w)) ≠ 0 := by
      intro w hw
      simpa using hqπ_ne (UpperHalfPlane.ofComplex w)
    simpa [hH2'_def, Function.comp] using (hH2_on.div hq_on hq_ne')
  -- `H₂ / exp(πiz) → 16` at `i∞`.
  have hH2'_lim : Tendsto H₂' UpperHalfPlane.atImInfty (nhds (16 : ℂ)) := by
    let g : UpperHalfPlane → ℂ := fun z => jacobiTheta₂ (z / 2) z
    have hg : Tendsto g UpperHalfPlane.atImInfty (nhds (2 : ℂ)) :=
      jacobiTheta₂_half_mul_apply_tendsto_atImInfty
    have hrewrite : H₂' = fun z => (g z) ^ 4 := by
      funext z
      have hΘ₂ : Θ₂ z = cexp (π * Complex.I * (z : ℂ) / 4) * g z := by
        simpa [g] using (Θ₂_as_jacobiTheta₂ z)
      -- `H₂ = Θ₂^4 = exp(πiz) * g^4`.
      have hE : cexp (π * Complex.I * (z : ℂ) / 4) ^ 4 = cexp (π * Complex.I * (z : ℂ)) := by
        have h := (Complex.exp_nat_mul (π * Complex.I * (z : ℂ) / 4) 4).symm
        have harg : (4 : ℂ) * (π * Complex.I * (z : ℂ) / 4) = π * Complex.I * (z : ℂ) := by
          simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        exact h.trans (by simpa using congrArg cexp harg)
      have hH2 :
          H₂ z = cexp (π * Complex.I * (z : ℂ)) * (g z) ^ 4 := by
        calc
          H₂ z = (Θ₂ z) ^ 4 := by simp [H₂]
          _ = (cexp (π * Complex.I * (z : ℂ) / 4) * g z) ^ 4 := by simp [hΘ₂]
          _ = cexp (π * Complex.I * (z : ℂ) / 4) ^ 4 * (g z) ^ 4 := by simp [mul_pow]
          _ = cexp (π * Complex.I * (z : ℂ)) * (g z) ^ 4 := by simp [hE]
      have hne : qπ z ≠ 0 := by simp [qπ]
      -- Cancel the exponential factor.
      calc
        H₂' z = (cexp (π * Complex.I * (z : ℂ)) * (g z) ^ 4) / qπ z := by
          simp [hH2'_def, qπ, hH2, mul_assoc]
        _ = (g z) ^ 4 := by
          -- Cancel the `exp(πiz)` factor.
          simp [qπ, mul_assoc]
    -- Finish.
    have h2pow : (2 : ℂ) ^ 4 = (16 : ℂ) := by norm_num
    simpa [hrewrite, h2pow] using (hg.pow 4)
  -- The polynomial factor in the definition of `G`.
  set poly : UpperHalfPlane → ℂ := 2 * H₂ ^ 2 + 5 * H₂ * H₄ + 5 * H₄ ^ 2 with hpoly_def
  have hpoly_lim : Tendsto poly UpperHalfPlane.atImInfty (nhds (5 : ℂ)) := by
    have hH2 : Tendsto H₂ UpperHalfPlane.atImInfty (nhds 0) := H₂_tendsto_atImInfty
    have hH4 : Tendsto H₄ UpperHalfPlane.atImInfty (nhds 1) := H₄_tendsto_atImInfty
    have hH2sq : Tendsto (fun z : UpperHalfPlane =>
      H₂ z ^ 2) UpperHalfPlane.atImInfty (nhds (0 : ℂ)) := by
      simpa using (hH2.pow 2)
    have hH4sq : Tendsto (fun z : UpperHalfPlane =>
      H₄ z ^ 2) UpperHalfPlane.atImInfty (nhds (1 : ℂ)) := by
      simpa using (hH4.pow 2)
    have hterm1 : Tendsto (fun z : UpperHalfPlane =>
      (2 : ℂ) * H₂ z ^ 2) UpperHalfPlane.atImInfty (nhds 0) := by
      simpa [mul_assoc] using
        ((tendsto_const_nhds : Tendsto (fun _ : UpperHalfPlane =>
          (2 : ℂ)) UpperHalfPlane.atImInfty (nhds (2 : ℂ))).mul
          hH2sq)
    have hterm2 : Tendsto (fun z : UpperHalfPlane =>
      5 * H₂ z * H₄ z) UpperHalfPlane.atImInfty (nhds 0) := by
      have h5H2 :
          Tendsto (fun z : UpperHalfPlane =>
            (5 : ℂ) * H₂ z) UpperHalfPlane.atImInfty (nhds (0 : ℂ)) := by
        simpa [mul_assoc] using
          ((tendsto_const_nhds :
                Tendsto (fun _ : UpperHalfPlane =>
                  (5 : ℂ)) UpperHalfPlane.atImInfty (nhds (5 : ℂ))).mul hH2)
      simpa [mul_assoc] using h5H2.mul hH4
    have hterm3 : Tendsto (fun z : UpperHalfPlane =>
      5 * H₄ z ^ 2) UpperHalfPlane.atImInfty (nhds (5 : ℂ)) := by
      simpa [mul_assoc] using
        ((tendsto_const_nhds : Tendsto (fun _ : UpperHalfPlane =>
          (5 : ℂ)) UpperHalfPlane.atImInfty (nhds (5 : ℂ))).mul hH4sq)
    -- Combine.
    have : Tendsto (fun z : UpperHalfPlane => (2 : ℂ) * H₂ z ^ 2 + (5 * H₂ z * H₄ z + 5 * H₄ z ^ 2))
        UpperHalfPlane.atImInfty (nhds (0 + (0 + 5) : ℂ)) :=
      hterm1.add (hterm2.add hterm3)
    -- Unfold the pointwise polynomial factor.
    simpa [hpoly_def, add_assoc] using this
  set G₀ : UpperHalfPlane → ℂ := fun z => (H₂' z) ^ 3 * poly z with hG0_def
  have hG0_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₀ := by
    have hH2cube : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : UpperHalfPlane => (H₂' z) ^ 3) := by
      -- `H₂'^3 = H₂' * (H₂'^2)`.
      have hH2sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : UpperHalfPlane => (H₂' z) ^ 2) := by
        simpa [pow_two] using hH2'_holo.mul hH2'_holo
      simpa [pow_succ, pow_two, Nat.succ_eq_add_one, mul_assoc] using hH2'_holo.mul hH2sq
    have hpoly_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) poly := by
      -- Polynomial expression in `H₂` and `H₄`.
      have hH2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂ := H₂_SIF_MDifferentiable
      have hH4 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄ := H₄_SIF_MDifferentiable
      have hH2sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 2) := by
        simpa [pow_two] using hH2.mul hH2
      have hH4sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₄ ^ 2) := by
        simpa [pow_two] using hH4.mul hH4
      have hconst2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun _ : UpperHalfPlane => (2 : ℂ)) :=
        mdifferentiable_const
      have hconst5 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun _ : UpperHalfPlane => (5 : ℂ)) :=
        mdifferentiable_const
      have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (2 * H₂ ^ 2) := by
        simpa using hconst2.mul hH2sq
      have h2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (5 * H₂ * H₄) := by
        -- `5 * H₂ * H₄ = (5 * H₂) * H₄`.
        have h5H2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (5 * H₂) := by
          simpa using hconst5.mul hH2
        simpa [mul_assoc] using h5H2.mul hH4
      have h3 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (5 * H₄ ^ 2) := by
        simpa using hconst5.mul hH4sq
      simpa [hpoly_def, add_assoc] using (h1.add (h2.add h3))
    simpa [hG0_def] using (hH2cube.mul hpoly_holo)
  have hG0lim : Tendsto G₀ UpperHalfPlane.atImInfty (nhds (20480 : ℂ)) := by
    have h1 : Tendsto (fun z : UpperHalfPlane =>
      (H₂' z) ^ 3) UpperHalfPlane.atImInfty (nhds ((16 : ℂ) ^ 3)) :=
      (hH2'_lim.pow 3)
    have h2 : Tendsto (fun z : UpperHalfPlane =>
      poly z) UpperHalfPlane.atImInfty (nhds (5 : ℂ)) := hpoly_lim
    have : Tendsto (fun z : UpperHalfPlane => (H₂' z) ^ 3 * poly z) UpperHalfPlane.atImInfty
        (nhds (((16 : ℂ) ^ 3) * (5 : ℂ))) := h1.mul h2
    have hconst : ((16 : ℂ) ^ 3) * (5 : ℂ) = (20480 : ℂ) := by norm_num
    simpa [hG0_def, hconst] using this
  have hG0_bdd : IsBoundedAtImInfty G₀ := by
    have hzero : Tendsto (fun z : UpperHalfPlane =>
      G₀ z - (20480 : ℂ)) UpperHalfPlane.atImInfty (nhds 0) := by
      have hconst :
          Tendsto (fun _ : UpperHalfPlane =>
            (20480 : ℂ)) UpperHalfPlane.atImInfty (nhds (20480 : ℂ)) :=
        tendsto_const_nhds
      simpa using hG0lim.sub hconst
    have hbdd_diff : IsBoundedAtImInfty (fun z : UpperHalfPlane => G₀ z - (20480 : ℂ)) :=
      UpperHalfPlane.IsZeroAtImInfty.isBoundedAtImInfty hzero
    have hbdd_const : IsBoundedAtImInfty (fun _ : UpperHalfPlane => (20480 : ℂ)) :=
      Filter.const_boundedAtFilter _ _
    have hbdd_sum :
        IsBoundedAtImInfty (fun z : UpperHalfPlane => (G₀ z - (20480 : ℂ)) + (20480 : ℂ)) := by
      dsimp [UpperHalfPlane.IsBoundedAtImInfty] at hbdd_diff hbdd_const ⊢
      exact BoundedAtFilter.add hbdd_diff hbdd_const
    have hEq : (fun z : UpperHalfPlane => (G₀ z - (20480 : ℂ)) + (20480 : ℂ)) = G₀ := by
      funext z; ring
    simpa [hEq] using hbdd_sum
  have hDG0_zero : UpperHalfPlane.IsZeroAtImInfty (D G₀) :=
    D_isZeroAtImInfty_of_bounded hG0_holo hG0_bdd
  have hDG0lim : Tendsto (D G₀) UpperHalfPlane.atImInfty (nhds (0 : ℂ)) := by
    simpa [UpperHalfPlane.IsZeroAtImInfty] using hDG0_zero
  have hH2_fun : H₂ = qπ * H₂' := by
    funext z
    have hq : qπ z ≠ 0 := hqπ_ne z
    have : qπ z * H₂' z = H₂ z := by
      calc
        qπ z * H₂' z = qπ z * (H₂ z / qπ z) := by
          simp [hH2'_def]
        _ = H₂ z := by
          simp [div_eq_mul_inv, mul_left_comm, hq]
    exact this.symm
  -- Clear definitional values to avoid `whnf` unfolding huge definitions in later algebra.
  clear_value H₂'
  clear hH2'_def
  clear_value poly
  -- Factorizations `F = q₂ * F₀` and `G = q₃ * G₀`.
  have hF_factor : F = fun z : UpperHalfPlane => q₂ z * F₀ z := by
    funext z
    have hq2 : q₂ z = (q₁ z) ^ 2 := by
      -- `exp(4πiz) = (exp(2πiz))^2`.
      calc
        q₂ z = cexp (4 * π * Complex.I * (z : ℂ)) := rfl
        _ = cexp (2 * (2 * π * Complex.I * (z : ℂ))) := by
          congr 1
          ring_nf
        _ = (cexp (2 * π * Complex.I * (z : ℂ))) ^ 2 := by
          simpa using (Complex.exp_nat_mul (2 * π * Complex.I * (z : ℂ)) 2)
        _ = (q₁ z) ^ 2 := by simp [q₁]
    have hA : A z = q₁ z * B z := by
      -- Multiply the defining equation `B = A / q₁` by `q₁` and cancel.
      have hq : q₁ z ≠ 0 := hq₁_ne z
      calc
        A z = (q₁ z * A z) / q₁ z := by
          simpa using (mul_div_cancel_left₀ (A z) hq).symm
        _ = q₁ z * (A z / q₁ z) := by
          simpa [mul_assoc] using (mul_div_assoc (q₁ z) (A z) (q₁ z))
        _ = q₁ z * B z := by rfl
    -- Now expand `F = A^2` and `F₀ = B^2`.
    calc
      F z = (A z) ^ 2 := by simp [F, A, A_E]
      _ = (q₁ z * B z) ^ 2 := by simp [hA]
      _ = (q₁ z) ^ 2 * (B z) ^ 2 := by simp [mul_pow]
      _ = q₂ z * F₀ z := by
            simp [hq2, F₀, pow_two, mul_assoc]
  have hG_factor : G = fun z : UpperHalfPlane => q₃ z * G₀ z := by
    funext z
    have hH2 : H₂ z = qπ z * H₂' z := by
      have hz : H₂ z = (qπ * H₂') z :=
        congrArg (fun f : UpperHalfPlane → ℂ => f z) hH2_fun
      exact hz.trans rfl
    have hq3 : q₃ z = (qπ z) ^ 3 := by
      -- `exp(3πiz) = (exp(πiz))^3`.
      dsimp [q₃, qπ]
      simpa [mul_assoc] using (Complex.exp_nat_mul (π * Complex.I * (z : ℂ)) 3)
    have hGz : G z = (H₂ z) ^ 3 * poly z := by
      -- Use `poly` to abbreviate the polynomial factor.
      have hG_fun : G = H₂ ^ 3 * poly := by
        dsimp [G]
        rw [hpoly_def]
      have hz : G z = (H₂ ^ 3 * poly) z := congrArg (fun f : UpperHalfPlane → ℂ => f z) hG_fun
      exact hz.trans rfl
    have hG0z : G₀ z = (H₂' z) ^ 3 * poly z := by
      have hz :
          G₀ z =
            (fun w : UpperHalfPlane => (H₂' w) ^ 3 * poly w) z :=
        congrArg (fun f : UpperHalfPlane → ℂ => f z) hG0_def
      exact hz.trans rfl
    -- Rewrite everything in terms of `qπ` and cancel powers.
    rw [hGz, hG0z, hH2, hq3]
    have hpow := (mul_pow (qπ z) (H₂' z) 3)
    -- Prevent `whnf` from unfolding large definitions by generalizing.
    rw [hpow]
    generalize ha : (qπ z) ^ 3 = a
    generalize hb : (H₂' z) ^ 3 = b
    generalize hc : poly z = c
    simpa using (mul_assoc a b c)
  -- Compute the limit of `L₁₀/(q₂*q₃)`.
  have hDF_over :
      (fun z : UpperHalfPlane => (D F z) / q₂ z) =
        fun z => (2 : ℂ) * F₀ z + D F₀ z := by
    funext z
    have hq2ne : q₂ z ≠ 0 := hq₂_ne z
    have hDq2 : D q₂ z = (2 : ℂ) * q₂ z := by
      -- `D exp(4πiz) = 2·exp(4πiz)`.
      simpa [q₂, coeff_4piI_div_2piI] using (D_cexp_mul (4 * π * Complex.I) z)
    have hDprod_z :
        D (fun w : UpperHalfPlane => q₂ w * F₀ w) z =
          (D q₂ z) * F₀ z + q₂ z * D F₀ z := by
      have hDprod := D_mul q₂ F₀ hq₂_holo hF0_holo
      simpa using congrArg (fun f => f z) hDprod
    have hDz : D F z = (D q₂ z) * F₀ z + q₂ z * D F₀ z := by
      simpa [hF_factor] using hDprod_z
    calc
      (D F z) / q₂ z = ((D q₂ z) * F₀ z + q₂ z * D F₀ z) / q₂ z := by
        simp [hDz]
      _ = (D q₂ z) * F₀ z / q₂ z + (q₂ z * D F₀ z) / q₂ z := by
        simp [add_div]
      _ = (2 : ℂ) * F₀ z + D F₀ z := by
        have hterm2 : (q₂ z * D F₀ z) / q₂ z = D F₀ z := by
          simpa [mul_assoc] using (mul_div_cancel_left₀ (D F₀ z) hq2ne)
        have hterm1 : (D q₂ z) * F₀ z / q₂ z = (2 : ℂ) * F₀ z := by
          calc
            (D q₂ z) * F₀ z / q₂ z = ((2 : ℂ) * q₂ z) * F₀ z / q₂ z := by
              simp [hDq2]
            _ = (2 : ℂ) * ((q₂ z * F₀ z) / q₂ z) := by
              simp [mul_assoc, mul_div_assoc]
            _ = (2 : ℂ) * F₀ z := by
              have : (q₂ z * F₀ z) / q₂ z = F₀ z := by
                simpa [mul_assoc] using (mul_div_cancel_left₀ (F₀ z) hq2ne)
              simp [this]
        simp [hterm1, hterm2]
  have hDG_over :
      (fun z : UpperHalfPlane => (D G z) / q₃ z) =
        fun z => (3 / 2 : ℂ) * G₀ z + D G₀ z := by
    funext z
    have hq3ne : q₃ z ≠ 0 := hq₃_ne z
    have hDq3 : D q₃ z = (3 / 2 : ℂ) * q₃ z := by
      -- `D exp(3πiz) = 3/2·exp(3πiz)`.
      simpa [q₃, coeff_3piI_div_2piI] using (D_cexp_mul (3 * π * Complex.I) z)
    have hDprod_z :
        D (fun w : UpperHalfPlane => q₃ w * G₀ w) z =
          (D q₃ z) * G₀ z + q₃ z * D G₀ z := by
      have hDprod := D_mul q₃ G₀ hq₃_holo hG0_holo
      simpa using congrArg (fun f => f z) hDprod
    have hDz : D G z = (D q₃ z) * G₀ z + q₃ z * D G₀ z := by
      simpa [hG_factor] using hDprod_z
    calc
      (D G z) / q₃ z = ((D q₃ z) * G₀ z + q₃ z * D G₀ z) / q₃ z := by
        simp [hDz]
      _ = (D q₃ z) * G₀ z / q₃ z + (q₃ z * D G₀ z) / q₃ z := by
        simp [add_div]
      _ = (3 / 2 : ℂ) * G₀ z + D G₀ z := by
              have hterm2 : (q₃ z * D G₀ z) / q₃ z = D G₀ z := by
                simpa [mul_assoc] using (mul_div_cancel_left₀ (D G₀ z) hq3ne)
              have hterm1 : (D q₃ z) * G₀ z / q₃ z = (3 / 2 : ℂ) * G₀ z := by
                calc
                  (D q₃ z) * G₀ z / q₃ z = ((3 / 2 : ℂ) * q₃ z) * G₀ z / q₃ z := by
                    simp [hDq3]
                  _ = (3 / 2 : ℂ) * ((q₃ z * G₀ z) / q₃ z) := by
                    simp [mul_assoc, mul_div_assoc]
                  _ = (3 / 2 : ℂ) * G₀ z := by
                    have : (q₃ z * G₀ z) / q₃ z = G₀ z := by
                      simpa [mul_assoc] using (mul_div_cancel_left₀ (G₀ z) hq3ne)
                    simp [this]
              simp [hterm1, hterm2]
  have hDF_over_lim :
      Tendsto (fun z : UpperHalfPlane =>
        (D F z) / q₂ z) UpperHalfPlane.atImInfty (nhds (1036800 : ℂ)) := by
    -- `DF/q₂ = 2*F₀ + D F₀`.
    have h1 : Tendsto (fun z : UpperHalfPlane =>
      (2 : ℂ) * F₀ z) UpperHalfPlane.atImInfty (nhds ((2 : ℂ) * (518400 : ℂ))) :=
      tendsto_const_nhds.mul hF0lim'
    have h2 : Tendsto (fun z : UpperHalfPlane => D F₀ z) UpperHalfPlane.atImInfty (nhds (0 : ℂ)) :=
      hDF0lim
    have hsum : Tendsto (fun z : UpperHalfPlane => (2 : ℂ) * F₀ z + D F₀ z) UpperHalfPlane.atImInfty
        (nhds (((2 : ℂ) * (518400 : ℂ)) + 0)) := h1.add h2
    have hconst : ((2 : ℂ) * (518400 : ℂ) + 0) = (1036800 : ℂ) := by norm_num
    simpa [hDF_over, hconst] using hsum
  have hDG_over_lim :
      Tendsto (fun z : UpperHalfPlane =>
        (D G z) / q₃ z) UpperHalfPlane.atImInfty (nhds (30720 : ℂ)) := by
    have hG0lim' : Tendsto G₀ UpperHalfPlane.atImInfty (nhds (20480 : ℂ)) := hG0lim
    have h1 :
        Tendsto (fun z : UpperHalfPlane => (3 / 2 : ℂ) * G₀ z) UpperHalfPlane.atImInfty
          (nhds ((3 / 2 : ℂ) * (20480 : ℂ))) :=
      tendsto_const_nhds.mul hG0lim'
    have h2 : Tendsto (fun z : UpperHalfPlane => D G₀ z) UpperHalfPlane.atImInfty (nhds (0 : ℂ)) :=
      hDG0lim
    have hsum :
        Tendsto (fun z : UpperHalfPlane => (3 / 2 : ℂ) * G₀ z + D G₀ z) UpperHalfPlane.atImInfty
          (nhds (((3 / 2 : ℂ) * (20480 : ℂ)) + 0)) := h1.add h2
    have hconst : ((3 / 2 : ℂ) * (20480 : ℂ) + 0) = (30720 : ℂ) := by norm_num
    simpa [hDG_over, hconst] using hsum
  have hL10_over_lim :
      Tendsto L₁₀_over UpperHalfPlane.atImInfty (nhds (5308416000 : ℂ)) := by
    -- `L₁₀/(q₂ q₃) = (D F/q₂) * G₀ - F₀ * (D G/q₃)`.
    have hF0lim'' : Tendsto F₀ UpperHalfPlane.atImInfty (nhds (518400 : ℂ)) := hF0lim'
    have hG0lim'' : Tendsto G₀ UpperHalfPlane.atImInfty (nhds (20480 : ℂ)) := hG0lim
    have h1 :
        Tendsto (fun z : UpperHalfPlane => ((D F z) / q₂ z) * G₀ z) UpperHalfPlane.atImInfty
          (nhds ((1036800 : ℂ) * (20480 : ℂ))) := hDF_over_lim.mul hG0lim''
    have h2 :
        Tendsto (fun z : UpperHalfPlane => F₀ z * ((D G z) / q₃ z)) UpperHalfPlane.atImInfty
          (nhds ((518400 : ℂ) * (30720 : ℂ))) := hF0lim''.mul hDG_over_lim
    have hsub :
        Tendsto (fun z : UpperHalfPlane =>
            ((D F z) / q₂ z) * G₀ z - F₀ z * ((D G z) / q₃ z))
          UpperHalfPlane.atImInfty (nhds
            (((1036800 : ℂ) * (20480 : ℂ)) - ((518400 : ℂ) * (30720 : ℂ)))) :=
      h1.sub h2
    have hconst :
        ((1036800 : ℂ) * (20480 : ℂ)) - ((518400 : ℂ) * (30720 : ℂ)) = (5308416000 : ℂ) := by
      norm_num
    have hsub' :
        Tendsto (fun z : UpperHalfPlane =>
              ((D F z) / q₂ z) * G₀ z - F₀ z * ((D G z) / q₃ z))
            UpperHalfPlane.atImInfty (nhds (5308416000 : ℂ)) := by
      simpa [hconst] using hsub
    have hL10_over_eq :
        (fun z : UpperHalfPlane => L₁₀_over z) =
          fun z : UpperHalfPlane => ((D F z) / q₂ z) * G₀ z - F₀ z * ((D G z) / q₃ z) := by
      funext z
      have hFz : F z = q₂ z * F₀ z := congrArg (fun f => f z) hF_factor
      have hGz : G z = q₃ z * G₀ z := congrArg (fun f => f z) hG_factor
      -- Cancel the exponential factors `q₂, q₃` by clearing denominators.
      have hq2 : q₂ z ≠ 0 := hq₂_ne z
      have hq3 : q₃ z ≠ 0 := hq₃_ne z
      dsimp [L₁₀_over, L₁₀]
      rw [hFz, hGz]
      field_simp [hq2, hq3]
    simpa [hL10_over_eq] using hsub'
  exact hL10_over_lim

private lemma L₁₀_over_eventuallyPos_re
    (hL10_over_lim : Tendsto L₁₀_over UpperHalfPlane.atImInfty (nhds (5308416000 : ℂ))) :
    ∀ᶠ t : ℝ in atTop, (0 : ℝ) < (L₁₀_over (UpperHalfPlane.ofComplex (Complex.I * t))).re := by
  -- Transfer the `atImInfty`-limit to a statement along `t → ∞` on the imaginary axis.
  have hL10_over_lim_t :
      Tendsto (fun t : ℝ =>
        L₁₀_over (UpperHalfPlane.ofComplex (Complex.I * t))) atTop (nhds (5308416000 : ℂ)) :=
    hL10_over_lim.comp tendsto_ofComplex_I_mul_atTop_atImInfty
  have hL10_over_re_lim :
      Tendsto (fun t : ℝ =>
      (L₁₀_over (UpperHalfPlane.ofComplex (Complex.I * t))).re) atTop (nhds (5308416000 : ℝ)) := by
    -- Take real parts (the limit is real).
    have := (Complex.continuous_re.tendsto (5308416000 : ℂ)).comp hL10_over_lim_t
    simpa using this
  -- Eventually the real part is close to the positive limit.
  exact hL10_over_re_lim.eventually (Ioi_mem_nhds (by norm_num))

private lemma ofComplex_I_mul_eq_mk (t : ℝ) (ht : 0 < t) :
    UpperHalfPlane.ofComplex (Complex.I * t) =
      (⟨Complex.I * t, by simpa using ht⟩ : UpperHalfPlane) := by
  simpa using UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using ht)

private lemma q₂q₃_mul_pos_re_and_im_zero (t : ℝ) (ht : 0 < t) :
    let z : UpperHalfPlane := ⟨Complex.I * t, by simpa using ht⟩
    (q₂ z * q₃ z ≠ 0) ∧ (q₂ z * q₃ z).im = 0 ∧ 0 < (q₂ z * q₃ z).re := by
  let z : UpperHalfPlane := ⟨Complex.I * t, by simpa using ht⟩
  have hq2_ofReal : q₂ z = cexp (-(t * (π * 4)) : ℝ) := by
    dsimp [q₂, z]
    refine congrArg cexp ?_
    simpa [mul_assoc, mul_left_comm, mul_comm] using (I_mul_I_mul (↑t * (↑π * 4)))
  have hq3_ofReal : q₃ z = cexp (-(t * (π * 3)) : ℝ) := by
    dsimp [q₃, z]
    refine congrArg cexp ?_
    simpa [mul_assoc, mul_left_comm, mul_comm] using (I_mul_I_mul (↑t * (↑π * 3)))
  have hq_ne : q₂ z * q₃ z ≠ 0 := by simp [q₂, q₃, z]
  have hq2_im : (q₂ z).im = 0 := by
    simpa [hq2_ofReal] using (Complex.exp_ofReal_im (-(t * (π * 4))))
  have hq3_im : (q₃ z).im = 0 := by
    simpa [hq3_ofReal] using (Complex.exp_ofReal_im (-(t * (π * 3))))
  have ha_im : (q₂ z * q₃ z).im = 0 := by
    simp [Complex.mul_im, hq2_im, hq3_im]
  have hqpos : 0 < (q₂ z * q₃ z).re := by
    have hq2_pos : 0 < (q₂ z).re := by
      have hq2_re : (q₂ z).re = Real.exp (-(t * (π * 4))) := by
        simpa [hq2_ofReal] using (Complex.exp_ofReal_re (-(t * (π * 4))))
      simpa [hq2_re] using (Real.exp_pos (-(t * (π * 4))))
    have hq3_pos : 0 < (q₃ z).re := by
      have hq3_re : (q₃ z).re = Real.exp (-(t * (π * 3))) := by
        simpa [hq3_ofReal] using (Complex.exp_ofReal_re (-(t * (π * 3))))
      simpa [hq3_re] using (Real.exp_pos (-(t * (π * 3))))
    simpa [Complex.mul_re, hq2_im, hq3_im] using (mul_pos hq2_pos hq3_pos)
  simpa [z] using (And.intro hq_ne (And.intro ha_im hqpos))

private lemma L₁₀_eval_and_over_im_zero (hL10_real : ResToImagAxis.Real L₁₀) (t : ℝ) (ht : 0 < t)
    (z : UpperHalfPlane) (hzdef : z = (⟨Complex.I * t, by simp [ht]⟩ : UpperHalfPlane))
    (a : ℂ) (ha : a = q₂ z * q₃ z) (ha_ne : a ≠ 0) (ha_im : a.im = 0) :
    L₁₀.resToImagAxis t = a * L₁₀_over z ∧ (L₁₀_over z).im = 0 := by
  have hL10_eval_z : L₁₀ z = a * L₁₀_over z := by
    have : a * (L₁₀ z / a) = L₁₀ z := by
      calc
        a * (L₁₀ z / a) = (a * L₁₀ z) / a := by
          simpa [mul_assoc] using (mul_div_assoc a (L₁₀ z) a).symm
        _ = L₁₀ z := by
          simpa [mul_assoc] using (mul_div_cancel_left₀ (L₁₀ z) ha_ne)
    simpa [L₁₀_over, ha.symm, mul_div_assoc] using this.symm
  have hres : L₁₀.resToImagAxis t = L₁₀ z := by
    simp [Function.resToImagAxis, ResToImagAxis, ht, hzdef.symm]
  have hL10_eval : L₁₀.resToImagAxis t = a * L₁₀_over z := hres.trans hL10_eval_z
  have hover_real : (L₁₀_over z).im = 0 := by
    have hL10_im_res : (L₁₀.resToImagAxis t).im = 0 := by
      simpa [Function.resToImagAxis_apply] using hL10_real t ht
    have hres_im : (L₁₀.resToImagAxis t).im = (L₁₀ z).im := by
      simpa using congrArg Complex.im hres
    have hL10_im : (L₁₀ z).im = 0 := by
      simpa using hres_im.symm.trans hL10_im_res
    simp [L₁₀_over, ha.symm, Complex.div_im, hL10_im, ha_im]
  exact ⟨hL10_eval, hover_real⟩

private lemma L₁₀_resToImagAxis_re_pos_of_mul (t : ℝ) (z : UpperHalfPlane)
    (a : ℂ) (ha_im : a.im = 0) (hover_real : (L₁₀_over z).im = 0)
    (hL10_eval : L₁₀.resToImagAxis t = a * L₁₀_over z)
    (ha_pos : 0 < a.re) (hover_pos : 0 < (L₁₀_over z).re) :
    0 < (L₁₀.resToImagAxis t).re := by
  rw [hL10_eval]
  simpa [Complex.mul_re, ha_im, hover_real] using mul_pos ha_pos hover_pos

private lemma L₁₀_eventuallyPos_of_over_aux_z (t₀ t : ℝ) (ht : max t₀ 1 ≤ t)
    (ht₀ : ∀ t, t₀ ≤ t → 0 < (L₁₀_over (UpperHalfPlane.ofComplex (Complex.I * t))).re) :
    ∃ htpos : 0 < t,
      ∃ z : UpperHalfPlane,
        z = (⟨Complex.I * t, by simpa using htpos⟩ : UpperHalfPlane) ∧
          UpperHalfPlane.ofComplex (Complex.I * t) = z ∧ 0 < (L₁₀_over z).re := by
  have htpos : 0 < t := lt_of_lt_of_le (by positivity : (0 : ℝ) < max t₀ 1) ht
  refine ⟨htpos, ?_⟩
  let z : UpperHalfPlane := ⟨Complex.I * t, by simpa using htpos⟩
  have hz_of : UpperHalfPlane.ofComplex (Complex.I * t) = z := by
    simpa [z] using ofComplex_I_mul_eq_mk t htpos
  have hpos_over : 0 < (L₁₀_over z).re := by
    simpa [hz_of] using ht₀ t (le_trans (le_max_left _ _) ht)
  refine ⟨z, rfl, hz_of, hpos_over⟩

private lemma L₁₀_eventuallyPos_of_over_aux_a (t : ℝ) (htpos : 0 < t)
    (z : UpperHalfPlane) (hz : z = (⟨Complex.I * t, by simpa using htpos⟩ : UpperHalfPlane)) :
    ∃ a : ℂ, a = q₂ z * q₃ z ∧ a ≠ 0 ∧ a.im = 0 ∧ 0 < a.re := by
  refine ⟨q₂ z * q₃ z, rfl, ?_⟩
  simpa [hz] using (q₂q₃_mul_pos_re_and_im_zero t htpos)

private lemma L₁₀_eventuallyPos_of_over_aux_eval (hL10_real : ResToImagAxis.Real L₁₀)
    (t : ℝ) (htpos : 0 < t) (z : UpperHalfPlane)
    (hz : z = (⟨Complex.I * t, by simpa using htpos⟩ : UpperHalfPlane))
    (a : ℂ) (ha : a = q₂ z * q₃ z) (ha_ne : a ≠ 0) (ha_im : a.im = 0) :
    L₁₀.resToImagAxis t = a * L₁₀_over z ∧ (L₁₀_over z).im = 0 :=
  L₁₀_eval_and_over_im_zero hL10_real t htpos z hz a ha ha_ne ha_im

private lemma L₁₀_eventuallyPos_of_over_aux_pos (t : ℝ) (z : UpperHalfPlane) (a : ℂ)
    (ha_im : a.im = 0) (hover_real : (L₁₀_over z).im = 0)
    (hL10_eval : L₁₀.resToImagAxis t = a * L₁₀_over z)
    (ha_pos : 0 < a.re) (hover_pos : 0 < (L₁₀_over z).re) :
    0 < (L₁₀.resToImagAxis t).re :=
  L₁₀_resToImagAxis_re_pos_of_mul t z a ha_im hover_real hL10_eval ha_pos hover_pos

private lemma L₁₀_eventuallyPos_of_over
    (hL10_real : ResToImagAxis.Real L₁₀)
    (hpos_event : ∀ᶠ t : ℝ in atTop,
      (0 : ℝ) < (L₁₀_over (UpperHalfPlane.ofComplex (Complex.I * t))).re) :
    ResToImagAxis.EventuallyPos L₁₀ := by
  rcases (Filter.eventually_atTop.1 hpos_event) with ⟨t₀, ht₀⟩
  refine ⟨hL10_real, max t₀ 1, by positivity, ?_⟩
  intro t ht
  rcases L₁₀_eventuallyPos_of_over_aux_z t₀ t ht ht₀ with ⟨htpos, z, hz, _, hpos_over⟩
  rcases L₁₀_eventuallyPos_of_over_aux_a t htpos z hz with ⟨a, ha, ha_ne, ha_im, ha_pos⟩
  rcases L₁₀_eventuallyPos_of_over_aux_eval hL10_real t htpos z hz a ha ha_ne ha_im with
    ⟨hL10_eval, hover_real⟩
  exact L₁₀_eventuallyPos_of_over_aux_pos t z a ha_im hover_real hL10_eval ha_pos hpos_over

private lemma L₁₀_eventuallyPos_step₁_real : ResToImagAxis.Real L₁₀ :=
  L₁₀_real_resToImagAxis

private lemma L₁₀_eventuallyPos_step₂_over_lim :
    Tendsto L₁₀_over UpperHalfPlane.atImInfty (nhds (5308416000 : ℂ)) :=
  L₁₀_over_tendsto_atImInfty

private lemma L₁₀_eventuallyPos_step₃_over_eventuallyPos :
    ∀ᶠ t : ℝ in atTop,
      (0 : ℝ) < (L₁₀_over (UpperHalfPlane.ofComplex (Complex.I * t))).re :=
  L₁₀_over_eventuallyPos_re L₁₀_eventuallyPos_step₂_over_lim

private lemma L₁₀_eventuallyPos_step₄ :
    ResToImagAxis.EventuallyPos L₁₀ :=
  L₁₀_eventuallyPos_of_over L₁₀_eventuallyPos_step₁_real L₁₀_eventuallyPos_step₃_over_eventuallyPos

/-- `L₁₀` is eventually positive on the imaginary axis. -/
public lemma L₁₀_eventuallyPos : ResToImagAxis.EventuallyPos L₁₀ :=
  L₁₀_eventuallyPos_step₄

end
