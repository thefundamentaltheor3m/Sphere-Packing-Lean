module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.ImagAxis

/-!
# Asymptotic bounds for `φ₂'` and `φ₄'` (AnotherIntegral.A)

Along the imaginary axis `z = it`, the modular forms `φ₂'` and `φ₄'` admit simple leading terms.
This file proves uniform bounds for the corresponding error terms once `t` is large enough.

## Main statements
* `exists_phi2'_sub_720_bound_ge`
* `exists_phi4'_sub_exp_sub_504_bound_ge`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Topology MatrixGroups CongruenceSubgroup ModularForm NNReal ENNReal
open scoped ArithmeticFunction.sigma

open Real Complex MeasureTheory Filter Function
open ArithmeticFunction

open MagicFunction.FourierEigenfunctions
open UpperHalfPlane ModularForm EisensteinSeries
open SlashInvariantFormClass ModularFormClass

noncomputable section

/-! ## Approximating `φ₂'` and `φ₄'` for large imaginary part. -/

lemma exp_neg_two_pi_pow_two_mul_exp_two_pi (t : ℝ) :
    Real.exp (-2 * π * t) ^ (2 : ℕ) * Real.exp (2 * π * t) = Real.exp (-2 * π * t) := by
  calc
    Real.exp (-2 * π * t) ^ (2 : ℕ) * Real.exp (2 * π * t) =
        Real.exp (2 * (-2 * π * t)) * Real.exp (2 * π * t) := by
          simpa using congrArg (fun r => r * Real.exp (2 * π * t))
            (Real.exp_nat_mul (-2 * π * t) 2).symm
    _ = Real.exp (2 * (-2 * π * t) + 2 * π * t) := by simp [Real.exp_add]
    _ = Real.exp (-2 * π * t) := by ring_nf

/-- For large `t`, `φ₂' (it)` differs from `720` by `O(exp (-2π t))`. -/
public lemma exists_phi2'_sub_720_bound_ge :
    ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧
      ∀ t : ℝ, (ht : 0 < t) → A ≤ t →
        ‖φ₂' (zI t ht) - (720 : ℂ)‖ ≤ C * Real.exp (-2 * π * t) := by
  rcases exists_inv_Delta_bound_exp with ⟨CΔinv, AΔ, hCΔinv_pos, hΔinv⟩
  rcases exists_E4_sub_one_bound with ⟨CE4, hCE4_pos, hE4⟩
  rcases exists_Delta_sub_q_bound with ⟨CΔq, hCΔq_pos, hΔq⟩
  rcases exists_E2E4_sub_E6_sub_720q_bound with ⟨CA, hCA_pos, hAq⟩
  let A : ℝ := max (1 : ℝ) AΔ
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAΔ : AΔ ≤ A := le_max_right _ _
  -- A fixed upper bound for `‖E₄‖` on `t ≥ 1`.
  let q1 : ℝ := Real.exp (-2 * π)
  have hq1 : q1 < 1 := by simpa [q1] using exp_neg_two_pi_lt_one
  let E4B : ℝ := 1 + CE4 * q1
  have hE4B_pos : 0 < E4B := by
    have : 0 ≤ CE4 * q1 := mul_nonneg hCE4_pos.le (Real.exp_pos _).le
    linarith
  -- Choose a convenient (positive) constant.
  let C : ℝ := 1 + CΔinv * (E4B * CA + 720 * (CE4 + CΔq))
  refine ⟨C, A, by
      have : 0 ≤ CΔinv * (E4B * CA + 720 * (CE4 + CΔq)) := by
        have : 0 ≤ (E4B * CA + 720 * (CE4 + CΔq)) := by
          have h0 : 0 ≤ E4B * CA := mul_nonneg (le_of_lt hE4B_pos) hCA_pos.le
          have h1 : 0 ≤ 720 * (CE4 + CΔq) := by
            have : 0 ≤ (CE4 + CΔq) := add_nonneg hCE4_pos.le hCΔq_pos.le
            nlinarith
          exact add_nonneg h0 h1
        exact mul_nonneg (le_of_lt hCΔinv_pos) this
      linarith, hA1, ?_⟩
  intro t ht0 htA
  have ht1 : 1 ≤ t := le_trans hA1 htA
  let z : ℍ := zI t ht0
  let q : ℝ := Real.exp (-2 * π * t)
  have hq_nonneg : 0 ≤ q := (Real.exp_pos _).le
  have hq_le_q1 : q ≤ q1 := by simpa [q, q1] using q_le_q1 (t := t) ht1
  have hE4norm : ‖E₄ z‖ ≤ E4B := by
    have hE4sub : ‖E₄ z - (1 : ℂ)‖ ≤ CE4 * q := by
      simpa [z, q] using hE4 t ht0 ht1
    have htri : ‖E₄ z‖ ≤ ‖E₄ z - (1 : ℂ)‖ + ‖(1 : ℂ)‖ := by
      simpa [sub_eq_add_neg, add_assoc] using (norm_add_le (E₄ z - (1 : ℂ)) (1 : ℂ))
    have hE4sub' : ‖E₄ z - (1 : ℂ)‖ ≤ CE4 * q1 :=
      le_trans hE4sub (mul_le_mul_of_nonneg_left hq_le_q1 hCE4_pos.le)
    have htri' : ‖E₄ z‖ ≤ ‖E₄ z - (1 : ℂ)‖ + 1 := by
      simpa using htri
    have hbound : ‖E₄ z - (1 : ℂ)‖ + 1 ≤ CE4 * q1 + 1 := by
      -- `add_le_add_left` produces `1 + a ≤ 1 + b`; commute to match our `a + 1` form.
      simpa [add_assoc, add_left_comm, add_comm] using (add_le_add_left hE4sub' 1)
    have : ‖E₄ z‖ ≤ CE4 * q1 + 1 := le_trans htri' hbound
    simpa [E4B, add_assoc, add_left_comm, add_comm] using this
  have hAerr : ‖(E₂ z) * (E₄ z) - (E₆ z) - (720 : ℂ) * (q : ℂ)‖ ≤ CA * q ^ (2 : ℕ) := by
    have := hAq t ht0 ht1
    simpa [z, q] using this
  have hΔerr : ‖Δ z - (q : ℂ)‖ ≤ CΔq * q ^ (2 : ℕ) := by
    have := hΔq t ht0 ht1
    simpa [z, q] using this
  have hΔinv' : ‖(Δ z)⁻¹‖ ≤ CΔinv * Real.exp (2 * π * t) := by
    have : AΔ ≤ z.im := by
      -- `z.im = t` and `AΔ ≤ A ≤ t`.
      have : AΔ ≤ t := le_trans hAΔ htA
      simpa [z, zI_im t ht0] using this
    simpa [z, zI_im t ht0] using hΔinv z this
  -- Bound `‖E₄*q - Δ‖` by `O(q^2)`.
  have hE4qΔ :
      ‖E₄ z * (q : ℂ) - Δ z‖ ≤ (CE4 + CΔq) * q ^ (2 : ℕ) := by
    have hE4sub : ‖E₄ z - (1 : ℂ)‖ ≤ CE4 * q := by
      simpa [z, q] using hE4 t ht0 ht1
    have h1 : ‖(E₄ z - (1 : ℂ)) * (q : ℂ)‖ ≤ CE4 * q ^ (2 : ℕ) := by
      have : ‖(q : ℂ)‖ = q := by
        simp [Complex.norm_real, abs_of_nonneg hq_nonneg]
      calc
        ‖(E₄ z - (1 : ℂ)) * (q : ℂ)‖ = ‖E₄ z - (1 : ℂ)‖ * ‖(q : ℂ)‖ := by simp
        _ ≤ (CE4 * q) * q := by
              have hmul := mul_le_mul_of_nonneg_right hE4sub (norm_nonneg (q : ℂ))
              simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq_nonneg, mul_assoc,
                mul_left_comm, mul_comm] using hmul
        _ = CE4 * q ^ (2 : ℕ) := by
              simp [pow_two, mul_left_comm, mul_comm]
    have h2 : ‖(q : ℂ) - Δ z‖ ≤ CΔq * q ^ (2 : ℕ) := by
      simpa [norm_sub_rev] using hΔerr
    have htri :
        ‖E₄ z * (q : ℂ) - Δ z‖ ≤ ‖(E₄ z - (1 : ℂ)) * (q : ℂ)‖ + ‖(q : ℂ) - Δ z‖ := by
      -- `E₄*q - Δ = (E₄-1)*q + (q-Δ)`.
      have hsum :
          E₄ z * (q : ℂ) - Δ z = (E₄ z - (1 : ℂ)) * (q : ℂ) + ((q : ℂ) - Δ z) := by ring
      calc
        ‖E₄ z * (q : ℂ) - Δ z‖ =
            ‖(E₄ z - (1 : ℂ)) * (q : ℂ) + ((q : ℂ) - Δ z)‖ :=
          congrArg norm hsum
        _ ≤ ‖(E₄ z - (1 : ℂ)) * (q : ℂ)‖ + ‖(q : ℂ) - Δ z‖ := norm_add_le _ _
    calc
      ‖E₄ z * (q : ℂ) - Δ z‖
          ≤ ‖(E₄ z - (1 : ℂ)) * (q : ℂ)‖ + ‖(q : ℂ) - Δ z‖ := htri
      _ ≤ CE4 * q ^ (2 : ℕ) + CΔq * q ^ (2 : ℕ) := by gcongr
      _ = (CE4 + CΔq) * q ^ (2 : ℕ) := by ring
  -- Rewrite and bound `φ₂' z - 720`.
  have hrew :
      φ₂' z - (720 : ℂ) =
        ((E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)) / (Δ z) := by
    have hΔ : (Δ z) ≠ 0 := Δ_ne_zero z
    dsimp [φ₂']
    field_simp [hΔ]
  -- Bound the numerator by `O(q^2)`.
  have hnum :
      ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)‖ ≤
        (E4B * CA + 720 * (CE4 + CΔq)) * q ^ (2 : ℕ) := by
    set Aterm : ℂ :=
      (E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z) - (720 : ℂ) * (q : ℂ))
    set Bterm : ℂ := (720 : ℂ) * (E₄ z * (q : ℂ) - Δ z)
    have hdecomp :
        (E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z) = Aterm + Bterm := by
      simp [Aterm, Bterm]
      ring
    have hA :
        ‖Aterm‖ ≤ (E4B * CA) * q ^ (2 : ℕ) := by
      have hmul :
          ‖Aterm‖ ≤ E4B * (CA * q ^ (2 : ℕ)) := by
        have hprod :=
          mul_le_mul hE4norm hAerr (norm_nonneg _) (le_of_lt hE4B_pos)
        simpa [Aterm, norm_mul, mul_assoc] using hprod
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    have hB :
        ‖Bterm‖ ≤ (720 * (CE4 + CΔq)) * q ^ (2 : ℕ) := by
      have h720 : ‖(720 : ℂ)‖ = (720 : ℝ) := by norm_num
      have hB' :
          ‖Bterm‖ ≤ (720 : ℝ) * ((CE4 + CΔq) * q ^ (2 : ℕ)) := by
        -- pull out the scalar `720` and use `hE4qΔ`.
        have := mul_le_mul_of_nonneg_left hE4qΔ (by norm_num : (0 : ℝ) ≤ (720 : ℝ))
        -- `‖(720:ℂ)‖ = 720`.
        simpa [Bterm, norm_mul, h720, mul_assoc, mul_left_comm, mul_comm] using this
      -- reassociate
      simpa [mul_assoc, mul_left_comm, mul_comm] using hB'
    -- Triangle inequality and collecting coefficients.
    calc
      ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)‖ =
          ‖Aterm + Bterm‖ := by simpa using congrArg norm hdecomp
      _ ≤ ‖Aterm‖ + ‖Bterm‖ := norm_add_le _ _
      _ ≤ (E4B * CA) * q ^ (2 : ℕ) + (720 * (CE4 + CΔq)) * q ^ (2 : ℕ) := by
            exact add_le_add hA hB
      _ = (E4B * CA + 720 * (CE4 + CΔq)) * q ^ (2 : ℕ) := by ring
  -- Multiply by `‖Δ⁻¹‖ = O(exp(2πt))` to obtain `O(q)`.
  have :
      ‖φ₂' z - (720 : ℂ)‖ ≤ (CΔinv * (E4B * CA + 720 * (CE4 + CΔq))) * q := by
    set K : ℝ := E4B * CA + 720 * (CE4 + CΔq)
    calc
      ‖φ₂' z - (720 : ℂ)‖
          = ‖((E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)) / (Δ z)‖ := by
              simp [hrew]
      _ = ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)‖ * ‖(Δ z)⁻¹‖ := by
              simp [div_eq_mul_inv]
      _ ≤ (K * q ^ (2 : ℕ)) * (CΔinv * Real.exp (2 * π * t)) := by
              have h1 :
                  ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)‖ ≤
                    K * q ^ (2 : ℕ) := by
                simpa [K] using hnum
              have h2 : ‖(Δ z)⁻¹‖ ≤ CΔinv * Real.exp (2 * π * t) := hΔinv'
              have hK : 0 ≤ K * q ^ (2 : ℕ) := by
                have : 0 ≤ K := by
                  dsimp [K]
                  exact add_nonneg (mul_nonneg (le_of_lt hE4B_pos) hCA_pos.le)
                    (by
                      have : 0 ≤ (CE4 + CΔq) := add_nonneg hCE4_pos.le hCΔq_pos.le
                      nlinarith)
                exact mul_nonneg this (pow_nonneg hq_nonneg _)
              exact mul_le_mul h1 h2 (norm_nonneg _) hK
      _ = (CΔinv * K) * q := by
              -- `q^2 * exp(2πt) = q` since `q = exp(-2πt)`.
              have hq2 : q ^ (2 : ℕ) * Real.exp (2 * π * t) = q := by
                simpa [q] using exp_neg_two_pi_pow_two_mul_exp_two_pi (t := t)
              -- Reassociate, then apply `hq2`.
              calc
                (K * q ^ (2 : ℕ)) * (CΔinv * Real.exp (2 * π * t))
                    = (CΔinv * K) * (q ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
                        ring
                _ = (CΔinv * K) * q := by simp [hq2]
  -- Enlarge the constant by `+1`.
  have hle :
      (CΔinv * (E4B * CA + 720 * (CE4 + CΔq))) * q ≤
        C * q := by
    have : CΔinv * (E4B * CA + 720 * (CE4 + CΔq)) ≤ C := by
      dsimp [C]; linarith
    exact mul_le_mul_of_nonneg_right this hq_nonneg
  simpa [z, q, A, C] using (this.trans hle)

lemma sq_add_sub_decomp (a b c : ℂ) :
    (a + b) ^ (2 : ℕ) - c = ((a ^ (2 : ℕ) - c) + (2 : ℂ) * a * b) + b ^ (2 : ℕ) := by
  ring

lemma norm_base240_sq_sub_target480_eq {q : ℝ} (hq_nonneg : 0 ≤ q) :
    ‖(((1 : ℂ) + (240 : ℂ) * (q : ℂ)) ^ (2 : ℕ) -
          ((1 : ℂ) + (480 : ℂ) * (q : ℂ)))‖ =
        (240 ^ 2 : ℝ) * q ^ (2 : ℕ) := by
  have h :
      ((1 : ℂ) + (240 : ℂ) * (q : ℂ)) ^ (2 : ℕ) -
          ((1 : ℂ) + (480 : ℂ) * (q : ℂ)) =
        (240 ^ 2 : ℂ) * (q : ℂ) ^ (2 : ℕ) := by
    simp [pow_two]
    ring
  have hq : ‖(q : ℂ) ^ (2 : ℕ)‖ = q ^ (2 : ℕ) := by
    simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq_nonneg]
  calc
    ‖((1 : ℂ) + (240 : ℂ) * (q : ℂ)) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * (q : ℂ))‖ =
        ‖(240 ^ 2 : ℂ) * (q : ℂ) ^ (2 : ℕ)‖ := by simp [h]
    _ = ‖(240 ^ 2 : ℂ)‖ * ‖(q : ℂ) ^ (2 : ℕ)‖ := by simp
    _ = (240 ^ 2 : ℝ) * q ^ (2 : ℕ) := by simp [hq]

lemma norm_two_mul_base240_mul_e_le
    {q CE4 B240 : ℝ} {e : ℂ}
    (he : ‖e‖ ≤ CE4 * q ^ (2 : ℕ))
    (hbase_norm : ‖((1 : ℂ) + (240 : ℂ) * (q : ℂ))‖ ≤ B240) :
    ‖(2 : ℂ) * ((1 : ℂ) + (240 : ℂ) * (q : ℂ)) * e‖ ≤
        (2 * B240 * CE4) * q ^ (2 : ℕ) := by
  have h2 : 0 ≤ ‖(2 : ℂ)‖ := norm_nonneg _
  have hB240 : 0 ≤ B240 := le_trans (norm_nonneg _) hbase_norm
  calc
    ‖(2 : ℂ) * ((1 : ℂ) + (240 : ℂ) * (q : ℂ)) * e‖ =
        ‖(2 : ℂ)‖ * ‖(1 : ℂ) + (240 : ℂ) * (q : ℂ)‖ * ‖e‖ := by
          simp [mul_assoc]
    _ ≤ ‖(2 : ℂ)‖ * B240 * (CE4 * q ^ (2 : ℕ)) := by
          gcongr
    _ = (2 * B240 * CE4) * q ^ (2 : ℕ) := by
          norm_num
          ring

lemma norm_e_sq_le
    {q CE4 : ℝ} {e : ℂ} (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (he : ‖e‖ ≤ CE4 * q ^ (2 : ℕ)) :
    ‖e ^ (2 : ℕ)‖ ≤ (CE4 ^ 2) * q ^ (2 : ℕ) := by
  have hq4_le_q2 : q ^ (4 : ℕ) ≤ q ^ (2 : ℕ) :=
    pow_le_pow_of_le_one hq_nonneg hq_le_one (by decide : (2 : ℕ) ≤ 4)
  have hCE4sq : 0 ≤ CE4 ^ 2 := sq_nonneg CE4
  calc
    ‖e ^ (2 : ℕ)‖ = ‖e‖ ^ (2 : ℕ) := by simp [norm_pow]
    _ ≤ (CE4 * q ^ (2 : ℕ)) ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) he _
    _ = (CE4 ^ 2) * q ^ (4 : ℕ) := by
          have hqpow : (q ^ (2 : ℕ)) ^ (2 : ℕ) = q ^ (4 : ℕ) := by
            simpa using (pow_mul q 2 2).symm
          calc
            (CE4 * q ^ (2 : ℕ)) ^ (2 : ℕ) = CE4 ^ (2 : ℕ) * (q ^ (2 : ℕ)) ^ (2 : ℕ) := by
              simp [mul_pow]
            _ = (CE4 ^ 2) * q ^ (4 : ℕ) := by simp [hqpow]
    _ ≤ (CE4 ^ 2) * q ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hq4_le_q2 hCE4sq

lemma norm_sq_sub_le_three_norms (base target e : ℂ) :
    ‖(base + e) ^ (2 : ℕ) - target‖ ≤
      ‖base ^ (2 : ℕ) - target‖ + ‖(2 : ℂ) * base * e‖ + ‖e ^ (2 : ℕ)‖ := by
  -- Expand the square and apply `‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖`.
  simpa [sq_add_sub_decomp, add_assoc, add_left_comm, add_comm] using
    (norm_add₃_le (a := base ^ (2 : ℕ) - target) (b := (2 : ℂ) * base * e) (c := e ^ (2 : ℕ)))

lemma norm_base_add_e_sq_sub_one_sub_480q_le_core
    {q CE4 B240 : ℝ} {e : ℂ}
    (hbase2 :
      ‖(((1 : ℂ) + (240 : ℂ) * (q : ℂ)) ^ (2 : ℕ) -
            ((1 : ℂ) + (480 : ℂ) * (q : ℂ)))‖ ≤ (240 ^ 2 : ℝ) * q ^ (2 : ℕ))
    (hlin :
      ‖(2 : ℂ) * ((1 : ℂ) + (240 : ℂ) * (q : ℂ)) * e‖ ≤ (2 * B240 * CE4) * q ^ (2 : ℕ))
    (hquad : ‖e ^ (2 : ℕ)‖ ≤ (CE4 ^ 2) * q ^ (2 : ℕ)) :
    ‖((((1 : ℂ) + (240 : ℂ) * (q : ℂ)) + e) ^ (2 : ℕ) -
          ((1 : ℂ) + (480 : ℂ) * (q : ℂ)))‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ) := by
  have htri :
      ‖((((1 : ℂ) + (240 : ℂ) * (q : ℂ)) + e) ^ (2 : ℕ) -
            ((1 : ℂ) + (480 : ℂ) * (q : ℂ)))‖ ≤
        ‖((1 : ℂ) + (240 : ℂ) * (q : ℂ)) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * (q : ℂ))‖ +
            ‖(2 : ℂ) * ((1 : ℂ) + (240 : ℂ) * (q : ℂ)) * e‖ + ‖e ^ (2 : ℕ)‖ := by
    simpa using
      (norm_sq_sub_le_three_norms ((1 : ℂ) + (240 : ℂ) * (q : ℂ)) ((1 : ℂ) + (480 : ℂ) * (q : ℂ)) e)
  have hsum :
      ‖((1 : ℂ) + (240 : ℂ) * (q : ℂ)) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * (q : ℂ))‖ +
            ‖(2 : ℂ) * ((1 : ℂ) + (240 : ℂ) * (q : ℂ)) * e‖ + ‖e ^ (2 : ℕ)‖ ≤
        (240 ^ 2 : ℝ) * q ^ (2 : ℕ) + (2 * B240 * CE4) * q ^ (2 : ℕ) + (CE4 ^ 2) * q ^ (2 : ℕ) := by
    linarith [hbase2, hlin, hquad]
  have hfac :
      (240 ^ 2 : ℝ) * q ^ (2 : ℕ) + (2 * B240 * CE4) * q ^ (2 : ℕ) + (CE4 ^ 2) * q ^ (2 : ℕ) =
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ) := by
    ring
  exact le_trans htri (le_trans hsum (le_of_eq hfac))

lemma norm_base_add_e_sq_sub_one_sub_480q_le
    {q CE4 B240 : ℝ} (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1) {e : ℂ}
    (he : ‖e‖ ≤ CE4 * q ^ (2 : ℕ))
    (hbase_norm : ‖((1 : ℂ) + (240 : ℂ) * (q : ℂ))‖ ≤ B240) :
    ‖((((1 : ℂ) + (240 : ℂ) * (q : ℂ)) + e) ^ (2 : ℕ) -
          ((1 : ℂ) + (480 : ℂ) * (q : ℂ)))‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ) := by
  simpa using
    (norm_base_add_e_sq_sub_one_sub_480q_le_core (q := q) (CE4 := CE4) (B240 := B240) (e := e)
      (by simpa using (le_of_eq (norm_base240_sq_sub_target480_eq (q := q) hq_nonneg)))
      (norm_two_mul_base240_mul_e_le (q := q) (CE4 := CE4) (B240 := B240) (e := e) he hbase_norm)
      (norm_e_sq_le (q := q) (CE4 := CE4) (e := e) hq_nonneg hq_le_one he))

lemma phi4_numerator_bound
    {t q : ℝ} {z : ℍ} {B240 CE4 CΔ3 CΔq : ℝ}
    (hE4sq :
      ‖(E₄ z) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * (q : ℂ))‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ))
    (hExpΔ :
      ‖(Real.exp (2 * π * t) : ℂ) * (Δ z) - ((1 : ℂ) + (-24 : ℂ) * (q : ℂ))‖ ≤
        CΔ3 * q ^ (2 : ℕ))
    (hΔ2err : ‖Δ z - (q : ℂ)‖ ≤ CΔq * q ^ (2 : ℕ)) :
    ‖(E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq) * q ^ (2 : ℕ) := by
  set qC : ℂ := (q : ℂ)
  have hcancel :
      ((1 : ℂ) + (480 : ℂ) * qC) - ((1 : ℂ) + (-24 : ℂ) * qC) - (504 : ℂ) * qC = 0 := by
    ring
  have hdecomp :
      (E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z) =
        ((E₄ z) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * qC)) -
          ((Real.exp (2 * π * t) : ℂ) * (Δ z) - ((1 : ℂ) + (-24 : ℂ) * qC)) -
            (504 : ℂ) * (Δ z - qC) := by
    have : ((1 : ℂ) + (480 : ℂ) * qC) - ((1 : ℂ) + (-24 : ℂ) * qC) - (504 : ℂ) * qC = 0 := hcancel
    ring
  have hterm3 : ‖(504 : ℂ) * (Δ z - qC)‖ ≤ (504 * CΔq) * q ^ (2 : ℕ) := by
    have hΔ : ‖Δ z - qC‖ ≤ CΔq * q ^ (2 : ℕ) := by
      simpa [qC] using hΔ2err
    have h504 : ‖(504 : ℂ)‖ = (504 : ℝ) := by norm_num
    have h504_nonneg : (0 : ℝ) ≤ (504 : ℝ) := by norm_num
    calc
      ‖(504 : ℂ) * (Δ z - qC)‖ = ‖(504 : ℂ)‖ * ‖Δ z - qC‖ := by simp
      _ = (504 : ℝ) * ‖Δ z - qC‖ := by simp
      _ ≤ (504 : ℝ) * (CΔq * q ^ (2 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hΔ h504_nonneg
      _ = (504 * CΔq) * q ^ (2 : ℕ) := by ring
  have htri :
      ‖(E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)‖ ≤
        ‖(E₄ z) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * qC)‖ +
          ‖(Real.exp (2 * π * t) : ℂ) * (Δ z) - ((1 : ℂ) + (-24 : ℂ) * qC)‖ +
            ‖(504 : ℂ) * (Δ z - qC)‖ := by
    set A : ℂ := (E₄ z) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * qC)
    set B : ℂ := (Real.exp (2 * π * t) : ℂ) * (Δ z) - ((1 : ℂ) + (-24 : ℂ) * qC)
    set C : ℂ := (504 : ℂ) * (Δ z - qC)
    have hAB : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le A B
    have hABC : ‖(A - B) - C‖ ≤ ‖A - B‖ + ‖C‖ := norm_sub_le (A - B) C
    calc
      ‖(E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)‖
          = ‖(A - B) - C‖ := by
              have hfull :
                  (E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z) =
                    (A - B) - C := by
                simpa [A, B, C] using hdecomp
              simpa using congrArg norm hfull
      _ ≤ ‖A - B‖ + ‖C‖ := hABC
      _ ≤ (‖A‖ + ‖B‖) + ‖C‖ := by
            simpa [add_assoc, add_left_comm, add_comm] using (add_le_add_left hAB ‖C‖)
      _ = ‖A‖ + ‖B‖ + ‖C‖ := by simp [add_assoc]
      _ = ‖(E₄ z) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * qC)‖ +
            ‖(Real.exp (2 * π * t) : ℂ) * (Δ z) - ((1 : ℂ) + (-24 : ℂ) * qC)‖ +
            ‖(504 : ℂ) * (Δ z - qC)‖ := by
            simp [A, B, C]
  have h1 : ‖(E₄ z) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * qC)‖ ≤
      ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ) := by
    simpa [qC] using hE4sq
  have h2 : ‖(Real.exp (2 * π * t) : ℂ) * (Δ z) - ((1 : ℂ) + (-24 : ℂ) * qC)‖ ≤
      CΔ3 * q ^ (2 : ℕ) := by
    simpa [qC] using hExpΔ
  have h3 : ‖(504 : ℂ) * (Δ z - qC)‖ ≤ (504 * CΔq) * q ^ (2 : ℕ) := hterm3
  have htmp :
      ‖(E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)‖ ≤
        (((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ)) +
          (CΔ3 * q ^ (2 : ℕ)) + ((504 * CΔq) * q ^ (2 : ℕ)) := by
    have := le_trans htri (add_le_add (add_le_add h1 h2) h3)
    simpa [add_assoc] using this
  have hEq :
      (((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ)) + (CΔ3 * q ^ (2 : ℕ)) +
            ((504 * CΔq) * q ^ (2 : ℕ)) =
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq) * q ^ (2 : ℕ) := by
    -- Factor `q^2` and collect coefficients.
    have hEq' :
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ) + CΔ3 * q ^ (2 : ℕ) +
              (504 * CΔq) * q ^ (2 : ℕ) =
          (((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) + CΔ3 + 504 * CΔq) * q ^ (2 : ℕ) := by
      ring
    -- Reassociate on the coefficient side.
    simpa [add_assoc, add_left_comm, add_comm] using hEq'
  exact htmp.trans (le_of_eq hEq)

/-- For large `t`, `φ₄' (it)` differs from `exp (2π t) + 504` by `O(exp (-2π t))`. -/
public lemma exists_phi4'_sub_exp_sub_504_bound_ge :
    ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧
      ∀ t : ℝ, ∀ ht : 0 < t, A ≤ t →
        ‖φ₄' (zI t ht) - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖ ≤
          C * Real.exp (-2 * π * t) := by
  rcases exists_inv_Delta_bound_exp with ⟨CΔinv, AΔ, hCΔinv_pos, hΔinv⟩
  rcases exists_E4_sub_one_sub_240q_bound with ⟨CE4, hCE4_pos, hE4⟩
  rcases exists_Delta_sub_q_bound with ⟨CΔq, hCΔq_pos, hΔq⟩
  rcases exists_Delta_sub_q_sub_neg24_qsq_bound with ⟨CΔ3, hCΔ3_pos, hΔ3⟩
  let A : ℝ := max (1 : ℝ) AΔ
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAΔ : AΔ ≤ A := le_max_right _ _
  -- Uniform bounds using `q ≤ q1` for `t ≥ 1`.
  let q1 : ℝ := Real.exp (-2 * π)
  have hq1_nonneg : 0 ≤ q1 := (Real.exp_pos _).le
  have hq1_lt_one : q1 < 1 := by simpa [q1] using exp_neg_two_pi_lt_one
  let B240 : ℝ := 1 + 240 * q1
  have hB240_pos : 0 < B240 := by
    have : 0 ≤ (240 : ℝ) * q1 := mul_nonneg (by norm_num) hq1_nonneg
    linarith
  -- A convenient constant (positive).
  let C : ℝ := 1 + CΔinv *
      ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq)
  refine ⟨C, A, by positivity, hA1, ?_⟩
  intro t ht0 htA
  have ht1 : 1 ≤ t := le_trans hA1 htA
  let z : ℍ := zI t ht0
  let q : ℝ := Real.exp (-2 * π * t)
  have hq_nonneg : 0 ≤ q := (Real.exp_pos _).le
  have hq_le_q1 : q ≤ q1 := by simpa [q, q1] using q_le_q1 (t := t) ht1
  have hq1_le_one : q1 ≤ 1 := le_of_lt hq1_lt_one
  have hq_le_one : q ≤ 1 := le_trans hq_le_q1 hq1_le_one
  have hΔinv' : ‖(Δ z)⁻¹‖ ≤ CΔinv * Real.exp (2 * π * t) := by
    have : AΔ ≤ z.im := by
      have : AΔ ≤ t := le_trans hAΔ htA
      simpa [z, zI_im t ht0] using this
    simpa [z, zI_im t ht0] using hΔinv z this
  -- `E₄` approximation: `E₄ = 1 + 240q + O(q^2)`.
  have hE4err : ‖E₄ z - ((1 : ℂ) + (240 : ℂ) * (q : ℂ))‖ ≤ CE4 * q ^ (2 : ℕ) := by
    simpa [z, q] using hE4 t ht0 ht1
  -- Squared approximation: `E₄^2 = 1 + 480q + O(q^2)`.
  have hE4sq :
      ‖(E₄ z) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * (q : ℂ))‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ) := by
    set e : ℂ := E₄ z - ((1 : ℂ) + (240 : ℂ) * (q : ℂ))
    have he : ‖e‖ ≤ CE4 * q ^ (2 : ℕ) := by
      simpa [e, sub_eq_add_neg, add_assoc] using hE4err
    have hE : E₄ z = ((1 : ℂ) + (240 : ℂ) * (q : ℂ)) + e := by
      simp [e, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    have hbase_norm : ‖((1 : ℂ) + (240 : ℂ) * (q : ℂ))‖ ≤ B240 := by
      have hqnorm : ‖(q : ℂ)‖ = q := by
        calc
          ‖(q : ℂ)‖ = ‖q‖ := Complex.norm_real q
          _ = q := Real.norm_of_nonneg hq_nonneg
      calc
        ‖((1 : ℂ) + (240 : ℂ) * (q : ℂ))‖
            ≤ ‖(1 : ℂ)‖ + ‖(240 : ℂ) * (q : ℂ)‖ := norm_add_le _ _
        _ = 1 + 240 * q := by
            have hmul : ‖(240 : ℂ) * (q : ℂ)‖ = (240 : ℝ) * q := by
              have h240 : ‖(240 : ℂ)‖ = (240 : ℝ) := by simp
              calc
                ‖(240 : ℂ) * (q : ℂ)‖ = ‖(240 : ℂ)‖ * ‖(q : ℂ)‖ := by simp
                _ = (240 : ℝ) * q := by simpa [h240, hqnorm]
            simpa [norm_one, hmul]
        _ ≤ 1 + 240 * q1 := by
            have : (240 : ℝ) * q ≤ (240 : ℝ) * q1 := by nlinarith [hq_le_q1]
            linarith
        _ = B240 := by simp [B240]
    have haux :=
      norm_base_add_e_sq_sub_one_sub_480q_le (q := q) (CE4 := CE4) (B240 := B240)
        hq_nonneg hq_le_one he hbase_norm
    -- Use the helper bound (it is stated for the same base).
    simpa [hE.symm] using haux
  -- `Δ` approximation at order 2: `Δ = q - 24 q^2 + O(q^3)`.
  have hΔ3err : ‖Δ z - ((q : ℂ) + (-24 : ℂ) * ((q : ℂ) ^ (2 : ℕ)))‖ ≤ CΔ3 * q ^ (3 : ℕ) := by
    simpa [z, q, pow_two] using hΔ3 t ht0 ht1
  -- Multiply by `exp(2πt)` to get `exp(2πt)*Δ = 1 - 24 q + O(q^2)`.
  have hExpΔ :
      ‖(Real.exp (2 * π * t) : ℂ) * Δ z - ((1 : ℂ) + (-24 : ℂ) * (q : ℂ))‖ ≤ CΔ3 * q ^ (2 : ℕ) := by
    have hExpq : (Real.exp (2 * π * t)) * q = 1 := by
      have : Real.exp (2 * π * t) * Real.exp (-2 * π * t) = Real.exp (0 : ℝ) := by
        simpa [Real.exp_add] using (Real.exp_add (2 * π * t) (-2 * π * t)).symm
      simpa [q] using this
    have hExpq2 : (Real.exp (2 * π * t)) * (q ^ (2 : ℕ)) = q := by
      calc
        Real.exp (2 * π * t) * (q ^ (2 : ℕ))
            = (Real.exp (2 * π * t) * q) * q := by
                simp [pow_two, mul_assoc]
        _ = 1 * q := by simp [hExpq]
        _ = q := by simp
    let E : ℂ := (Real.exp (2 * π * t) : ℂ)
    let qC : ℂ := (q : ℂ)
    let approx : ℂ := qC + (-24 : ℂ) * (qC ^ (2 : ℕ))
    have hE_norm : ‖E‖ = Real.exp (2 * π * t) := by
      dsimp [E]
      calc
        ‖(Real.exp (2 * π * t) : ℂ)‖ = ‖Real.exp (2 * π * t)‖ := Complex.norm_real _
        _ = Real.exp (2 * π * t) := Real.norm_of_nonneg (Real.exp_pos _).le
    have hmain :
        ‖E * (Δ z - approx)‖ ≤ (Real.exp (2 * π * t)) * (CΔ3 * q ^ (3 : ℕ)) := by
      calc
        ‖E * (Δ z - approx)‖ = ‖E‖ * ‖Δ z - approx‖ := by simp
        _ = Real.exp (2 * π * t) * ‖Δ z - approx‖ := by simp [hE_norm]
        _ ≤ Real.exp (2 * π * t) * (CΔ3 * q ^ (3 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left (by simpa [approx, qC] using hΔ3err) (Real.exp_pos _).le
    have hExpqC : E * qC = (1 : ℂ) := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hExpq
      simpa [E, qC, Complex.ofReal_mul] using this
    have hExpq2C : E * (qC ^ (2 : ℕ)) = qC := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hExpq2
      simpa [E, qC, Complex.ofReal_mul] using this
    have hdiff' : E * (Δ z - approx) = E * Δ z - ((1 : ℂ) + (-24 : ℂ) * qC) := by
      calc
        E * (Δ z - approx) = E * Δ z - E * approx := by simp [mul_sub]
        _ = E * Δ z - (E * qC + E * ((-24 : ℂ) * (qC ^ (2 : ℕ)))) := by
            simp [approx, mul_add]
        _ = E * Δ z - ((1 : ℂ) + (-24 : ℂ) * qC) := by
            -- `E*qC = 1` and `E*((-24)*qC^2) = (-24)*qC`.
            have h24pos : E * ((24 : ℂ) * (qC ^ (2 : ℕ))) = (24 : ℂ) * qC := by
              calc
                E * ((24 : ℂ) * (qC ^ (2 : ℕ))) = (24 : ℂ) * (E * (qC ^ (2 : ℕ))) := by
                  ring
                _ = (24 : ℂ) * qC := by simp [hExpq2C]
            simp [hExpqC, h24pos]
    have hdiff : E * Δ z - ((1 : ℂ) + (-24 : ℂ) * qC) = E * (Δ z - approx) :=
      hdiff'.symm
    have hRHS :
        (Real.exp (2 * π * t)) * (CΔ3 * q ^ (3 : ℕ)) = CΔ3 * q ^ (2 : ℕ) := by
      have hExpq3 : (Real.exp (2 * π * t)) * (q ^ (3 : ℕ)) = q ^ (2 : ℕ) := by
        calc
          Real.exp (2 * π * t) * (q ^ (3 : ℕ))
              = Real.exp (2 * π * t) * ((q ^ (2 : ℕ)) * q) := by
                  simp [pow_succ, mul_assoc]
          _ = (Real.exp (2 * π * t) * q) * (q ^ (2 : ℕ)) := by
                  simp [mul_assoc, mul_comm]
          _ = (q ^ (2 : ℕ)) := by simp [hExpq]
      calc
        Real.exp (2 * π * t) * (CΔ3 * q ^ (3 : ℕ))
            = CΔ3 * (Real.exp (2 * π * t) * (q ^ (3 : ℕ))) := by ring
        _ = CΔ3 * q ^ (2 : ℕ) := by simp [hExpq3]
    have hmain' : ‖E * Δ z - ((1 : ℂ) + (-24 : ℂ) * qC)‖ ≤
        (Real.exp (2 * π * t)) * (CΔ3 * q ^ (3 : ℕ)) := by
      simpa [hdiff.symm] using hmain
    -- Conclude.
    have hfinal : ‖E * Δ z - ((1 : ℂ) + (-24 : ℂ) * qC)‖ ≤ CΔ3 * q ^ (2 : ℕ) := by
      simpa [hRHS] using hmain'
    simpa [E, qC] using hfinal
  -- `Δ = q + O(q^2)`.
  have hΔ2err : ‖Δ z - (q : ℂ)‖ ≤ CΔq * q ^ (2 : ℕ) := by
    simpa [z, q] using hΔq t ht0 ht1
  -- Combine the cancellations in the numerator.
  have hnum :
      ‖(E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq) * q ^ (2 : ℕ) := by
    simpa using
      (phi4_numerator_bound (t := t) (q := q) (z := z)
        (B240 := B240) (CE4 := CE4) (CΔ3 := CΔ3) (CΔq := CΔq)
        hE4sq hExpΔ hΔ2err)
  -- Rewrite `φ₄'` and apply the numerator bound together with the inverse-Δ bound.
  have hrew :
      φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ) =
        ((E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)) / (Δ z) := by
    have hΔ : (Δ z) ≠ 0 := Δ_ne_zero z
    dsimp [φ₄']
    field_simp [hΔ]
  have :
      ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖ ≤
        (CΔinv * ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq)) * q := by
    set K : ℝ := (240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq
    set num : ℂ :=
      (E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)
    have hK : 0 ≤ K := by
      dsimp [K]
      nlinarith [hB240_pos.le, hCE4_pos.le, hCΔ3_pos.le, hCΔq_pos.le]
    have hrew_num :
        φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ) = num / (Δ z) := by
      simpa [num] using hrew
    calc
      ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖ = ‖num / (Δ z)‖ := by
        simpa using congrArg norm hrew_num
      _ = ‖num‖ * ‖(Δ z)⁻¹‖ := by
        simp [div_eq_mul_inv]
      _ ≤ (K * q ^ (2 : ℕ)) * (CΔinv * Real.exp (2 * π * t)) := by
            have h1 :
                ‖num‖ ≤ K * q ^ (2 : ℕ) := by
              simpa [K, num] using hnum
            have h2 : ‖(Δ z)⁻¹‖ ≤ CΔinv * Real.exp (2 * π * t) := hΔinv'
            exact mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hK (pow_nonneg hq_nonneg _))
      _ = (CΔinv * K) * q := by
        -- `q^2 * exp(2πt) = q` since `q = exp(-2πt)`.
        have hq2 : q ^ (2 : ℕ) * Real.exp (2 * π * t) = q := by
          simpa [q] using exp_neg_two_pi_pow_two_mul_exp_two_pi (t := t)
        calc
          (K * q ^ (2 : ℕ)) * (CΔinv * Real.exp (2 * π * t))
              = (CΔinv * K) * (q ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
                  ring
          _ = (CΔinv * K) * q := by simp [hq2]
  -- Enlarge the constant by `+1` and rewrite `q`.
  have hle :
      (CΔinv * ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq)) * q ≤ C * q := by
    have : CΔinv * ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq) ≤ C := by
      dsimp [C]; linarith
    exact mul_le_mul_of_nonneg_right this hq_nonneg
  simpa [z, q, A, C] using (this.trans hle)


end

end MagicFunction.g.CohnElkies.IntegralReps
