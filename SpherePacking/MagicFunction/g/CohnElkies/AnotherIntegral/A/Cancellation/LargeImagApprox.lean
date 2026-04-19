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
  rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf

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
  let q1 : ℝ := Real.exp (-2 * π)
  have hq1 : q1 < 1 := by simpa [q1] using exp_neg_two_pi_lt_one
  let E4B : ℝ := 1 + CE4 * q1
  have hE4B_pos : 0 < E4B := by
    have : 0 ≤ CE4 * q1 := mul_nonneg hCE4_pos.le (Real.exp_pos _).le; linarith
  let C : ℝ := 1 + CΔinv * (E4B * CA + 720 * (CE4 + CΔq))
  refine ⟨C, A, by positivity, hA1, ?_⟩
  intro t ht0 htA
  have ht1 : 1 ≤ t := le_trans hA1 htA
  let z : ℍ := zI t ht0
  let q : ℝ := Real.exp (-2 * π * t)
  have hq_nonneg : 0 ≤ q := (Real.exp_pos _).le
  have hq_le_q1 : q ≤ q1 := by simpa [q, q1] using q_le_q1 (t := t) ht1
  have hE4norm : ‖E₄ z‖ ≤ E4B := by
    have hE4sub' : ‖E₄ z - (1 : ℂ)‖ ≤ CE4 * q1 :=
      (by simpa [z, q] using hE4 t ht0 ht1 : ‖E₄ z - (1 : ℂ)‖ ≤ CE4 * q).trans
        (mul_le_mul_of_nonneg_left hq_le_q1 hCE4_pos.le)
    have htri : ‖E₄ z‖ ≤ ‖E₄ z - (1 : ℂ)‖ + 1 := by
      simpa using norm_add_le (E₄ z - (1 : ℂ)) (1 : ℂ)
    simp only [E4B]; linarith
  have hAerr : ‖(E₂ z) * (E₄ z) - (E₆ z) - (720 : ℂ) * (q : ℂ)‖ ≤ CA * q ^ (2 : ℕ) := by
    simpa [z, q] using hAq t ht0 ht1
  have hΔerr : ‖Δ z - (q : ℂ)‖ ≤ CΔq * q ^ (2 : ℕ) := by
    simpa [z, q] using hΔq t ht0 ht1
  have hΔinv' : ‖(Δ z)⁻¹‖ ≤ CΔinv * Real.exp (2 * π * t) := by
    simpa [z, zI_im t ht0] using hΔinv z
      (by simpa [z, zI_im t ht0] using hAΔ.trans htA)
  have hE4qΔ : ‖E₄ z * (q : ℂ) - Δ z‖ ≤ (CE4 + CΔq) * q ^ (2 : ℕ) := by
    have hE4sub : ‖E₄ z - (1 : ℂ)‖ ≤ CE4 * q := by simpa [z, q] using hE4 t ht0 ht1
    have hqnorm : ‖(q : ℂ)‖ = q := by simp [Complex.norm_real, abs_of_nonneg hq_nonneg]
    have h1 : ‖(E₄ z - (1 : ℂ)) * (q : ℂ)‖ ≤ CE4 * q ^ (2 : ℕ) := by
      rw [norm_mul, hqnorm, pow_two, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hE4sub hq_nonneg
    have h2 : ‖(q : ℂ) - Δ z‖ ≤ CΔq * q ^ (2 : ℕ) := by simpa [norm_sub_rev] using hΔerr
    have hsum : E₄ z * (q : ℂ) - Δ z = (E₄ z - (1 : ℂ)) * (q : ℂ) + ((q : ℂ) - Δ z) := by ring
    calc
      ‖E₄ z * (q : ℂ) - Δ z‖ = ‖(E₄ z - (1 : ℂ)) * (q : ℂ) + ((q : ℂ) - Δ z)‖ :=
            congrArg norm hsum
      _ ≤ ‖(E₄ z - (1 : ℂ)) * (q : ℂ)‖ + ‖(q : ℂ) - Δ z‖ := norm_add_le _ _
      _ ≤ CE4 * q ^ (2 : ℕ) + CΔq * q ^ (2 : ℕ) := by linarith
      _ = (CE4 + CΔq) * q ^ (2 : ℕ) := by ring
  have hrew :
      φ₂' z - (720 : ℂ) =
        ((E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)) / (Δ z) := by
    dsimp [φ₂']; field_simp [Δ_ne_zero z]
  have hnum :
      ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)‖ ≤
        (E4B * CA + 720 * (CE4 + CΔq)) * q ^ (2 : ℕ) := by
    set Aterm : ℂ := (E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z) - (720 : ℂ) * (q : ℂ))
    set Bterm : ℂ := (720 : ℂ) * (E₄ z * (q : ℂ) - Δ z)
    have hdecomp :
        (E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z) = Aterm + Bterm := by
      simp only [Aterm, Bterm]; ring
    have hA : ‖Aterm‖ ≤ (E4B * CA) * q ^ (2 : ℕ) := by
      have hmul : ‖Aterm‖ ≤ E4B * (CA * q ^ (2 : ℕ)) :=
        norm_mul_le_of_le hE4norm (hAq t ht0 ht1)
      linarith
    have hB : ‖Bterm‖ ≤ (720 * (CE4 + CΔq)) * q ^ (2 : ℕ) := by
      calc ‖Bterm‖ = 720 * ‖E₄ z * (q : ℂ) - Δ z‖ := by simp [Bterm]
        _ ≤ 720 * ((CE4 + CΔq) * q ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left hE4qΔ (by norm_num)
        _ = (720 * (CE4 + CΔq)) * q ^ (2 : ℕ) := by ring
    calc ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)‖
          = ‖Aterm + Bterm‖ := congrArg norm hdecomp
      _ ≤ ‖Aterm‖ + ‖Bterm‖ := norm_add_le _ _
      _ ≤ (E4B * CA + 720 * (CE4 + CΔq)) * q ^ (2 : ℕ) := by linarith
  have hq2 : q ^ (2 : ℕ) * Real.exp (2 * π * t) = q := by
    simpa [q] using exp_neg_two_pi_pow_two_mul_exp_two_pi (t := t)
  have : ‖φ₂' z - (720 : ℂ)‖ ≤ (CΔinv * (E4B * CA + 720 * (CE4 + CΔq))) * q := by
    set K : ℝ := E4B * CA + 720 * (CE4 + CΔq)
    have hK : 0 ≤ K * q ^ (2 : ℕ) := by positivity
    calc ‖φ₂' z - (720 : ℂ)‖
          = ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)‖ * ‖(Δ z)⁻¹‖ := by
              simp [hrew, div_eq_mul_inv]
      _ ≤ (K * q ^ (2 : ℕ)) * (CΔinv * Real.exp (2 * π * t)) :=
            mul_le_mul (by simpa [K] using hnum) hΔinv' (norm_nonneg _) hK
      _ = (CΔinv * K) * q := by rw [show (K * q ^ 2) * (CΔinv * Real.exp (2*π*t)) =
            (CΔinv * K) * (q ^ 2 * Real.exp (2*π*t)) from by ring, hq2]
  have hle : (CΔinv * (E4B * CA + 720 * (CE4 + CΔq))) * q ≤ C * q :=
    mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hq_nonneg
  simpa [z, q, A, C] using (this.trans hle)

lemma norm_base240_sq_sub_target480_eq {q : ℝ} :
    ‖(((1 : ℂ) + (240 : ℂ) * (q : ℂ)) ^ (2 : ℕ) -
          ((1 : ℂ) + (480 : ℂ) * (q : ℂ)))‖ =
        (240 ^ 2 : ℝ) * q ^ (2 : ℕ) := by
  have h : ((1 : ℂ) + (240 : ℂ) * (q : ℂ)) ^ (2 : ℕ) -
          ((1 : ℂ) + (480 : ℂ) * (q : ℂ)) = (240 ^ 2 : ℂ) * (q : ℂ) ^ (2 : ℕ) := by ring
  simp_all

lemma norm_base_add_e_sq_sub_one_sub_480q_le
    {q CE4 B240 : ℝ} (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1) {e : ℂ}
    (he : ‖e‖ ≤ CE4 * q ^ (2 : ℕ))
    (hbase_norm : ‖((1 : ℂ) + (240 : ℂ) * (q : ℂ))‖ ≤ B240) :
    ‖((((1 : ℂ) + (240 : ℂ) * (q : ℂ)) + e) ^ (2 : ℕ) -
          ((1 : ℂ) + (480 : ℂ) * (q : ℂ)))‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ) := by
  set b : ℂ := (1 : ℂ) + (240 : ℂ) * (q : ℂ)
  set t : ℂ := (1 : ℂ) + (480 : ℂ) * (q : ℂ)
  have hB240 : 0 ≤ B240 := (norm_nonneg _).trans hbase_norm
  have hbase2 : ‖b ^ (2 : ℕ) - t‖ ≤ (240 ^ 2 : ℝ) * q ^ (2 : ℕ) := by
    simpa [b, t] using (norm_base240_sq_sub_target480_eq (q := q)).le
  have hlin : ‖(2 : ℂ) * b * e‖ ≤ (2 * B240 * CE4) * q ^ (2 : ℕ) := by
    calc ‖(2 : ℂ) * b * e‖ = 2 * ‖b‖ * ‖e‖ := by simp [mul_assoc]
      _ ≤ 2 * B240 * (CE4 * q ^ (2 : ℕ)) := by gcongr
      _ = (2 * B240 * CE4) * q ^ (2 : ℕ) := by ring
  have hquad : ‖e ^ (2 : ℕ)‖ ≤ (CE4 ^ 2) * q ^ (2 : ℕ) := by
    have hq4 : q ^ (4 : ℕ) ≤ q ^ (2 : ℕ) :=
      pow_le_pow_of_le_one hq_nonneg hq_le_one (by decide)
    calc ‖e ^ (2 : ℕ)‖ = ‖e‖ ^ (2 : ℕ) := by simp [norm_pow]
      _ ≤ (CE4 * q ^ (2 : ℕ)) ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) he _
      _ = (CE4 ^ 2) * q ^ (4 : ℕ) := by ring
      _ ≤ (CE4 ^ 2) * q ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hq4 (sq_nonneg _)
  have htri : ‖(b + e) ^ (2 : ℕ) - t‖ ≤
      ‖b ^ (2 : ℕ) - t‖ + ‖(2 : ℂ) * b * e‖ + ‖e ^ (2 : ℕ)‖ := by
    have hdecomp : (b + e) ^ (2 : ℕ) - t = (b ^ (2 : ℕ) - t) + (2 : ℂ) * b * e + e ^ (2 : ℕ) := by
      ring
    simpa [hdecomp] using norm_add₃_le (a := b ^ (2 : ℕ) - t)
      (b := (2 : ℂ) * b * e) (c := e ^ (2 : ℕ))
  linarith

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
  set A : ℂ := (E₄ z) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * qC)
  set B : ℂ := (Real.exp (2 * π * t) : ℂ) * (Δ z) - ((1 : ℂ) + (-24 : ℂ) * qC)
  set C : ℂ := (504 : ℂ) * (Δ z - qC)
  have hdecomp : (E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) -
      (504 : ℂ) * (Δ z) = A - B - C := by simp only [A, B, C]; ring
  have hterm3 : ‖C‖ ≤ (504 * CΔq) * q ^ (2 : ℕ) := by
    calc ‖C‖ = 504 * ‖Δ z - qC‖ := by simp [C]
      _ ≤ 504 * (CΔq * q ^ (2 : ℕ)) := by gcongr
      _ = (504 * CΔq) * q ^ (2 : ℕ) := by ring
  calc ‖(E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)‖
        = ‖A - B - C‖ := by rw [hdecomp]
    _ ≤ ‖A‖ + ‖B‖ + ‖C‖ := (norm_sub_le _ C).trans (by linarith [norm_sub_le A B])
    _ ≤ _ := by linarith

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
  let q1 : ℝ := Real.exp (-2 * π)
  have hq1_nonneg : 0 ≤ q1 := (Real.exp_pos _).le
  have hq1_lt_one : q1 < 1 := by simpa [q1] using exp_neg_two_pi_lt_one
  let B240 : ℝ := 1 + 240 * q1
  have hB240_pos : 0 < B240 := by positivity
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
    simpa [z, zI_im t ht0] using hΔinv z
      (by simpa [z, zI_im t ht0] using le_trans hAΔ htA)
  have hE4err : ‖E₄ z - ((1 : ℂ) + (240 : ℂ) * (q : ℂ))‖ ≤ CE4 * q ^ (2 : ℕ) := by
    simpa [z, q] using hE4 t ht0 ht1
  have hE4sq :
      ‖(E₄ z) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * (q : ℂ))‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ) := by
    set e : ℂ := E₄ z - ((1 : ℂ) + (240 : ℂ) * (q : ℂ))
    have he : ‖e‖ ≤ CE4 * q ^ (2 : ℕ) := by
      simpa [e, sub_eq_add_neg, add_assoc] using hE4err
    have hE : E₄ z = ((1 : ℂ) + (240 : ℂ) * (q : ℂ)) + e := by
      simp [e, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    have hbase_norm : ‖((1 : ℂ) + (240 : ℂ) * (q : ℂ))‖ ≤ B240 := by
      calc ‖((1 : ℂ) + (240 : ℂ) * (q : ℂ))‖
            ≤ ‖(1 : ℂ)‖ + ‖(240 : ℂ) * (q : ℂ)‖ := norm_add_le _ _
        _ = 1 + 240 * q := by simp [abs_of_nonneg hq_nonneg]
        _ ≤ 1 + 240 * q1 := by linarith [hq_le_q1]
        _ = B240 := rfl
    simpa [hE.symm] using
      norm_base_add_e_sq_sub_one_sub_480q_le (q := q) (CE4 := CE4) (B240 := B240)
        hq_nonneg hq_le_one he hbase_norm
  have hΔ3err : ‖Δ z - ((q : ℂ) + (-24 : ℂ) * ((q : ℂ) ^ (2 : ℕ)))‖ ≤ CΔ3 * q ^ (3 : ℕ) := by
    simpa [z, q, pow_two] using hΔ3 t ht0 ht1
  have hExpq : (Real.exp (2 * π * t)) * q = 1 := by
    rw [show q = Real.exp (-2 * π * t) from rfl, ← Real.exp_add]; simp
  have hExpq3 : (Real.exp (2 * π * t)) * (q ^ (3 : ℕ)) = q ^ (2 : ℕ) := by
    rw [show Real.exp (2 * π * t) * (q ^ (3 : ℕ)) = (Real.exp (2*π*t) * q) * q ^ (2:ℕ) from by
      ring, hExpq, one_mul]
  have hExpΔ :
      ‖(Real.exp (2 * π * t) : ℂ) * Δ z - ((1 : ℂ) + (-24 : ℂ) * (q : ℂ))‖ ≤ CΔ3 * q ^ (2 : ℕ) := by
    set E : ℂ := (Real.exp (2 * π * t) : ℂ)
    set qC : ℂ := (q : ℂ)
    set approx : ℂ := qC + (-24 : ℂ) * (qC ^ (2 : ℕ))
    have hExpqC : E * qC = (1 : ℂ) := by
      simpa [E, qC, Complex.ofReal_mul] using congrArg (fun x : ℝ => (x : ℂ)) hExpq
    have hE2 : E * (qC ^ 2) = qC := by
      rw [show E * (qC ^ 2) = (E * qC) * qC from by ring, hExpqC, one_mul]
    have happ : E * approx = (1 : ℂ) + (-24 : ℂ) * qC := by
      simp only [approx, mul_add]
      rw [show E * ((-24 : ℂ) * (qC ^ 2)) = (-24) * (E * (qC ^ 2)) from by ring, hE2, hExpqC]
    have hdiff : E * Δ z - ((1 : ℂ) + (-24 : ℂ) * qC) = E * (Δ z - approx) := by
      rw [mul_sub, happ]
    rw [hdiff, norm_mul, show ‖E‖ = Real.exp (2 * π * t) from norm_ofReal_exp _]
    calc Real.exp (2*π*t) * ‖Δ z - approx‖
        ≤ Real.exp (2*π*t) * (CΔ3 * q ^ (3 : ℕ)) :=
          mul_le_mul_of_nonneg_left (by simpa [approx, qC] using hΔ3err) (Real.exp_pos _).le
      _ = CΔ3 * q ^ (2 : ℕ) := by rw [← mul_assoc, mul_comm _ CΔ3, mul_assoc, hExpq3]
  have hnum :
      ‖(E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq) * q ^ (2 : ℕ) :=
    phi4_numerator_bound hE4sq hExpΔ (hΔq t ht0 ht1)
  have hrew :
      φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ) =
        ((E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)) / (Δ z) := by
    dsimp [φ₄']; field_simp [Δ_ne_zero z]
  have hq2 : q ^ (2 : ℕ) * Real.exp (2 * π * t) = q := by
    simpa [q] using exp_neg_two_pi_pow_two_mul_exp_two_pi (t := t)
  have : ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖ ≤
      (CΔinv * ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq)) * q := by
    set K : ℝ := (240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq
    have hK : 0 ≤ K * q ^ (2 : ℕ) := by positivity
    calc ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖
          = ‖(E₄ z)^2 - (Real.exp (2*π*t) : ℂ) * Δ z - (504:ℂ) * Δ z‖ * ‖(Δ z)⁻¹‖ := by
            rw [hrew, norm_div, div_eq_mul_inv, norm_inv]
      _ ≤ (K * q ^ (2 : ℕ)) * (CΔinv * Real.exp (2 * π * t)) :=
          mul_le_mul hnum hΔinv' (norm_nonneg _) hK
      _ = (CΔinv * K) * q := by rw [show (K * q^2) * (CΔinv * Real.exp (2*π*t)) =
            (CΔinv * K) * (q^2 * Real.exp (2*π*t)) from by ring, hq2]
  have hle : (CΔinv * ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq)) * q ≤ C * q :=
    mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hq_nonneg
  simpa [z, q, A, C] using this.trans hle

end

end MagicFunction.g.CohnElkies.IntegralReps
