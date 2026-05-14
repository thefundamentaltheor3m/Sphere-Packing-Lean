module
public import Mathlib.Init
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.ImagAxis
import SpherePacking.ForMathlib.IntegrablePowMulExp

/-!
# Large-imaginary asymptotics and integrability for `AnotherIntegral.A`

* Uniform asymptotic error bounds for `φ₂'` and `φ₄'` along the imaginary axis
  (merged from `LaplaceA.LargeImagApprox`).
* Integrability of the `AnotherIntegral.A` integrand on `(0, ∞)` for `0 < u`.
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

/-! ## Large-imaginary asymptotics (merged from `LargeImagApprox`) -/

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
  let q1 : ℝ := Real.exp (-2 * π)
  let E4B : ℝ := 1 + CE4 * q1
  let C : ℝ := 1 + CΔinv * (E4B * CA + 720 * (CE4 + CΔq))
  have hA1 : 1 ≤ A := le_max_left _ _
  refine ⟨C, A, by positivity, hA1, ?_⟩
  intro t ht0 htA
  have ht1 : 1 ≤ t := le_trans hA1 htA
  let z : ℍ := zI t ht0
  let q : ℝ := Real.exp (-2 * π * t)
  have hq_nonneg : 0 ≤ q := (Real.exp_pos _).le
  have hq_le_q1 : q ≤ q1 := by simpa [q, q1] using q_le_q1 (t := t) ht1
  have hE4sub : ‖E₄ z - (1 : ℂ)‖ ≤ CE4 * q := by simpa [z, q] using hE4 t ht0 ht1
  have hE4norm : ‖E₄ z‖ ≤ E4B := by
    simp only [E4B]; linarith [hE4sub.trans (mul_le_mul_of_nonneg_left hq_le_q1 hCE4_pos.le),
      show ‖E₄ z‖ ≤ ‖E₄ z - (1 : ℂ)‖ + 1 from by simpa using norm_add_le (E₄ z - (1 : ℂ)) 1]
  have hΔerr : ‖Δ z - (q : ℂ)‖ ≤ CΔq * q ^ (2 : ℕ) := by
    simpa [z, q] using hΔq t ht0 ht1
  have hΔinv' : ‖(Δ z)⁻¹‖ ≤ CΔinv * Real.exp (2 * π * t) := by
    simpa [z, zI_im t ht0] using hΔinv z
      (by simpa [z, zI_im t ht0] using (le_max_right _ _ : AΔ ≤ A).trans htA)
  have hE4qΔ : ‖E₄ z * (q : ℂ) - Δ z‖ ≤ (CE4 + CΔq) * q ^ (2 : ℕ) := by
    have h1 : ‖(E₄ z - (1 : ℂ)) * (q : ℂ)‖ ≤ CE4 * q ^ (2 : ℕ) := by
      rw [norm_mul, show ‖(q : ℂ)‖ = q from by simp [abs_of_nonneg hq_nonneg], pow_two, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hE4sub hq_nonneg
    calc ‖E₄ z * (q : ℂ) - Δ z‖
          = ‖(E₄ z - (1 : ℂ)) * (q : ℂ) + ((q : ℂ) - Δ z)‖ := by congr 1; ring
      _ ≤ _ + _ := norm_add_le _ _
      _ ≤ _ := by linarith [show ‖(q : ℂ) - Δ z‖ ≤ CΔq * q ^ (2 : ℕ) from by
                    simpa [norm_sub_rev] using hΔerr]
  have hrew : φ₂' z - (720 : ℂ) =
      ((E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)) / (Δ z) := by
    dsimp [φ₂']; field_simp [Δ_ne_zero z]
  have hnum :
      ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)‖ ≤
        (E4B * CA + 720 * (CE4 + CΔq)) * q ^ (2 : ℕ) := by
    have hB : ‖(720 : ℂ) * (E₄ z * (q : ℂ) - Δ z)‖ ≤ (720 * (CE4 + CΔq)) * q ^ (2 : ℕ) := by
      rw [norm_mul, Complex.norm_ofNat]
      linarith [mul_le_mul_of_nonneg_left hE4qΔ (by norm_num : (0:ℝ) ≤ 720)]
    calc ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)‖
          = ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z) - (720 : ℂ) * (q : ℂ)) +
              (720 : ℂ) * (E₄ z * (q : ℂ) - Δ z)‖ := by congr 1; ring
      _ ≤ _ + _ := norm_add_le _ _
      _ ≤ _ := by linarith [norm_mul_le_of_le hE4norm (hAq t ht0 ht1)]
  have hq2 : q ^ (2 : ℕ) * Real.exp (2 * π * t) = q := by
    simp only [q]; rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
  have : ‖φ₂' z - (720 : ℂ)‖ ≤ (CΔinv * (E4B * CA + 720 * (CE4 + CΔq))) * q := by
    set K : ℝ := E4B * CA + 720 * (CE4 + CΔq)
    calc ‖φ₂' z - (720 : ℂ)‖
          = ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)‖ * ‖(Δ z)⁻¹‖ := by
              simp [hrew, div_eq_mul_inv]
      _ ≤ (K * q ^ (2 : ℕ)) * (CΔinv * Real.exp (2 * π * t)) := mul_le_mul
            (by simpa [K] using hnum) hΔinv' (norm_nonneg _) (by positivity)
      _ = (CΔinv * K) * q := by linear_combination (CΔinv * K) * hq2
  exact this.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hq_nonneg)

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
    rw [show b ^ (2 : ℕ) - t = (240 ^ 2 : ℂ) * (q : ℂ) ^ (2 : ℕ) by simp [b, t]; ring]; simp
  have hlin : ‖(2 : ℂ) * b * e‖ ≤ (2 * B240 * CE4) * q ^ (2 : ℕ) := by
    rw [show ‖(2 : ℂ) * b * e‖ = 2 * ‖b‖ * ‖e‖ by simp [mul_assoc]]
    nlinarith [mul_le_mul hbase_norm he (norm_nonneg _) hB240, norm_nonneg b, norm_nonneg e]
  have hquad : ‖e ^ (2 : ℕ)‖ ≤ (CE4 ^ 2) * q ^ (2 : ℕ) := by
    rw [show ‖e ^ (2 : ℕ)‖ = ‖e‖ ^ (2 : ℕ) by simp [norm_pow]]
    calc ‖e‖ ^ (2 : ℕ) ≤ (CE4 * q ^ (2 : ℕ)) ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) he _
      _ = (CE4 ^ 2) * q ^ (4 : ℕ) := by ring
      _ ≤ (CE4 ^ 2) * q ^ (2 : ℕ) := mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hq_nonneg hq_le_one (by decide)) (sq_nonneg _)
  have heq : (b + e) ^ (2 : ℕ) - t = (b ^ (2 : ℕ) - t) + (2 : ℂ) * b * e + e ^ (2 : ℕ) := by ring
  linarith [heq ▸ norm_add₃_le (a := b ^ (2 : ℕ) - t) (b := (2 : ℂ) * b * e) (c := e ^ (2 : ℕ))]

lemma phi4_numerator_bound
    {t q : ℝ} {z : ℍ} {B240 CE4 CΔ3 CΔq : ℝ}
    (hE4sq : ‖(E₄ z) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * (q : ℂ))‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ))
    (hExpΔ : ‖(Real.exp (2 * π * t) : ℂ) * (Δ z) - ((1 : ℂ) + (-24 : ℂ) * (q : ℂ))‖ ≤
        CΔ3 * q ^ (2 : ℕ))
    (hΔ2err : ‖Δ z - (q : ℂ)‖ ≤ CΔq * q ^ (2 : ℕ)) :
    ‖(E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq) * q ^ (2 : ℕ) := by
  set qC : ℂ := (q : ℂ)
  set A : ℂ := (E₄ z) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * qC)
  set B : ℂ := (Real.exp (2 * π * t) : ℂ) * (Δ z) - ((1 : ℂ) + (-24 : ℂ) * qC)
  set C : ℂ := (504 : ℂ) * (Δ z - qC)
  have hterm3 : ‖C‖ ≤ (504 * CΔq) * q ^ (2 : ℕ) := by
    rw [show ‖C‖ = 504 * ‖Δ z - qC‖ by simp [C]]; nlinarith [hΔ2err]
  calc ‖(E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)‖
        = ‖A - B - C‖ := by simp only [A, B, C]; ring_nf
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
  let q1 : ℝ := Real.exp (-2 * π)
  let B240 : ℝ := 1 + 240 * q1
  let C : ℝ := 1 + CΔinv * ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq)
  have hA1 : 1 ≤ A := le_max_left _ _
  refine ⟨C, A, by positivity, hA1, ?_⟩
  intro t ht0 htA
  have ht1 : 1 ≤ t := le_trans hA1 htA
  let z : ℍ := zI t ht0
  let q : ℝ := Real.exp (-2 * π * t)
  have hq_nonneg : 0 ≤ q := (Real.exp_pos _).le
  have hq_le_q1 : q ≤ q1 := by simpa [q, q1] using q_le_q1 (t := t) ht1
  have hq_le_one : q ≤ 1 :=
    hq_le_q1.trans (by simpa [q1] using exp_neg_two_pi_lt_one.le)
  have hΔinv' : ‖(Δ z)⁻¹‖ ≤ CΔinv * Real.exp (2 * π * t) := by
    simpa [z, zI_im t ht0] using hΔinv z
      (by simpa [z, zI_im t ht0] using (le_max_right _ _ : AΔ ≤ A).trans htA)
  have hE4err : ‖E₄ z - ((1 : ℂ) + (240 : ℂ) * (q : ℂ))‖ ≤ CE4 * q ^ (2 : ℕ) := by
    simpa [z, q] using hE4 t ht0 ht1
  have hE4sq :
      ‖(E₄ z) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * (q : ℂ))‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ) := by
    set e : ℂ := E₄ z - ((1 : ℂ) + (240 : ℂ) * (q : ℂ))
    have he : ‖e‖ ≤ CE4 * q ^ (2 : ℕ) := by simpa [e, sub_eq_add_neg, add_assoc] using hE4err
    have hE : E₄ z = ((1 : ℂ) + (240 : ℂ) * (q : ℂ)) + e := by
      simp [e, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    have hbase_norm : ‖((1 : ℂ) + (240 : ℂ) * (q : ℂ))‖ ≤ B240 := by
      have := norm_add_le ((1 : ℂ)) ((240 : ℂ) * (q : ℂ))
      simp [abs_of_nonneg hq_nonneg, B240] at this ⊢; linarith [hq_le_q1]
    simpa [hE.symm] using norm_base_add_e_sq_sub_one_sub_480q_le (q := q) (CE4 := CE4)
      (B240 := B240) hq_nonneg hq_le_one he hbase_norm
  have hΔ3err : ‖Δ z - ((q : ℂ) + (-24 : ℂ) * ((q : ℂ) ^ (2 : ℕ)))‖ ≤ CΔ3 * q ^ (3 : ℕ) := by
    simpa [z, q, pow_two] using hΔ3 t ht0 ht1
  have hExpq : (Real.exp (2 * π * t)) * q = 1 := by rw [← Real.exp_add]; simp
  have hExpΔ :
      ‖(Real.exp (2 * π * t) : ℂ) * Δ z - ((1 : ℂ) + (-24 : ℂ) * (q : ℂ))‖ ≤ CΔ3 * q ^ (2 : ℕ) := by
    set E : ℂ := (Real.exp (2 * π * t) : ℂ)
    set qC : ℂ := (q : ℂ)
    set approx : ℂ := qC + (-24 : ℂ) * (qC ^ (2 : ℕ))
    have hExpqC : E * qC = (1 : ℂ) := by
      simpa [E, qC, Complex.ofReal_mul] using congrArg (fun x : ℝ => (x : ℂ)) hExpq
    rw [show E * Δ z - ((1 : ℂ) + (-24 : ℂ) * qC) = E * (Δ z - approx) by
        simp only [approx, mul_sub, mul_add]
        linear_combination hExpqC + (-24 : ℂ) * (qC * hExpqC),
      norm_mul, show ‖E‖ = Real.exp (2 * π * t) from norm_ofReal_exp _]
    calc Real.exp (2*π*t) * ‖Δ z - approx‖
        ≤ Real.exp (2*π*t) * (CΔ3 * q ^ (3 : ℕ)) := mul_le_mul_of_nonneg_left
            (by simpa [approx, qC] using hΔ3err) (Real.exp_pos _).le
      _ = CΔ3 * q ^ (2 : ℕ) := by linear_combination CΔ3 * (q ^ 2 * hExpq)
  have hrew : φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ) =
      ((E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)) / (Δ z) := by
    dsimp [φ₄']; field_simp [Δ_ne_zero z]
  have hq2 : q ^ (2 : ℕ) * Real.exp (2 * π * t) = q := by
    simp only [q]; rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
  have : ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖ ≤
      (CΔinv * ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq)) * q := by
    set K : ℝ := (240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq
    calc ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖
          = ‖(E₄ z)^2 - (Real.exp (2*π*t) : ℂ) * Δ z - (504:ℂ) * Δ z‖ * ‖(Δ z)⁻¹‖ := by
            rw [hrew, norm_div, div_eq_mul_inv, norm_inv]
      _ ≤ (K * q ^ (2 : ℕ)) * (CΔinv * Real.exp (2 * π * t)) := mul_le_mul
          (phi4_numerator_bound hE4sq hExpΔ (hΔq t ht0 ht1)) hΔinv' (norm_nonneg _) (by positivity)
      _ = (CΔinv * K) * q := by linear_combination (CΔinv * K) * hq2
  exact this.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hq_nonneg)

/-! ## Integrability of `AnotherIntegral.A` integrand -/

private lemma continuousOn_phi0''_Idiv {s : Set ℝ} (hs : ∀ t ∈ s, 0 < t) :
    ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) s :=
  ((by simpa [upperHalfPlaneSet] using MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn :
    ContinuousOn (fun z : ℂ => φ₀'' z) {z : ℂ | 0 < z.im})).comp
    (continuous_const.continuousOn.div continuous_ofReal.continuousOn
      fun t ht => mod_cast (hs t ht).ne')
    fun t ht => by simpa [imag_I_div] using inv_pos.2 (hs t ht)

private def cancelExpr (t : ℝ) : ℂ :=
  ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
    ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
    ((8640 / π : ℝ) : ℂ) * t - ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)

lemma exists_phi0_cancellation_bound :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
        ‖cancelExpr t‖ ≤ C * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
  rcases norm_φ₀_imag_le with ⟨C₀, hC₀pos, hφ₀⟩
  rcases exists_phi2'_sub_720_bound_ge with ⟨C₂, A₂, hC₂pos, hA₂, hφ₂⟩
  rcases exists_phi4'_sub_exp_sub_504_bound_ge with ⟨C₄, A₄, hC₄pos, hA₄, hφ₄⟩
  let A : ℝ := max A₂ A₄
  have hrewrite :
      ∀ {t : ℝ} (ht0 : 0 < t),
        cancelExpr t =
          (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ (zI t ht0) -
              ((12 / π : ℝ) : ℂ) * t * (φ₂' (zI t ht0) - (720 : ℂ)) +
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
                (φ₄' (zI t ht0) - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))) := by
    intro t ht0
    let z : ℍ := zI t ht0
    have hzsq : (z : ℂ) ^ (2 : ℕ) = -((t ^ (2 : ℕ) : ℝ) : ℂ) := by
      dsimp [z, zI]; push_cast; simp [mul_pow]
    have hcoe : ((ModularGroup.S • z : ℍ) : ℂ) = (Complex.I : ℂ) / (t : ℂ) := by
      rw [show ModularGroup.S • z = zI t⁻¹ (inv_pos.2 ht0) by
        ext1; simpa [zI, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using
          ModularGroup.coe_S_smul (z := zI t ht0)]
      simp [zI, div_eq_mul_inv]
    have hST' :
        ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ (ModularGroup.S • z) =
          ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z -
            ((12 / π : ℝ) : ℂ) * t * φ₂' z +
            ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * φ₄' z := by
      have hneg' : (t : ℂ) * ((t : ℂ) * φ₀ (ModularGroup.S • z)) =
          (t : ℂ) * ((t : ℂ) * φ₀ z) +
            (36 / ((π : ℂ) * (π : ℂ)) * φ₄' z +
              (Complex.I : ℂ) * 12 / (π : ℂ) * (φ₂' z * (z : ℂ))) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
          mul_comm, pow_two, neg_add, neg_mul, mul_neg, neg_neg] using congrArg (fun w : ℂ => -w)
          (show φ₀ (ModularGroup.S • z) * (-((t ^ (2 : ℕ) : ℝ) : ℂ)) =
              φ₀ z * (-((t ^ (2 : ℕ) : ℝ) : ℂ)) + (-( (12 * Complex.I) / π * (z : ℂ) * φ₂' z)) +
              (-(36 / (π ^ 2) * φ₄' z)) by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, hzsq]
              using φ₀_S_transform_mul_sq z)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm, pow_two] using
        (by simpa [show (Complex.I : ℂ) * 12 / (π : ℂ) * (φ₂' z * (z : ℂ)) =
            -((t : ℂ) * ((12 : ℂ) / (π : ℂ) * φ₂' z)) by dsimp [z, zI]; ring_nf; simp] using hneg' :
          (t : ℂ) * ((t : ℂ) * φ₀ (ModularGroup.S • z)) =
            (t : ℂ) * ((t : ℂ) * φ₀ z) +
              (36 / ((π : ℂ) * (π : ℂ)) * φ₄' z + -((t : ℂ) * ((12 : ℂ) / (π : ℂ) * φ₂' z))))
    have hSTpow :
        (↑t ^ (2 : ℕ)) * φ₀'' (Complex.I / ↑t) =
          (↑t ^ (2 : ℕ)) * φ₀ z - (12 / (π : ℂ)) * (t : ℂ) * φ₂' z +
            (36 / (π : ℂ) ^ (2 : ℕ)) * φ₄' z := by
      simpa [show φ₀'' ((Complex.I : ℂ) / (t : ℂ)) = φ₀ (ModularGroup.S • z) by
        simpa using congrArg φ₀'' hcoe.symm] using hST'
    unfold cancelExpr; push_cast; linear_combination hSTpow
  let Clarge : ℝ := C₀ + (12 / π) * C₂ + (36 / (π ^ (2 : ℕ))) * C₄
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ t : ℝ, 1 ≤ t → t ≤ A → ‖cancelExpr t‖ ≤ M := by
    obtain ⟨t₀, _, ht₀max⟩ := isCompact_Icc.exists_isMaxOn (s := Set.Icc (1 : ℝ) A)
      ⟨1, le_rfl, hA₂.trans (le_max_left _ _)⟩
      (show ContinuousOn (fun t => ‖cancelExpr t‖) (Set.Icc (1 : ℝ) A) by
        simpa [cancelExpr] using (((((by fun_prop :
          ContinuousOn (fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ)) (Set.Icc (1 : ℝ) A)).mul
          (continuousOn_phi0''_Idiv fun t ht => lt_of_lt_of_le (by norm_num) ht.1)).sub
          (by fun_prop)).add (by fun_prop)).sub (by fun_prop)).norm)
    exact ⟨_, fun t ht1 htA => (isMaxOn_iff.mp ht₀max) t ⟨ht1, htA⟩⟩
  let C : ℝ := max Clarge (M / Real.exp (-2 * π * A))
  refine ⟨C, fun t ht1 => ?_⟩
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  by_cases htA : A ≤ t
  · let z : ℍ := zI t ht0
    have hφ₀z : ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * t) := by
      simpa [show φ₀'' ((Complex.I : ℂ) * (t : ℂ)) = φ₀ z by
        simpa [z, zI] using (φ₀''_coe_upperHalfPlane z)] using hφ₀ t ht1
    have hφ₂z : ‖φ₂' z - (720 : ℂ)‖ ≤ C₂ * Real.exp (-2 * π * t) := by
      simpa [z] using hφ₂ t ht0 ((le_max_left _ _).trans htA)
    have hφ₄z : ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖ ≤ C₄ * Real.exp (-2 * π * t) := by
      simpa [z] using hφ₄ t ht0 ((le_max_right _ _).trans htA)
    have ht2 : (1 : ℝ) ≤ t ^ (2 : ℕ) := by nlinarith [ht1]
    have hle_t : t ≤ t ^ (2 : ℕ) := by nlinarith [ht1]
    have hexp0 : 0 ≤ Real.exp (-2 * π * t) := (Real.exp_pos _).le
    have hnorm1 : ‖((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z‖ ≤
        C₀ * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [hφ₀z, hC₀pos, norm_nonneg (φ₀ z), hexp0]
    have hnorm2 :
        ‖((12 / π : ℝ) : ℂ) * t * (φ₂' z - (720 : ℂ))‖ ≤
          ((12 / π) * C₂) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) :=
      calc ‖((12 / π : ℝ) : ℂ) * t * (φ₂' z - (720 : ℂ))‖
          = (12 / π) * t * ‖φ₂' z - (720 : ℂ)‖ := by
            simp [mul_assoc, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg ht0.le, abs_of_pos Real.pi_pos]
        _ ≤ (12 / π) * t * (C₂ * Real.exp (-2 * π * t)) := by gcongr
        _ ≤ ((12 / π) * C₂) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
            nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle_t
              (mul_nonneg hC₂pos.le hexp0)) (show (0 : ℝ) ≤ 12 / π by positivity)]
    have hnorm3 :
        ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
            (φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))‖ ≤
          ((36 / (π ^ (2 : ℕ))) * C₄) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) :=
      calc ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
            (φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))‖
          = (36 / (π ^ (2 : ℕ))) * ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖ := by
            simp [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (36 / (π ^ (2 : ℕ))) * (C₄ * Real.exp (-2 * π * t)) := by gcongr
        _ ≤ ((36 / (π ^ (2 : ℕ))) * C₄) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
            nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht2
              (mul_nonneg hC₄pos.le hexp0)) (show (0 : ℝ) ≤ 36 / (π ^ (2 : ℕ)) by positivity)]
    have htri : ‖cancelExpr t‖ ≤ Clarge * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
      set x : ℂ := ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z
      set y : ℂ := ((12 / π : ℝ) : ℂ) * t * (φ₂' z - (720 : ℂ))
      set z' : ℂ := ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
        (φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))
      rw [show cancelExpr t = x - y + z' by simpa [x, y, z'] using hrewrite ht0]
      refine (((norm_add_le _ _).trans (by linarith [norm_sub_le x y, norm_nonneg z'])).trans
        (add_le_add_three hnorm1 hnorm2 hnorm3)).trans ?_
      dsimp [Clarge]; nlinarith [hexp0, sq_nonneg t]
    exact htri.trans (by gcongr; exact le_max_left _ _)
  · have hbound := hM t ht1 (le_of_not_ge htA)
    have hscale : M ≤ (M / Real.exp (-2 * π * A)) * ((t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) := by
      simpa [show (M / Real.exp (-2 * π * A)) * Real.exp (-2 * π * A) = M by
        field_simp [Real.exp_ne_zero]] using mul_le_mul_of_nonneg_left
        ((Real.exp_le_exp.2 <| mul_le_mul_of_nonpos_left (le_of_not_ge htA)
          (by nlinarith [Real.pi_pos])).trans <| by
          simpa using mul_le_mul_of_nonneg_right (by nlinarith [ht1] : (1 : ℝ) ≤ t ^ (2 : ℕ))
            (Real.exp_pos _).le : Real.exp (-2 * π * A) ≤ (t ^ (2 : ℕ)) * Real.exp (-2 * π * t))
        (div_nonneg (le_trans (norm_nonneg _) hbound) (Real.exp_pos (-2 * π * A)).le)
    nlinarith [hbound, hscale, mul_le_mul_of_nonneg_right (le_max_right Clarge _ : _ ≤ C)
      (by positivity : (0 : ℝ) ≤ (t ^ (2 : ℕ)) * Real.exp (-2 * π * t))]

private lemma continuousOn_aAnotherIntegrand_of_subset_Ioi
    {s : Set ℝ} (hs : ∀ t ∈ s, 0 < t) (u : ℝ) :
    ContinuousOn (fun t : ℝ => aAnotherIntegrand u t) s :=
  ((((by fun_prop : Continuous fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ)).continuousOn.mul
    (continuousOn_phi0''_Idiv hs)).sub (by fun_prop) |>.add (by fun_prop)).sub (by fun_prop)).mul
      (by fun_prop : Continuous fun t : ℝ => ((Real.exp (-π * u * t)) : ℂ)).continuousOn

lemma aAnotherIntegrand_integrableOn_Ioc {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => aAnotherIntegrand u t) (Set.Ioc (0 : ℝ) 1) := by
  rcases MagicFunction.PolyFourierCoeffBound.norm_φ₀_le with ⟨Cφ₀, hCφ₀_pos, hCφ₀⟩
  refine MeasureTheory.IntegrableOn.of_bound (by simp : (volume : Measure ℝ) (Set.Ioc 0 1) < ⊤)
    ((continuousOn_aAnotherIntegrand_of_subset_Ioi (fun t ht => ht.1) u).aestronglyMeasurable
      measurableSet_Ioc) (Cφ₀ + ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) +
        ‖((8640 / π : ℝ) : ℂ)‖ + ‖((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_))
  have him_pos : 0 < (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im := by
    simpa [imag_I_div] using inv_pos.2 ht.1
  let z : ℍ := ⟨(Complex.I : ℂ) / (t : ℂ), him_pos⟩
  have hzHalf : (1 / 2 : ℝ) < z.im := by
    linarith [(by simpa [z, UpperHalfPlane.im, imag_I_div] using (one_le_inv₀ ht.1).2 ht.2 :
      (1 : ℝ) ≤ z.im)]
  have hφ0'' : ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ Cφ₀ := by
    simpa [show φ₀ z = φ₀'' ((Complex.I : ℂ) / (t : ℂ)) by
      simpa [z] using (φ₀''_def (z := (Complex.I : ℂ) / (t : ℂ)) him_pos).symm] using
      (hCφ₀ z hzHalf).trans
        (by simpa using mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2
          (by nlinarith [Real.pi_pos, (z.2).le])) hCφ₀_pos.le)
  have ht2_le : (t ^ (2 : ℕ) : ℝ) ≤ 1 := by nlinarith [ht.1.le, ht.2]
  have hbr : ‖cancelExpr t‖ ≤
      (t ^ (2 : ℕ) : ℝ) * Cφ₀ +
        ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) +
        ‖((8640 / π : ℝ) : ℂ)‖ + ‖((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ := by
    unfold cancelExpr
    set A : ℂ := ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ))
    set B : ℂ := ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t)
    set Cc : ℂ := ((8640 / π : ℝ) : ℂ) * t
    set D : ℂ := ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)
    have ht2nn : (0 : ℝ) ≤ t ^ (2 : ℕ) := by positivity
    have hA : ‖A‖ ≤ (t ^ (2 : ℕ) : ℝ) * Cφ₀ := by
      simpa [A, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht2nn]
        using mul_le_mul_of_nonneg_left hφ0'' ht2nn
    have hB : ‖B‖ ≤ ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) := by
      rw [show ‖B‖ = ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π * t) by
        simp [-Complex.ofReal_exp, B]]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, ht.2])) (norm_nonneg _)
    have hC : ‖Cc‖ ≤ ‖((8640 / π : ℝ) : ℂ)‖ := by
      simpa [Cc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1.le] using
        mul_le_mul_of_nonneg_left ht.2 (norm_nonneg ((8640 / π : ℝ) : ℂ))
    linarith [((show ‖A - B + Cc - D‖ = ‖(A - B) + (Cc - D)‖ by ring_nf).le.trans
      (norm_add_le _ _)).trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))]
  have hmul : ‖aAnotherIntegrand u t‖ ≤ ‖cancelExpr t‖ := by
    simpa [cancelExpr, aAnotherIntegrand, norm_mul, mul_assoc] using mul_le_mul_of_nonneg_left
      (by rw [norm_ofReal_exp]; exact Real.exp_le_one_iff.2 (by
        nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hu.le) ht.1.le]) :
        ‖(Real.exp (-π * u * t) : ℂ)‖ ≤ 1) (norm_nonneg _)
  nlinarith [hmul.trans hbr, mul_le_mul_of_nonneg_right ht2_le hCφ₀_pos.le]

/-- For `u > 0`, the function `t ↦ aAnotherIntegrand u t` is integrable on `(0, ∞)`. -/
public lemma aAnotherIntegrand_integrable_of_pos {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => aAnotherIntegrand u t) (Set.Ioi (0 : ℝ)) := by
  rw [← Set.Ioc_union_Ici_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_lt_one]
  refine (aAnotherIntegrand_integrableOn_Ioc hu).union ?_
  rcases exists_phi0_cancellation_bound with ⟨C, hC⟩
  have hbound : ∀ t : ℝ, t ∈ Set.Ici (1 : ℝ) → ‖aAnotherIntegrand u t‖ ≤
      C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t) := fun t ht => by
    rw [show C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t) =
      (C * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) * Real.exp (-π * u * t) by
        rw [mul_assoc (C * _), ← Real.exp_add]; ring_nf]
    simpa [-Complex.ofReal_exp, cancelExpr, aAnotherIntegrand, mul_assoc, mul_left_comm,
        mul_comm] using mul_le_mul_of_nonneg_right (hC t ht) (Real.exp_pos (-π * u * t)).le
  have hdom :
      IntegrableOn (fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t))
        (Set.Ici (1 : ℝ)) := by
    simpa [mul_assoc] using (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici
      (n := 2) (b := 2 * π + π * u) (by positivity)).const_mul C
  exact MeasureTheory.Integrable.mono' hdom.integrable
    ((continuousOn_aAnotherIntegrand_of_subset_Ioi
      (fun t ht => lt_of_lt_of_le (by norm_num) ht) u).aestronglyMeasurable measurableSet_Ici)
    ((ae_restrict_iff' measurableSet_Ici).2 (Filter.Eventually.of_forall hbound))

end

end MagicFunction.g.CohnElkies.IntegralReps
