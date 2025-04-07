import Mathlib

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open ArithmeticFunction

noncomputable section Definitions

def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0

def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma ↑1) k :=
  (1/2 : ℂ) • eisensteinSeries_MF hk standardcongruencecondition /-they need  1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/

open Pointwise

def GammaSet_one_Equiv : (Fin 2 → ℤ) ≃ (⋃ n : ℕ, ({n} : Set ℕ)  • gammaSet 1 0) where
  toFun v := ⟨(v 0).gcd (v 1) • ![(v 0)/(v 0).gcd (v 1), (v 1)/(v 0).gcd (v 1)], by
    simp only [ mem_iUnion]
    use (v 0).gcd (v 1)
    by_cases hn : 0 < (v 0).gcd (v 1)
    apply Set.smul_mem_smul
    · simp only [mem_singleton]
    · rw [gammaSet]
      simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, mem_setOf_eq,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      constructor
      apply (Subsingleton.elim _ _)
      rw [@Int.isCoprime_iff_gcd_eq_one]
      apply Int.gcd_div_gcd_div_gcd hn
    · simp only [Fin.isValue, not_lt, nonpos_iff_eq_zero] at hn
      rw [hn]
      simp only [singleton_smul, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
        CharP.cast_eq_zero, EuclideanDomain.div_zero, zero_smul]
      rw [Set.zero_smul_set]
      simp only [Set.mem_zero]
      use ![1,1]
      rw [gammaSet]
      simp only [Fin.isValue, mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
      constructor
      apply (Subsingleton.elim _ _)
      rw [@Int.isCoprime_iff_gcd_eq_one]
      simp⟩
  invFun v := v
  left_inv := by
            intro v
            simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.smul_cons,
              nsmul_eq_mul, Matrix.smul_empty]
            ext i
            fin_cases i
            by_cases hv : v = 0
            simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
              Matrix.cons_val_zero]
            rw [hv]
            simp only [Pi.zero_apply, Int.gcd_self, Int.natAbs_zero, CharP.cast_eq_zero,
              EuclideanDomain.div_zero, mul_zero]
            simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
              Matrix.cons_val_zero]
            apply Int.mul_ediv_cancel'
            exact Int.gcd_dvd_left
            apply Int.mul_ediv_cancel'
            exact Int.gcd_dvd_right
  right_inv := by
            intro v
            ext i
            fin_cases i
            simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.zero_eta, Pi.smul_apply,
              Matrix.cons_val_zero, nsmul_eq_mul]
            apply Int.mul_ediv_cancel'
            exact Int.gcd_dvd_left
            apply Int.mul_ediv_cancel'
            exact Int.gcd_dvd_right

lemma EQ1 (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) : ∑' (x : Fin 2 → ℤ),
  1 / (x 0 * (z : ℂ) + x 1) ^ ↑k = 2 * riemannZeta ↑k +
    2 * ((-2 * ↑π * Complex.I) ^ k / ↑(k - 1)!) * ∑' (n : ℕ+), ↑((σ (k - 1)) ↑n) * cexp (2 * ↑π * Complex.I * ↑z * ↑↑n) := by sorry


lemma smul_disjoint ( i j : ℕ) (hij : i ≠ j) : Disjoint (({i} : Set ℕ)  • (gammaSet 1 0)) (({j} : Set ℕ)  • (gammaSet 1 0)) := by
  sorry
/-   rw [Set.disjoint_left ]
  intro v hv
  rw [Set.mem_smul] at *
  simp [eq_iff_true_of_subsingleton] at *
  obtain ⟨y, hy, hy2⟩:= hv
  intro x hx
  rw [←hy2]
  intro H
  have r1 : j * x 0 = i * y 0 := by
    exact congrFun H 0
  have r2 : j * x 1 = i * y 1 := by
    exact congrFun H 1
  have r11 := Int.gcd_mul_left j (x 0) (x 1)
  have r22 := Int.gcd_mul_left i (y 0) (y 1)
  simp at *
  rw [r1, r2, hx] at r11
  rw [hy] at r22
  rw [r22] at r11
  simp at r11
  exact hij r11 -/

lemma EQ2 (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) : ∑' (x : Fin 2 → ℤ),
  1 / (x 0 * (z : ℂ) + x 1) ^ ↑k = (riemannZeta (k)) * ∑' (c : gammaSet 1 0), 1 / ((c.1 0) * (z : ℂ) + (c.1 1)) ^ k := by
  have := GammaSet_one_Equiv.symm.tsum_eq (fun v => 1 / ((v 0 : ℂ) * z + v 1) ^ k)
  rw [← this]
  have h1 := smul_disjoint
  let h0 := (Set.unionEqSigmaOfDisjoint h1).symm
  rw [ ← h0.tsum_eq]
  rw [tsum_sigma]
  simp [GammaSet_one_Equiv]
  sorry

  sorry



/-This result is already proven in the modular forms repo and being PRed (slowly) into mathlib, so
we can use it freely here. -/
lemma E_k_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (E k hk) z = 1 +
        (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, sigma (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by
  rw [E]
  rw [ModularForm.smul_apply]
  have : (eisensteinSeries_MF hk standardcongruencecondition) z =
    (eisensteinSeries_SIF standardcongruencecondition k) z := rfl
  rw [this]
  have := eisensteinSeries_SIF_apply standardcongruencecondition k z
  rw [this, eisensteinSeries, standardcongruencecondition]
  simp
  simp_rw [eisSummand]
  have HE1 := EQ1 k hk hk2 z
  have HE2 := EQ2 k hk hk2 z
  have z2 : (riemannZeta (k)) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    simp
    omega
  rw [← inv_mul_eq_iff_eq_mul₀ z2 ] at HE2
  simp [UpperHalfPlane.coe] at *
  conv =>
    enter [1,2]
    rw [← HE2]
  simp_rw [← mul_assoc]
  rw [HE1, mul_add]
  have : 2⁻¹ * (riemannZeta (k))⁻¹ * (2 * riemannZeta (k)) = 1 := by
    field_simp
  rw [this]
  ring
