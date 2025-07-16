import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence



open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical


lemma norm_symm (x y : ℤ) : ‖![x, y]‖ = ‖![y,x]‖ := by
  simp_rw [EisensteinSeries.norm_eq_max_natAbs]
  rw [max_comm]
  simp


lemma linear_bigO (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹) := by
  have h1 : (fun (n : ℤ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    (fun n : ℤ => ((r z * ‖![n, m]‖))⁻¹) := by
    rw [@Asymptotics.isBigO_iff']
    use 1
    simp
    constructor
    repeat{
    use 0
    intro n hn
    have := EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![m, n]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, ge_iff_le] at *
    nth_rw 2 [mul_comm]
    simp_rw [Real.rpow_neg_one] at this
    have hr : (r z)⁻¹ = |r z|⁻¹ := by
      simp only [inv_inj]
      apply symm
      rw [abs_eq_self]
      exact (r_pos z).le
    rw [← hr, _root_.norm_symm]
    exact this}
  apply Asymptotics.IsBigO.trans h1
  rw [@Asymptotics.isBigO_iff']
  use (r z)⁻¹
  refine ⟨by simp; exact r_pos z, ?_⟩
  simp
  constructor
  use min (-1) m
  intro n hn
  --have := EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![n, m]
  rw [mul_comm]
  gcongr
  · simp [(r_pos z).le]
  · exact r_pos z
  · exact le_abs_self (r z)
  · simp; omega
  · rw [EisensteinSeries.norm_eq_max_natAbs]
    simp
    left
    norm_cast
    rw [Int.abs_eq_natAbs]
    rfl
  use max 1 m
  intro b hb
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp
  rw [mul_comm]
  gcongr
  · simp [(r_pos z).le]
  · exact r_pos z
  · exact le_abs_self (r z)
  · simp; omega
  · simp at *;
    left
    norm_cast
    rw [Int.abs_eq_natAbs]
    rfl

lemma linear_bigO_pow (m : ℤ) (z : ℍ) (k : ℕ) : (fun (n : ℤ) => ((((m : ℂ) * z + n)) ^ k )⁻¹) =O[cofinite]
    fun n => ((|(n : ℝ)| ^ k)⁻¹) := by
  simp_rw [← inv_pow]
  apply Asymptotics.IsBigO.pow
  apply linear_bigO m z


lemma Asymptotics.IsBigO.zify {α β: Type*} [Norm α] [Norm β] {f : ℤ → α} {g : ℤ → β} (hf : f =O[cofinite] g) :
    (fun (n : ℕ) => f n) =O[cofinite] fun n => g n := by
  rw [@isBigO_iff] at *
  obtain ⟨C, hC⟩ := hf
  use C
  rw [Int.cofinite_eq] at hC
  rw [Nat.cofinite_eq_atTop]
  apply Filter.Eventually.natCast_atTop (p := fun n => ‖f n‖ ≤ C * ‖g n‖)
  simp_all only [eventually_sup, eventually_atBot, eventually_atTop, ge_iff_le]


lemma Asymptotics.IsBigO.of_neg {α β: Type*} [Norm α] [Norm β] {f : ℤ → α} {g : ℤ → β}
    (hf : f =O[cofinite] g) : (fun n => f (-n)) =O[cofinite] fun n => g (-n) := by
  rw [← Equiv.neg_apply]
  apply Asymptotics.IsBigO.comp_tendsto hf
  refine Injective.tendsto_cofinite (Equiv.injective (Equiv.neg ℤ))


lemma linear_bigO_nat (m : ℤ) (z : ℍ) : (fun (n : ℕ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹) := by
  have := linear_bigO (m : ℤ) z
  apply this.zify




lemma linear_bigO' (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((n : ℂ) * z + m)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹) := by
  have h1 : (fun (n : ℤ) => ((n : ℂ) * z + m)⁻¹) =O[cofinite]
    (fun n : ℤ => ((r z * ‖![m, n]‖))⁻¹) := by
    rw [@Asymptotics.isBigO_iff']
    use 1
    simp
    constructor
    repeat{
      use 0
      intro n hn
      have := EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![n, m]
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, ge_iff_le] at *
      nth_rw 2 [mul_comm]
      simp_rw [Real.rpow_neg_one] at this
      have hr : (r z)⁻¹ = |r z|⁻¹ := by
        simp only [inv_inj]
        apply symm
        rw [abs_eq_self]
        exact (r_pos z).le
      rw [← hr, _root_.norm_symm]
      exact this}
  apply Asymptotics.IsBigO.trans h1
  rw [@Asymptotics.isBigO_iff']
  use (r z)⁻¹
  refine ⟨by simp; exact r_pos z, ?_⟩
  simp
  constructor
  use min (-1) m
  intro n hn
  --have := EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![n, m]
  rw [mul_comm]
  gcongr
  · simp [(r_pos z).le]
  · exact r_pos z
  · exact le_abs_self (r z)
  · simp; omega
  · rw [EisensteinSeries.norm_eq_max_natAbs]
    simp
    right
    norm_cast
    rw [Int.abs_eq_natAbs]
    rfl
  use max 1 m
  intro b hb
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp
  rw [mul_comm]
  gcongr
  · simp [(r_pos z).le]
  · exact r_pos z
  · exact le_abs_self (r z)
  · simp; omega
  · simp at *;
    right
    norm_cast
    rw [Int.abs_eq_natAbs]
    rfl
