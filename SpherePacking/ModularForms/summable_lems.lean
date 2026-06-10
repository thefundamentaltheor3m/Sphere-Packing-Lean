module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import SpherePacking.ModularForms.exp_lems

/-!
# Summability lemmas

Auxiliary summability lemmas for `ℕ+`-indexed series used in the q-expansions of
modular forms.

Most of the former content of this file (the cotangent series representation, iterated
derivatives of `∑' n, cexp (2 * π * I * n * z)`, the `q`-expansion identity for
`∑' d : ℤ, 1 / (z + d) ^ k`, and the `G₂`/`E₂` summability lemmas) has been upstreamed to
Mathlib, see `Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent`,
`Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion`,
`Mathlib.NumberTheory.TsumDivisorsAntidiagonal` and
`Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2`.
-/

@[expose] public section


open UpperHalfPlane Complex

open scoped Real

theorem tsum_pNat {α : Type _} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α] [T2Space α]
  [CompleteSpace α] (f : ℕ → α) (hf : f 0 = 0) : ∑' n : ℕ+, f n = ∑' n, f n := by
  by_cases hf2 : Summable f
  · rw [hf2.tsum_eq_zero_add, hf, zero_add]
    exact tsum_pnat_eq_tsum_succ
  rw [tsum_eq_zero_of_not_summable hf2,
    tsum_eq_zero_of_not_summable (summable_pnat_iff_summable_nat.not.mpr hf2)]

/-- Closed form for ∑ n·rⁿ over ℕ+ when ‖r‖ < 1. -/
lemma tsum_pnat_coe_mul_geometric {r : ℝ} (hr : ‖r‖ < 1) :
    (∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ)) = r / (1 - r) ^ 2 := by
  exact (tsum_pNat (fun n => (n : ℝ) * r ^ n) (by simp)).trans
    (tsum_coe_mul_geometric_of_norm_lt_one hr)

theorem a33 (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ+ => (c : ℂ) ^ k * exp (2 * ↑π * Complex.I * e * ↑z * c) := by
  apply Summable.of_norm
  conv =>
    enter [1]
    ext a
    rw [show cexp (2 * ↑π * Complex.I * ↑e * z * ↑a) = cexp (2 * ↑π * Complex.I * (↑e)* z) ^ (a : ℕ)
      by rw [← Complex.exp_nsmul]; congr; ring]
  have := summable_norm_pow_mul_geometric_of_norm_lt_one
    (r := cexp (2 * ↑π * Complex.I * (↑e)* z)) k ?_
  · apply this.subtype
  simp [norm_exp, mul_re, mul_im, Real.exp_lt_one_iff]; positivity

lemma exp_aux (z : ℍ) (n : ℕ) : cexp (2 * ↑π * Complex.I * n * ↑z) =
    cexp (2 * ↑π * Complex.I * ↑z) ^ n := by
  rw [← Complex.exp_nat_mul]; ring_nf

theorem summable_exp_pow (z : ℍ) : Summable fun i : ℕ ↦
    ‖(cexp (2 * ↑π * Complex.I * (↑i + 1) * z))‖ := by
  conv =>
    enter [1]
    ext i
    rw [show ((i : ℂ) + 1) = ((i + 1) : ℕ) by simp, exp_aux, norm_pow]
  rw [summable_nat_add_iff 1]
  simpa only [summable_geometric_iff_norm_lt_one, norm_norm] using exp_upperHalfPlane_lt_one z
