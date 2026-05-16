module
public import SpherePacking.ModularForms.ExpLemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open UpperHalfPlane TopologicalSpace Set Metric Filter Function Complex

/-- Summability of `∑_{c>0} c^k * exp(2π i e z c)` for `z ∈ ℍ`. -/
public theorem a33 (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ+ => (c : ℂ) ^ k * exp (2 * ↑π * Complex.I * e * ↑z * c) := by
  apply Summable.of_norm
  conv =>
    enter [1]
    ext a
    rw [show cexp (2 * ↑π * Complex.I * ↑e * z * ↑a) = cexp (2 * ↑π * Complex.I * (↑e)* z) ^ (a : ℕ)
      by rw [← Complex.exp_nsmul]; congr; ring]
  have hs := summable_norm_pow_mul_geometric_of_norm_lt_one
    (r := cexp (2 * ↑π * Complex.I * (↑e)* z)) k ?_
  · simpa [Function.comp] using (hs.subtype (p := fun n : ℕ => 0 < n))
  have he : (0 : ℝ) < (e : ℝ) := by exact_mod_cast e.pos
  let z' : ℍ := ⟨(e : ℂ) * z, by simpa [Complex.mul_im] using mul_pos he z.im_pos⟩
  simpa [z', mul_assoc, mul_left_comm, mul_comm] using exp_upperHalfPlane_lt_one z'

/-- Rewrite `exp(2π i n z)` as a power of `exp(2π i z)`. -/
public lemma exp_aux (z : ℍ) (n : ℕ) : cexp (2 * ↑π * Complex.I * n * ↑z) =
    cexp (2 * ↑π * Complex.I * ↑z) ^ n := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (Complex.exp_nat_mul (2 * ↑π * Complex.I * (z : ℂ)) n)

/-- Summability of the norms `‖exp(2π i (i+1) z)‖` for `z ∈ ℍ`. -/
public theorem summable_exp_pow (z : ℍ) : Summable fun i : ℕ ↦
     ‖(cexp (2 * ↑π * Complex.I * (↑i + 1) * z))‖ := by
  conv =>
    enter [1]
    ext i
    rw [show ((i : ℂ) + 1) = ((i + 1) : ℕ) by simp, exp_aux, norm_pow]
  rw [summable_nat_add_iff 1]
  simpa [summable_geometric_iff_norm_lt_one, norm_norm] using exp_upperHalfPlane_lt_one z
