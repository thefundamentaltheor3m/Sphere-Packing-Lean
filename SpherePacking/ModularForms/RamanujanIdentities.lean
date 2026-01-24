import SpherePacking.ModularForms.CoreRamanujan
import SpherePacking.ModularForms.FG

/-!
# Q-Expansion Identities for Eisenstein Series

This file contains q-expansion identities derived from the Ramanujan identities.

## Main results

* `D_exp_eq_n_mul` : D applied to exp(2πinz) gives n * exp(2πinz)
* `tsum_sigma_deriv_eq` : Double sum identity for sigma functions
* `D_E4_qexp` : Q-expansion of D(E₄) = 240·Σ n·σ₃(n)·qⁿ
* `E₂_mul_E₄_sub_E₆` : E₂·E₄ - E₆ = 720·Σ n·σ₃(n)·qⁿ

## References

See Blueprint Theorem 6.50 for the Ramanujan identities.
-/

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap
open ModularForm EisensteinSeries TopologicalSpace Set MeasureTheory
open Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped ModularForm MatrixGroups Manifold Interval Real NNReal ENNReal Topology BigOperators

noncomputable section

/-! ## Applications of Ramanujan identities -/

section Ramanujan_qExpansion

open scoped ArithmeticFunction.sigma

/--
Helper: D applied to exp(2πinz) gives n * exp(2πinz).
This follows from: d/dz[exp(2πinz)] = 2πin * exp(2πinz),
so D[exp(2πinz)] = (2πi)⁻¹ * 2πin * exp(2πinz) = n * exp(2πinz).
-/
lemma D_exp_eq_n_mul (n : ℕ) (z : ℍ) :
    D (fun w : ℍ => cexp (2 * π * I * n * w)) z = n * cexp (2 * π * I * n * z) := by
  simpa using D_qexp_term n 1 z

/--
Key identity: The double sum ∑' (c,d), c * d^(k+1) * exp(2πi*z*cd) equals
∑' n, n * σ_k(n) * exp(2πi*n*z).
This follows from σ_k(n) = ∑_{d|n} d^k and n * σ_k(n) = ∑_{cd=n} c * d^(k+1).

The proof uses `tsum_sigma_eqn` and differentiation multiplies by the exponent factor.
-/
lemma tsum_sigma_deriv_eq {k : ℕ} (z : ℍ) :
    ∑' c : ℕ+ × ℕ+, (c.1 : ℂ) * (c.2 : ℂ) ^ (k + 1) * cexp (2 * π * I * z * c.1 * c.2) =
    ∑' n : ℕ+, (n : ℂ) * (σ k n : ℂ) * cexp (2 * π * I * n * z) := by
  -- The key identity: for each n, ∑_{cd=n} c * d^(k+1) = n * σ_k(n)
  -- Proof: ∑_{cd=n} c * d^(k+1) = ∑_{d|n} (n/d) * d^(k+1) = ∑_{d|n} n * d^k = n * σ_k(n)
  --
  -- Use sigmaAntidiagonalEquivProd to convert pairs (c,d) to divisor sums
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  simp only [sigmaAntidiagonalEquivProd, mapdiv, PNat.mk_coe, Equiv.coe_fn_mk]
  -- Use summability to convert tsum over sigma to tsum over ℕ+
  have hsumm : Summable (fun c : (n : ℕ+) × {x // x ∈ (n : ℕ).divisorsAntidiagonal} ↦
      (↑(c.snd.val.1) : ℂ) * ↑(c.snd.val.2) ^ (k + 1) *
      cexp (2 * π * I * z * c.snd.val.1 * c.snd.val.2)) := by
    -- Summability follows from bounds adapting summable_auxil_1:
    -- For (a,b) ∈ divisorsAntidiagonal n: a * b = n, so
    --   a * b^(k+1) = n * b^k ≤ n^(k+1) (since b | n implies b ≤ n)
    --   |exp(2πi*z*ab)| = |exp(2πi*n*z)| (exponential decay)
    -- Sum over divisors: card(divisors) * n^(k+1) * |exp| ≤ n^(k+2) * |exp|
    -- Outer sum converges by hsum (k+2) z
    apply Summable.of_norm
    rw [summable_sigma_of_nonneg]
    constructor
    · -- Each inner sum over divisorsAntidiagonal is finite
      intro n
      exact (hasSum_fintype _).summable
    · -- Outer sum of norms converges
      simp only [Complex.norm_mul, norm_pow, RCLike.norm_natCast, tsum_fintype,
        Finset.univ_eq_attach]
      have H (n : ℕ+) := Finset.sum_attach ((n : ℕ).divisorsAntidiagonal) (fun (x : ℕ × ℕ) =>
        (x.1 : ℝ) * (x.2 : ℝ) ^ (k + 1) * ‖cexp (2 * π * I * z * x.1 * x.2)‖)
      have H2 (n : ℕ+) := Nat.sum_divisorsAntidiagonal ((fun (x : ℕ) => fun (y : ℕ) =>
        (x : ℝ) * (y : ℝ) ^ (k + 1) * ‖cexp (2 * π * I * z * x * y)‖)) (n := n)
      conv =>
        enter [1]
        ext b
        simp
        rw [H b]
        rw [H2 b]
      -- Bound each divisor sum by n^(k+1) * |exp(2πi*n*z)| * card(divisors)
      have hsum_bound := hsum (k + 1) z
      apply Summable.of_nonneg_of_le _ _ hsum_bound
      · intro b
        apply Finset.sum_nonneg
        intro i _
        apply mul_nonneg (mul_nonneg _ _) (norm_nonneg _)
        · exact Nat.cast_nonneg _
        · exact pow_nonneg (Nat.cast_nonneg _) _
      · intro b
        apply Finset.sum_le_sum
        intro i hi
        simp only [Nat.mem_divisors, ne_eq, PNat.ne_zero, not_false_eq_true, and_true] at hi
        -- After Nat.sum_divisorsAntidiagonal: term is i * (b/i)^(k+1) * ‖exp(...)‖
        -- For i | b: i * (b/i) = b
        have hdvd : i ∣ (b : ℕ) := hi
        have hi_pos : 0 < i := Nat.pos_of_ne_zero (fun h => by simp [h] at hdvd)
        have hquot_le_b : (b : ℕ) / i ≤ (b : ℕ) := Nat.div_le_self _ _
        have hprod : i * ((b : ℕ) / i) = (b : ℕ) := Nat.mul_div_cancel' hdvd
        -- Bound: i * (b/i)^(k+1) = i * (b/i) * (b/i)^k = b * (b/i)^k ≤ b * b^k = b^(k+1)
        -- Let q = (b : ℕ) / i for clarity
        set q := (b : ℕ) / i with hq_def
        have hcoeff_le : (i : ℝ) * (q : ℝ) ^ (k + 1) ≤ (b : ℝ) ^ (k + 1) := by
          calc (i : ℝ) * (q : ℝ) ^ (k + 1)
              = (i : ℝ) * (q : ℝ) * (q : ℝ) ^ k := by ring
            _ = ((i * q : ℕ) : ℝ) * (q : ℝ) ^ k := by rw [← Nat.cast_mul]
            _ = (b : ℝ) * (q : ℝ) ^ k := by rw [hq_def, hprod]
            _ ≤ (b : ℝ) * (b : ℝ) ^ k := by gcongr
            _ = (b : ℝ) ^ (k + 1) := by ring
        -- Exponential: i * q = b, so exp(2πi*z*i*q) = exp(2πi*z*b)
        have hexp_eq : ‖cexp (2 * π * I * z * i * q)‖ = ‖cexp (2 * π * I * z * b)‖ := by
          congr 1
          congr 1
          calc (2 : ℂ) * π * I * z * i * q
              = 2 * π * I * z * ((i * q : ℕ) : ℂ) := by simp only [Nat.cast_mul]; ring
            _ = 2 * π * I * z * (b : ℕ) := by rw [hq_def, hprod]
            _ = 2 * π * I * z * ↑↑b := by simp
        calc (i : ℝ) * (q : ℝ) ^ (k + 1) * ‖cexp (2 * π * I * z * i * q)‖
            = (i : ℝ) * (q : ℝ) ^ (k + 1) * ‖cexp (2 * π * I * z * b)‖ := by rw [hexp_eq]
          _ ≤ (b : ℝ) ^ (k + 1) * ‖cexp (2 * π * I * z * b)‖ := by gcongr
    · intro _
      exact norm_nonneg _
  rw [hsumm.tsum_sigma]
  apply tsum_congr
  intro n
  rw [tsum_fintype, Finset.univ_eq_attach]
  -- For each n, show ∑_{(c,d) with cd=n} c * d^(k+1) = n * σ_k(n)
  have hdiv := @Nat.sum_divisorsAntidiagonal' ℂ _ (fun (x : ℕ) => fun (y : ℕ) =>
    (x : ℂ) * (y : ℂ) ^ (k + 1) * cexp (2 * π * I * z * x * y)) n
  simp only at hdiv
  have H := Finset.sum_attach ((n : ℕ).divisorsAntidiagonal) (fun (x : ℕ × ℕ) =>
    (x.1 : ℂ) * (x.2 : ℂ) ^ (k + 1) * cexp (2 * π * I * z * x.1 * x.2))
  simp only at H
  rw [H, hdiv]
  -- Now show: ∑_{i|n} ↑(n/i) * i^(k+1) * exp(2πi * z * ↑(n/i) * i) = n * σ_k(n) * exp(2πinz)
  -- Note: Nat.sum_divisorsAntidiagonal' produces ↑(↑n / i) which is ℕ division cast to ℂ
  --
  -- Key identity for i | n: ↑((n/i : ℕ) * i : ℕ) = ↑n via Nat.div_mul_cancel
  -- This gives: ↑(n/i) * ↑i = ↑n (using ← Nat.cast_mul)
  -- Then: ↑(n/i) * i^(k+1) = ↑(n/i) * i * i^k = n * i^k
  -- And: exp(2πi*z*↑(n/i)*i) = exp(2πi*n*z) since ↑(n/i)*i = n
  --
  -- Convert each term using ← Nat.cast_mul and Nat.div_mul_cancel
  have hterm_eq : ∀ i ∈ (n : ℕ).divisors,
      (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) ^ (k + 1) *
        cexp (2 * π * I * z * (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ)) =
      (n : ℂ) * (i : ℂ) ^ k * cexp (2 * π * I * n * z) := by
    intro i hi
    have hdvd : i ∣ (n : ℕ) := Nat.dvd_of_mem_divisors hi
    -- Key: ↑((n/i) * i : ℕ) = ↑n, so ↑(n/i) * ↑i = ↑n
    have hprod : (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) = (n : ℂ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    -- Coefficient: ↑(n/i) * i^(k+1) = ↑(n/i) * i * i^k = n * i^k
    have hcoeff : (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) ^ (k + 1) = (n : ℂ) * (i : ℂ) ^ k := by
      calc (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) ^ (k + 1)
          = (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) * (i : ℂ) ^ k := by ring
        _ = (n : ℂ) * (i : ℂ) ^ k := by rw [hprod]
    -- Exponential: ↑(n/i) * i = n, so exp(...) = exp(2πi*n*z)
    -- Note: ((n : ℕ) / i) is ℕ division, which gets coerced to ℂ in this context
    have hexp : cexp (2 * π * I * z * (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ)) =
        cexp (2 * π * I * n * z) := by
      congr 1
      -- Rearrange to use hprod: ↑(↑n/i) * ↑i = ↑↑n (without using push_cast)
      have hrearr : (2 : ℂ) * π * I * z * (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) =
          2 * π * I * z * ((((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ)) := by ring
      rw [hrearr, hprod]
      ring
    rw [hcoeff, hexp]
  -- Apply the term rewrite to the sum using direct rewrites
  rw [Finset.sum_congr rfl hterm_eq, ← Finset.sum_mul, ← Finset.mul_sum]
  -- Now show: ∑ i ∈ n.divisors, (i : ℂ)^k = (σ k n : ℂ) using sigma_apply
  have hsigma_cast : ∑ i ∈ ((n : ℕ)).divisors, ((i : ℂ)) ^ k = ((σ k n) : ℂ) := by
    rw [ArithmeticFunction.sigma_apply]
    simp only [Nat.cast_sum, Nat.cast_pow]
  rw [hsigma_cast]

/--
The normalized derivative D multiplies q-expansion coefficients by n.
Since E₄ = 1 + 240·Σσ₃(n)·qⁿ, we have D(E₄) = 240·Σn·σ₃(n)·qⁿ.
-/
lemma D_E4_qexp (z : ℍ) :
    D E₄.toFun z = 240 * ∑' (n : ℕ+), n * (σ 3 n) * cexp (2 * π * Complex.I * n * z) :=
  DE₄_qexp z

/--
The q-expansion identity E₂E₄ - E₆ = 720·Σn·σ₃(n)·qⁿ.
This follows from Ramanujan's formula: E₂E₄ - E₆ = 3·D(E₄),
combined with D(E₄) = 240·Σn·σ₃(n)·qⁿ (since D multiplies q-coefficients by n).
-/
theorem E₂_mul_E₄_sub_E₆ (z : ℍ) :
    (E₂ z) * (E₄ z) - (E₆ z) = 720 * ∑' (n : ℕ+), n * (σ 3 n) * cexp (2 * π * Complex.I * n * z)
    := by
  -- From ramanujan_E₄: D E₄ = (1/3) * (E₂ * E₄ - E₆)
  -- So: E₂ * E₄ - E₆ = 3 * D E₄
  have hRam : (E₂ z) * (E₄ z) - (E₆ z) = 3 * D E₄.toFun z := by
    have h := congrFun ramanujan_E₄ z
    simp only [Pi.mul_apply, Pi.sub_apply, show (3⁻¹ : ℍ → ℂ) z = 3⁻¹ from rfl] at h
    field_simp at h ⊢
    ring_nf at h ⊢
    exact h.symm
  -- Substitute D(E₄) = 240 * ∑' n, n * σ₃(n) * q^n
  rw [hRam, D_E4_qexp]
  ring

end Ramanujan_qExpansion
