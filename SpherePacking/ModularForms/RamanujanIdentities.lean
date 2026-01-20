import SpherePacking.ModularForms.CoreRamanujan

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
  unfold D
  -- The key: (f ∘ ofComplex) agrees with f on the upper half-plane
  -- So their derivatives agree at points in ℍ
  have hcomp : deriv ((fun w : ℍ => cexp (2 * π * I * n * w)) ∘ ofComplex) z =
      deriv (fun w : ℂ => cexp (2 * π * I * n * w)) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    rfl
  rw [hcomp]
  -- deriv of exp(c*z) is c*exp(c*z)
  have hderiv : deriv (fun w : ℂ => cexp (2 * π * I * n * w)) z =
      (2 * π * I * n) * cexp (2 * π * I * n * z) := by
    -- Use the derivative chain rule lemma directly
    have hdiff_lin : DifferentiableAt ℂ (fun w => 2 * π * I * n * w) (z : ℂ) := by fun_prop
    have hderiv_lin : deriv (fun w : ℂ => 2 * π * I * n * w) (z : ℂ) = 2 * π * I * n := by
      rw [deriv_const_mul _ differentiableAt_id]
      simp only [deriv_id'', mul_one]
    calc deriv (fun w : ℂ => cexp (2 * π * I * n * w)) z
        = cexp (2 * π * I * n * z) * deriv (fun w => 2 * π * I * n * w) z := by
            exact deriv_cexp hdiff_lin
      _ = cexp (2 * π * I * n * z) * (2 * π * I * n) := by rw [hderiv_lin]
      _ = (2 * π * I * n) * cexp (2 * π * I * n * z) := by ring
  rw [hderiv]
  -- Simplify (2πi)⁻¹ * (2πin) = n
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, ofReal_eq_zero,
      Real.pi_ne_zero, I_ne_zero, or_self]
  field_simp

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
    D E₄.toFun z = 240 * ∑' (n : ℕ+), n * (σ 3 n) * cexp (2 * π * Complex.I * n * z) := by
  -- Step 1: Express E₄ using q-expansion
  -- E₄(z) = 1 + 240 * ∑' n : ℕ+, σ₃(n) * exp(2πi·z·n) from E_k_q_expansion
  have hE4 : ∀ w : ℍ, E₄.toFun w = 1 + 240 * ∑' (n : ℕ+), (σ 3 n) * cexp (2 * π * I * w * n) := by
    intro w
    -- E₄.toFun = E₄ by coercion, and E₄ = E 4 by definition
    have hE : E₄.toFun w = E 4 (by norm_num) w := by rfl
    have hqexp := E_k_q_expansion 4 (by norm_num) (by exact Nat.even_iff.mpr rfl) w
    -- hqexp uses ↑4 while target uses 4; they are equal
    simp only [Nat.cast_ofNat, Nat.succ_sub_succ_eq_sub, tsub_zero] at hqexp
    rw [hE, hqexp]
    -- Now goal is: 1 + (1/riemannZeta 4) * ((-2πi)^4 / 3!) * ∑'... = 1 + 240 * ...
    -- Need to show coefficient = 240
    -- Using riemannZeta_four : riemannZeta 4 = π^4 / 90
    congr 1
    have hzeta : riemannZeta 4 = (π : ℂ) ^ 4 / 90 := by
      simp only [riemannZeta_four]
    -- Coefficient = (1/(π^4/90)) * ((-2πi)^4 / 6) = (90/π^4) * (16π^4) / 6 = 240
    have hcoeff : (1 / riemannZeta 4) * ((-2 * π * I) ^ 4 / Nat.factorial 3) = (240 : ℂ) := by
      rw [hzeta]
      -- (-2πi)^4 = 16π^4 since I^4 = 1
      have hI4 : I ^ 4 = (1 : ℂ) := by norm_num [pow_succ, I_sq]
      have h1 : (-2 * (π : ℂ) * I) ^ 4 = 16 * (π : ℂ) ^ 4 := by
        have : (-2 * (π : ℂ) * I) ^ 4 = (-2) ^ 4 * (π : ℂ) ^ 4 * I ^ 4 := by ring
        rw [this, hI4]
        norm_num
      rw [h1]
      simp only [Nat.factorial_succ, Nat.reduceAdd]
      have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp
      ring
    convert mul_comm _ _ using 1
    rw [hcoeff]
    ring
  -- Step 2: Use deriv-tsum interchange
  unfold D
  have hz' : 0 < (z : ℂ).im := z.im_pos
  -- The composition E₄.toFun ∘ ofComplex agrees with the q-expansion on ℍ'
  have hE4' : ∀ w : ℂ, 0 < w.im →
      (E₄.toFun ∘ ofComplex) w = 1 + 240 * ∑' (n : ℕ+), (σ 3 n) * cexp (2 * π * I * w * n) := by
    intro w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    exact hE4 ⟨w, hw⟩
  -- Replace deriv of E₄ with deriv of q-expansion form
  have hderiv_eq : deriv (E₄.toFun ∘ ofComplex) (z : ℂ) =
      deriv (fun w => 1 + 240 * ∑' (n : ℕ+), (σ 3 n) * cexp (2 * π * I * w * n)) (z : ℂ) := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hz'] with w hw
    exact hE4' w hw
  rw [hderiv_eq]
  -- Now we need to interchange deriv with tsum
  -- Using hasDerivAt_tsum_fun from tsumderivWithin.lean
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  -- Define f n w := (σ 3 n) * cexp (2 * π * I * w * n)
  let f : ℕ+ → ℂ → ℂ := fun n w => (σ 3 n) * cexp (2 * π * I * w * n)
  -- Summability at each point
  have hf_summ : ∀ y : ℂ, 0 < y.im → Summable (fun n : ℕ+ => f n y) := by
    intro y hy
    -- |f n y| = |σ 3 n| * |exp(2πiny)| ≤ n^4 * r^n where r < 1
    -- This is summable as polynomial times geometric
    simp only [f]
    apply Summable.of_norm
    -- Use sigma_bound: σ 3 n ≤ n^4
    have hsigma_bound : ∀ n : ℕ+, (σ 3 n : ℝ) ≤ (n : ℕ) ^ 4 := fun n => by
      exact_mod_cast sigma_bound 3 n
    -- Construct UpperHalfPlane element
    let y_uhp : ℍ := ⟨y, hy⟩
    -- Use a33 with k=4 and e=1 for the bound
    have ha33 := a33 4 1 y_uhp
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (summable_norm_iff.mpr ha33)
    intro n
    simp only [Complex.norm_mul, norm_pow]
    -- |σ 3 n| * |exp(...)| ≤ n^4 * |exp(...)|
    have hσ_norm : ‖(σ 3 n : ℂ)‖ ≤ (n : ℝ) ^ 4 := by
      rw [Complex.norm_natCast]
      exact hsigma_bound n
    have hy_coe : (y_uhp : ℂ) = y := rfl
    -- After simp, goal is: (σ 3 n : ℝ) * ‖exp(...)‖ ≤ ‖n‖^4 * ‖exp(...)‖
    -- (because simp uses Complex.norm_natCast on ‖σ 3 n‖)
    -- Rewrite exponent argument to match ha33 form
    have harg : cexp (2 * π * I * y * n) = cexp (2 * π * I * (1 : ℕ+) * (y_uhp : ℂ) * n) := by
      congr 1
      -- Args needed for expression normalization even if linter says unused
      set_option linter.unusedSimpArgs false in
      simp only [hy_coe, PNat.one_coe, Nat.cast_one, Complex.ofReal_one, mul_one]
    rw [harg]
    -- Goal: (σ 3 n : ℝ) * ‖exp(...)‖ ≤ ‖n‖^4 * ‖exp(...)‖
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    -- Goal: (σ 3 n : ℝ) ≤ ‖n‖^4 = (n : ℝ)^4
    rw [Complex.norm_natCast]
    exact_mod_cast hsigma_bound n
  -- Uniform derivative bound on compact sets
  have hu : ∀ K ⊆ {w : ℂ | 0 < w.im}, IsCompact K →
      ∃ u : ℕ+ → ℝ, Summable u ∧
        ∀ (n : ℕ+) (k : K), ‖derivWithin (f n) {w | 0 < w.im} k‖ ≤ u n := by
    intro K hK hKc
    -- |deriv (f n)| = |σ 3 n| * |2πn| * |exp(...)| ≤ n^4 * 2πn * |exp(...)|
    -- Since n^4 * 2πn = n^5 * 2π ≤ (2πn)^5 (for n ≥ 1, 2π > 1)
    -- Use iter_deriv_comp_bound3 with k=5
    obtain ⟨u', hu'_sum, hu'_bound⟩ := iter_deriv_comp_bound3 K hK hKc 5
    use fun n => u' n
    constructor
    · exact hu'_sum.subtype _
    · intro n k
      rw [derivWithin_of_isOpen hopen (hK k.2)]
      simp only [f]
      have hderiv_fn : deriv (fun w => (σ 3 n : ℂ) * cexp (2 * π * I * w * n)) k =
          (σ 3 n : ℂ) * (2 * π * I * n) * cexp (2 * π * I * k * n) := by
        rw [deriv_const_mul_field]
        have h_inner_fun : (fun w : ℂ => 2 * π * I * w * n) = (fun w => (2 * π * I * n) * w) := by
          ext w; ring
        have h_deriv_inner : deriv (fun w : ℂ => 2 * π * I * w * n) k = 2 * π * I * n := by
          rw [h_inner_fun, deriv_const_mul_field, deriv_id'', mul_one]
        rw [deriv_cexp (by fun_prop : DifferentiableAt ℂ (fun w => 2 * π * I * w * n) k)]
        rw [h_deriv_inner]
        ring
      rw [hderiv_fn]
      have hσ : ‖(σ 3 n : ℂ)‖ ≤ (n : ℝ) ^ 4 := by
        rw [Complex.norm_natCast]
        exact_mod_cast sigma_bound 3 n
      have h2pin : ‖(2 * π * I * n : ℂ)‖ = 2 * |π| * n := by
        simp only [Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_I, mul_one, Complex.norm_natCast]
      have hargswap : cexp (2 * π * I * k * n) = cexp (2 * π * I * n * k) := by
        congr 1; ring
      -- n^4 * 2πn ≤ (2πn)^5 since 2π ≥ 1 and n ≥ 1
      have hbound : (n : ℝ) ^ 4 * (2 * |π| * n) ≤ (2 * |π| * n) ^ 5 := by
        have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.one_le
        have hpi : 1 ≤ 2 * |π| := by
          have : (0 : ℝ) < π := Real.pi_pos
          simp only [abs_of_pos this]
          linarith [Real.pi_gt_three]
        calc (n : ℝ) ^ 4 * (2 * |π| * n)
            = (2 * |π|) * n ^ 5 := by ring
          _ ≤ (2 * |π|) ^ 5 * n ^ 5 := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              calc (2 * |π|) = (2 * |π|) ^ 1 := by ring
                _ ≤ (2 * |π|) ^ 5 := pow_le_pow_right₀ hpi (by omega : 1 ≤ 5)
          _ = (2 * |π| * n) ^ 5 := by ring
      calc ‖(σ 3 n : ℂ) * (2 * π * I * n) * cexp (2 * π * I * k * n)‖
          = ‖(σ 3 n : ℂ)‖ * ‖(2 * π * I * n : ℂ)‖ * ‖cexp (2 * π * I * k * n)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ (n : ℝ) ^ 4 * (2 * |π| * n) * ‖cexp (2 * π * I * k * n)‖ := by
            rw [h2pin]
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            apply mul_le_mul_of_nonneg_right hσ; positivity
        _ ≤ (2 * |π| * n) ^ 5 * ‖cexp (2 * π * I * n * k)‖ := by
            rw [hargswap]
            apply mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
        _ ≤ u' n := hu'_bound n k
  -- Each term is differentiable
  have hf_diff : ∀ (n : ℕ+) (r : {w : ℂ | 0 < w.im}), DifferentiableAt ℂ (f n) r := by
    intro n r
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.cexp
    fun_prop
  -- Apply hasDerivAt_tsum_fun
  have hderiv_tsum : HasDerivAt (fun w => ∑' n : ℕ+, f n w)
      (∑' n : ℕ+, derivWithin (f n) {w | 0 < w.im} z) (z : ℂ) :=
    hasDerivAt_tsum_fun f hopen (z : ℂ) hz' hf_summ hu hf_diff
  -- deriv (1 + 240 * tsum) = 240 * deriv(tsum)
  -- First rewrite to (240 * tsum + 1) form for deriv_add_const
  have hfun_eq : (fun w => 1 + 240 * ∑' (n : ℕ+), f n w) =
      (fun w => 240 * ∑' (n : ℕ+), f n w + 1) := by ext w; ring
  have hdiff_tsum : DifferentiableAt ℂ (fun w => ∑' (n : ℕ+), f n w) z :=
    hderiv_tsum.differentiableAt
  have hderiv_add : deriv (fun w => 1 + 240 * ∑' (n : ℕ+), f n w) (z : ℂ) =
      240 * deriv (fun w => ∑' (n : ℕ+), f n w) (z : ℂ) := by
    rw [hfun_eq, deriv_add_const, deriv_const_mul _ hdiff_tsum]
  rw [hderiv_add]
  -- Extract the deriv from HasDerivAt
  have hderiv_tsum_eq : deriv (fun w => ∑' n : ℕ+, f n w) (z : ℂ) =
      ∑' n : ℕ+, derivWithin (f n) {w | 0 < w.im} z := hderiv_tsum.deriv
  rw [hderiv_tsum_eq]
  -- Compute derivWithin of each term
  have hderiv_term : ∀ n : ℕ+, derivWithin (f n) {w | 0 < w.im} z =
      (σ 3 n) * (2 * π * I * n) * cexp (2 * π * I * z * n) := by
    intro n
    rw [derivWithin_of_isOpen hopen hz']
    -- Derivative of 2πI * w * n is 2πI * n
    have hlin_deriv : deriv (fun w : ℂ => 2 * π * I * w * n) z = 2 * π * I * n := by
      have : (fun w : ℂ => 2 * π * I * w * n) = fun w => (2 * π * I * n) * w := by ext; ring
      rw [this, deriv_const_mul, deriv_id'', mul_one]
      exact differentiableAt_id
    have hderiv_exp : deriv (fun w => cexp (2 * π * I * w * n)) z =
        (2 * π * I * n) * cexp (2 * π * I * z * n) := by
      rw [deriv_cexp (by fun_prop : DifferentiableAt ℂ (fun w => 2 * π * I * w * n) z)]
      rw [hlin_deriv]
      ring
    simp only [f]
    rw [deriv_const_mul_field, hderiv_exp]
    ring
  -- First rewrite the tsum using hderiv_term
  have htsum_eq : ∑' n : ℕ+, derivWithin (f n) {w | 0 < w.im} z =
      ∑' n : ℕ+, (σ 3 n : ℂ) * (2 * π * I * n) * cexp (2 * π * I * z * n) :=
    tsum_congr hderiv_term
  rw [htsum_eq]
  -- Simplify: (2πi)⁻¹ * 240 * ∑ (σ 3 n) * (2πin) * exp(...) = 240 * ∑ n * (σ 3 n) * exp(...)
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, ofReal_eq_zero,
      Real.pi_ne_zero, I_ne_zero, or_self]
  -- Rewrite each term: (σ 3 n) * (2πIn) * exp(...) = (2πI) * n * (σ 3 n) * exp(...)
  have hterm_eq : ∀ n : ℕ+, (σ 3 n : ℂ) * (2 * π * I * n) * cexp (2 * π * I * (z : ℂ) * n) =
      (2 * π * I) * (n * (σ 3 n) * cexp (2 * π * I * n * z)) := by
    intro n
    have hexp_eq : cexp (2 * π * I * (z : ℂ) * n) = cexp (2 * π * I * n * z) := by ring_nf
    rw [hexp_eq]
    ring
  have htsum_eq2 : ∑' n : ℕ+, (σ 3 n : ℂ) * (2 * π * I * n) * cexp (2 * π * I * (z : ℂ) * n) =
      (2 * π * I) * ∑' n : ℕ+, n * (σ 3 n) * cexp (2 * π * I * n * z) := by
    rw [tsum_congr hterm_eq, tsum_mul_left]
  rw [htsum_eq2]
  -- Goal: (2πI)⁻¹ * (240 * ((2πI) * ∑ (...))) = 240 * ∑ (...)
  -- Use calc to handle the algebra step by step
  let T := ∑' n : ℕ+, (n : ℂ) * (σ 3 n) * cexp (2 * π * I * n * z)
  -- Unfold to reveal T in goal
  change (2 * π * I)⁻¹ * (240 * ((2 * π * I) * T)) = 240 * T
  calc (2 * π * I)⁻¹ * (240 * ((2 * π * I) * T))
      = (2 * π * I)⁻¹ * (2 * π * I) * (240 * T) := by ring
    _ = 1 * (240 * T) := by rw [inv_mul_cancel₀ h2pi]
    _ = 240 * T := by ring

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
    -- ramanujan_E₄ : D E₄.toFun = 3⁻¹ * (E₂ * E₄.toFun - E₆.toFun)
    -- Evaluating at z and rearranging gives the result
    have h3 : (3 : ℂ) ≠ 0 := by norm_num
    have h := congrFun ramanujan_E₄ z
    -- h : D E₄.toFun z = (3⁻¹ * (E₂ * E₄.toFun - E₆.toFun)) z
    -- Instead of simp, unfold Pi.mul directly
    -- (c * f) z where c : ℂ and f : ℍ → ℂ evaluates to c * f z
    -- But the * here might be Pi.mul with c as constant function
    -- Let's work around by computing the value directly
    calc E₂ z * E₄ z - E₆ z
        = E₂ z * E₄.toFun z - E₆.toFun z := by rfl
      _ = 3 * (3⁻¹ * (E₂ z * E₄.toFun z - E₆.toFun z)) := by field_simp
      _ = 3 * D E₄.toFun z := by
          congr 1
          -- The RHS of h is (3⁻¹ * (E₂ * E₄.toFun - E₆.toFun)) z
          -- We need to show this equals 3⁻¹ * (E₂ z * E₄.toFun z - E₆.toFun z)
          -- This follows from how Pi multiplication works
          simp only [Pi.mul_apply, Pi.sub_apply] at h
          exact h.symm
  -- Substitute D(E₄) = 240 * ∑' n, n * σ₃(n) * q^n
  rw [hRam, D_E4_qexp]
  ring

end Ramanujan_qExpansion
