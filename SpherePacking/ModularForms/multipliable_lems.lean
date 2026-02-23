module
public import SpherePacking.ModularForms.SummableLemmas.Basic
public import SpherePacking.ModularForms.SummableLemmas.Cotangent
public import SpherePacking.ModularForms.SummableLemmas.G2
public import SpherePacking.ModularForms.SummableLemmas.QExpansion
public import SpherePacking.ModularForms.SummableLemmas.IntPNat


/-!
# Multipliability lemmas for product expansions

This file records basic `Multipliable` and `tprod` lemmas used in modular form product
expansions (notably eta and delta product formulas).

## Main statements
* `MultipliableEtaProductExpansion`
* `MultipliableDeltaProductExpansion_pnat`
* `tprod_ne_zero`
* `tprod_pow`
-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ArithmeticFunction


/-this is being PRd-/
lemma Complex.summable_nat_multipliable_one_add (f : ℕ → ℂ) (hf : Summable f) :
    Multipliable (fun n : ℕ => 1 + f n) :=
  Complex.multipliable_of_summable_log (Complex.summable_log_one_add_of_summable hf)

/-- A basic nonvanishing lemma for the factors in the eta product on `ℍ`. -/
public theorem term_ne_zero (z : ℍ) (n : ℕ) :
    1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑z) ≠ 0 := by
  rw [@sub_ne_zero]
  intro h
  simpa [h.symm] using exp_upperHalfPlane_lt_one_nat z n

theorem ball_pow_ne_1 (x : ℂ) (hx : x ∈ ball 0 1) (n : ℕ) : 1 + (fun n ↦ -x ^ (n + 1)) n ≠ 0 := by
  simp only [mem_ball, dist_zero_right] at *
  rw [← sub_eq_add_neg, sub_ne_zero]
  have hxn : ‖(x ^ (n + 1))‖ < 1 := by
    simp only [norm_pow]
    refine pow_lt_one₀ ?_ hx ?_
    · exact norm_nonneg x
    omega
  intro h
  rw [← h] at hxn
  simp only [norm_one, lt_self_iff_false] at hxn

/-- If `x` lies in the open unit ball, then `∏ (1 - x^(i+1))` is a convergent infinite product. -/
public theorem multipliable_lt_one (x : ℂ) (hx : x ∈ Metric.ball 0 1) :
  Multipliable fun i ↦ 1 - x ^ (i+ 1) := by
  have := Complex.summable_nat_multipliable_one_add (fun n : ℕ => -x ^ (n + 1)) ?_
  · simpa [sub_eq_add_neg] using this
  simpa [summable_neg_iff, summable_nat_add_iff, summable_geometric_iff_norm_lt_one,
    Metric.mem_ball, dist_zero_right] using hx

/-- The eta product factors `∏ (1 - exp(2π i (n+1) z))` form a convergent infinite product. -/
public lemma MultipliableEtaProductExpansion (z : ℍ) :
    Multipliable (fun (n : ℕ) => (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ) := by
  refine (Complex.summable_nat_multipliable_one_add
    (fun n : ℕ ↦ -cexp (2 * π * Complex.I * (n + 1) * z)) ?_).congr ?_
  · rw [← summable_norm_iff]
    simpa using summable_exp_pow z
  intro n
  simp [sub_eq_add_neg]

/-- A `ℕ+`-indexed variant of `MultipliableEtaProductExpansion`. -/
public lemma MultipliableEtaProductExpansion_pnat (z : ℍ) :
  Multipliable (fun (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z))) := by
  refine (multipliable_pnat_iff_multipliable_succ
    (f := fun n : ℕ ↦ (1 - cexp (2 * π * Complex.I * n * z)))).2 ?_
  simpa using MultipliableEtaProductExpansion z

/-- If each factor is nonzero and the logarithms are summable, then the `tprod` is nonzero. -/
public lemma tprod_ne_zero (x : ℍ) (f : ℕ → ℍ → ℂ) (hf : ∀ i x, 1 + f i x ≠ 0)
  (hu : ∀ x : ℍ, Summable fun n => f n x) : (∏' i : ℕ, (1 + f i) x) ≠ 0 := by
  have htprod :
      cexp (∑' n : ℕ, log (1 + f n x)) = ∏' n : ℕ, (1 + f n x) :=
    Complex.cexp_tsum_eq_tprod (fun n => hf n x) (Complex.summable_log_one_add_of_summable (hu x))
  have hne : cexp (∑' n : ℕ, log (1 + f n x)) ≠ 0 := by
    simp
  -- rewrite the goal via `htprod`.
  simpa [htprod, Pi.add_apply, Pi.one_apply] using hne

/-- If `f` is multipliable, then so is `fun i => f i ^ n`. -/
public lemma Multipliable_pow {ι : Type*} (f : ι → ℂ) (hf : Multipliable f) (n : ℕ) :
    Multipliable (fun i => f i ^ n) := by
  simpa using hf.map (g := powMonoidHom n) (hg := by simpa using continuous_pow n)

/-- The delta product factors `∏ (1 - exp(2π i n z))^24` form a convergent infinite product. -/
public lemma MultipliableDeltaProductExpansion_pnat (z : ℍ) :
  Multipliable (fun (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z))^24) := by
  apply Multipliable_pow
  apply MultipliableEtaProductExpansion_pnat z

/-- For a multipliable family, the `tprod` commutes with taking a fixed power. -/
public lemma tprod_pow (f : ℕ → ℂ) (hf : Multipliable f) (n : ℕ) :
    (∏' (i : ℕ), f i) ^ n = ∏' (i : ℕ), (f i) ^ n := by
  simpa using hf.map_tprod (g := powMonoidHom n) (hg := by simpa using continuous_pow n)

variable {a a₁ a₂ : ℝ} {ι : Type*}

theorem hasProd_le_nonneg (f g : ι → ℝ) (h : ∀ i, f i ≤ g i) (h0 : ∀ i, 0 ≤ f i)
  (hf : HasProd f a₁) (hg : HasProd g a₂) : a₁ ≤ a₂ := by
  apply le_of_tendsto_of_tendsto' hf hg
  intro s
  apply Finset.prod_le_prod
  intros i hi
  · exact h0 i
  intros i hi
  exact h i

theorem HasProd.le_one_nonneg (g : ℕ → ℝ) (h : ∀ i, g i ≤ 1) (h0 : ∀ i, 0 ≤ g i)
    (ha : HasProd g a) : a ≤ 1 := by
  apply hasProd_le_nonneg (f := g) (g := fun _ => 1) h h0 ha hasProd_one

theorem one_le_tprod_nonneg (g : ℕ → ℝ) (h : ∀ i, g i ≤ 1) (h0 : ∀ i, 0 ≤ g i) : ∏' i, g i ≤ 1 := by
  by_cases hg : Multipliable g
  · apply hg.hasProd.le_one_nonneg g h h0
  · rw [tprod_eq_one_of_not_multipliable hg]
