module
public import SpherePacking.ModularForms.SummableLemmas.G2

/-!
# Summability lemmas for `q`-expansions

This file collects summability and `tsum` identities for exponential series on `ℍ` that are used to
derive `q`-expansions of Eisenstein series and related modular forms.

## Main statements
* `EisensteinSeries_Identity`
* `q_exp_iden`
* `tsum_sigma_eqn`
-/

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open ArithmeticFunction

theorem summable_1 (k : ℕ) (z : ℍ) (hk : 1 ≤ k) :
    Summable fun (b : ℕ) ↦ (((z : ℂ) - ↑↑b) ^ (k + 1))⁻¹ := by
  have hlin : (fun n : ℕ => (((z : ℂ) - n))⁻¹) =O[cofinite] fun n => (|(n : ℝ)|⁻¹) := by
    -- Start from the "`(-z) + n`" version (`m = -1`) and rewrite to `z - n`.
    refine (Asymptotics.IsBigO.neg_left <| linear_bigO_nat (-1) z).congr_left ?_
    intro n
    calc
      -((((-1 : ℤ) : ℂ) * (z : ℂ) + n)⁻¹) = (-( ((-1 : ℤ) : ℂ) * (z : ℂ) + n))⁻¹ := by
        simpa using (inv_neg (a := (((-1 : ℤ) : ℂ) * (z : ℂ) + n))).symm
      _ = ((z : ℂ) - n)⁻¹ := by
        congr 1
        ring
  simpa using (summable_pow_inv_of_linear_bigO (k := k) hk hlin)

theorem summable_2 (k : ℕ) (z : ℍ) (hk : 1 ≤ k) :
    Summable fun (b : ℕ) ↦ (((z : ℂ) + ↑↑b) ^ (k + 1))⁻¹ := by
  simpa [one_mul, add_comm, add_left_comm, add_assoc] using
    (summable_pow_inv_of_linear_bigO (k := k) hk (linear_bigO_nat (m := 1) z))


theorem summable_3 (m : ℕ) (y : ℍ) :
    Summable fun n : ℕ+ =>
      (-1 : ℂ) ^ m * ↑m ! * (1 / ((y : ℂ) - ↑n) ^ (m + 1)) +
        (-1) ^ m * ↑m ! * (1 / ((y : ℂ) + ↑n) ^ (m + 1)) := by
  by_cases hm : m = 0
  · simp_rw [hm]
    simp
    simpa using lhs_summable y
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm
  simp_rw [← mul_add]
  rw [summable_mul_left_iff]
  · apply Summable.add
    · simpa [Function.comp, one_div] using
        (summable_1 m y hm1).comp_injective PNat.coe_injective
    · simpa [Function.comp, one_div] using
        (summable_2 m y hm1).comp_injective PNat.coe_injective
  simp [Nat.factorial_ne_zero]


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
  · simpa [Function.comp] using (hs.subtype (s := { n : ℕ | 0 < n }))
  have he : (0 : ℝ) < (e : ℝ) := by exact_mod_cast e.pos
  let z' : ℍ := ⟨(e : ℂ) * z, by simpa [Complex.mul_im] using mul_pos he z.im_pos⟩
  simpa [z', mul_assoc, mul_left_comm, mul_comm] using exp_upperHalfPlane_lt_one z'

/-- A crude bound showing that a divisor sum is summable using `a33`. -/
public lemma hsum (k : ℕ) (z : ℍ) : Summable fun b : ℕ+ => ∑ _ ∈ (b : ℕ).divisors, b ^ k *
    ‖exp (2 * ↑π * Complex.I * ↑z * b)‖ := by
  have hs := summable_norm_iff.mpr (a33 (k + 1) 1 z)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun b => ?_) hs
  simp only [Finset.sum_const, nsmul_eq_mul, PNat.val_ofNat, Nat.cast_one, mul_one,
    Complex.norm_mul, norm_pow, norm_natCast]
  rw [← mul_assoc]
  gcongr
  rw [pow_add, mul_comm]
  gcongr
  simpa using Nat.card_divisors_le_self (b : ℕ)

/-- A sigma-type summability lemma over divisor antidiagonals used in Lambert series arguments. -/
public theorem summable_auxil_1 (k : ℕ) (z : ℍ) :
  Summable fun c : (n : ℕ+) × { x // x ∈ (n : ℕ).divisorsAntidiagonal } ↦
  ↑(↑(c.snd) : ℕ × ℕ).1 ^ k *
    cexp (2 * ↑π * Complex.I * ↑z * ↑(↑(c.snd) : ℕ × ℕ).1 * ↑↑(↑(c.snd) : ℕ × ℕ).2) := by
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg]
  constructor
  · apply fun n => (hasSum_fintype _).summable
  · simp only [Complex.norm_mul, norm_pow, RCLike.norm_natCast, tsum_fintype, Finset.univ_eq_attach]
    have H (n : ℕ+) := Finset.sum_attach ((n : ℕ).divisorsAntidiagonal) (fun (x : ℕ × ℕ) =>
      (x.1 : ℝ) ^ (k : ℕ) * ‖Complex.exp (2 * ↑π * Complex.I * z * x.1 * x.2)‖)
    have H2 (n : ℕ+) := Nat.sum_divisorsAntidiagonal ((fun (x : ℕ) => fun (y : ℕ) =>
      (x : ℝ) ^ (k : ℕ) * ‖Complex.exp (2 * ↑π * Complex.I * z * x * y)‖)) (n := n)
    conv =>
      enter [1]
      ext b
      simp
      rw [H b, H2 b]
    have hsum := hsum k z
    apply Summable.of_nonneg_of_le _ _ hsum
    · intro b
      apply Finset.sum_nonneg
      intro i hi
      simp
    · intro b
      apply Finset.sum_le_sum
      intro i hi
      simp only [Nat.mem_divisors, ne_eq, PNat.ne_zero, not_false_eq_true, and_true] at hi
      gcongr
      · apply Nat.le_of_dvd b.2 hi
      apply le_of_eq
      have hni : (i : ℂ) * (b / i : ℕ) = b := by
        norm_cast
        simp only [Finset.sum_const, nsmul_eq_mul] at *
        exact Nat.mul_div_cancel' hi
      rw [mul_assoc, hni]
  · intro i
    simp


/-- Split `∑_{m=0}^n f m` into `f 0 + ∑_{m < n} f (m+1)`. -/
public lemma sum_range_zero (f : ℤ → ℂ) (n : ℕ) : ∑ m ∈ Finset.range (n+1), f m = f 0 +
  ∑ m ∈ Finset.range n, f (m+1) := by
  simpa [add_comm] using (Finset.sum_range_succ' (f := fun m : ℕ => f m) n)


theorem exp_series_ite_deriv_uexp2 (k : ℕ) (x : {z : ℂ | 0 < z.im}) :
    iteratedDerivWithin k (fun z => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z))
    {z : ℂ | 0 < z.im} x =
    ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s))
    {z : ℂ | 0 < z.im} x := by
  -- Rewrite the series as a geometric series, use Mathlib's lemma for termwise iterated derivation,
  -- then rewrite each term back.
  have hx : (x : ℂ) ∈ ℍ' := x.2
  let z : ℍ := ⟨(x : ℂ), x.2⟩
  have hgeom (n : ℕ) (w : ℂ) :
      Complex.exp (2 * ↑π * Complex.I * n * w) = Complex.exp (2 * ↑π * Complex.I * w) ^ n := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Complex.exp_nat_mul (2 * ↑π * Complex.I * w) n)
  have hconv :
      iteratedDerivWithin k (fun w : ℂ => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * w)) ℍ' x =
        iteratedDerivWithin k (fun w : ℂ => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * w) ^ n) ℍ'
          x := by
    refine iteratedDerivWithin_congr (n := k) (s := ℍ') (x := (x : ℂ))
      (fun w _ => tsum_congr (fun n => hgeom n w)) hx
  have htsum :
      iteratedDerivWithin k (fun w : ℂ => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * w) ^ n) ℍ' x =
        ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * s) ^ n) ℍ'
          x := by
    simpa [ℍ', z] using (iteratedDerivWithin_tsum_cexp_eq k z)
  have hterm (n : ℕ) :
      iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * s) ^ n) ℍ' x =
        iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ' x := by
    refine iteratedDerivWithin_congr (n := k) (s := ℍ') (x := (x : ℂ)) (fun s _ => ?_) hx
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hgeom n s).symm
  calc
    iteratedDerivWithin k (fun w => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * w)) ℍ' x =
        iteratedDerivWithin k (fun w : ℂ => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * w) ^ n) ℍ'
          x := hconv
    _ =
        ∑' n : ℕ,
          iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * s) ^ n) ℍ' x :=
      htsum
    _ = ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ'
          x := by
        exact tsum_congr (fun n => hterm n)

theorem exp_series_ite_deriv_uexp'' (k : ℕ) (x : {z : ℂ | 0 < z.im}) :
    iteratedDerivWithin k (fun z => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z))
    {z : ℂ | 0 < z.im} x =
    ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ k * Complex.exp (2 * ↑π * Complex.I * n * x) := by
  simpa [exp_series_ite_deriv_uexp2] using (tsum_congr (fun b => exp_iter_deriv_within k b x.2))

theorem tsum_uexp_contDiffOn (k : ℕ) :
    ContDiffOn ℂ k (fun z : ℂ => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z)) ℍ' := by
  -- Use Mathlib's `contDiffOn_tsum_cexp` for the geometric series and rewrite termwise.
  have hcont :
      ContDiffOn ℂ k (fun w : ℂ => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * w) ^ n) ℍ' := by
    simpa [ℍ'] using (contDiffOn_tsum_cexp (k := (k : ℕ∞)))
  refine hcont.congr fun w _hw => ?_
  refine tsum_congr (fun n => ?_)
  simpa [mul_assoc, mul_left_comm, mul_comm] using (Complex.exp_nat_mul (2 * ↑π * Complex.I * w) n)

theorem iter_der_within_add (k : ℕ+) (x : {z : ℂ | 0 < z.im}) :
    iteratedDerivWithin k
        (fun z => ↑π * Complex.I - (2 * ↑π * Complex.I) •
        ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z)) {z : ℂ | 0 < z.im} x =
      -(2 * ↑π * Complex.I) * ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ (k : ℕ) *
      Complex.exp (2 * ↑π * Complex.I * n * x) := by
  rw [iteratedDerivWithin_const_sub (PNat.pos k)]
  simp only [smul_eq_mul, mem_setOf_eq, neg_mul]
  rw [iteratedDerivWithin_fun_neg,
    iteratedDerivWithin_const_mul x.2 <| IsOpen.uniqueDiffOn upper_half_plane_isOpen]
  · simpa using (exp_series_ite_deriv_uexp'' (k := (k : ℕ)) x)
  apply tsum_uexp_contDiffOn k
  exact x.2

theorem iter_exp_eqOn (k : ℕ+) :
    EqOn
      (iteratedDerivWithin k
        (fun z => ↑π * Complex.I - (2 * ↑π * Complex.I) • ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I
          * n * z)) {z : ℂ | 0 < z.im})
  (fun x : ℂ =>
        -(2 * ↑π * Complex.I) * ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π *
          Complex.I * n * x))
      {z : ℂ | 0 < z.im} :=
  fun z hz => iter_der_within_add k ⟨z, hz⟩

theorem summable_iter_aut (k : ℕ) (z : ℍ) :
    Summable fun n : ℕ+ => iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n))
      {z : ℂ | 0 < z.im} z := by
  refine (summable_congr
    (g := fun d : ℕ+ =>
      (-1 : ℂ) ^ k * k ! * (1 / ((z : ℂ) - d) ^ (k + 1)) +
        (-1) ^ k * k ! * (1 / ((z : ℂ) + d) ^ (k + 1)))
    (L := SummationFilter.unconditional _) (fun d => ?_)).2 ?_
  · simpa [Int.cast_natCast, one_div, Pi.add_apply] using iter_div_aut_add (d := (d : ℤ)) k z.2
  by_cases hk : 1 ≤ k
  · refine Summable.add
      (Summable.mul_left ((-1 : ℂ) ^ k * k !) <| ?_)
      (Summable.mul_left ((-1 : ℂ) ^ k * k !) <| ?_)
    · simpa [one_div] using (summable_1 k z hk).comp_injective PNat.coe_injective
    · simpa [one_div] using (summable_2 k z hk).comp_injective PNat.coe_injective
  · simp only [not_le, Nat.lt_one_iff] at hk
    simpa [hk, one_div] using lhs_summable z


lemma sub_bound (s : {z : ℂ | 0 < z.im}) (A B : ℝ) (hB : 0 < B)
    (hs : (⟨(s : ℂ), s.2⟩ : ℍ) ∈ verticalStrip A B) (k : ℕ)
    (n : ℕ+) :
    ‖((-1 : ℂ) ^ (k + 1) * (k + 1)! * (1 / (s - n) ^ (k + 2)))‖ ≤
    ‖((k + 1)! / r ⟨⟨A, B⟩, by simp [hB]⟩ ^ (k + 2)) * ((n : ℝ) ^ ((k : ℤ) +2))⁻¹‖ := by
  simp only [mem_setOf_eq, one_div, norm_pow, norm_neg, one_mem,
    CStarRing.norm_of_mem_unitary, one_pow, RCLike.norm_natCast, one_mul, norm_inv, norm_mul,
    norm_div, Real.norm_eq_abs, norm_zpow]
  rw [div_eq_mul_inv, mul_assoc]
  gcongr
  have := summand_bound_of_mem_verticalStrip (k := (k + 2)) (by norm_cast; omega) ![1,-n] hB hs
  simp only [Fin.isValue, Matrix.cons_val_zero, Int.cast_one, one_mul,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_natCast, neg_add_rev,
    ge_iff_le] at *
  simp_rw [← zpow_natCast, ← zpow_neg]
  convert this
  · rw [Int.natCast_add]
    simp [sub_eq_add_neg]
    norm_cast
  · simp only [Nat.cast_add, Nat.cast_ofNat, neg_add_rev, Int.reduceNeg]
    norm_cast
    congr
    rw [@abs_eq_self]
    apply (EisensteinSeries.r_pos _).le
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp only [neg_add_rev, Int.reduceNeg, Fin.isValue, Matrix.cons_val_zero, isUnit_one,
    Int.natAbs_of_isUnit, Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.natAbs_neg,
    Int.natAbs_natCast, Nat.cast_max, Nat.cast_one]
  norm_cast
  congr
  simp only [right_eq_sup]
  exact n.2


lemma add_bound (s : {z : ℂ | 0 < z.im}) (A B : ℝ) (hB : 0 < B)
    (hs : (⟨(s : ℂ), s.2⟩ : ℍ) ∈ verticalStrip A B) (k : ℕ)
    (n : ℕ+) :
    ‖((-1 : ℂ) ^ (k + 1) * (k + 1)! * (1 / (s + n) ^ (k + 2)))‖ ≤
    ‖((k + 1)! / r ⟨⟨A, B⟩, by simp [hB]⟩ ^ (k + 2)) * ((n : ℝ) ^ ((k : ℤ) +2))⁻¹‖ := by
  simp only [mem_setOf_eq, one_div, norm_pow, norm_neg, one_mem,
    CStarRing.norm_of_mem_unitary, one_pow, RCLike.norm_natCast, one_mul, norm_inv, norm_mul,
    norm_div, Real.norm_eq_abs, norm_zpow]
  rw [div_eq_mul_inv, mul_assoc]
  gcongr
  have := summand_bound_of_mem_verticalStrip (k := (k + 2)) (by norm_cast; omega) ![1,n] hB hs
  simp only [Fin.isValue, Matrix.cons_val_zero, Int.cast_one, one_mul,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_natCast, neg_add_rev, ge_iff_le] at *
  simp_rw [← zpow_natCast, ← zpow_neg]
  convert this
  · rw [Int.natCast_add]
    simp
    norm_cast
  · rw [Int.natCast_add]
    simp only [Nat.cast_ofNat, neg_add_rev, Int.reduceNeg]
    norm_cast
    congr
    rw [@abs_eq_self]
    apply (EisensteinSeries.r_pos _).le
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp only [neg_add_rev, Int.reduceNeg, Fin.isValue, Matrix.cons_val_zero, isUnit_one,
    Int.natAbs_of_isUnit, Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.natAbs_natCast,
    Nat.cast_max, Nat.cast_one]
  norm_cast
  congr
  simp only [right_eq_sup]
  exact n.2

theorem aut_bound_on_comp (K : Set {z : ℂ | 0 < z.im}) (hk2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ+ → ℝ,
      Summable u ∧
        ∀ (n : ℕ+) (s : K),
        ‖(derivWithin (fun z : ℂ =>
        iteratedDerivWithin k (fun z : ℂ => (z - (n : ℂ))⁻¹ + (z + n)⁻¹) {z : ℂ | 0 < z.im} z)
        {z : ℂ | 0 < z.im} s)‖ ≤
            u n := by
  by_cases h1 : Set.Nonempty K
  · let fK : {z : ℂ | 0 < z.im} → ℍ := fun z => ⟨(z : ℂ), z.2⟩
    have hfK : Continuous fK :=
      (Continuous.upperHalfPlaneMk (f := fun z : {z : ℂ | 0 < z.im} => (z : ℂ))
        continuous_subtype_val fun z => z.2)
    let Kℍ : Set ℍ := fK '' K
    have hKℍ : IsCompact Kℍ := hk2.image hfK
    obtain ⟨A, B, hB, hAB⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hKℍ
    let zAB : ℍ := ⟨⟨A, B⟩, by simp [hB]⟩
    refine ⟨fun a : ℕ+ => 2 * ‖((k + 1)! / r (zAB) ^ (k + 2)) * ((a : ℝ) ^ ((k : ℤ) +2))⁻¹‖,
      ?_, ?_⟩
    conv =>
      enter [1]
      ext a
      rw [norm_mul]
      rw [← mul_assoc]
    · apply Summable.mul_left
      simp only [norm_inv, norm_zpow, RCLike.norm_natCast]
      have : Summable fun (i : ℕ) ↦ ((i : ℝ) ^ ((k : ℤ) + 2))⁻¹ := by
        have := (Real.summable_nat_rpow_inv (p := k + 2)).mpr (by linarith)
        apply this.congr
        intro n
        norm_cast
      apply this.subtype
    intro n s
    have hsAB : fK (s : {z : ℂ | 0 < z.im}) ∈ verticalStrip A B := by
      exact hAB ⟨(s : {z : ℂ | 0 < z.im}), s.2, rfl⟩
    rw [← iteratedDerivWithin_succ]
    let S : ℂ := s
    have hS : S ∈ {z : ℂ | 0 < z.im} := by
      aesop
    have HT := iter_div_aut_add n (k+1) hS
    simp only [Int.cast_natCast, one_div, Pi.add_apply] at HT
    rw [HT]
    apply le_trans (norm_add_le _ _)
    simp_rw [mul_assoc]
    rw [two_mul]
    apply add_le_add
    · simpa [fK] using sub_bound (s := ⟨S, hS⟩) A B hB (by simpa [S] using hsAB) k n
    · simpa [fK] using add_bound (s := ⟨S, hS⟩) A B hB (by simpa [S] using hsAB) k n
  · refine ⟨fun _ => 0, summable_zero, ?_⟩
    intro n s
    exfalso
    exact h1 ⟨s.1, s.2⟩

theorem diff_on_aux (k : ℕ) (n : ℕ+) :
    DifferentiableOn ℂ
      ((fun t : ℂ => (-1 : ℂ) ^ k * k ! * (1 / (t - n) ^ (k + 1))) + fun t : ℂ =>
        (-1) ^ k * k ! * (1 / (t + n) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  have this (n : ℕ+) (z : ℂ) (hz : 0 < z.im) : (z + n) ^ (k + 1) ≠ 0 := by
    simpa using upper_ne_int ⟨z, hz⟩ n
  have this (n : ℕ+) (z : ℂ) (hz : 0 < z.im) : (z - n) ^ (k + 1) ≠ 0 := by
    simpa using upper_ne_int ⟨z, hz⟩ (-n)
  fun_prop (disch := aesop)

theorem diff_at_aux (s : {z : ℂ | 0 < z.im}) (k : ℕ) (n : ℕ+) :
    DifferentiableAt ℂ
      (fun z : ℂ => iteratedDerivWithin k (fun z : ℂ => (z - ↑n)⁻¹ + (z + ↑n)⁻¹) {z : ℂ | 0 < z.im}
        z)
      ↑s := by
  have := iter_div_aut_add n k
  apply DifferentiableOn.differentiableAt
  · apply DifferentiableOn.congr (diff_on_aux k n)
    intro r hr
    simpa [Int.cast_natCast, one_div, mem_setOf_eq, Pi.add_apply] using this hr
  exact (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simp)

theorem aut_series_ite_deriv_uexp2 (k : ℕ) (x : ℍ) :
    iteratedDerivWithin k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 < z.im} x
      =
      ∑' n : ℕ+, iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n)) {z : ℂ | 0 < z.im} x
        := by
  induction k generalizing x with
  | zero => simp only [iteratedDerivWithin_zero]
  | succ k IH =>
    rw [iteratedDerivWithin_succ]
    have HH :
      derivWithin (iteratedDerivWithin k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n)))
        {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im} x =
        derivWithin
          (fun z => ∑' n : ℕ+, iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n))
                                                     {z : ℂ | 0 < z.im} z)
          {z : ℂ | 0 < z.im}
          x := by
      apply derivWithin_congr
      · intro y hy
        apply IH ⟨y, hy⟩
      apply IH x
    simp_rw [HH]
    simp only [one_div]
    rw [derivWithin_tsum_fun']
    · apply tsum_congr
      intro b
      rw [iteratedDerivWithin_succ]
    · refine isOpen_lt ?_ ?_
      · fun_prop
      · fun_prop
    · simpa using x.2
    · intro y hy
      simpa using summable_iter_aut k ⟨y, hy⟩
    · intro K hK hK2
      have hKK2 : IsCompact (Set.image (inclusion hK) univ) :=
        IsCompact.image_of_continuousOn (isCompact_iff_isCompact_univ.mp hK2)
          (continuous_inclusion hK |>.continuousOn)
      obtain ⟨u, hu1, hu2⟩ := aut_bound_on_comp (Set.image (Set.inclusion hK) univ) hKK2 k
      refine ⟨u, hu1, ?_⟩
      intro n s
      apply hu2 n ⟨⟨s, by aesop⟩, by aesop⟩
    intro n r
    apply diff_at_aux

theorem tsum_ider_der_eq (k : ℕ) (x : {z : ℂ | 0 < z.im}) :
    ∑' n : ℕ+,
        iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n)) {z : ℂ | 0 < z.im} x =
      ∑' n : ℕ+,
        ((-1 : ℂ) ^ k * k ! * (1 / (x - n) ^ (k + 1)) +
          (-1) ^ k * k ! * (1 / (x + n) ^ (k + 1))) := by
  apply tsum_congr
  intro b
  simpa using iter_div_aut_add b k x.2


theorem auxp_series_ite_deriv_uexp''' (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n)))
    {z : ℂ | 0 < z.im})
    (fun x : ℂ =>
      ∑' n : ℕ+,
        ((-1 : ℂ) ^ k * k ! * (1 / (x - n) ^ (k + 1)) + (-1) ^ k * k ! * (1 / (x + n) ^ (k + 1))))
    {z : ℂ | 0 < z.im} := by
  intro x hx
  have h := aut_series_ite_deriv_uexp2 k ⟨x, hx⟩
  simp [one_div] at h
  simpa [h, one_div] using (tsum_ider_der_eq k ⟨x, hx⟩)


theorem tsum_aexp_contDiffOn (k : ℕ) :
    ContDiffOn ℂ k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 < z.im} := by
  apply contDiffOn_of_differentiableOn_deriv
  intro m hm
  have h1 := auxp_series_ite_deriv_uexp''' m
  apply DifferentiableOn.congr _ h1
  intro x hx
  apply HasDerivWithinAt.differentiableWithinAt
  apply hasDerivWithinAt_tsum_fun _ (isOpen_lt (by fun_prop) (by fun_prop)) _ hx
  · intro y hy
    apply summable_3 m ⟨y, hy⟩
  · intro K hK1 hK2
    have hKK2 : IsCompact (Set.image (inclusion hK1) univ) :=
      IsCompact.image_of_continuousOn (isCompact_iff_isCompact_univ.mp hK2)
        (continuous_inclusion hK1 |>.continuousOn)
    obtain ⟨u, hu1, hu2⟩ := aut_bound_on_comp (Set.image (Set.inclusion hK1) univ) hKK2 m
    refine ⟨u, hu1, ?_⟩
    intro n s
    have := hu2 n ⟨⟨s, by aesop⟩, by aesop⟩
    apply le_trans _ this
    apply le_of_eq
    congr 1
    apply derivWithin_congr
    · have h21 := (iter_div_aut_add n m).symm
      simp only [Nat.cast_le, one_div, mem_setOf_eq, coe_setOf, image_univ, Subtype.forall,
        Int.cast_natCast] at *
      intro v hv
      have h22 := h21 hv
      simp only [mem_setOf_eq, Pi.add_apply] at *
      rw [← h22]
    have hss : s.1 ∈ {z : ℂ | 0 < z.im} := by
      simpa using hK1 s.2
    have h21 := (iter_div_aut_add n m).symm hss
    simpa using h21
  intro n r
  have hN : {z : ℂ | 0 < z.im} ∈ 𝓝 r.1 :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds r.2
  have hdiff : DifferentiableOn ℂ
      ((fun t : ℂ => (-1 : ℂ) ^ m * m ! * (1 / (t - n) ^ (m + 1))) + fun t : ℂ =>
        (-1) ^ m * m ! * (1 / (t + n) ^ (m + 1))) {z : ℂ | 0 < z.im} := by
    simpa [Nat.cast_le, one_div, mem_setOf_eq] using diff_on_aux m n
  exact hdiff.differentiableAt hN


theorem aux_iter_der_tsum (k : ℕ) (hk : 1 ≤ k) (x : ℍ) :
    iteratedDerivWithin k
        ((fun z : ℂ => 1 / z) + fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 <
          z.im} x =
      (-1) ^ (k : ℕ) * (k : ℕ)! * ∑' n : ℤ, 1 / ((x : ℂ) + n) ^ (k + 1 : ℕ) := by
  rw [iteratedDerivWithin_add ?_ ?_]
  · have h1 := aut_iter_deriv 0 k x.2
    simp only [Int.cast_zero, add_zero, one_div] at *
    rw [h1]
    have := aut_series_ite_deriv_uexp2 k x
    simp only [one_div] at *
    rw [this]
    have h2 := tsum_ider_der_eq k ⟨(x : ℂ), x.2⟩
    simp only [one_div] at h2
    rw [h2]
    rw [int_tsum_pNat]
    · simp only [Int.cast_zero, add_zero, Int.cast_natCast, Int.cast_neg]
      rw [Summable.tsum_add]
      · rw [tsum_mul_left, tsum_mul_left, mul_add, mul_add] -- Pull out the scalar over the sum.
        ring_nf
      · rw [summable_mul_left_iff]
        · apply (summable_1 k x hk).subtype
        · exact neg_one_pow_mul_factorial_ne_zero k
      · rw [summable_mul_left_iff]
        · apply (summable_2 k x hk).subtype
        · exact neg_one_pow_mul_factorial_ne_zero k
    · rw [summable_int_iff_summable_nat_and_neg]
      refine ⟨summable_2 k x hk, (summable_1 k x hk).congr fun n => by simp [sub_eq_add_neg]⟩
  · have := (aut_contDiffOn 0 k)
    simp only [Int.cast_zero, sub_zero, one_div] at *
    apply this.contDiffWithinAt
    exact x.2
  · apply tsum_aexp_contDiffOn k
    exact x.2
  · exact x.2
  · refine IsOpen.uniqueDiffOn ?_
    refine isOpen_lt ?_ ?_
    · fun_prop
    · fun_prop

theorem aux_iter_der_tsum_eqOn (k : ℕ) (hk : 2 ≤ k) :
    EqOn (iteratedDerivWithin (k - 1)
    ((fun z : ℂ => 1 / z) + fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 < z.im})
    (fun z : ℂ => (-1) ^ (k - 1) * (k - 1)! * ∑' n : ℤ, 1 / (z + n) ^ (k : ℕ)) {z : ℂ | 0 < z.im}
    := by
  intro z hz
  have hk0 : 1 ≤ k - 1 := le_tsub_of_add_le_left hk
  have := aux_iter_der_tsum (k - 1) hk0 ⟨z, hz⟩
  have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (by linarith)
  rw [hk1] at this
  norm_cast at *


theorem pos_sum_eq (k : ℕ) (hk : 0 < k) :
    (fun x : ℂ =>
        -(2 * ↑π * Complex.I) * ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π *
          Complex.I * n * x)) =
      fun x : ℂ =>
      -(2 * ↑π * Complex.I) * ∑' n : ℕ+, (2 * ↑π * Complex.I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π *
        Complex.I * n * x) := by
  funext x
  let f : ℕ → ℂ := fun n =>
    (2 * ↑π * Complex.I * n) ^ k * Complex.exp (2 * ↑π * Complex.I * n * x)
  have hf0 : f 0 = 0 := by
    have hk' : k ≠ 0 := Nat.ne_of_gt hk
    simp [f, hk']
  simpa [f] using
    congrArg (fun t : ℂ => -(2 * ↑π * Complex.I) * t) ((tsum_pNat (f := f) hf0).symm)

theorem cot_series_repr (z : ℍ) :
    ↑π * cot (↑π * z) - 1 / z = ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) := by
  have h := cot_series_rep' (UpperHalfPlane.coe_mem_integerComplement z)
  simp only [one_div] at *
  have hrw := tsum_pnat_eq_tsum_succ3 fun n : ℕ => (1 / ((z : ℂ) - n) + 1 / (z + n))
  simp only [one_div, Nat.cast_add, Nat.cast_one] at hrw
  simpa [hrw] using h


/-- A `q`-expansion identity for the cotangent series on `ℍ`. -/
public lemma EisensteinSeries_Identity (z : ℍ) :
    1 / z + ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) =
      π * Complex.I - 2 * π * Complex.I * ∑' n : ℕ, Complex.exp (2 * π * Complex.I * z) ^ n := by
  simpa [add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm] using
    (sub_eq_iff_eq_add.1 (cot_series_repr z)).symm.trans (pi_mul_cot_pi_q_exp z)


theorem q_exp_iden'' (k : ℕ) (hk : 2 ≤ k) :
    EqOn (fun z : ℂ => (-1 : ℂ) ^ (k - 1) * (k - 1)! * ∑' d : ℤ, 1 / ((z : ℂ) + d) ^ k)
      (fun z : ℂ =>
        -(2 * ↑π * Complex.I) * ∑' n : ℕ+, (2 * ↑π * Complex.I * n) ^ ((k - 1) : ℕ) * Complex.exp (2
          * ↑π * Complex.I * n * z))
      {z : ℂ | 0 < z.im} := by
  have := (aux_iter_der_tsum_eqOn k hk).symm
  apply EqOn.trans this
  have hkpos : 0 < k - 1 := by omega
  have h2 := (iter_exp_eqOn (⟨k - 1, hkpos⟩ : ℕ+)).symm
  simp only [one_div, PNat.mk_coe, neg_mul, smul_eq_mul] at *
  have h3 := pos_sum_eq (k - 1) hkpos
  simp only [neg_mul] at h3
  rw [h3] at h2
  apply EqOn.symm
  apply EqOn.trans h2
  apply iteratedDerivWithin_congr
  intro z hz
  simp only [Pi.add_apply]
  have := EisensteinSeries_Identity ⟨z, hz⟩
  simp only [tsub_pos_iff_lt, one_div] at *
  rw [this]
  congr
  ext n
  rw [← Complex.exp_nsmul]
  congr
  ring

/-- A `q`-expansion for `∑_{d : ℤ} 1 / (z + d)^k` for `k ≥ 2`. -/
public theorem q_exp_iden (k : ℕ) (hk : 2 ≤ k) (z : ℍ) :
    ∑' d : ℤ, 1 / ((z : ℂ) + d) ^ k =
      (-2 * ↑π * Complex.I) ^ k / (k - 1)! * ∑' n : ℕ+, n ^ ((k - 1)) * Complex.exp (2 * ↑π *
        Complex.I * z * n) := by
  have := q_exp_iden'' k hk z.2
  simp only [one_div, neg_mul] at *
  have hk2 : (-1 : ℂ) ^ ((k - 1)) * (k - 1)! ≠ 0 := by
    exact neg_one_pow_mul_factorial_ne_zero (k - 1)
  rw [← mul_right_inj' hk2]
  rw [this]
  have h3 : (-1) ^ ((k - 1)) * ↑(k - 1)! * ((-(2 * ↑π * Complex.I)) ^ k / ↑(k - 1)!) = -(2 * ↑π *
    Complex.I) ^ k := by
    have hk1 : 1 ≤ k := by linarith
    have hkfac : (↑(k - 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k - 1)
    have hodd : Odd ((k - 1) + k) := by
      simpa [Nat.sub_add_cancel hk1, add_assoc] using
        (odd_add_self_one' (a := k - 1) : Odd ((k - 1) + ((k - 1) + 1)))
    have hcancel :
        (↑(k - 1)! : ℂ) * ((-(2 * ↑π * Complex.I)) ^ k / ↑(k - 1)!) =
          (-(2 * ↑π * Complex.I)) ^ k := by
      simpa [mul_div_assoc, mul_assoc] using
        (mul_div_cancel_left₀ ((-(2 * ↑π * Complex.I)) ^ k) hkfac)
    calc
      (-1 : ℂ) ^ (k - 1) * (↑(k - 1)! : ℂ) * ((-(2 * ↑π * Complex.I)) ^ k / ↑(k - 1)!) =
          (-1 : ℂ) ^ (k - 1) * (-(2 * ↑π * Complex.I)) ^ k := by
        rw [mul_assoc]
        simp [hcancel]
      _ = (-1 : ℂ) ^ (k - 1) * ((-1 : ℂ) ^ k * (2 * ↑π * Complex.I) ^ k) := by
        have hneg : (-(2 * ↑π * Complex.I)) ^ k =
            (-1 : ℂ) ^ k * (2 * ↑π * Complex.I) ^ k := by
          simpa [mul_assoc] using (neg_pow (2 * (↑π * Complex.I)) k)
        simp [hneg]
      _ = (-1 : ℂ) ^ ((k - 1) + k) * (2 * ↑π * Complex.I) ^ k := by
        rw [mul_assoc]
        simpa [mul_assoc] using congrArg (fun t : ℂ => t * (2 * ↑π * Complex.I) ^ k)
          ((pow_add (-1 : ℂ) (k - 1) k).symm)
      _ = -(2 * ↑π * Complex.I) ^ k := by
        simp [Odd.neg_one_pow hodd, mul_assoc]
  rw [← mul_assoc]
  norm_cast at *
  simp only [Int.reduceNegSucc, Int.reduceNeg, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast, ofReal_mul, ofReal_ofNat, mul_eq_zero, pow_eq_zero_iff',
    neg_eq_zero, one_ne_zero, ne_eq, false_and, Int.natCast_eq_zero, false_or, PNat.pow_coe,
    Nat.cast_pow] at *
  rw [h3]
  have hee :
    ∑' n : ℕ+, (2 * ↑π * Complex.I * ((n : ℕ) : ℂ)) ^ ((k - 1) : ℕ) *
        exp (2 * ↑π * Complex.I * ((n : ℕ) : ℂ) * ↑z) =
      (2 * ↑π * Complex.I) ^ (k - 1) *
        ∑' n : ℕ+, n ^ (k - 1) * exp (2 * ↑π * Complex.I * ↑z * n) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro b
    rw [← mul_assoc]
    ring_nf
  simp only [neg_mul, neg_inj] at *
  rw [hee]
  rw [← mul_assoc]
  have he2 : 2 * ↑π * Complex.I * (2 * ↑π * Complex.I) ^ (k - 1) = (2 * ↑π * Complex.I) ^ k := by
    have hke : k = 1 + (k - 1) := by
      apply symm; apply Nat.add_sub_of_le
      linarith
    nth_rw 2 [hke]
    norm_cast
    rw [pow_add]
    simp
  rw [he2]

/-- A Lambert-series identity rewriting a double `tsum` in terms of `sigma`. -/
public theorem tsum_sigma_eqn2 (k : ℕ) (z : ℍ) :
    ∑' (c : Fin 2 → ℕ+), (c 0 ^ k : ℂ) * Complex.exp (2 * ↑π * Complex.I * z * c 0 * c 1) =
      ∑' e : ℕ+, sigma k e * Complex.exp (2 * ↑π * Complex.I * z * e) := by
  -- Use Mathlib's Lambert-series identity `tsum_prod_pow_eq_tsum_sigma`.
  let q : ℂ := Complex.exp (2 * ↑π * Complex.I * z)
  have hq : ‖q‖ < 1 := by
    simpa [q] using exp_upperHalfPlane_lt_one z
  have hqpow (n : ℕ) : q ^ n = Complex.exp ((n : ℂ) * (2 * ↑π * Complex.I * z)) := by
    simpa [q, mul_assoc] using (Complex.exp_nat_mul (2 * ↑π * Complex.I * z) n).symm
  have hexp (a b : ℕ+) : Complex.exp (2 * ↑π * Complex.I * z * a * b) = q ^ (a * b : ℕ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm, Nat.cast_mul] using (hqpow (a * b : ℕ)).symm
  have hexp' (e : ℕ+) : Complex.exp (2 * ↑π * Complex.I * z * e) = q ^ (e : ℕ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hqpow (e : ℕ)).symm
  rw [← (piFinTwoEquiv fun _ => ℕ+).symm.tsum_eq]
  simp only [piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one]
  simp_rw [hexp, hexp']
  have hswap :
      (∑' c : ℕ+ × ℕ+, (c.1 : ℂ) ^ k * q ^ (c.1 * c.2 : ℕ)) =
        ∑' c : ℕ+ × ℕ+, (c.2 : ℂ) ^ k * q ^ (c.1 * c.2 : ℕ) := by
    let f : ℕ+ × ℕ+ → ℂ := fun c ↦ (c.1 : ℂ) ^ k * q ^ (c.1 * c.2 : ℕ)
    simpa [f, Nat.mul_comm] using ((Equiv.prodComm ℕ+ ℕ+).tsum_eq (f := f)).symm
  rw [hswap]
  have hs : Summable fun c : ℕ+ × ℕ+ ↦ (c.2 : ℂ) ^ k * q ^ (c.1 * c.2 : ℕ) := by
    simpa [q, mul_assoc] using (summable_prod_mul_pow (𝕜 := ℂ) k hq)
  rw [hs.tsum_prod]
  simpa [q] using (tsum_prod_pow_eq_tsum_sigma (𝕜 := ℂ) k hq)

/-- Summability of `∑_{d : ℤ} 1 / ((n z) + d)^k` for `k ≥ 2` and `z ∈ ℍ`. -/
public lemma G2_summable_aux (n : ℤ) (z : ℍ) (k : ℤ) (hk : 2 ≤ k) :
    Summable fun d : ℤ => ((((n : ℂ) * z) + d) ^ k)⁻¹ := by
  apply summable_inv_of_isBigO_rpow_inv (show 1 < (k : ℝ) by norm_cast)
  lift k to ℕ using (by linarith)
  simpa using (linear_bigO_pow n z k)

/-- A cleaner version of `tsum_sigma_eqn2` with product indexing by `ℕ+ × ℕ+`. -/
public theorem tsum_sigma_eqn {k : ℕ} (z : ℍ) :
    ∑' c : ℕ+ × ℕ+, (c.1 ^ k : ℂ) * Complex.exp (2 * ↑π * Complex.I * z * c.1 * c.2) =
      ∑' e : ℕ+, sigma k e * Complex.exp (2 * ↑π * Complex.I * e * z) := by
  rw [← (piFinTwoEquiv fun _ => ℕ+).tsum_eq]
  simpa [piFinTwoEquiv_apply, Fin.isValue, mul_assoc, mul_left_comm, mul_comm] using
    (tsum_sigma_eqn2 k z)

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

/-- Summability of a geometric series with a fixed prefactor. -/
public theorem a1 (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ => (e : ℂ) ^ (k - 1) * exp (2 * ↑π * Complex.I * ↑z * e * c) := by
  refine Summable.mul_left _ ?_
  have he : (0 : ℝ) < (e : ℝ) := by
    exact_mod_cast e.pos
  let z' : ℍ := ⟨(e : ℂ) * z, by simpa [Complex.mul_im] using mul_pos he z.im_pos⟩
  have hz' : ‖Complex.exp (2 * ↑π * Complex.I * z')‖ < 1 := exp_upperHalfPlane_lt_one z'
  refine (summable_geometric_iff_norm_lt_one.2 hz').congr (fun c => ?_)
  simpa [z', mul_assoc, mul_left_comm, mul_comm] using
    (Complex.exp_nat_mul (2 * ↑π * Complex.I * z') c).symm


/-- A summability lemma for a two-variable exponential sum, used with divisor antidiagonals. -/
public theorem a4 (k : ℕ) (z : ℍ) :
    Summable (uncurry fun b c : ℕ+ => ↑b ^ (k - 1) * exp (2 * ↑π * Complex.I * ↑c * ↑z * ↑b)) := by
  -- Use the antidiagonal equivalence `sigmaAntidiagonalEquivProd` (Mathlib) to reduce
  -- to the sigma-type summability lemma `summable_auxil_1`.
  rw [sigmaAntidiagonalEquivProd.summable_iff.symm]
  refine (summable_auxil_1 (k - 1) z).congr ?_
  intro b
  -- Unfold the equivalence and normalize the exponent by commutativity/associativity in `ℂ`.
  simp only [comp_apply, uncurry_apply_pair, sigmaAntidiagonalEquivProd,
    divisorsAntidiagonalFactors, Equiv.coe_fn_mk, PNat.mk_coe]
  ring_nf

/-- A specialized evaluation of a `tsum` using `q_exp_iden` at `k = 2`. -/
public lemma t9 (z : ℍ) : ∑' m : ℕ,
  ( 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ ((2 - 1)) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n)) = -
    8 * π ^ 2 * ∑' (n : ℕ+), (sigma 1 n) * cexp (2 * π * Complex.I * n * z) := by
  have := tsum_pnat_eq_tsum_succ3 (fun m => 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ ((2 - 1)) * Complex.exp (2 * ↑π * Complex.I * (m) * z * n))
  simp only [neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one, Nat.factorial_one, Nat.cast_one,
    div_one, pow_one, Nat.cast_add] at *
  rw [← this]
  rw [tsum_mul_left, ← tsum_sigma_eqn z (k := 1)]
  have he : 2 * (2 * ↑π * Complex.I) ^ 2 = - 8 * π ^ 2 := by
    rw [pow_two]; ring_nf; simp [I_sq, mul_neg, mul_one, neg_mul]
  rw [he]
  simp only [neg_mul, pow_one, neg_inj, mul_eq_mul_left_iff, mul_eq_zero, OfNat.ofNat_ne_zero,
    ne_eq, not_false_eq_true, pow_eq_zero_iff, ofReal_eq_zero, false_or]
  left
  symm
  simp only [neg_mul] at *
  rw [Summable.tsum_prod, Summable.tsum_comm']
  · congr
    funext m
    congr
    funext n
    simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero, PNat.ne_zero, or_false]
    congr 1
    ring
  · have := (a4 2 z).prod_symm
    simp only [Nat.add_one_sub_one, pow_one] at *
    apply this.congr
    intro b
    rw [Prod.swap]
    simp [uncurry]
    ring_nf
  · intro e
    have := a33 (k := 1) e z
    simp only [pow_one] at *
    apply this.congr
    intro b
    ring_nf
  · intro e
    have := a1 2 e z
    simp only [Nat.add_one_sub_one, pow_one] at *
    apply this.subtype
  have := a4 2 z
  apply this.congr
  intro b
  simp [uncurry]
  congr 1
  ring
