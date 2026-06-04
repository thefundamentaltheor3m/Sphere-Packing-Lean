module
public import SpherePacking.ModularForms.FG.Basic
import SpherePacking.ModularForms.DimensionFormulas
import SpherePacking.ForMathlib.ExpPiIMulMulI


/-!
# Positivity results for `F` and `G`

This file proves positivity statements on the imaginary axis for the key functions `F` and `G`,
and for the Serre derivative `SerreDer_22_L₁₀`.

## Main declarations
* `F_pos`, `G_pos`
* `SerreDer_22_L₁₀_pos`
-/


open scoped Real Manifold Topology ArithmeticFunction.sigma ModularForm MatrixGroups Derivative
open Filter Complex UpperHalfPlane
open ModularForm hiding E₄ E₆

-- Ensure the `SL(2,ℤ)` Möbius action on `ℍ` is available below.
noncomputable local instance : MulAction SL(2, ℤ) ℍ := UpperHalfPlane.SLAction (R := ℤ)

/-- The real part of `A_E τ` is positive on the imaginary axis. The proof bounds the q-series
of `A_E τ = 720 · ∑ n · σ₃(n) · q^n` from below by its positive first term `720 · 1 · σ₃(1) · r`. -/
private lemma A_E_re_pos_on_imag_axis (t : ℝ) (ht : 0 < t)
    (τ : UpperHalfPlane) (hτ : (τ : ℂ) = Complex.I * t) :
    0 < (A_E τ).re := by
  set A : ℂ := A_E τ
  let term : ℕ+ → ℂ :=
    fun n => (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (τ : ℂ))
  have hseries : A = (720 : ℂ) * ∑' n : ℕ+, term n := by
    simpa [A, A_E, term, mul_assoc, mul_left_comm, mul_comm] using (E₂_mul_E₄_sub_E₆ τ)
  set r : ℝ := Real.exp (-2 * Real.pi * t) with hr
  have hIImul (x : ℂ) : Complex.I * (Complex.I * x) = -x := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have exp_neg_two_pi_mul_eq (n : ℕ) :
      Real.exp (-(2 * Real.pi * (n : ℝ) * t)) = r ^ n := by
    rw [show (-(2 * Real.pi * (n : ℝ) * t)) = (n : ℝ) * (-2 * Real.pi * t) from by ring,
      Real.exp_nat_mul]
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_lt_one : r < 1 := by
    have : (-2 * Real.pi * t) < 0 := by nlinarith [Real.pi_pos]
    simpa [hr] using (Real.exp_lt_one_iff.2 this)
  have hr_norm : ‖r‖ < 1 := by simpa [Real.norm_of_nonneg hr_pos.le] using hr_lt_one
  -- Each `term n` is a complex number whose real part is `n · σ₃(n) · rⁿ ≥ 0`.
  have hterm_re (n : ℕ+) :
      (term n).re = (n : ℝ) * (σ 3 n : ℝ) * r ^ (n : ℕ) := by
    have harg : (2 * π * Complex.I * (n : ℂ) * (τ : ℂ) : ℂ) =
        ((-(2 * Real.pi * (n : ℝ) * t) : ℝ) : ℂ) := by
      simp [hτ, mul_assoc, mul_left_comm, mul_comm, hIImul]
    have hexp : cexp (2 * π * Complex.I * (n : ℂ) * (τ : ℂ)) =
        (Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℂ) := by rw [harg]; simp
    have hexp' : cexp (2 * π * Complex.I * (n : ℂ) * (τ : ℂ)) = ((r ^ (n : ℕ) : ℝ) : ℂ) := by
      rw [hexp]; exact_mod_cast congrArg ((↑) : ℝ → ℂ) (exp_neg_two_pi_mul_eq (n : ℕ))
    have hterm : term n = ((n : ℂ) * (σ 3 n : ℂ)) * ((r ^ (n : ℕ) : ℝ) : ℂ) := by
      dsimp [term]; rw [hexp']
    have hr_re : (((r ^ (n : ℕ) : ℝ) : ℂ)).re = r ^ (n : ℕ) := Complex.ofReal_re _
    have hr_im : (((r ^ (n : ℕ) : ℝ) : ℂ)).im = 0 := Complex.ofReal_im _
    rw [hterm, Complex.mul_re, hr_re, hr_im]
    simp [Complex.mul_re, Complex.mul_im, mul_comm, mul_left_comm]
  -- Bound the norm of `term n` by `n⁵ · rⁿ`, a summable majorant.
  have hsum_term : Summable term := by
    have hsum_g : Summable (fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5 hr_norm
    have hsum_g' : Summable (fun n : ℕ+ => ((n : ℝ) ^ 5 : ℝ) * r ^ (n : ℕ)) :=
      (nat_pos_tsum2 (f := fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * r ^ n) (by simp)).2 hsum_g
    refine Summable.of_norm_bounded (g := fun n : ℕ+ => ((n : ℝ) ^ 5 : ℝ) * r ^ (n : ℕ))
      hsum_g' fun n => ?_
    have harg : (2 * π * Complex.I * (n : ℂ) * (τ : ℂ) : ℂ) =
        ((-(2 * Real.pi * (n : ℝ) * t) : ℝ) : ℂ) := by
      simp [hτ, mul_assoc, mul_left_comm, mul_comm, hIImul]
    have hexp : cexp (2 * π * Complex.I * (n : ℂ) * (τ : ℂ)) =
        (Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℂ) := by rw [harg]; simp
    have hnorm_exp : ‖cexp (2 * π * Complex.I * (n : ℂ) * (τ : ℂ))‖ = r ^ (n : ℕ) := by
      rw [hexp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        exp_neg_two_pi_mul_eq (n : ℕ)]
    have hσ : (σ 3 n : ℝ) ≤ (n : ℝ) ^ 4 := by exact_mod_cast (sigma_bound 3 (n : ℕ))
    have hcoeff : (n : ℝ) * (σ 3 n : ℝ) ≤ (n : ℝ) ^ 5 := by
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left hσ hn0
    calc
      ‖term n‖
          = ‖(n : ℂ) * (σ 3 n : ℂ)‖ * ‖cexp (2 * π * Complex.I * (n : ℂ) * (τ : ℂ))‖ := by
            simp [term, mul_assoc]
      _ ≤ ((n : ℝ) * (σ 3 n : ℝ)) * (r ^ (n : ℕ)) := by simp [hnorm_exp]
      _ ≤ ((n : ℝ) ^ 5 : ℝ) * r ^ (n : ℕ) := by gcongr
  -- Conclude the real part is positive.
  have hsum_re : Summable (fun n : ℕ+ => (term n).re) := hsum_term.mapL Complex.reCLM
  have htsum_pos : 0 < ∑' n : ℕ+, (term n).re :=
    hsum_re.tsum_pos (fun n => by rw [hterm_re]; positivity)
      1 (by rw [hterm_re]; positivity)
  have hA_re : A.re = 720 * ∑' n : ℕ+, (term n).re := by
    have h := congrArg Complex.re hseries
    have hre_tsum : (∑' n : ℕ+, term n).re = ∑' n : ℕ+, (term n).re :=
      Complex.reCLM.map_tsum hsum_term
    simpa [hre_tsum, Complex.mul_re, mul_assoc] using h
  rw [show (A_E τ).re = A.re from rfl, hA_re]; exact mul_pos (by norm_num) htsum_pos

/-- The function `F` is positive on the imaginary axis. -/
public lemma F_pos : ResToImagAxis.Pos F := by
  have hbase : ResToImagAxis.Real (E₂ * E₄.toFun - E₆.toFun) :=
    .sub (.mul E₂_imag_axis_real E₄_imag_axis_real) E₆_imag_axis_real
  refine ⟨by simpa [F, pow_two] using hbase.mul hbase, ?_⟩
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, F]
  set τ : UpperHalfPlane := ⟨Complex.I * t, by simp [ht]⟩
  have hτ : (τ : ℂ) = Complex.I * t := rfl
  have hA_im : (A_E τ).im = 0 := by
    simpa [A_E, τ, Function.resToImagAxis, ResToImagAxis, ht] using hbase t ht
  have hA_pos : 0 < (A_E τ).re := A_E_re_pos_on_imag_axis t ht τ hτ
  have hF_re : ((A_E τ) ^ 2).re = (A_E τ).re ^ 2 := by simp [pow_two, Complex.mul_re, hA_im]
  simpa [A_E] using (hF_re ▸ pow_pos hA_pos 2 : 0 < ((A_E τ) ^ 2).re)

/-- The function `G` is positive on the imaginary axis. -/
public lemma G_pos : ResToImagAxis.Pos G := by
  have hH2 : ResToImagAxis.Pos H₂ := H₂_imag_axis_pos
  have hH4 : ResToImagAxis.Pos H₄ := H₄_imag_axis_pos
  have hconst {c : ℝ} (hc : 0 < c) : ResToImagAxis.Pos (fun _ : ℍ => (c : ℂ)) := by
    refine ⟨?_, ?_⟩ <;> intro t ht <;> simp [Function.resToImagAxis, ResToImagAxis, ht, hc]
  have hH2sq : ResToImagAxis.Pos (H₂ ^ 2) := by simpa [pow_two] using hH2.mul hH2
  have hH2cube : ResToImagAxis.Pos (H₂ ^ 3) := by
    simpa [pow_succ, pow_two, Nat.succ_eq_add_one, mul_assoc] using hH2sq.mul hH2
  have hH4sq : ResToImagAxis.Pos (H₄ ^ 2) := by simpa [pow_two] using hH4.mul hH4
  have hpoly : ResToImagAxis.Pos (2 * H₂ ^ 2 + 5 * H₂ * H₄ + 5 * H₄ ^ 2) := by
    have h1 : ResToImagAxis.Pos (2 * H₂ ^ 2) := by
      simpa [mul_assoc] using (hconst (c := 2) (by positivity)).mul hH2sq
    have h2 : ResToImagAxis.Pos (5 * H₂ * H₄) := by
      simpa [mul_assoc] using (hconst (c := 5) (by positivity)).mul (hH2.mul hH4)
    have h3 : ResToImagAxis.Pos (5 * H₄ ^ 2) := by
      simpa [mul_assoc] using (hconst (c := 5) (by positivity)).mul hH4sq
    simpa [add_assoc] using (h1.add h2).add h3
  simpa [G, mul_assoc] using ResToImagAxis.Pos.mul hH2cube hpoly

/-- q-expansion of `E₂` in sigma form: `E₂(z) = 1 - 24 * ∑ σ₁(n) q^n`. -/
public lemma E₂_eq_sigma_qexp (z : UpperHalfPlane) :
    E₂ z =
      1 - 24 * ∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
  have hE := E₂_eq z
  have hLambert :
      (∑' n : ℕ+,
          (n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) /
            (1 - cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)))) =
        ∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
    have hNat :
        (∑' n : ℕ,
            ((n + 1 : ℕ) : ℂ) * cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)) /
              (1 - cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)))) =
          ∑' n : ℕ, (σ 1 (n + 1) : ℂ) * cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)) := by
      simpa using (tsum_eq_tsum_sigma z)
    simpa using
      (tsum_pnat_eq_tsum_succ3 (f := fun n : ℕ =>
        (n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) /
          (1 - cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))))).trans
        (hNat.trans
          (tsum_pnat_eq_tsum_succ3 (f := fun n : ℕ =>
            (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)))).symm)
  simpa [hLambert] using hE

/-- The `E₂` q-coefficient at index `n`: `1` for `n = 0`, else `-24 · σ₁(n)`. -/
private noncomputable def E₂Coeff (n : ℕ) : ℂ :=
  if n = 0 then (1 : ℂ) else (-24 : ℂ) * (σ 1 n : ℂ)

/-- The `E₂` q-series is summable: bound `‖aₙ qⁿ‖ ≤ rⁿ + 24 n² rⁿ` with `r = ‖q‖ < 1`. -/
private lemma E₂_qexp_summable (z : UpperHalfPlane) :
    Summable (fun n : ℕ => E₂Coeff n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))) := by
  set r : ℝ := ‖cexp (2 * π * Complex.I * (z : ℂ))‖ with hr
  have hr_nonneg : 0 ≤ r := norm_nonneg _
  have hr_norm : ‖r‖ < 1 := by
    simpa [Real.norm_of_nonneg hr_nonneg] using (exp_upperHalfPlane_lt_one z)
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2 : ℝ) * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr_norm
  have hbound : ∀ n : ℕ,
      ‖E₂Coeff n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))‖ ≤
        1 * r ^ n + (24 : ℝ) * ((n : ℝ) ^ 2 * r ^ n) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp [E₂Coeff, r]
    · have hqpow : ‖cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))‖ = r ^ n := by
        have hexp : cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) =
            cexp (2 * π * Complex.I * (z : ℂ)) ^ n := by simpa using (exp_aux z n)
        simp [r, hr, hexp, norm_pow]
      have hσ : (σ 1 n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast (sigma_bound 1 n)
      have ha_norm : ‖E₂Coeff n‖ ≤ (24 : ℝ) * (n : ℝ) ^ 2 := by
        have : E₂Coeff n = (-24 : ℂ) * (σ 1 n : ℂ) := by simp [E₂Coeff, hn]
        simp_all
      calc
        ‖E₂Coeff n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))‖
            = ‖E₂Coeff n‖ * ‖cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))‖ := by simp
        _ ≤ ((24 : ℝ) * (n : ℝ) ^ 2) * (r ^ n) := by
              rw [hqpow]; exact mul_le_mul_of_nonneg_right ha_norm (pow_nonneg hr_nonneg _)
        _ ≤ 1 * r ^ n + (24 : ℝ) * ((n : ℝ) ^ 2 * r ^ n) := by
              nlinarith [hr_nonneg, pow_nonneg hr_nonneg n]
  exact Summable.of_norm_bounded (g := fun n : ℕ =>
    (1 : ℝ) * r ^ n + (24 : ℝ) * ((n : ℝ) ^ 2 * r ^ n))
    (((summable_geometric_of_norm_lt_one hr_norm).mul_left 1).add (hs.mul_left 24))
    (fun n => hbound n)

/-- The complement (`n ≠ 0` part) of the `E₂` q-series equals `-24 · ∑_{n≥1} σ₁(n) qⁿ`. -/
private lemma E₂_qexp_compl_eq (z : UpperHalfPlane) :
    (∑' n : ℕ, ite (n = 0) 0
        (E₂Coeff n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)))) =
      (-24 : ℂ) * ∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
  have hpnat :
      (∑' n : ℕ, ite (n = 0) 0
          (E₂Coeff n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)))) =
        ∑' n : ℕ+, ite ((n : ℕ) = 0) 0
          (E₂Coeff (n : ℕ) * cexp (2 * π * Complex.I * ((n : ℕ) : ℂ) * (z : ℂ))) := by
    simpa using (tsum_pNat
      (f := fun n : ℕ => ite (n = 0) 0
        (E₂Coeff n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))))
      (hf := by simp)).symm
  have hite : (fun n : ℕ+ => ite ((n : ℕ) = 0) 0
        (E₂Coeff (n : ℕ) * cexp (2 * π * Complex.I * ((n : ℕ) : ℂ) * (z : ℂ)))) =
      fun n : ℕ+ => (-24 : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
    funext n
    simp [E₂Coeff, Nat.ne_of_gt n.pos, mul_assoc]
  rw [hpnat, show (∑' n : ℕ+, ite ((n : ℕ) = 0) 0
      (E₂Coeff (n : ℕ) * cexp (2 * π * Complex.I * ((n : ℕ) : ℂ) * (z : ℂ)))) =
        ∑' n : ℕ+, (-24 : ℂ) * (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))
      from by simpa using congrArg (fun f : ℕ+ → ℂ => ∑' n : ℕ+, f n) hite]
  simpa [mul_assoc] using
    (tsum_mul_left (a := (-24 : ℂ))
      (f := fun n : ℕ+ => (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))))

/-- A `ℕ`-indexed q-expansion of `E₂` (including the constant term). -/
public lemma E₂_eq_qexp (z : UpperHalfPlane) :
    E₂ z =
      ∑' n : ℕ,
        (if n = 0 then (1 : ℂ) else (-24 : ℂ) * (σ 1 n : ℂ)) *
          cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
  have hEσ := E₂_eq_sigma_qexp z
  have hsum := E₂_qexp_summable z
  have htsum_split := hsum.tsum_eq_add_tsum_ite (b := 0)
  have hcompl := E₂_qexp_compl_eq z
  have ha0 : E₂Coeff 0 * cexp (2 * π * Complex.I * (0 : ℂ) * (z : ℂ)) = (1 : ℂ) := by
    simp [E₂Coeff]
  change E₂ z = ∑' n : ℕ, E₂Coeff n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))
  grind only

private lemma cexp_two_pi_I_nat_mul_I_mul (t : ℝ) (n : ℕ) :
    cexp (2 * π * Complex.I * n * (Complex.I * t)) = (rexp (-(2 * π * n * t)) : ℂ) := by
  ring_nf; simp

/-- The q-coefficient for `-D(E₂)`: `0` at `n = 0` and `24·n·σ₁(n)` for `n ≥ 1`. -/
private noncomputable def negDE₂Coeff (n : ℕ) : ℂ := (24 : ℂ) * (n : ℂ) * (σ 1 n : ℂ)

/-- Derivative bound on compact subsets of `ℍ` for the `E₂` q-series — used to feed
`D_qexp_tsum`. -/
private lemma E₂_qseries_deriv_bound :
    let a : ℕ → ℂ := fun n => if n = 0 then (1 : ℂ) else (-24 : ℂ) * (σ 1 n : ℂ)
    ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K),
        ‖a n * (2 * π * Complex.I * n) * cexp (2 * π * Complex.I * n * k.1)‖ ≤ u n := by
  intro a K hK hKc
  have him_pos : ∀ z ∈ K, (0 : ℝ) < z.im := fun z hz => hK hz
  obtain ⟨δ, hδ_pos, hδ_le⟩ :=
    IsCompact.exists_forall_le' (s := K) hKc Complex.continuous_im.continuousOn
      (a := (0 : ℝ)) him_pos
  let r : ℝ := Real.exp (-2 * Real.pi * δ)
  have hr_norm : ‖r‖ < 1 := by
    have hr_nonneg : 0 ≤ r := by positivity
    have hr_lt_one : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, hδ_pos])
    simpa [Real.norm_of_nonneg hr_nonneg] using hr_lt_one
  refine ⟨fun n => (48 * Real.pi) * (((n : ℝ) ^ 3 : ℝ) * r ^ n),
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hr_norm).mul_left (48 * Real.pi), ?_⟩
  intro n k
  by_cases hn0 : n = 0
  · subst hn0; simp [a]
  have hnorm_exp : ‖cexp (2 * π * Complex.I * (n : ℂ) * k.1)‖ ≤ r ^ n :=
    SpherePacking.ForMathlib.norm_cexp_two_pi_I_mul_nat_mul_le_pow_of_le_im n (hδ_le k.1 k.2)
  have hσ : (σ 1 n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast (sigma_bound 1 n)
  have ha_norm : ‖a n‖ ≤ (24 : ℝ) * (n : ℝ) ^ 2 := by
    have : a n = (-24 : ℂ) * (σ 1 n : ℂ) := by simp [a, hn0]
    simp_all
  have hnorm_2pin : ‖(2 * π * Complex.I * (n : ℂ) : ℂ)‖ = 2 * Real.pi * (n : ℝ) := by
    simp [Real.norm_of_nonneg Real.pi_pos.le, mul_left_comm, mul_comm]
  calc
    ‖a n * (2 * π * Complex.I * n) * cexp (2 * π * Complex.I * n * k.1)‖
        = ‖a n‖ * ‖(2 * π * Complex.I * (n : ℂ) : ℂ)‖ *
            ‖cexp (2 * π * Complex.I * (n : ℂ) * k.1)‖ := by simp [mul_assoc]
    _ ≤ ((24 : ℝ) * (n : ℝ) ^ 2) * (2 * Real.pi * (n : ℝ)) * (r ^ n) := by
          gcongr
          · simpa [hnorm_2pin] using (le_of_eq hnorm_2pin)
    _ ≤ (48 * Real.pi) * (((n : ℝ) ^ 3 : ℝ) * r ^ n) := by grind only

/-- The q-series formula for `-D(E₂)`: `negDE₂ τ = ∑ 24·n·σ₁(n)·exp(2πinτ)`. -/
private lemma negDE₂_eq_qseries (τ : UpperHalfPlane) :
    negDE₂ τ = ∑' n : ℕ, negDE₂Coeff n * cexp (2 * π * Complex.I * n * τ) := by
  let a : ℕ → ℂ := fun n => if n = 0 then (1 : ℂ) else (-24 : ℂ) * (σ 1 n : ℂ)
  have hE2fun : (E₂ : UpperHalfPlane → ℂ) =
      fun z : UpperHalfPlane => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
    funext z; simpa [a, mul_assoc] using (E₂_eq_qexp z)
  have hD : D E₂ τ = ∑' n : ℕ, (n : ℂ) * a n * cexp (2 * π * Complex.I * n * τ) := by
    have hD' := D_qexp_tsum a τ (E₂_qseries_deriv_bound)
    simpa [hE2fun] using hD'
  have hterm (n : ℕ) :
      -((n : ℂ) * a n * cexp (2 * π * Complex.I * n * τ)) =
        negDE₂Coeff n * cexp (2 * π * Complex.I * n * τ) := by
    by_cases hn : n = 0
    · subst hn; simp [a, negDE₂Coeff]
    · have ha : a n = (-24 : ℂ) * (σ 1 n : ℂ) := by simp [a, hn]
      rw [ha, negDE₂Coeff]; ring
  calc
    negDE₂ τ = -(D E₂ τ) := by simp [negDE₂, Pi.neg_apply]
    _ = ∑' n : ℕ, -((n : ℂ) * a n * cexp (2 * π * Complex.I * n * τ)) := by
          rw [hD]
          simpa using
            (tsum_neg (f := fun n : ℕ => (n : ℂ) * a n * cexp (2 * π * Complex.I * n * τ))).symm
    _ = ∑' n : ℕ, negDE₂Coeff n * cexp (2 * π * Complex.I * n * τ) := tsum_congr hterm

/-- The q-series for `-D(E₂) τ` is absolutely summable. -/
private lemma negDE₂_qseries_summable (τ : UpperHalfPlane) :
    Summable (fun n : ℕ => negDE₂Coeff n * cexp (2 * π * Complex.I * n * τ)) := by
  set r : ℝ := ‖cexp (2 * π * Complex.I * τ)‖ with hr
  have hr_nonneg : 0 ≤ r := norm_nonneg _
  have hr_lt_one : r < 1 := by simpa [r, hr] using (exp_upperHalfPlane_lt_one τ)
  have hr_norm : ‖(r : ℝ)‖ < 1 := by
    simpa [Real.norm_of_nonneg hr_nonneg] using hr_lt_one
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 3 : ℝ) * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hr_norm
  have hσ (n : ℕ) : (σ 1 n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast (sigma_bound 1 n)
  have hbound : ∀ n : ℕ, ‖negDE₂Coeff n * cexp (2 * π * Complex.I * n * τ)‖ ≤
      (24 : ℝ) * ((n : ℝ) ^ 3 * r ^ n) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp [r, negDE₂Coeff]
    · have hqpow : ‖cexp (2 * π * Complex.I * n * τ)‖ = r ^ n := by
        have hexp : cexp (2 * π * Complex.I * n * τ) = cexp (2 * π * Complex.I * τ) ^ n := by
          simpa using (exp_aux τ n)
        simp [r, hr, hexp, norm_pow]
      have hσ' := hσ n
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have hrn : 0 ≤ r ^ n := pow_nonneg hr_nonneg _
      calc
        ‖negDE₂Coeff n * cexp (2 * π * Complex.I * n * τ)‖
            = (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * ‖cexp (2 * π * Complex.I * n * τ)‖ := by
              simp [negDE₂Coeff, mul_assoc, mul_comm]
        _ = (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * (r ^ n) := by simp [hqpow]
        _ ≤ (24 : ℝ) * ((n : ℝ) ^ 3 * r ^ n) := by
              have hσmul : (n : ℝ) * (σ 1 n : ℝ) ≤ (n : ℝ) * (n : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_left hσ' hn0
              have hσmul' := mul_le_mul_of_nonneg_right hσmul hrn
              grind only
  exact Summable.of_norm_bounded (g := fun n : ℕ => (24 : ℝ) * ((n : ℝ) ^ 3 * r ^ n))
    (hs.mul_left 24) (fun n => hbound n)

/-- On the imaginary axis `τ = i·t`, the imaginary part of every term in the q-series vanishes. -/
private lemma negDE₂_term_im_zero_on_imag_axis (t : ℝ) (n : ℕ) (τ : UpperHalfPlane)
    (hτ : (τ : ℂ) = Complex.I * t) :
    (negDE₂Coeff n * cexp (2 * π * Complex.I * n * τ)).im = 0 := by
  have hq : cexp (2 * π * Complex.I * n * τ) = (rexp (-(2 * π * n * t)) : ℂ) := by
    rw [hτ]; exact cexp_two_pi_I_nat_mul_I_mul t n
  rw [hq]
  set x : ℂ := negDE₂Coeff n
  set y : ℂ := (rexp (-(2 * π * n * t)) : ℂ)
  have hx : x.im = 0 := by simp [x, negDE₂Coeff]
  have hy : y.im = 0 := by simpa [y] using (Complex.ofReal_im (rexp (-(2 * π * n * t))))
  have : (x * y).im = 0 := by simp [Complex.mul_im, hx, hy]
  simpa [x, y] using this

/-- On the imaginary axis `τ = i·t`, the real part of each q-series term equals
`24·n·σ₁(n)·exp(-2πnt) ≥ 0`. -/
private lemma negDE₂_term_re_on_imag_axis (t : ℝ) (n : ℕ) (τ : UpperHalfPlane)
    (hτ : (τ : ℂ) = Complex.I * t) :
    (negDE₂Coeff n * cexp (2 * π * Complex.I * n * τ)).re =
      (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * Real.exp (-2 * Real.pi * (n : ℝ) * t) := by
  have hq : cexp (2 * π * Complex.I * n * τ) = (rexp (-(2 * π * n * t)) : ℂ) := by
    rw [hτ]; exact cexp_two_pi_I_nat_mul_I_mul t n
  have harg : (-(2 * π * (n : ℝ) * t)) = (-2 * Real.pi * (n : ℝ) * t) := by ring
  rw [hq]
  set x : ℂ := negDE₂Coeff n
  set y : ℂ := (rexp (-(2 * π * n * t)) : ℂ)
  have hx_im : x.im = 0 := by simp [x, negDE₂Coeff]
  have hy_im : y.im = 0 := by simpa [y] using (Complex.ofReal_im (rexp (-(2 * π * n * t))))
  have hx_re : x.re = (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) := by
    simp [x, negDE₂Coeff, Complex.mul_re, mul_assoc, mul_comm]
  have hy_re : y.re = rexp (-(2 * π * n * t)) := by
    simpa [y] using (Complex.ofReal_re (rexp (-(2 * π * n * t))))
  have hxy : (x * y).re = (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * rexp (-(2 * π * n * t)) := by
    simp [Complex.mul_re, hx_im, hy_im, hx_re, hy_re, mul_assoc, mul_comm, mul_left_comm]
  change (x * y).re = _
  rw [hxy, ← harg]

/-- Summability of the real-valued majorant `∑ 24·n·σ₁(n)·exp(-2πnt)` on the imaginary axis. -/
private lemma negDE₂_re_series_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ =>
      (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * Real.exp (-2 * Real.pi * (n : ℝ) * t)) := by
  let r : ℝ := Real.exp (-2 * Real.pi * t)
  have hr_nonneg : 0 ≤ r := (Real.exp_pos _).le
  have hr_lt_one : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, ht])
  have hr_norm : ‖(r : ℝ)‖ < 1 := by
    simpa [Real.norm_of_nonneg hr_nonneg] using hr_lt_one
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 3 : ℝ) * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hr_norm
  have hσ (n : ℕ) : (σ 1 n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast (sigma_bound 1 n)
  have hbound : ∀ n : ℕ,
      ‖(24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * Real.exp (-2 * Real.pi * (n : ℝ) * t)‖ ≤
        (24 : ℝ) * ((n : ℝ) ^ 3 * r ^ n) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp [r]
    · have hexp : Real.exp (-2 * Real.pi * (n : ℝ) * t) = r ^ n := by
        rw [show (-2 * Real.pi * (n : ℝ) * t) = (n : ℕ) * (-2 * Real.pi * t) from by ring,
          Real.exp_nat_mul]
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have hrn : 0 ≤ r ^ n := pow_nonneg hr_nonneg _
      have hσ' := hσ n
      have hx_nonneg : 0 ≤ (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) *
          Real.exp (-2 * Real.pi * (n : ℝ) * t) := by
        have hσ0 : 0 ≤ (σ 1 n : ℝ) := by exact_mod_cast (Nat.zero_le _)
        positivity
      rw [Real.norm_of_nonneg hx_nonneg, hexp]
      have : (n : ℝ) * (σ 1 n : ℝ) ≤ (n : ℝ) ^ 3 := by
        nlinarith [mul_le_mul_of_nonneg_left hσ' hn0]
      nlinarith [mul_le_mul_of_nonneg_right this hrn, hrn]
  exact Summable.of_norm_bounded (g := fun n : ℕ => (24 : ℝ) * ((n : ℝ) ^ 3 * r ^ n))
    (hs.mul_left 24) (fun n => hbound n)

private lemma negDE₂_pos : ResToImagAxis.Pos negDE₂ := by
  refine ⟨?_, ?_⟩
  · -- Reality on the imaginary axis: every term's imaginary part is zero.
    intro t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
    set τ : UpperHalfPlane := ⟨Complex.I * t, by simp [ht]⟩
    have hτ : (τ : ℂ) = Complex.I * t := rfl
    rw [negDE₂_eq_qseries τ, im_tsum (negDE₂_qseries_summable τ)]
    simpa using (tsum_congr (negDE₂_term_im_zero_on_imag_axis t · τ hτ)).trans tsum_zero
  · -- Positivity of the real part: bound by a positive real q-series.
    intro t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
    set τ : UpperHalfPlane := ⟨Complex.I * t, by simp [ht]⟩
    have hτ : (τ : ℂ) = Complex.I * t := rfl
    have hpos : 0 < ∑' n : ℕ,
        (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * Real.exp (-2 * Real.pi * (n : ℝ) * t) :=
      Summable.tsum_pos (negDE₂_re_series_summable t ht)
        (fun i ↦ by positivity) 1 (by positivity)
    have hre_tsum : (negDE₂ τ).re =
        ∑' n : ℕ, (24 : ℝ) * (n : ℝ) * (σ 1 n : ℝ) * Real.exp (-2 * Real.pi * (n : ℝ) * t) := by
      have hre' : (negDE₂ τ).re =
          ∑' n : ℕ, (negDE₂Coeff n * cexp (2 * π * Complex.I * n * τ)).re := by
        simpa [negDE₂_eq_qseries τ] using
          (Complex.reCLM.map_tsum (negDE₂_qseries_summable τ))
      simp [hre', negDE₂_term_re_on_imag_axis t _ τ hτ]
    simpa [hre_tsum] using hpos

private lemma Δ_fun_pos : ResToImagAxis.Pos Δ_fun := by
  have hΔfun : Δ_fun = fun z : ℍ => (Delta z : ℂ) := funext fun z => by
    simpa [Δ_fun, one_div] using (Delta_apply_eq_one_div_1728_mul_E4_pow_three_sub_E6_sq z).symm
  simpa [hΔfun, Delta_apply] using (Delta_imag_axis_pos : ResToImagAxis.Pos Δ)

private lemma L₁₀_SerreDer : L₁₀ = (serre_D 10 F) * G - F * (serre_D 10 G) := by
  ext z; simp [L₁₀, serre_D_apply]; ring_nf

private lemma SerreDer_22_L₁₀_SerreDer :
    SerreDer_22_L₁₀ = (serre_D 12 (serre_D 10 F)) * G - F * (serre_D 12 (serre_D 10 G)) := by
  have SF_holo := @serre_D_differentiable F 10 F_holo
  have SG_holo := @serre_D_differentiable G 10 G_holo
  calc
    SerreDer_22_L₁₀ = serre_D 22 (serre_D 10 F * G - F * serre_D 10 G) := by
      simpa [SerreDer_22_L₁₀] using congrArg (serre_D 22) L₁₀_SerreDer
    _ = serre_D 22 (serre_D 10 F * G) - serre_D 22 (F * serre_D 10 G) := by
        simpa using
          (serre_D_sub 22 (serre_D 10 F * G) (F * serre_D 10 G)
            (MDifferentiable.mul SF_holo G_holo) (MDifferentiable.mul F_holo SG_holo))
    _ = serre_D (12 + 10) ((serre_D 10 F) * G) - serre_D (10 + 12) (F * serre_D 10 G) := by ring_nf
    _ = serre_D 12 (serre_D 10 F) * G + (serre_D 10 F) * (serre_D 10 G)
        - serre_D (10 + 12) (F * serre_D 10 G) := by
          simpa using (serre_D_mul 12 10 (serre_D 10 F) G SF_holo G_holo)
    _ = serre_D 12 (serre_D 10 F) * G + (serre_D 10 F) * (serre_D 10 G)
        - ((serre_D 10 F) * (serre_D 10 G) + F * (serre_D 12 (serre_D 10 G))) := by
          simpa using (serre_D_mul 10 12 F (serre_D 10 G) F_holo SG_holo)
    _ = (serre_D 12 (serre_D 10 F)) * G - F * (serre_D 12 (serre_D 10 G)) := by ring_nf

private lemma SerreDer_22_L₁₀_form :
    SerreDer_22_L₁₀ =
      (7200 : ℝ) • (Δ_fun * negDE₂ * G) + (640 : ℝ) • (Δ_fun * H₂ * F) := by
  ext z
  simp [SerreDer_22_L₁₀_SerreDer, MLDE_F, MLDE_G, mul_assoc, mul_comm]
  ring_nf

/-- The Serre derivative `serre_D 22 L₁₀` is positive on the imaginary axis. -/
public lemma SerreDer_22_L₁₀_pos : ResToImagAxis.Pos SerreDer_22_L₁₀ := by
  have hterm1 : ResToImagAxis.Pos (Δ_fun * negDE₂ * G) :=
    .mul (.mul Δ_fun_pos negDE₂_pos) G_pos
  have hterm2 : ResToImagAxis.Pos (Δ_fun * H₂ * F) :=
    .mul (.mul Δ_fun_pos H₂_imag_axis_pos) F_pos
  simpa [SerreDer_22_L₁₀_form] using
    (ResToImagAxis.Pos.smul (c := (7200 : ℝ)) hterm1 (by positivity)).add
      (ResToImagAxis.Pos.smul (c := (640 : ℝ)) hterm2 (by positivity))
