module
public import SpherePacking.ModularForms.FG.Basic
public import SpherePacking.ModularForms.ResToImagAxis
import SpherePacking.ModularForms.FG.Positivity
import SpherePacking.ModularForms.FG.AsymptoticsTools

/-!
# Eventual positivity of `L₁₀` on the imaginary axis

This file proves `L₁₀_eventuallyPos`, a performance-sensitive lemma used later in the `FG/`
development. The proof is split into several private steps to help compilation.

## Main declaration
* `L₁₀_eventuallyPos`
-/

open scoped Real Manifold Topology ArithmeticFunction.sigma ModularForm MatrixGroups Derivative
open Filter Complex UpperHalfPlane
open ModularForm hiding E₄ E₆

-- Ensure the `SL(2,ℤ)` Möbius action on `ℍ` is available below.
noncomputable local instance : MulAction SL(2, ℤ) ℍ := UpperHalfPlane.SLAction (R := ℤ)

section

-- Prevent `whnf` from unfolding `H₂` in the long asymptotics proof.
attribute [local irreducible] H₂

private noncomputable def q₁ : UpperHalfPlane → ℂ :=
  fun z => cexp ((2 * π * Complex.I) * (z : ℂ))

private noncomputable def q₂ : UpperHalfPlane → ℂ :=
  fun z => cexp ((4 * π * Complex.I) * (z : ℂ))

private noncomputable def q₃ : UpperHalfPlane → ℂ :=
  fun z => cexp ((3 * π * Complex.I) * (z : ℂ))

/-- The `q`-half factor for `H₂`: `qπ z = exp(πi·z)`. -/
private noncomputable def qπ : UpperHalfPlane → ℂ :=
  fun z => cexp (π * Complex.I * (z : ℂ))

/-- `B = A_E / q₁` so that `A_E = q₁ · B`. -/
private noncomputable def Bfun : UpperHalfPlane → ℂ := fun z => A_E z / q₁ z

/-- `F₀ = B²` so that `F = q₂ · F₀`. -/
private noncomputable def F₀fun : UpperHalfPlane → ℂ := fun z => (Bfun z) ^ 2

/-- `H₂' = H₂ / qπ` so that `H₂ = qπ · H₂'`. -/
private noncomputable def H₂'fun : UpperHalfPlane → ℂ := fun z => H₂ z / qπ z

/-- The polynomial factor in the definition of `G`. -/
private noncomputable def polyfun : UpperHalfPlane → ℂ :=
  2 * H₂ ^ 2 + 5 * H₂ * H₄ + 5 * H₄ ^ 2

/-- `G₀ = (H₂')³ · poly` so that `G = q₃ · G₀`. -/
private noncomputable def G₀fun : UpperHalfPlane → ℂ := fun z => (H₂'fun z) ^ 3 * polyfun z

private noncomputable def L₁₀_over : UpperHalfPlane → ℂ :=
  fun z => L₁₀ z / (q₂ z * q₃ z)

private lemma coeff_4piI_div_2piI : ((4 * π * Complex.I) / (2 * π * Complex.I) : ℂ) = (2 : ℂ) :=
  (div_eq_iff Complex.two_pi_I_ne_zero).2 (by ring)

private lemma coeff_3piI_div_2piI :
    ((3 * π * Complex.I) / (2 * π * Complex.I) : ℂ) = (3 / 2 : ℂ) :=
  (div_eq_iff Complex.two_pi_I_ne_zero).2 (by ring)

private lemma L₁₀_real_resToImagAxis : ResToImagAxis.Real L₁₀ := by
  have hFreal : ResToImagAxis.Real F := F_pos.1
  have hGreal : ResToImagAxis.Real G := G_pos.1
  have hDFreal : ResToImagAxis.Real (D F) := ResToImagAxis.Real.D_of_real hFreal F_holo
  have hDGreal : ResToImagAxis.Real (D G) := ResToImagAxis.Real.D_of_real hGreal G_holo
  simpa [L₁₀] using
    ResToImagAxis.Real.sub (ResToImagAxis.Real.mul hDFreal hGreal)
      (ResToImagAxis.Real.mul hFreal hDGreal)

private lemma hq₁_ne (z : UpperHalfPlane) : q₁ z ≠ 0 := by simp [q₁]
private lemma hq₂_ne (z : UpperHalfPlane) : q₂ z ≠ 0 := by simp [q₂]
private lemma hq₃_ne (z : UpperHalfPlane) : q₃ z ≠ 0 := by simp [q₃]
private lemma hqπ_ne (z : UpperHalfPlane) : qπ z ≠ 0 := by simp [qπ]

private lemma hq₁_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q₁ := by
  simpa [q₁] using mdifferentiable_cexp_mul (2 * π * Complex.I)
private lemma hq₂_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q₂ := by
  simpa [q₂] using mdifferentiable_cexp_mul (4 * π * Complex.I)
private lemma hq₃_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q₃ := by
  simpa [q₃] using mdifferentiable_cexp_mul (3 * π * Complex.I)
private lemma hqπ_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) qπ := by
  have h : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : UpperHalfPlane => cexp ((π * Complex.I) * (z : ℂ))) :=
    mdifferentiable_cexp_mul (π * Complex.I)
  exact h

private lemma A_E_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) A_E :=
  (MDifferentiable.mul E₂_holo' E₄.holo').sub E₆.holo'

private lemma Bfun_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Bfun := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hA' := (UpperHalfPlane.mdifferentiable_iff).1 A_E_holo
  have hq₁' := (UpperHalfPlane.mdifferentiable_iff).1 hq₁_holo
  simpa [Bfun, Function.comp] using
    hA'.div hq₁' (by intro w _; simpa using hq₁_ne (UpperHalfPlane.ofComplex w))

private lemma F₀fun_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F₀fun := by
  have h := Bfun_holo.mul Bfun_holo
  convert h using 1
  funext z; simp [F₀fun, pow_two]

private lemma H₂'fun_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂'fun := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hH2_on := (UpperHalfPlane.mdifferentiable_iff).1 H₂_SIF_MDifferentiable
  have hq_on := (UpperHalfPlane.mdifferentiable_iff).1 hqπ_holo
  simpa [H₂'fun, Function.comp] using
    hH2_on.div hq_on fun w _ => by simpa using hqπ_ne (UpperHalfPlane.ofComplex w)

private lemma polyfun_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) polyfun := by
  have hH2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂ := H₂_SIF_MDifferentiable
  have hH4 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄ := H₄_SIF_MDifferentiable
  have hH2sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 2) := by simpa [pow_two] using hH2.mul hH2
  have hH4sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₄ ^ 2) := by simpa [pow_two] using hH4.mul hH4
  have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (2 * H₂ ^ 2) := by
    simpa using mdifferentiable_const.mul hH2sq
  have h2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (5 * H₂ * H₄) := by
    simpa [mul_assoc] using (mdifferentiable_const.mul hH2).mul hH4
  have h3 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (5 * H₄ ^ 2) := by
    simpa using mdifferentiable_const.mul hH4sq
  simpa [polyfun, add_assoc] using h1.add (h2.add h3)

private lemma G₀fun_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₀fun := by
  have hH2cube : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : UpperHalfPlane => (H₂'fun z) ^ 3) := by
    have hH2sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : UpperHalfPlane => (H₂'fun z) ^ 2) := by
      simpa [pow_two] using H₂'fun_holo.mul H₂'fun_holo
    simpa [pow_succ, pow_two, mul_assoc] using H₂'fun_holo.mul hH2sq
  simpa [G₀fun] using (hH2cube.mul polyfun_holo)

/-- `B = A_E / q₁` expressed as a q-series. -/
private lemma Bfun_eq_qseries (z : UpperHalfPlane) :
    Bfun z = (720 : ℂ) * ∑' n : ℕ,
      ((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
  have hA : A_E z =
      (720 : ℂ) * ∑' (n : ℕ+),
        (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) := by
    simpa [A_E, mul_assoc, mul_left_comm, mul_comm] using (E₂_mul_E₄_sub_E₆ z)
  have hshift :
      (∑' (n : ℕ+), (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))) =
        ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) *
          cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm, add_assoc] using
      (tsum_pnat_eq_tsum_succ3 (f := fun n : ℕ =>
        (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))))
  have hexp_cancel (n : ℕ) :
      cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)) / q₁ z =
        cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
    rw [show q₁ z = cexp (2 * π * Complex.I * (z : ℂ)) by simp [q₁, mul_assoc], ← exp_sub]
    congr 1; push_cast; ring
  have hA' : A_E z = (720 : ℂ) * ∑' n : ℕ,
        ((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) *
          cexp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)) := by
    simpa [hshift] using hA
  change A_E z / q₁ z = _
  rw [hA', mul_div_assoc, ← tsum_div_const]
  refine congrArg ((720 : ℂ) * ·) (tsum_congr fun n => ?_)
  rw [mul_div_assoc, hexp_cancel]

/-- Summability of `‖(n+1)·σ₃(n+1)‖ · exp(-2πn)` — coefficients of the `B` q-series. -/
private lemma Bfun_qseries_coeff_summable :
    Summable (fun n : ℕ =>
      ‖(((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))‖ * Real.exp (-2 * π * n)) := by
  set r : ℝ := Real.exp (-2 * π) with hr
  have hr_nonneg : 0 ≤ r := (Real.exp_pos _).le
  have hr_lt_one : r < 1 := by
    have : (-2 * π : ℝ) < 0 := by nlinarith [Real.pi_pos]
    simpa [hr] using (Real.exp_lt_one_iff.2 this)
  have hr_norm : ‖r‖ < 1 := by
    simpa [Real.norm_of_nonneg hr_nonneg] using hr_lt_one
  have hsumm_pow : Summable (fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5 hr_norm
  have hbound : ∀ n : ℕ,
      ‖(((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))‖ * Real.exp (-2 * π * n) ≤
        (if n = 0 then 1 else 32 * ((n : ℝ) ^ 5 * r ^ n)) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp
    · have hn1 : 1 ≤ n := Nat.succ_le_iff.1 (Nat.pos_of_ne_zero hn)
      have hσ : (σ 3 (n + 1) : ℝ) ≤ (n + 1 : ℝ) ^ 4 := by
        exact_mod_cast (sigma_bound 3 (n + 1))
      have hcoeff : (n + 1 : ℝ) * (σ 3 (n + 1) : ℝ) ≤ (n + 1 : ℝ) ^ 5 := by nlinarith
      have hn_add : (n + 1 : ℝ) ≤ 2 * (n : ℝ) := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        linarith
      have hpow_le : (n + 1 : ℝ) ^ 5 ≤ 32 * (n : ℝ) ^ 5 := by
        calc (n + 1 : ℝ) ^ 5 ≤ ((2 : ℝ) * (n : ℝ)) ^ 5 :=
              pow_le_pow_left₀ (by positivity) hn_add 5
          _ = 32 * (n : ℝ) ^ 5 := by ring_nf
      have hterm : ‖(((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))‖ ≤ 32 * (n : ℝ) ^ 5 := by
        have heq : ‖(((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))‖ =
            (n + 1 : ℝ) * (σ 3 (n + 1) : ℝ) := by
          rw [Complex.norm_mul, Complex.norm_natCast, Complex.norm_natCast]; push_cast; ring
        rw [heq]; exact le_trans hcoeff hpow_le
      have hexp : Real.exp (-2 * π * n) = r ^ n := by
        rw [hr, show (-2 * π * n : ℝ) = (n : ℝ) * (-2 * π) by ring, Real.exp_nat_mul]
      have :
          ‖(((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))‖ * Real.exp (-2 * π * n) ≤
            (32 * (n : ℝ) ^ 5) * (r ^ n) := by
        have hnexp' : 0 ≤ Real.exp (-2 * π * n) := (Real.exp_pos _).le
        have hmul := (mul_le_mul_of_nonneg_right hterm hnexp' : _)
        grind only
      simpa [hn, mul_assoc, mul_left_comm, mul_comm] using this
  have hsumm_major :
      Summable (fun n : ℕ => (if n = 0 then (1 : ℝ) else 32 * ((n : ℝ) ^ 5 * r ^ n))) := by
    have hsumm1 : Summable (fun n : ℕ => (32 : ℝ) * ((n : ℝ) ^ 5 * r ^ n)) :=
      hsumm_pow.mul_left 32
    have hsumm0 : Summable (fun n : ℕ => (if n = 0 then (1 : ℝ) else 0)) := by
      refine summable_of_hasFiniteSupport ((Set.finite_singleton (0 : ℕ)).subset ?_)
      norm_num
    have hdecomp :
        (fun n : ℕ => (if n = 0 then (1 : ℝ) else 32 * ((n : ℝ) ^ 5 * r ^ n))) =
          (fun n : ℕ => (if n = 0 then (1 : ℝ) else 0) + (32 : ℝ) * ((n : ℝ) ^ 5 * r ^ n)) := by
      funext n; by_cases hn : n = 0 <;> simp [hn]
    simpa [hdecomp] using (hsumm0.add hsumm1)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsumm_major
  · exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  · exact hbound n

/-- `B → 720` at `i∞` (a `q`-series with constant term `720`). -/
private lemma Bfun_tendsto_atImInfty :
    Tendsto Bfun UpperHalfPlane.atImInfty (nhds (720 : ℂ)) := by
  let a : ℕ → ℂ := fun n => (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))
  have ha : Summable (fun n : ℕ => ‖a n‖ * Real.exp (-2 * π * n)) := by
    simpa [a] using Bfun_qseries_coeff_summable
  have hseries :
      Tendsto (fun z : UpperHalfPlane => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n))
        UpperHalfPlane.atImInfty (nhds (a 0)) :=
    QExp.tendsto_nat (a := a) (ha := ha)
  have hseries' :
      Tendsto (fun z : UpperHalfPlane =>
          (720 : ℂ) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n))
        UpperHalfPlane.atImInfty (nhds ((720 : ℂ) * (a 0))) :=
    tendsto_const_nhds.mul hseries
  have hEq :
      (fun z : UpperHalfPlane =>
          (720 : ℂ) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n)) = Bfun := by
    funext z
    simpa [a, mul_assoc, mul_left_comm, mul_comm] using (Bfun_eq_qseries z).symm
  have ha0 : a 0 = (1 : ℂ) := by simp [a]
  simpa [hEq, ha0] using hseries'

/-- `F₀ = B² → 518400` at `i∞`. -/
private lemma F₀fun_tendsto_atImInfty :
    Tendsto F₀fun UpperHalfPlane.atImInfty (nhds (518400 : ℂ)) := by
  have h := Bfun_tendsto_atImInfty.pow 2
  have hconst : (720 : ℂ) ^ 2 = (518400 : ℂ) := by norm_num
  simpa [F₀fun, hconst] using h

/-- A function tending to a constant `c` at `i∞` is bounded at `i∞`. -/
private lemma isBoundedAtImInfty_of_tendsto {f : UpperHalfPlane → ℂ} {c : ℂ}
    (h : Tendsto f UpperHalfPlane.atImInfty (nhds c)) : IsBoundedAtImInfty f := by
  have hzero : Tendsto (fun z : UpperHalfPlane => f z - c) UpperHalfPlane.atImInfty (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr h
  have hbdd_diff : IsBoundedAtImInfty (fun z : UpperHalfPlane => f z - c) :=
    UpperHalfPlane.IsZeroAtImInfty.isBoundedAtImInfty hzero
  have hbdd_const : IsBoundedAtImInfty (fun _ : UpperHalfPlane => c) :=
    Filter.const_boundedAtFilter _ _
  have hbdd_sum :
      IsBoundedAtImInfty (fun z : UpperHalfPlane => (f z - c) + c) := by
    dsimp [UpperHalfPlane.IsBoundedAtImInfty] at hbdd_diff hbdd_const ⊢
    exact BoundedAtFilter.add hbdd_diff hbdd_const
  have hEq : (fun z : UpperHalfPlane => (f z - c) + c) = f := by funext z; ring
  simpa [hEq] using hbdd_sum

/-- The derivative `D F₀ → 0` at `i∞`. -/
private lemma DF₀fun_tendsto_zero :
    Tendsto (D F₀fun) UpperHalfPlane.atImInfty (nhds (0 : ℂ)) := by
  have := D_isZeroAtImInfty_of_bounded F₀fun_holo
    (isBoundedAtImInfty_of_tendsto F₀fun_tendsto_atImInfty)
  simpa [UpperHalfPlane.IsZeroAtImInfty] using this

/-- `H₂' = H₂ / qπ → 16` at `i∞`, using the Jacobi theta expansion of `H₂`. -/
private lemma H₂'fun_tendsto_atImInfty :
    Tendsto H₂'fun UpperHalfPlane.atImInfty (nhds (16 : ℂ)) := by
  let g : UpperHalfPlane → ℂ := fun z => jacobiTheta₂ (z / 2) z
  have hg : Tendsto g UpperHalfPlane.atImInfty (nhds (2 : ℂ)) :=
    jacobiTheta₂_half_mul_apply_tendsto_atImInfty
  have hrewrite : H₂'fun = fun z => (g z) ^ 4 := by
    funext z
    have hΘ₂ : Θ₂ z = cexp (π * Complex.I * (z : ℂ) / 4) * g z := by
      simpa [g] using (Θ₂_as_jacobiTheta₂ z)
    have hE : cexp (π * Complex.I * (z : ℂ) / 4) ^ 4 = cexp (π * Complex.I * (z : ℂ)) := by
      rw [← Complex.exp_nat_mul]; congr 1; ring
    have hH2 : H₂ z = cexp (π * Complex.I * (z : ℂ)) * (g z) ^ 4 := by
      simp [H₂, hΘ₂, mul_pow, hE]
    exact Eq.symm (Mathlib.Tactic.CancelDenoms.cancel_factors_eq_div hH2.symm (hqπ_ne z))
  have h2pow : (2 : ℂ) ^ 4 = (16 : ℂ) := by norm_num
  simpa [hrewrite, h2pow] using hg.pow 4

/-- The polynomial factor `poly = 2 H₂² + 5 H₂ H₄ + 5 H₄² → 5` at `i∞`. -/
private lemma polyfun_tendsto_atImInfty :
    Tendsto polyfun UpperHalfPlane.atImInfty (nhds (5 : ℂ)) := by
  have hH2 : Tendsto H₂ UpperHalfPlane.atImInfty (nhds 0) := H₂_tendsto_atImInfty
  have hH4 : Tendsto H₄ UpperHalfPlane.atImInfty (nhds 1) := H₄_tendsto_atImInfty
  have h1 : Tendsto (fun z : UpperHalfPlane => (2 : ℂ) * H₂ z ^ 2)
      UpperHalfPlane.atImInfty (nhds 0) := by
    simpa using tendsto_const_nhds.mul (hH2.pow 2)
  have h2 : Tendsto (fun z : UpperHalfPlane => 5 * H₂ z * H₄ z)
      UpperHalfPlane.atImInfty (nhds 0) := by
    simpa [mul_assoc] using (tendsto_const_nhds.mul hH2).mul hH4
  have h3 : Tendsto (fun z : UpperHalfPlane => 5 * H₄ z ^ 2)
      UpperHalfPlane.atImInfty (nhds (5 : ℂ)) := by
    simpa using tendsto_const_nhds.mul (hH4.pow 2)
  simpa [polyfun, add_assoc] using h1.add (h2.add h3)

/-- `G₀ = (H₂')³ · poly → 20480` at `i∞`. -/
private lemma G₀fun_tendsto_atImInfty :
    Tendsto G₀fun UpperHalfPlane.atImInfty (nhds (20480 : ℂ)) := by
  have h := (H₂'fun_tendsto_atImInfty.pow 3).mul polyfun_tendsto_atImInfty
  simpa [G₀fun, show ((16 : ℂ) ^ 3) * (5 : ℂ) = (20480 : ℂ) by norm_num] using h

/-- The derivative `D G₀ → 0` at `i∞`. -/
private lemma DG₀fun_tendsto_zero :
    Tendsto (D G₀fun) UpperHalfPlane.atImInfty (nhds (0 : ℂ)) := by
  have := D_isZeroAtImInfty_of_bounded G₀fun_holo
    (isBoundedAtImInfty_of_tendsto G₀fun_tendsto_atImInfty)
  simpa [UpperHalfPlane.IsZeroAtImInfty] using this

/-- Factorization `F = q₂ · F₀`. -/
private lemma F_factor : F = fun z : UpperHalfPlane => q₂ z * F₀fun z := by
  funext z
  have hq2 : q₂ z = (q₁ z) ^ 2 := by
    dsimp [q₂, q₁]; rw [← Complex.exp_nat_mul]; congr 1; ring
  have hA : A_E z = q₁ z * Bfun z := (mul_div_cancel₀ (A_E z) (hq₁_ne z)).symm
  calc F z = (A_E z) ^ 2 := by simp [F, A_E]
    _ = (q₁ z * Bfun z) ^ 2 := by simp [hA]
    _ = q₂ z * F₀fun z := by simp [hq2, F₀fun, mul_pow]

/-- Factorization `G = q₃ · G₀`. -/
private lemma G_factor : G = fun z : UpperHalfPlane => q₃ z * G₀fun z := by
  funext z
  have hH2 : H₂ z = qπ z * H₂'fun z := (mul_div_cancel₀ (H₂ z) (hqπ_ne z)).symm
  have hq3 : q₃ z = (qπ z) ^ 3 := by
    dsimp [q₃, qπ]; rw [← Complex.exp_nat_mul]; congr 1; ring
  have hGz : G z = (H₂ z) ^ 3 * polyfun z := by
    have hG_fun : G = H₂ ^ 3 * polyfun := by dsimp [G, polyfun]
    exact (congrArg (fun f : UpperHalfPlane → ℂ => f z) hG_fun).trans rfl
  rw [hGz, show G₀fun z = (H₂'fun z) ^ 3 * polyfun z from rfl, hH2, hq3]
  ring

/-- The quotient `D F / q₂` decomposes as `2·F₀ + D F₀` via the product rule. -/
private lemma DF_div_q₂_eq :
    (fun z : UpperHalfPlane => (D F z) / q₂ z) =
      fun z => (2 : ℂ) * F₀fun z + D F₀fun z := by
  have hF_factor := F_factor
  funext z
  have hDq2 : D q₂ z = (2 : ℂ) * q₂ z := by
    simpa [q₂, coeff_4piI_div_2piI] using (D_cexp_mul (4 * π * Complex.I) z)
  have hDprod_z :
      D (fun w : UpperHalfPlane => q₂ w * F₀fun w) z =
        (D q₂ z) * F₀fun z + q₂ z * D F₀fun z := by
    have hDprod := D_mul q₂ F₀fun hq₂_holo F₀fun_holo
    simpa using congrArg (fun f => f z) hDprod
  have hq2ne : q₂ z ≠ 0 := hq₂_ne z
  rw [hF_factor]; grind only

/-- The quotient `D G / q₃` decomposes as `(3/2)·G₀ + D G₀` via the product rule. -/
private lemma DG_div_q₃_eq :
    (fun z : UpperHalfPlane => (D G z) / q₃ z) =
      fun z => (3 / 2 : ℂ) * G₀fun z + D G₀fun z := by
  have hG_factor := G_factor
  funext z
  have hDq3 : D q₃ z = (3 / 2 : ℂ) * q₃ z := by
    simpa [q₃, coeff_3piI_div_2piI] using (D_cexp_mul (3 * π * Complex.I) z)
  have hDprod_z :
      D (fun w : UpperHalfPlane => q₃ w * G₀fun w) z =
        (D q₃ z) * G₀fun z + q₃ z * D G₀fun z := by
    have hDprod := D_mul q₃ G₀fun hq₃_holo G₀fun_holo
    simpa using congrArg (fun f => f z) hDprod
  have hq3ne : q₃ z ≠ 0 := hq₃_ne z
  rw [hG_factor]; grind only

/-- `D F / q₂ → 1036800 = 2·518400` at `i∞`. -/
private lemma DF_div_q₂_tendsto_atImInfty :
    Tendsto (fun z : UpperHalfPlane => (D F z) / q₂ z) UpperHalfPlane.atImInfty
      (nhds (1036800 : ℂ)) := by
  have hsum : Tendsto (fun z : UpperHalfPlane => (2 : ℂ) * F₀fun z + D F₀fun z)
      UpperHalfPlane.atImInfty (nhds (((2 : ℂ) * (518400 : ℂ)) + 0)) :=
    (tendsto_const_nhds.mul F₀fun_tendsto_atImInfty).add DF₀fun_tendsto_zero
  simpa [DF_div_q₂_eq, show ((2 : ℂ) * (518400 : ℂ) + 0) = (1036800 : ℂ) by norm_num] using hsum

/-- `D G / q₃ → 30720 = (3/2)·20480` at `i∞`. -/
private lemma DG_div_q₃_tendsto_atImInfty :
    Tendsto (fun z : UpperHalfPlane => (D G z) / q₃ z) UpperHalfPlane.atImInfty
      (nhds (30720 : ℂ)) := by
  have hsum : Tendsto (fun z : UpperHalfPlane => (3 / 2 : ℂ) * G₀fun z + D G₀fun z)
      UpperHalfPlane.atImInfty (nhds (((3 / 2 : ℂ) * (20480 : ℂ)) + 0)) :=
    (tendsto_const_nhds.mul G₀fun_tendsto_atImInfty).add DG₀fun_tendsto_zero
  simpa [DG_div_q₃_eq, show ((3 / 2 : ℂ) * (20480 : ℂ) + 0) = (30720 : ℂ) by norm_num] using hsum

/-- Rewriting `L₁₀/(q₂·q₃)` using the factorizations of `F` and `G`. -/
private lemma L₁₀_over_eq :
    L₁₀_over =
      fun z : UpperHalfPlane => ((D F z) / q₂ z) * G₀fun z - F₀fun z * ((D G z) / q₃ z) := by
  funext z
  have hFz : F z = q₂ z * F₀fun z := congrArg (fun f => f z) F_factor
  have hGz : G z = q₃ z * G₀fun z := congrArg (fun f => f z) G_factor
  dsimp [L₁₀_over, L₁₀]
  rw [hFz, hGz]
  field_simp [hq₂_ne z, hq₃_ne z]

private lemma L₁₀_over_tendsto_atImInfty :
    Tendsto L₁₀_over UpperHalfPlane.atImInfty (nhds (5308416000 : ℂ)) := by
  -- Combine the limits of `D F / q₂` and `D G / q₃` with those of `F₀` and `G₀`.
  have hsub := (DF_div_q₂_tendsto_atImInfty.mul G₀fun_tendsto_atImInfty).sub
    (F₀fun_tendsto_atImInfty.mul DG_div_q₃_tendsto_atImInfty)
  simpa [L₁₀_over_eq,
    show ((1036800 : ℂ) * (20480 : ℂ)) - ((518400 : ℂ) * (30720 : ℂ)) = (5308416000 : ℂ) by
      norm_num] using hsub

private lemma L₁₀_over_eventuallyPos_re
    (hL10_over_lim : Tendsto L₁₀_over UpperHalfPlane.atImInfty (nhds (5308416000 : ℂ))) :
    ∀ᶠ t : ℝ in atTop, (0 : ℝ) < (L₁₀_over (UpperHalfPlane.ofComplex (Complex.I * t))).re := by
  -- Transfer the `atImInfty`-limit to a statement along `t → ∞` on the imaginary axis.
  have hL10_over_lim_t :
      Tendsto (fun t : ℝ =>
        L₁₀_over (UpperHalfPlane.ofComplex (Complex.I * t))) atTop (nhds (5308416000 : ℂ)) :=
    hL10_over_lim.comp tendsto_ofComplex_I_mul_atTop_atImInfty
  have hL10_over_re_lim :
      Tendsto (fun t : ℝ =>
      (L₁₀_over (UpperHalfPlane.ofComplex (Complex.I * t))).re) atTop (nhds (5308416000 : ℝ)) := by
    -- Take real parts (the limit is real).
    have := (Complex.continuous_re.tendsto (5308416000 : ℂ)).comp hL10_over_lim_t
    simpa using this
  -- Eventually the real part is close to the positive limit.
  exact hL10_over_re_lim.eventually (Ioi_mem_nhds (by norm_num))

private lemma ofComplex_I_mul_eq_mk (t : ℝ) (ht : 0 < t) :
    UpperHalfPlane.ofComplex (Complex.I * t) =
      (⟨Complex.I * t, by simpa using ht⟩ : UpperHalfPlane) := by
  simpa using UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using ht)

private lemma q₂q₃_mul_pos_re_and_im_zero (t : ℝ) (ht : 0 < t) :
    let z : UpperHalfPlane := ⟨Complex.I * t, by simpa using ht⟩
    (q₂ z * q₃ z ≠ 0) ∧ (q₂ z * q₃ z).im = 0 ∧ 0 < (q₂ z * q₃ z).re := by
  let z : UpperHalfPlane := ⟨Complex.I * t, by simpa using ht⟩
  have hq2_ofReal : q₂ z = cexp (-(t * (π * 4)) : ℝ) := by
    dsimp [q₂, z]
    refine congrArg cexp ?_
    have : Complex.I * (Complex.I * (↑t * (↑π * 4))) = -(↑t * (↑π * 4)) := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hq3_ofReal : q₃ z = cexp (-(t * (π * 3)) : ℝ) := by
    dsimp [q₃, z]
    refine congrArg cexp ?_
    have : Complex.I * (Complex.I * (↑t * (↑π * 3))) = -(↑t * (↑π * 3)) := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hq_ne : q₂ z * q₃ z ≠ 0 := by simp [q₂, q₃, z]
  have hq2_im : (q₂ z).im = 0 := by
    simpa [hq2_ofReal] using (Complex.exp_ofReal_im (-(t * (π * 4))))
  have hq3_im : (q₃ z).im = 0 := by
    simpa [hq3_ofReal] using (Complex.exp_ofReal_im (-(t * (π * 3))))
  have ha_im : (q₂ z * q₃ z).im = 0 := by
    simp [Complex.mul_im, hq2_im, hq3_im]
  have hqpos : 0 < (q₂ z * q₃ z).re := by
    have hq2_pos : 0 < (q₂ z).re := by
      have hq2_re : (q₂ z).re = Real.exp (-(t * (π * 4))) := by
        simpa [hq2_ofReal] using (Complex.exp_ofReal_re (-(t * (π * 4))))
      simpa [hq2_re] using (Real.exp_pos (-(t * (π * 4))))
    have hq3_pos : 0 < (q₃ z).re := by
      have hq3_re : (q₃ z).re = Real.exp (-(t * (π * 3))) := by
        simpa [hq3_ofReal] using (Complex.exp_ofReal_re (-(t * (π * 3))))
      simpa [hq3_re] using (Real.exp_pos (-(t * (π * 3))))
    simpa [Complex.mul_re, hq2_im, hq3_im] using (mul_pos hq2_pos hq3_pos)
  simpa [z] using (And.intro hq_ne (And.intro ha_im hqpos))

private lemma L₁₀_eval_and_over_im_zero (hL10_real : ResToImagAxis.Real L₁₀) (t : ℝ) (ht : 0 < t)
    (z : UpperHalfPlane) (hzdef : z = (⟨Complex.I * t, by simp [ht]⟩ : UpperHalfPlane))
    (a : ℂ) (ha : a = q₂ z * q₃ z) (ha_ne : a ≠ 0) (ha_im : a.im = 0) :
    L₁₀.resToImagAxis t = a * L₁₀_over z ∧ (L₁₀_over z).im = 0 := by
  have hL10_eval_z : L₁₀ z = a * L₁₀_over z := by
    have : a * (L₁₀ z / a) = L₁₀ z := mul_div_cancel₀ (L₁₀ z) ha_ne
    simpa [L₁₀_over, ha.symm, mul_div_assoc] using this.symm
  have hres : L₁₀.resToImagAxis t = L₁₀ z := by
    simp [Function.resToImagAxis, ResToImagAxis, ht, hzdef.symm]
  have hL10_eval : L₁₀.resToImagAxis t = a * L₁₀_over z := hres.trans hL10_eval_z
  have hover_real : (L₁₀_over z).im = 0 := by
    have hL10_im_res : (L₁₀.resToImagAxis t).im = 0 := by
      simpa [Function.resToImagAxis_apply] using hL10_real t ht
    have hres_im : (L₁₀.resToImagAxis t).im = (L₁₀ z).im := by
      simpa using congrArg Complex.im hres
    have hL10_im : (L₁₀ z).im = 0 := by
      simpa using hres_im.symm.trans hL10_im_res
    simp [L₁₀_over, ha.symm, Complex.div_im, hL10_im, ha_im]
  exact ⟨hL10_eval, hover_real⟩

private lemma L₁₀_resToImagAxis_re_pos_of_mul (t : ℝ) (z : UpperHalfPlane)
    (a : ℂ) (ha_im : a.im = 0) (hover_real : (L₁₀_over z).im = 0)
    (hL10_eval : L₁₀.resToImagAxis t = a * L₁₀_over z)
    (ha_pos : 0 < a.re) (hover_pos : 0 < (L₁₀_over z).re) :
    0 < (L₁₀.resToImagAxis t).re := by
  rw [hL10_eval]
  simpa [Complex.mul_re, ha_im, hover_real] using mul_pos ha_pos hover_pos

private lemma L₁₀_eventuallyPos_of_over
    (hL10_real : ResToImagAxis.Real L₁₀)
    (hpos_event : ∀ᶠ t : ℝ in atTop,
      (0 : ℝ) < (L₁₀_over (UpperHalfPlane.ofComplex (Complex.I * t))).re) :
    ResToImagAxis.EventuallyPos L₁₀ := by
  rcases (Filter.eventually_atTop.1 hpos_event) with ⟨t₀, ht₀⟩
  refine ⟨hL10_real, max t₀ 1, by positivity, ?_⟩
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le (by positivity : (0 : ℝ) < max t₀ 1) ht
  let z : UpperHalfPlane := ⟨Complex.I * t, by simpa using htpos⟩
  have hz_of : UpperHalfPlane.ofComplex (Complex.I * t) = z := by
    simpa [z] using ofComplex_I_mul_eq_mk t htpos
  have hpos_over : 0 < (L₁₀_over z).re := by
    simpa [hz_of] using ht₀ t (le_trans (le_max_left _ _) ht)
  obtain ⟨ha_ne, ha_im, ha_pos⟩ := q₂q₃_mul_pos_re_and_im_zero t htpos
  rcases L₁₀_eval_and_over_im_zero hL10_real t htpos z rfl _ rfl ha_ne ha_im with
    ⟨hL10_eval, hover_real⟩
  exact L₁₀_resToImagAxis_re_pos_of_mul t z _ ha_im hover_real hL10_eval ha_pos hpos_over

/-- `L₁₀` is eventually positive on the imaginary axis. -/
public lemma L₁₀_eventuallyPos : ResToImagAxis.EventuallyPos L₁₀ :=
  L₁₀_eventuallyPos_of_over L₁₀_real_resToImagAxis
    (L₁₀_over_eventuallyPos_re L₁₀_over_tendsto_atImInfty)

end
