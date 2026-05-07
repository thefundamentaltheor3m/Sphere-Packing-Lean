module

public import SpherePacking.ModularForms.Eisensteinqexpansions
public import SpherePacking.ModularForms.IsCuspForm
public import SpherePacking.ModularForms.summable_lems

@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open scoped ArithmeticFunction.sigma

noncomputable section

/-! ## Helper lemmas for dimension-one arguments -/

/-- In a rank-one module, every element is a scalar multiple of any nonzero element. -/
lemma exists_smul_eq_of_rank_one {M : Type*} [AddCommGroup M] [Module ℂ M]
    (hrank : Module.rank ℂ M = 1) {e : M} (he : e ≠ 0) (f : M) : ∃ c : ℂ, f = c • e := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' e he).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp hrank) f
  exact ⟨c, hc.symm⟩

/-- Symmetric version: `c • e = f` instead of `f = c • e`. -/
lemma exists_smul_eq_of_rank_one' {M : Type*} [AddCommGroup M] [Module ℂ M]
    (hrank : Module.rank ℂ M = 1) {e : M} (he : e ≠ 0) (f : M) : ∃ c : ℂ, c • e = f :=
  (finrank_eq_one_iff_of_nonzero' e he).mp (Module.rank_eq_one_iff_finrank_eq_one.mp hrank) f

/-- Convert smul equality of modular forms to pointwise equality. -/
lemma smul_modularForm_eq_pointwise {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f g : ModularForm Γ k}
    {c : ℂ} (h : f = c • g) (z : ℍ) : (f : ℍ → ℂ) z = c * (g : ℍ → ℂ) z := by
  simpa [ModularForm.coe_smul, smul_eq_mul] using
    congrFun (congrArg (↑· : ModularForm _ _ → ℍ → ℂ) h) z

section Definitions

/- The Eisenstein Series E₄ and E₆ -/
def E₄ := E 4 (by norm_num)

def E₆ := E 6 (by norm_num)

lemma E4_apply (z : ℍ) : E₄ z = E 4 (by norm_num) z := rfl

lemma E6_apply (z : ℍ) : E₆ z = E 6 (by norm_num) z := rfl

/-- E₄ is 1-periodic: E₄(z + 1) = E₄(z). This follows from E₄ being a modular form for Γ(1). -/
lemma E₄_periodic (z : ℍ) : E₄ ((1 : ℝ) +ᵥ z) = E₄ z := by
  simpa using SlashInvariantForm.vAdd_width_periodic 1 4 1 E₄.toSlashInvariantForm z

/-- E₆ is 1-periodic: E₆(z + 1) = E₆(z). This follows from E₆ being a modular form for Γ(1). -/
lemma E₆_periodic (z : ℍ) : E₆ ((1 : ℝ) +ᵥ z) = E₆ z := by
  simpa using SlashInvariantForm.vAdd_width_periodic 1 6 1 E₆.toSlashInvariantForm z

/-- E₄ transforms under S as: E₄(-1/z) = z⁴ · E₄(z) -/
lemma E₄_S_transform (z : ℍ) : E₄ (ModularGroup.S • z) = z ^ (4 : ℕ) * E₄ z := by
  have h : (E₄.toFun ∣[(4 : ℤ)] ModularGroup.S) z = E₄.toFun z := by
    apply congrFun
    apply E₄.slash_action_eq'
    simp only [Subgroup.mem_map, CongruenceSubgroup.mem_Gamma_one]
    use ModularGroup.S
  rw [SL_slash_apply] at h
  simp only [ModularGroup.denom_S, zpow_neg, ModularForm.toFun_eq_coe] at h
  field_simp [ne_zero z] at h
  exact h

/-- E₆ transforms under S as: E₆(-1/z) = z⁶ · E₆(z) -/
lemma E₆_S_transform (z : ℍ) : E₆ (ModularGroup.S • z) = z ^ (6 : ℕ) * E₆ z := by
  have h : (E₆.toFun ∣[(6 : ℤ)] ModularGroup.S) z = E₆.toFun z := by
    apply congrFun
    apply E₆.slash_action_eq'
    simp only [Subgroup.mem_map, CongruenceSubgroup.mem_Gamma_one]
    use ModularGroup.S
  rw [SL_slash_apply] at h
  simp only [ModularGroup.denom_S, zpow_neg, ModularForm.toFun_eq_coe] at h
  field_simp [ne_zero z] at h
  exact h

variable (f : ℍ → ℂ) (k : ℤ) (z : ℍ)

end Definitions

open Complex Real

noncomputable section

/- φ₀, φ₋₂ and φ₋₄, except we can't use - signs in subscripts for definitions... -/
def φ₀ (z : ℍ) := (((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) / (Δ z)
def φ₂' (z : ℍ) := (E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)
def φ₄' (z : ℍ) := ((E₄ z) ^ 2) / (Δ z)
/- We extend these definitions to ℂ for convenience. -/
def φ₀'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₀ ⟨z, hz⟩ else 0
def φ₂'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₂' ⟨z, hz⟩ else 0
def φ₄'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₄' ⟨z, hz⟩ else 0

lemma φ₀''_def {z : ℂ} (hz : 0 < z.im) : φ₀'' z = φ₀ ⟨z, hz⟩ := by simp [φ₀'', hz]

lemma φ₀''_mem_upperHalfPlane {z : ℂ} (hz : z ∈ upperHalfPlaneSet) : φ₀'' z = φ₀ ⟨z, hz⟩ :=
  φ₀''_def hz

lemma φ₀''_coe_upperHalfPlane (z : ℍ) : φ₀'' (z : ℂ) = φ₀ z := by
  simpa using (φ₀''_def (z := (z : ℂ)) (UpperHalfPlane.im_pos z))

open SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

open scoped Real MatrixGroups CongruenceSubgroup

local notation "𝕢" => Periodic.qParam
lemma Ek_q_exp_zero (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    (qExpansion 1 (E k hk)).coeff 0 = 1 :=
  EisensteinSeries.E_qExpansion_coeff_zero (mod_cast hk) hk2

private lemma E4_eq' :
    (E₄ : ℍ → ℂ) = (ModularForm.E (k := 4) (by norm_num) : ℍ → ℂ) := rfl

private lemma E6_eq' :
    (E₆ : ℍ → ℂ) = (ModularForm.E (k := 6) (by norm_num) : ℍ → ℂ) := rfl

lemma E4_q_exp : (fun m => (qExpansion 1 E₄).coeff m) =
    fun m => if m = 0 then 1 else (240 : ℂ) * (σ 3 m) := by
  ext m
  rw [E4_eq', EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) m]
  split
  · rfl
  · simp [bernoulli, bernoulli'_four]; ring

lemma E4_q_exp_zero : (qExpansion 1 E₄).coeff 0 = 1 := by
  simpa using congr_fun E4_q_exp 0

private lemma bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have h1 : Nat.choose 6 4 = 15 := by decide
  have h2 : Nat.choose 6 2 = 15 := by decide
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, h1, h2, h5]

lemma E6_q_exp : (fun m => (qExpansion 1 E₆).coeff m) =
    fun m => if m = 0 then 1 else -(504 : ℂ) * (σ 5 m) := by
  ext m
  rw [E6_eq', EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) m]
  split
  · rfl
  · simp only [bernoulli, bernoulli'_six]; push_cast; ring

lemma E6_q_exp_zero : (qExpansion 1 E₆).coeff 0 = 1 := by
  simpa using congr_fun E6_q_exp 0

private lemma qExpansion_constantCoeff_mul {a b : ℤ} (f : ModularForm Γ(1) a)
    (g : ModularForm Γ(1) b) :
    PowerSeries.constantCoeff (qExpansion 1 ⇑(f.mul g)) =
      PowerSeries.constantCoeff (qExpansion 1 ⇑f) *
        PowerSeries.constantCoeff (qExpansion 1 ⇑g) := by
  rw [coe_mul, qExpansion_mul (analyticAt_cuspFunction_zero f (by positivity) (by simp))
                              (analyticAt_cuspFunction_zero g (by positivity) (by simp))]
  exact PowerSeries.constantCoeff.map_mul (qExpansion 1 ⇑f) (qExpansion 1 ⇑g)

theorem E4E6_coeff_zero_eq_zero :
  (PowerSeries.coeff 0)
      (qExpansion 1
        ((1 / 1728 : ℂ) •
          ((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3 - (DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2)
            12)) =
    0 := by
  simp only [one_div, DirectSum.sub_apply]
  have hsub :
      qExpansion (1 : ℕ)
        ⇑((((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3) 12) -
          (((DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12)) =
      qExpansion 1 (((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3) 12) -
        qExpansion 1 (((DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12) := by
    simpa using
      (qExpansion_sub (Γ := Γ(1)) (h := (1 : ℕ))
        (hh := by positivity) (hΓ := by simp)
        ((((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3) 12))
        ((((DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12)))
  rw [← Nat.cast_one (R := ℝ), ← qExpansion_smul2, hsub]
  simp only [_root_.map_smul, map_sub, smul_eq_mul,
    mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
  have hds : (((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3) 12) = E₄.mul (E₄.mul E₄) := by
    ext z
    rw [pow_three, @DirectSum.of_mul_of, @DirectSum.of_mul_of]
    rfl
  have hd6 : ((DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12 = E₆.mul E₆ := by
    ext z
    rw [pow_two, @DirectSum.of_mul_of]
    rfl
  rw [hds, hd6]
  have hq4 : PowerSeries.constantCoeff (qExpansion 1 ⇑(E₄.mul (E₄.mul E₄))) = 1 := by
    rw [qExpansion_constantCoeff_mul E₄ (E₄.mul E₄), qExpansion_constantCoeff_mul E₄ E₄]
    rw [show PowerSeries.constantCoeff (qExpansion 1 ⇑E₄) = 1 by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using E4_q_exp_zero]
    norm_num
  have hq6 : PowerSeries.constantCoeff (qExpansion 1 ⇑(E₆.mul E₆)) = 1 := by
    rw [qExpansion_constantCoeff_mul E₆ E₆]
    rw [show PowerSeries.constantCoeff (qExpansion 1 ⇑E₆) = 1 by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using E6_q_exp_zero]
    norm_num
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using sub_eq_zero.mpr (hq4.trans hq6.symm)

def Delta_E4_E6_aux : CuspForm (CongruenceSubgroup.Gamma 1) 12 :=
  let F := DirectSum.of _ 4 E₄
  let G := DirectSum.of _ 6 E₆
  cuspFormOfCoeffZero ((1 / 1728 : ℂ) • (F ^ 3 - G ^ 2) 12) E4E6_coeff_zero_eq_zero

lemma Delta_cuspFuntion_eq : Set.EqOn (cuspFunction 1 Delta)
     (fun y => (y : ℂ) * ∏' i, ((1 : ℂ) - y ^ (i + 1)) ^ 24) (Metric.ball 0 (1/2)) := by
  rw [cuspFunction]
  intro y hy
  by_cases hyn0 : y = 0
  · rw [hyn0]
    simp
    have := CuspFormClass.cuspFunction_apply_zero (h := 1) Delta zero_lt_one (by simp)
    rw [cuspFunction] at this
    simpa using this
  · rw [Function.Periodic.cuspFunction_eq_of_nonzero]
    · simp
      have hz := Function.Periodic.im_invQParam_pos_of_norm_lt_one (h := 1) (by exact
        Real.zero_lt_one) (q := y) ?_ ?_
      · rw [ofComplex_apply_of_im_pos hz]
        rw [Delta_apply, Δ]
        have hq := Function.Periodic.qParam_right_inv (h := 1) ?_ (q := y) hyn0
        · simp
          have : cexp (2 * ↑π * Complex.I * Periodic.invQParam 1 y) = y := by
            nth_rw 2 [← hq]
            congr 1
            simp
          rw [this]
          congr
          ext n
          congr
          have : cexp (2 * ↑π * Complex.I * (↑n + 1) * Periodic.invQParam 1 y) =
            (cexp (2 * ↑π * Complex.I * Periodic.invQParam 1 y)) ^ (n+1) := by
            rw [← Complex.exp_nsmul]
            congr
            ring
          rw [this]
          congr
        exact Ne.symm (zero_ne_one' ℝ)
      · simp at hy
        apply lt_trans hy
        linarith
      · exact hyn0
    exact hyn0

lemma Delta_ne_zero : Delta ≠ 0 := by
  have := Δ_ne_zero UpperHalfPlane.I
  rw [@DFunLike.ne_iff]
  refine ⟨UpperHalfPlane.I, this⟩

lemma asdf : TendstoLocallyUniformlyOn
    (fun n : ℕ ↦ fun y : ℂ => ∏ x ∈ Finset.range n, (1 - y ^ (x + 1)))
    (fun x : ℂ ↦ ∏' i, (1 - x ^ (i + 1))) atTop
    (Metric.ball (0 : ℂ) (1/2 : ℝ))
      := by
  have hclosed :
      TendstoUniformlyOn (fun n : ℕ ↦ fun y : ℂ => ∏ x ∈ Finset.range n, (1 - y ^ (x + 1)))
        (fun x : ℂ ↦ ∏' i, (1 - x ^ (i + 1))) atTop (Metric.closedBall (0 : ℂ) (1/2 : ℝ)) := by
    have hsum : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
      rw [@summable_nat_add_iff, summable_geometric_iff_norm_lt_one]
      simp
      exact two_inv_lt_one
    simpa [sub_eq_add_neg] using
      (hsum.hasProdUniformlyOn_nat_one_add (f := fun n : ℕ => fun y : ℂ => -y ^ (n + 1))
        (hK := isCompact_closedBall (0 : ℂ) (1 / 2))
        (h := Filter.Eventually.of_forall (fun n (x : ℂ) hx => by
          have hx' : ‖x‖ ≤ (1 / 2 : ℝ) := by
            simpa [Metric.mem_closedBall, dist_eq_norm] using hx
          calc
            ‖-x ^ (n + 1)‖ = ‖x‖ ^ (n + 1) := by simp
            _ ≤ (1 / 2 : ℝ) ^ (n + 1) := by
              exact pow_le_pow_left₀ (norm_nonneg x) hx' _))
        (hcts := fun n => by fun_prop)).tendstoUniformlyOn_finsetRange
  exact TendstoLocallyUniformlyOn.mono (s := Metric.closedBall (0 : ℂ) (1/2 : ℝ))
    hclosed.tendstoLocallyUniformlyOn ball_subset_closedBall

theorem diffwithinat_prod_1 :
    DifferentiableWithinAt ℂ (fun (y : ℂ) ↦ ∏' (i : ℕ), (1 - y ^ (i + 1)) ^ 24) (ball 0 (1 / 2)) 0
    := by
  suffices DifferentiableWithinAt ℂ (fun (n : ℂ) ↦ (∏' (i : ℕ), (1 - n ^ (i + 1))) ^ 24) (ball 0 (1
    / 2)) 0 by
    apply this.congr
    · intro x hx
      rw [← tprod_pow _ (by apply multipliable_lt_one x (by simp at *; apply lt_trans hx; exact
        two_inv_lt_one))]
    simp
  apply DifferentiableWithinAt.pow
  have hu := asdf.differentiableOn ?_ ?_
  · apply hu
    simp
  · simp
    use 0
    intro b hb
    simpa [Finset.prod_fn] using
      (DifferentiableOn.finset_prod (u := Finset.range b)
        (f := fun x : ℕ => fun y : ℂ => 1 - y ^ (x + 1))
        (s := Metric.ball 0 (1 / 2)) (by
          intro i hi
          fun_prop))
  exact isOpen_ball


lemma Delta_q_one_term : (qExpansion 1 Delta).coeff 1 = 1 := by
  rw [qExpansion_coeff]
  simp
  rw [← derivWithin_of_isOpen (s := Metric.ball 0 (1 / 2 : ℝ)) (isOpen_ball) (by simp) ]
  rw [derivWithin_congr Delta_cuspFuntion_eq]
  · rw [derivWithin_fun_mul]
    · simp
      have := derivWithin_id' ( 0 * ∏' (i : ℕ), (1 - 0 ^ (i + 1)) ^ 24 : ℂ)
        (Metric.ball 0 (1 / 2 : ℝ)) ?_
      · simp at *
        rw [this]
      simp
      apply IsOpen.uniqueDiffWithinAt
      · exact isOpen_ball
      refine mem_ball_self (by norm_num)
    · exact differentiableWithinAt_id'
    apply diffwithinat_prod_1
  simp
  exact CuspFormClass.cuspFunction_apply_zero (h := 1) Delta zero_lt_one (by simp)

variable {α β γ : Type*}

variable [CommMonoid α] [TopologicalSpace α] [UniformSpace α]

lemma E4_q_exp_one : (qExpansion 1 E₄).coeff 1 = 240 := by
  have := E4_q_exp
  have H := congr_fun this 1
  simp at H
  rw [H]

lemma E6_q_exp_one : (qExpansion 1 E₆).coeff 1 = -504 := by
  have := E6_q_exp
  have H := congr_fun this 1
  simp at H
  rw [H]

lemma antidiagonal_one : Finset.antidiagonal 1 = {(1,0), (0,1)} := by
  ext ⟨x,y⟩
  simp
  omega

lemma E4_pow_q_exp_one : (qExpansion 1 ((E₄).mul ((E₄).mul E₄))).coeff 1 = 3 * 240 := by
  rw [← Nat.cast_one (R := ℝ), qExpansion_mul_coeff, qExpansion_mul_coeff]
  rw [PowerSeries.coeff_mul, antidiagonal_one]
  simp
  rw [PowerSeries.coeff_mul, antidiagonal_one]
  have := E4_q_exp_zero
  simp at *
  simp_rw [E4_q_exp_one, this]
  ring

lemma Ek_ne_zero (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) : E k hk ≠ 0 :=
  EisensteinSeries.E_ne_zero (mod_cast hk) hk2

/-This is in the mod forms repo-/
lemma E4_ne_zero : E₄ ≠ 0 := by
  apply Ek_ne_zero 4 (by norm_num) (by exact Nat.even_iff.mpr rfl)

lemma E6_ne_zero : E₆ ≠ 0 := by
    apply Ek_ne_zero 6 (by norm_num) (by exact Nat.even_iff.mpr rfl)

lemma modularForm_normalise (f : ModularForm Γ(1) k) (hf : ¬ IsCuspForm Γ(1) k f) :
    (qExpansion 1 (((qExpansion 1 f).coeff 0)⁻¹ • f)).coeff 0 = 1 := by
  rw [← Nat.cast_one (R := ℝ), ← qExpansion_smul2, Nat.cast_one]
  refine inv_mul_cancel₀ ?_
  intro h
  rw [← (IsCuspForm_iff_coeffZero_eq_zero k f)] at h
  exact hf h

lemma PowerSeries.coeff_add (f g : PowerSeries ℂ) (n : ℕ) :
    (f + g).coeff n = (f.coeff n) + (g.coeff n) := by
  exact rfl

open ArithmeticFunction

/-!
## Imaginary Axis Properties

Properties of Eisenstein series when restricted to the positive imaginary axis z = I*t.
-/

section ImagAxisProperties

open _root_.Complex hiding I

/-- `(-2πi)^k` is real for even k. -/
lemma neg_two_pi_I_pow_even_real (k : ℕ) (hk : Even k) :
    ((-2 * Real.pi * Complex.I) ^ k : ℂ).im = 0 := by
  have h : (-2 * Real.pi * Complex.I) ^ k = (-(2 * Real.pi) : ℂ) ^ k * Complex.I ^ k := by ring
  rw [h]
  have h1 : ((-(2 * Real.pi)) ^ k : ℂ).im = 0 := by norm_cast
  have h2 : (Complex.I ^ k : ℂ).im = 0 := by
    obtain ⟨m, rfl⟩ := hk
    simp only [← two_mul, pow_mul, I_sq]
    -- (-1)^m is real: ±1
    rcases m.even_or_odd with hm | hm <;> simp [hm.neg_one_pow]
  simp [Complex.mul_im, h1, h2]

/-- On imaginary axis z = I*t, the q-expansion exponent 2πi·n·z reduces to -(2πnt).
This is useful for reusing the same algebraic simplification across `E₂`, `E₄`, `E₆`. -/
lemma exp_imag_axis_arg (t : ℝ) (ht : 0 < t) (n : ℕ+) :
    2 * Real.pi * Complex.I * (⟨Complex.I * t, by simp [ht]⟩ : ℍ) * n =
    (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
  push_cast
  ring_nf
  simp only [I_sq]
  ring

/-- `E_k(it)` is real for all `t > 0` when `k` is even and `k ≥ 4`.
This is the generalized theorem from which `E₄_imag_axis_real` and `E₆_imag_axis_real` follow. -/
theorem E_even_imag_axis_real (k : ℕ) (hk : (3 : ℤ) ≤ k) (hk2 : Even k) :
    ResToImagAxis.Real (E k hk).toFun := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  change (E k hk z).im = 0
  have hq := E_k_q_expansion k hk hk2 z
  simp only at hq ⊢
  rw [hq]
  simp only [add_im, one_im, zero_add]
  -- Step 1: Show each term in the sum is real on the imaginary axis
  have hterm_im : ∀ n : ℕ+, (↑((ArithmeticFunction.sigma (k - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n)).im = 0 := by
    intro n
    have hexp_arg : 2 * ↑Real.pi * Complex.I * z * n = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
      simpa [z] using exp_imag_axis_arg (t := t) ht n
    rw [hexp_arg]
    -- Using simp only: `simp` gives false positive linter warning but args are needed
    simp only [mul_im, exp_ofReal_im, natCast_im, mul_zero, zero_mul, add_zero]
  -- Step 2: Summability of the series
  have hsum : Summable fun n : ℕ+ => ↑((ArithmeticFunction.sigma (k - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    · intro n
      calc ‖↑((ArithmeticFunction.sigma (k - 1)) ↑n) * cexp (2 * ↑Real.pi * Complex.I * z * n)‖
          = ‖(↑((ArithmeticFunction.sigma (k - 1)) ↑n) : ℂ)‖ *
            ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := norm_mul _ _
        _ ≤ ‖(↑n : ℂ) ^ k‖ * ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := by
          apply mul_le_mul_of_nonneg_right
          · rw [Complex.norm_natCast, Complex.norm_pow, Complex.norm_natCast]
            have hbound := ArithmeticFunction.sigma_le_pow_succ (k - 1) n
            have hk' : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
            rw [hk'] at hbound
            exact_mod_cast hbound
          · exact norm_nonneg _
        _ = ‖(↑n : ℂ) ^ k * cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := (norm_mul _ _).symm
    · have := a33 k 1 z
      simp only [PNat.val_ofNat, Nat.cast_one, mul_one] at this
      exact summable_norm_iff.mpr this
  -- Step 3: The sum has zero imaginary part
  have hsum_im : (∑' (n : ℕ+), ↑((ArithmeticFunction.sigma (k - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n)).im = 0 := by
    rw [im_tsum hsum]
    simp [hterm_im]
  -- Step 4: Show the coefficient is real and product with sum is real
  have hpow_im : ((-2 * Real.pi * Complex.I) ^ k : ℂ).im = 0 :=
    neg_two_pi_I_pow_even_real k hk2
  have hfact_im : ((k - 1).factorial : ℂ).im = 0 := by simp
  -- For ζ(k) when k ≥ 4, it's real (mathlib: riemannZeta_im_eq_zero_of_one_lt)
  have hzeta_im : (riemannZeta k).im = 0 := by
    rw [show (k : ℂ) = ((k : ℝ) : ℂ) from by push_cast; ring]
    exact riemannZeta_im_eq_zero_of_one_lt (by exact_mod_cast show 1 < (k : ℤ) by omega)
  have hinv_zeta_im : (1 / riemannZeta k).im = 0 := by simp [hzeta_im]
  simp only [mul_im, div_im, hinv_zeta_im, hsum_im, hpow_im, hfact_im]
  ring

/-- `E₄(it)` is real for all `t > 0`. -/
@[fun_prop]
theorem E₄_imag_axis_real : ResToImagAxis.Real E₄.toFun :=
  E_even_imag_axis_real 4 (by norm_num) (by norm_num)

/-- `E₆(it)` is real for all `t > 0`. -/
@[fun_prop]
theorem E₆_imag_axis_real : ResToImagAxis.Real E₆.toFun :=
  E_even_imag_axis_real 6 (by norm_num) (by norm_num)

/-- `E₂(it)` is real for all `t > 0`. -/
@[fun_prop]
theorem E₂_imag_axis_real : ResToImagAxis.Real E₂ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  change (E₂ z).im = 0
  have hq := E₂_eq z
  rw [hq]
  simp only [sub_im, one_im, zero_sub]
  -- Step 1: Show each term in the sum is real on the imaginary axis
  have hterm_im : ∀ n : ℕ+, (↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z))).im = 0 := by
    intro n
    have hexp_arg : 2 * ↑Real.pi * Complex.I * n * z = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
      have h1 : 2 * ↑Real.pi * Complex.I * z * n = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
        simpa [z] using exp_imag_axis_arg (t := t) ht n
      simpa [mul_assoc, mul_left_comm, mul_comm] using h1
    -- Using simp only: `simp` gives false positive linter warning but args are needed
    have hone_sub_real : (1 - cexp (2 * ↑Real.pi * Complex.I * ↑↑n * ↑z)).im = 0 := by
      simp only [Complex.sub_im, Complex.one_im, hexp_arg, exp_ofReal_im, sub_zero]
    have hnum_real : (↑n * cexp (2 * ↑Real.pi * Complex.I * n * z)).im = 0 := by
      simp only [mul_im, natCast_im, hexp_arg, exp_ofReal_im, mul_zero, zero_mul, add_zero]
    simp [Complex.div_im, hnum_real, hone_sub_real]
  -- Step 2: Summability of the series
  have hsum : Summable fun n : ℕ+ => ↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z)) := by
    set r : ℂ := cexp (2 * ↑Real.pi * Complex.I * z) with hr
    have hr_norm : ‖r‖ < 1 := by
      simpa [hr] using exp_upperHalfPlane_lt_one z
    have hs : Summable fun n : ℕ => (n : ℂ) * r ^ n / (1 - r ^ n) := by
      simpa [pow_one] using
        (summable_norm_pow_mul_geometric_div_one_sub (k := 1) (r := r) hr_norm)
    refine (hs.comp_injective PNat.coe_injective).congr ?_
    intro n
    have hpow : r ^ (n : ℕ) = cexp (2 * ↑Real.pi * Complex.I * (↑n : ℂ) * z) := by
      rw [hr]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.exp_nat_mul (2 * ↑Real.pi * Complex.I * z) (n : ℕ)).symm
    simp [hpow]
  -- Step 3: The sum has zero imaginary part
  have hsum_im : (∑' (n : ℕ+), ↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z))).im = 0 := by
    rw [Complex.im_tsum hsum]
    simp [hterm_im]
  -- Step 4: 24 * sum is real, so -(24 * sum).im = 0
  simp [Complex.mul_im, hsum_im]

end ImagAxisProperties

/-! ## Boundedness of E₂ -/

/-- For im(z) ≥ 1, ‖exp(2πiz)‖ ≤ exp(-2π).

This bound on the q-parameter is useful for estimating q-expansions when im(z) ≥ 1. -/
lemma norm_exp_two_pi_I_le_exp_neg_two_pi (z : ℍ) (hz : 1 ≤ z.im) :
    ‖cexp (2 * π * Complex.I * z)‖ ≤ Real.exp (-2 * π) := by
  have h : (2 * ↑π * Complex.I * (z : ℂ)).re = -2 * π * z.im := by
    rw [show (2 : ℂ) * ↑π * Complex.I * z = Complex.I * (2 * π * z) by ring]
    simp [Complex.I_re, Complex.I_im, mul_comm]
  rw [Complex.norm_exp, h, Real.exp_le_exp]
  nlinarith [Real.pi_pos]

/-- Bound on the q-series ∑ n·qⁿ/(1-qⁿ) that appears in E₂.

For ‖q‖ < 1, we have ‖∑ₙ₌₁ n·qⁿ/(1-qⁿ)‖ ≤ ‖q‖/(1-‖q‖)³.

The key estimates are:
- |1-qⁿ| ≥ 1-|q|ⁿ ≥ 1-|q| for n ≥ 1
- |n·qⁿ/(1-qⁿ)| ≤ n·|q|ⁿ/(1-|q|)
- ∑ n·rⁿ = r/(1-r)², so ∑ n·rⁿ/(1-r) = r/(1-r)³ -/
lemma norm_tsum_logDeriv_expo_le {q : ℂ} (hq : ‖q‖ < 1) :
    ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤ ‖q‖ / (1 - ‖q‖) ^ 3 := by
  set r : ℝ := ‖q‖
  have hr_norm_lt_one : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg (norm_nonneg q)]
  have hsumm_nat : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr_norm_lt_one
  have hsumm_majorant : Summable (fun n : ℕ+ => (n : ℝ) * r ^ (n : ℕ) / (1 - r)) := by
    simpa [div_eq_mul_inv] using (hsumm_nat.subtype _).mul_right (1 - r)⁻¹
  have hterm_bound : ∀ n : ℕ+, ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤
      n * r ^ (n : ℕ) / (1 - r) := fun n => by
    rw [norm_div, norm_mul, Complex.norm_natCast]
    have hdenom_lower : 1 - r ≤ ‖1 - q ^ (n : ℕ)‖ := calc
      1 - r ≤ 1 - r ^ (n : ℕ) := by
        have : r ^ (n : ℕ) ≤ r := pow_le_of_le_one q.norm_nonneg hq.le n.ne_zero
        linarith
      _ = 1 - ‖q ^ (n : ℕ)‖ := by rw [norm_pow]
      _ ≤ ‖1 - q ^ (n : ℕ)‖ := by
        have := norm_sub_norm_le (1 : ℂ) (q ^ (n : ℕ)); simp only [norm_one] at this; linarith
    calc ↑n * ‖q ^ (n : ℕ)‖ / ‖1 - q ^ (n : ℕ)‖ ≤ ↑n * ‖q ^ (n : ℕ)‖ / (1 - r) := by
          exact div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
            (sub_pos.mpr hq) hdenom_lower
      _ = ↑n * r ^ (n : ℕ) / (1 - r) := by rw [norm_pow]
  have hsumm_norms : Summable (fun n : ℕ+ => ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) hterm_bound hsumm_majorant
  calc ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
      ≤ ∑' n : ℕ+, ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ := norm_tsum_le_tsum_norm hsumm_norms
    _ ≤ ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r) :=
        hsumm_norms.tsum_le_tsum hterm_bound hsumm_majorant
    _ = r / (1 - r) ^ 3 := by
        simp only [div_eq_mul_inv, tsum_mul_right, tsum_pnat_coe_mul_geometric hr_norm_lt_one,
          pow_succ]
        field_simp

/-- Monotone version of `norm_tsum_logDeriv_expo_le`: if ‖q‖ ≤ r < 1, then
‖∑ n·qⁿ/(1-qⁿ)‖ ≤ r/(1-r)³. Useful when we have a uniform bound on ‖q‖. -/
lemma norm_tsum_logDeriv_expo_le_of_norm_le {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (hr : r < 1) :
    ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤ r / (1 - r) ^ 3 := by
  have hq : ‖q‖ < 1 := lt_of_le_of_lt hqr hr
  have hr_nonneg : 0 ≤ r := le_trans (norm_nonneg _) hqr
  calc ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
      ≤ ‖q‖ / (1 - ‖q‖) ^ 3 := norm_tsum_logDeriv_expo_le hq
    _ ≤ r / (1 - r) ^ 3 := by
        have := sub_pos.mpr hr
        have := sub_pos.mpr hq
        gcongr

/-- E₂ is bounded at infinity.

Uses `E₂_eq`: E₂(z) = 1 - 24·Σₙ₌₁ n·qⁿ/(1-qⁿ) where q = exp(2πiz).
For im(z) ≥ 1, |q| ≤ exp(-2π), so by `norm_tsum_logDeriv_expo_le`,
|E₂| ≤ 1 + 24·exp(-2π)/(1-exp(-2π))³. -/
lemma E₂_isBoundedAtImInfty : IsBoundedAtImInfty E₂ := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  set r₀ : ℝ := Real.exp (-2 * π)
  have hr₀_lt_one : r₀ < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  refine ⟨1 + 24 * (r₀ / (1 - r₀) ^ 3), 1, fun z hz => ?_⟩
  rw [E₂_eq]
  set q : ℂ := cexp (2 * π * Complex.I * z)
  have hq_bound : ‖q‖ ≤ r₀ := norm_exp_two_pi_I_le_exp_neg_two_pi z hz
  -- Rewrite sum in terms of q^n
  set S := ∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))
  have hS_eq : ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
      (1 - cexp (2 * π * Complex.I * ↑n * ↑z)) = S := by
    congr 1; ext n
    have : cexp (2 * π * Complex.I * n * z) = q ^ (n : ℕ) := by
      change _ = (cexp (2 * π * Complex.I * z)) ^ (n : ℕ)
      rw [← Complex.exp_nat_mul]; ring_nf
    simp [this]
  calc ‖1 - 24 * ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
          (1 - cexp (2 * π * Complex.I * ↑n * ↑z))‖
      = ‖1 - 24 * S‖ := by rw [hS_eq]
    _ ≤ 1 + 24 * ‖S‖ := by
        calc _ ≤ ‖(1 : ℂ)‖ + ‖24 * S‖ := norm_sub_le _ _
          _ = _ := by simp
    _ ≤ 1 + 24 * (r₀ / (1 - r₀) ^ 3) := by
        gcongr; exact norm_tsum_logDeriv_expo_le_of_norm_le hq_bound hr₀_lt_one

/-- E₄ is bounded at infinity (as a modular form). -/
lemma E₄_isBoundedAtImInfty : IsBoundedAtImInfty E₄.toFun :=
  ModularFormClass.bdd_at_infty E₄

/-- The product E₂ · E₄ is bounded at infinity. -/
lemma E₂_mul_E₄_isBoundedAtImInfty : IsBoundedAtImInfty (E₂ * E₄.toFun) :=
  E₂_isBoundedAtImInfty.mul E₄_isBoundedAtImInfty
