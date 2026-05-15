module

public import SpherePacking.ModularForms.SlashActionAuxil
public import SpherePacking.ModularForms.Eta
public import SpherePacking.ModularForms.MultipliableLemmas
public import SpherePacking.ModularForms.ResToImagAxis
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import SpherePacking.Tactic.NormNumI

public import SpherePacking.ForMathlib.Cusps

@[expose] public section

/-!
# Discriminant Product Formula

This file re-exports mathlib's `ModularForm.discriminant` under the project notations `Δ`/`Delta`
and packages the corollaries used in the sphere-packing argument.
-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

noncomputable section Definitions

/-- The discriminant form (`= ModularForm.discriminant`). -/
abbrev Δ : ℍ → ℂ := ModularForm.discriminant

/-- Unfold `Δ` to mathlib's q-product form. -/
lemma Δ_eq_qProd (z : ℍ) : Δ z = cexp (2 * π * Complex.I * z) * ∏' (n : ℕ),
    (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24 := by
  rw [show (Δ : ℍ → ℂ) = discriminant from rfl, discriminant_eq_q_prod]
  simp [Periodic.qParam, eta_q_eq_cexp]

/-- Reindex `Δ` from a product over `ℕ` to a product over `ℕ+`. -/
lemma DiscriminantProductFormula (z : ℍ) :
    Δ z = cexp (2 * π * Complex.I * z) * ∏' (n : ℕ+),
    (1 - cexp (2 * π * Complex.I * (n) * z)) ^ 24 := by
  simpa [Δ_eq_qProd, Nat.cast_add, Nat.cast_one, add_mul] using
    (tprod_pnat_eq_tprod_succ (f := fun n : ℕ =>
      (1 - cexp (2 * π * Complex.I * (n : ℂ) * z)) ^ 24)).symm

/-- The discriminant form is the 24th power of the Dedekind eta function. -/
lemma Delta_eq_eta_pow (z : ℍ) : Δ z = (η z) ^ 24 := rfl

/-- The discriminant is nonzero on the upper half-plane. -/
lemma Δ_ne_zero (z : ℍ) : Δ z ≠ 0 := discriminant_ne_zero z

/-- Invariance of `Δ` under the translation `T : z ↦ z + 1`. -/
public lemma Discriminant_T_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ :=
  discriminant_T_invariant

/-- Invariance of `Δ` under the inversion `S : z ↦ -1/z`. -/
public lemma Discriminant_S_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.S) = Δ :=
  discriminant_S_invariant

/-- Δ as a SlashInvariantForm of weight 12. -/
@[expose] public def Discriminant_SIF : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := Δ
  slash_action_eq' :=
    slashaction_generators_GL2R Δ 12 Discriminant_S_invariant Discriminant_T_invariant

/-- Δ is 1-periodic: Δ(z + 1) = Δ(z). -/
public lemma Δ_periodic (z : ℍ) : Δ ((1 : ℝ) +ᵥ z) = Δ z :=
  by simpa using SlashInvariantForm.vAdd_width_periodic 1 12 1 Discriminant_SIF z

/-- Δ transforms under S as: Δ(-1/z) = z¹² · Δ(z). -/
public lemma Δ_S_transform (z : ℍ) : Δ (ModularGroup.S • z) = z ^ (12 : ℕ) * Δ z := by
  have h := congrFun Discriminant_S_invariant z
  rw [SL_slash_apply] at h
  simp only [ModularGroup.denom_S, zpow_neg] at h
  field_simp [ne_zero z] at h
  rw [h, mul_comm]

lemma I_in_atImInfty (A : ℝ) : { z : ℍ | A ≤ z.im} ∈ atImInfty := by
  rw [atImInfty_mem]; exact ⟨A, fun _ hz ↦ hz⟩

/-- Scalar multiplication of `ℍ` by a positive natural number. -/
public instance natPosSMul : SMul ℕ+ ℍ where
  smul x z := UpperHalfPlane.mk (x * z) <| by
    have hx : 0 < (x : ℝ) := by exact_mod_cast x.pos
    simpa [mul_im] using mul_pos hx z.2

/-- Coercion formula for the `ℕ+`-scalar action on `ℍ`. -/
public theorem natPosSMul_apply (c : ℕ+) (z : ℍ) :
    ((c • z : ℍ) : ℂ) = (c : ℂ) * (z : ℂ) := rfl

/-- The bounded factor in the discriminant product tends to `1` at `Im z → ∞`. -/
public theorem Delta_boundedfactor :
    Tendsto (fun x : ℍ ↦ ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑x)) ^ 24)
      atImInfty (𝓝 1) := by
  refine (tendsto_atImInfty_tprod_one_sub_eta_q_pow.congr fun z => ?_)
  exact tprod_congr fun n => by rw [eta_q_eq_cexp]

/-- The discriminant cusp form of weight `12` on `Γ(1)`. -/
def Delta : CuspForm (CongruenceSubgroup.Gamma 1) 12 :=
  (CuspForm.discriminant : CuspForm _ 12).copy Δ rfl CongruenceSubgroup.Gamma_one_coe_eq_SL

/-- Unfolding lemma for `Delta`. -/
public lemma Delta_apply (z : ℍ) : Delta z = Δ z := rfl

/-- The discriminant cusp form is nonzero. -/
public lemma Delta_ne_zero : Delta ≠ 0 :=
  (DFunLike.ne_iff).2 ⟨UpperHalfPlane.I, by simpa [Delta_apply] using Δ_ne_zero UpperHalfPlane.I⟩

/-- The discriminant cusp form is `Θ`-equivalent to `exp(-2π Im z)` at `Im z → ∞`. -/
public lemma Delta_isTheta_rexp : Delta =Θ[atImInfty] (fun τ => Real.exp (-2 * π * τ.im)) :=
  ⟨by simpa using CuspFormClass.exp_decay_atImInfty (h := 1) Delta,
    by simpa [Delta_apply, Δ] using exp_isBigO_discriminant⟩

/-- Division of a cusp form by the discriminant, as a `ModularForm`. -/
public def CuspForm_div_Discriminant (k : ℤ)
    (f : CuspForm (CongruenceSubgroup.Gamma 1) k) :
    ModularForm (CongruenceSubgroup.Gamma 1) (k - 12) :=
  let f' : CuspForm 𝒮ℒ k := f.copy f rfl CongruenceSubgroup.Gamma_one_coe_eq_SL.symm
  (CuspForm.divDiscriminant f').copy (fun z => f z / Δ z)
    (by ext z; exact (CuspForm.divDiscriminant_apply f' z).symm)
    CongruenceSubgroup.Gamma_one_coe_eq_SL

/-- Pointwise evaluation of `CuspForm_div_Discriminant`. -/
public lemma CuspForm_div_Discriminant_apply (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k)
    (z : ℍ) : (CuspForm_div_Discriminant k f) z = f z / Δ z := rfl

/-- The map `CuspForm_div_Discriminant k` is additive. -/
public theorem CuspForm_div_Discriminant_Add (k : ℤ)
    (x y : CuspForm (CongruenceSubgroup.Gamma 1) k) :
    CuspForm_div_Discriminant k (x + y) =
      CuspForm_div_Discriminant k x + CuspForm_div_Discriminant k y := by
  ext z; simp [CuspForm_div_Discriminant_apply, add_div]

/-! ## Imaginary-axis positivity -/

private lemma Complex_im_finset_prod_eq_zero_of_im_eq_zero (s : Finset ℕ) (f : ℕ → ℂ)
    (h : ∀ i ∈ s, (f i).im = 0) : (∏ i ∈ s, f i).im = 0 := by
  refine (Complex.im_eq_zero_iff_isSelfAdjoint _).2 ?_
  revert h
  refine Finset.induction_on s (by intro; simp) ?_
  intro a s ha ih h
  simpa [Finset.prod_insert, ha] using
    IsSelfAdjoint.mul
      ((Complex.im_eq_zero_iff_isSelfAdjoint (f a)).1 (h a (by simp [ha])))
      (ih (fun i hi => h i (by simp [hi])))

private lemma Complex_im_tprod_eq_zero_of_im_eq_zero (f : ℕ → ℂ) (hf : Multipliable f)
    (him : ∀ n, (f n).im = 0) : (∏' n : ℕ, f n).im = 0 := by
  have hz : ∀ n, (∏ i ∈ Finset.range n, f i).im = 0 := fun n =>
    Complex_im_finset_prod_eq_zero_of_im_eq_zero (s := Finset.range n) (f := f)
      (by intro i _; simpa using him i)
  have h2 : Tendsto (fun n => (∏ i ∈ Finset.range n, f i).im) atTop (𝓝 (0 : ℝ)) := by simp [hz]
  exact tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp hf.hasProd.tendsto_prod_nat) h2

/-- If `Im z = 0` then `Im (z^m) = 0`. -/
public lemma Complex.im_pow_eq_zero_of_im_eq_zero {z : ℂ} (hz : z.im = 0) (m : ℕ) :
    (z ^ m).im = 0 :=
  (Complex.im_eq_zero_iff_isSelfAdjoint _).2 <|
    IsSelfAdjoint.pow ((Complex.im_eq_zero_iff_isSelfAdjoint z).1 hz) m

/-- `Δ (i t)` is real for `t > 0`. -/
public lemma Delta_imag_axis_real : ResToImagAxis.Real Δ := by
  intro t ht
  have cexp_aux (t : ℝ) (n : ℕ) : (cexp (-2 * π * (n + 1) * t)).im = 0 := by
    simpa [Complex.ofReal_mul, Complex.ofReal_neg] using exp_ofReal_im (-2 * π * (n + 1) * t)
  simp only [resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, Δ_eq_qProd, mul_im]
  set g : ℕ → ℂ := fun n => (1 - cexp (2 * π * Complex.I * (n + 1) * (Complex.I * t))) ^ 24
  have hArg (n : ℕ) :
      2 * (π : ℂ) * Complex.I * (n + 1) * (Complex.I * t) = -(2 * (π : ℂ) * (n + 1) * t) := by
    calc
      2 * (π : ℂ) * Complex.I * (n + 1) * (Complex.I * t)
        = 2 * (π : ℂ) * (Complex.I * Complex.I) * (n + 1) * t := by ring
      _ = -(2 * (π : ℂ) * (n + 1) * t) := by simp
  have him_g : ∀ n, (g n).im = 0 := fun n => by
    have : (cexp (-(2 * (π : ℂ) * ((n + 1) : ℂ) * t))).im = 0 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (cexp_aux t n)
    have : ((1 - cexp (2 * (π : ℂ) * Complex.I * (n + 1) * (Complex.I * t))) : ℂ).im = 0 := by
      simpa [Complex.sub_im, hArg n] using this
    simpa [g] using Complex.im_pow_eq_zero_of_im_eq_zero this 24
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hmul : Multipliable g := by
    have hz : (z : ℂ) = Complex.I * t := rfl
    simpa [g, hz] using
      (Multipliable_pow _ (by simpa using MultipliableEtaProductExpansion z) 24)
  have htprod_im : (∏' n : ℕ, g n).im = 0 :=
    Complex_im_tprod_eq_zero_of_im_eq_zero g hmul him_g
  have him_pref : (cexp (2 * π * Complex.I * (Complex.I * t))).im = 0 := by
    have : (cexp (-(2 * π * t))).im = 0 := by
      simpa [Complex.ofReal_mul, Complex.ofReal_neg] using exp_ofReal_im (-(2 * π * t))
    simpa [by simpa using hArg 0] using this
  simp [g, him_pref, htprod_im]

/-- Real-part formula for `Δ (i t)` on the imaginary axis, rewritten as a real infinite product. -/
public lemma re_ResToImagAxis_Delta_eq_real_prod (t : ℝ) (ht : 0 < t) :
    (Δ.resToImagAxis t).re =
      Real.exp (-2 * π * t) *
        ∏' (n : ℕ), (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24 := by
  have cexp_aux2 (t : ℝ) (n : ℕ) :
      cexp (2 * π * Complex.I * (n + 1) * (Complex.I * t)) = rexp (-(2 * π * (n + 1) * t)) := by
    calc
      _ = cexp (2 * ↑π * (n + 1) * (Complex.I * Complex.I) * t) := by ring_nf
      _ = rexp (-(2 * π * (n + 1) * t)) := by simp
  have cexp_aux1 (t : ℝ) : cexp (2 * ↑π * Complex.I * (Complex.I * t)) = rexp (-2 * π * t) := by
    simpa using (cexp_aux2 t 0)
  set fR : ℕ → ℝ := fun n => (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24
  have hMap' :
      Complex.ofReal (∏' n : ℕ, fR n) = ∏' n : ℕ, ((fR n : ℝ) : ℂ) := by
    simpa using
      (Function.LeftInverse.map_tprod (f := fR)
        (g := Complex.ofRealHom.toMonoidHom)
        (hg := by simpa using Complex.continuous_ofReal)
        (hg' := Complex.continuous_re)
        (hgg' := by intro x; simp))
  simpa [ResToImagAxis, ht, Delta_apply, Δ_eq_qProd, cexp_aux1, cexp_aux2, hMap', fR] using
    Complex.ofReal_re (Real.exp (-2 * π * t) * ∏' n : ℕ, fR n)

private lemma Delta_tprod_pos_nat_im (z : ℍ) :
    0 < ∏' (n : ℕ), (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24 := by
  have hpos_pow : ∀ n : ℕ, 0 < (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24 := fun n =>
    pow_pos (sub_pos.2 ((Real.exp_lt_one_iff).2 (neg_lt_zero.2 (by positivity)))) _
  have hsum_log :
      Summable (fun n : ℕ => Real.log ((1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24)) := by
    simp only [Real.log_pow, Nat.cast_ofNat, ← smul_eq_mul]
    apply Summable.const_smul
    apply Real.summable_log_one_add_of_summable
    apply Summable.neg
    have h0 : Summable (fun n : ℕ => Real.exp (n * (-(2 * π * z.im)))) :=
      Real.summable_exp_nat_mul_iff.mpr
        (by simpa using (neg_lt_zero.mpr (by positivity : 0 < 2 * π * z.im)))
    simpa [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using
      ((summable_nat_add_iff 1).2 h0)
  rw [← Real.rexp_tsum_eq_tprod
        (f := fun n : ℕ => (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24)
        hpos_pow hsum_log]
  exact Real.exp_pos _

/-- `Δ (i t)` is positive for `t > 0`. -/
public lemma Delta_imag_axis_pos : ResToImagAxis.Pos Δ := by
  refine ⟨Delta_imag_axis_real, fun t ht => ?_⟩
  rw [re_ResToImagAxis_Delta_eq_real_prod t ht]
  exact mul_pos (Real.exp_pos _)
    (by simpa [UpperHalfPlane.im] using
      Delta_tprod_pos_nat_im (z := ⟨Complex.I * t, by simp [ht]⟩))

end Definitions
