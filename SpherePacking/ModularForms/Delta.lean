module

public import SpherePacking.ModularForms.SlashActionAuxil
public import SpherePacking.ModularForms.clog_arg_lems
public import SpherePacking.ModularForms.E2
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import SpherePacking.ModularForms.exp_lems
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import SpherePacking.ModularForms.ResToImagAxis
import Mathlib.NumberTheory.ModularForms.QExpansion
import SpherePacking.Tactic.NormNumI

public import SpherePacking.ForMathlib.Cusps

@[expose] public section

/-!
# Discriminant Product Formula

This file proves results such as `DiscriminantProductFormula`, `Delta_eq_eta_pow`,
`Discriminant_T_invariant`, `Discriminant_S_invariant`, `I_in_atImInfty`.
-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat ModularForm

open ArithmeticFunction

theorem term_ne_zero (z : ℍ) (n : ℕ) : 1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑z) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have := exp_upperHalfPlane_lt_one_nat z n
  rw [← h] at this
  simp only [norm_one, lt_self_iff_false] at *

lemma MultipliableEtaProductExpansion (z : ℍ) :
    Multipliable (fun (n : ℕ) => (1 - cexp (2 * π * Complex.I * (n + 1) * z))) := by
  apply (ModularForm.multipliable_one_sub_pow
    (UpperHalfPlane.norm_exp_two_pi_I_lt_one z)).congr
  intro n
  congr 1
  rw [← Complex.exp_nat_mul]
  push_cast
  ring_nf

lemma MultipliableEtaProductExpansion_pnat (z : ℍ) :
    Multipliable (fun (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z))) := by
  conv =>
    enter [1]
    ext n
    rw [sub_eq_add_neg]
  let g := (fun (n : ℕ) => (1 - cexp (2 * π * Complex.I * n * z)) )
  have := MultipliableEtaProductExpansion z
  conv at this =>
    enter [1]
    ext n
    rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp]
  rw [← multipliable_pnat_iff_multipliable_succ (f := g)] at this
  apply this.congr
  intro b
  rfl

lemma MultipliableDeltaProductExpansion_pnat (z : ℍ) :
    Multipliable (fun (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z))^24) :=
  (MultipliableEtaProductExpansion_pnat z).pow 24

noncomputable section Definitions

/- The discriminant form -/
def Δ (z : UpperHalfPlane) := cexp (2 * π * Complex.I * z) * ∏' (n : ℕ),
    (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24

/-- Reindex `Δ` from a product over `ℕ` to a product over `ℕ+`. -/
lemma DiscriminantProductFormula (z : ℍ) :
    Δ z = cexp (2 * π * Complex.I * z) * ∏' (n : ℕ+),
    (1 - cexp (2 * π * Complex.I * (n) * z)) ^ 24 := by
  simpa [Δ, Nat.cast_add, Nat.cast_one, add_mul] using
    (tprod_pnat_eq_tprod_succ (f := fun n : ℕ =>
      (1 - cexp (2 * π * Complex.I * (n : ℂ) * z)) ^ 24)).symm

/-- The discriminant form is the 24th power of the Dedekind eta function. -/
lemma Delta_eq_eta_pow (z : ℍ) : Δ z = (η z) ^ 24 := by
  have hm : Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n z) := by
    refine (MultipliableEtaProductExpansion z).congr ?_
    intro n
    simp [ModularForm.eta_q_eq_cexp]
  rw [ModularForm.eta, Δ, mul_pow, ← hm.tprod_pow 24]
  congr
  · rw [Periodic.qParam]
    rw [← Complex.exp_nat_mul]
    congr 1
    simp [field]
  · ext n
    simp [ModularForm.eta_q_eq_cexp]

/-This should be easy from the definition and the Mulitpliable bit. -/
/-- The project's `Δ` agrees with mathlib's `ModularForm.discriminant`. -/
lemma Δ_eq_discriminant : Δ = ModularForm.discriminant :=
  funext fun z => Delta_eq_eta_pow z

lemma Δ_ne_zero (z : UpperHalfPlane) : Δ z ≠ 0 := by
  rw [Delta_eq_eta_pow]
  exact pow_ne_zero 24 (ModularForm.eta_ne_zero (z := (z : ℂ)) z.2)

lemma Discriminant_T_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ := by
  rw [Δ_eq_discriminant]
  exact ModularForm.discriminant_T_invariant

lemma Discriminant_S_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.S) = Δ := by
  rw [Δ_eq_discriminant]
  exact ModularForm.discriminant_S_invariant

/-- Δ as a SlashInvariantForm of weight 12 -/
@[expose] public def Discriminant_SIF : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := Δ
  slash_action_eq' :=
    slashaction_generators_GL2R Δ 12 Discriminant_S_invariant Discriminant_T_invariant

/-- Δ is 1-periodic: Δ(z + 1) = Δ(z) -/
lemma Δ_periodic (z : ℍ) : Δ ((1 : ℝ) +ᵥ z) = Δ z := by
  change (Discriminant_SIF : ℍ → ℂ) ((1 : ℝ) +ᵥ z) = (Discriminant_SIF : ℍ → ℂ) z
  simpa only [Int.cast_one, Nat.cast_one, one_mul, mul_one] using
    SlashInvariantForm.vAdd_width_periodic 1 12 1 Discriminant_SIF z

/-- Δ transforms under S as: Δ(-1/z) = z¹² · Δ(z) -/
public lemma Δ_S_transform (z : ℍ) : Δ (ModularGroup.S • z) = z ^ (12 : ℕ) * Δ z := by
  have h := congrFun Discriminant_S_invariant z
  rw [SL_slash_apply] at h
  simp only [ModularGroup.denom_S, zpow_neg] at h
  field_simp [ne_zero z] at h
  rw [h, mul_comm]

theorem Delta_boundedfactor :
  Tendsto (fun x : ℍ ↦ ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑x)) ^ 24) atImInfty
    (𝓝 1) := by
  apply ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow.congr
  exact fun x => tprod_congr fun n => by rw [ModularForm.eta_q_eq_cexp]

/-- The discriminant has a zero at the cusp `∞` after any `SL(2,ℤ)` slash action. -/
public lemma Discriminant_zeroAtImInfty :
    ∀ γ ∈ 𝒮ℒ, IsZeroAtImInfty (Discriminant_SIF ∣[(12 : ℤ)] (γ : GL (Fin 2) ℝ)) := by
  intro γ ⟨γ', hγ⟩
  rw [IsZeroAtImInfty, ZeroAtFilter]
  have := Discriminant_SIF.slash_action_eq' γ ⟨γ', CongruenceSubgroup.mem_Gamma_one γ', hγ⟩
  simp at *
  rw [this]
  have h0 : Tendsto Δ atImInfty (𝓝 0) := by
    rw [Δ_eq_discriminant]
    exact ModularForm.discriminant_isZeroAtImInfty
  simpa [Discriminant_SIF] using h0

/-- The discriminant cusp form of weight `12` on `Γ(1)`. -/
def Delta : CuspForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := Discriminant_SIF
  slash_action_eq' := Discriminant_SIF.slash_action_eq'
  holo' := by
    rw [mdifferentiable_iff]
    simp only [SlashInvariantForm.coe_mk]
    have he2 : DifferentiableOn ℂ (fun z => (η z) ^ 24) {z | 0 < z.im} := by
      apply DifferentiableOn.pow
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      simpa using (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (z := x) hx)
    rw [Discriminant_SIF]
    simp only [SlashInvariantForm.coe_mk]
    apply he2.congr
    intro z hz
    have := Delta_eq_eta_pow (⟨z, hz⟩ : ℍ)
    simp only [comp_apply] at *
    rw [ofComplex_apply_of_im_pos hz]
    exact this
  zero_at_cusps' hc := zero_at_cusps_of_zero_at_infty hc Discriminant_zeroAtImInfty

/-- Unfolding lemma for `Delta`. -/
public lemma Delta_apply (z : ℍ) : Delta z = Δ z := rfl

/-- The discriminant cusp form is nonzero. -/
public lemma Delta_ne_zero : Delta ≠ 0 := by
  refine (DFunLike.ne_iff).2 ⟨UpperHalfPlane.I, ?_⟩
  simpa [Delta_apply] using Δ_ne_zero UpperHalfPlane.I

/-- The discriminant cusp form is `Theta`-equivalent to `exp (-2π Im z)` at `Im z → ∞`. -/
public lemma Delta_isTheta_rexp : Delta =Θ[atImInfty] (fun τ => Real.exp (-2 * π * τ.im)) := by
  rw [Asymptotics.IsTheta]
  refine ⟨by simpa using CuspFormClass.exp_decay_atImInfty (h := 1) Delta, ?_⟩
  have := ModularForm.exp_isBigO_discriminant
  rw [← Δ_eq_discriminant] at this
  exact this.congr_right fun z => (Delta_apply z).symm

lemma cexp_aux1 (t : ℝ) : cexp (2 * ↑π * Complex.I * (Complex.I * t)) = rexp (-2 * π * t) := by
  calc
    _ = cexp (2 * ↑π * (Complex.I * Complex.I) * t) := by ring_nf
    _ = rexp (-2 * π * t) := by simp

lemma cexp_aux2 (t : ℝ) (n : ℕ)
    : cexp (2 * π * Complex.I * (n + 1) * (Complex.I * t)) = rexp (-(2 * π * (n + 1) * t)) := by
  calc
    _ = cexp (2 * ↑π * (n + 1) * (Complex.I * Complex.I) * t) := by ring_nf
    _ = rexp (-(2 * π * (n + 1) * t)) := by simp

lemma cexp_aux3 (t : ℝ) (n : ℕ) (ht : 0 < t) : 0 < 1 - rexp (-(2 * π * (n + 1) * t)) := by
  have _ : rexp (-(2 * π * (n + 1) * t)) < 1 := Real.exp_lt_one_iff.mpr (by simp; positivity)
  linarith

lemma cexp_aux4 (t : ℝ) (n : ℕ) : (cexp (-2 * π * (n + 1) * t)).im = 0 := by
  simpa [Complex.ofReal_mul, Complex.ofReal_neg] using exp_ofReal_im (-2 * π * (n + 1) * t)

lemma cexp_aux5 (t : ℝ) : (cexp (-(2 * π * t))).im = 0 := by
  simpa [Complex.ofReal_mul, Complex.ofReal_neg] using exp_ofReal_im (-(2 * π * t))

/-- If `Im z = 0` then `Im (z^m) = 0`. -/
public lemma Complex.im_pow_eq_zero_of_im_eq_zero {z : ℂ} (hz : z.im = 0) (m : ℕ) :
    (z ^ m).im = 0 :=
  (Complex.im_eq_zero_iff_isSelfAdjoint _).2 <|
    IsSelfAdjoint.pow ((Complex.im_eq_zero_iff_isSelfAdjoint z).1 hz) m

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

/-- `Δ (i t)` is real for `t > 0`. -/
public lemma Delta_imag_axis_real : ResToImagAxis.Real Δ := by
  intro t ht
  have cexp_aux4 (t : ℝ) (n : ℕ) : (cexp (-2 * π * (n + 1) * t)).im = 0 := by
    simpa [Complex.ofReal_mul, Complex.ofReal_neg] using exp_ofReal_im (-2 * π * (n + 1) * t)
  simp only [resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, Δ, mul_im]
  set g : ℕ → ℂ := fun n => (1 - cexp (2 * π * Complex.I * (n + 1) * (Complex.I * t))) ^ 24
  have hArg (n : ℕ) :
      2 * (π : ℂ) * Complex.I * (n + 1) * (Complex.I * t) = -(2 * (π : ℂ) * (n + 1) * t) := by
    calc
      2 * (π : ℂ) * Complex.I * (n + 1) * (Complex.I * t)
        = 2 * (π : ℂ) * (Complex.I * Complex.I) * (n + 1) * t := by ring
      _ = -(2 * (π : ℂ) * (n + 1) * t) := by simp
  have him_g : ∀ n, (g n).im = 0 := fun n => by
    have : (cexp (-(2 * (π : ℂ) * ((n + 1) : ℂ) * t))).im = 0 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (cexp_aux4 t n)
    have : ((1 - cexp (2 * (π : ℂ) * Complex.I * (n + 1) * (Complex.I * t))) : ℂ).im = 0 := by
      simpa [Complex.sub_im, hArg n] using this
    simpa [g] using Complex.im_pow_eq_zero_of_im_eq_zero this 24
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hmul : Multipliable g := by
    have hz : (z : ℂ) = Complex.I * t := rfl
    simpa [g, hz] using
      (Multipliable.pow (by simpa using MultipliableEtaProductExpansion z) 24)
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
      cexp (2 * π * Complex.I * (n + 1) * (Complex.I * t)) = rexp (-(2 * π * (n + 1) * t)) :=
    cexp_aux2 t n
  have cexp_aux1 (t : ℝ) : cexp (2 * ↑π * Complex.I * (Complex.I * t)) = rexp (-2 * π * t) := by
    simpa using (cexp_aux2 t 0)
  set fR : ℕ → ℝ := fun n => (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24
  have hMap' :
      Complex.ofReal (∏' n : ℕ, fR n) = ∏' n : ℕ, ((fR n : ℝ) : ℂ) := by
    simpa using
      (Function.LeftInverse.map_tprod (f := fR)
        (g := Complex.ofRealHom.toMonoidHom)
        (hg := by
          change Continuous (fun x : ℝ => (x : ℂ))
          exact Complex.continuous_ofReal)
        (hg' := Complex.continuous_re)
        (hgg' := by intro x; simp))
  simpa [ResToImagAxis, ht, Delta_apply, Δ, cexp_aux1, cexp_aux2, hMap', fR] using
    Complex.ofReal_re (Real.exp (-2 * π * t) * ∏' n : ℕ, fR n)

private lemma Delta_tprod_pos_nat_im (z : ℍ) :
    0 < ∏' (n : ℕ), (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24 := by
  have hpos_pow :
      ∀ n : ℕ, 0 < (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24 := fun n =>
        pow_pos (sub_pos.2 ((Real.exp_lt_one_iff).2 (neg_lt_zero.2 (by positivity)))) _
  have hsum_log :
      Summable (fun n : ℕ => Real.log ((1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24)) := by
    simp only [Real.log_pow, Nat.cast_ofNat, ← smul_eq_mul]
    apply Summable.const_smul
    apply Real.summable_log_one_add_of_summable
    apply Summable.neg
    have h0 : Summable (fun n : ℕ => Real.exp (n * (-(2 * π * z.im)))) :=
      (Real.summable_exp_nat_mul_iff.mpr
        (by
          simpa using (neg_lt_zero.mpr (by positivity : 0 < 2 * π * z.im))))
    simpa [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using
      ((summable_nat_add_iff 1).2 h0)
  rw [← Real.rexp_tsum_eq_tprod
        (f := fun n : ℕ => (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24)
        hpos_pow hsum_log]
  exact Real.exp_pos _

/-- `Δ (i t)` is positive for `t > 0`. -/
public lemma Delta_imag_axis_pos : ResToImagAxis.Pos Δ := by
  rw [ResToImagAxis.Pos]
  refine And.intro Delta_imag_axis_real ?_
  intro t ht
  have hprod :
      0 < ∏' (n : ℕ), (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24 := by
    simpa [UpperHalfPlane.im] using
      (Delta_tprod_pos_nat_im (z := ⟨Complex.I * t, by simp [ht]⟩))
  rw [re_ResToImagAxis_Delta_eq_real_prod t ht]
  exact mul_pos (Real.exp_pos _) hprod

end Definitions
