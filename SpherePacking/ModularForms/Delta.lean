/-
Copyright (c) 2024 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import SpherePacking.ForMathlib.Cusps
public import SpherePacking.ModularForms.clog_arg_lems
public import SpherePacking.ModularForms.E2
public import SpherePacking.ModularForms.exp_lems
public import SpherePacking.ModularForms.ResToImagAxis
public import SpherePacking.ModularForms.SlashActionAuxil
public import SpherePacking.Tactic.NormNumI


/-! # The modular discriminant `Δ`

Mathlib's `ModularForm.discriminant` provides the modular discriminant together with its
fundamental properties: non-vanishing (`ModularForm.discriminant_ne_zero`), invariance under the
generators of `SL(2, ℤ)`, decay at `i∞`, and the associated cusp form `CuspForm.discriminant` of
weight `12` for `𝒮ℒ`. This file introduces the notation `Δ` for it and provides the complements
used in this project:

* `Δ_eq_cexp_prod`, `DiscriminantProductFormula`: the `q`-product for `Δ` written with explicit
  complex exponentials, indexed by `ℕ` and `ℕ+` respectively.
* `Δ_periodic`, `Δ_S_transform`: pointwise transformation laws under the generators.
* `Δ_imag_axis_pos`: `Δ` is real and positive on the positive imaginary axis.
-/

@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat ModularForm

/-- `Δ` is mathlib's modular discriminant `ModularForm.discriminant`. -/
notation "Δ" => ModularForm.discriminant

lemma MultipliableEtaProductExpansion_pnat (z : ℍ) :
    Multipliable fun n : ℕ+ ↦ 1 - cexp (2 * π * Complex.I * n * z) := by
  rw [multipliable_pnat_iff_multipliable_succ
    (f := fun n : ℕ ↦ 1 - cexp (2 * π * Complex.I * n * z))]
  exact (ModularForm.multipliableLocallyUniformlyOn_eta.multipliable z.2).congr fun n ↦ by
    rw [ModularForm.eta_q_eq_cexp]
    push_cast
    ring_nf

/-- The discriminant as a `q`-product with explicit complex exponentials. -/
lemma Δ_eq_cexp_prod (z : ℍ) : Δ z = cexp (2 * π * Complex.I * z) * ∏' n : ℕ,
    (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24 := by
  simp only [ModularForm.discriminant_eq_q_prod, ModularForm.eta_q_eq_cexp, Periodic.qParam,
    ofReal_one, div_one]

lemma DiscriminantProductFormula (z : ℍ) : Δ z = cexp (2 * π * Complex.I * z) * ∏' n : ℕ+,
    (1 - cexp (2 * π * Complex.I * n * z)) ^ 24 := by
  rw [Δ_eq_cexp_prod]
  congr 1
  rw [tprod_pnat_eq_tprod_succ (f := fun n : ℕ ↦ (1 - cexp (2 * π * Complex.I * n * z)) ^ 24)]
  exact tprod_congr fun n ↦ by push_cast; ring_nf

/-- `Δ` is 1-periodic: `Δ (z + 1) = Δ z`. -/
lemma Δ_periodic (z : ℍ) : Δ ((1 : ℝ) +ᵥ z) = Δ z :=
  SlashInvariantForm.vAdd_apply_of_mem_strictPeriods CuspForm.discriminant z
    one_mem_strictPeriods_SL

/-- `Δ` transforms under `S` as `Δ (-1 / z) = z ^ 12 * Δ z`. -/
lemma Δ_S_transform (z : ℍ) : Δ (ModularGroup.S • z) = z ^ (12 : ℕ) * Δ z := by
  have h := congrFun ModularForm.discriminant_S_invariant z
  rw [SL_slash_apply] at h
  simp only [ModularGroup.denom_S, zpow_neg] at h
  field_simp [ne_zero z] at h
  rw [h, mul_comm]

theorem Δ_boundedfactor :
    Tendsto (fun x : ℍ ↦ ∏' n : ℕ, (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑x)) ^ 24) atImInfty
      (𝓝 1) := by
  apply ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow.congr
  exact fun x ↦ tprod_congr fun n ↦ by rw [ModularForm.eta_q_eq_cexp]

open Real

/-- On the positive imaginary axis, `Δ (i t)` is the real quantity
`e ^ (-2 π t) * ∏' (1 - e ^ (-2 π (n + 1) t)) ^ 24`. -/
private lemma resToImagAxis_Δ_eq (t : ℝ) (ht : 0 < t) :
    Function.resToImagAxis Δ t =
      ((Real.exp (-2 * π * t) *
        ∏' n : ℕ, (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24 : ℝ) : ℂ) := by
  have h1 : cexp (2 * ↑π * Complex.I * (Complex.I * t)) = rexp (-2 * π * t) := by
    calc
      _ = cexp (2 * ↑π * (Complex.I * Complex.I) * t) := by ring_nf
      _ = rexp (-2 * π * t) := by simp
  have h2 (n : ℕ) :
      cexp (2 * π * Complex.I * (n + 1) * (Complex.I * t)) = rexp (-(2 * π * (n + 1) * t)) := by
    calc
      _ = cexp (2 * ↑π * (n + 1) * (Complex.I * Complex.I) * t) := by ring_nf
      _ = rexp (-(2 * π * (n + 1) * t)) := by simp
  set fR : ℕ → ℝ := fun n => (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24
  have hMap' : Complex.ofReal (∏' n : ℕ, fR n) = ∏' n : ℕ, ((fR n : ℝ) : ℂ) := by
    simpa using
      (Function.LeftInverse.map_tprod (f := fR) (g := Complex.ofRealHom.toMonoidHom)
        (hg := by change Continuous (fun x : ℝ => (x : ℂ)); exact Complex.continuous_ofReal)
        (hg' := Complex.continuous_re) (hgg' := by intro x; simp))
  simp [ResToImagAxis, ht, Δ_eq_cexp_prod, h1, h2, hMap', fR]

private lemma tprod_pos (t : ℝ) (ht : 0 < t) :
    0 < ∏' n : ℕ, (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24 := by
  have hpos_pow : ∀ n : ℕ, 0 < (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24 := fun n =>
    pow_pos (sub_pos.mpr (exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity)))) _
  have hsum_log : Summable fun n : ℕ =>
      Real.log ((1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24) := by
    simp only [Real.log_pow, Nat.cast_ofNat, ← smul_eq_mul]
    apply Summable.const_smul
    simp [sub_eq_add_neg]
    apply Real.summable_log_one_add_of_summable
    apply Summable.neg
    have h0 : Summable fun n : ℕ => Real.exp (n * (-(2 * π * t))) :=
      Real.summable_exp_nat_mul_iff.mpr
        (by simpa using neg_lt_zero.mpr (by positivity : 0 < 2 * π * t))
    simpa [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using
      (summable_nat_add_iff 1).2 h0
  rw [← Real.rexp_tsum_eq_tprod
        (f := fun n : ℕ => (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24) hpos_pow hsum_log]
  exact Real.exp_pos _

/-- `Δ` is real and positive on the positive imaginary axis. -/
lemma Δ_imag_axis_pos : ResToImagAxis.Pos Δ := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [resToImagAxis_Δ_eq t ht, Complex.ofReal_im]
  · rw [resToImagAxis_Δ_eq t ht, Complex.ofReal_re]
    exact mul_pos (Real.exp_pos _) (tprod_pos t ht)
