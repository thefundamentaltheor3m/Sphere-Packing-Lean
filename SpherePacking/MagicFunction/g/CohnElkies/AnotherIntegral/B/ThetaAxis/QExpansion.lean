module
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Mul
public import SpherePacking.ModularForms.JacobiTheta
public import SpherePacking.ModularForms.ResToImagAxis
public import SpherePacking.MagicFunction.b.PsiBounds
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Topology.Order.Compact
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common

/-! # Theta-function `q`-expansion bounds on the imaginary axis (`Θ₂`, `Θ₃`, `Θ₄`). -/

namespace MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis

open scoped BigOperators UpperHalfPlane

open Real Complex Filter Topology
open Set

noncomputable section

public lemma norm_exp_neg_pi_mul_le_one (t : ℝ) (ht : 0 < t) :
    ‖(Real.exp (-Real.pi * t) : ℂ)‖ ≤ 1 := by
  simpa [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp] using
    Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht.le] : (-Real.pi * t) ≤ 0)

lemma norm_Theta2_term_resToImagAxis (n : ℤ) (t : ℝ) (ht : 0 < t) :
    ‖Θ₂_term n ⟨(Complex.I : ℂ) * t, by simp [ht]⟩‖ =
      Real.exp (-Real.pi * (((n : ℝ) + (1 / 2)) ^ 2) * t) := by
  set r : ℝ := (n : ℝ) + (2⁻¹ : ℝ)
  simp_rw [Θ₂_term, div_eq_mul_inv, one_mul]
  rw [show (Real.pi * Complex.I * (n + (2⁻¹ : ℂ) : ℂ) ^ 2 * ((⟨(Complex.I : ℂ) * t,
        by simp [ht]⟩ : ℍ) : ℂ) : ℂ) = ((-(Real.pi * r ^ 2 * t) : ℝ) : ℂ) from by
      simp [show (n + (2⁻¹ : ℂ) : ℂ) = (r : ℂ) by push_cast [r]; ring]; ring_nf; simp,
    Complex.norm_exp_ofReal]
  simp [r]

public lemma Theta3_eq_jacobiTheta (τ : ℍ) : Θ₃ τ = jacobiTheta (τ : ℂ) := by
  simp [Θ₃, Θ₃_term, jacobiTheta]

lemma Theta4_eq_jacobiTheta_add_one (τ : ℍ) : Θ₄ τ = jacobiTheta ((τ : ℂ) + 1) :=
  tsum_congr fun n => by
    have hpiI : Complex.exp (Real.pi * Complex.I * (n : ℂ) ^ 2) = (-1 : ℂ) ^ n := by
      rw [show (Real.pi * Complex.I * (n : ℂ) ^ 2 : ℂ) = (n ^ 2 : ℤ) * (Real.pi * Complex.I) by
        push_cast; ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]
      simp [neg_one_zpow_eq_ite, show Even (n ^ 2 : ℤ) ↔ Even n from by
        simpa using Int.even_pow' (m := n) (n := 2) two_ne_zero]
    rw [show Θ₄_term n τ = Complex.exp (Real.pi * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ)) *
      Complex.exp (Real.pi * Complex.I * (n : ℂ) ^ 2) from by
      simp [Θ₄_term, mul_assoc, mul_comm, hpiI.symm], ← Complex.exp_add]; ring_nf

public lemma exists_bound_norm_Theta2_resToImagAxis_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖Θ₂.resToImagAxis t‖ ≤ C := by
  let majorant : ℤ → ℝ := fun n ↦ Real.exp (-Real.pi / 4) *
    Real.exp (-Real.pi * ((1 : ℝ) * (n ^ 2) - 2 * (1 / 2 : ℝ) * |n|))
  have hmajorant : Summable majorant := by
    simpa [majorant, pow_zero, one_mul] using
      (summable_pow_mul_jacobiTheta₂_term_bound (S := (1 / 2 : ℝ)) (T := (1 : ℝ))
        (by positivity) 0).mul_left (Real.exp (-Real.pi / 4))
  refine ⟨∑' n : ℤ, majorant n, fun t ht => ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set τ : ℍ := ⟨Complex.I * t, by simp [htpos]⟩
  have hterm : ∀ n : ℤ, ‖Θ₂_term n τ‖ ≤ majorant n := fun n => by
    have hpref : ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)‖ ≤ Real.exp (-Real.pi / 4) := by
      rw [show ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)‖ = Real.exp (-Real.pi * t / 4) by
        simp [Complex.norm_exp, τ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])
    have hcore : ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ ≤
        Real.exp (-Real.pi * ((1 : ℝ) * (n ^ 2) - 2 * (1 / 2 : ℝ) * |n|)) := by
      rw [show ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ =
          Real.exp (-Real.pi * (t * ((n ^ 2 : ℤ) : ℝ) + t * (n : ℝ))) by
        simp [norm_jacobiTheta₂_term, τ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        ring_nf]
      have hbase : t * (((n ^ 2 : ℤ) : ℝ) + (n : ℝ)) ≥ ((n ^ 2 : ℤ) : ℝ) - (|n| : ℝ) := by
        have hdiff : 0 ≤ ((n ^ 2 : ℤ) : ℝ) - (|n| : ℝ) := sub_nonneg.2 <| mod_cast
          (by simpa [Int.natCast_natAbs] using Int.natAbs_le_self_sq n : (|n| : ℤ) ≤ n ^ 2)
        nlinarith [(mod_cast neg_abs_le n : (-(|n| : ℝ)) ≤ (n : ℝ)), htpos.le, hdiff, ht]
      simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using
        Real.exp_le_exp.mpr (by nlinarith [hbase, Real.pi_pos] :
          -Real.pi * (t * (((n ^ 2 : ℤ) : ℝ) + (n : ℝ))) ≤
            -Real.pi * (((n ^ 2 : ℤ) : ℝ) - (|n| : ℝ)))
    simpa [show Θ₂_term n τ = Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4) *
        jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ) by simp [Θ₂_term_as_jacobiTheta₂_term],
      majorant, mul_assoc] using mul_le_mul hpref hcore (by positivity) (by positivity)
  simpa [Function.resToImagAxis, ResToImagAxis, htpos, Θ₂, τ] using
    tsum_of_norm_bounded hmajorant.hasSum hterm

private lemma norm_jacobiTheta_I_mul_add_real_sub_one_le (a : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    ‖jacobiTheta (((Complex.I : ℂ) * (t : ℂ)) + a) - 1‖ ≤
      (2 / (1 - Real.exp (-Real.pi))) * Real.exp (-Real.pi * t) := by
  refine (?_ : _ ≤ (2 / (1 - Real.exp (-Real.pi * t))) * Real.exp (-Real.pi * t)).trans <|
    mul_le_mul_of_nonneg_right (by
      have hInv : (1 / (1 - Real.exp (-Real.pi * t))) ≤ (1 / (1 - Real.exp (-Real.pi))) :=
        one_div_le_one_div_of_le (sub_pos.2 <| Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos]))
          (by linarith [Real.exp_le_exp.2 (show (-Real.pi * t : ℝ) ≤ -Real.pi from by
            nlinarith [Real.pi_pos, ht])])
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hInv (by norm_num : (0 : ℝ) ≤ 2))
      (by positivity)
  simpa using norm_jacobiTheta_sub_one_le (τ := ((Complex.I : ℂ) * (t : ℂ)) + a)
    (by simpa using lt_of_lt_of_le zero_lt_one ht)

public lemma exists_bound_norm_Theta3_resToImagAxis_sub_one_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖Θ₃.resToImagAxis t - 1‖ ≤ C * Real.exp (-Real.pi * t) :=
  ⟨2 / (1 - Real.exp (-Real.pi)), fun t ht => by
    simpa [Function.resToImagAxis, ResToImagAxis, lt_of_lt_of_le zero_lt_one ht,
      Theta3_eq_jacobiTheta] using norm_jacobiTheta_I_mul_add_real_sub_one_le (a := 0) ht⟩

public lemma exists_bound_norm_Theta4_resToImagAxis_sub_one_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖Θ₄.resToImagAxis t - 1‖ ≤ C * Real.exp (-Real.pi * t) :=
  ⟨2 / (1 - Real.exp (-Real.pi)), fun t ht => by
    simpa [Function.resToImagAxis, ResToImagAxis, lt_of_lt_of_le zero_lt_one ht,
      Theta4_eq_jacobiTheta_add_one] using norm_jacobiTheta_I_mul_add_real_sub_one_le (a := 1) ht⟩

public lemma exists_bound_norm_Theta2_resToImagAxis_sub_two_terms_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖Θ₂.resToImagAxis t
          - (2 : ℂ) * (Real.exp (-Real.pi * t / 4) : ℂ)
          - (2 : ℂ) * (Real.exp (-(9 / 4 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(25 / 4 : ℝ) * Real.pi * t) := by
  refine ⟨2 / (1 - Real.exp (-Real.pi)), fun t ht => ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set τ : ℍ := ⟨Complex.I * t, by simp [htpos]⟩
  set f : ℕ → ℂ := fun n ↦ Θ₂_term (n : ℤ) τ
  have hsumZ : Summable (fun n : ℤ ↦ Θ₂_term n τ) := by
    simpa [show (fun n : ℤ ↦ Θ₂_term n τ) = fun n : ℤ ↦
        Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4) *
          jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ) from
      funext fun n => by simp [Θ₂_term_as_jacobiTheta₂_term, mul_assoc]] using
      ((summable_jacobiTheta₂_term_iff (z := (τ : ℂ) / 2) (τ := (τ : ℂ))).2
        (by simpa using τ.im_pos)).mul_left (Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4))
  have hf : Summable f := hsumZ.comp_injective Nat.cast_injective
  have hshift : (∑' n : ℕ, f n) - (f 0 + f 1) = ∑' n : ℕ, f (n + 2) := sub_eq_iff_eq_add.2 <| by
    simpa [Finset.range_add_one, add_comm, add_left_comm, add_assoc] using
      (Summable.sum_add_tsum_nat_add (k := 2) hf).symm
  have hf_eq (c : ℝ) (n : ℕ) (h : Real.pi * Complex.I * (((n : ℂ) + 1 / 2) ^ 2 * (τ : ℂ)) =
      ((c : ℝ) : ℂ)) : f n = (Real.exp c : ℂ) := by
    unfold f Θ₂_term
    rw [Complex.ofReal_exp c]; exact congrArg Complex.exp (by simpa [mul_assoc] using h)
  have hf0 : f 0 = (Real.exp (-Real.pi * t / 4) : ℂ) := hf_eq _ 0 (by
    simp [τ, pow_two, div_eq_mul_inv, mul_assoc, mul_comm]; ring_nf; simp [div_eq_mul_inv])
  have hf1 : f 1 = (Real.exp (-(9 / 4 : ℝ) * Real.pi * t) : ℂ) := hf_eq _ 1 (by
    simp [τ, pow_two, div_eq_mul_inv, mul_assoc, mul_comm]; ring_nf; simp [div_eq_mul_inv])
  rw [show Θ₂.resToImagAxis t - (2 : ℂ) * (Real.exp (-Real.pi * t / 4) : ℂ) -
        (2 : ℂ) * (Real.exp (-(9 / 4 : ℝ) * Real.pi * t) : ℂ) = (2 : ℂ) * ∑' n : ℕ, f (n + 2) by
    rw [← hf0, ← hf1, ← hshift, show Θ₂.resToImagAxis t = (2 : ℂ) * ∑' n : ℕ, f n by
      rw [show Θ₂.resToImagAxis t = Θ₂ τ by
          simp [Function.resToImagAxis, ResToImagAxis, htpos, τ],
        Θ₂, (tsum_nat_add_neg_add_one (f := fun n : ℤ ↦ Θ₂_term n τ) hsumZ).symm,
        ← tsum_mul_left]
      refine tsum_congr fun n => ?_
      rw [show Θ₂_term (-(n + 1 : ℤ)) τ = Θ₂_term (n : ℤ) τ by
        unfold Θ₂_term; grind only, two_mul]]; ring]
  set r : ℝ := Real.exp (-Real.pi)
  have hgeom : HasSum (fun n : ℕ ↦ r ^ n) ((1 - r)⁻¹) :=
    hasSum_geometric_of_lt_one (Real.exp_pos _).le <| by
      simpa [r, Real.exp_lt_one_iff] using (by nlinarith [Real.pi_pos] : (-Real.pi : ℝ) < 0)
  have hterm : ∀ n : ℕ,
      ‖f (n + 2)‖ ≤ Real.exp (-(25 / 4 : ℝ) * Real.pi * t) * (r ^ n) := fun n => by
    have hnorm : ‖f (n + 2)‖ = Real.exp (-Real.pi * (((n : ℝ) + (5 / 2 : ℝ)) ^ 2) * t) := by
      have := norm_Theta2_term_resToImagAxis (n := (n + 2 : ℕ)) (t := t) htpos
      simp [f, τ] at this ⊢; grind only
    have hbase : ((n : ℝ) + (5 / 2 : ℝ)) ^ 2 * t ≥ (25 / 4 : ℝ) * t + n := by
      nlinarith [ht, sq_nonneg ((n : ℝ) - (1 / 2 : ℝ)), mul_le_mul_of_nonneg_right
        (show ((25 / 4 : ℝ) + n) ≤ ((n : ℝ) + (5 / 2 : ℝ)) ^ 2 by nlinarith)
        (by linarith : (0:ℝ) ≤ t)]
    rw [hnorm, show r ^ n = Real.exp (n * (-Real.pi)) by
      simpa [r] using (Real.exp_nat_mul (-Real.pi) n).symm, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [hbase, Real.pi_pos])
  rw [norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) from by simp,
    show (2 / (1 - r)) * Real.exp (-(25 / 4 : ℝ) * Real.pi * t) =
      (2 : ℝ) * (Real.exp (-(25 / 4 : ℝ) * Real.pi * t) * ((1 - r)⁻¹)) from by ring]
  gcongr
  exact tsum_of_norm_bounded (hgeom.mul_left (Real.exp (-(25 / 4 : ℝ) * Real.pi * t))) hterm

private lemma jacobiTheta_tail_bound {τ : ℂ} {t : ℝ} (hτim : τ.im = t) (ht : 1 ≤ t) :
    ‖(2 : ℂ) * ∑' n : ℕ, (fun n : ℕ ↦
        Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ)) (n + 1)‖
      ≤ (2 / (1 - Real.exp (-Real.pi))) * Real.exp (-(4 : ℝ) * Real.pi * t) := by
  set a : ℕ → ℂ := fun n ↦ Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ)
  set r : ℝ := Real.exp (-Real.pi)
  have hgeom : HasSum (fun n : ℕ ↦ r ^ n) ((1 - r)⁻¹) :=
    hasSum_geometric_of_lt_one (Real.exp_pos _).le <| by
      simpa [r, Real.exp_lt_one_iff] using (by nlinarith [Real.pi_pos] : (-Real.pi : ℝ) < 0)
  have hterm : ∀ n : ℕ, ‖a (n + 1)‖ ≤ Real.exp (-(4 : ℝ) * Real.pi * t) * (r ^ n) := fun n => by
    have hnorm : ‖a (n + 1)‖ = Real.exp (-Real.pi * (((n : ℝ) + 2) ^ 2 * t)) := by
      rw [show a (n + 1) = jacobiTheta₂_term (n + 2 : ℤ) (0 : ℂ) τ from by
        simp [a, jacobiTheta₂_term, mul_assoc, mul_left_comm, mul_comm, add_left_comm,
          add_comm, pow_two, one_add_one_eq_two]]
      simpa [norm_jacobiTheta₂_term, hτim, show ((n + 2 : ℤ) : ℝ) = (n : ℝ) + 2 from by
        norm_cast] using by ring_nf
    simpa [hnorm, r, pow_two, mul_assoc] using (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
      (by nlinarith [sq_nonneg (n : ℝ), ht] :
        ((4 : ℝ) * t + (n : ℝ)) ≤ ((n : ℝ) + 2) ^ 2 * t)
      (by nlinarith [Real.pi_pos] : (-Real.pi : ℝ) ≤ 0))).trans_eq (by
      rw [show Real.exp (-Real.pi) ^ n = Real.exp ((n : ℝ) * (-Real.pi)) by
        simpa [mul_comm] using (Real.exp_nat_mul (-Real.pi) n).symm, ← Real.exp_add]; ring_nf)
  rw [norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) from by simp,
    show (2 / (1 - Real.exp (-Real.pi))) * Real.exp (-(4 : ℝ) * Real.pi * t) =
      (2 : ℝ) * (Real.exp (-(4 : ℝ) * Real.pi * t) * ((1 - r)⁻¹)) from by simp [r]; ring]
  gcongr; exact tsum_of_norm_bounded (hgeom.mul_left (Real.exp (-(4 : ℝ) * Real.pi * t))) hterm

private lemma jacobiTheta_setup {τ : ℂ} (hτ : 0 < τ.im) :
    let a : ℕ → ℂ := fun n ↦ Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ)
    jacobiTheta τ = (1 : ℂ) + (2 : ℂ) * ∑' n : ℕ, a n ∧
    (∑' n : ℕ, a n) - a 0 = ∑' n : ℕ, a (n + 1) :=
  ⟨by simpa using (jacobiTheta_eq_tsum_nat (τ := τ) hτ), sub_eq_iff_eq_add.2 <| by
    simpa [Finset.range_one, add_comm, add_left_comm, add_assoc] using
      ((hasSum_nat_jacobiTheta (τ := τ) hτ).summable.sum_add_tsum_nat_add 1).symm⟩

public lemma exists_bound_norm_Theta3_resToImagAxis_sub_one_sub_two_exp_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖Θ₃.resToImagAxis t - (1 : ℂ) - (2 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(4 : ℝ) * Real.pi * t) := by
  refine ⟨2 / (1 - Real.exp (-Real.pi)), fun t ht => ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set τ : ℂ := (Complex.I : ℂ) * t
  set a : ℕ → ℂ := fun n ↦ Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ)
  obtain ⟨hjac, hshift⟩ := jacobiTheta_setup (τ := τ) (by simpa [τ] using htpos)
  have ha0 : a 0 = (Real.exp (-Real.pi * t) : ℂ) := by
    simp [a, τ, pow_two, mul_assoc, mul_left_comm, mul_comm, Complex.ofReal_exp,
      show ∀ z : ℂ, I * (I * z) = -z from fun z => by rw [← mul_assoc, I_mul_I, neg_one_mul]]
  rw [show Θ₃.resToImagAxis t - (1 : ℂ) - (2 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) =
      (2 : ℂ) * ∑' n : ℕ, a (n + 1) from by
    rw [show Θ₃.resToImagAxis t = jacobiTheta τ by
      simp [Function.resToImagAxis, ResToImagAxis, htpos, τ, Theta3_eq_jacobiTheta],
      hjac, ← ha0, ← hshift]; ring]
  exact jacobiTheta_tail_bound (by simp [τ]) ht

public lemma exists_bound_norm_Theta4_resToImagAxis_sub_one_add_two_exp_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖Θ₄.resToImagAxis t - (1 : ℂ) + (2 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(4 : ℝ) * Real.pi * t) := by
  refine ⟨2 / (1 - Real.exp (-Real.pi)), fun t ht => ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set τ : ℂ := (Complex.I : ℂ) * t + 1
  set a : ℕ → ℂ := fun n ↦ Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ)
  obtain ⟨hjac, hshift⟩ := jacobiTheta_setup (τ := τ) (by simpa [τ] using htpos)
  have ha0 : a 0 = - (Real.exp (-Real.pi * t) : ℂ) := by
    rw [show a 0 = Complex.exp (Real.pi * Complex.I * ((Complex.I : ℂ) * t)) *
        Complex.exp (Real.pi * Complex.I) from by
      rw [← Complex.exp_add]; simp [a, pow_two, τ, mul_assoc, mul_left_comm, mul_comm]; ring_nf,
      show (Real.pi * Complex.I * ((Complex.I : ℂ) * t) : ℂ) = ((-Real.pi * t : ℝ) : ℂ) by
        rw [show (Real.pi * Complex.I * ((Complex.I : ℂ) * t) : ℂ) =
          (Real.pi : ℂ) * (Complex.I * Complex.I) * (t : ℂ) by ring, Complex.I_mul_I]; push_cast
        ring, Complex.exp_pi_mul_I]
    simp
  rw [show Θ₄.resToImagAxis t - (1 : ℂ) + (2 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) =
      (2 : ℂ) * ∑' n : ℕ, a (n + 1) from by
    rw [show Θ₄.resToImagAxis t = jacobiTheta τ by
      simp [Function.resToImagAxis, ResToImagAxis, htpos, τ, Theta4_eq_jacobiTheta_add_one],
      hjac, show (Real.exp (-Real.pi * t) : ℂ) = -a 0 by simp [ha0], ← hshift]; ring]
  exact jacobiTheta_tail_bound (by simp [τ]) ht

end

end MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis
