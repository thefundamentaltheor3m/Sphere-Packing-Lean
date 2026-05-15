module
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import SpherePacking.ModularForms.ResToImagAxis
public import SpherePacking.MagicFunction.b.PsiBounds
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Topology.Order.Compact
import SpherePacking.ModularForms.JacobiTheta

/-! Cancellation estimates for `ψI'(it)` and the `bAnotherBase` bracket.

After subtracting `exp (2π t)` and `144`, the remainder decays like `O(exp (-π t))`. The
`bAnotherBase` bracket combines this with the explicit terms and is shown to be uniformly
bounded on `Ioi 0` and integrable against `exp (-π u t)`. -/

namespace MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis

open scoped BigOperators UpperHalfPlane
open Real Complex Filter Topology Set

noncomputable section

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

private lemma norm_pow4_sub_le (x y : ℂ) :
    ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤ 4 * ‖x - y‖ * (‖x‖ + ‖y‖) ^ 3 := by
  have hx : ‖x‖ ≤ ‖x‖ + ‖y‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hy : ‖y‖ ≤ ‖x‖ + ‖y‖ := le_add_of_nonneg_left (norm_nonneg _)
  rw [show x ^ (4 : ℕ) - y ^ (4 : ℕ) =
    (x - y) * (x ^ (3 : ℕ) + x ^ (2 : ℕ) * y + x * y ^ (2 : ℕ) + y ^ (3 : ℕ)) by ring, norm_mul]
  nlinarith [norm_add_le (x ^ (3 : ℕ) + x ^ (2 : ℕ) * y + x * y ^ (2 : ℕ)) (y ^ (3 : ℕ)),
    norm_add_le (x ^ (3 : ℕ) + x ^ (2 : ℕ) * y) (x * y ^ (2 : ℕ)),
    norm_add_le (x ^ (3 : ℕ)) (x ^ (2 : ℕ) * y),
    show ‖x ^ (3 : ℕ)‖ ≤ (‖x‖ + ‖y‖) ^ 3 by
      simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hx 3,
    show ‖y ^ (3 : ℕ)‖ ≤ (‖x‖ + ‖y‖) ^ 3 by
      simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hy 3,
    show ‖x ^ (2 : ℕ) * y‖ ≤ (‖x‖ + ‖y‖) ^ 3 by
      simpa [norm_pow, pow_succ, mul_comm] using
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx 2) hy (norm_nonneg _) (by positivity),
    show ‖x * y ^ (2 : ℕ)‖ ≤ (‖x‖ + ‖y‖) ^ 3 by
      simpa [norm_pow, pow_succ, mul_comm] using
        mul_le_mul hx (pow_le_pow_left₀ (norm_nonneg _) hy 2) (by positivity) (by positivity),
    norm_nonneg (x - y)]

private lemma ofReal_exp_neg_pi_pow_eq (t : ℝ) (N : ℕ) :
    (Real.exp (-Real.pi * t) : ℂ) ^ N = (Real.exp (-(N : ℝ) * Real.pi * t) : ℂ) := by
  rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]; push_cast; ring_nf

private lemma nonneg_of_norm_le_mul_exp {α : Type*} [SeminormedAddCommGroup α] {a : α} {C r : ℝ}
    (h : ‖a‖ ≤ C * Real.exp r) : 0 ≤ C :=
  nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) (Real.exp_pos _)

private lemma norm_le_one_add_of_sub_one (x : ℂ) {C : ℝ} (h : ‖x - 1‖ ≤ C) : ‖x‖ ≤ 1 + C :=
  by linarith [show ‖x‖ ≤ ‖x - 1‖ + 1 by simpa [sub_add_cancel] using norm_add_le (x - 1) (1 : ℂ)]

public lemma exists_bound_norm_H2_resToImagAxis_sub_two_terms_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖H₂.resToImagAxis t - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
          (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(5 : ℝ) * Real.pi * t) := by
  obtain ⟨M, hM⟩ := exists_bound_norm_Theta2_resToImagAxis_Ici_one
  obtain ⟨Cθ, hCθ⟩ := exists_bound_norm_Theta2_resToImagAxis_sub_two_terms_Ici_one
  have hCθ0 : 0 ≤ Cθ := nonneg_of_norm_le_mul_exp (hCθ 1 le_rfl)
  refine ⟨(4 * (M + 4) ^ 3) * Cθ + 176, fun t ht => ?_⟩
  set a : ℂ := (Real.exp (-Real.pi * t / 4) : ℂ)
  set b : ℂ := (Real.exp (-(9 / 4 : ℝ) * Real.pi * t) : ℂ)
  set x : ℂ := Θ₂.resToImagAxis t
  set y : ℂ := (2 : ℂ) * a + (2 : ℂ) * b
  have ha_norm : ‖a‖ = Real.exp (-Real.pi * t / 4) := by
    simp [-Complex.ofReal_exp, a, abs_of_nonneg (Real.exp_pos _).le]
  have hb_norm : ‖b‖ = Real.exp (-(9 / 4 : ℝ) * Real.pi * t) := by
    simp [-Complex.ofReal_exp, b, abs_of_nonneg (Real.exp_pos _).le]
  have hy : ‖y‖ ≤ 4 := by
    have htri := norm_add_le ((2 : ℂ) * a) ((2 : ℂ) * b)
    simp only [norm_mul, Complex.norm_ofNat, ha_norm, hb_norm] at htri
    linarith [Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht] : -Real.pi * t / 4 ≤ 0),
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht] : -(9 / 4 : ℝ) * Real.pi * t ≤ 0)]
  have hpow' : ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤
        (4 * (M + 4) ^ 3) * Cθ * Real.exp (-(5 : ℝ) * Real.pi * t) := by
    refine (norm_pow4_sub_le x y).trans <| (?_ : _ ≤
        4 * (Cθ * Real.exp (-(5 : ℝ) * Real.pi * t)) * (M + 4) ^ 3).trans_eq (by ring)
    gcongr (4 * ?_ * ?_)
    exacts [(show ‖x - y‖ ≤ Cθ * Real.exp (-(25 / 4 : ℝ) * Real.pi * t) by grind only).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])) hCθ0),
      pow_le_pow_left₀ (by positivity) (by linarith [hM t ht]) 3]
  have hy_main : y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) - (64 : ℂ) *
      (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) = (96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ)) +
        (64 : ℂ) * (a * b ^ (3 : ℕ)) + (16 : ℂ) * (b ^ (4 : ℕ)) := by
    grind only [show a ^ (3 : ℕ) * b = (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul,
          ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf,
      show a ^ (4 : ℕ) = (Real.exp (-Real.pi * t) : ℂ) by
        rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]; push_cast; ring_nf]
  have hy_tail : ‖y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
        (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖ ≤
          176 * Real.exp (-(5 : ℝ) * Real.pi * t) := by
    have hab : ‖a ^ (2 : ℕ) * b ^ (2 : ℕ)‖ = Real.exp (-(5 : ℝ) * Real.pi * t) := by
      simpa [norm_mul, norm_pow, ha_norm, hb_norm, ← Real.exp_nat_mul, ← Real.exp_add] using
        congrArg Real.exp (show (2 : ℕ) * (-Real.pi * t / 4) +
          (2 : ℕ) * (-(9 / 4 : ℝ) * Real.pi * t) = -(5 : ℝ) * Real.pi * t by ring)
    have hab3_le : ‖a * b ^ (3 : ℕ)‖ ≤ Real.exp (-(5 : ℝ) * Real.pi * t) :=
      (show ‖a * b ^ (3 : ℕ)‖ = Real.exp (-(7 : ℝ) * Real.pi * t) by
        simpa [norm_mul, norm_pow, ha_norm, hb_norm, ← Real.exp_nat_mul, ← Real.exp_add] using
          congrArg Real.exp (show -Real.pi * t / 4 + (3 : ℕ) * (-(9 / 4 : ℝ) * Real.pi * t) =
            -(7 : ℝ) * Real.pi * t by ring)).le.trans
        (Real.exp_monotone (by nlinarith [Real.pi_pos, ht]))
    have hb4_le : ‖b ^ (4 : ℕ)‖ ≤ Real.exp (-(5 : ℝ) * Real.pi * t) :=
      (show ‖b ^ (4 : ℕ)‖ = Real.exp (-(9 : ℝ) * Real.pi * t) by
        simpa [norm_pow, hb_norm, ← Real.exp_nat_mul] using congrArg Real.exp
          (show (4 : ℕ) * (-(9 / 4 : ℝ) * Real.pi * t) = -(9 : ℝ) * Real.pi * t by ring)).le.trans
        (Real.exp_monotone (by nlinarith [Real.pi_pos, ht]))
    rw [hy_main]
    nlinarith [norm_add_le ((96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ)) +
      (64 : ℂ) * (a * b ^ (3 : ℕ))) ((16 : ℂ) * (b ^ (4 : ℕ))),
      norm_add_le ((96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ))) ((64 : ℂ) * (a * b ^ (3 : ℕ))),
      hab, hab3_le, hb4_le,
      (by simp : ‖(96 : ℂ) * (a ^ (2 : ℕ) * b ^ (2 : ℕ))‖ = 96 * ‖a ^ (2 : ℕ) * b ^ (2 : ℕ)‖),
      (by simp : ‖(64 : ℂ) * (a * b ^ (3 : ℕ))‖ = 64 * ‖a * b ^ (3 : ℕ)‖),
      (by simp : ‖(16 : ℂ) * (b ^ (4 : ℕ))‖ = 16 * ‖b ^ (4 : ℕ)‖)]
  rw [show H₂.resToImagAxis t = x ^ (4 : ℕ) by
    simp [x, H₂, Function.resToImagAxis, ResToImagAxis, lt_of_lt_of_le zero_lt_one ht]]
  linarith [hpow', hy_tail, (show x ^ (4 : ℕ) - y ^ (4 : ℕ) +
    (y ^ (4 : ℕ) - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
      (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)) = x ^ (4 : ℕ) -
    (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
    (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) by ring) ▸ norm_add_le _ _]

private lemma exists_bound_H3_or_H4_aux {Hj Θj : ℝ → ℂ} {σ : ℂ} (hσ : σ = 1 ∨ σ = -1)
    (hHj : ∀ t : ℝ, 0 < t → Hj t = (Θj t) ^ (4 : ℕ)) {C1 C2 : ℝ}
    (hC1 : ∀ t : ℝ, 1 ≤ t → ‖Θj t - 1‖ ≤ C1 * Real.exp (-Real.pi * t))
    (hC2 : ∀ t : ℝ, 1 ≤ t →
      ‖Θj t - 1 - σ * (2 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖ ≤
        C2 * Real.exp (-(4 : ℝ) * Real.pi * t)) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖Hj t - (1 : ℂ) - σ * (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
          (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(3 : ℝ) * Real.pi * t) := by
  have hC20 : 0 ≤ C2 := nonneg_of_norm_le_mul_exp (hC2 1 le_rfl)
  refine ⟨(4 * (1 + C1 + 3) ^ 3) * C2 + 48, fun t ht ↦ ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set q' : ℂ := (Real.exp (-Real.pi * t) : ℂ)
  set x : ℂ := Θj t
  set y : ℂ := (1 : ℂ) + σ * (2 : ℂ) * q'
  have hq : ‖q'‖ ≤ 1 := by
    simpa [q', abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp] using
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht0.le] : (-Real.pi * t) ≤ 0)
  have hx : ‖x‖ ≤ 1 + C1 := norm_le_one_add_of_sub_one x <| (hC1 t ht).trans <| by
    simpa using mul_le_of_le_one_right (nonneg_of_norm_le_mul_exp (hC1 1 le_rfl))
      (Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht0.le]))
  have hσ_norm : ‖σ‖ = 1 := by rcases hσ with rfl | rfl <;> simp
  have hy : ‖y‖ ≤ 3 := by
    have h := norm_add_le (1 : ℂ) (σ * (2 : ℂ) * q'); simp [hσ_norm] at h; linarith
  have hxy : ‖x - y‖ ≤ C2 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
    simpa [x, y, q', sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using hC2 t ht
  have hpow' : ‖x ^ (4 : ℕ) - y ^ (4 : ℕ)‖ ≤
        (4 * (1 + C1 + 3) ^ 3) * C2 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
    refine (norm_pow4_sub_le x y).trans <| (?_ : _ ≤
        4 * (C2 * Real.exp (-(3 : ℝ) * Real.pi * t)) * (1 + C1 + 3) ^ 3).trans_eq (by ring)
    gcongr (4 * ?_ * ?_)
    exacts [hxy.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])) hC20),
      pow_le_pow_left₀ (by positivity) (by linarith [hx, hy]) 3]
  have hy4 : ‖y ^ (4 : ℕ) - (1 : ℂ) - σ * (8 : ℂ) * q' - (24 : ℂ) * (q' ^ (2 : ℕ))‖ ≤
        48 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
    have hq3' : ‖q' ^ (3 : ℕ)‖ = Real.exp (-(3 : ℝ) * Real.pi * t) := by
      rw [show (q' ^ (3 : ℕ) : ℂ) = (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) by
        simpa [q'] using ofReal_exp_neg_pi_pow_eq t 3,
        Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have htri := norm_add_le ((32 : ℂ) * σ ^ 3 * (q' ^ (3 : ℕ))) ((16 : ℂ) * (q' ^ (4 : ℕ)))
    simp only [norm_mul, Complex.norm_ofNat,
      show ‖σ ^ 3‖ = 1 by rw [norm_pow, hσ_norm]; ring, mul_one] at htri
    rw [show y ^ (4 : ℕ) - (1 : ℂ) - σ * (8 : ℂ) * q' - (24 : ℂ) * (q' ^ (2 : ℕ)) =
      (32 : ℂ) * σ ^ 3 * (q' ^ (3 : ℕ)) + (16 : ℂ) * (q' ^ (4 : ℕ)) by
      rcases hσ with rfl | rfl <;> simp [y] <;> ring]
    nlinarith [htri, show ‖q' ^ (4 : ℕ)‖ ≤ ‖q' ^ (3 : ℕ)‖ from by
      simpa [pow_succ, norm_mul] using mul_le_mul_of_nonneg_left hq (norm_nonneg (q' ^ (3 : ℕ))),
      hq3', norm_nonneg (q' ^ (3 : ℕ))]
  rw [hHj t ht0, show (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ) =
    (Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ) from (ofReal_exp_neg_pi_pow_eq t 2).symm]
  linarith [hpow', hy4, (show x ^ (4 : ℕ) - y ^ (4 : ℕ) + (y ^ (4 : ℕ) - (1 : ℂ) -
    σ * (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
    (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ))) = x ^ (4 : ℕ) - (1 : ℂ) -
    σ * (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
    (24 : ℂ) * ((Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ)) by ring) ▸ norm_add_le _ _]

lemma exists_bound_norm_H3_resToImagAxis_sub_two_terms_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖H₃.resToImagAxis t - (1 : ℂ) - (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
          (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(3 : ℝ) * Real.pi * t) := by
  obtain ⟨C1, hC1⟩ := exists_bound_norm_Theta3_resToImagAxis_sub_one_Ici_one
  obtain ⟨C2, hC2⟩ := exists_bound_norm_Theta3_resToImagAxis_sub_one_sub_two_exp_Ici_one
  exact (exists_bound_H3_or_H4_aux (Hj := H₃.resToImagAxis) (Θj := Θ₃.resToImagAxis) (σ := 1)
    (.inl rfl) (fun t ht0 => by simp [H₃, Function.resToImagAxis, ResToImagAxis, ht0]) hC1
    fun t ht => by simpa [sub_eq_add_neg, mul_assoc] using hC2 t ht).imp fun _ hC t ht => by
    simpa [one_mul] using hC t ht

public lemma exists_bound_norm_H4_resToImagAxis_sub_two_terms_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
          (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(3 : ℝ) * Real.pi * t) := by
  obtain ⟨C1, hC1⟩ := exists_bound_norm_Theta4_resToImagAxis_sub_one_Ici_one
  obtain ⟨C2, hC2⟩ := exists_bound_norm_Theta4_resToImagAxis_sub_one_add_two_exp_Ici_one
  exact (exists_bound_H3_or_H4_aux (Hj := H₄.resToImagAxis) (Θj := Θ₄.resToImagAxis) (σ := -1)
    (.inr rfl) (fun t ht0 => by simp [H₄, Function.resToImagAxis, ResToImagAxis, ht0]) hC1
    fun t ht => by simpa [sub_eq_add_neg, mul_assoc, add_left_comm, add_comm] using hC2 t ht).imp
    fun _ hC t ht => by simpa [neg_mul, sub_eq_add_neg] using hC t ht

public lemma exists_bound_norm_H3_add_H4_resToImagAxis_sub_two_sub_main_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖(H₃.resToImagAxis t + H₄.resToImagAxis t) - (2 : ℂ) -
          (48 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ C * Real.exp (-(3 : ℝ) * Real.pi * t) := by
  obtain ⟨C3, hC3⟩ := exists_bound_norm_H3_resToImagAxis_sub_two_terms_Ici_one
  obtain ⟨C4, hC4⟩ := exists_bound_norm_H4_resToImagAxis_sub_two_terms_Ici_one
  refine ⟨C3 + C4, fun t ht => ?_⟩
  set A : ℂ := H₃.resToImagAxis t - 1 - 8 * (Real.exp (-Real.pi * t) : ℂ) -
    24 * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)
  set B : ℂ := H₄.resToImagAxis t - 1 + 8 * (Real.exp (-Real.pi * t) : ℂ) -
    24 * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)
  linarith [hC3 t ht, hC4 t ht, (show A + B = (H₃.resToImagAxis t + H₄.resToImagAxis t) - 2 -
    48 * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ) by simp [A, B]; ring) ▸ norm_add_le A B]

public lemma exists_bound_norm_inv_H3_sq_sub_one_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖((H₃.resToImagAxis t) ^ (2 : ℕ))⁻¹ - (1 : ℂ)‖ ≤ C * Real.exp (-Real.pi * t) := by
  obtain ⟨C3, hC3⟩ := exists_bound_norm_H3_resToImagAxis_sub_two_terms_Ici_one
  let C0 : ℝ := C3 + 32
  have hC30 : 0 ≤ C3 := nonneg_of_norm_le_mul_exp (hC3 1 le_rfl)
  have hsub1 : ∀ t : ℝ, 1 ≤ t → ‖H₃.resToImagAxis t - (1 : ℂ)‖ ≤ C0 * Real.exp (-Real.pi * t) :=
    fun t ht => by
      set u : ℂ := (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
      set v : ℂ := (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)
      nlinarith [norm_add_le u v, hC3 t ht,
        (by simpa using norm_add_le (H₃.resToImagAxis t - (1 : ℂ) - u - v) (u + v) :
          ‖H₃.resToImagAxis t - (1 : ℂ)‖ ≤ ‖H₃.resToImagAxis t - 1 - u - v‖ + ‖u + v‖),
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (by nlinarith [Real.pi_pos, ht] : -(3 : ℝ) * Real.pi * t ≤ -Real.pi * t)) hC30,
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht] :
          -(2 : ℝ) * Real.pi * t ≤ -Real.pi * t),
        (by simp [u, abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp] :
          ‖u‖ = 8 * Real.exp (-Real.pi * t)),
        (by simp [v, abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp] :
          ‖v‖ = 24 * Real.exp (-(2 : ℝ) * Real.pi * t))]
  have hnorm_H3_ge_one : ∀ t : ℝ, 1 ≤ t → (1 : ℝ) ≤ ‖H₃.resToImagAxis t‖ := fun t ht => by
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    set τ : ℂ := (Complex.I : ℂ) * (t : ℂ)
    let f : ℕ → ℝ := fun n => Real.exp (-Real.pi * (((n : ℝ) + 1) ^ 2) * t)
    have hterm : ∀ n : ℕ, cexp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ) = (f n : ℂ) :=
      fun n => by simp [f, show (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ : ℂ) =
        (-(Real.pi * (((n : ℝ) + 1) ^ 2) * t) : ℂ) by
        rw [show τ = Complex.I * (t : ℂ) from rfl]; push_cast
        linear_combination (Complex.I_mul_I) * (Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * (t : ℂ)]
    have hnormΘ₃ : (1 : ℝ) ≤ ‖Θ₃.resToImagAxis t‖ := by
      rw [show Θ₃.resToImagAxis t = jacobiTheta τ by
        simp [Function.resToImagAxis, ResToImagAxis, ht0, Theta3_eq_jacobiTheta, τ],
        show jacobiTheta τ = ((1 + 2 * (∑' n : ℕ, f n) : ℝ) : ℂ) by
          rw [jacobiTheta_eq_tsum_nat (τ := τ) (by simpa [τ] using ht0),
            show (∑' n : ℕ, cexp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ)) =
              (↑(∑' n : ℕ, f n) : ℂ) by simp [Complex.ofReal_tsum, hterm]]
          push_cast; ring, Complex.norm_of_nonneg (by positivity)]
      linarith [(tsum_nonneg fun n => by positivity : 0 ≤ ∑' n : ℕ, f n)]
    simpa [show ‖ResToImagAxis H₃ t‖ = ‖ResToImagAxis Θ₃ t‖ ^ (4 : ℕ) by
      simp [H₃, ResToImagAxis, ht0, norm_pow]] using
      pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1) hnormΘ₃ 4
  refine ⟨C0 * (C0 + 2), fun t ht => ?_⟩
  set x : ℂ := H₃.resToImagAxis t
  have hx_inv : ‖(x ^ (2 : ℕ))⁻¹‖ ≤ 1 := by
    simpa [norm_inv, norm_pow] using inv_le_one_of_one_le₀ (one_le_pow₀ (hnorm_H3_ge_one t ht))
  have hx_le : ‖x‖ + 1 ≤ C0 + 2 := by
    nlinarith [norm_le_one_add_of_sub_one x (hsub1 t ht),
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht] : -Real.pi * t ≤ 0)]
  have hx2sub : ‖x ^ (2 : ℕ) - (1 : ℂ)‖ ≤ (C0 + 2) * (C0 * Real.exp (-Real.pi * t)) := by
    rw [show x ^ (2 : ℕ) - (1 : ℂ) = (x - 1) * (x + 1) by ring, norm_mul, mul_comm]
    gcongr ?_ * ?_
    exacts [((by simpa using norm_add_le x (1 : ℂ)) : ‖x + 1‖ ≤ ‖x‖ + 1).trans hx_le, hsub1 t ht]
  have hinv_le : ‖(x ^ (2 : ℕ))⁻¹ - (1 : ℂ)‖ ≤ ‖x ^ (2 : ℕ) - (1 : ℂ)‖ := by
    have : x ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le zero_lt_one (hnorm_H3_ge_one t ht))
    rw [show (x ^ (2 : ℕ))⁻¹ - (1 : ℂ) = ((1 : ℂ) - x ^ (2 : ℕ)) * (x ^ (2 : ℕ))⁻¹ by field_simp,
      norm_mul, norm_sub_rev]
    simpa using mul_le_mul_of_nonneg_left hx_inv (norm_nonneg (x ^ (2 : ℕ) - (1 : ℂ)))
  simpa [x, mul_assoc, mul_left_comm, mul_comm] using hinv_le.trans hx2sub

private lemma theta2_norm_ge_two_exp_quarter (t : ℝ) (ht : 0 < t) :
    (2 : ℝ) * Real.exp (-Real.pi * t / 4) ≤ ‖Θ₂.resToImagAxis t‖ := by
  set τ : ℍ := ⟨(Complex.I : ℂ) * t, by simp [ht]⟩
  let g : ℤ → ℝ := fun n => Real.exp (-Real.pi * (((n : ℝ) + (1 / 2 : ℝ)) ^ 2) * t)
  have hterm : ∀ n : ℤ, Θ₂_term n τ = (g n : ℂ) := fun n => by
    set r : ℝ := (n : ℝ) + (2⁻¹ : ℝ)
    have hr : (n + (2⁻¹ : ℂ)) = (r : ℂ) := by apply Complex.ext <;> simp [r]
    have harg : (π * I * (n + (2⁻¹ : ℂ)) ^ 2 * ((Complex.I : ℂ) * t) : ℂ) =
        (-(Real.pi * (r ^ 2) * t) : ℂ) := by
      grind only [show (n + (2⁻¹ : ℂ)) ^ 2 = ((r ^ 2 : ℝ) : ℂ) by simp_all,
        show (I : ℂ) * ((I : ℂ) * (t : ℂ)) = -(t : ℂ) by
          rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]]
    simpa [Θ₂_term, one_div, r, pow_two, mul_assoc, mul_left_comm, mul_comm, g, τ] using
      show Θ₂_term n τ = (Real.exp (-(Real.pi * (r ^ 2) * t)) : ℂ) from by
        simp [Θ₂_term, one_div, harg, τ]
  have hsum : Summable (fun n : ℤ => Θ₂_term n τ) := by
    simpa [Θ₂_term_as_jacobiTheta₂_term, mul_assoc] using
      ((summable_jacobiTheta₂_term_iff (z := (τ : ℂ) / 2) (τ := (τ : ℂ))).2
        (by simpa using τ.im_pos)).mul_left (cexp (Real.pi * Complex.I * (τ : ℂ) / 4))
  have hnonneg : ∀ n : ℤ, 0 ≤ g n := fun _ => by positivity
  have hfin : (∑ n ∈ ({0, (-1 : ℤ)} : Finset ℤ), g n) ≤ ∑' n : ℤ, g n := by
    simpa using ((Complex.summable_ofReal).1 (by simpa [hterm] using hsum)).sum_le_tsum
      ({0, (-1 : ℤ)} : Finset ℤ) (fun n _ ↦ hnonneg n)
  have hsum2 : (∑ n ∈ ({0, (-1 : ℤ)} : Finset ℤ), g n) = 2 * Real.exp (-Real.pi * t / 4) := by
    simp [Finset.sum_insert, g, pow_two]; ring_nf
  simpa [Function.resToImagAxis, show ‖ResToImagAxis Θ₂ t‖ = (∑' n : ℤ, g n) from by
    simp [ResToImagAxis, ht, τ, show Θ₂ τ = (↑(∑' n : ℤ, g n) : ℂ) from by
      simp [Θ₂, hterm, g, Complex.ofReal_tsum], abs_of_nonneg (tsum_nonneg hnonneg)]] using
    (by simpa [hsum2] using hfin : 2 * Real.exp (-Real.pi * t / 4) ≤ (∑' n : ℤ, g n))

lemma H2_norm_pow_two_ge (t : ℝ) (ht0 : 0 < t) :
    (256 : ℝ) * Real.exp (-(2 : ℝ) * Real.pi * t) ≤ ‖H₂.resToImagAxis t‖ ^ (2 : ℕ) := by
  have hx_ge : (16 : ℝ) * Real.exp (-Real.pi * t) ≤ ‖H₂.resToImagAxis t‖ := by
    rw [show ‖H₂.resToImagAxis t‖ = ‖Θ₂.resToImagAxis t‖ ^ (4 : ℕ) from by
      simp [H₂, Function.resToImagAxis, ResToImagAxis, ht0, norm_pow],
      show (16 : ℝ) * Real.exp (-Real.pi * t) = (2 * Real.exp (-Real.pi * t / 4)) ^ (4 : ℕ) by
        rw [mul_pow, ← Real.exp_nat_mul]; ring_nf]
    exact pow_le_pow_left₀ (by positivity) (theta2_norm_ge_two_exp_quarter t ht0) 4
  linarith [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 16 * Real.exp (-Real.pi * t)) hx_ge 2,
    show (16 * Real.exp (-Real.pi * t)) ^ (2 : ℕ) = (256 : ℝ) * Real.exp (-(2 : ℝ) * Real.pi * t)
      by rw [mul_pow, ← Real.exp_nat_mul]; ring_nf]

private lemma bound_w_inv_sub_one_sub (t u C0 : ℝ) (w : ℂ)
    (hw_norm_ge : (1 : ℝ) ≤ ‖w‖) (hw_inv : ‖w⁻¹‖ ≤ 1)
    (hw_tail : ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ ≤ C0 * Real.exp (-(4 : ℝ) * Real.pi * t))
    (hw_one : ‖w - (1 : ℂ)‖ ≤ (8 + C0) * Real.exp (-(2 : ℝ) * Real.pi * t)) :
    ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ ≤ ((8 + C0) ^ 2 + C0) * Real.exp (-(4 : ℝ) * Real.pi * t) := by
  have hid : w⁻¹ - (2 - w) = (w - 1) ^ (2 : ℕ) * w⁻¹ := by
    have : w ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans_le hw_norm_ge); field_simp; ring
  nlinarith [show ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ ≤
      ‖w⁻¹ - (2 - w)‖ + ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ by
        rw [show w⁻¹ - (1 - ((8 * u : ℝ) : ℂ)) =
          (w⁻¹ - (2 - w)) - (w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)) from by ring]; exact norm_sub_le _ _,
    hw_tail, calc ‖w⁻¹ - (2 - w)‖
        = ‖w - 1‖ ^ (2 : ℕ) * ‖w⁻¹‖ := by simp [hid, norm_pow]
      _ ≤ ‖w - 1‖ ^ (2 : ℕ) := by
          simpa using mul_le_mul_of_nonneg_left hw_inv (by positivity : 0 ≤ ‖w - 1‖ ^ (2 : ℕ))
      _ ≤ ((8 + C0) * Real.exp (-(2 : ℝ) * Real.pi * t)) ^ (2 : ℕ) :=
          pow_le_pow_left₀ (norm_nonneg _) hw_one 2
      _ = (8 + C0) ^ 2 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
          rw [mul_pow, ← Real.exp_nat_mul]; ring_nf]

private lemma hw_tail_bound (t : ℝ) (ht : 1 ≤ t) (CH2 : ℝ)
    (hx_err :
      ‖H₂.resToImagAxis t - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) - (64 : ℂ) *
          (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
        ≤ CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) :
    ‖(((Real.exp (2 * Real.pi * t) / 256 : ℝ) : ℂ) * (H₂.resToImagAxis t) ^ (2 : ℕ))
          - (1 : ℂ) - ((8 * Real.exp (-(2 : ℝ) * Real.pi * t) : ℝ) : ℂ)‖
        ≤ (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256) * Real.exp (-(4 : ℝ) * Real.pi * t) := by
  set e : ℝ := Real.exp (2 * Real.pi * t)
  set u : ℝ := Real.exp (-(2 : ℝ) * Real.pi * t)
  set A : ℂ := ((e / 256 : ℝ) : ℂ)
  set x : ℂ := H₂.resToImagAxis t
  set w : ℂ := A * (x ^ (2 : ℕ))
  have heu : e * u = 1 := by simp [e, u, ← Real.exp_add]
  set C0 : ℝ := 16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256
  have hw_tail :
      ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ ≤ C0 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
    set main : ℂ :=
      (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) + (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)
    set r : ℂ := x - main
    have hr : ‖r‖ ≤ CH2 * Real.exp (-(5 : ℝ) * Real.pi * t) := by
      simpa [r, main, x, sub_eq_add_neg, add_assoc, add_comm] using hx_err
    have hmain_norm : ‖main‖ ≤ 80 * Real.exp (-Real.pi * t) := by
      nlinarith [show ‖main‖ ≤
          16 * Real.exp (-Real.pi * t) + 64 * Real.exp (-(3 : ℝ) * Real.pi * t) by
        simpa [main, abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp] using
          norm_add_le ((16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ))
            ((64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)),
        Real.exp_le_exp.mpr (show (-(3 : ℝ) * Real.pi * t) ≤ -Real.pi * t by
          nlinarith [Real.pi_pos, ht])]
    have hmain_sq :
        ‖main ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)‖ ≤
          (4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t) := by
      rw [show main ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ) =
        (4096 : ℂ) * (Real.exp (-(6 : ℝ) * Real.pi * t) : ℂ) from by
        grind only [show (Real.exp (-Real.pi * t) : ℂ) ^ (2 : ℕ) = (u : ℂ) by
            exact_mod_cast show Real.exp (-Real.pi * t) ^ (2 : ℕ) = u by
              simp only [u, ← Real.exp_nat_mul]; ring_nf,
          show (Real.exp (-Real.pi * t) : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) =
              ((u ^ (2 : ℕ) : ℝ) : ℂ) by
            rw [show (u ^ (2 : ℕ) : ℝ) = Real.exp (-(4 : ℝ) * Real.pi * t) by
              simp only [u, ← Real.exp_nat_mul]; ring_nf]
            exact_mod_cast show Real.exp (-Real.pi * t) * Real.exp (-(3 : ℝ) * Real.pi * t)
              = Real.exp (-(4 : ℝ) * Real.pi * t) by rw [← Real.exp_add]; ring_nf,
          show (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ) ^ (2 : ℕ) =
              (Real.exp (-(6 : ℝ) * Real.pi * t) : ℂ) by
            exact_mod_cast show Real.exp (-(3 : ℝ) * Real.pi * t) ^ (2 : ℕ) =
              Real.exp (-(6 : ℝ) * Real.pi * t) by rw [← Real.exp_nat_mul]; ring_nf]]
      simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
    have hsq : ‖x ^ (2 : ℕ) - main ^ (2 : ℕ)‖ ≤
          (160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) +
            (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2 :=
      calc ‖x ^ (2 : ℕ) - main ^ (2 : ℕ)‖ = ‖r‖ * ‖x + main‖ := by
            rw [show x ^ 2 - main ^ 2 = (x - main) * (x + main) from by ring, norm_mul]
        _ ≤ ‖r‖ * ((160 * Real.exp (-Real.pi * t)) + ‖r‖) := by
            gcongr
            nlinarith [norm_add_le x main, norm_le_norm_add_norm_sub' x main, hmain_norm]
        _ = (160 * Real.exp (-Real.pi * t)) * ‖r‖ + ‖r‖ ^ 2 := by ring
        _ ≤ (160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) +
              (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2 := by gcongr
    have he256 : 0 ≤ e / 256 := by positivity
    have hA_norm : ‖A‖ = e / 256 := by
      simpa [A, abs_of_nonneg he256] using (RCLike.norm_ofReal (K := ℂ) (e / 256))
    have hw_rewrite : w - (1 : ℂ) - ((8 * u : ℝ) : ℂ) =
        A * (x ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)) := by
      have h256' : A * ((256 * u : ℝ) : ℂ) = (1 : ℂ) := by
        simp only [A]; exact_mod_cast congrArg (fun r : ℝ ↦ (r : ℂ))
          (show (e / 256) * (256 * u) = 1 by linear_combination heu)
      have h2048' : A * ((2048 * (u ^ (2 : ℕ) : ℝ) : ℝ) : ℂ) = ((8 * u : ℝ) : ℂ) := by
        simp only [A]; exact_mod_cast congrArg (fun r : ℝ ↦ (r : ℂ))
          (show (e / 256) * (2048 * (u ^ (2 : ℕ) : ℝ)) = 8 * u by
            rw [show (u ^ (2 : ℕ) : ℝ) = u * u from by ring]; linear_combination 8 * u * heu)
      rw [show A * (x ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)) =
        A * (x ^ (2 : ℕ)) - A * ((256 * u : ℝ) : ℂ) - A * ((2048 * (u ^ (2 : ℕ) : ℝ) : ℝ) : ℂ)
        from by push_cast; ring, h256', h2048']
    have hbr : ‖x ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)‖
        ≤ (4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t) +
            (160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) +
            (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2 := by
      have := norm_add_le (x ^ (2 : ℕ) - main ^ (2 : ℕ))
        (main ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ))
      grind only
    have he6 : e * Real.exp (-(6 : ℝ) * Real.pi * t) = Real.exp (-(4 : ℝ) * Real.pi * t) := by
      simp only [e, ← Real.exp_add]; ring_nf
    have he15 : e * (Real.exp (-Real.pi * t) * Real.exp (-(5 : ℝ) * Real.pi * t)) =
        Real.exp (-(4 : ℝ) * Real.pi * t) := by
      simp only [e, ← Real.exp_add]; ring_nf
    have h1 : (e / 256) * ((4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t)) =
        16 * Real.exp (-(4 : ℝ) * Real.pi * t) := by linear_combination 16 * he6
    have h2 : (e / 256) *
        ((160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t))) =
        (160 / 256) * CH2 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
      linear_combination (160 / 256 : ℝ) * CH2 * he15
    have h3 : (e / 256) * ((CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2) ≤
        (CH2 ^ 2) / 256 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
      nlinarith [show e * (Real.exp (-(5 : ℝ) * Real.pi * t)) ^ (2 : ℕ) =
          Real.exp (-(8 : ℝ) * Real.pi * t) by
        simp only [e, ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf,
        Real.exp_le_exp.mpr (show -(8 : ℝ) * Real.pi * t ≤ -(4 : ℝ) * Real.pi * t by
          nlinarith [Real.pi_pos, ht]), sq_nonneg CH2]
    calc
      ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖
          = ‖A‖ * ‖x ^ (2 : ℕ) - (256 : ℂ) * (u : ℂ) - (2048 : ℂ) * ((u ^ (2 : ℕ) : ℝ) : ℂ)‖ := by
            rw [hw_rewrite]; simp
      _ ≤ (e / 256) *
            ((4096 : ℝ) * Real.exp (-(6 : ℝ) * Real.pi * t) +
              (160 * Real.exp (-Real.pi * t)) * (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) +
              (CH2 * Real.exp (-(5 : ℝ) * Real.pi * t)) ^ 2) := by
            rw [hA_norm]; exact mul_le_mul_of_nonneg_left hbr he256
      _ ≤ C0 * Real.exp (-(4 : ℝ) * Real.pi * t) := by grind only
  simpa [w, A, x, e, u, C0] using hw_tail

public lemma exists_bound_norm_inv_H2_sq_sub_exp_add_const_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖((H₂.resToImagAxis t) ^ (2 : ℕ))⁻¹
          - ((Real.exp (2 * Real.pi * t) / 256 : ℝ) : ℂ)
          + ((1 / 32 : ℝ) : ℂ)‖
        ≤ C * Real.exp (-(2 : ℝ) * Real.pi * t) := by
  rcases exists_bound_norm_H2_resToImagAxis_sub_two_terms_Ici_one with ⟨CH2, hH2⟩
  refine ⟨(256 * ((8 + (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256)) ^ 2 +
        (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256))) , fun t ht => ?_⟩
  set e : ℝ := Real.exp (2 * Real.pi * t)
  set u : ℝ := Real.exp (-(2 : ℝ) * Real.pi * t)
  set A : ℂ := ((e / 256 : ℝ) : ℂ)
  set x : ℂ := H₂.resToImagAxis t
  set w : ℂ := A * (x ^ (2 : ℕ))
  have he256 : 0 ≤ e / 256 := by positivity
  have hA_norm : ‖A‖ = e / 256 := by
    simpa [A, abs_of_nonneg he256] using (RCLike.norm_ofReal (K := ℂ) (e / 256))
  have hCH2 : 0 ≤ CH2 :=
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hH2 1 le_rfl)) (Real.exp_pos _)
  set C0 : ℝ := 16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256
  have heu : e * u = 1 := by simp [e, u, ← Real.exp_add]
  have hmain_id :
      ((x ^ (2 : ℕ))⁻¹ - A + ((1 / 32 : ℝ) : ℂ)) = A * (w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))) := by
    have hA0 : A ≠ 0 := ofReal_ne_zero.mpr (div_ne_zero (ne_of_gt (Real.exp_pos _)) (by norm_num))
    have hA8u : A * ((8 * u : ℝ) : ℂ) = ((1 / 32 : ℝ) : ℂ) := by
      simpa [A, Complex.ofReal_mul, mul_assoc, mul_left_comm, mul_comm] using
        congrArg (fun r : ℝ ↦ (r : ℂ))
          (show (e / 256) * (8 * u) = (1 / 32 : ℝ) by linear_combination (8 / 256 : ℝ) * heu)
    linear_combination -(by simp [w, mul_inv_rev, hA0, mul_comm, mul_left_comm] :
      A * w⁻¹ = (x ^ (2 : ℕ))⁻¹) - hA8u
  have hw_tail : ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ ≤ C0 * Real.exp (-(4 : ℝ) * Real.pi * t) := by
    simpa [w, A, x, e, u, C0] using hw_tail_bound t ht CH2 (by simpa [x] using hH2 t ht)
  have hw_one : ‖w - (1 : ℂ)‖ ≤ (8 + C0) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
    have hu0 : (0 : ℝ) ≤ u := (Real.exp_pos _).le
    have hu1 : u ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht])
    have hw_tail' : ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ ≤ C0 * (u ^ (2 : ℕ)) := by
      simpa [show u ^ (2 : ℕ) = Real.exp (-(4 : ℝ) * Real.pi * t) by
        simp only [u, ← Real.exp_nat_mul]; ring_nf] using hw_tail
    refine (show ‖w - (1 : ℂ)‖ ≤ (8 + |C0|) * u from ?_).trans <| by
      simp [u, abs_of_nonneg (show (0:ℝ) ≤ C0 by positivity)]
    linarith [show ‖w - 1‖ ≤ ‖w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)‖ + ‖((8 * u : ℝ) : ℂ)‖ by
      simpa [show (w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)) + ((8 * u : ℝ) : ℂ) = w - 1 from by ring]
        using norm_add_le (w - (1 : ℂ) - ((8 * u : ℝ) : ℂ)) ((8 * u : ℝ) : ℂ),
      hw_tail'.trans <| (mul_le_mul_of_nonneg_right (le_abs_self C0) (pow_nonneg hu0 _)).trans
        (mul_le_mul_of_nonneg_left (by simpa [pow_two] using mul_le_of_le_one_right hu0 hu1)
          (abs_nonneg C0)),
      show ‖((8 * u : ℝ) : ℂ)‖ = 8 * u from by
        simpa [RCLike.norm_ofReal, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 * u)]]
  have hw_norm_ge : (1 : ℝ) ≤ ‖w‖ := by
    rw [show ‖w‖ = (e / 256) * ‖x‖ ^ (2 : ℕ) from by simp [w, hA_norm, norm_pow]]
    linarith [mul_le_mul_of_nonneg_left (show (256 : ℝ) * u ≤ ‖x‖ ^ (2 : ℕ) by
        simpa [x, u] using H2_norm_pow_two_ge t (lt_of_lt_of_le zero_lt_one ht)) he256,
      show (e / 256) * ((256 : ℝ) * u) = 1 from by linear_combination heu]
  have hdiff : ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ ≤
      ((8 + C0) ^ 2 + C0) * Real.exp (-(4 : ℝ) * Real.pi * t) :=
    bound_w_inv_sub_one_sub t u C0 w hw_norm_ge
      (norm_inv w ▸ inv_le_one_of_one_le₀ hw_norm_ge) hw_tail hw_one
  calc ‖((H₂.resToImagAxis t) ^ (2 : ℕ))⁻¹
          - ((Real.exp (2 * Real.pi * t) / 256 : ℝ) : ℂ)
          + ((1 / 32 : ℝ) : ℂ)‖
      = ‖A‖ * ‖w⁻¹ - (1 - ((8 * u : ℝ) : ℂ))‖ := by rw [hmain_id, norm_mul]
    _ ≤ (e / 256) * (((8 + C0) ^ 2 + C0) * Real.exp (-(4 : ℝ) * Real.pi * t)) := by
        rw [hA_norm]; exact mul_le_mul_of_nonneg_left hdiff he256
    _ = (1 / 256 : ℝ) * ((8 + C0) ^ 2 + C0) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
        have he4 : e * Real.exp (-(4 : ℝ) * Real.pi * t) =
            Real.exp (-(2 : ℝ) * Real.pi * t) := by simp only [e, ← Real.exp_add]; ring_nf
        linear_combination (((8 + C0) ^ 2 + C0) / 256 : ℝ) * he4
    _ ≤ (256 * ((8 + (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256)) ^ 2 +
          (16 + (160 / 256) * CH2 + (CH2 ^ 2) / 256))) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
        gcongr; nlinarith [show (0:ℝ) ≤ (8 + C0) ^ 2 + C0 from by positivity, show C0 = 16 +
          (160 / 256) * CH2 + (CH2 ^ 2) / 256 from rfl]

end

end MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis

namespace MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation

open scoped BigOperators UpperHalfPlane

open MeasureTheory Real Complex Filter Topology

noncomputable section

open MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis

/-- For `c ≥ 1` and `t ≥ 0`, `exp (-c π t) ≤ exp (-π t)`. -/
private lemma exp_neg_scaled_pi_le (c : ℝ) (hc : 1 ≤ c) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-c * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
  Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.mpr hc) ht])

/-- If `A = err + main`, `‖err‖ ≤ Cerr * exp(-k π t)` with `k ≥ 1`, and
`‖main‖ ≤ Cm * exp(-π t)`, then `‖A‖ ≤ (Cerr + Cm) * exp(-π t)`. -/
private lemma norm_le_err_plus_main {A err main : ℂ} (hdec : A = err + main)
    {Cerr k Cm : ℝ} (hCerr : 0 ≤ Cerr) (hk : 1 ≤ k) {t : ℝ} (ht : 0 ≤ t)
    (herr : ‖err‖ ≤ Cerr * Real.exp (-k * Real.pi * t))
    (hmain : ‖main‖ ≤ Cm * Real.exp (-Real.pi * t)) :
    ‖A‖ ≤ (Cerr + Cm) * Real.exp (-Real.pi * t) :=
  hdec ▸ (norm_add_le _ _).trans (by
    nlinarith [mul_le_mul_of_nonneg_left (exp_neg_scaled_pi_le k hk ht) hCerr, herr, hmain])

/-- Bound `‖A·exp(-π t) + B·exp(-k π t)‖ ≤ M·exp(-π t)` when `‖A‖+‖B‖ ≤ M, k ≥ 1, t ≥ 0`. -/
private lemma norm_two_exp_le_const {A B : ℂ} {k M : ℝ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 ≤ t)
    (hAB : ‖A‖ + ‖B‖ ≤ M) :
    ‖A * (Real.exp (-Real.pi * t) : ℂ) + B * (Real.exp (-k * Real.pi * t) : ℂ)‖ ≤
      M * Real.exp (-Real.pi * t) := by
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  nlinarith [mul_le_mul_of_nonneg_left (exp_neg_scaled_pi_le k hk ht) (norm_nonneg B), hAB,
    Real.exp_pos (-Real.pi * t), norm_nonneg A]

/-- Evaluate `ψI'` on the positive imaginary axis as a restriction of `ψI`. -/
public lemma psiI'_mul_I_eq_resToImagAxis (t : ℝ) (ht : 0 < t) :
    ψI' (Complex.I * (t : ℂ)) = ψI.resToImagAxis t := by
  simp [ψI', Function.resToImagAxis, ResToImagAxis, ht]

/-- Cancellation estimate for `ψI'(it)` on `t ≥ 1`: after subtracting `144` and `exp (2π t)`,
the remainder is `O(exp (-π t))`. -/
public lemma exists_bound_norm_psiI'_mul_I_sub_exp_add_const_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖ψI' (Complex.I * (t : ℂ)) - (144 : ℂ) - (Real.exp (2 * π * t) : ℂ)‖
        ≤ C * Real.exp (-Real.pi * t) := by
  obtain ⟨Csum, hsum⟩ := exists_bound_norm_H3_add_H4_resToImagAxis_sub_two_sub_main_Ici_one
  obtain ⟨Cinv2, hinv2⟩ := exists_bound_norm_inv_H2_sq_sub_exp_add_const_Ici_one
  obtain ⟨Cinv3, hinv3⟩ := exists_bound_norm_inv_H3_sq_sub_one_Ici_one
  obtain ⟨CH2, hH2⟩ := exists_bound_norm_H2_resToImagAxis_sub_two_terms_Ici_one
  obtain ⟨CH4, hH4⟩ := exists_bound_norm_H4_resToImagAxis_sub_two_terms_Ici_one
  have nn : ∀ {C : ℝ} {x : ℂ} {a : ℝ}, ‖x‖ ≤ C * Real.exp a → 0 ≤ C := fun h =>
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) (Real.exp_pos _)
  have hCsum := nn (hsum 1 le_rfl); have hCinv2 := nn (hinv2 1 le_rfl)
  have hCinv3 := nn (hinv3 1 le_rfl)
  have hCH2 := nn (hH2 1 le_rfl); have hCH4 := nn (hH4 1 le_rfl)
  refine ⟨(128 : ℝ) *
      (((Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2)) +
        ((CH2 + CH4 + 112) * (Cinv3 + 2) + Cinv3)) + 192, fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht0' : 0 ≤ t := ht0.le
  set e : ℝ := Real.exp (2 * Real.pi * t)
  set u : ℝ := Real.exp (-(2 : ℝ) * Real.pi * t)
  set x : ℂ := H₃.resToImagAxis t + H₄.resToImagAxis t
  set y : ℂ := ((H₂.resToImagAxis t) ^ (2 : ℕ))⁻¹
  set z : ℂ := H₄.resToImagAxis t - H₂.resToImagAxis t
  set w : ℂ := ((H₃.resToImagAxis t) ^ (2 : ℕ))⁻¹
  set x0 : ℂ := (2 : ℂ) + (48 : ℂ) * (u : ℂ)
  set y0 : ℂ := ((e / 256 : ℝ) : ℂ) - ((1 / 32 : ℝ) : ℂ)
  have hx : ‖x - x0‖ ≤ Csum * Real.exp (-(3 : ℝ) * Real.pi * t) := by
    simpa [x, x0, u, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using hsum t ht
  have hy : ‖y - y0‖ ≤ Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t) := by
    simpa [y, y0, e, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hinv2 t ht
  have hw1 : ‖w - 1‖ ≤ Cinv3 * Real.exp (-Real.pi * t) := by
    simpa [w, sub_eq_add_neg] using hinv3 t ht
  have hle2 : Real.exp (-(2 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
    exp_neg_scaled_pi_le 2 (by norm_num) ht0'
  have hle3 : Real.exp (-(3 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
    exp_neg_scaled_pi_le 3 (by norm_num) ht0'
  have hle5 : Real.exp (-(5 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
    exp_neg_scaled_pi_le 5 (by norm_num) ht0'
  have hu_le : u ≤ Real.exp (-Real.pi * t) := hle2
  have heu : (e : ℂ) * (u : ℂ) = 1 := by exact_mod_cast (by simp [e, u, ← Real.exp_add] : e * u = 1)
  have hx0_bound : ‖x0‖ ≤ 50 := by
    have hu : 0 ≤ u := (Real.exp_pos _).le
    linarith [show ‖x0‖ ≤ 2 + 48 * u from by
      simpa [x0, abs_of_nonneg hu] using norm_add_le (2 : ℂ) ((48 : ℂ) * (u : ℂ)),
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht0'] : -(2 : ℝ) * Real.pi * t ≤ 0)]
  have hy0_bound : ‖y0‖ ≤ (e / 256) + (1 / 32) := by
    have he : 0 ≤ e := (Real.exp_pos _).le
    simpa [y0, RCLike.norm_ofReal, Real.norm_eq_abs, abs_of_nonneg he,
      abs_of_nonneg (by positivity : 0 ≤ (1 / 32 : ℝ))] using
        norm_sub_le ((e / 256 : ℝ) : ℂ) ((1 / 32 : ℝ) : ℂ)
  have hH2_bd : ‖H₂.resToImagAxis t‖ ≤ (CH2 + 80) * Real.exp (-Real.pi * t) :=
    norm_le_err_plus_main (by ring) hCH2 (by norm_num : (1 : ℝ) ≤ 5) ht0' (hH2 t ht) <|
      norm_two_exp_le_const (A := (16 : ℂ)) (B := (64 : ℂ)) (k := 3) (by norm_num) ht0'
        (by norm_num)
  have hH4_bd : ‖H₄.resToImagAxis t - 1‖ ≤ (CH4 + 32) * Real.exp (-Real.pi * t) := by
    have herr : ‖H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
          (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
            ≤ CH4 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hH4 t ht
    refine norm_le_err_plus_main (by ring) hCH4 (by norm_num : (1 : ℝ) ≤ 3) ht0' herr <|
      norm_two_exp_le_const (A := -(8 : ℂ)) (B := (24 : ℂ)) (k := 2) (by norm_num) ht0'
        (by norm_num)
  have hz1 : ‖z - 1‖ ≤ (CH2 + CH4 + 112) * Real.exp (-Real.pi * t) := by
    calc ‖z - 1‖ = ‖(H₄.resToImagAxis t - 1) - H₂.resToImagAxis t‖ := by dsimp [z]; ring_nf
      _ ≤ ‖H₄.resToImagAxis t - 1‖ + ‖H₂.resToImagAxis t‖ := norm_sub_le _ _
      _ ≤ (CH2 + CH4 + 112) * Real.exp (-Real.pi * t) := by linarith [hH4_bd, hH2_bd]
  have hw_bd : ‖w‖ ≤ Cinv3 + 2 := by
    have h := norm_add_le (w - 1) (1 : ℂ); simp at h
    nlinarith [mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2
      (by nlinarith [Real.pi_pos, ht0'] : -Real.pi * t ≤ 0)) hCinv3, hw1]
  have hdecomp :
      (128 : ℂ) * (x * y + z * w) - (e : ℂ) - (144 : ℂ) =
        ((128 : ℂ) * (x * y) - (e : ℂ) - (16 : ℂ)) +
          ((128 : ℂ) * (z * w) - (128 : ℂ)) := by ring
  have hA :
      ‖(128 : ℂ) * (x * y) - (e : ℂ) - (16 : ℂ)‖ ≤
        ((128 : ℝ) * ((Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2)) + 192) *
          Real.exp (-Real.pi * t) := by
    have he : e * Real.exp (-(3 : ℝ) * Real.pi * t) = Real.exp (-Real.pi * t) := by
      simp only [e, ← Real.exp_add]; congr 1; ring
    have hxdy : ‖(x - x0) * y0‖ ≤ (Csum + Csum / 256) * Real.exp (-Real.pi * t) := by
      nlinarith [norm_mul_le_of_le hx (show ‖y0‖ ≤ (e / 256) + 1 by linarith),
        mul_le_mul_of_nonneg_left hle3 hCsum, he]
    have hx0dy : ‖x0 * (y - y0)‖ ≤ (50 * Cinv2) * Real.exp (-Real.pi * t) := by
      have h0 : (0 : ℝ) ≤ 50 * Cinv2 := mul_nonneg (by linarith) hCinv2
      calc ‖x0 * (y - y0)‖ ≤ ‖x0‖ * ‖y - y0‖ := by simp
        _ ≤ 50 * (Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t)) :=
            mul_le_mul hx0_bound hy (norm_nonneg _) (by linarith)
        _ ≤ (50 * Cinv2) * Real.exp (-Real.pi * t) := by
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left hle2 h0
    have hdxdy : ‖(x - x0) * (y - y0)‖ ≤ (Csum * Cinv2) * Real.exp (-Real.pi * t) := by
      have hExp : Real.exp (-(3 : ℝ) * Real.pi * t) * Real.exp (-(2 : ℝ) * Real.pi * t) =
          Real.exp (-(5 : ℝ) * Real.pi * t) := by rw [← Real.exp_add]; congr 1; ring
      calc ‖(x - x0) * (y - y0)‖ = ‖x - x0‖ * ‖y - y0‖ := by simp
        _ ≤ (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) *
              (Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t)) :=
            mul_le_mul hx hy (norm_nonneg _) (mul_nonneg hCsum (Real.exp_pos _).le)
        _ = (Csum * Cinv2) * Real.exp (-(5 : ℝ) * Real.pi * t) := by
            linear_combination (Csum * Cinv2) * hExp
        _ ≤ (Csum * Cinv2) * Real.exp (-Real.pi * t) :=
            mul_le_mul_of_nonneg_left hle5 (mul_nonneg hCsum hCinv2)
    have hu_term : ‖(192 : ℂ) * (u : ℂ)‖ ≤ (192 : ℝ) * Real.exp (-Real.pi * t) := by
      simpa [abs_of_nonneg (by positivity : (0:ℝ) ≤ u)] using
        mul_le_mul_of_nonneg_left hu_le (by norm_num : (0:ℝ) ≤ 192)
    rw [show (128 : ℂ) * (x * y) - (e : ℂ) - (16 : ℂ) =
        (128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0)) -
          (192 : ℂ) * (u : ℂ) from by simp [x0, y0]; linear_combination 24 * heu]
    set Kxy : ℝ := (Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2) with hKxy
    have hS : ‖(x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0)‖ ≤
        Kxy * Real.exp (-Real.pi * t) := by
      rw [hKxy]; nlinarith [hxdy, hx0dy, hdxdy,
        norm_add₃_le (a := (x - x0) * y0) (b := x0 * (y - y0)) (c := (x - x0) * (y - y0))]
    calc ‖(128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0)) -
          (192 : ℂ) * (u : ℂ)‖
        ≤ ‖(128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0))‖ +
            ‖(192 : ℂ) * (u : ℂ)‖ := norm_sub_le _ _
      _ ≤ (128 : ℝ) * Kxy * Real.exp (-Real.pi * t) + (192 : ℝ) * Real.exp (-Real.pi * t) := by
          linarith [hu_term, show ‖(128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) +
              (x - x0) * (y - y0))‖ ≤ (128 : ℝ) * Kxy * Real.exp (-Real.pi * t) by
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left hS (by norm_num : (0:ℝ) ≤ 128)]
      _ = ((128 : ℝ) * Kxy + 192) * Real.exp (-Real.pi * t) := by ring
  have hB :
      ‖(128 : ℂ) * (z * w) - (128 : ℂ)‖ ≤
        (128 : ℝ) * ((CH2 + CH4 + 112) * (Cinv3 + 2) + Cinv3) * Real.exp (-Real.pi * t) := by
    have hzw : ‖z * w - 1‖ ≤ ‖z - 1‖ * ‖w‖ + ‖w - 1‖ := by
      simpa [show z * w - 1 = (z - 1) * w + (w - 1) by ring]
        using norm_add_le ((z - 1) * w) (w - 1)
    rw [show ‖(128 : ℂ) * (z * w) - (128 : ℂ)‖ = (128 : ℝ) * ‖z * w - 1‖ by
      rw [show (128 : ℂ) * (z * w) - (128 : ℂ) = (128 : ℂ) * (z * w - 1) by ring]; simp]
    have hz1' : ‖z - 1‖ * ‖w‖ ≤ ((CH2 + CH4 + 112) * Real.exp (-Real.pi * t)) * (Cinv3 + 2) :=
      mul_le_mul hz1 hw_bd (norm_nonneg _) (by positivity)
    grind only
  calc ‖ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) - ((Real.exp (2 * π * t) : ℝ) : ℂ)‖
      = ‖((128 : ℂ) * (x * y) - (e : ℂ) - (16 : ℂ)) +
          ((128 : ℂ) * (z * w) - (128 : ℂ))‖ := by
        rw [show ((Real.exp (2 * π * t) : ℝ) : ℂ) = (e : ℂ) from rfl,
          psiI'_mul_I_eq_resToImagAxis t ht0, show ψI.resToImagAxis t =
            (128 : ℂ) * (x * y + z * w) by
          simpa [Function.resToImagAxis, ResToImagAxis, ht0, nsmul_eq_mul, div_eq_mul_inv,
            mul_add, add_mul, x, y, z, w] using
              congrArg (fun f : ℍ → ℂ => f ⟨Complex.I * (t : ℂ), by simpa using ht0⟩) ψI_eq,
          ← hdecomp]; congr 1; ring
    _ ≤ _ + _ := norm_add_le _ _
    _ ≤ ((128 : ℝ) * (((Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2)) +
          ((CH2 + CH4 + 112) * (Cinv3 + 2) + Cinv3)) + 192) * Real.exp (-Real.pi * t) := by
        nlinarith [hA, hB, Real.exp_pos (-Real.pi * t)]

end

end MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators UpperHalfPlane

open MeasureTheory Real Complex
open Filter Topology

noncomputable section

/-- The bracket appearing in the "another integral" representation of `b'`. -/
@[expose] public def bAnotherBase (t : ℝ) : ℂ :=
  ψI' (Complex.I * (t : ℂ)) - (144 : ℂ) - (Real.exp (2 * π * t) : ℂ)

@[simp] public lemma bAnotherBase_eq (t : ℝ) :
    bAnotherBase t = ψI' (Complex.I * (t : ℂ)) - (144 : ℂ) - (Real.exp (2 * π * t) : ℂ) := rfl

public lemma continuousOn_bAnotherBase : ContinuousOn bAnotherBase (Set.Ioi (0 : ℝ)) := by
  refine (((Function.continuousOn_resToImagAxis_Ioi_of (F := ψI)
    MagicFunction.b.PsiBounds.continuous_ψI).congr fun t ht => ?_).sub continuousOn_const).sub
      (by fun_prop)
  simpa using
    MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation.psiI'_mul_I_eq_resToImagAxis t ht

lemma exists_bound_norm_bAnotherBase_Ioi :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ‖bAnotherBase t‖ ≤ C := by
  rcases
      MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
    ⟨Cψ, hCψ⟩
  let Cψ0 : ℝ := max Cψ 0
  have hCψ0 : 0 ≤ Cψ0 := le_max_right _ _
  have hψS_bound (s : ℝ) (hs : 1 ≤ s) :
      ‖ψS.resToImagAxis s‖ ≤ Cψ0 * Real.exp (-π * s) :=
    (hCψ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hψI'_small (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
      ‖ψI' (Complex.I * (t : ℂ))‖ ≤ Cψ0 := by
    have ht' : 1 ≤ (1 / t : ℝ) := by simpa [one_div] using (one_le_div ht0).2 ht1
    have hψS' : ‖ψS.resToImagAxis (1 / t : ℝ)‖ ≤ Cψ0 := by
      simpa using (hψS_bound (1 / t : ℝ) ht').trans
        (mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, (one_div_pos.2 ht0).le]))
          hCψ0)
    rw [MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation.psiI'_mul_I_eq_resToImagAxis
      t ht0, show ψI.resToImagAxis t = (-(t ^ (2 : ℕ)) : ℂ) * ψS.resToImagAxis (1 / t) by
        simpa [ψS_slash_S, zpow_two, pow_two] using
          ResToImagAxis.SlashActionS (F := ψS) (k := (-2 : ℤ)) (t := t) ht0, norm_mul]
    nlinarith [show ‖(-(t ^ (2 : ℕ)) : ℂ)‖ = t ^ (2 : ℕ) from by simp, hψS', hCψ0,
      show t ^ (2 : ℕ) ≤ 1 from by simpa using pow_le_one₀ (n := 2) ht0.le ht1]
  open MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation in
    rcases exists_bound_norm_psiI'_mul_I_sub_exp_add_const_Ici_one with ⟨Ctail, hCtail⟩
  let Ctail0 : ℝ := max Ctail 0
  have hCtail0 : 0 ≤ Ctail0 := le_max_right _ _
  have htail (t : ℝ) (ht : 1 ≤ t) : ‖bAnotherBase t‖ ≤ Ctail0 := by
    have h1 : ‖bAnotherBase t‖ ≤ Ctail0 * Real.exp (-Real.pi * t) :=
      (hCtail t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hexp_le : Real.exp (-Real.pi * t) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    exact h1.trans (by simpa [mul_one] using mul_le_mul_of_nonneg_left hexp_le hCtail0)
  let Csmall : ℝ := Cψ0 + 144 + Real.exp (2 * π)
  refine ⟨max Csmall Ctail0, fun t ht0 => ?_⟩
  by_cases ht1 : t ≤ 1
  · have hexp : ‖(Real.exp (2 * π * t) : ℂ)‖ ≤ Real.exp (2 * π) := by
      rw [Complex.ofReal_exp, Complex.norm_exp_ofReal]
      exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    have htri :
        ‖bAnotherBase t‖ ≤ ‖ψI' (Complex.I * (t : ℂ))‖ + ‖(144 : ℂ)‖ +
            ‖(Real.exp (2 * π * t) : ℂ)‖ := by
      simpa [bAnotherBase, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (calc
          ‖ψI' (Complex.I * (t : ℂ)) - ((144 : ℂ) + (Real.exp (2 * π * t) : ℂ))‖
              ≤ ‖ψI' (Complex.I * (t : ℂ))‖ +
                  ‖(144 : ℂ) + (Real.exp (2 * π * t) : ℂ)‖ := norm_sub_le _ _
          _ ≤ ‖ψI' (Complex.I * (t : ℂ))‖ +
                (‖(144 : ℂ)‖ + ‖(Real.exp (2 * π * t) : ℂ)‖) := by
                gcongr; exact norm_add_le _ _)
    exact (by
      grind only [hψI'_small t ht0 ht1, show ‖(144 : ℂ)‖ = (144 : ℝ) from by norm_num] :
      ‖bAnotherBase t‖ ≤ Csmall).trans (le_max_left _ _)
  · exact (htail t (le_of_not_ge ht1)).trans (le_max_right _ _)

/-- Integrability of `t ↦ bAnotherBase t * exp (-π u t)` on `t > 0`, for `u > 0`. -/
public lemma bAnotherBase_integrable_exp {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => bAnotherBase t * (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
  obtain ⟨C, hC⟩ := exists_bound_norm_bAnotherBase_Ioi
  set C0 : ℝ := max C 0
  have hb : ∀ t : ℝ, 0 < t → ‖bAnotherBase t‖ ≤ C0 :=
    fun t ht => (hC t ht).trans (le_max_left _ _)
  have hg :
      Integrable (fun t : ℝ => C0 * Real.exp (-(π * u) * t))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
    simpa [MeasureTheory.IntegrableOn, mul_assoc] using
      (exp_neg_integrableOn_Ioi (a := (0 : ℝ)) (mul_pos Real.pi_pos hu)).const_mul C0
  have hf_meas :
      AEStronglyMeasurable (fun t : ℝ => bAnotherBase t * (Real.exp (-π * u * t) : ℂ))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) :=
    (continuousOn_bAnotherBase.mul (by fun_prop : ContinuousOn
      (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)))).aestronglyMeasurable
        measurableSet_Ioi
  have hbound :
      ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))),
        ‖bAnotherBase t * (Real.exp (-π * u * t) : ℂ)‖ ≤
          C0 * Real.exp (-(π * u) * t) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    rw [norm_mul, show ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-(π * u) * t) from by
      rw [show (-π * u * t) = (-(π * u) * t) from by ring, Complex.ofReal_exp,
        Complex.norm_exp_ofReal]]
    gcongr; exact hb t ht
  simpa [MeasureTheory.IntegrableOn] using Integrable.mono' hg hf_meas hbound

end

end MagicFunction.g.CohnElkies.IntegralReps
