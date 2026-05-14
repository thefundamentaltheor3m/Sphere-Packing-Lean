module
public import SpherePacking.MagicFunction.b.Psi
public import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import SpherePacking.ModularForms.ResToImagAxis
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis.QExpansion
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis.HExpansions
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis.InvH2Sq
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common

/-! Cancellation estimates for `ψI'(it)` and the `bAnotherBase` bracket.

After subtracting `exp (2π t)` and `144`, the remainder decays like `O(exp (-π t))`. The
`bAnotherBase` bracket combines this with the explicit terms and is shown to be uniformly
bounded on `Ioi 0` and integrable against `exp (-π u t)`. -/

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
  have hCinv3 := nn (hinv3 1 le_rfl); have hCH2 := nn (hH2 1 le_rfl)
  have hCH4 := nn (hH4 1 le_rfl)
  refine ⟨(128 : ℝ) *
      (((Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2)) +
        ((CH2 + CH4 + 112) * (Cinv3 + 2) + Cinv3)) + 192, ?_⟩
  intro t ht
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
  refine ⟨max Csmall Ctail0, ?_⟩
  intro t ht0
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
