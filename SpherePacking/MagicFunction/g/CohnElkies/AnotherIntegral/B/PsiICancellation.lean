module
public import SpherePacking.MagicFunction.b.Psi
public import SpherePacking.ModularForms.ResToImagAxis
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis.QExpansion
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis.HExpansions
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis.InvH2Sq
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common


/-!
# Cancellation estimate for `ψI'(it)` (AnotherIntegral.B)

After subtracting the main terms `exp (2π t)` and `144`, the remainder decays like
`O(exp (-π t))`.
-/

namespace MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation

open scoped BigOperators UpperHalfPlane

open MeasureTheory Real Complex Filter Topology

noncomputable section

open MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis

/-- For `c ≥ 1` and `t ≥ 0`, `exp (-c π t) ≤ exp (-π t)`. -/
private lemma exp_neg_scaled_pi_le (c : ℝ) (hc : 1 ≤ c) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-c * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
  Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.mpr hc) ht])

/--
If `A = err + main` where `‖err‖ ≤ Cerr * exp(-k π t)` with `k ≥ 1` and
`‖main‖ ≤ Cm * exp(-π t)`, then `‖A‖ ≤ (Cerr + Cm) * exp(-π t)`.
-/
private lemma norm_le_err_plus_main {A err main : ℂ} (hdec : A = err + main)
    {Cerr k Cm : ℝ} (hCerr : 0 ≤ Cerr) (hk : 1 ≤ k) {t : ℝ} (ht : 0 ≤ t)
    (herr : ‖err‖ ≤ Cerr * Real.exp (-k * Real.pi * t))
    (hmain : ‖main‖ ≤ Cm * Real.exp (-Real.pi * t)) :
    ‖A‖ ≤ (Cerr + Cm) * Real.exp (-Real.pi * t) :=
  hdec ▸ (norm_add_le _ _).trans (by
    nlinarith [mul_le_mul_of_nonneg_left (exp_neg_scaled_pi_le k hk ht) hCerr, herr, hmain])

/-- Evaluate `ψI'` on the positive imaginary axis as a restriction of `ψI`. -/
public lemma psiI'_mul_I_eq_resToImagAxis (t : ℝ) (ht : 0 < t) :
    ψI' (Complex.I * (t : ℂ)) = ψI.resToImagAxis t := by
  simp [ψI', Function.resToImagAxis, ResToImagAxis, ht]

lemma psiI_resToImagAxis_eq (t : ℝ) (ht : 0 < t) :
    ψI.resToImagAxis t =
      (128 : ℂ) *
          (((H₃.resToImagAxis t + H₄.resToImagAxis t) / (H₂.resToImagAxis t) ^ (2 : ℕ)) +
            ((H₄.resToImagAxis t - H₂.resToImagAxis t) / (H₃.resToImagAxis t) ^ (2 : ℕ))) := by
  simpa [Function.resToImagAxis, ResToImagAxis, ht, nsmul_eq_mul, div_eq_mul_inv, mul_add, add_mul]
    using congrArg (fun f : ℍ → ℂ => f ⟨Complex.I * (t : ℂ), by simpa using ht⟩) ψI_eq

/--
Cancellation estimate for `ψI'(it)` on `t ≥ 1`.

After subtracting `144` and `exp (2π t)`, the remainder is `O(exp (-π t))`.
-/
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
  have hCsum := nn (hsum 1 le_rfl)
  have hCinv2 := nn (hinv2 1 le_rfl)
  have hCinv3 := nn (hinv3 1 le_rfl)
  have hCH2 := nn (hH2 1 le_rfl)
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
  have hxy0_main :
      (128 : ℂ) * (x0 * y0) = (e : ℂ) + (16 : ℂ) - (192 : ℂ) * (u : ℂ) := by
    simp [x0, y0]; linear_combination 24 * heu
  have hx0_bound : ‖x0‖ ≤ 50 := by
    have hu : 0 ≤ u := (Real.exp_pos _).le
    have hu1 : u ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht0'])
    linarith [show ‖x0‖ ≤ 2 + 48 * u from by
      simpa [x0, abs_of_nonneg hu] using norm_add_le (2 : ℂ) ((48 : ℂ) * (u : ℂ))]
  have hy0_bound : ‖y0‖ ≤ (e / 256) + (1 / 32) := by
    have he : 0 ≤ e := (Real.exp_pos _).le
    simpa [y0, RCLike.norm_ofReal, Real.norm_eq_abs, abs_of_nonneg he,
      abs_of_nonneg (by positivity : 0 ≤ (1 / 32 : ℝ))] using
        norm_sub_le ((e / 256 : ℝ) : ℂ) ((1 / 32 : ℝ) : ℂ)
  have hH2_bd : ‖H₂.resToImagAxis t‖ ≤ (CH2 + 80) * Real.exp (-Real.pi * t) :=
    norm_le_err_plus_main (by ring) hCH2 (by norm_num : (1 : ℝ) ≤ 5) ht0' (hH2 t ht) <| calc
      ‖(16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
          (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
      _ ≤ ‖(16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖ +
            ‖(64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖ := norm_add_le _ _
      _ = (16 : ℝ) * Real.exp (-Real.pi * t) +
            (64 : ℝ) * Real.exp (-(3 : ℝ) * Real.pi * t) := by
          simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
      _ ≤ (80 : ℝ) * Real.exp (-Real.pi * t) := by
          linarith [mul_le_mul_of_nonneg_left hle3 (by norm_num : (0:ℝ) ≤ 64)]
  have hH4_bd : ‖H₄.resToImagAxis t - 1‖ ≤ (CH4 + 32) * Real.exp (-Real.pi * t) := by
    have herr : ‖H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) -
          (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
            ≤ CH4 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hH4 t ht
    refine norm_le_err_plus_main (by ring) hCH4 (by norm_num : (1 : ℝ) ≤ 3) ht0' herr <| calc
      ‖-(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
          (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
      _ ≤ ‖-(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖ +
            ‖(24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ := norm_add_le _ _
      _ = (8 : ℝ) * Real.exp (-Real.pi * t) +
            (24 : ℝ) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
          simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
      _ ≤ (32 : ℝ) * Real.exp (-Real.pi * t) := by
          linarith [mul_le_mul_of_nonneg_left hle2 (by norm_num : (0:ℝ) ≤ 24)]
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
      have h1 := norm_mul_le_of_le hx (show ‖y0‖ ≤ (e / 256) + 1 by linarith)
      nlinarith [h1, mul_le_mul_of_nonneg_left hle3 hCsum, he]
    have hx0dy : ‖x0 * (y - y0)‖ ≤ (50 * Cinv2) * Real.exp (-Real.pi * t) := by
      have h0 : (0 : ℝ) ≤ 50 * Cinv2 := mul_nonneg (by linarith) hCinv2
      calc ‖x0 * (y - y0)‖ ≤ ‖x0‖ * ‖y - y0‖ := by simp
        _ ≤ 50 * (Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t)) :=
            mul_le_mul hx0_bound hy (norm_nonneg _) (by linarith)
        _ ≤ (50 * Cinv2) * Real.exp (-Real.pi * t) := by
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left hle2 h0
    have hExp : Real.exp (-(3 : ℝ) * Real.pi * t) * Real.exp (-(2 : ℝ) * Real.pi * t) =
        Real.exp (-(5 : ℝ) * Real.pi * t) := by rw [← Real.exp_add]; congr 1; ring
    have hdxdy :
        ‖(x - x0) * (y - y0)‖ ≤ (Csum * Cinv2) * Real.exp (-Real.pi * t) := calc
      _ = ‖x - x0‖ * ‖y - y0‖ := by simp
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
          (192 : ℂ) * (u : ℂ) from by grind only]
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
            (128 : ℂ) * (x * y + z * w) from psiI_resToImagAxis_eq t ht0, ← hdecomp]; congr 1; ring
    _ ≤ _ + _ := norm_add_le _ _
    _ ≤ ((128 : ℝ) * (((Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2)) +
          ((CH2 + CH4 + 112) * (Cinv3 + 2) + Cinv3)) + 192) * Real.exp (-Real.pi * t) := by
        nlinarith [hA, hB, Real.exp_pos (-Real.pi * t)]

end

end MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation
