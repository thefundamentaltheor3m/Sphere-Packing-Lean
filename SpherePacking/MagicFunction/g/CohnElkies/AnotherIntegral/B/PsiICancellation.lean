module
public import SpherePacking.MagicFunction.b.Psi
public import SpherePacking.ModularForms.ResToImagAxis
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis.QExpansion
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis.HExpansions
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis.InvH2Sq
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common


/-!
# Cancellation estimate for `ψI'(it)` (AnotherIntegral.B)

This file combines the theta-function bounds from the `ThetaAxis` files into the cancellation
estimate for `ψI'` on the positive imaginary axis: after subtracting the main terms `exp (2π t)`
and `144`, the remainder decays like `O(exp (-π t))`.

## Main statements
* `psiI'_mul_I_eq_resToImagAxis`
* `exists_bound_norm_psiI'_mul_I_sub_exp_add_const_Ici_one`
-/

namespace MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation

open scoped BigOperators UpperHalfPlane

open MeasureTheory Real Complex Filter Topology

noncomputable section

open MagicFunction.g.CohnElkies.AnotherIntegral.B.ThetaAxis

/-- For `c ≥ 1` and `t ≥ 0`, `exp (-c π t) ≤ exp (-π t)`. -/
private lemma exp_neg_scaled_pi_le (c : ℝ) (hc : 1 ≤ c) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-c * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
  Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht, hc])

/-- Bound the norm of a two-term scaled-exponential combination by a single `exp(-π t)` factor. -/
private lemma norm_two_exp_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {c d : ℝ}
    (hc : 1 ≤ c) (hd : 1 ≤ d) {t : ℝ} (ht : 0 ≤ t) :
    ‖(a : ℂ) * (Real.exp (-c * Real.pi * t) : ℂ) +
        (b : ℂ) * (Real.exp (-d * Real.pi * t) : ℂ)‖
      ≤ (a + b) * Real.exp (-Real.pi * t) := by
  calc
    ‖(a : ℂ) * (Real.exp (-c * Real.pi * t) : ℂ) +
        (b : ℂ) * (Real.exp (-d * Real.pi * t) : ℂ)‖
        ≤ ‖(a : ℂ) * (Real.exp (-c * Real.pi * t) : ℂ)‖ +
            ‖(b : ℂ) * (Real.exp (-d * Real.pi * t) : ℂ)‖ := norm_add_le _ _
    _ = a * Real.exp (-c * Real.pi * t) + b * Real.exp (-d * Real.pi * t) := by
          simp [abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg ha, abs_of_nonneg hb,
            -Complex.ofReal_exp]
    _ ≤ a * Real.exp (-Real.pi * t) + b * Real.exp (-Real.pi * t) := by
          gcongr <;> [exact exp_neg_scaled_pi_le c hc ht; exact exp_neg_scaled_pi_le d hd ht]
    _ = (a + b) * Real.exp (-Real.pi * t) := by ring

/--
If `A = err + main` where `‖err‖ ≤ Cerr * exp(-k π t)` with `k ≥ 1` and
`‖main‖ ≤ Cm * exp(-π t)`, then `‖A‖ ≤ (Cerr + Cm) * exp(-π t)`.
(Specialized to our `exp` exponents; used for `H₂` and `H₄ - 1` bounds.)
-/
private lemma norm_le_err_plus_main {A err main : ℂ} (hdec : A = err + main)
    {Cerr k Cm : ℝ} (hCerr : 0 ≤ Cerr) (hk : 1 ≤ k) {t : ℝ} (ht : 0 ≤ t)
    (herr : ‖err‖ ≤ Cerr * Real.exp (-k * Real.pi * t))
    (hmain : ‖main‖ ≤ Cm * Real.exp (-Real.pi * t)) :
    ‖A‖ ≤ (Cerr + Cm) * Real.exp (-Real.pi * t) := by
  have hterm : Cerr * Real.exp (-k * Real.pi * t) ≤ Cerr * Real.exp (-Real.pi * t) :=
    mul_le_mul_of_nonneg_left (exp_neg_scaled_pi_le k hk ht) hCerr
  calc
    ‖A‖ = ‖err + main‖ := by rw [hdec]
    _ ≤ ‖err‖ + ‖main‖ := norm_add_le _ _
    _ ≤ Cerr * Real.exp (-k * Real.pi * t) + Cm * Real.exp (-Real.pi * t) :=
        add_le_add herr hmain
    _ ≤ Cerr * Real.exp (-Real.pi * t) + Cm * Real.exp (-Real.pi * t) :=
        add_le_add_right hterm _
    _ = (Cerr + Cm) * Real.exp (-Real.pi * t) := by ring

/-- Evaluate `ψI'` on the positive imaginary axis as a restriction of `ψI`. -/
public lemma psiI'_mul_I_eq_resToImagAxis (t : ℝ) (ht : 0 < t) :
    ψI' (Complex.I * (t : ℂ)) = ψI.resToImagAxis t := by
  simp [ψI', Function.resToImagAxis, ResToImagAxis, ht]

lemma psiI_resToImagAxis_eq (t : ℝ) (ht : 0 < t) :
    ψI.resToImagAxis t =
      (128 : ℂ) *
          (((H₃.resToImagAxis t + H₄.resToImagAxis t) / (H₂.resToImagAxis t) ^ (2 : ℕ)) +
            ((H₄.resToImagAxis t - H₂.resToImagAxis t) / (H₃.resToImagAxis t) ^ (2 : ℕ))) := by
  have hψ := congrArg (fun f : ℍ → ℂ => f ⟨Complex.I * (t : ℂ), by simpa using ht⟩) ψI_eq
  simpa [Function.resToImagAxis, ResToImagAxis, ht, nsmul_eq_mul, div_eq_mul_inv, mul_add, add_mul]
    using hψ

/--
Cancellation estimate for `ψI'(it)` on `t ≥ 1`.

After subtracting `144` and `exp (2π t)`, the remainder is `O(exp (-π t))`.
-/
public lemma exists_bound_norm_psiI'_mul_I_sub_exp_add_const_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖ψI' (Complex.I * (t : ℂ)) - (144 : ℂ) - (Real.exp (2 * π * t) : ℂ)‖
        ≤ C * Real.exp (-Real.pi * t) := by
  rcases exists_bound_norm_H3_add_H4_resToImagAxis_sub_two_sub_main_Ici_one with ⟨Csum, hsum⟩
  rcases exists_bound_norm_inv_H2_sq_sub_exp_add_const_Ici_one with ⟨Cinv2, hinv2⟩
  rcases exists_bound_norm_inv_H3_sq_sub_one_Ici_one with ⟨Cinv3, hinv3⟩
  rcases exists_bound_norm_H2_resToImagAxis_sub_two_terms_Ici_one with ⟨CH2, hH2⟩
  rcases exists_bound_norm_H4_resToImagAxis_sub_two_terms_Ici_one with ⟨CH4, hH4⟩
  have nonneg_of_bound {C : ℝ} {x : ℂ} {a : ℝ} (h : ‖x‖ ≤ C * Real.exp a) : 0 ≤ C :=
    nonneg_of_mul_nonneg_left ((norm_nonneg x).trans h) (Real.exp_pos a)
  have hCsum : 0 ≤ Csum := nonneg_of_bound (hsum 1 le_rfl)
  have hCinv2 : 0 ≤ Cinv2 := nonneg_of_bound (hinv2 1 le_rfl)
  have hCinv3 : 0 ≤ Cinv3 := nonneg_of_bound (hinv3 1 le_rfl)
  have hCH2 : 0 ≤ CH2 := nonneg_of_bound (hH2 1 le_rfl)
  have hCH4 : 0 ≤ CH4 := nonneg_of_bound (hH4 1 le_rfl)
  refine ⟨(128 : ℝ) *
      (((Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2)) +
        ((CH2 + CH4 + 112) * (Cinv3 + 2) + Cinv3)) + 192, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht0' : 0 ≤ t := le_of_lt ht0
  have hres : ψI' ((Complex.I : ℂ) * (t : ℂ)) = ψI.resToImagAxis t :=
    psiI'_mul_I_eq_resToImagAxis t ht0
  have hψI := psiI_resToImagAxis_eq t ht0
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
  have heu : e * u = 1 := by
    rw [show e = Real.exp (2 * Real.pi * t) from rfl,
        show u = Real.exp (-(2 : ℝ) * Real.pi * t) from rfl, ← Real.exp_add]
    simp [show (2 : ℝ) * Real.pi * t + -(2 : ℝ) * Real.pi * t = 0 by ring]
  have hxy0_mainR :
      (128 : ℝ) * ((2 + 48 * u) * (e / 256 - 1 / 32)) = e + 16 - 192 * u := by
    have heu' : u * e = 1 := by simpa [mul_comm] using heu
    ring_nf
    simp [heu']
    ring_nf
  have hxy0_main :
      (128 : ℂ) * (x0 * y0) = (e : ℂ) + (16 : ℂ) - (192 : ℂ) * (u : ℂ) := by
    have hcast :
        (128 : ℂ) * (x0 * y0) =
          ((128 : ℝ) * ((2 + 48 * u) * (e / 256 - 1 / 32)) : ℂ) := by
      simp [x0, y0]
    calc
      (128 : ℂ) * (x0 * y0) =
          ((128 : ℝ) * ((2 + 48 * u) * (e / 256 - 1 / 32)) : ℂ) := hcast
      _ = ((e + 16 - 192 * u : ℝ) : ℂ) := by
            simpa using congrArg (fun r : ℝ => (r : ℂ)) hxy0_mainR
      _ = (e : ℂ) + (16 : ℂ) - (192 : ℂ) * (u : ℂ) := by simp [sub_eq_add_neg]
  have hx0_bound : ‖x0‖ ≤ 50 := by
    have hu1 : u ≤ 1 := by
      have : (-(2 : ℝ) * Real.pi * t) ≤ 0 := by nlinarith [Real.pi_pos, ht0']
      simpa [u] using (Real.exp_le_one_iff.2 this)
    have hu : 0 ≤ u := (Real.exp_pos _).le
    have huNorm : ‖(48 : ℂ) * (u : ℂ)‖ = (48 : ℝ) * u := by
      simp [abs_of_nonneg hu]
    have hx0_le : ‖x0‖ ≤ 2 + 48 * u := by
      calc
        ‖x0‖ = ‖(2 : ℂ) + (48 : ℂ) * (u : ℂ)‖ := by simp [x0]
        _ ≤ ‖(2 : ℂ)‖ + ‖(48 : ℂ) * (u : ℂ)‖ := norm_add_le _ _
        _ = 2 + 48 * u := by rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by simp, huNorm]
    linarith
  have hy0_bound : ‖y0‖ ≤ (e / 256) + (1 / 32) := by
    have he : 0 ≤ e := (Real.exp_pos _).le
    simpa [y0, RCLike.norm_ofReal, Real.norm_eq_abs,
      abs_of_nonneg he,
      abs_of_nonneg (by positivity : 0 ≤ (1 / 32 : ℝ))] using
        norm_sub_le ((e / 256 : ℝ) : ℂ) ((1 / 32 : ℝ) : ℂ)
  -- Use `norm_le_err_plus_main` to combine the `err` and `main` bounds for H₂ and H₄ - 1.
  have hH2_bd : ‖H₂.resToImagAxis t‖ ≤ (CH2 + 80) * Real.exp (-Real.pi * t) := by
    have hdec : H₂.resToImagAxis t =
        (H₂.resToImagAxis t - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
            - (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)) +
          ((16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
            (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)) := by ring
    have hmain := norm_two_exp_le (a := (16 : ℝ)) (b := (64 : ℝ)) (by norm_num) (by norm_num)
      (c := (1 : ℝ)) (d := (3 : ℝ)) le_rfl (by norm_num) ht0'
    have hmain' :
        ‖(16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
            (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
          ≤ (80 : ℝ) * Real.exp (-Real.pi * t) := by
      simpa [show (-(1 : ℝ) * Real.pi * t) = -Real.pi * t by ring] using hmain
    exact norm_le_err_plus_main hdec hCH2 (by norm_num : (1 : ℝ) ≤ 5) ht0' (hH2 t ht) hmain'
  have hH4_bd : ‖H₄.resToImagAxis t - 1‖ ≤ (CH4 + 32) * Real.exp (-Real.pi * t) := by
    have hdec : H₄.resToImagAxis t - 1 =
        (H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
            - (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)) +
          (-(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
            (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)) := by ring
    have herr :
        ‖H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
            - (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
          ≤ CH4 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hH4 t ht
    -- `-8 * exp + 24 * exp2 = (-8) * exp + 24 * exp2`; bound using triangle + scaling.
    have hmain :
        ‖-(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
            (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
          ≤ (32 : ℝ) * Real.exp (-Real.pi * t) := by
      calc
        ‖-(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
            (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
            ≤ ‖-(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖ +
                ‖(24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ := norm_add_le _ _
        _ = (8 : ℝ) * Real.exp (-Real.pi * t) +
              (24 : ℝ) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
              simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
        _ ≤ (8 : ℝ) * Real.exp (-Real.pi * t) +
              (24 : ℝ) * Real.exp (-Real.pi * t) := by gcongr
        _ = (32 : ℝ) * Real.exp (-Real.pi * t) := by ring
    exact norm_le_err_plus_main hdec hCH4 (by norm_num : (1 : ℝ) ≤ 3) ht0' herr hmain
  have hz1 : ‖z - 1‖ ≤ (CH2 + CH4 + 112) * Real.exp (-Real.pi * t) := by
    have hz : z - 1 = (H₄.resToImagAxis t - 1) - H₂.resToImagAxis t := by dsimp [z]; ring
    calc
      ‖z - 1‖ = ‖(H₄.resToImagAxis t - 1) - H₂.resToImagAxis t‖ := by simp [hz]
      _ ≤ ‖H₄.resToImagAxis t - 1‖ + ‖H₂.resToImagAxis t‖ := norm_sub_le _ _
      _ ≤ (CH4 + 32) * Real.exp (-Real.pi * t) + (CH2 + 80) * Real.exp (-Real.pi * t) :=
          add_le_add hH4_bd hH2_bd
      _ = (CH2 + CH4 + 112) * Real.exp (-Real.pi * t) := by ring
  have hw_bd : ‖w‖ ≤ Cinv3 + 2 := by
    have hexp_le : Real.exp (-Real.pi * t) ≤ 1 :=
      (Real.exp_le_one_iff).2 (by nlinarith [Real.pi_pos, ht0'])
    have hterm : Cinv3 * Real.exp (-Real.pi * t) ≤ Cinv3 := by
      simpa [mul_one] using mul_le_mul_of_nonneg_left hexp_le hCinv3
    have hw_le : ‖w‖ ≤ Cinv3 * Real.exp (-Real.pi * t) + 1 := by
      have hw : w = (w - 1) + 1 := by ring
      calc
        ‖w‖ = ‖(w - 1) + 1‖ := by rw [← hw]
        _ ≤ ‖w - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ Cinv3 * Real.exp (-Real.pi * t) + 1 := by simpa using hw1
    linarith
  have hdecomp :
      (128 : ℂ) * (x * y + z * w) - (e : ℂ) - (144 : ℂ) =
        ((128 : ℂ) * (x * y) - (e : ℂ) - (16 : ℂ)) +
          ((128 : ℂ) * (z * w) - (128 : ℂ)) := by ring
  have hA :
      ‖(128 : ℂ) * (x * y) - (e : ℂ) - (16 : ℂ)‖ ≤
        ((128 : ℝ) * ((Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2)) + 192) *
          Real.exp (-Real.pi * t) := by
    have hxdy :
        ‖(x - x0) * y0‖ ≤ (Csum + Csum / 256) * Real.exp (-Real.pi * t) := by
      have hy0' : ‖y0‖ ≤ (e / 256) + 1 := by linarith
      have hE :
          (e / 256) * Real.exp (-(3 : ℝ) * Real.pi * t) =
            (1 / 256) * Real.exp (-Real.pi * t) := by
        have he : e * Real.exp (-(3 : ℝ) * Real.pi * t) = Real.exp (-Real.pi * t) := by
          rw [show e = Real.exp (2 * Real.pi * t) from rfl, ← Real.exp_add]
          congr 1; ring
        calc
          (e / 256) * Real.exp (-(3 : ℝ) * Real.pi * t)
              = (e * Real.exp (-(3 : ℝ) * Real.pi * t)) / 256 := by ring
          _ = Real.exp (-Real.pi * t) / 256 := by rw [he]
          _ = (1 / 256) * Real.exp (-Real.pi * t) := by ring
      have hterm3 : Csum * Real.exp (-(3 : ℝ) * Real.pi * t) ≤ Csum * Real.exp (-Real.pi * t) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hle3 hCsum
      have hfirst :
          (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) * (e / 256) =
            (Csum / 256) * Real.exp (-Real.pi * t) := by
        calc
          (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) * (e / 256)
              = Csum * ((e / 256) * Real.exp (-(3 : ℝ) * Real.pi * t)) := by ring
          _ = Csum * ((1 / 256) * Real.exp (-Real.pi * t)) := by rw [hE]
          _ = (Csum / 256) * Real.exp (-Real.pi * t) := by ring
      calc
        ‖(x - x0) * y0‖ ≤ (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) * ((e / 256) + 1) :=
            norm_mul_le_of_le hx hy0'
        _ = (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) * (e / 256) +
              (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) := by ring
        _ = (Csum / 256) * Real.exp (-Real.pi * t) +
              (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) := by rw [hfirst]
        _ ≤ (Csum / 256) * Real.exp (-Real.pi * t) + (Csum * Real.exp (-Real.pi * t)) := by
              linarith
        _ = (Csum + Csum / 256) * Real.exp (-Real.pi * t) := by ring
    have hx0dy : ‖x0 * (y - y0)‖ ≤ (50 * Cinv2) * Real.exp (-Real.pi * t) := by
      have h0 : (0 : ℝ) ≤ 50 * Cinv2 := mul_nonneg (by linarith) hCinv2
      calc
        ‖x0 * (y - y0)‖ ≤ ‖x0‖ * ‖y - y0‖ := by simp
        _ ≤ 50 * (Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t)) :=
            mul_le_mul hx0_bound hy (norm_nonneg _) (by linarith)
        _ ≤ (50 * Cinv2) * Real.exp (-Real.pi * t) := by
              simpa [mul_assoc] using mul_le_mul_of_nonneg_left hle2 h0
    have hdxdy :
        ‖(x - x0) * (y - y0)‖ ≤ (Csum * Cinv2) * Real.exp (-Real.pi * t) := by
      have hExp :
          Real.exp (-(3 : ℝ) * Real.pi * t) * Real.exp (-(2 : ℝ) * Real.pi * t) =
            Real.exp (-(5 : ℝ) * Real.pi * t) := by
        rw [← Real.exp_add]; congr 1; ring
      have h0 : 0 ≤ Csum * Cinv2 := mul_nonneg hCsum hCinv2
      calc
        ‖(x - x0) * (y - y0)‖ = ‖x - x0‖ * ‖y - y0‖ := by simp
        _ ≤ (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) *
              (Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t)) :=
            mul_le_mul hx hy (norm_nonneg _) (mul_nonneg hCsum (Real.exp_pos _).le)
        _ = (Csum * Cinv2) * Real.exp (-(5 : ℝ) * Real.pi * t) := by
              rw [show (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) *
                (Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t)) =
                  (Csum * Cinv2) *
                  (Real.exp (-(3 : ℝ) * Real.pi * t) * Real.exp (-(2 : ℝ) * Real.pi * t))
                from by ring, hExp]
        _ ≤ (Csum * Cinv2) * Real.exp (-Real.pi * t) := mul_le_mul_of_nonneg_left hle5 h0
    have hu_term : ‖(192 : ℂ) * (u : ℂ)‖ ≤ (192 : ℝ) * Real.exp (-Real.pi * t) := by
      have hu0 : 0 ≤ u := by positivity
      have habs : |u| ≤ Real.exp (-Real.pi * t) := by
        simpa [abs_of_nonneg hu0] using hu_le
      calc
        ‖(192 : ℂ) * (u : ℂ)‖ = (192 : ℝ) * |u| := by simp
        _ ≤ (192 : ℝ) * Real.exp (-Real.pi * t) :=
            mul_le_mul_of_nonneg_left habs (by linarith)
    have hsplit :
        (128 : ℂ) * (x * y) - (e : ℂ) - (16 : ℂ) =
          (128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0)) -
            (192 : ℂ) * (u : ℂ) := by grind only
    rw [hsplit]
    set Kxy : ℝ := (Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2)
    have hsum' :
        ‖(128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0))‖
          ≤ (128 : ℝ) * Kxy * Real.exp (-Real.pi * t) := by
      have hS :
          ‖(x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0)‖ ≤
            Kxy * Real.exp (-Real.pi * t) := by
        calc
          ‖(x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0)‖
              ≤ ‖(x - x0) * y0‖ + ‖x0 * (y - y0)‖ + ‖(x - x0) * (y - y0)‖ := norm_add₃_le
          _ ≤ (Csum + Csum / 256) * Real.exp (-Real.pi * t) +
                (50 * Cinv2) * Real.exp (-Real.pi * t) +
                (Csum * Cinv2) * Real.exp (-Real.pi * t) := by gcongr
          _ = Kxy * Real.exp (-Real.pi * t) := by simp [Kxy]; ring
      calc
        ‖(128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0))‖
            = (128 : ℝ) * ‖(x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0)‖ := by simp
        _ ≤ (128 : ℝ) * (Kxy * Real.exp (-Real.pi * t)) :=
            mul_le_mul_of_nonneg_left hS (by linarith)
        _ = (128 : ℝ) * Kxy * Real.exp (-Real.pi * t) := by ring
    calc
      ‖(128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0)) -
          (192 : ℂ) * (u : ℂ)‖
          ≤ ‖(128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0))‖ +
              ‖(192 : ℂ) * (u : ℂ)‖ := norm_sub_le _ _
      _ ≤ (128 : ℝ) * Kxy * Real.exp (-Real.pi * t) + (192 : ℝ) * Real.exp (-Real.pi * t) :=
            add_le_add hsum' hu_term
      _ = ((128 : ℝ) * Kxy + 192) * Real.exp (-Real.pi * t) := by ring
  have hB :
      ‖(128 : ℂ) * (z * w) - (128 : ℂ)‖ ≤
        (128 : ℝ) * ((CH2 + CH4 + 112) * (Cinv3 + 2) + Cinv3) * Real.exp (-Real.pi * t) := by
    have hzww : z * w - 1 = (z - 1) * w + (w - 1) := by ring
    have hzw : ‖z * w - 1‖ ≤ ‖z - 1‖ * ‖w‖ + ‖w - 1‖ := by
      calc
        ‖z * w - 1‖ = ‖(z - 1) * w + (w - 1)‖ := by simp [hzww]
        _ ≤ ‖(z - 1) * w‖ + ‖w - 1‖ := norm_add_le _ _
        _ = ‖z - 1‖ * ‖w‖ + ‖w - 1‖ := by simp
    have hfac : (128 : ℂ) * (z * w) - (128 : ℂ) = (128 : ℂ) * (z * w - 1) := by ring
    have hn : ‖(128 : ℂ) * (z * w) - (128 : ℂ)‖ = (128 : ℝ) * ‖z * w - 1‖ := by
      rw [hfac]; simp
    rw [hn]
    have hz1' :
        ‖z - 1‖ * ‖w‖ ≤ ((CH2 + CH4 + 112) * Real.exp (-Real.pi * t)) * (Cinv3 + 2) := by
      have h0 : 0 ≤ (CH2 + CH4 + 112) * Real.exp (-Real.pi * t) :=
        mul_nonneg (by linarith [hCH2, hCH4]) (Real.exp_pos _).le
      exact mul_le_mul hz1 hw_bd (norm_nonneg _) h0
    grind only
  have hψI' : ψI.resToImagAxis t = (128 : ℂ) * (x * y + z * w) := by assumption
  calc
    ‖ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) - ((Real.exp (2 * π * t) : ℝ) : ℂ)‖
        = ‖ψI.resToImagAxis t - (144 : ℂ) - (e : ℂ)‖ := by simp [hres, e]
    _ = ‖(128 : ℂ) * (x * y + z * w) - (144 : ℂ) - (e : ℂ)‖ := by rw [hψI']
    _ = ‖(128 : ℂ) * (x * y + z * w) - (e : ℂ) - (144 : ℂ)‖ := by congr 1; ring
    _ = ‖((128 : ℂ) * (x * y) - (e : ℂ) - (16 : ℂ)) +
          ((128 : ℂ) * (z * w) - (128 : ℂ))‖ := by rw [hdecomp]
    _ ≤ ‖(128 : ℂ) * (x * y) - (e : ℂ) - (16 : ℂ)‖ + ‖(128 : ℂ) * (z * w) - (128 : ℂ)‖ :=
          norm_add_le _ _
    _ ≤ ((128 : ℝ) * ((Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2)) + 192) *
            Real.exp (-Real.pi * t) +
          (128 : ℝ) * ((CH2 + CH4 + 112) * (Cinv3 + 2) + Cinv3) * Real.exp (-Real.pi * t) :=
          add_le_add hA hB
    _ ≤ ((128 : ℝ) *
            (((Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2)) +
              ((CH2 + CH4 + 112) * (Cinv3 + 2) + Cinv3)) + 192) * Real.exp (-Real.pi * t) := by
          apply le_of_eq; ring

end

end MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation
