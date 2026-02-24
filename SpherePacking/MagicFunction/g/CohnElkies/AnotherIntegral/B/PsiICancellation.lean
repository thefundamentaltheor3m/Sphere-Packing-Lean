module
public import SpherePacking.MagicFunction.b.psi
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

lemma exp_mul_exp_eq (a b : ℝ) :
    Real.exp a * Real.exp b = Real.exp (a + b) := by
  simp [Real.exp_add]

lemma exp_two_pi_mul_exp_neg_two_pi (t : ℝ) :
    Real.exp (2 * Real.pi * t) * Real.exp (-(2 : ℝ) * Real.pi * t) = 1 := by
  simp [exp_mul_exp_eq]

lemma exp_two_pi_mul_exp_neg_three_pi (t : ℝ) :
    Real.exp (2 * Real.pi * t) * Real.exp (-(3 : ℝ) * Real.pi * t) =
      Real.exp (-Real.pi * t) := by
  have h := exp_mul_exp_eq (2 * Real.pi * t) (-(3 : ℝ) * Real.pi * t)
  rw [h]
  congr 1
  ring

lemma exp_neg_two_pi_le_exp_neg_pi {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(2 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) := by
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_pos, ht]

lemma exp_neg_three_pi_le_exp_neg_pi {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(3 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) := by
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_pos, ht]

lemma exp_neg_five_pi_le_exp_neg_pi {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(5 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) := by
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_pos, ht]

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
  -- These constants must be nonnegative since they bound norms.
  have nonneg_of_bound {C : ℝ} {x : ℂ} {a : ℝ} (h : ‖x‖ ≤ C * Real.exp a) : 0 ≤ C := by
    have h0 : 0 ≤ C * Real.exp a := le_trans (norm_nonneg x) h
    exact nonneg_of_mul_nonneg_left h0 (Real.exp_pos a)
  have hCsum : 0 ≤ Csum := nonneg_of_bound (hsum 1 le_rfl)
  have hCinv2 : 0 ≤ Cinv2 := nonneg_of_bound (hinv2 1 le_rfl)
  have hCinv3 : 0 ≤ Cinv3 := nonneg_of_bound (hinv3 1 le_rfl)
  have hCH2 : 0 ≤ CH2 := nonneg_of_bound (hH2 1 le_rfl)
  have hCH4 : 0 ≤ CH4 := nonneg_of_bound (hH4 1 le_rfl)
  -- A coarse constant; we do not optimize.
  refine ⟨(128 : ℝ) *
      (((Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2)) +
        ((CH2 + CH4 + 200) * (Cinv3 + 2) + Cinv3)) + 192, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht0' : 0 ≤ t := le_of_lt ht0
  have hres : ψI' ((Complex.I : ℂ) * (t : ℂ)) = ψI.resToImagAxis t :=
    psiI'_mul_I_eq_resToImagAxis t ht0
  have hψI := psiI_resToImagAxis_eq t ht0
  -- Abbreviations.
  set e : ℝ := Real.exp (2 * Real.pi * t)
  set u : ℝ := Real.exp (-(2 : ℝ) * Real.pi * t)
  set x : ℂ := H₃.resToImagAxis t + H₄.resToImagAxis t
  set y : ℂ := ((H₂.resToImagAxis t) ^ (2 : ℕ))⁻¹
  set z : ℂ := H₄.resToImagAxis t - H₂.resToImagAxis t
  set w : ℂ := ((H₃.resToImagAxis t) ^ (2 : ℕ))⁻¹
  set x0 : ℂ := (2 : ℂ) + (48 : ℂ) * (u : ℂ)
  set y0 : ℂ := ((e / 256 : ℝ) : ℂ) - ((1 / 32 : ℝ) : ℂ)
  have hx : ‖x - x0‖ ≤ Csum * Real.exp (-(3 : ℝ) * Real.pi * t) := by
    have := hsum t ht
    simpa [x, x0, u, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using this
  have hy : ‖y - y0‖ ≤ Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t) := by
    have := hinv2 t ht
    simpa [y, y0, e, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  have hw1 : ‖w - 1‖ ≤ Cinv3 * Real.exp (-Real.pi * t) := by
    have := hinv3 t ht
    simpa [w, sub_eq_add_neg] using this
  have hu_le : u ≤ Real.exp (-Real.pi * t) := by
    simpa [u] using exp_neg_two_pi_le_exp_neg_pi (t := t) ht0'
  have heu : e * u = 1 := by
    simpa [e, u] using exp_two_pi_mul_exp_neg_two_pi (t := t)
  -- Compute the main term for the `x*y` contribution.
  have hxy0_mainR :
      (128 : ℝ) * ((2 + 48 * u) * (e / 256 - 1 / 32)) = e + 16 - 192 * u := by
    -- `ring_nf` isolates a factor `(e*u)`, which we rewrite using `heu`.
    have heu' : u * e = 1 := by simpa [mul_comm] using heu
    ring_nf
    simp [heu']
    ring_nf
  have hxy0_main :
      (128 : ℂ) * (x0 * y0) = (e : ℂ) + (16 : ℂ) - (192 : ℂ) * (u : ℂ) := by
    -- `x0` and `y0` are real scalars in `ℂ`.
    have hcast :
        (128 : ℂ) * (x0 * y0) =
          ((128 : ℝ) * ((2 + 48 * u) * (e / 256 - 1 / 32)) : ℂ) := by
      simp [x0, y0]
    have hcastR :
        ((128 : ℝ) * ((2 + 48 * u) * (e / 256 - 1 / 32)) : ℂ) =
          ((e + 16 - 192 * u : ℝ) : ℂ) := by
      simpa using congrArg (fun r : ℝ => (r : ℂ)) hxy0_mainR
    calc
      (128 : ℂ) * (x0 * y0) =
          ((128 : ℝ) * ((2 + 48 * u) * (e / 256 - 1 / 32)) : ℂ) := hcast
      _ = ((e + 16 - 192 * u : ℝ) : ℂ) := hcastR
      _ = (e : ℂ) + (16 : ℂ) - (192 : ℂ) * (u : ℂ) := by
            simp [sub_eq_add_neg]
  -- Crude bounds needed for the error terms.
  have hx0_bound : ‖x0‖ ≤ 50 := by
    have hu1 : u ≤ 1 := by
      have : (-(2 : ℝ) * Real.pi * t) ≤ 0 := by nlinarith [Real.pi_pos, ht0']
      simpa [u] using (Real.exp_le_one_iff.2 this)
    have huNorm : ‖(48 : ℂ) * (u : ℂ)‖ = (48 : ℝ) * u := by
      have hu : 0 ≤ u := (Real.exp_pos _).le
      calc
        ‖(48 : ℂ) * (u : ℂ)‖ = ‖(48 : ℂ)‖ * ‖(u : ℂ)‖ := by simp
        _ = (48 : ℝ) * |u| := by simp
        _ = (48 : ℝ) * u := by simp [abs_of_nonneg hu]
    have hx0_le : ‖x0‖ ≤ 2 + 48 * u := by
      have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by simp
      calc
        ‖x0‖ = ‖(2 : ℂ) + (48 : ℂ) * (u : ℂ)‖ := by simp [x0]
        _ ≤ ‖(2 : ℂ)‖ + ‖(48 : ℂ) * (u : ℂ)‖ := norm_add_le _ _
        _ = 2 + 48 * u := by
              rw [h2, huNorm]
    have hx0_le' : (2 : ℝ) + 48 * u ≤ 50 := by nlinarith [hu1]
    exact le_trans hx0_le hx0_le'
  have hy0_bound : ‖y0‖ ≤ (e / 256) + (1 / 32) := by
    have h := norm_sub_le ((e / 256 : ℝ) : ℂ) ((1 / 32 : ℝ) : ℂ)
    have he : 0 ≤ e := by
      -- `e = exp(2πt) ≥ 0`.
      simpa [e] using (Real.exp_pos (2 * Real.pi * t)).le
    simpa [y0, RCLike.norm_ofReal, Real.norm_eq_abs,
      abs_of_nonneg he,
      abs_of_nonneg (by positivity : 0 ≤ (1 / 32 : ℝ))] using h
  have hz1 :
      ‖z - 1‖ ≤ (CH2 + CH4 + 200) * Real.exp (-Real.pi * t) := by
    -- Bound `‖H₂‖` from its two-term expansion.
    have hH2' := hH2 t ht
    have hH2_bd : ‖H₂.resToImagAxis t‖ ≤ (CH2 + 100) * Real.exp (-Real.pi * t) := by
      have hle3 : Real.exp (-(3 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
        exp_neg_three_pi_le_exp_neg_pi (t := t) ht0'
      have hle5 : Real.exp (-(5 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
        exp_neg_five_pi_le_exp_neg_pi (t := t) ht0'
      have hmain :
          ‖(16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
              (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
            ≤ (80 : ℝ) * Real.exp (-Real.pi * t) := by
        have htri :=
          norm_add_le
            ((16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ))
            ((64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ))
        calc
          ‖(16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
              (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
              ≤ ‖(16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖ +
                  ‖(64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖ := htri
          _ =
              (16 : ℝ) * Real.exp (-Real.pi * t) +
                (64 : ℝ) * Real.exp (-(3 : ℝ) * Real.pi * t) := by
                simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
          _ ≤
              (16 : ℝ) * Real.exp (-Real.pi * t) +
                (64 : ℝ) * Real.exp (-Real.pi * t) := by
                gcongr
          _ = (80 : ℝ) * Real.exp (-Real.pi * t) := by ring
      have : ‖H₂.resToImagAxis t‖ ≤ CH2 * Real.exp (-(5 : ℝ) * Real.pi * t) +
          (80 : ℝ) * Real.exp (-Real.pi * t) := by
        -- `H₂ = (H₂ - main) + main`.
        have : H₂.resToImagAxis t =
            (H₂.resToImagAxis t - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
                - (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)) +
              ((16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
                (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)) := by
          ring
        have htri := norm_add_le
          (H₂.resToImagAxis t - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
              - (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ))
          ((16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
            (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ))
        have herr :
            ‖H₂.resToImagAxis t - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
                - (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖
              ≤ CH2 * Real.exp (-(5 : ℝ) * Real.pi * t) := hH2'
        have h0 :
            ‖H₂.resToImagAxis t‖ ≤
              ‖H₂.resToImagAxis t - (16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
                    - (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖ +
                ‖(16 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
                    (64 : ℂ) * (Real.exp (-(3 : ℝ) * Real.pi * t) : ℂ)‖ := by
          -- Rewrite `H₂` as `err + main` and apply triangle inequality.
          simpa [this] using htri
        exact le_trans h0 (add_le_add herr hmain)
      have hterm :
          CH2 * Real.exp (-(5 : ℝ) * Real.pi * t) ≤ CH2 * Real.exp (-Real.pi * t) := by
        -- Multiply `exp(-5πt) ≤ exp(-πt)` by the nonnegative constant `CH2`.
        have := mul_le_mul_of_nonneg_left hle5 hCH2
        simpa [mul_assoc] using this
      have h80 :
          (80 : ℝ) * Real.exp (-Real.pi * t) ≤ (100 : ℝ) * Real.exp (-Real.pi * t) := by
        simpa using mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      calc
        ‖H₂.resToImagAxis t‖ ≤
            CH2 * Real.exp (-(5 : ℝ) * Real.pi * t) + (80 : ℝ) * Real.exp (-Real.pi * t) := this
        _ ≤ CH2 * Real.exp (-Real.pi * t) + (100 : ℝ) * Real.exp (-Real.pi * t) := by
              exact add_le_add hterm h80
        _ = (CH2 + 100) * Real.exp (-Real.pi * t) := by ring
    -- Bound `‖H₄ - 1‖` from its two-term expansion.
    have hH4' := hH4 t ht
    have hH4_bd : ‖H₄.resToImagAxis t - 1‖ ≤ (CH4 + 100) * Real.exp (-Real.pi * t) := by
      have hle2 : Real.exp (-(2 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
        exp_neg_two_pi_le_exp_neg_pi (t := t) ht0'
      have hle3 : Real.exp (-(3 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
        exp_neg_three_pi_le_exp_neg_pi (t := t) ht0'
      have herr :
          ‖H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
              - (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
            ≤ CH4 * Real.exp (-(3 : ℝ) * Real.pi * t) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hH4'
      have htri :=
        norm_add_le
          (H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
              - (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
          (-(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
              (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
      have hmain :
          ‖-(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
              (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
            ≤ (40 : ℝ) * Real.exp (-Real.pi * t) := by
        have htri' :=
          norm_add_le
            (-(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ))
            ((24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ))
        calc
          ‖-(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
              (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖
              ≤ ‖-(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)‖ +
                  ‖(24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ := htri'
          _ =
              (8 : ℝ) * Real.exp (-Real.pi * t) +
                (24 : ℝ) * Real.exp (-(2 : ℝ) * Real.pi * t) := by
                simp [abs_of_nonneg (Real.exp_pos _).le, -Complex.ofReal_exp]
          _ ≤
              (8 : ℝ) * Real.exp (-Real.pi * t) +
                (24 : ℝ) * Real.exp (-Real.pi * t) := by
                gcongr
          _ = (32 : ℝ) * Real.exp (-Real.pi * t) := by ring
          _ ≤ (40 : ℝ) * Real.exp (-Real.pi * t) := by
                gcongr
                linarith
      have : ‖H₄.resToImagAxis t - 1‖ ≤
          CH4 * Real.exp (-(3 : ℝ) * Real.pi * t) + (40 : ℝ) * Real.exp (-Real.pi * t) := by
        -- `H₄ - 1 = (err) + (main)`.
        have : H₄.resToImagAxis t - 1 =
            (H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
                - (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)) +
              (-(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
                (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)) := by
          ring
        have h0 :
            ‖H₄.resToImagAxis t - 1‖ ≤
              ‖H₄.resToImagAxis t - (1 : ℂ) + (8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ)
                    - (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ +
                ‖-(8 : ℂ) * (Real.exp (-Real.pi * t) : ℂ) +
                    (24 : ℂ) * (Real.exp (-(2 : ℝ) * Real.pi * t) : ℂ)‖ := by
          simpa [this] using htri
        exact le_trans h0 (add_le_add herr hmain)
      have hterm :
          CH4 * Real.exp (-(3 : ℝ) * Real.pi * t) ≤ CH4 * Real.exp (-Real.pi * t) := by
        have := mul_le_mul_of_nonneg_left hle3 hCH4
        simpa [mul_assoc] using this
      have h40 :
          (40 : ℝ) * Real.exp (-Real.pi * t) ≤ (100 : ℝ) * Real.exp (-Real.pi * t) := by
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      calc
        ‖H₄.resToImagAxis t - 1‖ ≤
            CH4 * Real.exp (-(3 : ℝ) * Real.pi * t) + (40 : ℝ) * Real.exp (-Real.pi * t) := this
        _ ≤ CH4 * Real.exp (-Real.pi * t) + (100 : ℝ) * Real.exp (-Real.pi * t) := by
              exact add_le_add hterm h40
        _ = (CH4 + 100) * Real.exp (-Real.pi * t) := by ring
    -- Combine: `z - 1 = (H₄ - 1) - H₂`.
    have htri := norm_sub_le (H₄.resToImagAxis t - 1) (H₂.resToImagAxis t)
    have hz :
        z - 1 = (H₄.resToImagAxis t - 1) - H₂.resToImagAxis t := by
      dsimp [z]
      ring
    -- Triangle inequality + previously established bounds.
    calc
      ‖z - 1‖ = ‖(H₄.resToImagAxis t - 1) - H₂.resToImagAxis t‖ := by simp [hz]
      _ ≤ ‖H₄.resToImagAxis t - 1‖ + ‖H₂.resToImagAxis t‖ := htri
      _ ≤ (CH4 + 100) * Real.exp (-Real.pi * t) + (CH2 + 100) * Real.exp (-Real.pi * t) := by
            exact add_le_add hH4_bd hH2_bd
      _ = (CH2 + CH4 + 200) * Real.exp (-Real.pi * t) := by ring
  have hw_bd : ‖w‖ ≤ Cinv3 + 2 := by
    have htri := norm_add_le (w - 1) (1 : ℂ)
    have hw : w = (w - 1) + 1 := by ring
    have hexp_le : Real.exp (-Real.pi * t) ≤ 1 := by
      have : (-Real.pi * t) ≤ 0 := by nlinarith [Real.pi_pos, ht0']
      exact (Real.exp_le_one_iff).2 this
    have hw_le : ‖w‖ ≤ Cinv3 * Real.exp (-Real.pi * t) + 1 := by
      have hsum : ‖w - 1‖ + ‖(1 : ℂ)‖ ≤ Cinv3 * Real.exp (-Real.pi * t) + 1 := by
        simpa using add_le_add hw1 (le_of_eq (by simp : ‖(1 : ℂ)‖ = (1 : ℝ)))
      calc
        ‖w‖ = ‖(w - 1) + 1‖ := by
              exact congrArg (fun z : ℂ => ‖z‖) hw
        _ ≤ ‖w - 1‖ + ‖(1 : ℂ)‖ := htri
        _ ≤ Cinv3 * Real.exp (-Real.pi * t) + 1 := hsum
    have hterm : Cinv3 * Real.exp (-Real.pi * t) ≤ Cinv3 := by
      simpa [mul_one] using (mul_le_mul_of_nonneg_left hexp_le hCinv3)
    calc
      ‖w‖ ≤ Cinv3 * Real.exp (-Real.pi * t) + 1 := hw_le
      _ ≤ Cinv3 + 1 := by
        have h' := add_le_add_left hterm 1
        simpa [add_assoc, add_left_comm, add_comm] using h'
      _ ≤ Cinv3 + 2 := by linarith
  -- Now bound the full `ψI` expression.
  have hdecomp :
      (128 : ℂ) * (x * y + z * w) - (e : ℂ) - (144 : ℂ) =
        ((128 : ℂ) * (x * y) - (e : ℂ) - (16 : ℂ)) +
          ((128 : ℂ) * (z * w) - (128 : ℂ)) := by
    ring
  have hA :
      ‖(128 : ℂ) * (x * y) - (e : ℂ) - (16 : ℂ)‖ ≤
        ((128 : ℝ) * ((Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2)) + 192) *
          Real.exp (-Real.pi * t) := by
    -- Expand around the model `x0*y0`.
    have hx' : ‖x - x0‖ ≤ Csum * Real.exp (-(3 : ℝ) * Real.pi * t) := hx
    have hy' : ‖y - y0‖ ≤ Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t) := hy
    have hle2 : Real.exp (-(2 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
      exp_neg_two_pi_le_exp_neg_pi (t := t) ht0'
    have hle3 : Real.exp (-(3 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
      exp_neg_three_pi_le_exp_neg_pi (t := t) ht0'
    have hle5 : Real.exp (-(5 : ℝ) * Real.pi * t) ≤ Real.exp (-Real.pi * t) :=
      exp_neg_five_pi_le_exp_neg_pi (t := t) ht0'
    have hxdy :
        ‖(x - x0) * y0‖ ≤ (Csum + Csum / 256) * Real.exp (-Real.pi * t) := by
      have hy0' : ‖y0‖ ≤ (e / 256) + 1 := by
        refine le_trans hy0_bound ?_
        linarith
      have hb0 : 0 ≤ Csum * Real.exp (-(3 : ℝ) * Real.pi * t) :=
        mul_nonneg hCsum (Real.exp_pos _).le
      have h1 := norm_mul_le_of_le hx hy0'
      have hE :
          (e / 256) * Real.exp (-(3 : ℝ) * Real.pi * t) =
            (1 / 256) * Real.exp (-Real.pi * t) := by
        have he : e * Real.exp (-(3 : ℝ) * Real.pi * t) = Real.exp (-Real.pi * t) := by
          simpa [e] using exp_two_pi_mul_exp_neg_three_pi (t := t)
        calc
          (e / 256) * Real.exp (-(3 : ℝ) * Real.pi * t)
              = (e * Real.exp (-(3 : ℝ) * Real.pi * t)) * (256 : ℝ)⁻¹ := by
                  simp [div_eq_mul_inv, mul_assoc, mul_comm]
              _ = Real.exp (-Real.pi * t) * (256 : ℝ)⁻¹ := by
                  rw [he]
              _ = (1 / 256) * Real.exp (-Real.pi * t) := by
                  simp [one_div, mul_comm]
      have hterm3 : Csum * Real.exp (-(3 : ℝ) * Real.pi * t) ≤ Csum * Real.exp (-Real.pi * t) := by
        have := mul_le_mul_of_nonneg_left hle3 hCsum
        simpa [mul_assoc] using this
      have hfirst :
          (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) * (e / 256) =
            (Csum / 256) * Real.exp (-Real.pi * t) := by
        calc
          (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) * (e / 256)
              = Csum * ((e / 256) * Real.exp (-(3 : ℝ) * Real.pi * t)) := by ring
              _ = Csum * ((1 / 256) * Real.exp (-Real.pi * t)) := by rw [hE]
              _ = (Csum / 256) * Real.exp (-Real.pi * t) := by
                  simp [div_eq_mul_inv, mul_comm, mul_assoc]
      calc
        ‖(x - x0) * y0‖ ≤ (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) * ((e / 256) + 1) := h1
        _ = (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) * (e / 256) +
              (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) := by
              simp [mul_add]
        _ =
            (Csum / 256) * Real.exp (-Real.pi * t) +
              (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) := by rw [hfirst]
        _ ≤ (Csum / 256) * Real.exp (-Real.pi * t) + (Csum * Real.exp (-Real.pi * t)) :=
              (add_le_add_iff_left (Csum / 256 * rexp (-π * t))).mpr hterm3
        _ = (Csum + Csum / 256) * Real.exp (-Real.pi * t) := by ring
    have hx0dy :
        ‖x0 * (y - y0)‖ ≤ (50 * Cinv2) * Real.exp (-Real.pi * t) := by
      have hmul : ‖x0 * (y - y0)‖ ≤ ‖x0‖ * ‖y - y0‖ := by simp
      have h1 : ‖x0‖ * ‖y - y0‖ ≤ 50 * ‖y - y0‖ := by
        exact mul_le_mul_of_nonneg_right hx0_bound (norm_nonneg _)
      have h2 : 50 * ‖y - y0‖ ≤ 50 * (Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t)) := by
        have h50 : 0 ≤ (50 : ℝ) := by linarith
        exact mul_le_mul_of_nonneg_left hy' h50
      have h3 :
          50 * (Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t)) ≤
            (50 * Cinv2) * Real.exp (-Real.pi * t) := by
        have h0 : 0 ≤ 50 * Cinv2 := mul_nonneg (by linarith) hCinv2
        have h' :
            (50 * Cinv2) * Real.exp (-(2 : ℝ) * Real.pi * t) ≤
              (50 * Cinv2) * Real.exp (-Real.pi * t) :=
          mul_le_mul_of_nonneg_left hle2 h0
        simpa [mul_assoc] using h'
      have h' : ‖x0 * (y - y0)‖ ≤ 50 * (Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t)) := by
        exact le_trans (le_trans hmul h1) h2
      exact le_trans h' h3
    have hdxdy :
        ‖(x - x0) * (y - y0)‖ ≤ (Csum * Cinv2) * Real.exp (-Real.pi * t) := by
      have hmul : ‖(x - x0) * (y - y0)‖ = ‖x - x0‖ * ‖y - y0‖ := by
        simp
      have hb0 : 0 ≤ Csum * Real.exp (-(3 : ℝ) * Real.pi * t) :=
        mul_nonneg hCsum (Real.exp_pos _).le
      have h1 :
          ‖x - x0‖ * ‖y - y0‖ ≤
            (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) *
              (Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t)) := by
        exact mul_le_mul hx' hy' (norm_nonneg _) hb0
      have hExp :
          Real.exp (-(3 : ℝ) * Real.pi * t) * Real.exp (-(2 : ℝ) * Real.pi * t) =
            Real.exp (-(5 : ℝ) * Real.pi * t) := by
        have h := exp_mul_exp_eq (-(3 : ℝ) * Real.pi * t) (-(2 : ℝ) * Real.pi * t)
        rw [h]
        congr 1
        ring
      have h2 :
          (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) *
              (Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t)) =
            (Csum * Cinv2) * Real.exp (-(5 : ℝ) * Real.pi * t) := by
        -- reassociate and fold `exp(-3πt) * exp(-2πt)` into `exp(-5πt)`
        calc
          (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) *
              (Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t)) =
              (Csum * Cinv2) *
                (Real.exp (-(3 : ℝ) * Real.pi * t) * Real.exp (-(2 : ℝ) * Real.pi * t)) := by
                ring
          _ = (Csum * Cinv2) * Real.exp (-(5 : ℝ) * Real.pi * t) := by
                rw [hExp]
      have hterm :
          (Csum * Cinv2) * Real.exp (-(5 : ℝ) * Real.pi * t) ≤
            (Csum * Cinv2) * Real.exp (-Real.pi * t) := by
        have h0 : 0 ≤ Csum * Cinv2 := mul_nonneg hCsum hCinv2
        exact mul_le_mul_of_nonneg_left hle5 h0
      calc
        ‖(x - x0) * (y - y0)‖ = ‖x - x0‖ * ‖y - y0‖ := hmul
        _ ≤
            (Csum * Real.exp (-(3 : ℝ) * Real.pi * t)) *
              (Cinv2 * Real.exp (-(2 : ℝ) * Real.pi * t)) := h1
        _ = (Csum * Cinv2) * Real.exp (-(5 : ℝ) * Real.pi * t) := h2
        _ ≤ (Csum * Cinv2) * Real.exp (-Real.pi * t) := hterm
    have hu_term : ‖(192 : ℂ) * (u : ℂ)‖ ≤ (192 : ℝ) * Real.exp (-Real.pi * t) := by
      have hu0 : 0 ≤ u := by positivity
      have habs : |u| ≤ Real.exp (-Real.pi * t) := by
        simpa [abs_of_nonneg hu0] using hu_le
      have hEq : ‖(192 : ℂ) * (u : ℂ)‖ = (192 : ℝ) * |u| := by
        simp
      calc
        ‖(192 : ℂ) * (u : ℂ)‖ = (192 : ℝ) * |u| := hEq
        _ ≤ (192 : ℝ) * Real.exp (-Real.pi * t) := by
              exact mul_le_mul_of_nonneg_left habs (by linarith)
    -- `x*y - x0*y0 = (x-x0)*y0 + x0*(y-y0) + (x-x0)*(y-y0)`.
    have hsplit :
        (128 : ℂ) * (x * y) - (e : ℂ) - (16 : ℂ) =
          (128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0)) -
            (192 : ℂ) * (u : ℂ) := by
      have hmain : (e : ℂ) + (16 : ℂ) = (128 : ℂ) * (x0 * y0) + (192 : ℂ) * (u : ℂ) := by
        -- rearrange `hxy0_main`
        have h' :=
          congrArg (fun z : ℂ => z + (192 : ℂ) * (u : ℂ)) hxy0_main
        -- `... - 192*u + 192*u = ...`
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'.symm
      have hxy :
          x * y - x0 * y0 = (x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0) := by
        ring
      calc
        (128 : ℂ) * (x * y) - (e : ℂ) - (16 : ℂ)
            = (128 : ℂ) * (x * y) - ((e : ℂ) + (16 : ℂ)) := by ring
        _ = (128 : ℂ) * (x * y) - ((128 : ℂ) * (x0 * y0) + (192 : ℂ) * (u : ℂ)) := by
              simp [hmain]
        _ = (128 : ℂ) * (x * y - x0 * y0) - (192 : ℂ) * (u : ℂ) := by ring
        _ = (128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0)) -
              (192 : ℂ) * (u : ℂ) := by
              simp [hxy]
    -- Bound the RHS using triangle inequality.
    rw [hsplit]
    have htri :=
      norm_sub_le
        ((128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0)))
        ((192 : ℂ) * (u : ℂ))
    -- Bundle the three error terms.
    set Kxy : ℝ := (Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2)
    have hsum' :
        ‖(128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0))‖
          ≤ (128 : ℝ) * Kxy * Real.exp (-Real.pi * t) := by
      let a : ℂ := (x - x0) * y0
      let b : ℂ := x0 * (y - y0)
      let c : ℂ := (x - x0) * (y - y0)
      have htri' : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
        have hab : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
        have hab' : ‖a + b‖ + ‖c‖ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by
          exact add_le_add hab le_rfl
        calc
          ‖a + b + c‖ = ‖(a + b) + c‖ := by simp [add_assoc]
          _ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
          _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := hab'
          _ = ‖a‖ + ‖b‖ + ‖c‖ := by simp [add_assoc]
      have ha : ‖a‖ ≤ (Csum + Csum / 256) * Real.exp (-Real.pi * t) := by
        simpa [a] using hxdy
      have hb : ‖b‖ ≤ (50 * Cinv2) * Real.exp (-Real.pi * t) := by
        simpa [b] using hx0dy
      have hc : ‖c‖ ≤ (Csum * Cinv2) * Real.exp (-Real.pi * t) := by
        simpa [c] using hdxdy
      have hsum0 : ‖a + b + c‖ ≤ Kxy * Real.exp (-Real.pi * t) := by
        have hab : ‖a‖ + ‖b‖ ≤
            (Csum + Csum / 256) * Real.exp (-Real.pi * t) +
              (50 * Cinv2) * Real.exp (-Real.pi * t) :=
          add_le_add ha hb
        have habc :
            (‖a‖ + ‖b‖) + ‖c‖ ≤
                ((Csum + Csum / 256) * Real.exp (-Real.pi * t) +
                      (50 * Cinv2) * Real.exp (-Real.pi * t)) +
                    (Csum * Cinv2) * Real.exp (-Real.pi * t) := by
          exact add_le_add hab hc
        calc
          ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := htri'
          _ = (‖a‖ + ‖b‖) + ‖c‖ := by simp [add_assoc]
          _ ≤
              ((Csum + Csum / 256) * Real.exp (-Real.pi * t) +
                    (50 * Cinv2) * Real.exp (-Real.pi * t)) +
                  (Csum * Cinv2) * Real.exp (-Real.pi * t) := habc
          _ = Kxy * Real.exp (-Real.pi * t) := by
                simp [Kxy]
                ring
      have hS :
          ‖(x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0)‖ ≤
            Kxy * Real.exp (-Real.pi * t) := by
        simpa [a, b, c, add_assoc] using hsum0
      have h128 : 0 ≤ (128 : ℝ) := by linarith
      calc
        ‖(128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0))‖
            = (128 : ℝ) * ‖(x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0)‖ := by
                simp
        _ ≤ (128 : ℝ) * (Kxy * Real.exp (-Real.pi * t)) := by
              exact mul_le_mul_of_nonneg_left hS h128
        _ = (128 : ℝ) * Kxy * Real.exp (-Real.pi * t) := by ring
    have hfinal :
        ‖(128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0)) -
            (192 : ℂ) * (u : ℂ)‖
          ≤ ((128 : ℝ) * Kxy + 192) * Real.exp (-Real.pi * t) := by
      calc
        ‖(128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0)) -
              (192 : ℂ) * (u : ℂ)‖
            ≤ ‖(128 : ℂ) * ((x - x0) * y0 + x0 * (y - y0) + (x - x0) * (y - y0))‖ +
                ‖(192 : ℂ) * (u : ℂ)‖ := htri
        _ ≤ (128 : ℝ) * Kxy * Real.exp (-Real.pi * t) + (192 : ℝ) * Real.exp (-Real.pi * t) := by
              exact add_le_add hsum' hu_term
        _ = ((128 : ℝ) * Kxy + 192) * Real.exp (-Real.pi * t) := by ring
    simpa [Kxy] using hfinal
  have hB :
      ‖(128 : ℂ) * (z * w) - (128 : ℂ)‖ ≤
        (128 : ℝ) * ((CH2 + CH4 + 200) * (Cinv3 + 2) + Cinv3) * Real.exp (-Real.pi * t) :=
    by
      have hzw :
          ‖z * w - 1‖ ≤ ‖z - 1‖ * ‖w‖ + ‖w - 1‖ := by
        have hzww : z * w - 1 = (z - 1) * w + (w - 1) := by ring
        calc
          ‖z * w - 1‖ = ‖(z - 1) * w + (w - 1)‖ := by simp [hzww]
          _ ≤ ‖(z - 1) * w‖ + ‖w - 1‖ := norm_add_le _ _
          _ = ‖z - 1‖ * ‖w‖ + ‖w - 1‖ := by simp
      have hn :
        ‖(128 : ℂ) * (z * w) - (128 : ℂ)‖ = (128 : ℝ) * ‖z * w - 1‖ := by
        have hfac : (128 : ℂ) * (z * w) - (128 : ℂ) = (128 : ℂ) * (z * w - 1) := by ring
        calc
          ‖(128 : ℂ) * (z * w) - (128 : ℂ)‖ = ‖(128 : ℂ) * (z * w - 1)‖ := by simp [hfac]
          _ = ‖(128 : ℂ)‖ * ‖z * w - 1‖ := by simp
          _ = (128 : ℝ) * ‖z * w - 1‖ := by simp
      rw [hn]
      have hz1' :
          ‖z - 1‖ * ‖w‖ ≤ ((CH2 + CH4 + 200) * Real.exp (-Real.pi * t)) * (Cinv3 + 2) := by
        have h0 : 0 ≤ (CH2 + CH4 + 200) * Real.exp (-Real.pi * t) := by
          have h' : 0 ≤ CH2 + CH4 + 200 := by linarith [hCH2, hCH4]
          exact mul_nonneg h' (Real.exp_pos _).le
        exact mul_le_mul hz1 hw_bd (norm_nonneg _) h0
      have hzwn :
          ‖z * w - 1‖ ≤ ((CH2 + CH4 + 200) * Real.exp (-Real.pi * t)) * (Cinv3 + 2) +
              Cinv3 * Real.exp (-Real.pi * t) := by
        exact le_trans hzw (add_le_add hz1' hw1)
      have h128 : 0 ≤ (128 : ℝ) := by linarith
      have hmul :
          (128 : ℝ) * ‖z * w - 1‖ ≤
            (128 : ℝ) *
              (((CH2 + CH4 + 200) * Real.exp (-Real.pi * t)) * (Cinv3 + 2) +
                    Cinv3 * Real.exp (-Real.pi * t)) :=
        mul_le_mul_of_nonneg_left hzwn h128
      -- factor out `exp(-πt)`
      have hEq :
          (((CH2 + CH4 + 200) * Real.exp (-Real.pi * t)) * (Cinv3 + 2) +
                Cinv3 * Real.exp (-Real.pi * t)) =
            ((CH2 + CH4 + 200) * (Cinv3 + 2) + Cinv3) * Real.exp (-Real.pi * t) := by
        ring
      -- conclude
      have hEq' :
          (128 : ℝ) *
              (((CH2 + CH4 + 200) * Real.exp (-Real.pi * t)) * (Cinv3 + 2) +
                    Cinv3 * Real.exp (-Real.pi * t)) =
            (128 : ℝ) * (((CH2 + CH4 + 200) * (Cinv3 + 2) + Cinv3) * Real.exp (-Real.pi * t)) := by
        simpa using congrArg (fun r : ℝ => (128 : ℝ) * r) hEq
      have hmul' :
          (128 : ℝ) * ‖z * w - 1‖ ≤
            (128 : ℝ) * (((CH2 + CH4 + 200) * (Cinv3 + 2) + Cinv3) * Real.exp (-Real.pi * t)) :=
        le_of_le_of_eq hmul hEq'
      simpa [mul_assoc] using hmul'
  -- Finish with `ψI = 128*(x*y + z*w)` and triangle inequality.
  have hψI' : ψI.resToImagAxis t = (128 : ℂ) * (x * y + z * w) := by
    -- rewrite divisions into inverses, and match `x*y`/`z*w`
    have hψI'' :
        ψI.resToImagAxis t =
          (128 : ℂ) *
            (x * ((H₂.resToImagAxis t) ^ (2 : ℕ))⁻¹ +
              z * ((H₃.resToImagAxis t) ^ (2 : ℕ))⁻¹) := by
      simpa [div_eq_mul_inv, mul_add, add_mul, mul_assoc] using hψI
    simpa [y, w, mul_add, add_mul, mul_assoc, add_assoc] using hψI''
  calc
    ‖ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) - ((Real.exp (2 * π * t) : ℝ) : ℂ)‖
        = ‖ψI.resToImagAxis t - (144 : ℂ) - (e : ℂ)‖ := by simp [hres, e]
    _ = ‖(128 : ℂ) * (x * y + z * w) - (144 : ℂ) - (e : ℂ)‖ := by
          have h' :
              ψI.resToImagAxis t - (144 : ℂ) - (e : ℂ) =
                (128 : ℂ) * (x * y + z * w) - (144 : ℂ) - (e : ℂ) := by
            simpa [hψI']
          simpa using congrArg (fun z : ℂ => ‖z‖) h'
    _ = ‖(128 : ℂ) * (x * y + z * w) - (e : ℂ) - (144 : ℂ)‖ := by
          congr 1
          ring
    _ = ‖((128 : ℂ) * (x * y) - (e : ℂ) - (16 : ℂ)) +
          ((128 : ℂ) * (z * w) - (128 : ℂ))‖ := by
          simpa using congrArg (fun z : ℂ => ‖z‖) hdecomp
    _ ≤ ‖(128 : ℂ) * (x * y) - (e : ℂ) - (16 : ℂ)‖ + ‖(128 : ℂ) * (z * w) - (128 : ℂ)‖ :=
          norm_add_le _ _
    _ ≤ ((128 : ℝ) * ((Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2)) + 192) *
            Real.exp (-Real.pi * t) +
          (128 : ℝ) * ((CH2 + CH4 + 200) * (Cinv3 + 2) + Cinv3) * Real.exp (-Real.pi * t) := by
          exact add_le_add hA hB
    _ ≤ ((128 : ℝ) *
            (((Csum + Csum / 256) + (50 * Cinv2) + (Csum * Cinv2)) +
              ((CH2 + CH4 + 200) * (Cinv3 + 2) + Cinv3)) + 192) * Real.exp (-Real.pi * t) := by
          -- this is an equality, but `≤` suffices
          refine le_of_eq ?_
          ring

end

end MagicFunction.g.CohnElkies.AnotherIntegral.B.PsiICancellation
