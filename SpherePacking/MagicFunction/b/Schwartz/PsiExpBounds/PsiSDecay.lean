module
public import SpherePacking.MagicFunction.b.PsiBounds

import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Topology.Order.Compact
import SpherePacking.ForMathlib.DerivHelpers

/-!
# Exponential decay of `ψS` on the imaginary axis

Derives `‖H₂(it)‖ ≤ C * exp(-π t)` for `t ≥ 1`, then combines that exponential bound with the
algebraic factorization of `ψS` to obtain `‖ψS(it)‖ ≤ C * exp(-π t)` for `t ≥ 1`.

## Main statement
* `exists_bound_norm_ψS_resToImagAxis_exp_Ici_one`
-/

namespace MagicFunction.b.PsiBounds.PsiExpBounds

noncomputable section

open scoped Topology UpperHalfPlane
open Complex Real Filter Topology UpperHalfPlane Set HurwitzKernelBounds

lemma norm_Θ₂_resToImagAxis_le (t : ℝ) (ht : 0 < t) :
    ‖Θ₂.resToImagAxis t‖ ≤
      (2 * rexp (-π * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - rexp (-π * t)) := by
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hτ : (τ : ℂ) = (Complex.I : ℂ) * t := rfl
  have hΘ (n : ℤ) : ‖Θ₂_term n τ‖ = f_int 0 (1 / 2 : ℝ) t n := by
    have hnorm_pref : ‖cexp (π * (Complex.I : ℂ) * (τ : ℂ) / 4)‖ = rexp (-π * (t / 4)) := by
      simp [Complex.norm_exp, hτ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have hnorm_core :
        ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ =
          rexp (-(π * (n : ℝ) ^ 2 * t) - 2 * π * (n : ℝ) * (t / 2)) := by
      rw [show ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ =
        rexp (-π * (n : ℝ) ^ 2 * t - 2 * π * (n : ℝ) * (t / 2)) by
          simpa [hτ] using norm_jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)]
      ring_nf
    simp [HurwitzKernelBounds.f_int, pow_zero, one_mul,
      show ‖Θ₂_term n τ‖ = rexp (-π * (((n : ℝ) + (1 / 2)) ^ 2) * t) from
        calc ‖Θ₂_term n τ‖ =
                ‖cexp (π * (Complex.I : ℂ) * (τ : ℂ) / 4)‖ *
                  ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ := by
                  simp [Θ₂_term_as_jacobiTheta₂_term, hτ, mul_assoc]
          _ = rexp (-π * (((n : ℝ) + (1 / 2)) ^ 2) * t) := by
                  rw [hnorm_pref, hnorm_core, ← Real.exp_add]; congr 1; ring]
  have hsumm : Summable (fun n : ℤ => ‖Θ₂_term n τ‖) :=
    (summable_f_int 0 (1 / 2 : ℝ) ht).congr (fun n => by simpa using (hΘ n).symm)
  have hbd_nat' :
      F_nat 0 (1 / 2 : ℝ) t ≤ rexp (-π * ((1 / 2 : ℝ) ^ 2) * t) / (1 - rexp (-π * t)) := by
    have hnonneg' : 0 ≤ F_nat 0 (2⁻¹ : ℝ) t :=
      tsum_nonneg (fun n : ℕ => by simp only [HurwitzKernelBounds.f_nat, pow_zero]; positivity)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg'] using
      (F_nat_zero_le (a := (1 / 2 : ℝ)) (ha := by norm_num) ht)
  calc ‖Θ₂.resToImagAxis t‖
      ≤ ∑' n : ℤ, ‖Θ₂_term n τ‖ := by
        simpa [ResToImagAxis, Θ₂, τ, ht] using (norm_tsum_le_tsum_norm hsumm)
    _ = F_int 0 ((1 / 2 : ℝ) : UnitAddCircle) t := by
        simpa [HurwitzKernelBounds.F_int] using tsum_congr fun n => by simpa using hΘ n
    _ = F_nat 0 (1 / 2 : ℝ) t + F_nat 0 (1 / 2 : ℝ) t := by
        simpa [show (1 : ℝ) - (2⁻¹ : ℝ) = (2⁻¹ : ℝ) by norm_num] using
          F_int_eq_of_mem_Icc 0 (a := (1 / 2 : ℝ)) ⟨by norm_num, by norm_num⟩ ht
    _ ≤ _ := by rw [show (2 * rexp (-π * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - rexp (-π * t)) =
                    rexp (-π * ((1 / 2 : ℝ) ^ 2) * t) / (1 - rexp (-π * t)) +
                    rexp (-π * ((1 / 2 : ℝ) ^ 2) * t) / (1 - rexp (-π * t)) from by ring]; gcongr

/-- Exponential decay bound for `H₂` on the positive imaginary axis. -/
public lemma exists_bound_norm_H₂_resToImagAxis_exp_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖H₂.resToImagAxis t‖ ≤ C * rexp (-π * t) := by
  let Cθ : ℝ := (2 : ℝ) / (1 - rexp (-π))
  refine ⟨Cθ ^ 4, fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hΘ2 : ‖Θ₂.resToImagAxis t‖ ≤ Cθ * rexp (-π * (t / 4)) := by
    have hden_pos : 0 < (1 - rexp (-π : ℝ)) :=
      sub_pos.2 (Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos]))
    calc
      ‖Θ₂.resToImagAxis t‖ ≤
          (2 * rexp (-π * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - rexp (-π * t)) :=
            norm_Θ₂_resToImagAxis_le t ht0
      _ = (2 * rexp (-π * (t / 4))) / (1 - rexp (-π * t)) := by
            rw [show -π * ((1 / 2 : ℝ) ^ 2) * t = -π * (t / 4) by ring]
      _ ≤ (2 * rexp (-π * (t / 4))) / (1 - rexp (-π : ℝ)) :=
            div_le_div_of_nonneg_left (by positivity) hden_pos
              (sub_le_sub_left (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, ht])) 1)
      _ = Cθ * rexp (-π * (t / 4)) := by
            simp [Cθ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  calc
    ‖H₂.resToImagAxis t‖ = ‖Θ₂.resToImagAxis t‖ ^ 4 := by
      simp [H₂, Function.resToImagAxis, ResToImagAxis, ht0, norm_pow]
    _ ≤ (Cθ * rexp (-π * (t / 4))) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hΘ2 4
    _ = (Cθ ^ 4) * rexp (-π * t) := by
      rw [mul_pow, ← Real.exp_nat_mul, show (4 : ℕ) * (-π * (t / 4)) = -π * t by push_cast; ring]

/-- Exponential decay bound for `ψS.resToImagAxis` on `Ici (1 : ℝ)`. -/
public theorem exists_bound_norm_ψS_resToImagAxis_exp_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ C * rexp (-π * t) := by
  obtain ⟨CH2, hH2⟩ := exists_bound_norm_H₂_resToImagAxis_exp_Ici_one
  let CH2' : ℝ := max CH2 0
  have hCH2' : 0 ≤ CH2' := le_max_right _ _
  have hH2' : ∀ t : ℝ, 1 ≤ t → ‖H₂.resToImagAxis t‖ ≤ CH2' * rexp (-π * t) := fun t ht =>
    le_mul_of_le_mul_of_nonneg_right (hH2 t ht) (le_max_left _ _) (by positivity)
  -- `H₃` and `H₄` converge to `1` along the imaginary axis, so their norms are bounded above
  -- and below away from `0` on `t ≥ 1` by compactness on an initial segment.
  have hEv (H : ℍ → ℂ) (hH : Tendsto (fun z : ℍ => H z) atImInfty (𝓝 (1 : ℂ))) :
      ∀ᶠ t in atTop, ‖H.resToImagAxis t - (1 : ℂ)‖ ≤ (1 / 2 : ℝ) :=
    (tendsto_sub_nhds_zero_iff.mpr (by simpa using
        (Function.tendsto_resToImagAxis_atImInfty (F := H) (l := (1 : ℂ)) hH))).norm.eventually
      (Iic_mem_nhds (by norm_num))
  obtain ⟨T0, hT0⟩ :=
    eventually_atTop.1 ((hEv H₃ H₃_tendsto_atImInfty).and (hEv H₄ H₄_tendsto_atImInfty))
  let T : ℝ := max T0 1
  have hH_ne (H : ℍ → ℂ) (hne : ∀ z : ℍ, H z ≠ 0) :
      ∀ t : ℝ, 1 ≤ t → H.resToImagAxis t ≠ (0 : ℂ) := fun t ht ↦ by
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    simpa [Function.resToImagAxis, ResToImagAxis, ht0] using hne ⟨Complex.I * t, by simp [ht0]⟩
  let φ : Icc 1 T → ℍ := fun t ↦ ⟨(Complex.I : ℂ) * (t : ℝ), by
    have : (0 : ℝ) < (t : ℝ) := lt_of_lt_of_le (by norm_num) t.2.1; simp [this]⟩
  have hcont_norm_resToImagAxis (H : ℍ → ℂ) (hH : Continuous H) :
      ContinuousOn (fun t : ℝ => ‖ResToImagAxis H t‖) (Icc 1 T) :=
    (continuousOn_iff_continuous_restrict).2 <| by
      simpa [show ((Icc 1 T).restrict fun t : ℝ ↦ ‖ResToImagAxis H t‖) =
        fun t : Icc 1 T ↦ ‖H (φ t)‖ from funext fun t ↦ by
          have ht0 : (0 : ℝ) < (t : ℝ) := lt_of_lt_of_le (by norm_num) t.2.1
          simp [Set.restrict, ResToImagAxis, ht0, φ]] using
        (hH.comp (by fun_prop : Continuous φ)).norm
  have hcontH4 : ContinuousOn (fun t : ℝ => ‖ResToImagAxis H₄ t‖) (Icc 1 T) :=
    hcont_norm_resToImagAxis H₄ mdifferentiable_H₄.continuous
  obtain ⟨m3, hm3, hm3le⟩ := SpherePacking.ForMathlib.exists_lower_bound_pos_on_Icc
    (g := fun t ↦ ‖H₃.resToImagAxis t‖)
    (hg := by simpa [Function.resToImagAxis_eq_resToImagAxis] using
      hcont_norm_resToImagAxis H₃ mdifferentiable_H₃.continuous)
    (hpos := fun t ht => norm_pos_iff.2 (hH_ne H₃ H₃_ne_zero t ht.1))
  obtain ⟨m4, hm4, hm4le⟩ := SpherePacking.ForMathlib.exists_lower_bound_pos_on_Icc
    (g := fun t ↦ ‖H₄.resToImagAxis t‖)
    (hg := by simpa [Function.resToImagAxis_eq_resToImagAxis] using hcontH4)
    (hpos := fun t ht => norm_pos_iff.2 (hH_ne H₄ H₄_ne_zero t ht.1))
  obtain ⟨M4Icc, hM4Icc⟩ := SpherePacking.ForMathlib.exists_upper_bound_on_Icc
    (g := fun t : ℝ => ‖H₄.resToImagAxis t‖) (hab := le_max_right _ _)
    (hg := by simpa [Function.resToImagAxis_eq_resToImagAxis] using hcontH4)
  let M4 : ℝ := max M4Icc 2
  have half_le_norm {x : ℂ} (h : ‖x - (1 : ℂ)‖ ≤ (1 / 2 : ℝ)) : (1 / 2 : ℝ) ≤ ‖x‖ := by
    have := (sub_le_iff_le_add).2 (norm_le_norm_add_norm_sub' (1 : ℂ) x)
    simp [norm_sub_rev] at this; linarith
  have hH3_lower : ∀ t : ℝ, 1 ≤ t → min m3 (1 / 2 : ℝ) ≤ ‖H₃.resToImagAxis t‖ := fun t ht ↦ by
    by_cases htT : t ≤ T
    · exact inf_le_of_left_le (hm3le t ⟨ht, htT⟩)
    · exact inf_le_of_right_le
        (half_le_norm (hT0 t ((le_max_left _ _).trans (le_of_not_ge htT))).1)
  have hH4_lower : ∀ t : ℝ, 1 ≤ t → min m4 (1 / 2 : ℝ) ≤ ‖H₄.resToImagAxis t‖ := fun t ht ↦ by
    by_cases htT : t ≤ T
    · exact inf_le_of_left_le (hm4le t ⟨ht, htT⟩)
    · exact inf_le_of_right_le
        (half_le_norm (hT0 t ((le_max_left _ _).trans (le_of_not_ge htT))).2)
  have hH4_upper : ∀ t : ℝ, 1 ≤ t → ‖H₄.resToImagAxis t‖ ≤ M4 := fun t ht ↦ by
    by_cases htT : t ≤ T
    · exact (hM4Icc t ⟨ht, htT⟩).trans (le_max_left _ _)
    · have hx : ‖H₄.resToImagAxis t‖ ≤ ‖H₄.resToImagAxis t - (1 : ℂ)‖ + 1 := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, norm_one] using
          norm_add_le (H₄.resToImagAxis t - (1 : ℂ)) (1 : ℂ)
      have h32 : ‖H₄.resToImagAxis t‖ ≤ (3 / 2 : ℝ) := by
        linarith [(hT0 t ((le_max_left _ _).trans (le_of_not_ge htT))).2]
      exact h32.trans ((by norm_num : (3 / 2 : ℝ) ≤ 2).trans (le_max_right _ _))
  -- Bound the polynomial factor in `ψS_apply_eq_factor`.
  let P : ℝ := 2 * (CH2' ^ 2) + 5 * CH2' * M4 + 5 * (M4 ^ 2)
  let c3 : ℝ := min m3 (1 / 2 : ℝ)
  let c4 : ℝ := min m4 (1 / 2 : ℝ)
  have hc3 : 0 < c3 := lt_min hm3 (by norm_num)
  have hc4 : 0 < c4 := lt_min hm4 (by norm_num)
  refine ⟨(128 : ℝ) * P * ((c3 ^ 2 * c4 ^ 2)⁻¹) * CH2', ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hH2t : ‖H₂.resToImagAxis t‖ ≤ CH2' * rexp (-π * t) := hH2' t ht
  have hH2le : ‖H₂.resToImagAxis t‖ ≤ CH2' := hH2t.trans <| by
    simpa using mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht0.le])) hCH2'
  have hH4le : ‖H₄.resToImagAxis t‖ ≤ M4 := hH4_upper t ht
  have hpoly :
      ‖(2 : ℂ) * (H₂.resToImagAxis t) ^ 2
          + (5 : ℂ) * (H₂.resToImagAxis t) * (H₄.resToImagAxis t)
          + (5 : ℂ) * (H₄.resToImagAxis t) ^ 2‖ ≤ P := by
    have h1 : ‖(2 : ℂ) * (H₂.resToImagAxis t) ^ 2‖ ≤ 2 * (CH2' ^ 2) := by
      simpa [norm_mul, norm_pow] using mul_le_mul_of_nonneg_left
        (by simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hH2le 2) (norm_nonneg (2 : ℂ))
    have h2 : ‖(5 : ℂ) * (H₂.resToImagAxis t) * (H₄.resToImagAxis t)‖ ≤ 5 * CH2' * M4 := by
      simpa [norm_mul, mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left
        (by gcongr : ‖H₂.resToImagAxis t‖ * ‖H₄.resToImagAxis t‖ ≤ CH2' * M4) (norm_nonneg (5 : ℂ))
    have h3 : ‖(5 : ℂ) * (H₄.resToImagAxis t) ^ 2‖ ≤ 5 * (M4 ^ 2) := by
      simpa [norm_mul, norm_pow] using mul_le_mul_of_nonneg_left
        (by simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hH4le 2) (norm_nonneg (5 : ℂ))
    exact norm_add_le_of_le ((norm_add_le _ _).trans (by linarith [h1, h2])) h3
  -- Now bound `ψS.resToImagAxis t` using `ψS_apply_eq_factor`.
  let z : ℍ := ⟨Complex.I * t, by simp [ht0]⟩
  have hψS : ‖ψS.resToImagAxis t‖ = ‖(-128 : ℂ) *
      (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
        ((H₃ z) ^ 2 * (H₄ z) ^ 2)‖ := by
    change ‖ResToImagAxis ψS t‖ = _
    rw [show ResToImagAxis ψS t = ψS z by simp [ResToImagAxis, ht0, z],
      show ψS z = (-128 : ℂ) *
            (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
            ((H₃ z) ^ 2 * (H₄ z) ^ 2) by simpa using ψS_apply_eq_factor z]
  have hHz2 : ResToImagAxis H₂ t = H₂ z := by simp [ResToImagAxis, ht0, z]
  have hHz3 : ResToImagAxis H₃ t = H₃ z := by simp [ResToImagAxis, ht0, z]
  have hHz4 : ResToImagAxis H₄ t = H₄ z := by simp [ResToImagAxis, ht0, z]
  have hden_lower : c3 ≤ ‖H₃ z‖ := by
    simpa [hHz3] using (show c3 ≤ ‖ResToImagAxis H₃ t‖ from hH3_lower t ht)
  have hden_lower4 : c4 ≤ ‖H₄ z‖ := by
    simpa [hHz4] using (show c4 ≤ ‖ResToImagAxis H₄ t‖ from hH4_lower t ht)
  have hinv : ‖((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ ≤ (c3 ^ 2 * c4 ^ 2)⁻¹ := by
    have hpos : 0 < ‖(H₃ z) ^ 2 * (H₄ z) ^ 2‖ :=
      norm_pos_iff.2 (mul_ne_zero (pow_ne_zero 2 (H₃_ne_zero z)) (pow_ne_zero 2 (H₄_ne_zero z)))
    have hden : c3 ^ 2 * c4 ^ 2 ≤ ‖(H₃ z) ^ 2 * (H₄ z) ^ 2‖ := by
      simpa [norm_mul, norm_pow] using mul_le_mul (pow_le_pow_left₀ hc3.le hden_lower 2)
        (pow_le_pow_left₀ hc4.le hden_lower4 2) (by positivity) (by positivity)
    simpa [norm_inv] using (inv_le_inv₀ hpos (by positivity)).2 hden
  have hH2z : ‖H₂ z‖ ≤ CH2' * rexp (-π * t) := by
    simpa [hHz2, Function.resToImagAxis] using hH2t
  have hpoly' :
      ‖2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2‖ ≤ P := by
    simpa [hHz2, hHz4, Function.resToImagAxis] using hpoly
  have hP0 : (0 : ℝ) ≤ P := (norm_nonneg _).trans hpoly'
  calc
    ‖ψS.resToImagAxis t‖ = ‖(-128 : ℂ) *
        (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
          ((H₃ z) ^ 2 * (H₄ z) ^ 2)‖ := hψS
    _ = ‖(-128 : ℂ) *
            (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) *
              ((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ := by
          simp [div_eq_mul_inv, mul_assoc]
    _ ≤ (128 : ℝ) * (‖H₂ z‖ * ‖2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2‖) *
          ‖((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ := by
          simp [div_eq_mul_inv, mul_assoc]
    _ ≤ (128 : ℝ) * (‖H₂ z‖ * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ := by
          have h2 : (‖H₂ z‖ * ‖2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2‖) *
                ‖((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ ≤ (‖H₂ z‖ * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ :=
            mul_le_mul (mul_le_mul_of_nonneg_left hpoly' (norm_nonneg _)) hinv (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) hP0)
          grind only
    _ ≤ (128 : ℝ) * ((CH2' * rexp (-π * t)) * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ := by
          have h2 : (‖H₂ z‖ * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ ≤
              ((CH2' * rexp (-π * t)) * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hH2z hP0) (by positivity)
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 128)
    _ = ((128 : ℝ) * P * (c3 ^ 2 * c4 ^ 2)⁻¹ * CH2') * rexp (-π * t) := by ring

end

end MagicFunction.b.PsiBounds.PsiExpBounds
