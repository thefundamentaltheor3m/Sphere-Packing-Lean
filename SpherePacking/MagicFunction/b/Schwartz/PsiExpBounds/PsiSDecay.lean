module
public import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.Basic
import SpherePacking.ForMathlib.BoundsOnIcc

/-!
# Exponential decay of `ψS` on the imaginary axis

This file combines the exponential bound for `H₂` with the algebraic factorization of `ψS` to
derive an estimate of the form `‖ψS(it)‖ ≤ C * exp(-π t)` for `t ≥ 1`.

## Main statement
* `exists_bound_norm_ψS_resToImagAxis_exp_Ici_one`
-/

namespace MagicFunction.b.PsiBounds.PsiExpBounds

noncomputable section

open scoped Topology UpperHalfPlane

open Complex Real Filter Topology UpperHalfPlane Set
open HurwitzKernelBounds

/-- Exponential decay bound for `ψS.resToImagAxis` on `Ici (1 : ℝ)`. -/
public theorem exists_bound_norm_ψS_resToImagAxis_exp_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ C * rexp (-π * t) := by
  rcases exists_bound_norm_H₂_resToImagAxis_exp_Ici_one with ⟨CH2, hH2⟩
  let CH2' : ℝ := max CH2 0
  have hCH2' : 0 ≤ CH2' := le_max_right _ _
  have hH2' : ∀ t : ℝ, 1 ≤ t → ‖H₂.resToImagAxis t‖ ≤ CH2' * rexp (-π * t) := by
    intro t ht
    have hle : CH2 ≤ CH2' := le_max_left _ _
    have hexp : 0 ≤ rexp (-π * t) := by positivity
    exact le_mul_of_le_mul_of_nonneg_right (hH2 t ht) hle hexp
  -- `H₃` and `H₄` converge to `1` along the imaginary axis, so their norms are bounded above
  -- and below away from `0` on `t ≥ 1` by compactness on an initial segment.
  have htendH3 : Tendsto (fun t : ℝ => H₃.resToImagAxis t) atTop (𝓝 (1 : ℂ)) := by
    simpa using
      (Function.tendsto_resToImagAxis_atImInfty (F := H₃) (l := (1 : ℂ)) H₃_tendsto_atImInfty)
  have htendH4 : Tendsto (fun t : ℝ => H₄.resToImagAxis t) atTop (𝓝 (1 : ℂ)) := by
    simpa using
      (Function.tendsto_resToImagAxis_atImInfty (F := H₄) (l := (1 : ℂ)) H₄_tendsto_atImInfty)
  have hEvH3 : ∀ᶠ t in atTop, ‖H₃.resToImagAxis t - (1 : ℂ)‖ ≤ (1 / 2 : ℝ) := by
    have hsub :
        Tendsto (fun t : ℝ => H₃.resToImagAxis t - (1 : ℂ)) atTop (𝓝 (0 : ℂ)) :=
      tendsto_sub_nhds_zero_iff.mpr htendH3
    have := (hsub.norm)
    exact this.eventually (Iic_mem_nhds (by norm_num))
  have hEvH4 : ∀ᶠ t in atTop, ‖H₄.resToImagAxis t - (1 : ℂ)‖ ≤ (1 / 2 : ℝ) := by
    have hsub :
        Tendsto (fun t : ℝ => H₄.resToImagAxis t - (1 : ℂ)) atTop (𝓝 (0 : ℂ)) :=
      tendsto_sub_nhds_zero_iff.mpr htendH4
    have := (hsub.norm)
    exact this.eventually (Iic_mem_nhds (by norm_num))
  rcases (eventually_atTop.1 (hEvH3.and hEvH4)) with ⟨T0, hT0⟩
  let T : ℝ := max T0 1
  have hT1 : 1 ≤ T := le_max_right _ _
  -- Nonvanishing on the imaginary axis.
  have hH3_ne : ∀ t : ℝ, 1 ≤ t → H₃.resToImagAxis t ≠ (0 : ℂ) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    let z : ℍ := ⟨Complex.I * t, by simp [ht0]⟩
    have : H₃ z ≠ 0 := H₃_ne_zero z
    simpa [Function.resToImagAxis, ResToImagAxis, ht0, z] using this
  have hH4_ne : ∀ t : ℝ, 1 ≤ t → H₄.resToImagAxis t ≠ (0 : ℂ) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    let z : ℍ := ⟨Complex.I * t, by simp [ht0]⟩
    have : H₄ z ≠ 0 := H₄_ne_zero z
    simpa [Function.resToImagAxis, ResToImagAxis, ht0, z] using this
  -- Continuity of the norm on the compact interval `[1,T]`.
  have hI : Continuous fun t : Icc 1 T => (Complex.I : ℂ) * (t : ℝ) :=
    continuous_const.mul (Complex.continuous_ofReal.comp continuous_subtype_val)
  let φ : Icc 1 T → ℍ :=
    fun t =>
      ⟨(Complex.I : ℂ) * (t : ℝ), by
        have : (0 : ℝ) < (t : ℝ) := lt_of_lt_of_le (by norm_num) t.2.1
        simp [this]⟩
  have hφ : Continuous φ := by
    fun_prop
  have hcont_norm_resToImagAxis (H : ℍ → ℂ) (hH : Continuous H) :
      ContinuousOn (fun t : ℝ => ‖ResToImagAxis H t‖) (Icc 1 T) := by
    refine (continuousOn_iff_continuous_restrict).2 ?_
    have hcomp : Continuous fun t : Icc 1 T => H (φ t) := hH.comp hφ
    have hcomp' : Continuous fun t : Icc 1 T => ‖H (φ t)‖ := hcomp.norm
    have hEq :
        ((Icc 1 T).restrict fun t : ℝ => ‖ResToImagAxis H t‖) =
          fun t : Icc 1 T => ‖H (φ t)‖ := by
      funext t
      have ht0 : (0 : ℝ) < (t : ℝ) := lt_of_lt_of_le (by norm_num) t.2.1
      simp [Set.restrict, ResToImagAxis, ht0, φ]
    simpa [hEq] using hcomp'
  have hcontH3 : ContinuousOn (fun t : ℝ => ‖ResToImagAxis H₃ t‖) (Icc 1 T) :=
    hcont_norm_resToImagAxis H₃ mdifferentiable_H₃.continuous
  have hcontH4 : ContinuousOn (fun t : ℝ => ‖ResToImagAxis H₄ t‖) (Icc 1 T) :=
    hcont_norm_resToImagAxis H₄ mdifferentiable_H₄.continuous
  have hpos3 : ∀ t ∈ Icc (1 : ℝ) T, 0 < ‖H₃.resToImagAxis t‖ := by
    intro t ht
    exact norm_pos_iff.2 (hH3_ne t ht.1)
  have hpos4 : ∀ t ∈ Icc (1 : ℝ) T, 0 < ‖H₄.resToImagAxis t‖ := by
    intro t ht
    exact norm_pos_iff.2 (hH4_ne t ht.1)
  rcases SpherePacking.ForMathlib.exists_lower_bound_pos_on_Icc (g := fun t ↦ ‖H₃.resToImagAxis t‖)
      (hg := by simpa [Function.resToImagAxis_eq_resToImagAxis] using hcontH3)
      (hpos := hpos3) with ⟨m3, hm3, hm3le⟩
  rcases SpherePacking.ForMathlib.exists_lower_bound_pos_on_Icc (g := fun t ↦ ‖H₄.resToImagAxis t‖)
      (hg := by simpa [Function.resToImagAxis_eq_resToImagAxis] using hcontH4)
      (hpos := hpos4) with ⟨m4, hm4, hm4le⟩
  rcases SpherePacking.ForMathlib.exists_upper_bound_on_Icc (g := fun t : ℝ => ‖H₄.resToImagAxis t‖)
      (hab := hT1) (hg := by simpa [Function.resToImagAxis_eq_resToImagAxis] using hcontH4)
      with ⟨M4Icc, hM4Icc⟩
  let M4 : ℝ := max M4Icc 2
  have half_le_norm_of_norm_sub_one_le_half {x : ℂ} (h : ‖x - (1 : ℂ)‖ ≤ (1 / 2 : ℝ)) :
      (1 / 2 : ℝ) ≤ ‖x‖ := by
    have hdiff : (1 : ℝ) - ‖x - (1 : ℂ)‖ ≤ ‖x‖ := by
      -- reverse triangle inequality: `‖1‖ - ‖1 - x‖ ≤ ‖x‖`
      have h' : ‖(1 : ℂ)‖ - ‖(1 : ℂ) - x‖ ≤ ‖x‖ := by
        refine (sub_le_iff_le_add).2 ?_
        exact norm_le_norm_add_norm_sub' 1 x
      simpa [norm_one, norm_sub_rev] using h'
    have hhalf : (1 / 2 : ℝ) ≤ (1 : ℝ) - ‖x - (1 : ℂ)‖ := by
      linarith
    exact le_trans hhalf hdiff
  have norm_le_three_halves_of_norm_sub_one_le_half {x : ℂ} (h : ‖x - (1 : ℂ)‖ ≤ (1 / 2 : ℝ)) :
      ‖x‖ ≤ (3 / 2 : ℝ) := by
    have hx0 : ‖x‖ ≤ ‖x - (1 : ℂ)‖ + ‖(1 : ℂ)‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_add_le (x - (1 : ℂ)) (1 : ℂ))
    have hx : ‖x‖ ≤ ‖x - (1 : ℂ)‖ + 1 := by
      simpa [norm_one] using hx0
    linarith
  have hH3_lower : ∀ t : ℝ, 1 ≤ t → min m3 (1 / 2 : ℝ) ≤ ‖H₃.resToImagAxis t‖ := by
    intro t ht
    by_cases htT : t ≤ T
    · have htI : t ∈ Icc (1 : ℝ) T := ⟨ht, htT⟩
      exact inf_le_of_left_le (hm3le t htI)
    · have htT' : T ≤ t := le_of_not_ge htT
      have htT0 : T0 ≤ t := le_trans (le_max_left _ _) htT'
      have hnear : ‖H₃.resToImagAxis t - (1 : ℂ)‖ ≤ 1 / 2 := (hT0 t htT0).1
      exact inf_le_of_right_le (half_le_norm_of_norm_sub_one_le_half hnear)
  have hH4_lower : ∀ t : ℝ, 1 ≤ t → min m4 (1 / 2 : ℝ) ≤ ‖H₄.resToImagAxis t‖ := by
    intro t ht
    by_cases htT : t ≤ T
    · have htI : t ∈ Icc (1 : ℝ) T := ⟨ht, htT⟩
      exact inf_le_of_left_le (hm4le t htI)
    · have htT' : T ≤ t := le_of_not_ge htT
      have htT0 : T0 ≤ t := le_trans (le_max_left _ _) htT'
      have hnear : ‖H₄.resToImagAxis t - (1 : ℂ)‖ ≤ 1 / 2 := (hT0 t htT0).2
      exact inf_le_of_right_le (half_le_norm_of_norm_sub_one_le_half hnear)
  have hH4_upper : ∀ t : ℝ, 1 ≤ t → ‖H₄.resToImagAxis t‖ ≤ M4 := by
    intro t ht
    by_cases htT : t ≤ T
    · have htI : t ∈ Icc (1 : ℝ) T := ⟨ht, htT⟩
      have : ‖H₄.resToImagAxis t‖ ≤ M4Icc := hM4Icc t htI
      exact this.trans (le_max_left _ _)
    · have htT' : T ≤ t := le_of_not_ge htT
      have htT0 : T0 ≤ t := le_trans (le_max_left _ _) htT'
      have hnear : ‖H₄.resToImagAxis t - (1 : ℂ)‖ ≤ 1 / 2 := (hT0 t htT0).2
      have : ‖H₄.resToImagAxis t‖ ≤ (3 / 2 : ℝ) :=
        norm_le_three_halves_of_norm_sub_one_le_half (x := H₄.resToImagAxis t) hnear
      exact this.trans (by
        have : (3 / 2 : ℝ) ≤ M4 := by
          exact (show (3 / 2 : ℝ) ≤ 2 by norm_num).trans (le_max_right _ _)
        exact this)
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
  have hH2le : ‖H₂.resToImagAxis t‖ ≤ CH2' := by
    have hexp : rexp (-π * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [Real.pi_pos, ht0.le]
    calc
      ‖H₂.resToImagAxis t‖ ≤ CH2' * rexp (-π * t) := hH2t
      _ ≤ CH2' * 1 := by
            exact mul_le_mul_of_nonneg_left hexp hCH2'
      _ = CH2' := by ring
  have hH4le : ‖H₄.resToImagAxis t‖ ≤ M4 := hH4_upper t ht
  have hpoly :
      ‖(2 : ℂ) * (H₂.resToImagAxis t) ^ 2
          + (5 : ℂ) * (H₂.resToImagAxis t) * (H₄.resToImagAxis t)
          + (5 : ℂ) * (H₄.resToImagAxis t) ^ 2‖ ≤ P := by
    -- triangle inequality + the norm bounds on `H₂` and `H₄`
    have h1 :
        ‖(2 : ℂ) * (H₂.resToImagAxis t) ^ 2‖ ≤ 2 * (CH2' ^ 2) := by
      have : ‖(H₂.resToImagAxis t) ^ 2‖ ≤ CH2' ^ 2 := by
        simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hH2le 2
      have hcoeff : 0 ≤ ‖(2 : ℂ)‖ := norm_nonneg _
      simpa [norm_mul, norm_pow] using (mul_le_mul_of_nonneg_left this hcoeff)
    have h2 :
        ‖(5 : ℂ) * (H₂.resToImagAxis t) * (H₄.resToImagAxis t)‖ ≤ 5 * CH2' * M4 := by
      have : ‖H₂.resToImagAxis t‖ * ‖H₄.resToImagAxis t‖ ≤ CH2' * M4 := by
        gcongr
      simpa [norm_mul, mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left this (norm_nonneg (5 : ℂ)))
    have h3 :
        ‖(5 : ℂ) * (H₄.resToImagAxis t) ^ 2‖ ≤ 5 * (M4 ^ 2) := by
      have : ‖(H₄.resToImagAxis t) ^ 2‖ ≤ M4 ^ 2 := by
        simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hH4le 2
      have hcoeff : 0 ≤ ‖(5 : ℂ)‖ := norm_nonneg _
      simpa [norm_mul, norm_pow] using (mul_le_mul_of_nonneg_left this hcoeff)
    have h12 :
        ‖(2 : ℂ) * (H₂.resToImagAxis t) ^ 2
            + (5 : ℂ) * (H₂.resToImagAxis t) * (H₄.resToImagAxis t)‖ ≤
          2 * (CH2' ^ 2) + 5 * CH2' * M4 := by
      exact (norm_add_le _ _).trans (by linarith [h1, h2])
    exact norm_add_le_of_le h12 h3
  -- Now bound `ψS.resToImagAxis t` using `ψS_apply_eq_factor`.
  let z : ℍ := ⟨Complex.I * t, by simp [ht0]⟩
  have hψS :
      ‖ψS.resToImagAxis t‖ =
        ‖(-128 : ℂ) *
            (H₂ z *
                (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
              ((H₃ z) ^ 2 * (H₄ z) ^ 2)‖ := by
    -- unfold `resToImagAxis` and rewrite using `ψS_apply_eq_factor`.
    change ‖ResToImagAxis ψS t‖ = _
    have hz : ResToImagAxis ψS t = ψS z := by
      simp [ResToImagAxis, ht0, z]
    have hEq : ψS z =
        (-128 : ℂ) *
            (H₂ z *
              (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
            ((H₃ z) ^ 2 * (H₄ z) ^ 2) := by
      simpa using ψS_apply_eq_factor z
    calc
      ‖ResToImagAxis ψS t‖ = ‖ψS z‖ := by simp [hz]
      _ = ‖(-128 : ℂ) *
            (H₂ z *
              (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
            ((H₃ z) ^ 2 * (H₄ z) ^ 2)‖ := by
            rw [hEq]
  have hHz2 : ResToImagAxis H₂ t = H₂ z := by simp [ResToImagAxis, ht0, z]
  have hHz3 : ResToImagAxis H₃ t = H₃ z := by simp [ResToImagAxis, ht0, z]
  have hHz4 : ResToImagAxis H₄ t = H₄ z := by simp [ResToImagAxis, ht0, z]
  have hden_lower : c3 ≤ ‖H₃ z‖ := by
    have : c3 ≤ ‖ResToImagAxis H₃ t‖ := by
      dsimp [c3]
      -- rewrite the RHS to match `hH3_lower`
      change min m3 (1 / 2 : ℝ) ≤ ‖H₃.resToImagAxis t‖
      exact hH3_lower t ht
    simpa [hHz3] using this
  have hden_lower4 : c4 ≤ ‖H₄ z‖ := by
    have : c4 ≤ ‖ResToImagAxis H₄ t‖ := by
      dsimp [c4]
      change min m4 (1 / 2 : ℝ) ≤ ‖H₄.resToImagAxis t‖
      exact hH4_lower t ht
    simpa [hHz4] using this
  have hinv :
      ‖((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ ≤ (c3 ^ 2 * c4 ^ 2)⁻¹ := by
    have hpos : 0 < ‖(H₃ z) ^ 2 * (H₄ z) ^ 2‖ := by
      have : (H₃ z) ^ 2 * (H₄ z) ^ 2 ≠ 0 := by
        exact mul_ne_zero (pow_ne_zero 2 (H₃_ne_zero z)) (pow_ne_zero 2 (H₄_ne_zero z))
      exact norm_pos_iff.2 this
    have h3 : c3 ^ 2 ≤ ‖H₃ z‖ ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hc3) hden_lower 2
    have h4 : c4 ^ 2 ≤ ‖H₄ z‖ ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hc4) hden_lower4 2
    have hmul : c3 ^ 2 * c4 ^ 2 ≤ ‖H₃ z‖ ^ 2 * ‖H₄ z‖ ^ 2 := by
      exact mul_le_mul h3 h4 (by positivity) (by positivity)
    have hden : c3 ^ 2 * c4 ^ 2 ≤ ‖(H₃ z) ^ 2 * (H₄ z) ^ 2‖ := by
      simpa [norm_mul, norm_pow] using hmul
    have hinv' :
        (‖(H₃ z) ^ 2 * (H₄ z) ^ 2‖)⁻¹ ≤ (c3 ^ 2 * c4 ^ 2)⁻¹ :=
      (inv_le_inv₀ hpos (by positivity)).2 hden
    simpa [norm_inv] using hinv'
  have hH2z : ‖H₂ z‖ ≤ CH2' * rexp (-π * t) := by
    have hH2t' : ‖ResToImagAxis H₂ t‖ ≤ CH2' * rexp (-π * t) := by
      simpa [Function.resToImagAxis, ResToImagAxis] using hH2t
    simpa [hHz2] using hH2t'
  have hpoly' :
      ‖2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2‖ ≤ P := by
    have hpoly0 :
        ‖(2 : ℂ) * (ResToImagAxis H₂ t) ^ 2
            + (5 : ℂ) * (ResToImagAxis H₂ t) * (ResToImagAxis H₄ t)
            + (5 : ℂ) * (ResToImagAxis H₄ t) ^ 2‖ ≤ P := by
      simpa [Function.resToImagAxis, ResToImagAxis] using hpoly
    simpa [hHz2, hHz4] using hpoly0
  -- put everything together
  calc
    ‖ψS.resToImagAxis t‖ =
        ‖(-128 : ℂ) *
            (H₂ z *
                (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
              ((H₃ z) ^ 2 * (H₄ z) ^ 2)‖ := hψS
    _ = ‖(-128 : ℂ) *
            (H₂ z *
                (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) *
              ((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ := by
          simp [div_eq_mul_inv, mul_assoc]
    _ ≤ (128 : ℝ) * (‖H₂ z‖ * ‖2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2‖) *
          ‖((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ := by
          -- drop the sign and use submultiplicativity (avoid `simp` timeouts)
          set p : ℂ :=
            2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2
          set denInv : ℂ := ((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹
          have hnorm :
              ‖(-128 : ℂ) * (H₂ z * p) * denInv‖ ≤
                (‖(-128 : ℂ)‖ * (‖H₂ z‖ * ‖p‖)) * ‖denInv‖ := by
            calc
              ‖(-128 : ℂ) * (H₂ z * p) * denInv‖
                  = ‖((-128 : ℂ) * (H₂ z * p)) * denInv‖ := by simp [mul_assoc]
              _ ≤ ‖(-128 : ℂ) * (H₂ z * p)‖ * ‖denInv‖ := norm_mul_le _ _
              _ ≤ (‖(-128 : ℂ)‖ * ‖H₂ z * p‖) * ‖denInv‖ := by
                    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                    simp
              _ ≤ (‖(-128 : ℂ)‖ * (‖H₂ z‖ * ‖p‖)) * ‖denInv‖ := by
                    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                    exact mul_le_mul_of_nonneg_left (norm_mul_le (H₂ z) p) (norm_nonneg _)
          -- clean up scalars / associations
          simp [p, denInv, mul_assoc]
    _ ≤ (128 : ℝ) * (‖H₂ z‖ * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ := by
          have hP0 : (0 : ℝ) ≤ P := le_trans (norm_nonneg _) hpoly'
          have h1 :
              ‖H₂ z‖ * ‖2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2‖ ≤
                ‖H₂ z‖ * P := by
            exact mul_le_mul_of_nonneg_left hpoly' (norm_nonneg _)
          have h2 :
              (‖H₂ z‖ * ‖2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2‖) *
                  ‖((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ ≤
                (‖H₂ z‖ * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ :=
            mul_le_mul h1 hinv (norm_nonneg _)
                (mul_nonneg (norm_nonneg _) hP0)
          grind only
    _ ≤ (128 : ℝ) * ((CH2' * rexp (-π * t)) * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ := by
          have hP0 : (0 : ℝ) ≤ P := le_trans (norm_nonneg _) hpoly'
          have h1 : ‖H₂ z‖ * P ≤ (CH2' * rexp (-π * t)) * P := by
            exact mul_le_mul_of_nonneg_right hH2z hP0
          have h2 :
              (‖H₂ z‖ * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ ≤
                ((CH2' * rexp (-π * t)) * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
          have h3 :
              (128 : ℝ) * ((‖H₂ z‖ * P) * (c3 ^ 2 * c4 ^ 2)⁻¹) ≤
                (128 : ℝ) * (((CH2' * rexp (-π * t)) * P) * (c3 ^ 2 * c4 ^ 2)⁻¹) := by
            exact mul_le_mul_of_nonneg_left h2 (by positivity)
          simpa [mul_assoc] using h3
    _ = ((128 : ℝ) * P * (c3 ^ 2 * c4 ^ 2)⁻¹ * CH2') * rexp (-π * t) := by ring

end

end MagicFunction.b.PsiBounds.PsiExpBounds
