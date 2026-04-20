module
public import SpherePacking.MagicFunction.b.Psi
public import SpherePacking.ModularForms.Delta
import SpherePacking.ForMathlib.BoundsOnIcc

import Mathlib.Topology.Algebra.InfiniteSum.NatInt


/-!
# Bounds for the `ψ`-functions (imaginary axis)

This file provides the analytic bounds on `ψS` needed to prove the Schwartz decay of the
integrals defining Viazovska's magic function `b`.
-/

namespace MagicFunction.b.PsiBounds

open scoped Topology UpperHalfPlane Manifold

open Complex Real Filter Topology UpperHalfPlane Set

noncomputable section

/-! ## Algebraic factorization of `ψS` -/

/-- Factorization of `ψS` in terms of the Jacobi theta functions `H₂`, `H₃`, and `H₄`. -/
public lemma ψS_apply_eq_factor (z : ℍ) :
    ψS z =
      (-128 : ℂ) *
        (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
          ((H₃ z) ^ 2 * (H₄ z) ^ 2) := by
  have hψ :
      ψS z = 128 * (((H₄ z - H₂ z) / (H₃ z) ^ 2) - ((H₂ z + H₃ z) / (H₄ z) ^ 2)) := by
    simpa using congrArg (fun f : ℍ → ℂ => f z) ψS_eq'
  have hJ : H₃ z = H₂ z + H₄ z := by
    simpa using congrArg (fun f : ℍ → ℂ => f z) jacobi_identity.symm
  have h3₀ : H₃ z ≠ 0 := H₃_ne_zero z
  have h4₀ : H₄ z ≠ 0 := H₄_ne_zero z
  have h3 : (H₃ z) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 h3₀
  have h4 : (H₄ z) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 h4₀
  have hden : (H₃ z) ^ 2 * (H₄ z) ^ 2 ≠ 0 := mul_ne_zero h3 h4
  refine (eq_div_iff hden).2 ?_
  rw [hψ]
  field_simp [h3₀, h4₀]
  simp [hJ]
  ring_nf

end

/-! ## Continuity and bounds for `ψS` on the imaginary axis -/

/-- Continuity of the modular function `ψS`. -/
public lemma continuous_ψS : Continuous ψS := by
  have hH2 : Continuous H₂ := mdifferentiable_H₂.continuous
  have hH3 : Continuous H₃ := mdifferentiable_H₃.continuous
  have hH4 : Continuous H₄ := mdifferentiable_H₄.continuous
  simpa [ψS_eq', mul_assoc] using
    (continuous_const.mul
      (((hH4.sub hH2).div (hH3.pow 2) (fun z => pow_ne_zero 2 (H₃_ne_zero z))).sub
        ((hH2.add hH3).div (hH4.pow 2) (fun z => pow_ne_zero 2 (H₄_ne_zero z)))))

/-- Continuity of the modular function `ψT`. -/
public lemma continuous_ψT : Continuous ψT := by
  have hH2 : Continuous H₂ := mdifferentiable_H₂.continuous
  have hH3 : Continuous H₃ := mdifferentiable_H₃.continuous
  have hH4 : Continuous H₄ := mdifferentiable_H₄.continuous
  simpa [ψT_eq, mul_assoc] using
    (continuous_const.mul
      (((hH3.add hH4).div (hH2.pow 2) (fun z => pow_ne_zero 2 (H₂_ne_zero z))).add
        ((hH2.add hH3).div (hH4.pow 2) (fun z => pow_ne_zero 2 (H₄_ne_zero z)))))

/-- Continuity of the modular function `ψI`. -/
public lemma continuous_ψI : Continuous ψI := by
  have hH2 : Continuous H₂ := mdifferentiable_H₂.continuous
  have hH3 : Continuous H₃ := mdifferentiable_H₃.continuous
  have hH4 : Continuous H₄ := mdifferentiable_H₄.continuous
  have hψ :
      ψI =
        fun z : ℍ =>
    (128 : ℂ) * ((H₃ z + H₄ z) / (H₂ z) ^ 2) +
            (128 : ℂ) * ((H₄ z - H₂ z) / (H₃ z) ^ 2) := by
    funext z
    simpa [nsmul_eq_mul, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
      mul_comm] using
      congrArg (fun f : ℍ → ℂ => f z) ψI_eq
  rw [hψ]
  simpa [mul_assoc] using
    (continuous_const.mul
      ((hH3.add hH4).div (hH2.pow 2) (fun z => pow_ne_zero 2 (H₂_ne_zero z)))).add
      (continuous_const.mul
        ((hH4.sub hH2).div (hH3.pow 2) (fun z => pow_ne_zero 2 (H₃_ne_zero z))))

/-- `ψS` tends to `0` at `Im z → ∞`. -/
public theorem tendsto_ψS_atImInfty : Tendsto ψS atImInfty (𝓝 (0 : ℂ)) := by
  have hH2 : Tendsto H₂ atImInfty (𝓝 (0 : ℂ)) := H₂_tendsto_atImInfty
  have hH3 : Tendsto H₃ atImInfty (𝓝 (1 : ℂ)) := H₃_tendsto_atImInfty
  have hH4 : Tendsto H₄ atImInfty (𝓝 (1 : ℂ)) := H₄_tendsto_atImInfty
  have hpoly :
      Tendsto
        (fun z : ℍ => 2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)
        atImInfty (𝓝 (5 : ℂ)) := by
    have h1 : Tendsto (fun z : ℍ => 2 * (H₂ z) ^ 2) atImInfty (𝓝 (0 : ℂ)) := by
      simpa using (tendsto_const_nhds.mul (hH2.pow 2))
    have h2 : Tendsto (fun z : ℍ => 5 * (H₂ z) * (H₄ z)) atImInfty (𝓝 (0 : ℂ)) := by
      simpa [mul_assoc] using (tendsto_const_nhds.mul (hH2.mul hH4))
    have h3 : Tendsto (fun z : ℍ => 5 * (H₄ z) ^ 2) atImInfty (𝓝 (5 : ℂ)) := by
      simpa using (tendsto_const_nhds.mul (hH4.pow 2))
    simpa [add_assoc] using (h1.add h2).add h3
  have hnum :
      Tendsto
        (fun z : ℍ =>
          -((128 : ℂ) *
            (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2))))
        atImInfty (𝓝 (0 : ℂ)) := by
    simpa [mul_assoc] using (tendsto_const_nhds.mul (hH2.mul hpoly)).neg
  have hden :
      Tendsto (fun z : ℍ => (H₃ z) ^ 2 * (H₄ z) ^ 2) atImInfty (𝓝 (1 : ℂ)) := by
    simpa using (hH3.pow 2).mul (hH4.pow 2)
  have hdiv :
      Tendsto
        (fun z : ℍ =>
          (-((128 : ℂ) *
              (H₂ z *
                (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)))) /
              ((H₃ z) ^ 2 * (H₄ z) ^ 2))
        atImInfty (𝓝 (0 : ℂ)) := by
    simpa [Pi.div_apply] using (hnum.div hden (by norm_num : (1 : ℂ) ≠ 0) : _)
  have hEq :
      ψS =
        fun z : ℍ =>
          -((128 : ℂ) *
              (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2))) /
            ((H₃ z) ^ 2 * (H₄ z) ^ 2) := by
    funext z
    simp [ψS_apply_eq_factor]
  simpa [hEq] using hdiv

lemma tendsto_ψS_resToImagAxis_atTop :
    Tendsto (fun t : ℝ => ψS.resToImagAxis t) atTop (𝓝 (0 : ℂ)) := by
  simpa using
    Function.tendsto_resToImagAxis_atImInfty (F := ψS) (l := (0 : ℂ)) tendsto_ψS_atImInfty

/-- Uniform bound for `‖ψS.resToImagAxis t‖` on `Ici (1 : ℝ)`. -/
public lemma exists_bound_norm_ψS_resToImagAxis_Ici_one :
    ∃ M, ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ M := by
  have htend' : Tendsto (fun t : ℝ => ‖ψS.resToImagAxis t‖) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_zero_iff_norm_tendsto_zero).1 tendsto_ψS_resToImagAxis_atTop
  have hEv_lt : ∀ᶠ t in atTop, ‖ψS.resToImagAxis t‖ < (1 : ℝ) :=
    htend'.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  rcases (eventually_atTop.1 hEv_lt) with ⟨A, hA⟩
  let B : ℝ := max A 1
  have hB : 1 ≤ B := le_max_right _ _
  have hcontOn : ContinuousOn (fun t : ℝ => ‖ψS.resToImagAxis t‖) (Icc 1 B) := by
    have hres : ContinuousOn (ψS.resToImagAxis) (Icc 1 B) :=
      (Function.continuousOn_resToImagAxis_Ioi_of (F := ψS) continuous_ψS).mono fun _ ht =>
        lt_of_lt_of_le (by norm_num) ht.1
    simpa using (continuous_norm.comp_continuousOn hres)
  obtain ⟨C, hC⟩ := SpherePacking.ForMathlib.exists_upper_bound_on_Icc (hab := hB) (hg := hcontOn)
  refine ⟨max C 1, ?_⟩
  intro t ht
  by_cases htB : t ≤ B
  · exact (hC t ⟨ht, htB⟩).trans (le_max_left _ _)
  · have htA : A ≤ t := le_trans (le_max_left _ _) (le_of_not_ge htB)
    exact (hA t htA).le.trans (le_max_right _ _)

end MagicFunction.b.PsiBounds
