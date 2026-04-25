module
public import SpherePacking.MagicFunction.IntegralParametrisations
public import SpherePacking.ModularForms.ResToImagAxis


/-!
# Modular rewrite on the `z₁'` segment

This file contains shared continuity and boundedness lemmas for rewriting modular-form expressions
along the parametrised segment `t ↦ z₁' t`.
-/

namespace MagicFunction

open scoped Interval

open Complex Real Set
open MagicFunction.Parametrisations UpperHalfPlane

/-- A generic continuity lemma for a modular rewrite on `Ioc 0 1`.

This is stated for a general parametrisation `z` and an identity `hEq` expressing `ψT' (z t)` in
terms of the restriction of `ψS` to the imaginary axis and the factor `((I : ℂ) * t)^k`.
-/
public lemma continuousOn_ψT'_Ioc_of (k : ℕ) (ψS : ℍ → ℂ) (ψT' : ℂ → ℂ) (z : ℝ → ℂ)
    (hψS : ContinuousOn ψS.resToImagAxis (Ici (1 : ℝ)))
    (hEq : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ψT' (z t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ k) :
    ContinuousOn (fun t : ℝ => ψT' (z t)) (Ioc (0 : ℝ) 1) := by
  have hpow : Continuous fun t : ℝ => ((Complex.I : ℂ) * (t : ℂ)) ^ k := by
    simpa using (continuous_const.mul Complex.continuous_ofReal).pow k
  have hcont_one_div : ContinuousOn (fun t : ℝ => (1 / t : ℝ)) (Ioc (0 : ℝ) 1) := by
    simpa [one_div] using
      (continuousOn_inv₀ : ContinuousOn (fun t : ℝ => (t : ℝ)⁻¹) ({0}ᶜ)).mono
        (fun t ht => by simp [ne_of_gt ht.1])
  exact ((hψS.comp hcont_one_div (fun t ht => one_le_one_div ht.1 ht.2)).mul
    hpow.continuousOn).congr hEq

/-- Continuity of the modular rewrite along the segment `t ↦ z₁' t` on `(0, 1)`. -/
public lemma continuousOn_ψT'_z₁'_of (k : ℕ) (ψS : ℍ → ℂ) (ψT' : ℂ → ℂ)
    (hψS : ContinuousOn ψS.resToImagAxis (Ici (1 : ℝ)))
    (hEq : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ψT' (z₁' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ k) :
    ContinuousOn (fun t : ℝ => ψT' (z₁' t)) (Ioo (0 : ℝ) 1) :=
  (continuousOn_ψT'_Ioc_of (k := k) (ψS := ψS) (ψT' := ψT') (z := z₁') hψS hEq).mono
    (fun _ ht => ⟨ht.1, le_of_lt ht.2⟩)

/-- A uniform bound for `‖ψT' (z₁' t)‖` on `t ∈ (0, 1)`, assuming a bound for `ψS` on `Ici 1`. -/
public lemma exists_bound_norm_ψT'_z₁'_of (k : ℕ) (ψS : ℍ → ℂ) (ψT' : ℂ → ℂ)
    (hBound : ∃ M : ℝ, ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ M)
    (hEq : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ψT' (z₁' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ k) :
    ∃ M : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ‖ψT' (z₁' t)‖ ≤ M := by
  obtain ⟨M, hM⟩ := hBound
  refine ⟨M, fun t ht => ?_⟩
  have htIoc : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  have hψS : ‖ψS.resToImagAxis (1 / t)‖ ≤ M := hM (1 / t) (one_le_one_div ht.1 ht.2.le)
  have htK : t ^ k ≤ (1 : ℝ) := by simpa using pow_le_one₀ (n := k) ht.1.le ht.2.le
  have hnorm : ‖((Complex.I : ℂ) * (t : ℂ)) ^ k‖ = t ^ k := by
    simp [norm_pow, Complex.norm_real, abs_of_nonneg ht.1.le]
  calc
    ‖ψT' (z₁' t)‖ = ‖ψS.resToImagAxis (1 / t)‖ * ‖((Complex.I : ℂ) * (t : ℂ)) ^ k‖ := by
      simp [hEq t htIoc]
    _ = ‖ψS.resToImagAxis (1 / t)‖ * t ^ k := by simp [hnorm]
    _ ≤ M * t ^ k := mul_le_mul_of_nonneg_right hψS (pow_nonneg ht.1.le k)
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left htK ((norm_nonneg _).trans hψS)
    _ = M := mul_one M

/-- A pointwise bound for a modular rewrite on `Ioc 0 1`, given a bound on `ψS.resToImagAxis`. -/
public lemma norm_modular_rewrite_Ioc_bound (k : ℕ) (ψS : ℍ → ℂ) (ψZ : ℂ → ℂ) (z : ℝ → ℂ)
    (hEq : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ψZ (z t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ k)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) {B : ℝ} (hB : ‖ψS.resToImagAxis (1 / t)‖ ≤ B) :
    ‖ψZ (z t)‖ ≤ B * t ^ k := by
  have ht0' : 0 ≤ t := le_of_lt ht.1
  have hnorm : ‖((Complex.I : ℂ) * (t : ℂ)) ^ k‖ = t ^ k := by
    simp [norm_pow, Complex.norm_real, abs_of_nonneg ht0']
  calc
    ‖ψZ (z t)‖ = ‖ψS.resToImagAxis (1 / t)‖ * ‖((Complex.I : ℂ) * (t : ℂ)) ^ k‖ := by
      simp [hEq t ht]
    _ = ‖ψS.resToImagAxis (1 / t)‖ * t ^ k := by simp [hnorm]
    _ ≤ B * t ^ k := mul_le_mul_of_nonneg_right hB (pow_nonneg ht0' k)

/-- A pointwise bound for a modular rewrite on `Ioc 0 1` with exponential decay input. -/
public lemma norm_modular_rewrite_Ioc_exp_bound (k : ℕ) (Cψ : ℝ) (ψS : ℍ → ℂ) (ψZ : ℂ → ℂ)
    (z : ℝ → ℂ)
    (hCψ : ∀ y : ℝ, 1 ≤ y → ‖ψS.resToImagAxis y‖ ≤ Cψ * Real.exp (-Real.pi * y))
    (hEq : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ψZ (z t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ k)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖ψZ (z t)‖ ≤ Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ k :=
  norm_modular_rewrite_Ioc_bound k ψS ψZ z hEq ht (hCψ (1 / t) (one_le_one_div ht.1 ht.2))

end MagicFunction
