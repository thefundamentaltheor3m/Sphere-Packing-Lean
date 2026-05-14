module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.NormNum
import SpherePacking.ForMathlib.DerivHelpers

/-!
# Inversion change of variables and endpoint integrability on `Ioc (0, 1]`

Collects change-of-variables lemmas for the substitution `t ↦ 1 / t` on `Ioc (0, 1]`,
rewriting integrals over `Ioc (0, 1]` into integrals over `Ici 1` using the one-dimensional
Jacobian formula, and uses these to obtain endpoint integrability of weights such as
`(1 / t ^ 2) * exp (-c / t)` on `Ioc (0, 1]`.
-/

namespace SpherePacking.Integration

noncomputable section

open Set MeasureTheory

namespace InvChangeOfVariables

open Complex Real

/-- Simplify the Jacobian factor and an inverse power after substituting `t ↦ 1 / t`:
`(1 / t ^ 2) * (1 / t) ^ (-k) = t ^ (k - 2)` for `2 ≤ k` and `t ≠ 0`. -/
public lemma one_div_pow_two_mul_one_div_zpow (k : ℕ) (t : ℝ) (hk : 2 ≤ k) (ht : t ≠ 0) :
    (1 / t ^ 2) * ((1 / t : ℝ) ^ (-(k : ℤ))) = t ^ (k - 2) := by
  have hzpow : (1 / t : ℝ) ^ (-(k : ℤ)) = t ^ k := by rw [one_div]; simp [zpow_natCast]
  simpa [one_div, hzpow, mul_assoc, mul_left_comm, mul_comm] using (pow_sub₀ t ht hk).symm

/-- The image of `t ↦ 1 / t` on `Ioc (0, 1]` is `Ici 1`. -/
public lemma Ici_one_eq_image_inv_Ioc :
    Ici (1 : ℝ) = (fun t : ℝ ↦ 1 / t) '' (Ioc (0 : ℝ) (1 : ℝ)) := by
  refine Set.eq_of_subset_of_subset (fun x hx ↦ ?_) ?_
  · have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
    exact ⟨x⁻¹, ⟨by simpa [one_div] using inv_pos.2 hx0,
      by simpa [one_div] using (inv_le_one₀ hx0).2 hx⟩, by simp⟩
  · rintro _ ⟨y, hy, rfl⟩
    simpa [one_div, mem_Ici] using one_le_inv_iff₀.2 hy

/-- Change-of-variables formula for `t ↦ 1 / t` from `Ici 1` back to `Ioc (0, 1]`. -/
public lemma integral_Ici_one_eq_integral_abs_deriv_smul (g : ℝ → ℂ) :
    ∫ s in Ici (1 : ℝ), g s = ∫ t in Ioc (0 : ℝ) 1, |(-1 / t ^ 2)| • g (1 / t) := by
  rw [Ici_one_eq_image_inv_Ioc]
  refine integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun x hx ↦ by
      simpa [one_div, div_eq_mul_inv] using
        hasDerivWithinAt_inv (x := x) (ne_of_gt hx.1) (Ioc 0 1))
    (fun x _ y _ hxy ↦ inv_inj.1 (by simpa [one_div] using hxy)) g

end InvChangeOfVariables

/-- Integrability of the endpoint weight `(1 / t ^ 2) * exp (-c / t)` on `Ioc (0, 1]` for `c > 0`.
-/
public lemma integrableOn_one_div_sq_mul_exp_neg_div (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ ↦ (1 / t ^ 2) * Real.exp (-c / t)) (Set.Ioc (0 : ℝ) 1) volume := by
  let s : Set ℝ := Set.Ioc (0 : ℝ) 1
  let f : ℝ → ℝ := fun t ↦ (1 : ℝ) / t
  let f' : ℝ → ℝ := fun t ↦ -(1 : ℝ) / t ^ 2
  have hs : MeasurableSet s := measurableSet_Ioc
  have hf' : ∀ t ∈ s, HasDerivWithinAt f (f' t) s t := fun t ht => by
    simpa [f, f', one_div, div_eq_mul_inv, pow_two, ne_of_gt ht.1] using
      (hasDerivAt_inv (ne_of_gt ht.1)).hasDerivWithinAt
  have hfinj : Set.InjOn f s := fun a _ b _ hab =>
    inv_injective (by simpa [f, one_div] using hab)
  have himage : f '' s = Set.Ici (1 : ℝ) := by
    simpa [f, s] using (InvChangeOfVariables.Ici_one_eq_image_inv_Ioc).symm
  have hmain : IntegrableOn (fun t : ℝ ↦ |f' t| * Real.exp (-(c * f t))) s volume := by
    have : IntegrableOn (fun y : ℝ ↦ Real.exp (-(c * y))) (f '' s) volume := by
      simpa [himage, pow_zero, one_mul] using
        (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 0) (b := c) hc)
    simpa [smul_eq_mul] using
      (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul (hs := hs) (hf' := hf')
        (hf := hfinj) (g := fun y : ℝ ↦ Real.exp (-(c * y)))).1 this
  refine hmain.congr_fun (hs := hs) fun t _ => ?_
  simp [f', f, abs_div, abs_of_nonneg (pow_two_nonneg t), div_eq_mul_inv]

end

end SpherePacking.Integration
