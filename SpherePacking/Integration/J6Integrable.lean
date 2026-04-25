module
public import SpherePacking.ForMathlib.IntegrablePowMulExp
public import SpherePacking.ForMathlib.DerivHelpers
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Integrability for `J₆'`-type integrands

This file provides a reusable integrability lemma for the `J₆'`-type integrands on `Ici 1`.
-/

namespace SpherePacking.Integration

noncomputable section

open Complex Real Set MeasureTheory Filter

/-- The `n`-th `x`-derivative integrand appearing in `J₆'`-type formulas. -/
@[expose] public def gN_J6_integrand (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℝ → ℂ :=
  fun t : ℝ =>
    ((-Real.pi * t : ℂ) ^ n) *
      ((Complex.I : ℂ) * (f t * cexp ((x : ℂ) * (-Real.pi * t : ℂ))))

/-- Integrability of `gN_J6_integrand` on `Ici 1` under an exponential bound on `f`. -/
public lemma integrable_gN_J6 (f : ℝ → ℂ)
    (hBound : ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * Real.exp (-Real.pi * t))
    (n : ℕ) (x : ℝ) (hx : -1 < x)
    (hmeas :
      AEStronglyMeasurable (gN_J6_integrand f n x)
        ((volume : Measure ℝ).restrict (Ici (1 : ℝ)))) :
    Integrable
      (gN_J6_integrand f n x)
      ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) := by
  rcases hBound with ⟨C, hC⟩
  have hC_nonneg : 0 ≤ C :=
    ForMathlib.nonneg_of_nonneg_le_mul (a := ‖f 1‖) (b := Real.exp (-Real.pi * (1 : ℝ)))
      (C := C) (norm_nonneg _) (by positivity) (by simpa using hC 1 le_rfl)
  have hb : 0 < Real.pi * (x + 1) := mul_pos Real.pi_pos (by linarith)
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))
  let bound : ℝ → ℝ :=
    fun t ↦ (Real.pi ^ n) * (t ^ n * Real.exp (-(Real.pi * (x + 1)) * t)) * C
  have hbound_int : Integrable bound μ := by
    have hInt := ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := Real.pi * (x + 1))
      (by simpa [mul_assoc] using hb)
    simpa [bound, μ, IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using
      (hInt : Integrable _ _).const_mul ((Real.pi ^ n) * C)
  refine Integrable.mono' hbound_int (by simpa [μ] using hmeas) ?_
  refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
  intro t ht
  have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
  calc
    ‖gN_J6_integrand f n x t‖
        = (Real.pi * t) ^ n * (‖f t‖ * Real.exp (-Real.pi * x * t)) := by
          simp [gN_J6_integrand, norm_pow, Complex.norm_exp, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_nonneg ht0,
            mul_left_comm, mul_comm]
    _ ≤ (Real.pi * t) ^ n * ((C * Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * x * t)) := by
          gcongr
          exact hC t ht
    _ = bound t := by
          change (Real.pi * t) ^ n * ((C * Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * x * t)) =
            (Real.pi ^ n) * (t ^ n * Real.exp (-(Real.pi * (x + 1)) * t)) * C
          rw [show (-(Real.pi * (x + 1)) * t) = (-Real.pi * t) + (-Real.pi * x * t) by ring_nf,
            Real.exp_add]
          ring

end

end SpherePacking.Integration
