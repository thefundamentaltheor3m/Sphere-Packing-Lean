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
  have hC_nonneg : 0 ≤ C := by
    refine ForMathlib.nonneg_of_nonneg_le_mul (a := ‖f 1‖)
      (b := Real.exp (-Real.pi * (1 : ℝ))) (C := C) (norm_nonneg _) (by positivity) ?_
    simpa using (hC 1 (le_rfl : (1 : ℝ) ≤ 1))
  have hb : 0 < Real.pi * (x + 1) := mul_pos Real.pi_pos (by linarith)
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))
  let bound : ℝ → ℝ :=
    fun t ↦ (Real.pi ^ n) * (t ^ n * Real.exp (-(Real.pi * (x + 1)) * t)) * C
  have hbound_int : Integrable bound μ := by
    have hInt :
        IntegrableOn (fun t : ℝ ↦ t ^ n * Real.exp (-(Real.pi * (x + 1)) * t)) (Ici (1 : ℝ))
          volume :=
      ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := Real.pi * (x + 1))
        (by simpa [mul_assoc] using hb)
    have : Integrable (fun t : ℝ ↦ t ^ n * Real.exp (-(Real.pi * (x + 1)) * t)) μ := by
      simpa [IntegrableOn, μ] using hInt
    simpa [bound, μ, mul_assoc, mul_left_comm, mul_comm] using this.const_mul ((Real.pi ^ n) * C)
  refine Integrable.mono' hbound_int (by simpa [μ] using hmeas) ?_
  refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
  intro t ht
  have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
  have hf : ‖f t‖ ≤ C * Real.exp (-Real.pi * t) := hC t ht
  have hg' :
      ‖(Complex.I : ℂ) * (f t * cexp ((x : ℂ) * (-Real.pi * t : ℂ)))‖ =
        ‖f t‖ * Real.exp (-Real.pi * x * t) := by
    simp [Complex.norm_exp, mul_left_comm, mul_comm]
  have hexp :
      Real.exp (-Real.pi * t) * Real.exp (-Real.pi * x * t) =
        Real.exp (-(Real.pi * (x + 1)) * t) := by
    have harg : (-(Real.pi * (x + 1)) * t) = (-Real.pi * t) + (-Real.pi * x * t) := by ring_nf
    simp [harg, Real.exp_add, mul_comm]
  calc
    ‖gN_J6_integrand f n x t‖
        = ‖(-Real.pi * t : ℂ)‖ ^ n *
            ‖(Complex.I : ℂ) * (f t * cexp ((x : ℂ) * (-Real.pi * t : ℂ)))‖ := by
          simp [gN_J6_integrand, norm_pow]
    _ = ‖(-Real.pi * t : ℂ)‖ ^ n * (‖f t‖ * Real.exp (-Real.pi * x * t)) := by
          rw [hg']
    _ = (Real.pi * t) ^ n * (‖f t‖ * Real.exp (-Real.pi * x * t)) := by
          have hn : ‖(-Real.pi * t : ℂ)‖ = Real.pi * t := by
            simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_nonneg ht0]
          -- avoid `simp` cancelling the common factor
          rw [hn]
    _ ≤ (Real.pi * t) ^ n * ((C * Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * x * t)) := by
          gcongr
    _ = bound t := by
          have hp : (Real.pi * t) ^ n = (Real.pi ^ n) * t ^ n := by
            simp [mul_pow, mul_comm]
          have hmulExp :
              (C * Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * x * t) =
                C * Real.exp (-(Real.pi * (x + 1)) * t) := by
            calc
              (C * Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * x * t) =
                  C * (Real.exp (-Real.pi * t) * Real.exp (-Real.pi * x * t)) := by ring_nf
              _ = C * Real.exp (-(Real.pi * (x + 1)) * t) := by rw [hexp]
          rw [hp, hmulExp]
          simp [bound, mul_assoc, mul_left_comm, mul_comm]

end

end SpherePacking.Integration
