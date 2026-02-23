module

public import Mathlib.Init
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import SpherePacking.Integration.Measure
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.IntegrablePowMulExp

/-!
# Differentiation under the integral sign on `Ici 1`

This file provides a reusable dominated-differentiation lemma for integrals over `Ici 1`.
It is used in several magic-function developments (e.g. the `I₆'` and `J₆'` smoothness proofs).
-/

namespace SpherePacking.Integration.SmoothIntegralIciOne
noncomputable section

open scoped Topology
open Complex Real Set MeasureTheory Filter

open SpherePacking.Integration (μIciOne)

/-- The coefficient function used in the exponential weight. -/
@[expose] public def coeff (t : ℝ) : ℂ := (-Real.pi * t : ℂ)

/-- The basic integrand `t ↦ I * (hf t * exp (x * coeff t))`. -/
@[expose] public def g (hf : ℝ → ℂ) (x t : ℝ) : ℂ :=
  (Complex.I : ℂ) * (hf t * cexp ((x : ℂ) * coeff t))

/-- The auxiliary integrand `gN n`, corresponding to the `n`-th derivative in `x`. -/
@[expose] public def gN (hf : ℝ → ℂ) (n : ℕ) (x t : ℝ) : ℂ :=
  (coeff t) ^ n * g (hf := hf) x t

/-- Norm of `coeff t` on `Ici 1`. -/
public lemma coeff_norm (t : ℝ) (ht : t ∈ Set.Ici (1 : ℝ)) : ‖coeff t‖ = Real.pi * t := by
  simp [coeff, Complex.norm_real, abs_of_nonneg Real.pi_pos.le,
    abs_of_nonneg (zero_le_one.trans (by simpa [Set.mem_Ici] using ht))]

/-- A crude bound on the integrand `g` in terms of `‖hf t‖` and `exp (-π * x * t)`. -/
public lemma g_norm_bound (hf : ℝ → ℂ) (x t : ℝ) :
    ‖g (hf := hf) x t‖ ≤ ‖hf t‖ * Real.exp (-Real.pi * x * t) := by
  simp [g, coeff, Complex.norm_exp, mul_left_comm, mul_comm]

/-- Differentiate under the integral sign for `∫ t ∈ Ici 1, gN n x t`, under standard bounds. -/
public lemma hasDerivAt_integral_gN
    {hf : ℝ → ℂ} {shift : ℝ} (hshift : 1 ≤ shift)
    (exists_bound_norm_hf :
      ∃ C, ∀ t : ℝ, 1 ≤ t → ‖hf t‖ ≤ C * Real.exp (-(Real.pi * shift) * t))
    (gN_measurable :
      ∀ n : ℕ, ∀ x : ℝ, AEStronglyMeasurable (gN (hf := hf) n x) μIciOne)
    (n : ℕ) (x : ℝ) (hx : -1 < x)
    (hF_int : Integrable (gN (hf := hf) n x) μIciOne) :
    HasDerivAt (fun y : ℝ ↦ ∫ t in Set.Ici (1 : ℝ), gN (hf := hf) n y t)
      (∫ t in Set.Ici (1 : ℝ), gN (hf := hf) (n + 1) x t) x := by
  have hxshift : 0 < x + shift := by linarith
  -- Shrink the neighborhood so that `x + shift` stays uniformly positive.
  let ε : ℝ := (x + shift) / 2
  have ε_pos : 0 < ε := by
    simpa [ε] using (half_pos hxshift)
  obtain ⟨C, hC⟩ := exists_bound_norm_hf
  have hC0 : 0 ≤ C := by
    refine SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖hf 1‖)
      (b := Real.exp (-(Real.pi * shift) * (1 : ℝ))) (C := C) (norm_nonneg _) (by positivity) ?_
    simpa using (hC 1 (le_rfl : (1 : ℝ) ≤ 1))
  have hb : 0 < Real.pi * ε := mul_pos Real.pi_pos ε_pos
  let bound : ℝ → ℝ :=
    fun t ↦ (Real.pi ^ (n + 1)) * (t ^ (n + 1) * Real.exp (-(Real.pi * ε) * t)) * C
  have hbound_int : Integrable bound μIciOne := by
    have hInt : Integrable (fun t : ℝ ↦ t ^ (n + 1) * Real.exp (-(Real.pi * ε) * t)) μIciOne := by
      simpa [IntegrableOn, μIciOne, mul_assoc] using
        (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n + 1)
          (b := Real.pi * ε) (by simpa [mul_assoc] using hb))
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using hInt.const_mul ((Real.pi ^ (n + 1)) * C)
  have h_bound :
      ∀ᵐ t ∂μIciOne, ∀ y ∈ Metric.ball x ε, ‖gN (hf := hf) (n + 1) y t‖ ≤ bound t := by
    refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
    intro t ht y hy
    have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
    have hy0 : ε ≤ y + shift := by
      have hdist : |y - x| < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hy
      have : x - ε < y := by nlinarith [abs_lt.1 hdist |>.1]
      have : x + shift - ε < y + shift := by linarith
      have hε_def : x + shift - ε = ε := by
        dsimp [ε]
        ring_nf
      exact le_of_lt (by simpa [hε_def] using this)
    have hlin : (-(Real.pi * (y + shift)) * t : ℝ) ≤ (-(Real.pi * ε) * t) := by
      have hπ : (Real.pi : ℝ) * ε ≤ (Real.pi : ℝ) * (y + shift) :=
        mul_le_mul_of_nonneg_left hy0 Real.pi_pos.le
      have ht' : (Real.pi * ε) * t ≤ (Real.pi * (y + shift)) * t :=
        mul_le_mul_of_nonneg_right hπ ht0
      have := neg_le_neg ht'
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hexp2 : Real.exp (-(Real.pi * (y + shift)) * t) ≤ Real.exp (-(Real.pi * ε) * t) :=
      Real.exp_le_exp.2 hlin
    have hcoeff : ‖coeff t‖ ^ (n + 1) ≤ (Real.pi * t) ^ (n + 1) := by
      have : ‖coeff t‖ = Real.pi * t := coeff_norm (t := t) ht
      simp [this]
    have hhf : ‖hf t‖ ≤ C * Real.exp (-(Real.pi * shift) * t) := hC t ht
    have hg : ‖g (hf := hf) y t‖ ≤ C * Real.exp (-(Real.pi * (y + shift)) * t) := by
      have hg' : ‖g (hf := hf) y t‖ ≤ ‖hf t‖ * Real.exp (-Real.pi * y * t) :=
        g_norm_bound (hf := hf) (x := y) (t := t)
      have hexp :
          Real.exp (-(Real.pi * shift) * t) * Real.exp (-Real.pi * y * t) =
            Real.exp (-(Real.pi * (y + shift)) * t) := by
        have harg :
            (-(Real.pi * (y + shift)) * t) =
              (-(Real.pi * shift) * t) + (-Real.pi * y * t) := by ring_nf
        simp [harg, Real.exp_add, mul_comm]
      calc
        ‖g (hf := hf) y t‖ ≤ ‖hf t‖ * Real.exp (-Real.pi * y * t) := hg'
        _ ≤ (C * Real.exp (-(Real.pi * shift) * t)) * Real.exp (-Real.pi * y * t) := by gcongr
        _ = C * Real.exp (-(Real.pi * (y + shift)) * t) := by
          calc
            (C * Real.exp (-(Real.pi * shift) * t)) * Real.exp (-Real.pi * y * t)
                =
                C * (Real.exp (-(Real.pi * shift) * t) * Real.exp (-Real.pi * y * t)) := by
                  ring_nf
            _ = C * Real.exp (-(Real.pi * (y + shift)) * t) := by
              rw [hexp]
    calc
      ‖gN (hf := hf) (n + 1) y t‖ = ‖coeff t‖ ^ (n + 1) * ‖g (hf := hf) y t‖ := by
            simp [gN, norm_pow]
      _ ≤ (Real.pi * t) ^ (n + 1) * (C * Real.exp (-(Real.pi * (y + shift)) * t)) := by
            gcongr
      _ ≤ (Real.pi * t) ^ (n + 1) * (C * Real.exp (-(Real.pi * ε) * t)) := by
            gcongr
      _ = bound t := by
            simp [bound, mul_pow, mul_assoc, mul_left_comm, mul_comm]
  have h_diff :
      ∀ᵐ t ∂μIciOne, ∀ y ∈ Metric.ball x ε,
        HasDerivAt (fun y : ℝ ↦ gN (hf := hf) n y t) (gN (hf := hf) (n + 1) y t) y := by
    refine ae_of_all _ fun t y _ => ?_
    have hg : HasDerivAt (fun y : ℝ ↦ g (hf := hf) y t) (coeff t * g (hf := hf) y t) y := by
      simpa [g, mul_assoc, mul_left_comm, mul_comm] using
        (SpherePacking.ForMathlib.hasDerivAt_mul_cexp_ofReal_mul_const
          (a := (Complex.I : ℂ) * (hf t)) (c := coeff t) y)
    have h := hg.const_mul ((coeff t) ^ n)
    simpa [gN, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h
  -- Apply dominated differentiation.
  simpa [μIciOne, ε] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μIciOne)
      (s := Metric.ball x ε) (F := fun y t ↦ gN (hf := hf) n y t) (x₀ := x)
      (Metric.ball_mem_nhds x ε_pos)
      (hF_meas := Eventually.of_forall fun y ↦ gN_measurable n y) (hF_int := hF_int)
      (hF'_meas := gN_measurable (n + 1) x)
      (h_bound := h_bound) (bound_integrable := hbound_int) (h_diff := h_diff)).2

end

end SpherePacking.Integration.SmoothIntegralIciOne
