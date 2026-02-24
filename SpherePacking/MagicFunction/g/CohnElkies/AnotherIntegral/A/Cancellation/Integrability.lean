module
public import Mathlib.Init
public import
SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.LargeImagApprox

/-!
# Integrability of the `AnotherIntegral.A` integrand

This file proves that the integrand `aAnotherIntegrand u` is integrable on `(0, ∞)` for `0 < u`.
The main work is on the tail `[1, ∞)`, where we use cancellation and exponential decay coming from
large-imaginary-part bounds for `φ₂'` and `φ₄'`.

## Main statement
* `aAnotherIntegrand_integrable_of_pos`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Topology MatrixGroups CongruenceSubgroup ModularForm NNReal ENNReal
open scoped ArithmeticFunction.sigma

open Real Complex MeasureTheory Filter Function
open ArithmeticFunction

open MagicFunction.FourierEigenfunctions
open UpperHalfPlane ModularForm EisensteinSeries
open SlashInvariantFormClass ModularFormClass

noncomputable section

/-! ## Asymptotic/cancellation bound for integrability on `[1,∞)`. -/

lemma exp_neg2piA_le_tpow2_mul_exp_neg2pit {A t : ℝ} (ht1 : 1 ≤ t) (htA : t ≤ A) :
    Real.exp (-2 * π * A) ≤ (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
  have hexp : Real.exp (-2 * π * A) ≤ Real.exp (-2 * π * t) := by
    refine Real.exp_le_exp.2 ?_
    have hconst : (-2 * π : ℝ) ≤ 0 := by nlinarith [Real.pi_pos]
    exact mul_le_mul_of_nonpos_left htA hconst
  have ht2 : (1 : ℝ) ≤ t ^ (2 : ℕ) := by nlinarith [ht1]
  exact hexp.trans <| by
    have hexp0 : 0 ≤ Real.exp (-2 * π * t) := (Real.exp_pos _).le
    simpa [one_mul] using mul_le_mul_of_nonneg_right ht2 hexp0

lemma M_le_divExp_mul_tpow2_exp {M A t : ℝ} (hM0 : 0 ≤ M) (ht1 : 1 ≤ t) (htA : t ≤ A) :
    M ≤ (M / Real.exp (-2 * π * A)) * ((t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) := by
  have hden_le : Real.exp (-2 * π * A) ≤ (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) :=
    exp_neg2piA_le_tpow2_mul_exp_neg2pit (A := A) (t := t) ht1 htA
  have hcoef0 : 0 ≤ M / Real.exp (-2 * π * A) := div_nonneg hM0 (Real.exp_pos _).le
  have hmul :=
    mul_le_mul_of_nonneg_left hden_le hcoef0
  have hleft : (M / Real.exp (-2 * π * A)) * Real.exp (-2 * π * A) = M := by
    field_simp [Real.exp_ne_zero]
  simpa [hleft] using hmul

lemma phi0Cancellation_compact_case {M A C t : ℝ} (ht1 : 1 ≤ t) (htA : t ≤ A)
    (hbound :
      ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
            ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
            ((8640 / π : ℝ) : ℂ) * t -
            ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖ ≤ M)
    (hCle : M / Real.exp (-2 * π * A) ≤ C) :
    ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
          ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
          ((8640 / π : ℝ) : ℂ) * t -
          ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖ ≤
      C * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hbound
  have hscale :
      M ≤ (M / Real.exp (-2 * π * A)) * ((t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) :=
    M_le_divExp_mul_tpow2_exp (M := M) (A := A) (t := t) hM0 ht1 htA
  have hfac0 : 0 ≤ (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by positivity
  have hmul :
      (M / Real.exp (-2 * π * A)) * ((t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) ≤
        C * ((t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) :=
    mul_le_mul_of_nonneg_right hCle hfac0
  have hMle : M ≤ C * ((t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) :=
    hscale.trans hmul
  have hfinal : ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
        ((8640 / π : ℝ) : ℂ) * t -
        ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖ ≤
      C * ((t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) :=
    le_trans hbound hMle
  simpa [mul_assoc] using hfinal

lemma exists_phi0_cancellation_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 1 ≤ t →
        ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
              ((8640 / π : ℝ) : ℂ) * t -
              ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖ ≤
          C * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
  rcases norm_φ₀_imag_le with ⟨C₀, hC₀pos, hφ₀⟩
  rcases exists_phi2'_sub_720_bound_ge with ⟨C₂, A₂, hC₂pos, hA₂, hφ₂⟩
  rcases exists_phi4'_sub_exp_sub_504_bound_ge with ⟨C₄, A₄, hC₄pos, hA₄, hφ₄⟩
  let A : ℝ := max A₂ A₄
  have hA1 : 1 ≤ A := le_trans hA₂ (le_max_left _ _)
  have hA₂' : A₂ ≤ A := le_max_left _ _
  have hA₄' : A₄ ≤ A := le_max_right _ _
  -- Rewrite the cancellation expression using the `S`-transform.
  -- Also expand the `φ₂'`/`φ₄'` principal parts.
  have hrewrite :
      ∀ {t : ℝ} (ht0 : 0 < t),
        (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
              ((8640 / π : ℝ) : ℂ) * t -
              ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) =
          (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ (zI t ht0) -
              ((12 / π : ℝ) : ℂ) * t * (φ₂' (zI t ht0) - (720 : ℂ)) +
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
                (φ₄' (zI t ht0) - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))) := by
    intro t ht0
    let z : ℍ := zI t ht0
    have htinv : 0 < t⁻¹ := inv_pos.2 ht0
    have hS : ModularGroup.S • z = zI t⁻¹ htinv := by
      simpa [z] using modular_S_smul_zI t ht0
    have hcoe : ((ModularGroup.S • z : ℍ) : ℂ) = (Complex.I : ℂ) / (t : ℂ) := by
      calc
        ((ModularGroup.S • z : ℍ) : ℂ) = (Complex.I : ℂ) * (t⁻¹ : ℂ) := by
          have : ((ModularGroup.S • z : ℍ) : ℂ) = ((zI t⁻¹ htinv : ℍ) : ℂ) := by
            simp [hS]
          simpa [zI] using this
        _ = (Complex.I : ℂ) / (t : ℂ) := by
          simp [div_eq_mul_inv]
    have hφ₀S : φ₀'' ((Complex.I : ℂ) / (t : ℂ)) = φ₀ (ModularGroup.S • z) := by
      have hcoe' :
          (Complex.I : ℂ) / (t : ℂ) = ((ModularGroup.S • z : ℍ) : ℂ) := hcoe.symm
      calc
        φ₀'' ((Complex.I : ℂ) / (t : ℂ))
            = φ₀'' ((ModularGroup.S • z : ℍ) : ℂ) := by
                simpa using congrArg φ₀'' hcoe'
        _ = φ₀ (ModularGroup.S • z) := by
              simp
    have hzsq : (z : ℂ) ^ (2 : ℕ) = -((t ^ (2 : ℕ) : ℝ) : ℂ) := by
      dsimp [z, zI]
      calc
        ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ)
            = (Complex.I : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (2 : ℕ) := by
                simpa using (mul_pow (Complex.I : ℂ) (t : ℂ) 2)
        _ = (-1 : ℂ) * (t : ℂ) ^ (2 : ℕ) := by simp
        _ = -((t : ℂ) ^ (2 : ℕ)) := by simp
        _ = -((t ^ (2 : ℕ) : ℝ) : ℂ) := by
            simp only [ofReal_pow]
    have hST' :
        ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ (ModularGroup.S • z) =
          ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z -
            ((12 / π : ℝ) : ℂ) * t * φ₂' z +
            ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * φ₄' z := by
      -- Multiply the `S`-transform identity by `-1` and use `(it)^2 = -t^2`.
      have h0 := φ₀_S_transform_mul_sq z
      -- Substitute `(z : ℂ)^2 = -t^2`.
      have h0' :
          φ₀ (ModularGroup.S • z) * (-((t ^ (2 : ℕ) : ℝ) : ℂ)) =
            φ₀ z * (-((t ^ (2 : ℕ) : ℝ) : ℂ)) -
              (12 * Complex.I) / π * (z : ℂ) * φ₂' z - 36 / (π ^ 2) * φ₄' z := by
        simpa [hzsq] using h0
      -- Rewrite RHS using only addition, then negate both sides.
      have h0'' :
          φ₀ (ModularGroup.S • z) * (-((t ^ (2 : ℕ) : ℝ) : ℂ)) =
            φ₀ z * (-((t ^ (2 : ℕ) : ℝ) : ℂ)) +
              (-( (12 * Complex.I) / π * (z : ℂ) * φ₂' z)) +
              (-(36 / (π ^ 2) * φ₄' z)) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using h0'
      have hneg := congrArg (fun w : ℂ => -w) h0''
      have hneg' :
          (t : ℂ) * ((t : ℂ) * φ₀ (ModularGroup.S • z)) =
            (t : ℂ) * ((t : ℂ) * φ₀ z) +
              (36 / ((π : ℂ) * (π : ℂ)) * φ₄' z +
                (Complex.I : ℂ) * 12 / (π : ℂ) * (φ₂' z * (z : ℂ))) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
          mul_assoc, mul_left_comm, mul_comm, pow_two, neg_add, neg_mul,
          mul_neg, neg_neg] using hneg
      have hcoeffTerm :
          (Complex.I : ℂ) * 12 / (π : ℂ) * (φ₂' z * (z : ℂ)) =
            -((t : ℂ) * ((12 : ℂ) / (π : ℂ) * φ₂' z)) := by
        dsimp [z, zI]
        ring_nf
        simp
      -- Rewrite the `φ₂'` term using `z = i t`.
      have hneg'' :
          (t : ℂ) * ((t : ℂ) * φ₀ (ModularGroup.S • z)) =
            (t : ℂ) * ((t : ℂ) * φ₀ z) +
              (36 / ((π : ℂ) * (π : ℂ)) * φ₄' z + -((t : ℂ) * ((12 : ℂ) / (π : ℂ) * φ₂' z))) := by
        simpa [hcoeffTerm] using hneg'
      -- Convert back to the target form.
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm, pow_two] using hneg''
    -- Replace `φ₀(S•z)` by `φ₀''(I/t)` and expand the principal parts.
    have hST'' :
        (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ))) =
          ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z -
            ((12 / π : ℝ) : ℂ) * t * φ₂' z +
            ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * φ₄' z := by
      simpa [hφ₀S] using hST'
    -- Algebraic cleanup: insert/remove the principal parts `720` and `504`.
    have h720 : (12 / (π : ℂ)) * (t : ℂ) * (720 : ℂ) = (8640 / (π : ℂ)) * (t : ℂ) := by
      have hpi : (π : ℂ) ≠ 0 := by
        exact_mod_cast Real.pi_ne_zero
      field_simp [hpi]
      ring
    have h504 : (36 / (π : ℂ) ^ (2 : ℕ)) * (504 : ℂ) = (18144 / (π : ℂ) ^ (2 : ℕ)) := by
      have hpi : (π : ℂ) ≠ 0 := by
        exact_mod_cast Real.pi_ne_zero
      field_simp [hpi]
      norm_num
    have hSTpow :
        (↑t ^ (2 : ℕ)) * φ₀'' (Complex.I / ↑t) =
          (↑t ^ (2 : ℕ)) * φ₀ z - (12 / (π : ℂ)) * (t : ℂ) * φ₂' z +
            (36 / (π : ℂ) ^ (2 : ℕ)) * φ₄' z := by
      simpa using hST''
    -- Expand the difference form.
    calc
      (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
            ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
            ((8640 / π : ℝ) : ℂ) * t -
            ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))
          =
            (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z -
                ((12 / π : ℝ) : ℂ) * t * φ₂' z +
                ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * φ₄' z) -
                ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                  ((12 / π : ℝ) : ℂ) * t * (720 : ℂ) -
                    ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (504 : ℂ) := by
                  -- Replace the explicit constants by the `720` and `504` factorizations.
                  simp [hSTpow, h720, h504, sub_eq_add_neg, add_left_comm, add_comm]
      _ =
            (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z -
                ((12 / π : ℝ) : ℂ) * t * (φ₂' z - (720 : ℂ)) +
                ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
                  (φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))) := by
              ring_nf
      _ = _ := by rfl
  -- Large-`t` bound from the previously established asymptotics.
  let Clarge : ℝ := C₀ + (12 / π) * C₂ + (36 / (π ^ (2 : ℕ))) * C₄
  have hClarge_pos : 0 < Clarge := by
    dsimp [Clarge]
    have h12pi : 0 < (12 / π : ℝ) :=
      div_pos (by norm_num) Real.pi_pos
    have h36pi2 : 0 < (36 / (π ^ (2 : ℕ)) : ℝ) :=
      div_pos (by norm_num) (pow_pos Real.pi_pos _)
    have hterm2 : 0 < (12 / π : ℝ) * C₂ := mul_pos h12pi hC₂pos
    have hterm4 : 0 < (36 / (π ^ (2 : ℕ)) : ℝ) * C₄ := mul_pos h36pi2 hC₄pos
    exact add_pos (add_pos hC₀pos hterm2) hterm4
  -- Bound on the compact interval `t ∈ [1,A]`.
  have hcompact :
      ∃ M : ℝ, ∀ t : ℝ, 1 ≤ t → t ≤ A →
        ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
              ((8640 / π : ℝ) : ℂ) * t -
              ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖ ≤ M := by
    -- Use the extreme value theorem on the compact interval `t ∈ [1,A]`.
    let g : ℝ → ℝ := fun t =>
      ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
            ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
            ((8640 / π : ℝ) : ℂ) * t -
            ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖
    have hg_cont : ContinuousOn g (Set.Icc (1 : ℝ) A) := by
      -- Continuity of `t ↦ φ₀''(I/t)` on `t ∈ [1,A]` via the upper half-plane.
      have hcontφ : ContinuousOn (fun z : ℂ => φ₀'' z) {z : ℂ | 0 < z.im} := by
        simpa [upperHalfPlaneSet] using MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn
      have hcontDen : ContinuousOn (fun t : ℝ => (t : ℂ)) (Set.Icc (1 : ℝ) A) :=
        (continuous_ofReal : Continuous fun t : ℝ => (t : ℂ)).continuousOn
      have hden0 : ∀ t ∈ Set.Icc (1 : ℝ) A, (t : ℂ) ≠ 0 := by
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
        exact_mod_cast (ne_of_gt ht0)
      have hcontIdiv :
          ContinuousOn (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Icc (1 : ℝ) A) :=
        (continuous_const.continuousOn.div hcontDen hden0)
      have hmaps :
          Set.MapsTo (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Icc (1 : ℝ) A)
            {z : ℂ | 0 < z.im} := by
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
        have : 0 < (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im := by
          simpa [imag_I_div t] using (inv_pos.2 ht0)
        exact this
      have hcontPhiDiv :
          ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) (Set.Icc (1 : ℝ) A) :=
        hcontφ.comp hcontIdiv hmaps
      have hcontExpr :
          ContinuousOn
              (fun t : ℝ =>
                (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                      ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                      ((8640 / π : ℝ) : ℂ) * t -
                      ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))) (Set.Icc (1 : ℝ) A) := by
        have hcontT2 :
            ContinuousOn (fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ)) (Set.Icc (1 : ℝ) A) := by
          fun_prop
        have hcontExp :
            ContinuousOn (fun t : ℝ => (Real.exp (2 * π * t) : ℂ)) (Set.Icc (1 : ℝ) A) := by
          fun_prop
        have hterm1 := hcontT2.mul hcontPhiDiv
        have hterm2 :
            ContinuousOn
              (fun t : ℝ => ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (Real.exp (2 * π * t) : ℂ))
              (Set.Icc (1 : ℝ) A) := by
          fun_prop
        have hterm3 :
            ContinuousOn (fun t : ℝ => (((8640 / π : ℝ) : ℂ) * t)) (Set.Icc (1 : ℝ) A) := by
          fun_prop
        have hterm4 :
            ContinuousOn (fun _t : ℝ => (((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))) (Set.Icc (1 : ℝ) A) :=
          continuous_const.continuousOn
        -- Assemble.
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using
          ((hterm1.sub hterm2).add hterm3).sub hterm4
      simpa [g] using hcontExpr.norm
    have hcomp : IsCompact (Set.Icc (1 : ℝ) A) := isCompact_Icc
    have hne : (Set.Icc (1 : ℝ) A).Nonempty := by
      refine ⟨1, le_rfl, hA1⟩
    rcases hcomp.exists_isMaxOn hne hg_cont with ⟨t₀, ht₀mem, ht₀max⟩
    refine ⟨g t₀, ?_⟩
    intro t ht1 htA
    have htmem : t ∈ Set.Icc (1 : ℝ) A := ⟨ht1, htA⟩
    have ht₀max' : ∀ t ∈ Set.Icc (1 : ℝ) A, g t ≤ g t₀ := by
      simpa [isMaxOn_iff] using ht₀max
    have hle : g t ≤ g t₀ := ht₀max' t htmem
    simpa [g] using hle
  -- Final constant.
  rcases hcompact with ⟨M, hM⟩
  let C : ℝ := max Clarge (M / Real.exp (-2 * π * A))
  refine ⟨C, ?_, ?_⟩
  · have : 0 < Clarge := hClarge_pos
    exact lt_of_lt_of_le this (le_max_left _ _)
  · intro t ht1
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
    by_cases htA : A ≤ t
    · -- `t ≥ A`: use the asymptotic bounds for `φ₂'` and `φ₄'`.
      have hA₂t : A₂ ≤ t := le_trans hA₂' htA
      have hA₄t : A₄ ≤ t := le_trans hA₄' htA
      let z : ℍ := zI t ht0
      have hφ₀z : ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * t) := by
        have hz : φ₀'' ((Complex.I : ℂ) * (t : ℂ)) = φ₀ z := by
          simpa [z, zI] using (φ₀''_coe_upperHalfPlane z)
        simpa [hz] using hφ₀ t ht1
      have hφ₂z : ‖φ₂' z - (720 : ℂ)‖ ≤ C₂ * Real.exp (-2 * π * t) := by
        simpa [z] using hφ₂ t ht0 hA₂t
      have hφ₄z :
          ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖ ≤ C₄ * Real.exp (-2 * π * t) := by
        simpa [z] using hφ₄ t ht0 hA₄t
      have ht2 : (1 : ℝ) ≤ t ^ (2 : ℕ) := by nlinarith [ht1]
      have hle_t : t ≤ t ^ (2 : ℕ) := by nlinarith [ht1]
      have hrew := hrewrite ht0
      -- Apply the triangle inequality to the rewritten form.
      have hnorm1 :
          ‖((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z‖ ≤ C₀ * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
        have ht2nn : 0 ≤ (t ^ (2 : ℕ) : ℝ) := by positivity
        calc
          ‖((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z‖
              = (t ^ (2 : ℕ) : ℝ) * ‖φ₀ z‖ := by
                  simp [Complex.norm_real]
          _ ≤ (t ^ (2 : ℕ) : ℝ) * (C₀ * Real.exp (-2 * π * t)) := by
                  gcongr
          _ = C₀ * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by ring
      have hnorm2 :
          ‖((12 / π : ℝ) : ℂ) * t * (φ₂' z - (720 : ℂ))‖ ≤
            ((12 / π) * C₂) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
        have ht0le : 0 ≤ t := (le_trans (by norm_num) ht1)
        have htnn : 0 ≤ (t ^ (2 : ℕ) : ℝ) := by positivity
        calc
          ‖((12 / π : ℝ) : ℂ) * t * (φ₂' z - (720 : ℂ))‖
              = ‖((12 / π : ℝ) : ℂ)‖ * ‖(t : ℂ)‖ * ‖φ₂' z - (720 : ℂ)‖ := by
                  simp [mul_assoc]
          _ ≤ (12 / π) * t * (C₂ * Real.exp (-2 * π * t)) := by
                  have htcoeff : 0 ≤ ‖((12 / π : ℝ) : ℂ)‖ * ‖(t : ℂ)‖ :=
                    mul_nonneg (norm_nonneg _) (norm_nonneg _)
                  have hmul := mul_le_mul_of_nonneg_left hφ₂z htcoeff
                  -- Simplify the scalar norms using `t ≥ 0` and `π > 0`.
                  simpa [mul_assoc, mul_left_comm, mul_comm, Complex.norm_real, Real.norm_eq_abs,
                    abs_div, abs_of_nonneg ht0le, abs_of_pos Real.pi_pos] using hmul
          _ ≤ (12 / π) * (t ^ (2 : ℕ)) * (C₂ * Real.exp (-2 * π * t)) := by
                  have h12pi0 : 0 ≤ (12 / π : ℝ) :=
                    le_of_lt (div_pos (by norm_num) Real.pi_pos)
                  have hX0 : 0 ≤ C₂ * Real.exp (-2 * π * t) := by
                    have : 0 ≤ C₂ := le_of_lt hC₂pos
                    exact mul_nonneg this (le_of_lt (Real.exp_pos _))
                  -- Use `t ≤ t^2` on `[1,∞)`.
                  have hmul : t * (C₂ * Real.exp (-2 * π * t)) ≤
                      (t ^ (2 : ℕ)) * (C₂ * Real.exp (-2 * π * t)) := by
                    exact mul_le_mul_of_nonneg_right hle_t hX0
                  -- Multiply by `12/π ≥ 0`.
                  simpa [mul_assoc, mul_left_comm, mul_comm] using
                    mul_le_mul_of_nonneg_left hmul h12pi0
          _ = ((12 / π) * C₂) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by ring
      have hnorm3 :
          ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
              (φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))‖ ≤
            ((36 / (π ^ (2 : ℕ))) * C₄) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
        have ht2nn : 0 ≤ (t ^ (2 : ℕ) : ℝ) := by positivity
        calc
          ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
              (φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))‖
              = ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ *
                  ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖ := by
                    simp
          _ ≤ (36 / (π ^ (2 : ℕ))) * (C₄ * Real.exp (-2 * π * t)) := by
            have hcoeff : 0 ≤ ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ := norm_nonneg _
            have hmul := mul_le_mul_of_nonneg_left hφ₄z hcoeff
            have h1 : ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ = (36 / (π ^ (2 : ℕ)) : ℝ) := by
              have h36pi2_0 : 0 ≤ (36 / (π ^ (2 : ℕ)) : ℝ) :=
                le_of_lt (div_pos (by norm_num) (pow_pos Real.pi_pos _))
              simp [Complex.norm_real, Real.norm_eq_abs]
            simpa [h1, mul_assoc] using hmul
          _ ≤ (36 / (π ^ (2 : ℕ))) * (t ^ (2 : ℕ)) * (C₄ * Real.exp (-2 * π * t)) := by
                  have h36pi2_0 : 0 ≤ (36 / (π ^ (2 : ℕ)) : ℝ) :=
                    le_of_lt (div_pos (by norm_num) (pow_pos Real.pi_pos _))
                  have hX0 : 0 ≤ C₄ * Real.exp (-2 * π * t) := by
                    have : 0 ≤ C₄ := le_of_lt hC₄pos
                    exact mul_nonneg this (le_of_lt (Real.exp_pos _))
                  have hmul :
                      C₄ * Real.exp (-2 * π * t) ≤
                        (t ^ (2 : ℕ)) * (C₄ * Real.exp (-2 * π * t)) := by
                    simpa [one_mul] using (mul_le_mul_of_nonneg_right ht2 hX0)
                  -- Multiply by `36/π^2 ≥ 0`.
                  simpa [mul_assoc, mul_left_comm, mul_comm] using
                    mul_le_mul_of_nonneg_left hmul h36pi2_0
          _ = ((36 / (π ^ (2 : ℕ))) * C₄) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by ring
      have htri :
          ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
              ((8640 / π : ℝ) : ℂ) * t -
              ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖ ≤
            Clarge * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
        -- Rewrite and apply the triangle inequality.
        -- Use `‖x - y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖`.
        have hE :
            (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                ((8640 / π : ℝ) : ℂ) * t -
                ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) =
              (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z -
                  ((12 / π : ℝ) : ℂ) * t * (φ₂' z - (720 : ℂ)) +
                  ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
                    (φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))) := by
          simpa [z] using hrew
        -- Combine the three bounds.
        have hsum :
              ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z -
                  ((12 / π : ℝ) : ℂ) * t * (φ₂' z - (720 : ℂ)) +
                  ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
                    (φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)))‖ ≤
                (C₀ * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) +
                  ((12 / π) * C₂) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) +
                  ((36 / (π ^ (2 : ℕ))) * C₄) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) := by
            -- `‖x - y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖`, then apply the three bounds.
            set x : ℂ := ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z
            set y : ℂ := ((12 / π : ℝ) : ℂ) * t * (φ₂' z - (720 : ℂ))
            set z' : ℂ :=
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))
            have hxy : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := by
              simpa [sub_eq_add_neg, norm_neg] using (norm_add_le x (-y))
            have hxyz : ‖x - y + z'‖ ≤ (‖x‖ + ‖y‖) + ‖z'‖ := by
              have h1 : ‖x - y + z'‖ ≤ ‖x - y‖ + ‖z'‖ := by
                simpa [sub_eq_add_neg, add_assoc] using (norm_add_le (x - y) z')
              have h2 : ‖x - y‖ + ‖z'‖ ≤ (‖x‖ + ‖y‖) + ‖z'‖ := by
                have h2' : ‖z'‖ + ‖x - y‖ ≤ ‖z'‖ + (‖x‖ + ‖y‖) := add_le_add_right hxy ‖z'‖
                have hx : ‖x - y‖ + ‖z'‖ = ‖z'‖ + ‖x - y‖ :=
                  add_comm ‖x - y‖ ‖z'‖
                have hz : ‖z'‖ + (‖x‖ + ‖y‖) = (‖x‖ + ‖y‖) + ‖z'‖ :=
                  add_comm ‖z'‖ (‖x‖ + ‖y‖)
                calc
                  ‖x - y‖ + ‖z'‖ = ‖z'‖ + ‖x - y‖ := hx
                  _ ≤ ‖z'‖ + (‖x‖ + ‖y‖) := h2'
                  _ = (‖x‖ + ‖y‖) + ‖z'‖ := hz
              exact h1.trans h2
            have hsum' :
                (‖x‖ + ‖y‖) + ‖z'‖ ≤
                  (C₀ * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) +
                    ((12 / π) * C₂) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) +
                    ((36 / (π ^ (2 : ℕ))) * C₄) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) := by
              have hxy' :
                  ‖x‖ + ‖y‖ ≤
                    C₀ * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) +
                      ((12 / π) * C₂) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
                exact add_le_add hnorm1 hnorm2
              have hxyz' :
                  (‖x‖ + ‖y‖) + ‖z'‖ ≤
                    (C₀ * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) +
                      ((12 / π) * C₂) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) +
                        ((36 / (π ^ (2 : ℕ))) * C₄) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
                exact add_le_add hxy' hnorm3
              simpa [add_assoc] using hxyz'
            exact hxyz.trans hsum'
        -- Factor the common term.
        have hsum' :
            (C₀ * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) +
              ((12 / π) * C₂) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) +
              ((36 / (π ^ (2 : ℕ))) * C₄) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t))
              = Clarge * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
          dsimp [Clarge, Clarge]
          ring
        -- Rewrite using `hE` and apply the triangle-inequality bound `hsum`.
        rw [hE]
        exact hsum.trans (le_of_eq hsum')
      have hCle : Clarge ≤ C := le_max_left _ _
      have hCmul :
          Clarge * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) ≤
            C * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
        have ht2nn : 0 ≤ t ^ (2 : ℕ) := by positivity
        have hexpnn : 0 ≤ Real.exp (-2 * π * t) := le_of_lt (Real.exp_pos _)
        have hmul_t2 : Clarge * (t ^ (2 : ℕ)) ≤ C * (t ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right hCle ht2nn
        exact mul_le_mul_of_nonneg_right hmul_t2 hexpnn
      exact le_trans htri hCmul
    · -- `t ≤ A`: use the compact bound.
      have htA' : t ≤ A := le_of_not_ge htA
      have hCle : M / Real.exp (-2 * π * A) ≤ C := le_max_right _ _
      exact
        phi0Cancellation_compact_case (M := M) (A := A) (C := C) (t := t) ht1 htA'
          (hM t ht1 htA') hCle

/-! ## Integrability of the "another integrand" for `0 < u`. -/

lemma aAnotherIntegrand_integrableOn_Ioc {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => aAnotherIntegrand u t) (Set.Ioc (0 : ℝ) 1) := by
  -- Finite measure; show essential boundedness.
  have hμ : (volume : Measure ℝ) (Set.Ioc (0 : ℝ) 1) < ⊤ := by simp
  have hmeas : MeasurableSet (Set.Ioc (0 : ℝ) 1) := measurableSet_Ioc
  rcases MagicFunction.PolyFourierCoeffBound.norm_φ₀_le with ⟨Cφ₀, hCφ₀_pos, hCφ₀⟩
  let M : ℝ :=
    Cφ₀ +
      ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) +
      ‖((8640 / π : ℝ) : ℂ)‖ + ‖((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖
  have hmeas_f :
      AEStronglyMeasurable (fun t : ℝ => aAnotherIntegrand u t)
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine (ContinuousOn.aestronglyMeasurable ?_ hmeas)
    have hcontφ : ContinuousOn (fun z : ℂ => φ₀'' z) {z : ℂ | 0 < z.im} := by
      simpa [upperHalfPlaneSet] using MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn
    have hcontIdiv : ContinuousOn (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Ioc (0 : ℝ) 1) := by
      have hcont : ContinuousOn (fun t : ℝ => (t : ℂ)) (Set.Ioc (0 : ℝ) 1) :=
        (continuous_ofReal : Continuous fun t : ℝ => (t : ℂ)).continuousOn
      have hne : ∀ t ∈ Set.Ioc (0 : ℝ) 1, (t : ℂ) ≠ 0 := by
        intro t ht; exact_mod_cast (ne_of_gt ht.1)
      simpa [div_eq_mul_inv] using (continuous_const.continuousOn.mul (hcont.inv₀ hne))
    have hmaps :
        Set.MapsTo (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Ioc (0 : ℝ) 1)
          {z : ℂ | 0 < z.im} := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have : (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im = t⁻¹ := imag_I_div t
      simpa [this] using (inv_pos.2 ht0)
    have hφcont :
        ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) (Set.Ioc (0 : ℝ) 1) :=
      hcontφ.comp hcontIdiv hmaps
    have hpowC : Continuous fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ) := by fun_prop
    have hexpC : Continuous fun t : ℝ => ((Real.exp (-π * u * t)) : ℂ) := by fun_prop
    refine
      ((hpowC.continuousOn.mul hφcont).sub ?_ |>.add ?_ |>.sub ?_).mul
        hexpC.continuousOn
    · fun_prop
    · fun_prop
    · fun_prop
  refine (MeasureTheory.IntegrableOn.of_bound hμ hmeas_f M ?_)
  -- pointwise bound on the restricted measure
  refine (ae_restrict_iff' hmeas).2 ?_
  refine Filter.Eventually.of_forall (fun t ht => ?_)
  have ht0 : 0 < t := ht.1
  have him_div : (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im = t⁻¹ := imag_I_div t
  have him_pos : 0 < (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im := by
    simpa [him_div] using inv_pos.2 ht0
  let z : ℍ := ⟨(Complex.I : ℂ) / (t : ℂ), him_pos⟩
  have hzHalf : (1 / 2 : ℝ) < z.im := by
    have : (1 : ℝ) ≤ z.im := by
      -- `1 ≤ 1/t` for `t ≤ 1`.
      have ht1 : t ≤ 1 := ht.2
      have : (1 : ℝ) ≤ t⁻¹ := by
        exact (one_le_inv₀ ht0).2 ht1
      simpa [z, UpperHalfPlane.im, him_div] using this
    exact lt_of_lt_of_le (by norm_num) this
  have hφ0z : ‖φ₀ z‖ ≤ Cφ₀ * Real.exp (-2 * π * z.im) := hCφ₀ z hzHalf
  have hφ0'' :
      ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ Cφ₀ := by
    have hexp_le_one : Real.exp (-2 * π * z.im) ≤ 1 := by
      have : (-2 * π * z.im) ≤ 0 := by nlinarith [Real.pi_pos, (z.2).le]
      exact Real.exp_le_one_iff.2 this
    have hdef : φ₀ z = φ₀'' ((Complex.I : ℂ) / (t : ℂ)) := by
      simpa [z] using (φ₀''_def (z := (Complex.I : ℂ) / (t : ℂ)) him_pos).symm
    have hmul : Cφ₀ * Real.exp (-2 * π * z.im) ≤ Cφ₀ * 1 := by
      have := mul_le_mul_of_nonneg_left hexp_le_one hCφ₀_pos.le
      simpa using this
    have : ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ Cφ₀ := by
      have := le_trans hφ0z hmul
      -- Rewrite `φ₀ z` to `φ₀''`.
      simpa [hdef] using this
    simpa using this
  have ht2_le : (t ^ (2 : ℕ) : ℝ) ≤ 1 := by
    have : 0 ≤ t := ht0.le
    nlinarith [ht.2]
  have hexp_le_one : Real.exp (-π * u * t) ≤ 1 := by
    have hnonneg : 0 ≤ π * u * t := by positivity
    have hneg : -(π * u * t) ≤ 0 := neg_nonpos.mpr hnonneg
    have hEq : (-π * u * t) = -(π * u * t) := by ring
    have : (-π * u * t) ≤ 0 := by simpa [hEq] using hneg
    exact Real.exp_le_one_iff.2 this
  -- Now bound `‖aAnotherIntegrand u t‖` by `M`.
  have hnorm :
      ‖aAnotherIntegrand u t‖ ≤ M := by
    -- Triangle inequality on the bracket and `exp(-π u t) ≤ 1`.
    have hbr :
        ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
              ((8640 / π : ℝ) : ℂ) * t -
              ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖ ≤
          (t ^ (2 : ℕ) : ℝ) * Cφ₀ +
            ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) +
            ‖((8640 / π : ℝ) : ℂ)‖ + ‖((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ := by
      -- Rewrite as `A - B + C - D`, then use the triangle inequality.
      let A : ℂ :=
        ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ))
      let B : ℂ :=
        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t)
      let Cc : ℂ := ((8640 / π : ℝ) : ℂ) * t
      let D : ℂ := ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)
      have hsum : ‖A - B + Cc - D‖ ≤ ‖A‖ + ‖B‖ + ‖Cc‖ + ‖D‖ := by
        calc
          ‖A - B + Cc - D‖ = ‖(A - B) + (Cc - D)‖ := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ ≤ ‖A - B‖ + ‖Cc - D‖ := norm_add_le _ _
          _ ≤ (‖A‖ + ‖B‖) + (‖Cc‖ + ‖D‖) := by
            exact add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
          _ = ‖A‖ + ‖B‖ + ‖Cc‖ + ‖D‖ := by ring
      have hA : ‖A‖ ≤ (t ^ (2 : ℕ) : ℝ) * Cφ₀ := by
        have : ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ Cφ₀ := hφ0''
        have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ (t ^ (2 : ℕ) : ℝ))
        have ht2nonneg : 0 ≤ (t ^ (2 : ℕ) : ℝ) := by positivity
        simpa [A, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht2nonneg] using this
      have hExp2 : Real.exp (2 * π * t) ≤ Real.exp (2 * π) := by
        have : (2 * π * t) ≤ (2 * π * (1 : ℝ)) := by nlinarith [Real.pi_pos, ht.2]
        simpa using (Real.exp_le_exp.2 this)
      have hB : ‖B‖ ≤ ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) := by
        have hExpNorm :
            ‖(Real.exp (2 * π * t) : ℂ)‖ = Real.exp (2 * π * t) := by
          have hpos : 0 < Real.exp (2 * π * t) := Real.exp_pos _
          calc
            ‖(Real.exp (2 * π * t) : ℂ)‖ = |Real.exp (2 * π * t)| := by
              simpa using (RCLike.norm_ofReal (K := ℂ) (Real.exp (2 * π * t)))
            _ = Real.exp (2 * π * t) := by simp [abs_of_pos hpos]
        have hB' :
            ‖B‖ = ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π * t) := by
          -- Avoid rewriting `Real.exp` into `Complex.exp`.
          calc
            ‖B‖ = ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * ‖(Real.exp (2 * π * t) : ℂ)‖ := by
              simp [-Complex.ofReal_exp, B]
            _ = ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π * t) := by
              rw [hExpNorm]
        rw [hB']
        exact mul_le_mul_of_nonneg_left hExp2 (norm_nonneg _)
      have ht_le1 : t ≤ 1 := ht.2
      have hC : ‖Cc‖ ≤ ‖((8640 / π : ℝ) : ℂ)‖ := by
        have hCc' : ‖Cc‖ = ‖((8640 / π : ℝ) : ℂ)‖ * t := by
          simp [Cc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le]
        rw [hCc']
        -- `0 ≤ ‖((8640 / π : ℝ) : ℂ)‖`.
        have := mul_le_mul_of_nonneg_left ht_le1 (norm_nonneg ((8640 / π : ℝ) : ℂ))
        simpa using this
      have hD : ‖D‖ = ‖((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ := by simp [D]
      -- Combine.
      have hcomb :
          ‖A‖ + ‖B‖ + ‖Cc‖ + ‖D‖ ≤
            (t ^ (2 : ℕ) : ℝ) * Cφ₀ +
              ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) +
              ‖((8640 / π : ℝ) : ℂ)‖ + ‖((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ := by
        -- Assemble from `hA`, `hB`, `hC`, and `hD`.
        have hAB :
            ‖A‖ + ‖B‖ ≤
              (t ^ (2 : ℕ) : ℝ) * Cφ₀ +
                ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) :=
          add_le_add hA hB
        have hABC : ‖A‖ + ‖B‖ + ‖Cc‖ ≤
            (t ^ (2 : ℕ) : ℝ) * Cφ₀ +
              ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) +
              ‖((8640 / π : ℝ) : ℂ)‖ := by
          simpa [add_assoc] using add_le_add hAB hC
        have hABCD : ‖A‖ + ‖B‖ + ‖Cc‖ + ‖D‖ ≤
            (t ^ (2 : ℕ) : ℝ) * Cφ₀ +
              ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) +
              ‖((8640 / π : ℝ) : ℂ)‖ + ‖((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ := by
          have := add_le_add hABC (le_of_eq hD)
          simpa [add_assoc] using this
        exact hABCD
      -- Finish by rewriting `A,B,Cc,D` back to the original expression.
      have hmain :
          ‖A - B + Cc - D‖ ≤
            (t ^ (2 : ℕ) : ℝ) * Cφ₀ +
              ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) +
              ‖((8640 / π : ℝ) : ℂ)‖ + ‖((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ :=
        (hsum.trans hcomb)
      simpa [A, B, Cc, D] using hmain
    have hmul :
        ‖aAnotherIntegrand u t‖ ≤
          ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                ((8640 / π : ℝ) : ℂ) * t -
                ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖ := by
      -- Multiply by `exp(-π u t) ≤ 1`.
      have hExpNorm : ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) := by
        simpa using (norm_ofReal_exp (-π * u * t))
      have : ‖(Real.exp (-π * u * t) : ℂ)‖ ≤ 1 := by
        rw [hExpNorm]
        exact hexp_le_one
      simpa [aAnotherIntegrand, norm_mul, mul_assoc] using
        (mul_le_mul_of_nonneg_left this (norm_nonneg _))
    have : ‖aAnotherIntegrand u t‖ ≤ (t ^ (2 : ℕ) : ℝ) * Cφ₀ +
            ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) +
            ‖((8640 / π : ℝ) : ℂ)‖ + ‖((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ :=
      le_trans hmul hbr
    -- Use `t^2 ≤ 1` to replace `(t^2)*Cφ₀` by `Cφ₀`.
    have : (t ^ (2 : ℕ) : ℝ) * Cφ₀ ≤ Cφ₀ := by
      have := mul_le_mul_of_nonneg_right ht2_le hCφ₀_pos.le
      simpa [one_mul] using this
    nlinarith [this]
  exact hnorm

lemma aAnotherIntegrand_integrableOn_Ici {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => aAnotherIntegrand u t) (Set.Ici (1 : ℝ)) := by
  rcases exists_phi0_cancellation_bound with ⟨C, hCpos, hC⟩
  have hbound :
      ∀ t : ℝ, t ∈ Set.Ici (1 : ℝ) →
        ‖aAnotherIntegrand u t‖ ≤ C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t) := by
    intro t ht
    have ht1 : 1 ≤ t := ht
    have hmain := hC t ht1
    have hexp :
        Real.exp (-2 * π * t) * Real.exp (-π * u * t) = Real.exp (-(2 * π + π * u) * t) := by
      calc
        Real.exp (-2 * π * t) * Real.exp (-π * u * t) =
            Real.exp ((-2 * π * t) + (-π * u * t)) := by
              simpa using (Real.exp_add (-2 * π * t) (-π * u * t)).symm
        _ = Real.exp (-(2 * π + π * u) * t) := by
              have : (-2 * π * t) + (-π * u * t) = (-(2 * π + π * u) * t) := by ring
              simpa [this]
    have hmul :=
      (mul_le_mul_of_nonneg_right hmain (Real.exp_pos (-π * u * t)).le)
    -- Convert the bound on the bracket to a bound on the full integrand.
    have hnorm :
        ‖aAnotherIntegrand u t‖ =
          ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                ((8640 / π : ℝ) : ℂ) * t -
                ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖ * Real.exp (-π * u * t) := by
      -- `Real.exp` is positive, so `‖(Real.exp x : ℂ)‖ = Real.exp x`.
      let A : ℂ :=
        (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
              ((8640 / π : ℝ) : ℂ) * t -
              ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))
      have hA : aAnotherIntegrand u t = A * (Real.exp (-π * u * t) : ℂ) := by
        -- Avoid rewriting `Real.exp` into `Complex.exp`.
        simp [-Complex.ofReal_exp, aAnotherIntegrand, A, mul_left_comm, mul_comm]
      have hExp :
          ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) := by
        simpa using (norm_ofReal_exp (-π * u * t))
      calc
        ‖aAnotherIntegrand u t‖ = ‖A * (Real.exp (-π * u * t) : ℂ)‖ := by simp [hA]
        _ = ‖A‖ * ‖(Real.exp (-π * u * t) : ℂ)‖ := by
              simp
        _ = ‖A‖ * Real.exp (-π * u * t) := by rw [hExp]
    -- Finish by rewriting the exponential product.
    have : ‖aAnotherIntegrand u t‖ ≤
        (C * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) * Real.exp (-π * u * t) := by
      simpa [hnorm, mul_assoc, mul_left_comm, mul_comm] using hmul
    -- Rewrite the RHS using `exp(-2πt) * exp(-πut) = exp(-(2π+πu)t)`.
    calc
      ‖aAnotherIntegrand u t‖ ≤
          (C * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) * Real.exp (-π * u * t) := this
      _ = C * (t ^ (2 : ℕ)) * (Real.exp (-2 * π * t) * Real.exp (-π * u * t)) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
      _ = C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t) := by
          -- Rewrite the inner product using `hexp` without canceling `C * t^2`.
          simpa [mul_assoc] using congrArg (fun s : ℝ => C * (t ^ (2 : ℕ)) * s) hexp
  -- Dominate by an integrable real function on `(1,∞)`.
  have hdom :
      IntegrableOn (fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t))
        (Set.Ici (1 : ℝ)) := by
    have ha : 0 < (2 * π + π * u) / 2 := by positivity
    have hcont :
        ContinuousOn (fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t))
          (Set.Ici (1 : ℝ)) := by
      fun_prop
    -- Use `integrable_of_isBigO_exp_neg`.
    have hO :
        (fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t)) =O[atTop]
          fun t : ℝ => Real.exp (-((2 * π + π * u) / 2) * t) := by
      -- Let `b = (2π + πu) / 2 > 0`.
      set b : ℝ := (2 * π + π * u) / 2
      have hb : 0 < b := ha
      have hlittle :
          (fun t : ℝ => (t ^ (2 : ℕ) : ℝ)) =o[atTop] fun t : ℝ => Real.exp (b * t) :=
        isLittleO_pow_exp_pos_mul_atTop 2 hb
      have hlittleC :
          (fun t : ℝ => C * (t ^ (2 : ℕ) : ℝ)) =o[atTop] fun t : ℝ => Real.exp (b * t) :=
        hlittle.const_mul_left C
      have hExp : (fun t : ℝ => Real.exp (-b * t)) =O[atTop] fun t : ℝ => Real.exp (-b * t) := by
        simpa using (Asymptotics.isBigO_refl (fun t : ℝ => Real.exp (-b * t)) atTop)
      -- First show `C*t^2*exp(-b*t) = O(1)` using `t^2 = o(exp(b*t))`.
      have hfac :
          (fun t : ℝ => (C * (t ^ (2 : ℕ) : ℝ)) * Real.exp (-b * t)) =o[atTop]
            fun t : ℝ => (Real.exp (b * t)) * Real.exp (-b * t) :=
        hlittleC.mul_isBigO hExp
      have hfac' :
          (fun t : ℝ => (C * (t ^ (2 : ℕ) : ℝ)) * Real.exp (-b * t)) =o[atTop]
            fun _t : ℝ => (1 : ℝ) :=
        hfac.congr_right (fun t => by
          calc
            Real.exp (b * t) * Real.exp (-b * t) = Real.exp (b * t + (-b * t)) := by
              simpa [Real.exp_add] using (Real.exp_add (b * t) (-b * t)).symm
            _ = 1 := by simp)
      have hfacBig :
          (fun t : ℝ => (C * (t ^ (2 : ℕ) : ℝ)) * Real.exp (-b * t)) =O[atTop]
            fun _t : ℝ => (1 : ℝ) :=
        hfac'.isBigO
      -- Multiply by `exp(-b*t)` one more time to get `C*t^2*exp(-(2b)*t) = O(exp(-b*t))`.
      have hO' :
          (fun t : ℝ => ((C * (t ^ (2 : ℕ) : ℝ)) * Real.exp (-b * t)) * Real.exp (-b * t)) =O[atTop]
            fun t : ℝ => (1 : ℝ) * Real.exp (-b * t) :=
        hfacBig.mul (Asymptotics.isBigO_refl (fun t : ℝ => Real.exp (-b * t)) atTop)
      have hO'' :
          (fun t : ℝ => C * (t ^ (2 : ℕ) : ℝ) * Real.exp (-(2 * π + π * u) * t)) =O[atTop]
            fun t : ℝ => Real.exp (-b * t) := by
        -- Simplify the right side of `hO'`.
        have hO1 :
            (fun t : ℝ =>
                ((C * (t ^ (2 : ℕ) : ℝ)) * Real.exp (-b * t)) * Real.exp (-b * t)) =O[atTop]
              fun t : ℝ => Real.exp (-b * t) := by
          simpa [one_mul] using hO'
        -- Rewrite the left side using `exp_add` and `b = (2π+πu)/2`.
        refine hO1.congr_left (fun t => ?_)
        have hmul :
            Real.exp (-b * t) * Real.exp (-b * t) = Real.exp (-(2 * b * t)) := by
          have h := (Real.exp_add (-(b * t)) (-(b * t))).symm
          have : (-(b * t)) + (-(b * t)) = -(2 * b * t) := by ring
          -- Rewrite `-b*t` as `-(b*t)` using `neg_mul`.
          simpa [neg_mul, this] using h
        -- Now unfold `b` in the exponent.
        have hb2 : (2 * b) = (2 * π + π * u) := by
          dsimp [b]
          ring_nf
        -- Put everything together.
        calc
          ((C * (t ^ (2 : ℕ) : ℝ)) * Real.exp (-b * t)) * Real.exp (-b * t)
              = (C * (t ^ (2 : ℕ) : ℝ)) * (Real.exp (-b * t) * Real.exp (-b * t)) := by
                  simp [mul_assoc]
          _ = (C * (t ^ (2 : ℕ) : ℝ)) * Real.exp (-(2 * b * t)) := by
                  -- Use `hmul` without cancellation.
                  simpa [mul_assoc] using congrArg (fun s : ℝ => (C * (t ^ (2 : ℕ) : ℝ)) * s) hmul
          _ = C * (t ^ (2 : ℕ) : ℝ) * Real.exp (-(2 * π + π * u) * t) := by
                  -- Rewrite `2*b*t` using `hb2`, inside the exponential.
                  have harg : (2 * b * t) = (2 * π + π * u) * t := by
                    calc
                      2 * b * t = (2 * b) * t := by ring
                      _ = (2 * π + π * u) * t := by simp [hb2]
                  have harg' : -(2 * b * t) = -(2 * π + π * u) * t := by
                    -- Multiply `harg` by `-1` and rewrite `-((·) * t)` as `-(·) * t` by `ring`.
                    have hneg : -(2 * b * t) = -((2 * π + π * u) * t) :=
                      congrArg (fun x : ℝ => -x) harg
                    -- Keep `t` inside to avoid `mul_eq_mul_right_iff` cancellations.
                    simpa [mul_assoc] using (hneg.trans (by ring))
                  rw [hb2, neg_mul]
      simpa using hO''
    have hIntIoi :
        IntegrableOn (fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t))
          (Set.Ioi (1 : ℝ)) :=
      integrable_of_isBigO_exp_neg (a := (1 : ℝ)) (b := (2 * π + π * u) / 2) ha
        (by simpa [Set.Ici] using hcont) hO
    exact (integrableOn_Ici_iff_integrableOn_Ioi (μ := (volume : Measure ℝ))
        (f := fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t))
        (b := (1 : ℝ))).2 hIntIoi
  -- Apply domination under the restricted measure using `Integrable.mono'`.
  have hg :
      Integrable (fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t))
        ((volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))) :=
    hdom.integrable
  have hf :
      AEStronglyMeasurable (fun t : ℝ => aAnotherIntegrand u t)
        ((volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))) := by
    have hcont :
        ContinuousOn (fun t : ℝ => aAnotherIntegrand u t) (Set.Ici (1 : ℝ)) := by
      have hcontφ : ContinuousOn (fun z : ℂ => φ₀'' z) {z : ℂ | 0 < z.im} := by
        simpa [upperHalfPlaneSet] using MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn
      have hcontIdiv : ContinuousOn (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Ici (1 : ℝ)) := by
        have hcont : ContinuousOn (fun t : ℝ => (t : ℂ)) (Set.Ici (1 : ℝ)) :=
          (continuous_ofReal : Continuous fun t : ℝ => (t : ℂ)).continuousOn
        have hne : ∀ t ∈ Set.Ici (1 : ℝ), (t : ℂ) ≠ 0 := by
          intro t ht; exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) ht))
        simpa [div_eq_mul_inv] using (continuous_const.continuousOn.mul (hcont.inv₀ hne))
      have hmaps :
          Set.MapsTo (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Ici (1 : ℝ))
            {z : ℂ | 0 < z.im} := by
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
        have : (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im = t⁻¹ := imag_I_div t
        simpa [this] using inv_pos.2 ht0
      have hφcont :
          ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) (Set.Ici (1 : ℝ)) :=
        hcontφ.comp hcontIdiv hmaps
      have hpowC : Continuous fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ) := by fun_prop
      have hexpC : Continuous fun t : ℝ => ((Real.exp (-π * u * t)) : ℂ) := by fun_prop
      refine
        ((hpowC.continuousOn.mul hφcont).sub ?_ |>.add ?_ |>.sub ?_).mul
          hexpC.continuousOn
      · fun_prop
      · fun_prop
      · fun_prop
    exact hcont.aestronglyMeasurable measurableSet_Ici
  have hfg :
      ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))),
        ‖aAnotherIntegrand u t‖ ≤ C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t) := by
    refine (ae_restrict_iff' measurableSet_Ici).2 ?_
    exact Filter.Eventually.of_forall (fun t ht => hbound t ht)
  exact (MeasureTheory.Integrable.mono' hg hf hfg)

/-- For `u > 0`, the function `t ↦ aAnotherIntegrand u t` is integrable on `(0, ∞)`. -/
public lemma aAnotherIntegrand_integrable_of_pos {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => aAnotherIntegrand u t) (Set.Ioi (0 : ℝ)) := by
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ici (1 : ℝ) := by
    ext t
    constructor
    · intro ht
      by_cases h1 : t ≤ 1
      · exact Or.inl ⟨ht, h1⟩
      · exact Or.inr (le_of_not_ge h1)
    · rintro (ht | ht)
      · exact ht.1
      · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht
  have h1 := aAnotherIntegrand_integrableOn_Ioc (u := u) hu
  have h2 := aAnotherIntegrand_integrableOn_Ici (u := u) hu
  have hU :
      IntegrableOn (fun t : ℝ => aAnotherIntegrand u t) (Set.Ioc (0 : ℝ) 1 ∪ Set.Ici (1 : ℝ)) :=
    h1.union h2
  -- Rewrite the domain and close.
  -- Avoid `simp` recursion by rewriting the set.
  rw [hsplit]
  exact hU

end

end MagicFunction.g.CohnElkies.IntegralReps
