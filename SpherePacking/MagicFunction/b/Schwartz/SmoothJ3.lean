module
public import SpherePacking.MagicFunction.b.Basic
public import SpherePacking.MagicFunction.b.Schwartz.SmoothJ5

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import SpherePacking.ForMathlib.IteratedDeriv
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.MagicFunction.b.PsiParamRelations


/-!
# Smooth J3

This file proves smoothness and Schwartz-type decay bounds for the primed radial integral `J₃'`.
The key input is a reduction of `J₃'` to `J₅'` via modular translation identities for `ψT'` along
the parametrisations `z₃'` and `z₅'`.

## Main statements
* `ψT'_z₃'_eq_ψI'_z₅'`
* `contDiff_J₃'`
* `decay_J₃'`
-/


namespace MagicFunction.b.Schwartz.J3Smooth

noncomputable section

open scoped Interval Manifold Topology UpperHalfPlane MatrixGroups ModularForm

open Complex Real Set intervalIntegral

open MagicFunction.Parametrisations
open MagicFunction.b.RealIntegrals
open Matrix ModularGroup
open ModularForm

/-- Compatibility of the primed extensions `ψT'` and `ψI'` along the parametrisations `z₃'`/`z₅'`.

The primes refer to the extensions `ψT'`, `ψI' : ℂ → ℂ` and the parametrisations `z₃'`, `z₅'`. -/
public lemma ψT'_z₃'_eq_ψI'_z₅' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ψT' (z₃' t) = ψI' (z₅' t) := by
  simpa using MagicFunction.b.PsiParamRelations.ψT'_z₃'_eq_ψI'_z₅' (t := t) ht

lemma cexp_mul_z₃'_eq (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    cexp (π * (Complex.I : ℂ) * x * (z₃' t)) =
      cexp (π * (Complex.I : ℂ) * x * (z₅' t)) * cexp (π * (Complex.I : ℂ) * x) := by
  have hz : z₃' t = z₅' t + 1 := z₃'_eq_z₅'_add_one (t := t) ht
  simp [hz, mul_add, mul_assoc, mul_left_comm, mul_comm, Complex.exp_add]

lemma J₃'_eq (x : ℝ) :
    J₃' x = (-1 / 2 : ℂ) * cexp ((π : ℂ) * Complex.I * (x : ℂ)) * J₅' x := by
  have hJ3 :
      J₃' x =
        (∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * x * (z₅' t))) *
          cexp (π * (Complex.I : ℂ) * x) := by
    calc
      J₃' x
          = ∫ t in (0 : ℝ)..1,
              (Complex.I : ℂ) * ψT' (z₃' t) * cexp (π * (Complex.I : ℂ) * x * (z₃' t)) := by
              simp [RealIntegrals.J₃']
      _ = ∫ t in (0 : ℝ)..1,
              (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * x * (z₅' t)) *
                cexp (π * (Complex.I : ℂ) * x) := by
              refine intervalIntegral.integral_congr fun t ht => ?_
              have htIcc : t ∈ Icc (0 : ℝ) 1 := by
                simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
              have hψ := ψT'_z₃'_eq_ψI'_z₅' (t := t) htIcc
              have hcexp := cexp_mul_z₃'_eq (x := x) (t := t) htIcc
              grind only
      _ = (∫ t in (0 : ℝ)..1,
              (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * x * (z₅' t))) *
            cexp (π * (Complex.I : ℂ) * x) := integral_mul_const _ _
  have hK :
      (∫ t in (0 : ℝ)..1,
          (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * x * (z₅' t))) =
        (-1 / 2 : ℂ) * J₅' x := by
    set K : ℂ :=
      ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * x * (z₅' t))
    have hJ5 : J₅' x = (-2 : ℂ) * K := by simp [RealIntegrals.J₅', K]
    grind only
  calc
    J₃' x = ((-1 / 2 : ℂ) * J₅' x) * cexp (π * (Complex.I : ℂ) * x) := by simpa [hK] using hJ3
    _ = (-1 / 2 : ℂ) * cexp ((π : ℂ) * Complex.I * (x : ℂ)) * J₅' x := by ring_nf

/-- Smoothness of `J₃'`.

The prime in `contDiff_J₃'` refers to the function `J₃'`. -/
public theorem contDiff_J₃' : ContDiff ℝ (⊤ : ℕ∞) J₃' := by
  have hExp : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ cexp ((π : ℂ) * Complex.I * (x : ℂ))) :=
    ((contDiff_const.mul contDiff_const).mul ofRealCLM.contDiff).cexp
  have hmul : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ ↦ (-1 / 2 : ℂ) * cexp ((π : ℂ) * Complex.I * (x : ℂ)) * J₅' x) :=
    (contDiff_const.mul hExp).mul MagicFunction.b.Schwartz.J5Smooth.contDiff_J₅'
  have hEq : (fun x : ℝ ↦ (-1 / 2 : ℂ) * cexp ((π : ℂ) * Complex.I * (x : ℂ)) * J₅' x) = J₃' :=
    funext fun x => by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (J₃'_eq (x := x)).symm
  simpa [hEq] using hmul

/-- Schwartz-type decay bounds for `J₃'` and its iterated derivatives on `0 ≤ x`.

The prime in `decay_J₃'` refers to the function `J₃'`. -/
public theorem decay_J₃' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₃' x‖ ≤ C := by
  intro k n
  let c : ℂ := (Real.pi : ℂ) * Complex.I
  let e : ℝ → ℂ := fun x ↦ cexp ((x : ℂ) * c)
  let f : ℝ → ℂ := fun x ↦ (-1 / 2 : ℂ) • e x
  have hf_cont : ContDiff ℝ (⊤ : ℕ∞) f := by
    simpa [f, e] using ((ofRealCLM.contDiff.mul contDiff_const).cexp.const_smul (-1 / 2 : ℂ))
  have hbound_f : ∀ m : ℕ, ∀ x : ℝ, ‖iteratedFDeriv ℝ m f x‖ ≤ (1 / 2 : ℝ) * Real.pi ^ m :=
    fun m x => SpherePacking.ForMathlib.norm_iteratedFDeriv_smul_cexp_mul_pi_I_le m x
  have hdec5 : ∀ m : ℕ, ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ m J₅' x‖ ≤ C :=
    fun m => by simpa using (MagicFunction.b.Schwartz.J5Smooth.decay_J₅' (k := k) (n := m))
  obtain ⟨C, hC⟩ := SpherePacking.ForMathlib.decay_iteratedFDeriv_mul_of_bound_left
    (f := f) (g := J₅') (k := k) (n := n) (B := fun m ↦ (1 / 2 : ℝ) * Real.pi ^ m)
    hf_cont MagicFunction.b.Schwartz.J5Smooth.contDiff_J₅' hbound_f hdec5
  refine ⟨C, fun x hx => ?_⟩
  have hJ3fun : J₃' = fun y : ℝ ↦ f y * J₅' y :=
    funext fun y => by simp [f, e, c, mul_assoc, mul_left_comm, mul_comm, J₃'_eq (x := y)]
  simpa [hJ3fun] using hC x hx

end

end MagicFunction.b.Schwartz.J3Smooth
