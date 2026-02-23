module
public import SpherePacking.MagicFunction.b.psi
public import SpherePacking.Contour.MobiusInv.Basic
import SpherePacking.Contour.MobiusInv.PermJ12PsiFourier


/-!
# Permutation for `J₁+J₂`

This file defines the integrands used in the `b`-side permutation argument for `J₁ + J₂` and
records the modular/Mobius identities that relate them.

The main steps are:
1. Rewrite the Fourier transforms of `J₁` and `J₂` as curve integrals of `Ψ₁_fourier`.
2. Use the modular relation `ψT ∣[-2] S = -ψT` to rewrite `Ψ₁_fourier` as a Mobius pullback of
   `Ψ₁'`.
3. Deform the contour inside a wedge region using the Poincare lemma.

## Main definitions
* `Ψ₁'`
* `Ψ₁_fourier`

## Main statements
* `ψT'_mobiusInv_eq_div`
* `Ψ₁_fourier_eq_neg_deriv_mul`
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory

section PermJ12

open MeasureTheory Set Complex Real
open Filter
open scoped Interval

open SpherePacking


/-- The integrand for the primed real integrals `J₁'` and `J₂'`.

The prime in `Ψ₁'` matches the primed integrals `J₁', J₂'` appearing in the permutation argument. -/
@[expose] public def Ψ₁' (r : ℝ) (z : ℂ) : ℂ :=
  ψT' z * cexp ((π : ℂ) * I * (r : ℂ) * z)

/-- The Fourier-side integrand obtained from `Ψ₁'` after the Gaussian Fourier transform and the
Mobius change of variables `z ↦ -1 / z`. -/
@[expose] public def Ψ₁_fourier (r : ℝ) (z : ℂ) : ℂ :=
  ψT' z * (((I : ℂ) / z) ^ (4 : ℕ)) * cexp ((π : ℂ) * I * (r : ℂ) * (-1 / z))

/-- Modular relation for `ψT'` under Mobius inversion `z ↦ -1 / z`. -/
public lemma ψT'_mobiusInv_eq_div (z : ℂ) (hz : 0 < z.im) :
    ψT' (mobiusInv z) = -(ψT' z) / z ^ (2 : ℕ) := by
  let zH : UpperHalfPlane := ⟨z, hz⟩
  have hz0 : (zH : ℂ) ≠ 0 := by
    exact fun hz0 => (ne_of_gt hz) (by simpa [zH] using congrArg Complex.im hz0)
  have hz2 : ((zH : ℂ) ^ (2 : ℕ) : ℂ) ≠ 0 := pow_ne_zero 2 hz0
  -- Evaluate `ψT ∣[-2] S = -ψT` at `zH`.
  have h := congrArg (fun F : UpperHalfPlane → ℂ => F zH) ψT_slash_S
  have hS :
      (SlashAction.map (-2) ModularGroup.S ψT) zH =
        ψT (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos) * (zH : ℂ) ^ (2 : ℕ) := by
    simpa using (modular_slash_S_apply (f := ψT) (k := (-2 : ℤ)) (z := zH))
  have hS' :
      ψT (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos) * (zH : ℂ) ^ (2 : ℕ) =
        -ψT zH := by
    simpa [hS] using h
  have hdiv :
      ψT (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos) =
        (-ψT zH) / (zH : ℂ) ^ (2 : ℕ) := by
    exact (eq_div_iff hz2).2 hS'
  -- Identify the Möbius image point: `(-zH)⁻¹ = mobiusInv z`.
  have hz' : 0 < (mobiusInv z).im := mobiusInv_im_pos z hz
  have hmk :
      (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos : UpperHalfPlane) =
        ⟨mobiusInv z, hz'⟩ := by
    ext1
    simp [zH, mobiusInv, inv_neg]
  -- Convert to `ψT'` on `ℂ`.
  have hTz : ψT' z = ψT zH := by simp [ψT', hz, zH]
  have hTw : ψT' (mobiusInv z) = ψT ⟨mobiusInv z, hz'⟩ := by
    simp [ψT', hz']
  have hmkψ :
      ψT ⟨mobiusInv z, hz'⟩ =
        ψT (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos) := by
    simpa using congrArg ψT hmk.symm
  -- Rewrite `hdiv` using `hmk` and the definitions of `ψT'`.
  calc
    ψT' (mobiusInv z) = ψT ⟨mobiusInv z, hz'⟩ := hTw
    _ = ψT (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos) := hmkψ
    _ = (-ψT zH) / (zH : ℂ) ^ (2 : ℕ) := hdiv
    _ = -(ψT' z) / z ^ (2 : ℕ) := by
      simp [hTz, zH, div_eq_mul_inv]

/-- Express `Ψ₁_fourier` as the pullback of `Ψ₁'` under Mobius inversion, including the Jacobian
factor `-deriv mobiusInv`. -/
public lemma Ψ₁_fourier_eq_neg_deriv_mul (r : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Ψ₁_fourier r z = -(deriv mobiusInv z) * Ψ₁' r (mobiusInv z) := by
  simpa [Ψ₁', Ψ₁_fourier, mul_assoc, mul_left_comm, mul_comm] using
    (SpherePacking.Contour.permJ12_Ψ₁_fourier_eq_neg_deriv_mul
      (ψ := ψT') (A := (π : ℂ) * Complex.I) (q := 2) (r := r) (z := z) hz
      (hψ := ψT'_mobiusInv_eq_div (z := z) hz) (hI := by simp))

end Integral_Permutations.PermJ12
end

end MagicFunction.b.Fourier
