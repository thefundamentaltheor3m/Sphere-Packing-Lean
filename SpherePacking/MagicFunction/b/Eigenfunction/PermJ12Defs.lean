module
public import SpherePacking.MagicFunction.b.Psi
public import SpherePacking.Contour.MobiusInv.Basic
import SpherePacking.Contour.MobiusInv.PermJ12PsiFourier

/-!
# Permutation for `J₁+J₂`

Integrands for the `b`-side `J₁ + J₂` permutation and the modular/Mobius identities relating
them: rewrite `𝓕 J₁`, `𝓕 J₂` as curve integrals, use `ψT ∣[-2] S = -ψT` to rewrite `Ψ₁_fourier`
as a Mobius pullback of `Ψ₁'`, and deform the contour inside a wedge region.
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology Real Interval
open Set Complex Real MeasureTheory Filter SpherePacking


/-- The integrand for the primed real integrals `J₁'` and `J₂'`. -/
@[expose] public def Ψ₁' (r : ℝ) (z : ℂ) : ℂ := ψT' z * cexp ((π : ℂ) * I * (r : ℂ) * z)

/-- The Fourier-side integrand: `Ψ₁'` after Gaussian Fourier transform and `z ↦ -1 / z`. -/
@[expose] public def Ψ₁_fourier (r : ℝ) (z : ℂ) : ℂ :=
  ψT' z * (((I : ℂ) / z) ^ (4 : ℕ)) * cexp ((π : ℂ) * I * (r : ℂ) * (-1 / z))

/-- Modular relation for `ψT'` under Mobius inversion `z ↦ -1 / z`. -/
public lemma ψT'_mobiusInv_eq_div (z : ℂ) (hz : 0 < z.im) :
    ψT' (mobiusInv z) = -(ψT' z) / z ^ (2 : ℕ) := by
  let zH : UpperHalfPlane := ⟨z, hz⟩
  have hz0 : (zH : ℂ) ≠ 0 :=
    fun hz0 => hz.ne' (by simpa [zH] using congrArg Complex.im hz0)
  have hdiv : ψT (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos) =
      (-ψT zH) / (zH : ℂ) ^ (2 : ℕ) :=
    (eq_div_iff (pow_ne_zero 2 hz0)).2 <| by
      simpa using (modular_slash_S_apply (f := ψT) (k := (-2 : ℤ)) (z := zH)).symm.trans
        (congrArg (fun F : UpperHalfPlane → ℂ => F zH) ψT_slash_S)
  have hz' : 0 < (mobiusInv z).im := by
    simpa [mobiusInv, Complex.inv_im, div_eq_mul_inv] using
      div_pos hz (Complex.normSq_pos.2 fun hz0 => hz.ne' (by simp [hz0]))
  calc
    ψT' (mobiusInv z) = ψT ⟨mobiusInv z, hz'⟩ := by simp [ψT', hz']
    _ = ψT (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos) := by
      congr 1; ext1; simp [zH, mobiusInv, inv_neg]
    _ = (-ψT zH) / (zH : ℂ) ^ (2 : ℕ) := hdiv
    _ = -(ψT' z) / z ^ (2 : ℕ) := by simp [ψT', hz, zH, div_eq_mul_inv]

/-- Express `Ψ₁_fourier` as the pullback of `Ψ₁'` under Mobius inversion, including the Jacobian
factor `-deriv mobiusInv`. -/
public lemma Ψ₁_fourier_eq_neg_deriv_mul (r : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Ψ₁_fourier r z = -(deriv mobiusInv z) * Ψ₁' r (mobiusInv z) := by
  simpa [Ψ₁', Ψ₁_fourier, mul_assoc, mul_left_comm, mul_comm] using
    SpherePacking.Contour.permJ12_Ψ₁_fourier_eq_neg_deriv_mul
      (ψ := ψT') (A := (π : ℂ) * Complex.I) (q := 2) (r := r) (z := z) hz
      (hψ := ψT'_mobiusInv_eq_div (z := z) hz) (hI := by simp)

end

end MagicFunction.b.Fourier
