/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import Architect
import SpherePacking.MagicFunction.a.Schwartz

open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

open scoped FourierTransform

namespace MagicFunction.a.Fourier

section Integral_Permutations

lemma fourier_involution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : 𝓢(V, E)) :
    (FourierTransform.fourierCLE ℂ _) ((FourierTransform.fourierCLE ℂ _) f) = fun x => f (-x) :=
by
  ext x; change 𝓕 (𝓕 f) x = f (-x)
  simpa [Real.fourierInv_eq_fourier_neg, neg_neg] using
    congrArg (fun g : V → E => g (-x))
      (f.continuous.fourierInv_fourier_eq
        f.integrable ((FourierTransform.fourierCLE ℂ _) f).integrable)

lemma radial_inversion {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : 𝓢(V, E)) (hf : Function.Even f) :
    (FourierTransform.fourierCLE ℂ _) ((FourierTransform.fourierCLE ℂ _) f) = f :=
by
  ext x; simpa [hf x] using congrArg (fun g => g x) (fourier_involution (V:=V) (E:=E) f)

theorem perm_I₁_I₂ : (FourierTransform.fourierCLE ℂ _) (I₁ + I₂) = I₃ + I₄ := by sorry

theorem perm_I₅ : (FourierTransform.fourierCLE ℂ _) (I₅) = I₆ := by sorry

-- Should use results from `RadialSchwartz.Radial` to prove the reverse.

theorem perm_₃_I₄ : (FourierTransform.fourierCLE ℂ _) (I₃ + I₄) = I₁ + I₂ := by
  exact perm_I₁_I₂ ▸
    radial_inversion (I₁ + I₂) (fun _ => by
      simp [I₁, I₂, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply])

-- should use fourier_involution and the radial symmetry of I₅
theorem perm_I₆ : (FourierTransform.fourierCLE ℂ _) (I₆) = I₅ :=
by
  simpa [← perm_I₅] using
    radial_inversion I₅ (fun _ => by
      simp [I₅, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply])

end Integral_Permutations

section Eigenfunction

@[blueprint
  "prop:a-fourier"
  (statement := /-- $a(x)$ satisfies \eqref{eqn:a-fourier}. -/)
  (proof := /--
  We recall that the Fourier transform of a Gaussian function is
  \begin{equation}\label{eqn:gaussian Fourier}
      \mathcal{F}(e^{\pi i \|x\|^2 z})(y)=z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z}) }.
  \end{equation}
  Next, we exchange the contour integration with respect to $z$ variable and Fourier transform with
  respect to $x$ variable in \eqref{eqn:a-definition}.
  This can be done, since the corresponding double integral converges absolutely. In this way we
  obtain
  \begin{align}
      \widehat{a}(y)=&\int\limits_{-1}^i\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,z^{-4}\,e^{\pi i
      \|y\|^2 \,(\frac{-1}{z})}\,dz
      +\int\limits_{1}^i\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,z^{-4}\,e^{\pi i \|y\|^2
      \,(\frac{-1}{z})}\,dz\notag \\
      -&2\int\limits_{0}^i\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,z^{-4}\,e^{\pi i \|y\|^2
      \,(\frac{-1}{z})}\,dz +2\int\limits_{i}^{i\infty}\phi_0(z)\,z^{-4}\,e^{\pi i \|y\|^2
      \,(\frac{-1}{z})}\,dz.\notag
  \end{align}
  Now we make a change of variables $w=\frac{-1}{z}$. We obtain
  \begin{align}
      \widehat{a}(y)=&\int\limits_{1}^i\phi_0\Big(1-\frac{1}{w-1}\Big)\,(\frac{-1}{w}+1)^2\,w^{2}\,e^{\pi
      i \|y\|^2 \,w}\,dw\notag\\
      +&\int\limits_{-1}^i\phi_0\Big(1-\frac{1}{w+1}\Big)\,(\frac{-1}{w}-1)^2\,w^2\,e^{\pi i \|y\|^2
      \,w}\,dw\\
      -&2\int\limits_{i \infty}^i\phi_0(w)\,e^{\pi i \|y\|^2 \,w}\,dw
      +2\int\limits_{i}^{0}\phi_0\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|y\|^2 \,w}\,dw.\notag
  \end{align}
  Since $\phi_0$ is $1$-periodic we have
  \begin{align}
      \widehat{a}(y)\,=\,&\int\limits_{1}^i\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i \|y\|^2
      \,z}\,dz
      +\int\limits_{-1}^i\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i \|y\|^2 \,z}\,dz\notag \\
      +&2\int\limits_{i}^{i\infty}\phi_0(z)\,e^{\pi i \|y\|^2 \,z}\,dz
      -2\int\limits_{0}^{i}\phi_0\Big(\frac{-1}{z}\Big)\,z^{2}\,e^{\pi i \|y\|^2 \,z}\,dz\notag \\
      \,=\,&a(y).
  \end{align}
  This finishes the proof of the proposition.
  -/)
  (proofUses := ["lemma:Gaussian-Fourier"])
  (latexEnv := "proposition")]
theorem eig_a : (FourierTransform.fourierCLE ℂ _) a = a := by
  rw [a_eq_sum_integrals_SchwartzIntegrals]
  have hrw : I₁ + I₂ + I₃ + I₄ + I₅ + I₆ = (I₁ + I₂) + (I₃ + I₄) + I₅ + I₆ := by ac_rfl
  rw [hrw, map_add, map_add, map_add, perm_I₁_I₂, perm_I₅, perm_₃_I₄, perm_I₆]
  ac_rfl

end Eigenfunction
end MagicFunction.a.Fourier
