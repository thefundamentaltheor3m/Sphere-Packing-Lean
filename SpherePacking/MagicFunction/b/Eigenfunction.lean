/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import Architect
import SpherePacking.MagicFunction.b.Schwartz

open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

open scoped FourierTransform

namespace MagicFunction.b.Fourier

section Integral_Permutations

theorem perm_J₁_J₂ : (FourierTransform.fourierCLE ℂ _) (J₁ + J₂) = -(J₃ + J₄) := by sorry

theorem perm_J₅ : (FourierTransform.fourierCLE ℂ _) (J₅) = -J₆ := by sorry

-- Should use results from `RadialSchwartz.Radial` and linearity to prove the reverse.

theorem perm_₃_J₄ : (FourierTransform.fourierCLE ℂ _) (J₃ + J₄) = -(J₁ + J₂) := by
  have h₁ : (FourierTransform.fourierCLE ℂ _) ((FourierTransform.fourierCLE ℂ _) J₁) = J₁ := by
    ext x
    simpa [J₁, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply,
      Real.fourierInv_eq_fourier_neg] using
        congrArg (· (-x)) (J₁.continuous.fourierInv_fourier_eq J₁.integrable
          ((FourierTransform.fourierCLE ℂ _) J₁).integrable)
  have h₂ : (FourierTransform.fourierCLE ℂ _) ((FourierTransform.fourierCLE ℂ _) J₂) = J₂ := by
    ext x
    simpa [J₂, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply,
      Real.fourierInv_eq_fourier_neg] using
        congrArg (· (-x)) (J₂.continuous.fourierInv_fourier_eq J₂.integrable
          ((FourierTransform.fourierCLE ℂ _) J₂).integrable)
  simpa only [neg_add_rev, add_comm, map_add, map_neg, neg_neg, h₁, h₂] using
    congrArg (-(FourierTransform.fourierCLE ℂ _) ·) perm_J₁_J₂ |>.symm

theorem perm_J₆ : (FourierTransform.fourierCLE ℂ _) (J₆) = -J₅ := by
  have h : ((FourierTransform.fourierCLE ℂ _)).symm J₆ = (FourierTransform.fourierCLE ℂ _) J₆ := by
    ext x
    simp only [FourierTransform.fourierCLE_symm_apply, FourierTransform.fourierCLE_apply,
      fourier_coe, fourierInv_coe, Real.fourierInv_eq_fourier_comp_neg]
    suffices (fun x ↦ J₆ (-x)) = ⇑J₆ by exact congr(𝓕 $this x)
    ext
    simp [J₆, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]
  have := (congrArg ((FourierTransform.fourierCLE ℂ _)).symm perm_J₅).symm
  simp only [map_neg, ContinuousLinearEquiv.symm_apply_apply, ← h] at this ⊢
  rw [← this, neg_neg]

end Integral_Permutations

section Eigenfunction

@[blueprint
  "prop:b-fourier"
  (statement := /-- $b(x)$ satisfies \eqref{eqn:b-fourier}. -/)
  (proof := /--
  Here, we repeat the arguments used in the proof of Proposition~\ref{prop:a-fourier}.
  We use identity~\eqref{eqn:gaussian Fourier} and change contour integration in $z$ and Fourier
  transform in $x$. Thus we obtain
  \begin{align}
      \mathcal{F}(b)(x)= & \int\limits_{-1}^{i}\psi_T(z)\,z^{-4}\,e^{\pi i \|x\|^2
      (\frac{-1}{z})}\,dz
          + \int\limits_{1}^{i}\psi_T(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz \notag \\
      -& 2\,\int\limits_{0}^{i}\psi_I(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz
      - 2\,\int\limits_{i}^{i\infty}\psi_S(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz. \notag
  \end{align}
  We make the change of variables $w=\frac{-1}{z}$ and arrive at
  \begin{align}
      \mathcal{F}(b)(x)= & \int\limits_{1}^{i}\psi_T\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2
      w}\,dw
          + \int\limits_{-1}^{i}\psi_T\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw \notag
          \\
      -& 2\,\int\limits_{i\infty}^{i}\psi_I\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw
      - 2\,\int\limits_{i}^{0}\psi_S\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw.\notag
  \end{align}
  Now we observe that the definitions \eqref{eqn:psiI-define}--\eqref{eqn:psiS-define} imply
  \begin{align}
      \psi_T|_{-2}S=&-\psi_T \notag \\
      \psi_I|_{-2}S=&\psi_S \notag \\
      \psi_S|_{-2}S=&\psi_I. \notag
  \end{align}
  Therefore, we arrive at
  \begin{align}
      \mathcal{F}(b)(x)= & \int\limits_{1}^{i}-\psi_T(z)\,e^{\pi i \|x\|^2 z}\,dz
          + \int\limits_{-1}^{i}-\psi_T(z)\,e^{\pi i \|x\|^2 z}\,dz \notag \\
      +& 2\,\int\limits_{i}^{i\infty}\psi_S(z)\,e^{\pi i \|x\|^2 z}\,dz
      + 2\,\int\limits_{0}^{i}\psi_I(z)\,e^{\pi i \|x\|^2 w}\,dw.\notag
  \end{align}
  Now from~\eqref{eqn:b-definition} we see that
  $$ \mathcal{F}(b)(x)=-b(x). $$
  -/)
  (proofUses := ["lemma:Gaussian-Fourier"])
  (latexEnv := "proposition")]
theorem eig_b : (FourierTransform.fourierCLE ℂ _) b = -b := by
  rw [b_eq_sum_integrals_SchwartzIntegrals]
  have hrw : J₁ + J₂ + J₃ + J₄ + J₅ + J₆ = (J₁ + J₂) + (J₃ + J₄) + J₅ + J₆ := by ac_rfl
  rw [hrw, map_add, map_add, map_add, perm_J₁_J₂, perm_J₅, perm_₃_J₄, perm_J₆]
  abel

end Eigenfunction

end MagicFunction.b.Fourier
