import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Monotone.Defs

import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.JacobiTheta

open Filter
open scoped Real Manifold


/--
Definition of $F$ and $G$ and auxiliary functions for the inequality between them
on the imaginary axis.
-/
noncomputable def F := (E₂ * E₄.toFun - E₆.toFun) ^ 2

noncomputable def G := H₂ ^ 3 * ((2 : ℝ) • H₂ ^ 2 + (5 : ℝ) • H₂ * H₄ + (5 : ℝ) • H₄ ^ 2)

noncomputable def negDE₂ := - (D E₂)

noncomputable def Δ_fun := 1728⁻¹ * (E₄.toFun ^ 3 - E₆.toFun ^ 2)

noncomputable def L₁₀ := (D F) * G - F * (D G)

noncomputable def SerreDer_22_L₁₀ := serre_D 22 L₁₀

noncomputable def FReal (t : ℝ) : ℝ := (F.resToImagAxis t).re

noncomputable def GReal (t : ℝ) : ℝ := (G.resToImagAxis t).re

noncomputable def FmodGReal (t : ℝ) : ℝ := (FReal t) / (GReal t)

theorem F_eq_FReal {t : ℝ} (ht : 0 < t) : F.resToImagAxis t = FReal t := by sorry

theorem G_eq_GReal {t : ℝ} (ht : 0 < t) : G.resToImagAxis t = GReal t := by sorry

theorem FmodG_eq_FmodGReal {t : ℝ} (ht : 0 < t) :
    FmodGReal t = (F.resToImagAxis t) / (G.resToImagAxis t) := by sorry

/- Some basic facts -/
theorem F_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
  have h : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₂ * E₄.toFun - E₆.toFun) := by
    exact MDifferentiable.sub (MDifferentiable.mul E₂_holo' E₄.holo') E₆.holo'
  rw [F, pow_two]
  exact MDifferentiable.mul h h

theorem G_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
  sorry

theorem SerreF_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D 10 F) := by
  exact serre_D_differentiable F_holo

theorem SerreG_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D 10 G) := by
  exact serre_D_differentiable G_holo

theorem FReal_Differentiable {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ FReal t := by
  sorry

theorem GReal_Differentiable {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ GReal t := by
  sorry

theorem F_aux : D F = 5 * 6⁻¹ * E₂ ^ 3 * E₄.toFun ^ 2 - 5 * 2⁻¹ * E₂ ^ 2 * E₄.toFun * E₆.toFun
    + 5 * 6⁻¹ * E₂ * E₄.toFun ^ 3 + 5 * 3⁻¹ * E₂ * E₆.toFun ^ 2 - 5 * 6⁻¹ * E₄.toFun^2 * E₆.toFun
    := by
  rw [F, D_sq, D_sub, D_mul]
  · ring_nf
    rw [ramanujan_E₂, ramanujan_E₄, ramanujan_E₆]
    ext z
    simp
    ring_nf

  -- Holomorphicity of the terms
  · exact E₂_holo'
  · exact E₄.holo'
  · exact MDifferentiable.mul E₂_holo' E₄.holo'
  · exact E₆.holo'
  · exact MDifferentiable.sub (MDifferentiable.mul E₂_holo' E₄.holo') E₆.holo'

/--
Modular linear differential equation satisfied by $F$.
-/
theorem MLDE_F : serre_D 12 (serre_D 10 F) = 5 * 6⁻¹ * F + 7200 * Δ_fun * negDE₂ := by
  ext x
  rw [negDE₂, Δ_fun, serre_D, serre_D, F_aux]
  unfold serre_D
  rw [F_aux]
  sorry

/--
Modular linear differential equation satisfied by $G$.
-/
theorem MLDE_G : serre_D 12 (serre_D 10 G) = 5 * 6⁻¹ * G - 640 * Δ_fun * H₂ := by
  sorry

/- Positivity of (quasi)modular forms. $F, G, H_2$ are all (sum of) squares. -/
lemma negDE₂_pos : ResToImagAxis.Pos negDE₂ := by
  sorry

lemma Δ_fun_pos : ResToImagAxis.Pos Δ_fun := by
  sorry

lemma F_pos : ResToImagAxis.Pos F := by
  sorry

@[fun_prop]
lemma H₂_pos : ResToImagAxis.Pos H₂ := by
  sorry

@[fun_prop]
lemma H₄_pos : ResToImagAxis.Pos H₄ := by
  sorry

lemma G_pos : ResToImagAxis.Pos G := by
  have _ : 0 < (2 : ℝ) := by positivity
  have _ : 0 < (5 : ℝ) := by positivity
  apply ResToImagAxis.Pos.mul
  · exact ResToImagAxis.Pos.pow H₂_pos 3
  · apply ResToImagAxis.Pos.add
    · apply ResToImagAxis.Pos.add
      · apply ResToImagAxis.Pos.smul _ (by positivity)
        exact ResToImagAxis.Pos.pow H₂_pos 2
      · apply ResToImagAxis.Pos.mul
        · apply ResToImagAxis.Pos.smul _ (by positivity)
          exact H₂_pos
        · exact H₄_pos
    · apply ResToImagAxis.Pos.smul _ (by positivity)
      exact ResToImagAxis.Pos.pow H₄_pos 2


lemma L₁₀_SerreDer : L₁₀ = (serre_D 10 F) * G - F * (serre_D 10 G) := by
  calc
    L₁₀ = (D F) * G - F * (D G) := rfl
    _ = (D F - 10 * 12⁻¹ * E₂ * F) * G - F * (D G - 10 * 12⁻¹ * E₂ * G) := by ring_nf
    _ = (serre_D 10 F) * G - F * (serre_D 10 G) := by ext z; simp [serre_D]

lemma SerreDer_22_L₁₀_SerreDer :
    SerreDer_22_L₁₀ = (serre_D 12 (serre_D 10 F)) * G - F * (serre_D 12 (serre_D 10 G)) := by
  have SF_holo := @serre_D_differentiable F 10 F_holo
  have SG_holo := @serre_D_differentiable G 10 G_holo
  calc
    SerreDer_22_L₁₀ = serre_D 22 L₁₀ := rfl
    _ = serre_D 22 (serre_D 10 F * G - F * serre_D 10 G) := by rw [L₁₀_SerreDer]
    _ = serre_D 22 (serre_D 10 F * G) - serre_D 22 (F * serre_D 10 G) := by
        apply serre_D_sub _ _ _
        · exact MDifferentiable.mul SF_holo G_holo
        · exact MDifferentiable.mul F_holo SG_holo
    _ = serre_D (12 + 10) ((serre_D 10 F) * G) - serre_D (10 + 12) (F * serre_D 10 G) := by ring_nf
    _ = serre_D 12 (serre_D 10 F) * G + (serre_D 10 F) * (serre_D 10 G)
        - serre_D (10 + 12) (F * serre_D 10 G) := by
          simpa using (serre_D_mul 12 10 (serre_D 10 F) G SF_holo G_holo)
    _ = serre_D 12 (serre_D 10 F) * G + (serre_D 10 F) * (serre_D 10 G)
        - ((serre_D 10 F) * (serre_D 10 G) + F * (serre_D 12 (serre_D 10 G))) := by
          simpa using (serre_D_mul 10 12 F (serre_D 10 G) F_holo SG_holo)
    _ = (serre_D 12 (serre_D 10 F)) * G - F * (serre_D 12 (serre_D 10 G)) := by ring_nf

/- $\partial_{22} \mathcal{L}_{1, 0}$ is positive on the imaginary axis. -/
lemma SerreDer_22_L₁₀_real : ResToImagAxis.Real SerreDer_22_L₁₀ := by
  rw [SerreDer_22_L₁₀_SerreDer, MLDE_F, MLDE_G, ResToImagAxis.Real]
  intro t ht
  ring_nf
  simp only [Function.resToImagAxis_apply]
  sorry

lemma SerreDer_22_L₁₀_pos : ResToImagAxis.Pos SerreDer_22_L₁₀ := by
  refine And.intro SerreDer_22_L₁₀_real ?_
  intro t ht
  rw [SerreDer_22_L₁₀_SerreDer, MLDE_F, MLDE_G]
  ring_nf
  sorry

/- $\mathcal{L}_{1, 0}$ is eventually positive on the imaginary axis. -/
lemma L₁₀_eventuallyPos : ResToImagAxis.EventuallyPos L₁₀ := by
  sorry

/- $\mathcal{L}_{1, 0}$ is positive on the imaginary axis. -/
lemma L₁₀_pos : ResToImagAxis.Pos L₁₀ := antiSerreDerPos SerreDer_22_L₁₀_pos L₁₀_eventuallyPos

/--
$t \mapsto F(it) / G(it)$ is monotone decreasing.
-/
theorem FmodG_antitone : AntitoneOn FmodGReal (Set.Ioi 0) := by
  sorry

/--
$\lim_{t \to 0^+} F(it) / G(it) = 18 / \pi^2$.
-/
theorem FmodG_rightLimitAt_zero :
    Tendsto FmodGReal (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin (18 * (π ^ (-2 : ℤ))) Set.univ) := by
  sorry

/--
Main inequalities between $F$ and $G$ on the imaginary axis.
-/
theorem FG_inequality_1 {t : ℝ} (ht : 0 < t) :
    FReal t + 18 * (π ^ (-2 : ℤ)) * GReal t > 0 := by
  sorry

theorem FG_inequality_2 {t : ℝ} (ht : 0 < t) :
    FReal t - 18 * (π ^ (-2 : ℤ)) * GReal t < 0 := by
  sorry
