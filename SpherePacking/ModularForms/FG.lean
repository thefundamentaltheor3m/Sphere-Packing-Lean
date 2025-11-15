import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Monotone.Defs

import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.JacobiTheta

open Filter
open scoped Real


/--
Definition of $F$ and $G$ and auxiliary functions for the inequality between them
on the imaginary axis.
-/
noncomputable def F := (E₂ * E₄.toFun - E₆.toFun) ^ 2

noncomputable def G := H₂ ^ 3 * (2 * H₂ ^ 2 + 5 * H₂ * H₄ + 5 * H₄ ^ 2)

noncomputable def X₄₂ := 288⁻¹ * (E₄.toFun - E₂ * E₂)

noncomputable def Δ_fun := 1728⁻¹ * (E₄.toFun ^ 3 - E₆.toFun ^ 2)

noncomputable def L₁₀ := (D F) * G - F * (D G)

noncomputable def SerreDer_22_L₁₀ := serre_D 22 L₁₀

noncomputable def FReal (t : ℝ) : ℝ := (F.resToImagAxis t).re

noncomputable def GReal (t : ℝ) : ℝ := (G.resToImagAxis t).re

noncomputable def FmodGReal (t : ℝ) : ℝ := (FReal t) / (GReal t)

theorem F_eq_FReal (t : ℝ) (ht : 0 < t) : F.resToImagAxis t = FReal t := by sorry

theorem G_eq_GReal (t : ℝ) (ht : 0 < t) : G.resToImagAxis t = GReal t := by sorry

theorem FmodG_eq_FmodGReal (t : ℝ) (ht : 0 < t) :
    FmodGReal t = (F.resToImagAxis t) / (G.resToImagAxis t) := by sorry

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
  have h24 := MDifferentiable.mul E₂_holo' E₄.holo'
  exact MDifferentiable.sub h24 E₆.holo'


/--
Modular linear differential equation satisfied by $F$.
-/
theorem MLDE_F : serre_D 12 (serre_D 10 F) = 5 * 6⁻¹ * F + 172800 * Δ_fun * X₄₂ := by
  ext x
  rw [X₄₂, Δ_fun, serre_D, serre_D, F_aux]
  unfold serre_D
  rw [F_aux]
  sorry

/--
Modular linear differential equation satisfied by $G$.
-/
theorem MLDE_G : serre_D 12 (serre_D 10 G) = 5 * 6⁻¹ * G - 640 * Δ_fun * H₂ := by
  sorry

theorem F_pos : ResToImagAxis.Pos F := by
  sorry

theorem G_pos : ResToImagAxis.Pos G := by
  sorry

theorem X₄₂_pos : ResToImagAxis.Pos X₄₂ := by
  sorry

theorem Δ_fun_pos : ResToImagAxis.Pos Δ_fun := by
  sorry

theorem H₂_pos : ResToImagAxis.Pos H₂ := by
  sorry

theorem L₁₀_SerreDer : L₁₀ = (serre_D 10 F) * G - F * (serre_D 10 G) := by
  sorry

theorem SerreDer_22_L₁₀_SerreDer :
    SerreDer_22_L₁₀ = (serre_D 12 (serre_D 10 F)) * G - F * (serre_D 12 (serre_D 10 G)) := by
sorry

/- $\partial_{22} \mathcal{L}_{1, 0}$ is positive on the imaginary axis. -/
theorem SerreDer_22_L₁₀_pos : ResToImagAxis.Pos SerreDer_22_L₁₀ := by
  rw [SerreDer_22_L₁₀_SerreDer, MLDE_F, MLDE_G, ResToImagAxis.Pos]
  ring_nf
  intro t ht
  obtain ⟨Ft, hFtpos, hFtres⟩ := F_pos t ht
  obtain ⟨Gt, hGtpos, hGtres⟩ := G_pos t ht
  obtain ⟨X₄₂t, hX₄₂tpos, hX₄₂tres⟩ := X₄₂_pos t ht
  obtain ⟨Δt, hΔtpos, hΔtres⟩ := Δ_fun_pos t ht
  obtain ⟨H₂t, hH₂tpos, hH₂tres⟩ := H₂_pos t ht
  let r := Ft * Δt * H₂t * 640 + Δt * X₄₂t * Gt * 172800
  have hr_pos : 0 < r := by positivity
  use r
  constructor
  · exact hr_pos
  · sorry

/- $\mathcal{L}_{1, 0}$ is eventually positive on the imaginary axis. -/
theorem L₁₀_eventuallyPos : ResToImagAxis.EventuallyPos L₁₀ := by
  sorry

/- $\mathcal{L}_{1, 0}$ is positive on the imaginary axis. -/
theorem L₁₀_pos : ResToImagAxis.Pos L₁₀ := antiSerreDerPos SerreDer_22_L₁₀_pos L₁₀_eventuallyPos

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
Main inequality between $F$ and $G$ on the imaginary axis.
-/
theorem FG_inequality {t : ℝ} (ht : 0 < t) :
    (F.resToImagAxis t).re < 18 * (π ^ (-2 : ℤ)) * (G.resToImagAxis t).re := by
  sorry
