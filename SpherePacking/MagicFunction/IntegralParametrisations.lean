/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Integral parametrisations

Explicit complex-valued parametrisations `z₁`--`z₆` used to rewrite contour integrals in the magic
function argument, together with their extensions `z₁'`--`z₆'` to all real parameters.
-/

namespace MagicFunction.Parametrisations

open Set Complex Real

local notation "ℍ₀" => UpperHalfPlane.upperHalfPlaneSet

noncomputable section Parametrisations

/-- Vertical segment `-1 → -1 + i`. -/
@[expose] public def z₁ (t : Icc (0 : ℝ) 1) : ℂ := -1 + I * t
/-- Horizontal segment `-1 + i → i`. -/
@[expose] public def z₂ (t : Icc (0 : ℝ) 1) : ℂ := -1 + t + I
/-- Vertical segment `1 → 1 + i`. -/
@[expose] public def z₃ (t : Icc (0 : ℝ) 1) : ℂ := 1 + I * t
/-- Horizontal segment `1 + i → i`. -/
@[expose] public def z₄ (t : Icc (0 : ℝ) 1) : ℂ := 1 - t + I
/-- Vertical segment `0 → i`. -/
@[expose] public def z₅ (t : Icc (0 : ℝ) 1) : ℂ := I * t
/-- Imaginary ray `i * Ici 1`. -/
@[expose] public def z₆ (t : Ici (1 : ℝ)) : ℂ := I * t

/-- `IccExtend` of `z₁`. -/
@[expose] public def z₁' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₁ t
/-- `IccExtend` of `z₂`. -/
@[expose] public def z₂' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₂ t
/-- `IccExtend` of `z₃`. -/
@[expose] public def z₃' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₃ t
/-- `IccExtend` of `z₄`. -/
@[expose] public def z₄' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₄ t
/-- `IccExtend` of `z₅`. -/
@[expose] public def z₅' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₅ t
/-- `IciExtend` of `z₆`. -/
@[expose] public def z₆' (t : ℝ) : ℂ := IciExtend z₆ t

/-- `(z₂' t).im = 1`. -/
public lemma im_z₂'_eq_one (t : ℝ) : (z₂' t).im = (1 : ℝ) := by simp [z₂', Set.IccExtend_apply, z₂]
/-- `(z₄' t).im = 1`. -/
public lemma im_z₄'_eq_one (t : ℝ) : (z₄' t).im = (1 : ℝ) := by simp [z₄', Set.IccExtend_apply, z₄]
/-- `(z₂' t).im > 0`. -/
public lemma im_z₂'_pos_all (t : ℝ) : 0 < (z₂' t).im := by simp [im_z₂'_eq_one]
/-- `(z₄' t).im > 0`. -/
public lemma im_z₄'_pos_all (t : ℝ) : 0 < (z₄' t).im := by simp [im_z₄'_eq_one]

/-- `‖z₅' t‖ ≤ 1`. -/
public lemma norm_z₅'_le_one (t : ℝ) : ‖z₅' t‖ ≤ 1 := by
  set u : ℝ := max 0 (min 1 t) with hu
  simpa [show ‖z₅' t‖ = u from by simp [z₅', Set.IccExtend_apply, z₅, hu, Complex.norm_real]]
    using (by simp [hu] : u ≤ 1)

/-- `‖z₁' t‖ ≤ 2`. -/
public lemma norm_z₁'_le_two (t : ℝ) : ‖z₁' t‖ ≤ 2 := by
  set u : ℝ := max 0 (min 1 t) with hu
  rw [show z₁' t = (-1 : ℂ) + (I : ℂ) * (u : ℂ) from by simp [z₁', Set.IccExtend_apply, z₁, hu]]
  refine (norm_add_le _ _).trans ?_
  simp [Complex.norm_real, abs_of_nonneg (by simp [hu] : (0 : ℝ) ≤ u)]
  linarith [show u ≤ 1 by simp [hu]]

/-- `‖z₂' t‖ ≤ 2`. -/
public lemma norm_z₂'_le_two (t : ℝ) : ‖z₂' t‖ ≤ 2 := by
  set u : ℝ := max 0 (min 1 t) with hu
  have hnorm : ‖(-1 : ℂ) + (u : ℂ)‖ ≤ 1 := by
    rw [show ‖(-1 : ℂ) + (u : ℂ)‖ = |u - 1| from by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using Complex.norm_real (u - 1)]
    grind only [= max_def, = min_def, = abs.eq_1]
  rw [show z₂' t = ((-1 : ℂ) + (u : ℂ)) + (I : ℂ) from by simp [z₂', Set.IccExtend_apply, z₂, hu]]
  exact (norm_add_le _ _).trans (by linarith [hnorm, show ‖(I : ℂ)‖ = 1 by simp])

/-- `‖z₄' t‖ ≤ 2`. -/
public lemma norm_z₄'_le_two (t : ℝ) : ‖z₄' t‖ ≤ 2 := by
  set u : ℝ := max 0 (min 1 t) with hu
  have hnorm : ‖(1 : ℂ) - (u : ℂ)‖ ≤ 1 := by
    rw [show ‖(1 : ℂ) - (u : ℂ)‖ = |1 - u| from by simpa using Complex.norm_real (1 - u),
      abs_of_nonneg (sub_nonneg.mpr (by simp [hu] : u ≤ 1))]
    linarith [show (0 : ℝ) ≤ u by simp [hu]]
  rw [show z₄' t = ((1 : ℂ) - (u : ℂ)) + (I : ℂ) from by
    simp [z₄', Set.IccExtend_apply, z₄, hu, sub_eq_add_neg]]
  exact (norm_add_le _ _).trans (by linarith [hnorm, show ‖(I : ℂ)‖ = 1 by simp])

end Parametrisations

section UpperHalfPlane

open scoped UpperHalfPlane

private lemma im_pos_of_mapsto {s : Set ℝ} {f : ℝ → ℂ} (hf : MapsTo f s ℍ₀) {t : ℝ} (ht : t ∈ s) :
    0 < (f t).im := by simpa [UpperHalfPlane.upperHalfPlaneSet] using hf ht

/-- `z₁'` sends `Ioc 0 1` into ℍ. -/
public lemma z₁'_mapsto : MapsTo z₁' (Ioc 0 1) ℍ₀ := fun _ ht => by
  simpa [UpperHalfPlane.upperHalfPlaneSet, z₁', IccExtend_of_mem, mem_Icc_of_Ioc ht, z₁] using ht.1
/-- For `t ∈ Ioc 0 1`, `(z₁' t).im` is positive. -/
public lemma im_z₁'_pos {t : ℝ} (ht : t ∈ Ioc 0 1) : 0 < (z₁' t).im :=
  im_pos_of_mapsto z₁'_mapsto ht
/-- `z₂'` sends `Icc 0 1` into ℍ. -/
public lemma z₂'_mapsto : MapsTo z₂' (Icc 0 1) ℍ₀ := fun _ ht => by
  simp [UpperHalfPlane.upperHalfPlaneSet, z₂', IccExtend_of_mem zero_le_one z₂ ht, z₂]
/-- For `t ∈ Icc 0 1`, `(z₂' t).im` is positive. -/
public lemma im_z₂'_pos {t : ℝ} (ht : t ∈ Icc 0 1) : 0 < (z₂' t).im :=
  im_pos_of_mapsto z₂'_mapsto ht
/-- `z₃'` sends `Ioc 0 1` into ℍ. -/
public lemma z₃'_mapsto : MapsTo z₃' (Ioc 0 1) ℍ₀ := fun _ ht => by
  simpa [UpperHalfPlane.upperHalfPlaneSet, z₃', IccExtend_of_mem, mem_Icc_of_Ioc ht, z₃] using ht.1
/-- For `t ∈ Ioc 0 1`, `(z₃' t).im` is positive. -/
public lemma im_z₃'_pos {t : ℝ} (ht : t ∈ Ioc 0 1) : 0 < (z₃' t).im :=
  im_pos_of_mapsto z₃'_mapsto ht
/-- `z₄'` sends `Icc 0 1` into ℍ. -/
public lemma z₄'_mapsto : MapsTo z₄' (Icc 0 1) ℍ₀ := fun _ ht => by
  simp [UpperHalfPlane.upperHalfPlaneSet, z₄', IccExtend_of_mem zero_le_one z₄ ht, z₄]
/-- For `t ∈ Icc 0 1`, `(z₄' t).im` is positive. -/
public lemma im_z₄'_pos {t : ℝ} (ht : t ∈ Icc 0 1) : 0 < (z₄' t).im :=
  im_pos_of_mapsto z₄'_mapsto ht
/-- `z₅'` sends `Ioc 0 1` into ℍ. -/
public lemma z₅'_mapsto : MapsTo z₅' (Ioc 0 1) ℍ₀ := fun _ ht => by
  simpa [UpperHalfPlane.upperHalfPlaneSet, z₅', IccExtend_of_mem, mem_Icc_of_Ioc ht, z₅] using ht.1
/-- For `t ∈ Ioc 0 1`, `(z₅' t).im` is positive. -/
public lemma im_z₅'_pos {t : ℝ} (ht : t ∈ Ioc 0 1) : 0 < (z₅' t).im :=
  im_pos_of_mapsto z₅'_mapsto ht
/-- `z₆'` sends `Ici 1` into ℍ. -/
public lemma z₆'_mapsto : MapsTo z₆' (Ici 1) ℍ₀ := fun _ ht => by
  simpa [UpperHalfPlane.upperHalfPlaneSet, z₆', IciExtend_of_mem, ht, z₆] using one_pos.trans_le ht

end UpperHalfPlane

/-- `z₁' = z₁` on `Icc 0 1`. -/
public lemma z₁'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₁' t = -1 + I * t := by
  rw [z₁', IccExtend_of_mem zero_le_one z₁ ht, z₁]
/-- `z₂' = z₂` on `Icc 0 1`. -/
public lemma z₂'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₂' t = -1 + t + I := by
  rw [z₂', IccExtend_of_mem zero_le_one z₂ ht, z₂]
/-- `z₃' = z₃` on `Icc 0 1`. -/
public lemma z₃'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₃' t = 1 + I * t := by
  rw [z₃', IccExtend_of_mem zero_le_one z₃ ht, z₃]
/-- `z₄' = z₄` on `Icc 0 1`. -/
public lemma z₄'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₄' t = 1 - t + I := by
  rw [z₄', IccExtend_of_mem zero_le_one z₄ ht, z₄]
/-- `z₅' = z₅` on `Icc 0 1`. -/
public lemma z₅'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₅' t = I * t := by
  rw [z₅', IccExtend_of_mem zero_le_one z₅ ht, z₅]
/-- `z₆' = z₆` on `Ici 1`. -/
public lemma z₆'_eq_of_mem {t : ℝ} (ht : t ∈ Ici 1) : z₆' t = I * t := by
  rw [z₆', IciExtend_of_mem z₆ ht, z₆]

/-! ### Continuity of `z₁'`--`z₅'` -/

/-- The extension `z₁' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₁' : Continuous z₁' :=
  Continuous.Icc_extend' (f := z₁) <| by unfold z₁; fun_prop

/-- The extension `z₂' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₂' : Continuous z₂' :=
  Continuous.Icc_extend' (f := z₂) <| by unfold z₂; fun_prop

/-- The extension `z₃' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₃' : Continuous z₃' :=
  Continuous.Icc_extend' (f := z₃) <| by unfold z₃; fun_prop

/-- The extension `z₄' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₄' : Continuous z₄' :=
  Continuous.Icc_extend' (f := z₄) <| by unfold z₄; fun_prop

/-- The extension `z₅' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₅' : Continuous z₅' :=
  Continuous.Icc_extend' (f := z₅) <| by unfold z₅; fun_prop

end MagicFunction.Parametrisations
