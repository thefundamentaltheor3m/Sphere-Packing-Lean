module
public import SpherePacking.MagicFunction.b.Psi
public import SpherePacking.MagicFunction.IntegralParametrisations

import SpherePacking.ModularForms.SlashActionAuxil

/-!
# Relations between `ψT'` and `ψI'` along parametrisations

This file records modular-translation identities relating `ψT'` and `ψI'` along the
parametrisations `z₁'`, `z₃'`, and `z₅'`.

## Main statements
* `ψT'_z₁'_eq_ψI'_z₅'`
* `ψT'_z₃'_eq_ψI'_z₅'`
-/

namespace MagicFunction.b.PsiParamRelations

open scoped UpperHalfPlane

open Complex Real Set UpperHalfPlane

open MagicFunction.Parametrisations

private lemma ψT'_eq_ψI'_of_ψT_eq_ψI {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    (h : ψT ⟨z, hz⟩ = ψI ⟨w, hw⟩) :
    ψT' z = ψI' w := by
  simpa [ψT', ψI', hz, hw] using h

private lemma ψT_eq_ψI_vadd_one (z : ℍ) :
    ψT z = ψI ((1 : ℝ) +ᵥ z) := by
  simp [ψT, modular_slash_T_apply]

private lemma ψT_vadd_one_eq_ψI (z : ℍ) :
    ψT ((1 : ℝ) +ᵥ z) = ψI z := by
  simpa [modular_slash_T_apply] using congrFun ψT_slash_T z

private lemma vadd_one_z₁'_eq_z₅' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hz1 : 0 < (z₁' t).im) (hz5 : 0 < (z₅' t).im) :
    ((1 : ℝ) +ᵥ (⟨z₁' t, hz1⟩ : ℍ) : ℍ) = ⟨z₅' t, hz5⟩ := by
  ext1
  simp [z₁'_eq_of_mem (t := t) ht, z₅'_eq_of_mem (t := t) ht, add_left_comm, add_comm]

private lemma vadd_one_z₅'_eq_z₃' (t : ℝ)
    (hz5 : 0 < (z₅' t).im) (hz3 : 0 < (z₃' t).im) :
    ((1 : ℝ) +ᵥ (⟨z₅' t, hz5⟩ : ℍ) : ℍ) = ⟨z₃' t, hz3⟩ := by
  rfl

/-- Compatibility of the primed extensions `ψT'` and `ψI'` along the parametrisations `z₁'`/`z₅'`.

The primes indicate the extensions to `ℂ` defined by `ψT'`/`ψI'` and the parametrisations
`z₁'`/`z₅'`. -/
public lemma ψT'_z₁'_eq_ψI'_z₅' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ψT' (z₁' t) = ψI' (z₅' t) := by
  by_cases ht0 : t = 0
  · subst ht0
    simp [ψT', ψI', z₁'_eq_of_mem (t := 0) (by simp), z₅'_eq_of_mem (t := 0) (by simp)]
  · have htIoc : t ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
    have hz1 : 0 < (z₁' t).im := im_z₁'_pos (t := t) htIoc
    have hz5 : 0 < (z₅' t).im := im_z₅'_pos (t := t) htIoc
    refine ψT'_eq_ψI'_of_ψT_eq_ψI hz1 hz5 ?_
    simpa [vadd_one_z₁'_eq_z₅' (t := t) ht hz1 hz5] using
      ψT_eq_ψI_vadd_one ⟨z₁' t, hz1⟩

/-- Compatibility of the primed extensions `ψT'` and `ψI'` along the parametrisations `z₃'`/`z₅'`.

The primes indicate the extensions to `ℂ` defined by `ψT'`/`ψI'` and the parametrisations
`z₃'`/`z₅'`. -/
public lemma ψT'_z₃'_eq_ψI'_z₅' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ψT' (z₃' t) = ψI' (z₅' t) := by
  by_cases ht0 : t = 0
  · subst ht0
    simp [ψT', ψI', z₃'_eq_of_mem (t := 0) (by simp), z₅'_eq_of_mem (t := 0) (by simp)]
  · have htIoc : t ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
    have hz3 : 0 < (z₃' t).im := im_z₃'_pos (t := t) htIoc
    have hz5 : 0 < (z₅' t).im := im_z₅'_pos (t := t) htIoc
    refine ψT'_eq_ψI'_of_ψT_eq_ψI hz3 hz5 ?_
    simpa [vadd_one_z₅'_eq_z₃' (t := t) hz5 hz3] using
      ψT_vadd_one_eq_ψI ⟨z₅' t, hz5⟩

end MagicFunction.b.PsiParamRelations
