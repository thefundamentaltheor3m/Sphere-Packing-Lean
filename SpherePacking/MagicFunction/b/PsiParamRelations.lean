module
public import SpherePacking.MagicFunction.b.Psi
public import SpherePacking.MagicFunction.IntegralParametrisations

import SpherePacking.ModularForms.SlashActionAuxil

/-!
# Relations between `ψT'` and `ψI'` along parametrisations

Modular-translation identities relating `ψT'` and `ψI'` along the parametrisations
`z₁'`, `z₃'`, and `z₅'`.

## Main statements
* `ψT'_z₁'_eq_ψI'_z₅'`
* `ψT'_z₃'_eq_ψI'_z₅'`
-/

namespace MagicFunction.b.PsiParamRelations

open scoped UpperHalfPlane
open Complex Real Set UpperHalfPlane MagicFunction.Parametrisations

private lemma ψT'_eq_ψI'_of_ψT_eq_ψI {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    (h : ψT ⟨z, hz⟩ = ψI ⟨w, hw⟩) : ψT' z = ψI' w := by
  simpa [ψT', ψI', hz, hw] using h

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
    have hvadd : ((1 : ℝ) +ᵥ (⟨z₁' t, hz1⟩ : ℍ) : ℍ) = ⟨z₅' t, hz5⟩ := by
      ext1; simp [z₁'_eq_of_mem (t := t) ht, z₅'_eq_of_mem (t := t) ht,
        add_left_comm, add_comm]
    simpa [hvadd] using (show ψT (⟨z₁' t, hz1⟩ : ℍ) = ψI ((1 : ℝ) +ᵥ ⟨z₁' t, hz1⟩) by
      simp [ψT, modular_slash_T_apply])

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
    simpa [show ((1 : ℝ) +ᵥ (⟨z₅' t, hz5⟩ : ℍ) : ℍ) = ⟨z₃' t, hz3⟩ from rfl] using
      (show ψT ((1 : ℝ) +ᵥ (⟨z₅' t, hz5⟩ : ℍ)) = ψI (⟨z₅' t, hz5⟩ : ℍ) by
        simpa [modular_slash_T_apply] using congrFun ψT_slash_T (⟨z₅' t, hz5⟩ : ℍ))

end MagicFunction.b.PsiParamRelations
