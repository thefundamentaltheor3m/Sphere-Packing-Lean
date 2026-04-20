module

public import SpherePacking.Basic.Domains.RightHalfPlane
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

import Mathlib.Tactic.FunProp

/-!
# Analytic continuation domain

This file defines the right-half-plane domain
`U = {u : ℂ | 0 < re u} \ {2}` used for analytic continuation in the integral representations for
Viazovska's magic function.

## Main definitions
* `MagicFunction.g.CohnElkies.IntegralReps.ACDomain`

## Main statements
* `MagicFunction.g.CohnElkies.IntegralReps.ACDomain_isPreconnected`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped Topology
open Real Complex
open SpherePacking

/-- The analytic continuation domain `U = {u : ℂ | 0 < re u} \ {2}`. -/
@[expose] public def ACDomain : Set ℂ := rightHalfPlane \ {2}

/-- The analytic continuation domain `ACDomain` is preconnected. -/
public lemma ACDomain_isPreconnected : IsPreconnected ACDomain := by
  -- We use a homeomorphism `ℂ ≃ₜ {u : ℂ // 0 < u.re}` to reduce to connectedness of the
  -- complement of a singleton in `ℂ`.
  let z2 : {u : ℂ // 0 < u.re} := ⟨(2 : ℂ), by simp⟩
  let h₃ : (Set.Ioi (0 : ℝ) × ℝ) ≃ₜ {u : ℂ // 0 < u.re} :=
    { toEquiv :=
        { toFun := fun p =>
            ⟨(p.1 : ℝ) + p.2 * Complex.I, by
              have hp : (0 : ℝ) < (p.1 : ℝ) := p.1.2
              simpa using hp⟩
          invFun := fun z => (⟨z.1.re, z.2⟩, z.1.im)
          left_inv := by
            rintro ⟨x, y⟩
            ext <;> simp
          right_inv := by
            rintro ⟨z, hz⟩
            apply Subtype.ext
            simp [Complex.re_add_im] }
      continuous_toFun := by
        refine
            (show Continuous (fun p : Set.Ioi (0 : ℝ) × ℝ => (p.1 : ℝ) + p.2 * Complex.I) by
              fun_prop).subtype_mk fun p => by
            have hp : (0 : ℝ) < (p.1 : ℝ) := p.1.2
            simpa using hp
      continuous_invFun := by
        fun_prop }
  let h : ℂ ≃ₜ {u : ℂ // 0 < u.re} :=
    (Complex.equivRealProdCLM.toHomeomorph.trans
          ((Real.expOrderIso.toHomeomorph).prodCongr (Homeomorph.refl ℝ))).trans h₃
  have hpre : IsPreconnected ({z2}ᶜ : Set {u : ℂ // 0 < u.re}) := by
    have hconn : IsConnected ({h.symm z2}ᶜ : Set ℂ) :=
      isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) (h.symm z2)
    have himage :
        h '' ({h.symm z2}ᶜ : Set ℂ) = ({z2}ᶜ : Set {u : ℂ // 0 < u.re}) := by
      ext z
      refine ⟨?_, fun hz => ⟨h.symm z, by simpa, by simp⟩⟩
      rintro ⟨x, hx, rfl⟩
      have hx' : x ≠ h.symm z2 := by simpa using hx
      simpa using fun hz => hx' (by simpa using congrArg h.symm hz)
    simpa [himage] using hconn.isPreconnected.image h h.continuous.continuousOn
  have hval :
      ((Subtype.val : {u : ℂ // 0 < u.re} → ℂ) '' ({z2}ᶜ :
          Set {u : ℂ // 0 < u.re})) = ACDomain := by
    ext u
    refine ⟨?_, ?_⟩
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ≠ z2 := by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
      exact ⟨z.2, by simpa using fun hEq => hz' (Subtype.ext hEq)⟩
    · rintro hu
      have hu_re : 0 < u.re := by simpa [rightHalfPlane] using hu.1
      refine ⟨⟨u, hu_re⟩, ?_, rfl⟩
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using fun hEq =>
        (by simpa using hu.2 : u ≠ (2 : ℂ)) (congrArg Subtype.val hEq)
  simpa [hval] using
    hpre.image (Subtype.val : {u : ℂ // 0 < u.re} → ℂ) continuous_subtype_val.continuousOn

end MagicFunction.g.CohnElkies.IntegralReps
