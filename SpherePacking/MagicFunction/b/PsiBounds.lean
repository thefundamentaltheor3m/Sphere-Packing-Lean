module
public import SpherePacking.ModularForms.JacobiTheta
public import SpherePacking.MagicFunction.IntegralParametrisations
public import SpherePacking.ModularForms.Delta
public import SpherePacking.ModularForms.ResToImagAxis
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.ModularFormsHelpers

import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Topology.Order.Compact

/-!
# Definitions and bounds for the `ψ`-functions

Defines `ψI`, `ψT`, `ψS` (and their `ℂ`-extensions `ψI'`, `ψT'`, `ψS'`) in terms of Jacobi
theta functions, used in the definition of the `-1`-eigenfunction `b`. Also packages the six
contour integrals `J₁'`-`J₆'` and the radial profile `b'`.

Provides the analytic bounds on `ψS` needed to prove the Schwartz decay of the integrals
defining Viazovska's magic function `b`, including `‖H₂(it)‖ ≤ C * exp(-π t)` for `t ≥ 1` and
`‖ψS(it)‖ ≤ C * exp(-π t)` for `t ≥ 1` (originally in `Schwartz.PsiExpBounds.PsiSDecay`).

The `ψ` definitions and modular relations were originally in `MagicFunction.b.Psi`.
-/

open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

noncomputable section defs

/-- Auxiliary function used to define the `ψ`-functions via slash actions. -/
@[expose] public def h : ℍ → ℂ := 128 • (H₃_MF + H₄_MF) / (H₂_MF ^ 2)

/-- The function `ψI`, defined from `h` and its slash transform by `S * T` (weight `-2`). -/
@[expose] public def ψI : ℍ → ℂ := h - h ∣[-2] (S * T)

/-- The function `ψT`, obtained from `ψI` by the slash action of `T` (weight `-2`). -/
@[expose] public def ψT : ℍ → ℂ := ψI ∣[-2] T

/-- The function `ψS`, obtained from `ψI` by the slash action of `S` (weight `-2`). -/
@[expose] public def ψS : ℍ → ℂ := ψI ∣[-2] S

/-- Extend `ψI` to `ℂ`, defined as `0` outside the upper half-plane. -/
@[expose] public def ψI' (z : ℂ) : ℂ := if hz : 0 < z.im then ψI ⟨z, hz⟩ else 0

/-- Extend `ψS` to `ℂ`, defined as `0` outside the upper half-plane. -/
@[expose] public def ψS' (z : ℂ) : ℂ := if hz : 0 < z.im then ψS ⟨z, hz⟩ else 0

/-- Extend `ψT` to `ℂ`, defined as `0` outside the upper half-plane. -/
@[expose] public def ψT' (z : ℂ) : ℂ := if hz : 0 < z.im then ψT ⟨z, hz⟩ else 0
end defs

section eq

section aux

lemma z_plus_one_nonzero (z : ℍ) : (z + 1 : ℂ) ≠ 0 := fun hz =>
  lt_irrefl (0 : ℝ) (by simpa [hz] using (by simpa using z.2 : 0 < (z + 1 : ℂ).im))

/-- Slash-action formula for `S` in weight `-2`. -/
public lemma slashS' (z : ℍ) (F : ℍ → ℂ) :
    (F ∣[(-2 : ℤ)] (S)) (z) = F (S • z) * (z : ℂ) ^ (2 : ℕ) := by
  simp [SL_slash_apply, S, denom, zpow_two, pow_two]

lemma slashS'' (z : ℍ) (F : ℍ → ℂ) :
    F (S • z) = (F ∣[(2 : ℤ)] (S)) (z) * (z : ℂ) ^ (2 : ℕ) := by
  simp [SL_slash_apply, S, denom, zpow_two, pow_two, UpperHalfPlane.ne_zero z, mul_assoc]

lemma slashT (z : ℍ) (F : ℍ → ℂ) : ((F) ∣[(2 : ℤ)] (T)) (z) = (F) (T • z) := by
  simp [SL_slash_apply, T, denom]

lemma slashT' (z : ℍ) (F : ℍ → ℂ) : ((F) ∣[(-2 : ℤ)] (T)) (z) = (F) (T • z) := by
  simp [SL_slash_apply, T, denom]

/-- Slash-action formula for `S * T` in weight `-2`. -/
public lemma slashST' (z : ℍ) (F : ℍ → ℂ) :
    ((F) ∣[(-2 : ℤ)] (S * T)) (z) = F ((S * T) • z ) * (z + 1 : ℂ) ^ (2 : ℕ) := by
  simp [SL_slash_apply, ModularGroup.S_mul_T, denom, sl_moeb, zpow_two, pow_two]

lemma slashST'' (z : ℍ) (F : ℍ → ℂ) :
    F ((S * T) • z) = (F ∣[(2 : ℤ)] (S * T)) (z) * (z + 1 : ℂ) ^ 2 := by
  simp [SL_slash_apply, ModularGroup.S_mul_T, denom, zpow_two, pow_two, z_plus_one_nonzero z,
    mul_assoc]

private lemma H₂_MF_coe : (H₂_MF : ℍ → ℂ) = H₂ := rfl
private lemma H₃_MF_coe : (H₃_MF : ℍ → ℂ) = H₃ := rfl
private lemma H₄_MF_coe : (H₄_MF : ℍ → ℂ) = H₄ := rfl
end aux

/-- Explicit formula for `ψI` in terms of `H₂`, `H₃`, `H₄` (Lemma 7.16 in the blueprint). -/
public lemma ψI_eq :
    ψI = 128 • ((H₃_MF + H₄_MF) / (H₂_MF ^ 2) + (H₄_MF - H₂_MF) / H₃_MF ^ 2) := by
  rw [ψI, h]
  conv_rhs => rw [smul_add]
  conv_lhs => rw [sub_eq_add_neg, smul_div_assoc 128 (⇑H₃_MF + ⇑H₄_MF) (⇑H₂_MF ^ 2)]
  simp only [Int.reduceNeg, add_right_inj]
  ext z
  have hz1 : (z + 1 : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (z_plus_one_nonzero z)
  rw [Pi.neg_apply, slashST',
    show (128 • ((⇑H₃_MF + ⇑H₄_MF) / (⇑H₂_MF ^ 2))) ((S * T) • z) =
        128 • ((H₃_MF ((S * T) • z) + H₄_MF ((S * T) • z)) / ((H₂_MF ((S * T) • z)) ^ 2)) from by
      simp only [nsmul_eq_mul, Nat.cast_ofNat, sl_moeb, map_mul, Pi.div_apply, Pi.add_apply,
        Pi.mul_apply, Pi.ofNat_apply, Pi.pow_apply],
    slashST'' z ⇑H₂_MF, slashST'' z ⇑H₃_MF, slashST'' z ⇑H₄_MF,
    H₂_MF_coe, H₃_MF_coe, H₄_MF_coe, slash_mul, slash_mul, slash_mul, H₂_S_action, H₃_S_action,
    H₄_S_action, SlashAction.neg_slash, SlashAction.neg_slash, SlashAction.neg_slash, H₂_T_action,
    H₃_T_action, H₄_T_action, neg_neg, ← add_mul]
  nth_rw 2 [pow_two]
  rw [← mul_assoc, mul_div_mul_comm, div_self hz1, mul_one]
  nth_rw 2 [mul_comm]
  rw [← mul_assoc, ← pow_two, ← div_div, smul_mul_assoc, div_mul_comm, div_self hz1, one_mul,
    ← neg_nsmul, neg_div', add_comm ]
  simp only [Pi.neg_apply, neg_add_rev, neg_neg, even_two, Even.neg_pow, nsmul_eq_mul,
    Nat.cast_ofNat, Pi.smul_apply, Pi.div_apply, Pi.sub_apply, Pi.pow_apply, mul_eq_mul_left_iff,
    OfNat.ofNat_ne_zero, or_false]
  rw [sub_eq_add_neg]

/-- Explicit formula for `ψT` in terms of the Jacobi theta functions `H₂`, `H₃`, and `H₄`. -/
public lemma ψT_eq :
    ψT = 128 * ((H₃_MF + H₄_MF) / (H₂_MF ^ 2) + (H₂_MF + H₃_MF) / H₄_MF ^ 2) := by
  rw [ψT, ψI_eq]
  ext z
  rw [slashT']
  simp only [Pi.smul_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply, Pi.sub_apply, smul_add,
    nsmul_eq_mul, Nat.cast_ofNat, Pi.mul_apply, Pi.ofNat_apply]
  rw [← slashT z ⇑H₂_MF, ← slashT z ⇑H₃_MF, ← slashT z ⇑H₄_MF,
    H₂_MF_coe, H₃_MF_coe, H₄_MF_coe, H₂_T_action, H₃_T_action, H₄_T_action]
  simp [← mul_add, add_comm (H₄ z) (H₃ z), add_comm (H₃ z) (H₂ z)]

-- there was a typo in the blueprint, thats why we first formalized the following version of ψS_eq
-- here is the description that can be found in Maryna's paper.
/-- A first explicit formula for `ψS` in terms of `H₂`, `H₃`, and `H₄`. -/
public lemma ψS_eq' :
    ψS = 128 * ((H₄_MF - H₂_MF) / (H₃_MF ^ 2) - (H₂_MF + H₃_MF) / H₄_MF ^ 2) := by
  rw [ψS, ψI_eq]
  ext z
  rw [slashS']
  simp only [Pi.smul_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply,
    Pi.sub_apply, smul_add, nsmul_eq_mul, Nat.cast_ofNat, Pi.mul_apply, Pi.ofNat_apply]
  rw [slashS'' z ⇑H₂_MF, slashS'' z ⇑H₃_MF, slashS'' z ⇑H₄_MF,
    H₂_MF_coe, H₃_MF_coe, H₄_MF_coe, H₂_S_action, H₃_S_action, H₄_S_action]
  simp only [Pi.neg_apply]
  field_simp [show (z : ℂ) ≠ 0 from ne_zero z]; ring

/-- A rearranged explicit formula for `ψS`, derived from `ψS_eq'`. -/
public lemma ψS_eq :
    ψS = 128 * (- ((H₂_MF + H₃_MF) / H₄_MF ^ 2) - (H₂_MF - H₄_MF) / (H₃_MF ^ 2)) := by
  rw [ψS_eq', sub_eq_add_neg (H₄_MF : ℍ → ℂ), add_comm (H₄_MF : ℍ → ℂ) _, ← sub_neg_eq_add,
    ← neg_sub', neg_div, ← neg_add', add_comm, neg_add']

/-- Decomposition of `ψI` as the sum `ψT + ψS`. -/
public lemma ψI_eq_add_ψT_ψS : ψI = ψT + ψS := by
  ext z; simp [ψI_eq, ψT_eq, ψS_eq, sub_eq_add_neg]; ring

end eq

section rels

/-- Modular relation: `ψT ∣[-2] T = ψI`. -/
public lemma ψT_slash_T : ψT ∣[-2] T = ψI := by
  ext z
  rw [ψT_eq, ψI_eq, slashT']
  simp only [Pi.mul_apply, Pi.ofNat_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply, Pi.smul_apply,
    Pi.sub_apply, smul_add, nsmul_eq_mul, Nat.cast_ofNat]
  rw [← slashT z ⇑H₂_MF, ← slashT z ⇑H₃_MF, ← slashT z ⇑H₄_MF,
    H₂_MF_coe, H₃_MF_coe, H₄_MF_coe, H₂_T_action, H₃_T_action, H₄_T_action]
  simp [← mul_add, add_comm (H₄ z) (H₃ z), add_comm  (- (H₂ z)) (H₄ z), sub_eq_add_neg]

/-- Modular relation: `ψS ∣[-2] S = ψI`. -/
public lemma ψS_slash_S : ψS ∣[-2] S = ψI := by
  rw [ψS, ← slash_mul, ModularGroup.modular_S_sq]; norm_num

/-- Modular relation: `ψS ∣[-2] (S * T) = ψT`. -/
public lemma ψS_slash_ST : ψS ∣[-2] (S * T) = ψT := by
  rw [ψS, ψT, ← slash_mul, ← mul_assoc, ModularGroup.modular_S_sq]
  simp [show Even (-2 : ℤ) from ⟨-1, by ring⟩]

-- The `-` sign on `ψS` is missing in Maryna's paper. Since we bound integrals in absolute value
-- the difference is irrelevant; it makes the `J`s look more similar to the `I`s.
/-- Modular relation: `ψS ∣[-2] T = -ψS`. -/
public lemma ψS_slash_T : ψS ∣[-2] T = -ψS := by
  ext z
  rw [ψS_eq', slashT']
  simp only [Pi.mul_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply, Pi.sub_apply]
  rw [← slashT z ⇑H₂_MF, ← slashT z ⇑H₃_MF, ← slashT z ⇑H₄_MF,
    H₂_MF_coe, H₃_MF_coe, H₄_MF_coe, H₂_T_action, H₃_T_action, H₄_T_action]
  simp [sub_eq_add_neg, add_comm]; ring

/-- Modular relation: `ψT ∣[-2] S = -ψT`. -/
public lemma ψT_slash_S : ψT ∣[-2] S = -ψT := by
  ext z
  rw [ψT_eq, slashS']
  simp only [Pi.mul_apply, Pi.ofNat_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply, Pi.neg_apply]
  rw [slashS'' z ⇑H₂_MF, slashS'' z ⇑H₃_MF, slashS'' z ⇑H₄_MF,
    H₂_MF_coe, H₃_MF_coe, H₄_MF_coe, H₂_S_action, H₃_S_action, H₄_S_action]
  simp only [Pi.neg_apply, neg_mul, even_two, Even.neg_pow]
  field_simp [show (z : ℂ) ≠ 0 from ne_zero z]; ring

/-- Modular relation: `ψS ∣[-2] (S * T * S) = -ψT`. -/
public lemma ψS_slash_STS : ψS ∣[-2] (S * T * S) = -ψT := by
  ext z
  rw [slash_mul, slash_mul, ψS_slash_S]
  simpa [ψT] using congrArg (fun f => f z) (ψT_slash_S : ψT ∣[-2] S = -ψT)

end rels

/-! ## Relations between `ψT'` and `ψI'` along parametrisations -/

namespace MagicFunction.b.PsiParamRelations

open Set MagicFunction.Parametrisations

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
    simpa [show ((1 : ℝ) +ᵥ (⟨z₁' t, hz1⟩ : ℍ) : ℍ) = ⟨z₅' t, hz5⟩ from by
      ext1; simp [z₁'_eq_of_mem (t := t) ht, z₅'_eq_of_mem (t := t) ht,
        add_left_comm, add_comm]] using (show ψT (⟨z₁' t, hz1⟩ : ℍ) = ψI ((1 : ℝ) +ᵥ ⟨z₁' t, hz1⟩) by
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

/-! ## Defining integrals for `b`

The six contour integrals `J₁'`-`J₆'` used to build the magic function `b`. The prime indicates
the radial profile as a function of the real parameter `x = ‖v‖^2`; the unprimed versions
`J₁`-`J₆` are the induced functions on `EuclideanSpace ℝ (Fin 8)`. -/

noncomputable section bDefs

local notation "V" => EuclideanSpace ℝ (Fin 8)

open Set Complex Real MagicFunction.Parametrisations

namespace MagicFunction.b.RealIntegrals

/-- The six auxiliary contour integrals `J₁'`-`J₆'` defining the radial profile of `b`. -/
@[expose] public def J₁' (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, I * ψT' (z₁' t) * cexp (π * I * x * (z₁' t))
@[expose] public def J₂' (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, ψT' (z₂' t) * cexp (π * I * x * (z₂' t))
@[expose] public def J₃' (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, I * ψT' (z₃' t) * cexp (π * I * x * (z₃' t))
@[expose] public def J₄' (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, -1 * ψT' (z₄' t) * cexp (π * I * x * (z₄' t))
@[expose] public def J₅' (x : ℝ) : ℂ :=
  -2 * ∫ t in (0 : ℝ)..1, I * ψI' (z₅' t) * cexp (π * I * x * (z₅' t))
@[expose] public def J₆' (x : ℝ) : ℂ :=
  -2 * ∫ t in Ici (1 : ℝ), I * ψS' (z₆' t) * cexp (π * I * x * (z₆' t))

/-- The radial profile defining the magic function `b` as a function of `x = ‖v‖^2`. -/
@[expose] public def b' (x : ℝ) := J₁' x + J₂' x + J₃' x + J₄' x + J₅' x + J₆' x

end MagicFunction.b.RealIntegrals
open MagicFunction.b.RealIntegrals

namespace MagicFunction.b.RadialFunctions

/-- The functions on `V` induced from the radial profiles `J₁'`-`J₆'` by `x = ‖v‖^2`. -/
@[expose] public def J₁ (x : V) : ℂ := J₁' (‖x‖ ^ 2)
@[expose] public def J₂ (x : V) : ℂ := J₂' (‖x‖ ^ 2)
@[expose] public def J₃ (x : V) : ℂ := J₃' (‖x‖ ^ 2)
@[expose] public def J₄ (x : V) : ℂ := J₄' (‖x‖ ^ 2)
@[expose] public def J₅ (x : V) : ℂ := J₅' (‖x‖ ^ 2)
@[expose] public def J₆ (x : V) : ℂ := J₆' (‖x‖ ^ 2)

/-- The magic function `b` on `V`, obtained from the radial profile `b'` by `x = ‖v‖^2`. -/
@[expose] public def b (x : V) : ℂ := b' (‖x‖ ^ 2)

end MagicFunction.b.RadialFunctions

end bDefs

namespace MagicFunction.b.PsiBounds

open scoped Topology UpperHalfPlane Manifold
open Complex Real Filter Topology UpperHalfPlane Set

noncomputable section

/-! ## Algebraic factorization of `ψS` -/

/-- Factorization of `ψS` in terms of the Jacobi theta functions `H₂`, `H₃`, and `H₄`. -/
public lemma ψS_apply_eq_factor (z : ℍ) :
    ψS z =
      (-128 : ℂ) *
        (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
          ((H₃ z) ^ 2 * (H₄ z) ^ 2) := by
  have hJ : H₃ z = H₂ z + H₄ z := by
    simpa using congrArg (fun f : ℍ → ℂ => f z) jacobi_identity.symm
  refine (eq_div_iff (mul_ne_zero (pow_ne_zero 2 (H₃_ne_zero z))
    (pow_ne_zero 2 (H₄_ne_zero z)))).2 ?_
  rw [show ψS z = 128 * (((H₄ z - H₂ z) / (H₃ z) ^ 2) - ((H₂ z + H₃ z) / (H₄ z) ^ 2)) by
    simpa using congrArg (fun f : ℍ → ℂ => f z) ψS_eq']
  field_simp [H₃_ne_zero z, H₄_ne_zero z]
  simp [hJ]; ring_nf

end

/-! ## Continuity and bounds for `ψS` on the imaginary axis -/

/-- Continuity of the modular function `ψS`. -/
public lemma continuous_ψS : Continuous ψS := by
  have hH2 := mdifferentiable_H₂.continuous; have hH3 := mdifferentiable_H₃.continuous
  have hH4 := mdifferentiable_H₄.continuous
  simpa [ψS_eq', mul_assoc] using continuous_const.mul
    (((hH4.sub hH2).div (hH3.pow 2) (fun z => pow_ne_zero 2 (H₃_ne_zero z))).sub
      ((hH2.add hH3).div (hH4.pow 2) (fun z => pow_ne_zero 2 (H₄_ne_zero z))))

/-- Continuity of the modular function `ψT`. -/
public lemma continuous_ψT : Continuous ψT := by
  have hH2 := mdifferentiable_H₂.continuous; have hH3 := mdifferentiable_H₃.continuous
  have hH4 := mdifferentiable_H₄.continuous
  simpa [ψT_eq, mul_assoc] using continuous_const.mul
    (((hH3.add hH4).div (hH2.pow 2) (fun z => pow_ne_zero 2 (H₂_ne_zero z))).add
      ((hH2.add hH3).div (hH4.pow 2) (fun z => pow_ne_zero 2 (H₄_ne_zero z))))

/-- Continuity of the modular function `ψI`. -/
public lemma continuous_ψI : Continuous ψI := by
  have hH2 := mdifferentiable_H₂.continuous; have hH3 := mdifferentiable_H₃.continuous
  have hH4 := mdifferentiable_H₄.continuous
  rw [show ψI = fun z : ℍ =>
        (128 : ℂ) * ((H₃ z + H₄ z) / (H₂ z) ^ 2) +
          (128 : ℂ) * ((H₄ z - H₂ z) / (H₃ z) ^ 2) from funext fun z => by
    simpa [nsmul_eq_mul, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
      mul_comm] using congrArg (fun f : ℍ → ℂ => f z) ψI_eq]
  simpa [mul_assoc] using (continuous_const.mul
    ((hH3.add hH4).div (hH2.pow 2) (fun z => pow_ne_zero 2 (H₂_ne_zero z)))).add
    (continuous_const.mul
      ((hH4.sub hH2).div (hH3.pow 2) (fun z => pow_ne_zero 2 (H₃_ne_zero z))))

/-- `ψS` tends to `0` at `Im z → ∞`. -/
public theorem tendsto_ψS_atImInfty : Tendsto ψS atImInfty (𝓝 (0 : ℂ)) := by
  have hH2 := H₂_tendsto_atImInfty; have hH4 := H₄_tendsto_atImInfty
  have hpoly :
      Tendsto (fun z : ℍ => 2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)
        atImInfty (𝓝 (5 : ℂ)) := by
    have h1 : Tendsto (fun z : ℍ => 2 * (H₂ z) ^ 2) atImInfty (𝓝 (0 : ℂ)) := by
      simpa using tendsto_const_nhds.mul (hH2.pow 2)
    have h2 : Tendsto (fun z : ℍ => 5 * (H₂ z) * (H₄ z)) atImInfty (𝓝 (0 : ℂ)) := by
      simpa [mul_assoc] using tendsto_const_nhds.mul (hH2.mul hH4)
    have h3 : Tendsto (fun z : ℍ => 5 * (H₄ z) ^ 2) atImInfty (𝓝 (5 : ℂ)) := by
      simpa using tendsto_const_nhds.mul (hH4.pow 2)
    simpa [add_assoc] using (h1.add h2).add h3
  rw [show ψS = fun z : ℍ =>
        -((128 : ℂ) *
            (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2))) /
          ((H₃ z) ^ 2 * (H₄ z) ^ 2) from funext fun z => by simp [ψS_apply_eq_factor]]
  simpa [Pi.div_apply] using ((tendsto_const_nhds.mul (hH2.mul hpoly)).neg.div
    (by simpa using (H₃_tendsto_atImInfty.pow 2).mul (hH4.pow 2)) (by norm_num : (1 : ℂ) ≠ 0))

/-- Uniform bound for `‖ψS.resToImagAxis t‖` on `Ici (1 : ℝ)`. -/
public lemma exists_bound_norm_ψS_resToImagAxis_Ici_one :
    ∃ M, ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ M := by
  rcases eventually_atTop.1 <|
    ((tendsto_zero_iff_norm_tendsto_zero).1 (by
      simpa using Function.tendsto_resToImagAxis_atImInfty (F := ψS) (l := (0 : ℂ))
        tendsto_ψS_atImInfty : Tendsto (fun t : ℝ => ψS.resToImagAxis t) atTop (𝓝 (0 : ℂ)))
      ).eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)) with ⟨A, hA⟩
  obtain ⟨C, hC⟩ := SpherePacking.ForMathlib.exists_upper_bound_on_Icc (a := 1) (b := max A 1)
    (hab := le_max_right _ _)
    (hg := continuous_norm.comp_continuousOn <|
      (Function.continuousOn_resToImagAxis_Ioi_of (F := ψS) continuous_ψS).mono fun _ ht =>
        lt_of_lt_of_le (by norm_num) ht.1)
  refine ⟨max C 1, fun t ht => ?_⟩
  by_cases htB : t ≤ max A 1
  · exact (hC t ⟨ht, htB⟩).trans (le_max_left _ _)
  · exact (hA t (le_trans (le_max_left _ _) (le_of_not_ge htB))).le.trans (le_max_right _ _)

end MagicFunction.b.PsiBounds

namespace SpherePacking.ForMathlib

open Filter Real

/-- Uniform bound for `x ^ k * exp (-b * x)` on `0 ≤ x` when `0 < b`. -/
public lemma exists_bound_pow_mul_exp_neg_mul (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → x ^ k * Real.exp (-b * x) ≤ C := by
  let f : ℝ → ℝ := fun x ↦ x ^ k * Real.exp (-b * x)
  rcases (eventually_atTop.1 <| ((by
    simpa [f, Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (k : ℝ)) (b := b) hb)) :
      Tendsto f atTop (nhds (0 : ℝ))).eventually (Iio_mem_nhds zero_lt_one)) with ⟨A, hA⟩
  rcases (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (max A 0))).exists_isMaxOn
      (Set.nonempty_Icc.2 (le_max_right A 0)) (by fun_prop : Continuous f).continuousOn
    with ⟨x0, hx0, hxmax⟩
  refine ⟨max (f x0) 1, fun x hx => ?_⟩
  by_cases hxA : x ≤ max A 0
  · exact (hxmax ⟨hx, hxA⟩).trans (le_max_left _ _)
  · exact (le_of_lt (hA x ((le_max_left _ _).trans (le_of_not_ge hxA)))).trans (le_max_right _ _)

/-- Uniform bound for `x ^ k * exp (-b * sqrt x)` on `0 ≤ x`. -/
public lemma exists_bound_pow_mul_exp_neg_mul_sqrt (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → x ^ k * Real.exp (-b * Real.sqrt x) ≤ C :=
  let ⟨C, hC⟩ := exists_bound_pow_mul_exp_neg_mul (k := 2 * k) (b := b) hb
  ⟨C, fun x hx => by
    simpa [pow_mul, Real.sq_sqrt hx] using hC (Real.sqrt x) (Real.sqrt_nonneg _)⟩

/-- AM-GM style inequality for the exponential weight: for `0 ≤ x`, `0 < t`,
`exp (-π / t) * exp (-π * x * t) ≤ exp (-2 * π * sqrt x)`. -/
public lemma exp_neg_pi_div_mul_exp_neg_pi_mul_le (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    Real.exp (-Real.pi / t) * Real.exp (-Real.pi * x * t) ≤
      Real.exp (-2 * Real.pi * Real.sqrt x) := by
  have hAMGM : 2 * Real.sqrt (x * t) * (Real.sqrt t)⁻¹ ≤ x * t + 1 / t := by
    have h := two_mul_le_add_sq (Real.sqrt (x * t)) ((Real.sqrt t)⁻¹)
    have hinv : ((Real.sqrt t)⁻¹ : ℝ) ^ 2 = (1 / t : ℝ) := by simp [one_div, Real.sq_sqrt ht.le]
    simpa [Real.sq_sqrt (mul_nonneg hx ht.le), hinv, mul_assoc, mul_left_comm, mul_comm] using h
  have hmul_sqrt : Real.sqrt (x * t) * (Real.sqrt t)⁻¹ = Real.sqrt x := by
    have hsqrt : Real.sqrt (x * t) = Real.sqrt x * Real.sqrt t := by
      simpa [mul_comm] using Real.sqrt_mul hx t
    grind
  refine (Real.exp_add _ _).symm.trans_le (Real.exp_le_exp.2 ?_)
  rw [show (-Real.pi / t) + (-Real.pi * x * t) = -(Real.pi * (x * t + 1 / t)) from by ring,
    show -2 * Real.pi * Real.sqrt x = -(Real.pi * (2 * Real.sqrt x)) from by ring]
  exact neg_le_neg (mul_le_mul_of_nonneg_left
    (by simpa [hmul_sqrt, mul_assoc] using hAMGM : 2 * Real.sqrt x ≤ x * t + 1 / t) Real.pi_pos.le)

end SpherePacking.ForMathlib

namespace MagicFunction

open scoped Interval

open Complex Real Set
open MagicFunction.Parametrisations UpperHalfPlane

/-- A generic continuity lemma for a modular rewrite on `Ioc 0 1`. -/
public lemma continuousOn_ψT'_Ioc_of (k : ℕ) (ψS : ℍ → ℂ) (ψT' : ℂ → ℂ) (z : ℝ → ℂ)
    (hψS : ContinuousOn ψS.resToImagAxis (Ici (1 : ℝ)))
    (hEq : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ψT' (z t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ k) :
    ContinuousOn (fun t : ℝ => ψT' (z t)) (Ioc (0 : ℝ) 1) := by
  have hpow : Continuous fun t : ℝ => ((Complex.I : ℂ) * (t : ℂ)) ^ k := by
    simpa using (continuous_const.mul Complex.continuous_ofReal).pow k
  have hcont_one_div : ContinuousOn (fun t : ℝ => (1 / t : ℝ)) (Ioc (0 : ℝ) 1) := by
    simpa [one_div] using
      (continuousOn_inv₀ : ContinuousOn (fun t : ℝ => (t : ℝ)⁻¹) ({0}ᶜ)).mono
        (fun t ht => by simp [ne_of_gt ht.1])
  exact ((hψS.comp hcont_one_div (fun t ht => one_le_one_div ht.1 ht.2)).mul
    hpow.continuousOn).congr hEq

/-- Continuity of the modular rewrite along `t ↦ z₁' t` on `(0, 1)`. -/
public lemma continuousOn_ψT'_z₁'_of (k : ℕ) (ψS : ℍ → ℂ) (ψT' : ℂ → ℂ)
    (hψS : ContinuousOn ψS.resToImagAxis (Ici (1 : ℝ)))
    (hEq : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ψT' (z₁' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ k) :
    ContinuousOn (fun t : ℝ => ψT' (z₁' t)) (Ioo (0 : ℝ) 1) :=
  (continuousOn_ψT'_Ioc_of (k := k) (ψS := ψS) (ψT' := ψT') (z := z₁') hψS hEq).mono
    fun _ ht => ⟨ht.1, le_of_lt ht.2⟩

/-- A uniform bound for `‖ψT' (z₁' t)‖` on `(0, 1)`, given a bound for `ψS` on `Ici 1`. -/
public lemma exists_bound_norm_ψT'_z₁'_of (k : ℕ) (ψS : ℍ → ℂ) (ψT' : ℂ → ℂ)
    (hBound : ∃ M : ℝ, ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ M)
    (hEq : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ψT' (z₁' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ k) :
    ∃ M : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ‖ψT' (z₁' t)‖ ≤ M := by
  obtain ⟨M, hM⟩ := hBound
  refine ⟨M, fun t ht => ?_⟩
  have hψS : ‖ψS.resToImagAxis (1 / t)‖ ≤ M := hM (1 / t) (one_le_one_div ht.1 ht.2.le)
  calc
    ‖ψT' (z₁' t)‖ = ‖ψS.resToImagAxis (1 / t)‖ * ‖((Complex.I : ℂ) * (t : ℂ)) ^ k‖ := by
      simp [hEq t ⟨ht.1, ht.2.le⟩]
    _ = ‖ψS.resToImagAxis (1 / t)‖ * t ^ k := by
      simp [norm_pow, Complex.norm_real, abs_of_nonneg ht.1.le]
    _ ≤ M * t ^ k := mul_le_mul_of_nonneg_right hψS (pow_nonneg ht.1.le k)
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left
        (by simpa using pow_le_one₀ (n := k) ht.1.le ht.2.le) ((norm_nonneg _).trans hψS)
    _ = M := mul_one M

/-- Pointwise bound for a modular rewrite on `Ioc 0 1`. -/
public lemma norm_modular_rewrite_Ioc_bound (k : ℕ) (ψS : ℍ → ℂ) (ψZ : ℂ → ℂ) (z : ℝ → ℂ)
    (hEq : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ψZ (z t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ k)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) {B : ℝ} (hB : ‖ψS.resToImagAxis (1 / t)‖ ≤ B) :
    ‖ψZ (z t)‖ ≤ B * t ^ k := by
  calc
    ‖ψZ (z t)‖ = ‖ψS.resToImagAxis (1 / t)‖ * ‖((Complex.I : ℂ) * (t : ℂ)) ^ k‖ := by
      simp [hEq t ht]
    _ = ‖ψS.resToImagAxis (1 / t)‖ * t ^ k := by
      simp [norm_pow, Complex.norm_real, abs_of_nonneg ht.1.le]
    _ ≤ B * t ^ k := mul_le_mul_of_nonneg_right hB (pow_nonneg ht.1.le k)

/-- Pointwise bound for a modular rewrite on `Ioc 0 1` with exponential decay. -/
public lemma norm_modular_rewrite_Ioc_exp_bound (k : ℕ) (Cψ : ℝ) (ψS : ℍ → ℂ) (ψZ : ℂ → ℂ)
    (z : ℝ → ℂ)
    (hCψ : ∀ y : ℝ, 1 ≤ y → ‖ψS.resToImagAxis y‖ ≤ Cψ * Real.exp (-Real.pi * y))
    (hEq : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ψZ (z t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ k)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖ψZ (z t)‖ ≤ Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ k :=
  norm_modular_rewrite_Ioc_bound k ψS ψZ z hEq ht (hCψ (1 / t) (one_le_one_div ht.1 ht.2))

end MagicFunction

namespace MagicFunction.b.PsiBounds.PsiExpBounds

noncomputable section

open scoped Topology UpperHalfPlane
open Complex Real Filter Topology UpperHalfPlane Set HurwitzKernelBounds

lemma norm_Θ₂_resToImagAxis_le (t : ℝ) (ht : 0 < t) :
    ‖Θ₂.resToImagAxis t‖ ≤
      (2 * rexp (-π * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - rexp (-π * t)) := by
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hτ : (τ : ℂ) = (Complex.I : ℂ) * t := rfl
  have hΘ (n : ℤ) : ‖Θ₂_term n τ‖ = f_int 0 (1 / 2 : ℝ) t n := by
    have hnorm_pref : ‖cexp (π * (Complex.I : ℂ) * (τ : ℂ) / 4)‖ = rexp (-π * (t / 4)) := by
      simp [Complex.norm_exp, hτ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have hnorm_core :
        ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ =
          rexp (-(π * (n : ℝ) ^ 2 * t) - 2 * π * (n : ℝ) * (t / 2)) := by
      rw [show ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ =
        rexp (-π * (n : ℝ) ^ 2 * t - 2 * π * (n : ℝ) * (t / 2)) by
          simpa [hτ] using norm_jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)]
      ring_nf
    simp [HurwitzKernelBounds.f_int, pow_zero, one_mul,
      show ‖Θ₂_term n τ‖ = rexp (-π * (((n : ℝ) + (1 / 2)) ^ 2) * t) from
        calc ‖Θ₂_term n τ‖ =
                ‖cexp (π * (Complex.I : ℂ) * (τ : ℂ) / 4)‖ *
                  ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ := by
                  simp [Θ₂_term_as_jacobiTheta₂_term, hτ, mul_assoc]
          _ = rexp (-π * (((n : ℝ) + (1 / 2)) ^ 2) * t) := by
                  rw [hnorm_pref, hnorm_core, ← Real.exp_add]; congr 1; ring]
  have hsumm : Summable (fun n : ℤ => ‖Θ₂_term n τ‖) :=
    (summable_f_int 0 (1 / 2 : ℝ) ht).congr (fun n => by simpa using (hΘ n).symm)
  have hbd_nat' :
      F_nat 0 (1 / 2 : ℝ) t ≤ rexp (-π * ((1 / 2 : ℝ) ^ 2) * t) / (1 - rexp (-π * t)) := by
    have hnonneg' : 0 ≤ F_nat 0 (2⁻¹ : ℝ) t :=
      tsum_nonneg (fun n : ℕ => by simp only [HurwitzKernelBounds.f_nat, pow_zero]; positivity)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg'] using
      (F_nat_zero_le (a := (1 / 2 : ℝ)) (ha := by norm_num) ht)
  calc ‖Θ₂.resToImagAxis t‖
      ≤ ∑' n : ℤ, ‖Θ₂_term n τ‖ := by
        simpa [ResToImagAxis, Θ₂, τ, ht] using (norm_tsum_le_tsum_norm hsumm)
    _ = F_int 0 ((1 / 2 : ℝ) : UnitAddCircle) t := by
        simpa [HurwitzKernelBounds.F_int] using tsum_congr fun n => by simpa using hΘ n
    _ = F_nat 0 (1 / 2 : ℝ) t + F_nat 0 (1 / 2 : ℝ) t := by
        simpa [show (1 : ℝ) - (2⁻¹ : ℝ) = (2⁻¹ : ℝ) by norm_num] using
          F_int_eq_of_mem_Icc 0 (a := (1 / 2 : ℝ)) ⟨by norm_num, by norm_num⟩ ht
    _ ≤ _ := by rw [show (2 * rexp (-π * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - rexp (-π * t)) =
                    rexp (-π * ((1 / 2 : ℝ) ^ 2) * t) / (1 - rexp (-π * t)) +
                    rexp (-π * ((1 / 2 : ℝ) ^ 2) * t) / (1 - rexp (-π * t)) from by ring]; gcongr

/-- Exponential decay bound for `H₂` on the positive imaginary axis. -/
public lemma exists_bound_norm_H₂_resToImagAxis_exp_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖H₂.resToImagAxis t‖ ≤ C * rexp (-π * t) := by
  let Cθ : ℝ := (2 : ℝ) / (1 - rexp (-π))
  refine ⟨Cθ ^ 4, fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hΘ2 : ‖Θ₂.resToImagAxis t‖ ≤ Cθ * rexp (-π * (t / 4)) := calc
    ‖Θ₂.resToImagAxis t‖ ≤
        (2 * rexp (-π * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - rexp (-π * t)) :=
          norm_Θ₂_resToImagAxis_le t ht0
    _ = (2 * rexp (-π * (t / 4))) / (1 - rexp (-π * t)) := by
          rw [show -π * ((1 / 2 : ℝ) ^ 2) * t = -π * (t / 4) by ring]
    _ ≤ (2 * rexp (-π * (t / 4))) / (1 - rexp (-π : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity)
            (sub_pos.2 (Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])))
            (sub_le_sub_left (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, ht])) 1)
    _ = Cθ * rexp (-π * (t / 4)) := by
          simp [Cθ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  calc
    ‖H₂.resToImagAxis t‖ = ‖Θ₂.resToImagAxis t‖ ^ 4 := by
      simp [H₂, Function.resToImagAxis, ResToImagAxis, ht0, norm_pow]
    _ ≤ (Cθ * rexp (-π * (t / 4))) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hΘ2 4
    _ = (Cθ ^ 4) * rexp (-π * t) := by
      rw [mul_pow, ← Real.exp_nat_mul, show (4 : ℕ) * (-π * (t / 4)) = -π * t by push_cast; ring]

/-- Exponential decay bound for `ψS.resToImagAxis` on `Ici (1 : ℝ)`. -/
public theorem exists_bound_norm_ψS_resToImagAxis_exp_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ C * rexp (-π * t) := by
  obtain ⟨CH2, hH2⟩ := exists_bound_norm_H₂_resToImagAxis_exp_Ici_one
  let CH2' : ℝ := max CH2 0
  have hCH2' : 0 ≤ CH2' := le_max_right _ _
  have hH2' : ∀ t : ℝ, 1 ≤ t → ‖H₂.resToImagAxis t‖ ≤ CH2' * rexp (-π * t) := fun t ht =>
    le_mul_of_le_mul_of_nonneg_right (hH2 t ht) (le_max_left _ _) (by positivity)
  -- `H₃` and `H₄` converge to `1` along the imaginary axis, so their norms are bounded above
  -- and below away from `0` on `t ≥ 1` by compactness on an initial segment.
  have hEv (H : ℍ → ℂ) (hH : Tendsto (fun z : ℍ => H z) atImInfty (𝓝 (1 : ℂ))) :
      ∀ᶠ t in atTop, ‖H.resToImagAxis t - (1 : ℂ)‖ ≤ (1 / 2 : ℝ) :=
    (tendsto_sub_nhds_zero_iff.mpr (by simpa using
        (Function.tendsto_resToImagAxis_atImInfty (F := H) (l := (1 : ℂ)) hH))).norm.eventually
      (Iic_mem_nhds (by norm_num))
  obtain ⟨T0, hT0⟩ :=
    eventually_atTop.1 ((hEv H₃ H₃_tendsto_atImInfty).and (hEv H₄ H₄_tendsto_atImInfty))
  let T : ℝ := max T0 1
  have hH_ne (H : ℍ → ℂ) (hne : ∀ z : ℍ, H z ≠ 0) :
      ∀ t : ℝ, 1 ≤ t → H.resToImagAxis t ≠ (0 : ℂ) := fun t ht ↦ by
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    simpa [Function.resToImagAxis, ResToImagAxis, ht0] using hne ⟨Complex.I * t, by simp [ht0]⟩
  let φ : Icc 1 T → ℍ := fun t ↦ ⟨(Complex.I : ℂ) * (t : ℝ), by
    have : (0 : ℝ) < (t : ℝ) := lt_of_lt_of_le (by norm_num) t.2.1; simp [this]⟩
  have hcont_norm_resToImagAxis (H : ℍ → ℂ) (hH : Continuous H) :
      ContinuousOn (fun t : ℝ => ‖ResToImagAxis H t‖) (Icc 1 T) :=
    (continuousOn_iff_continuous_restrict).2 <| by
      simpa [show ((Icc 1 T).restrict fun t : ℝ ↦ ‖ResToImagAxis H t‖) =
        fun t : Icc 1 T ↦ ‖H (φ t)‖ from funext fun t ↦ by
          have ht0 : (0 : ℝ) < (t : ℝ) := lt_of_lt_of_le (by norm_num) t.2.1
          simp [Set.restrict, ResToImagAxis, ht0, φ]] using
        (hH.comp (by fun_prop : Continuous φ)).norm
  have hcontH4 : ContinuousOn (fun t : ℝ => ‖ResToImagAxis H₄ t‖) (Icc 1 T) :=
    hcont_norm_resToImagAxis H₄ mdifferentiable_H₄.continuous
  obtain ⟨m3, hm3, hm3le⟩ := SpherePacking.ForMathlib.exists_lower_bound_pos_on_Icc
    (g := fun t ↦ ‖H₃.resToImagAxis t‖)
    (hg := by simpa [Function.resToImagAxis_eq_resToImagAxis] using
      hcont_norm_resToImagAxis H₃ mdifferentiable_H₃.continuous)
    (hpos := fun t ht => norm_pos_iff.2 (hH_ne H₃ H₃_ne_zero t ht.1))
  obtain ⟨m4, hm4, hm4le⟩ := SpherePacking.ForMathlib.exists_lower_bound_pos_on_Icc
    (g := fun t ↦ ‖H₄.resToImagAxis t‖)
    (hg := by simpa [Function.resToImagAxis_eq_resToImagAxis] using hcontH4)
    (hpos := fun t ht => norm_pos_iff.2 (hH_ne H₄ H₄_ne_zero t ht.1))
  obtain ⟨M4Icc, hM4Icc⟩ := SpherePacking.ForMathlib.exists_upper_bound_on_Icc
    (g := fun t : ℝ => ‖H₄.resToImagAxis t‖) (hab := le_max_right _ _)
    (hg := by simpa [Function.resToImagAxis_eq_resToImagAxis] using hcontH4)
  let M4 : ℝ := max M4Icc 2
  have half_le_norm {x : ℂ} (h : ‖x - (1 : ℂ)‖ ≤ (1 / 2 : ℝ)) : (1 / 2 : ℝ) ≤ ‖x‖ := by
    have := (sub_le_iff_le_add).2 (norm_le_norm_add_norm_sub' (1 : ℂ) x)
    simp [norm_sub_rev] at this; linarith
  have hH3_lower : ∀ t : ℝ, 1 ≤ t → min m3 (1 / 2 : ℝ) ≤ ‖H₃.resToImagAxis t‖ := fun t ht ↦ by
    by_cases htT : t ≤ T
    · exact inf_le_of_left_le (hm3le t ⟨ht, htT⟩)
    · exact inf_le_of_right_le
        (half_le_norm (hT0 t ((le_max_left _ _).trans (le_of_not_ge htT))).1)
  have hH4_lower : ∀ t : ℝ, 1 ≤ t → min m4 (1 / 2 : ℝ) ≤ ‖H₄.resToImagAxis t‖ := fun t ht ↦ by
    by_cases htT : t ≤ T
    · exact inf_le_of_left_le (hm4le t ⟨ht, htT⟩)
    · exact inf_le_of_right_le
        (half_le_norm (hT0 t ((le_max_left _ _).trans (le_of_not_ge htT))).2)
  have hH4_upper : ∀ t : ℝ, 1 ≤ t → ‖H₄.resToImagAxis t‖ ≤ M4 := fun t ht ↦ by
    by_cases htT : t ≤ T
    · exact (hM4Icc t ⟨ht, htT⟩).trans (le_max_left _ _)
    · have hx : ‖H₄.resToImagAxis t‖ ≤ ‖H₄.resToImagAxis t - (1 : ℂ)‖ + 1 := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, norm_one] using
          norm_add_le (H₄.resToImagAxis t - (1 : ℂ)) (1 : ℂ)
      have h32 : ‖H₄.resToImagAxis t‖ ≤ (3 / 2 : ℝ) := by
        linarith [(hT0 t ((le_max_left _ _).trans (le_of_not_ge htT))).2]
      exact h32.trans ((by norm_num : (3 / 2 : ℝ) ≤ 2).trans (le_max_right _ _))
  -- Bound the polynomial factor in `ψS_apply_eq_factor`.
  let P : ℝ := 2 * (CH2' ^ 2) + 5 * CH2' * M4 + 5 * (M4 ^ 2)
  let c3 : ℝ := min m3 (1 / 2 : ℝ); let c4 : ℝ := min m4 (1 / 2 : ℝ)
  have hc3 : 0 < c3 := lt_min hm3 (by norm_num); have hc4 : 0 < c4 := lt_min hm4 (by norm_num)
  refine ⟨(128 : ℝ) * P * ((c3 ^ 2 * c4 ^ 2)⁻¹) * CH2', fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hH2le : ‖H₂.resToImagAxis t‖ ≤ CH2' := (hH2' t ht).trans <| by
    simpa using mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht0.le])) hCH2'
  have hH4le : ‖H₄.resToImagAxis t‖ ≤ M4 := hH4_upper t ht
  have hpoly :
      ‖(2 : ℂ) * (H₂.resToImagAxis t) ^ 2
          + (5 : ℂ) * (H₂.resToImagAxis t) * (H₄.resToImagAxis t)
          + (5 : ℂ) * (H₄.resToImagAxis t) ^ 2‖ ≤ P := by
    have h1 : ‖(2 : ℂ) * (H₂.resToImagAxis t) ^ 2‖ ≤ 2 * (CH2' ^ 2) := by
      simpa [norm_mul, norm_pow] using mul_le_mul_of_nonneg_left
        (by simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hH2le 2) (norm_nonneg (2 : ℂ))
    have h2 : ‖(5 : ℂ) * (H₂.resToImagAxis t) * (H₄.resToImagAxis t)‖ ≤ 5 * CH2' * M4 := by
      simpa [norm_mul, mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left
        (by gcongr : ‖H₂.resToImagAxis t‖ * ‖H₄.resToImagAxis t‖ ≤ CH2' * M4) (norm_nonneg (5 : ℂ))
    have h3 : ‖(5 : ℂ) * (H₄.resToImagAxis t) ^ 2‖ ≤ 5 * (M4 ^ 2) := by
      simpa [norm_mul, norm_pow] using mul_le_mul_of_nonneg_left
        (by simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hH4le 2) (norm_nonneg (5 : ℂ))
    exact norm_add_le_of_le ((norm_add_le _ _).trans (by linarith [h1, h2])) h3
  -- Now bound `ψS.resToImagAxis t` using `ψS_apply_eq_factor`.
  let z : ℍ := ⟨Complex.I * t, by simp [ht0]⟩
  have hψS : ‖ψS.resToImagAxis t‖ = ‖(-128 : ℂ) *
      (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
        ((H₃ z) ^ 2 * (H₄ z) ^ 2)‖ := by
    change ‖ResToImagAxis ψS t‖ = _
    rw [show ResToImagAxis ψS t = ψS z by simp [ResToImagAxis, ht0, z],
      show ψS z = (-128 : ℂ) *
            (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
            ((H₃ z) ^ 2 * (H₄ z) ^ 2) by simpa using ψS_apply_eq_factor z]
  have hHz2 : ResToImagAxis H₂ t = H₂ z := by simp [ResToImagAxis, ht0, z]
  have hHz3 : ResToImagAxis H₃ t = H₃ z := by simp [ResToImagAxis, ht0, z]
  have hHz4 : ResToImagAxis H₄ t = H₄ z := by simp [ResToImagAxis, ht0, z]
  have hden_lower : c3 ≤ ‖H₃ z‖ := by
    simpa [hHz3] using (show c3 ≤ ‖ResToImagAxis H₃ t‖ from hH3_lower t ht)
  have hden_lower4 : c4 ≤ ‖H₄ z‖ := by
    simpa [hHz4] using (show c4 ≤ ‖ResToImagAxis H₄ t‖ from hH4_lower t ht)
  have hinv : ‖((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ ≤ (c3 ^ 2 * c4 ^ 2)⁻¹ := by
    have hpos : 0 < ‖(H₃ z) ^ 2 * (H₄ z) ^ 2‖ :=
      norm_pos_iff.2 (mul_ne_zero (pow_ne_zero 2 (H₃_ne_zero z)) (pow_ne_zero 2 (H₄_ne_zero z)))
    have hden : c3 ^ 2 * c4 ^ 2 ≤ ‖(H₃ z) ^ 2 * (H₄ z) ^ 2‖ := by
      simpa [norm_mul, norm_pow] using mul_le_mul (pow_le_pow_left₀ hc3.le hden_lower 2)
        (pow_le_pow_left₀ hc4.le hden_lower4 2) (by positivity) (by positivity)
    simpa [norm_inv] using (inv_le_inv₀ hpos (by positivity)).2 hden
  have hH2z : ‖H₂ z‖ ≤ CH2' * rexp (-π * t) := by
    simpa [hHz2, Function.resToImagAxis] using hH2' t ht
  have hpoly' :
      ‖2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2‖ ≤ P := by
    simpa [hHz2, hHz4, Function.resToImagAxis] using hpoly
  have hP0 : (0 : ℝ) ≤ P := (norm_nonneg _).trans hpoly'
  calc
    ‖ψS.resToImagAxis t‖ = ‖(-128 : ℂ) *
        (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
          ((H₃ z) ^ 2 * (H₄ z) ^ 2)‖ := hψS
    _ = ‖(-128 : ℂ) *
            (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) *
              ((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ := by
          simp [div_eq_mul_inv, mul_assoc]
    _ ≤ (128 : ℝ) * (‖H₂ z‖ * ‖2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2‖) *
          ‖((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ := by
          simp [mul_assoc]
    _ ≤ (128 : ℝ) * (‖H₂ z‖ * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ := by
          have h2 : (‖H₂ z‖ * ‖2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2‖) *
                ‖((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ ≤ (‖H₂ z‖ * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ :=
            mul_le_mul (mul_le_mul_of_nonneg_left hpoly' (norm_nonneg _)) hinv (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) hP0)
          grind only
    _ ≤ (128 : ℝ) * ((CH2' * rexp (-π * t)) * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ := by
          have h2 : (‖H₂ z‖ * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ ≤
              ((CH2' * rexp (-π * t)) * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hH2z hP0) (by positivity)
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 128)
    _ = ((128 : ℝ) * P * (c3 ^ 2 * c4 ^ 2)⁻¹ * CH2') * rexp (-π * t) := by ring

end

end MagicFunction.b.PsiBounds.PsiExpBounds
