module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# Slash Actions

Auxiliary lemmas about slash actions of the modular group.
-/

@[expose] public section

-- Maybe this belongs in NumberTheory/ModularForms/SlashActions.lean, next to ModularForm.mul_slash

local notation "GL(" n ", " R ")" "⁺" => @Matrix.GLPos (Fin n) R (instDecidableEqFin n)
  (Fin.fintype n) Real.linearOrderedCommRing

open ModularForm MatrixGroups UpperHalfPlane Complex

/- Looks like the way to fix the errors is to replace each GL(n, ℝ)⁺ with
  `@Matrix.GLPos (Fin 2) ℝ (instDecidableEqFin 2) (Fin.fintype 2) Real.linearOrderedCommRing :
  Subgroup (GL (Fin 2) ℝ)`... but it's just so ugly!
-/

/-- Slash action under -I₂ as a GL(n, ℝ)⁺ matrix. See `ModularForm.slash_neg_one'` for the SL(2, ℤ)
version. -/
theorem ModularForm.slash_neg_one {k : ℤ} (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-1 : (GL (Fin 2) ℝ)) =
    f ∣[k] (1 : (GL (Fin 2) ℝ)) := by
  simp [slash_def, denom, hk.neg_one_zpow, Matrix.det_neg, σ]

/-- Slash action under -I₂ as a SL(2, ℤ) matrix. See `ModularForm.slash_neg_one` for the GL(n, ℝ)⁺
version. -/
theorem ModularForm.slash_neg_one' {k : ℤ} (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-1 : SL(2, ℤ)) = f ∣[k] (1 : SL(2, ℤ)) := by
  simp [SL_slash_def, denom, hk.neg_one_zpow]

/-- See `ModularForm.slash_neg'` for the version where `g` is a SL(2, ℤ) matrix. -/
theorem ModularForm.slash_neg {k : ℤ} (g : GL (Fin 2) ℝ) (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-g) = f ∣[k] g := by
  rw [← neg_one_mul, SlashAction.slash_mul, slash_neg_one f hk, SlashAction.slash_one]

/-- See `ModularForm.slash_neg` for the version where `g` is a GL(n, ℝ)⁺ matrix. -/
theorem ModularForm.slash_neg' {k : ℤ} (g : SL(2, ℤ)) (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-g) = f ∣[k] g := by
  rw [SL_slash, ← slash_neg _ _ hk]
  congr
  aesop

-- See mathlib PR https://github.com/leanprover-community/mathlib4/pull/44356
/-- `SlashAction.add_slash` for a difference. -/
@[simp]
theorem SlashAction.sub_slash {β G α : Type*} [Monoid G] [AddGroup α] [SlashAction β G α] (k : β)
    (g : G) (a b : α) : (a - b) ∣[k] g = a ∣[k] g - b ∣[k] g := by
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, sub_eq_add_neg]

theorem zpow_slash (n k : ℤ) (A : GL (Fin 2) ℝ) (f : ℍ → ℂ) :
    (f ^ n) ∣[n * k] A = |(A.det : ℝ)| ^ (n - 1) • (f ∣[k] A) ^ n := by
  ext1 τ
  have hd : ((|A.det| : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr <| abs_ne_zero.mpr <| NeZero.ne _
  simp only [slash_apply, Pi.pow_apply, Pi.smul_apply, real_smul, ofReal_zpow, map_zpow₀, mul_zpow,
    ← zpow_mul, mul_comm]
  rw [show n * k - 1 = n - 1 + (k - 1) * n by ring, zpow_add₀ hd]
  ring_nf

theorem pow_slash (n : ℕ) (k : ℤ) (A : GL (Fin 2) ℝ) (f : ℍ → ℂ) :
    (f ^ n) ∣[n * k] A = |(A.det : ℝ)| ^ (n - 1 : ℤ) • (f ∣[k] A) ^ n := by
  simpa using zpow_slash n k A f

theorem inv_slash (k : ℤ) (A : GL (Fin 2) ℝ) (f : ℍ → ℂ) :
    (f⁻¹) ∣[k] A = |(A.det : ℝ)| ^ (-2 : ℤ) • (f ∣[-k] A)⁻¹ := by
  simpa using zpow_slash (-1) (-k) A f

theorem zpow_slash_SL2 (n k : ℤ) (A : SL(2, ℤ)) (f : ℍ → ℂ) :
    (f ^ n) ∣[n * k] A = (f ∣[k] A) ^ n := by
  simp [SL_slash, zpow_slash]

theorem pow_slash_SL2 (n : ℕ) (k : ℤ) (A : SL(2, ℤ)) (f : ℍ → ℂ) :
    (f ^ n) ∣[n * k] A = (f ∣[k] A) ^ n := by
  simp [SL_slash, pow_slash]

@[simp]
theorem inv_slash_SL2 (k : ℤ) (A : SL(2, ℤ)) (f : ℍ → ℂ) :
    (f⁻¹) ∣[k] A = (f ∣[-k] A)⁻¹ := by
  simp [SL_slash, inv_slash]
