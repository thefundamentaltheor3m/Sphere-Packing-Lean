/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-! # A tactic for normalization of numeral expressions in ℂ -/

open Lean Meta Elab Qq Tactic Complex
open Mathlib.Meta.NormNum

namespace Mathlib.Tactic.NormNumI

theorem split_num (a : ℂ) : a = a + 0 * I := by simp

theorem split_I : I = 0 + 1 * I := by simp

theorem split_add {z₁ z₂ a₁ a₂ b₁ b₂ : ℂ} (h₁ : z₁ = a₁ + b₁ * I) (h₂ : z₂ = a₂ + b₂ * I) :
    z₁ + z₂ = (a₁ + a₂) + (b₁ + b₂) * I := by
  linear_combination h₁ + h₂

theorem split_mul {z₁ z₂ a₁ a₂ b₁ b₂ : ℂ} (h₁ : z₁ = a₁ + b₁ * I) (h₂ : z₂ = a₂ + b₂ * I) :
    z₁ * z₂ = (a₁ * a₂ - b₁ * b₂) + (a₁ * b₂ + b₁ * a₂) * I := by
  rw [h₁, h₂]
  linear_combination b₁ * b₂ * I_sq

theorem eq_of_eq_re_im {z a a' b b' : ℂ} (h : z = a + b * I) (ha : a = a') (hb : b = b') :
    z = a' + b' * I := by
  simp [h, ha, hb]

theorem eq_of_eq_of_eq {a b c : ℂ} (ha : a = c) (hb : b = c) : a = b := by simp [ha, hb]

/-- Record `norm_num` normalization of `(0:ℂ)`. -/
def rz : Result q((0:ℂ)) :=
  let inz : Q(IsNat (0:ℂ) 0) := q(IsNat.mk (Nat.cast_zero (R := ℂ)).symm)
  Result.isNat q(AddGroupWithOne.toAddMonoidWithOne) (mkRawNatLit 0) inz

/-- Record `norm_num` normalization of `(1:ℂ)`. -/
def ro : Result q((1:ℂ)) :=
  let ino : Q(IsNat (1:ℂ) 1) := q(IsNat.mk (Nat.cast_one (R := ℂ)).symm)
  Result.isNat q(AddGroupWithOne.toAddMonoidWithOne) (mkRawNatLit 1) ino

def evalReMul.core {x₁ x₂ y₁ y₂ : Q(ℂ)} (rx₁ : Result (u := 0) x₁)
    (rx₂ : Result (u := 0) x₂) (ry₁ : Result (u := 0) y₁) (ry₂ : Result (u := 0) y₂) :
    Option (Result (u := 0) q($x₁ * $x₂ - $y₁ * $y₂)) := do
  let i' : Q(Semiring ℂ) := q(Complex.instSemiring)
  let i'' : Q(Ring ℂ) := q(Complex.instRing)
  let A₁ ← evalMul.core q($x₁ * $x₂) q(HMul.hMul) _ _ i' rx₁ rx₂
  let A₂ ← evalMul.core q($y₁ * $y₂) q(HMul.hMul) _ _ i' ry₁ ry₂
  evalSub.core q($x₁ * $x₂ - $y₁ * $y₂) q(HSub.hSub) _ _ i'' A₁ A₂

def evalImMul.core {x₁ x₂ y₁ y₂ : Q(ℂ)} (rx₁ : Result (u := 0) x₁)
    (rx₂ : Result (u := 0) x₂) (ry₁ : Result (u := 0) y₁) (ry₂ : Result (u := 0) y₂) :
    Option (Result (u := 0) q($x₁ * $y₂ + $y₁ * $x₂)) := do
  let i' : Q(Semiring ℂ) := q(Complex.instSemiring)
  let A₁ ← evalMul.core q($x₁ * $y₂) q(HMul.hMul) _ _ i' rx₁ ry₂
  let A₂ ← evalMul.core q($y₁ * $x₂) q(HMul.hMul) _ _ i' ry₁ rx₂
  evalAdd.core q($x₁ * $y₂ + $y₁ * $x₂) q(HAdd.hAdd) _ _ A₁ A₂

def evalNormSq.core {x y : Q(ℂ)} (rx : Result (u := 0) x) (ry : Result (u := 0) y) :
    Option (Result (u := 0) q($x * $x + $y * $y)) := do
  let i' : Q(Semiring ℂ) := q(Complex.instSemiring)
  let X ← evalMul.core q($x * $x) q(HMul.hMul) _ _ i' rx rx
  let Y ← evalMul.core q($y * $y) q(HMul.hMul) _ _ i' ry ry
  evalAdd.core q($x * $x + $y * $y) q(HAdd.hAdd) q($x * $x) q($y * $y) X Y

-- #synth CharZero ℂ
def evalReInv.core {x y : Q(ℂ)} (rx : Result (u := 0) x) (ry : Result (u := 0) y) :
    Option (Result (u := 0) q($x / ($x * $x + $y * $y))) := do
  let i' : Q(Semiring ℂ) := q(Complex.instSemiring)
  let i'' : Q(DivisionRing ℂ) := q(Field.toDivisionRing)
  let i''' : Q(CharZero ℂ) := q(Complex.instCharZero)
  let D ← evalNormSq.core rx ry
  let D' ← evalInv.core q(($x * $x + $y * $y)⁻¹) _ D i'' (some i''')
  evalMul.core q($x / ($x * $x + $y * $y)) q(HMul.hMul) _ _ i' rx D'

def evalImInv.core {x y : Q(ℂ)} (rx : Result (u := 0) x) (ry : Result (u := 0) y) :
    Option (Result (u := 0) q($x / ($x * $x + $y * $y))) := do
  let i' : Q(Ring ℂ) := q(Complex.instRing)
  let i'' : Q(DivisionRing ℂ) := q(Field.toDivisionRing)
  let i''' : Q(CharZero ℂ) := q(Complex.instCharZero)
  let D ← evalNormSq.core rx ry
  let D' ← evalInv.core q(($x * $x + $y * $y)⁻¹) _ D i'' (some i''')
  let y' ← evalNeg.core q(-$y) q(Neg.neg) _ ry i'
  evalMul.core q(-$y / ($x * $x + $y * $y)) q(HMul.hMul) _ _ i' y' D'

partial def parse (z : Q(ℂ)) :
    MetaM (Σ a b : Q(ℂ), Result (u := 0) a × Result (u := 0) b × Q($z = $a + $b * Complex.I)) := do
  match z with
  /- parse an addition: `z₁ + z₂` -/
  | ~q($z₁ + $z₂) =>
    let ⟨a₁, b₁, r₁, s₁, pf₁⟩ ← parse z₁
    let ⟨a₂, b₂, r₂, s₂, pf₂⟩ ← parse z₂
    let some ra := evalAdd.core q($a₁ + $a₂) q(HAdd.hAdd) a₁ a₂ r₁ r₂ | throwError "zz"
    let some rb := evalAdd.core q($b₁ + $b₂) q(HAdd.hAdd) b₁ b₂ s₁ s₂ | throwError "zz"
    pure ⟨q($a₁ + $a₂), q($b₁ + $b₂), ra, rb, q(split_add $pf₁ $pf₂)⟩
  /- parse a multiplication: `z₁ * z₂` -/
  | ~q($z₁ * $z₂) =>
    let ⟨a₁, b₁, r₁, s₁, pf₁⟩ ← parse z₁
    let ⟨a₂, b₂, r₂, s₂, pf₂⟩ ← parse z₂
    let some A := evalReMul.core r₁ r₂ s₁ s₂ | throwError "zz"
    let some B := evalImMul.core r₁ r₂ s₁ s₂ | throwError "zz"
    pure ⟨q($a₁ * $a₂ - $b₁ * $b₂), q($a₁ * $b₂ + $b₁ * $a₂), A, B, q(split_mul $pf₁ $pf₂)⟩
  /- parse an inversion: `z⁻¹` -/
  | ~q($z⁻¹) =>
    let ⟨x, y, r, s, pf⟩ ← parse z
    let some A := evalReInv.core r s | throwError "zz"
    let some B := evalImInv.core r s | throwError "zz"
    pure ⟨q($x / ($x * $x + $y * $y)), q(-$y / ($x * $x + $y * $y)), A, B, q(sorry)⟩
  /- parse `(I:ℂ)` -/
  | ~q(Complex.I) =>
    pure ⟨q(0), q(1), rz, ro, q(split_I)⟩
  /- anything else needs to be on the list of atoms -/
  | _ =>
    let a ← Mathlib.Meta.NormNum.derive z
      <|> throwError "found the atom {z} which is not a rational numeral"
    pure ⟨z, q(0), a, rz, q(split_num $z)⟩

def normalize (z : Q(ℂ)) : MetaM (Σ a b : Q(ℂ), Q($z = $a + $b * Complex.I)) := do
  let ⟨_a, _b, ra, rb, pf⟩ ← parse z
  let { expr := (a' : Q(ℂ)), proof? := (pf_a : Q($_a = $a')) } ← ra.toSimpResult | unreachable!
  let { expr := (b' : Q(ℂ)), proof? := (pf_b : Q($_b = $b')) } ← rb.toSimpResult | unreachable!
  return ⟨a', b', q(eq_of_eq_re_im $pf $pf_a $pf_b)⟩

elab "norm_numI" : conv => do
  let z ← Conv.getLhs
  unless (q(ℂ) == (← inferType z)) do throwError "{z} is not a complex number"
  have z : Q(ℂ) := z
  let ⟨a, b, pf⟩ ← normalize z
  Conv.applySimpResult { expr := q($a + $b * Complex.I), proof? := some pf }

def proveEq (g : MVarId) : MetaM Unit := do
  let some ⟨α, a, b⟩ := (← g.getType).eq? | throwError "goal is not an equality"
  guard (← withReducibleAndInstances (isDefEq α q(ℂ))) <|> throwError "type of equality is not ℂ"
  let ⟨a₁, a₂, pf_a⟩ := ← normalize a
  let ⟨b₁, b₂, pf_b⟩ := ← normalize b
  guard (← withReducibleAndInstances (isDefEq a₁ b₁)) <|>
    throwError "Real-part disagreement: LHS normalizes to {a₁}, RHS normalizes to {b₁}"
  guard (← withReducibleAndInstances (isDefEq a₁ b₁)) <|>
    throwError "Imaginary-part disagreement: LHS normalizes to {a₂}, RHS normalizes to {b₂}"
  g.assign (← mkAppM ``eq_of_eq_of_eq #[pf_a, pf_b])

elab "norm_numI" : tactic => liftMetaFinishingTactic proveEq

end Mathlib.Tactic.NormNumI
