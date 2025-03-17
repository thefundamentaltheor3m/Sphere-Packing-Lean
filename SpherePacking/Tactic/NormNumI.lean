/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yunzhou Xie
-/
import Mathlib.Data.Complex.Basic

open Lean Meta Elab Qq Tactic Complex
open ComplexConjugate

namespace Mathlib.Tactic.NormNumI

theorem split_I : I = ⟨0, 1⟩ := rfl

theorem split_zero : (0 : ℂ) = ⟨0, 0⟩ := rfl

theorem split_one : (1 : ℂ) = ⟨1, 0⟩ := rfl

theorem split_add {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ}
    (h₁ : z₁ = ⟨a₁, b₁⟩) (h₂ : z₂ = ⟨a₂, b₂⟩) :
    z₁ + z₂ = ⟨(a₁ + a₂), (b₁ + b₂)⟩ := by
  substs h₁ h₂
  rfl

theorem split_mul {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ} (h₁ : z₁ = ⟨a₁, b₁⟩) (h₂ : z₂ = ⟨a₂, b₂⟩) :
    z₁ * z₂ = ⟨(a₁ * a₂ - b₁ * b₂), (a₁ * b₂ + b₁ * a₂)⟩ :=
  Ring.mul_congr h₁ h₂ rfl

theorem split_inv {z : ℂ} {x y : ℝ} (h : z = ⟨x, y⟩) :
    z⁻¹ = ⟨x / (x * x + y * y), - y / (x * x + y * y)⟩ := by
  subst h
  rw [inv_def]
  exact Complex.ext (by simp [normSq_apply]; rfl) (by simp [normSq_apply, neg_div]; rfl)

theorem split_neg {z : ℂ} {a b : ℝ} (h : z = ⟨a, b⟩) :
    -z = ⟨-a, -b⟩ := by
  subst h
  rfl

theorem split_conj {w : ℂ} {a b : ℝ} (hw : w = ⟨a, b⟩):
    conj w = ⟨a, -b⟩ := by
  rw [hw]
  rfl

theorem split_num (n : ℕ) [n.AtLeastTwo]:
    OfNat.ofNat (α := ℂ) n = ⟨OfNat.ofNat n, 0⟩ := rfl

theorem split_scientific (m exp : ℕ) (x : Bool) :
    (OfScientific.ofScientific m x exp : ℂ) = ⟨(OfScientific.ofScientific m x exp : ℝ), 0⟩ :=
  rfl

theorem eq_eq {z : ℂ} {a b a' b' : ℝ} (pf : z = ⟨a, b⟩)
  (pf_a : a = a') (pf_b : b = b') :
  z = ⟨a', b'⟩ := by simp_all

theorem eq_of_eq_of_eq {a b c : ℂ} (ha : a = c) (hb : b = c) : a = b := by simp [ha, hb]

partial def parse (z : Q(ℂ)) :
    MetaM (Σ a b : Q(ℝ),  Q($z = ⟨$a, $b⟩)) := do
  match z with
  /- parse an addition: `z₁ + z₂` -/
  | ~q($z₁ + $z₂) =>
    let ⟨a₁, b₁, pf₁⟩ ← parse z₁
    let ⟨a₂, b₂, pf₂⟩ ← parse z₂
    pure ⟨q($a₁ + $a₂), q($b₁ + $b₂), q(split_add $pf₁ $pf₂)⟩
  /- parse a multiplication: `z₁ * z₂` -/
  | ~q($z₁ * $z₂) =>
    let ⟨a₁, b₁, pf₁⟩ ← parse z₁
    let ⟨a₂, b₂, pf₂⟩ ← parse z₂
    pure ⟨q($a₁ * $a₂ - $b₁ * $b₂), q($a₁ * $b₂ + $b₁ * $a₂), q(split_mul $pf₁ $pf₂)⟩
  /- parse an inversion: `z⁻¹` -/
  | ~q($z⁻¹) =>
    let ⟨x, y, pf⟩ ← parse z
    pure ⟨q($x / ($x * $x + $y * $y)), q(-$y / ($x * $x + $y * $y)), q(split_inv $pf)⟩
  /- parse `z₁/z₂` -/
  | ~q($z₁ / $z₂) => parse q($z₁ * $z₂⁻¹)
  /- parse `-z` -/
  | ~q(-$w) =>
    let ⟨a, b, pf⟩ ← parse w
    pure ⟨q(-$a), q(-$b), q(split_neg $pf)⟩
  /- parse a subtraction `z₁ - z₂` -/
  | ~q($z₁ - $z₂) => parse q($z₁ + -$z₂)
  /- parse conjugate `conj z` -/
  | ~q(conj $w) =>
    let ⟨a, b, pf⟩ ← parse w
    return ⟨q($a), q(-$b), q(split_conj $pf)⟩
  | ~q(@HPow.hPow ℂ ℕ ℂ instHPow $w $n) =>
    match n.nat? with
    | some 0 =>
      return ⟨q(1), q(0), (q(pow_zero $w) :)⟩
    | some (n + 1) => parse q($w ^ $n * $w)
    | none => throwError "exponent {n} not handled by norm_numI"
  /- parse `(I:ℂ)` -/
  | ~q(Complex.I) =>
    pure ⟨q(0), q(1), q(split_I)⟩
  /- anything else needs to be on the list of atoms -/
  | ~q(OfNat.ofNat $n (self := _)) =>
    let some n := n.rawNatLit? | throwError "{n} is not a natural number"
    if n == 0 then
      return ⟨q(0), q(0), (q(split_zero):)⟩
    else if n == 1 then
      return ⟨q(1), q(0), (q(split_one):)⟩
    else
      let _i : Q(Nat.AtLeastTwo $n) ← synthInstanceQ q(Nat.AtLeastTwo $n)
      return ⟨q(OfNat.ofNat $n), q(0), (q(split_num $n):)⟩
  | ~q(OfScientific.ofScientific $m $x $exp) =>
    return ⟨q(OfScientific.ofScientific $m $x $exp), q(0), q(split_scientific _ _ _)⟩
  /- parse a constructor type -/
  |~q(Complex.mk $a $b) =>
    pure ⟨a, b, q(rfl)⟩
  | _ => throwError "found the atom {z} which is not a numeral"

def normalize (z : Q(ℂ)) : MetaM (Σ a b : Q(ℝ), Q($z = ⟨$a, $b⟩)) := do
  let ⟨a, b, pf⟩ ← parse z
  let ra ← Mathlib.Meta.NormNum.derive (α := q(ℝ)) a
  let rb ← Mathlib.Meta.NormNum.derive (α := q(ℝ)) b
  let { expr := (a' : Q(ℝ)), proof? := (pf_a : Q($a = $a')) } ← ra.toSimpResult | unreachable!
  let { expr := (b' : Q(ℝ)), proof? := (pf_b : Q($b = $b')) } ← rb.toSimpResult | unreachable!
  return ⟨a', b', q(eq_eq $pf $pf_a $pf_b)⟩

elab "norm_numI" : conv => do
  let z ← Conv.getLhs
  unless (q(ℂ) == (← inferType z)) do throwError "{z} is not a complex number"
  have z : Q(ℂ) := z
  let ⟨a, b, pf⟩ ← normalize z
  Conv.applySimpResult { expr := q(Complex.mk $a $b), proof? := some pf }

def proveEq (g : MVarId) : MetaM Unit := do
  let tgt ← g.getType
  let some ⟨α, a, b⟩ := tgt.consumeMData.eq? | throwError "goal is not an equality"
  guard (← withReducibleAndInstances (isDefEq α q(ℂ))) <|> throwError "type of equality is not ℂ"
  let ⟨a₁, a₂, pf_a⟩ := ← normalize a
  let ⟨b₁, b₂, pf_b⟩ := ← normalize b
  guard (← withReducibleAndInstances (isDefEq a₁ b₁)) <|>
    throwError "Real-part disagreement: LHS normalizes to {a₁}, RHS normalizes to {b₁}"
  guard (← withReducibleAndInstances (isDefEq a₂ b₂)) <|>
    throwError "Imaginary-part disagreement: LHS normalizes to {a₂}, RHS normalizes to {b₂}"
  g.assign (← mkAppM ``eq_of_eq_of_eq #[pf_a, pf_b])

elab "norm_numI" : tactic => liftMetaFinishingTactic proveEq

end Mathlib.Tactic.NormNumI
