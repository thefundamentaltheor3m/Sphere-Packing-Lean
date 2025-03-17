/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

open Lean Meta Elab Qq Tactic Complex
open Mathlib.Meta.NormNum
open ComplexConjugate

namespace Mathlib.Tactic.NormNumI

theorem split_num (a : ℝ) : a = (⟨a, 0⟩ : ℂ) := rfl

theorem split_I : I = ⟨0, 1⟩ := rfl

theorem split_add {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ}
    (h₁ : z₁ = ⟨a₁, b₁⟩) (h₂ : z₂ = ⟨a₂, b₂⟩) :
    z₁ + z₂ = ⟨(a₁ + a₂), (b₁ + b₂)⟩ := by
  substs h₁ h₂
  rfl

theorem split_sub {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ} (h₁ : z₁ = ⟨a₁, b₁⟩) (h₂ : z₂ = ⟨a₂, b₂⟩) :
    z₁ - z₂ = ⟨(a₁ - a₂), (b₁ - b₂)⟩ :=
  Ring.sub_congr h₁ h₂ rfl

theorem split_mul {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ} (h₁ : z₁ = ⟨a₁, b₁⟩) (h₂ : z₂ = ⟨a₂, b₂⟩) :
    z₁ * z₂ = ⟨(a₁ * a₂ - b₁ * b₂), (a₁ * b₂ + b₁ * a₂)⟩ :=
  Ring.mul_congr h₁ h₂ rfl


theorem split_inv {z : ℂ} {x y : ℝ} (h : z = ⟨x, y⟩) :
    z⁻¹ = ⟨x / (x * x + y * y), - y / (x * x + y * y)⟩ := by
  subst h
  rw [inv_def]
  exact Complex.ext (by simp [normSq_apply]; rfl) (by simp [normSq_apply, neg_div]; rfl)

theorem eq_of_eq_re_im {z a a' b b' : ℂ} (h : z = a + b * I) (ha : a = a') (hb : b = b') :
    z = a' + b' * I := by
  simp [h, ha, hb]

theorem eq_of_eq_of_eq {a b c : ℂ} (ha : a = c) (hb : b = c) : a = b := by simp [ha, hb]

-- theorem

theorem extracted_1 (z : ℂ) (n : ℤ) (d : ℕ) (pf : IsRat z n d) :
    z = { re := @Rat.cast ℝ Real.instRatCast ((n : ℚ) / (d : ℚ)), im := 0 } := by
  simp
  obtain ⟨hd1, hd2⟩ := pf
  rw [hd2]
  apply Complex.ext
  · sorry
  · sorry

theorem extracted_2 (w : ℂ) :
  let z := (starRingEnd ℂ) w
  ∀ (a b : ℝ), w = { re := a, im := b} → z = { re := a, im := -b } := sorry

/-- Record `norm_num` normalization of `(0:ℂ)`. -/
def rz : Result q((0:ℝ)) :=
  let inz : Q(IsNat (0:ℝ) 0) := q(IsNat.mk (Nat.cast_zero (R := ℝ)).symm)
  Result.isNat q(AddGroupWithOne.toAddMonoidWithOne) (mkRawNatLit 0) inz

/-- Record `norm_num` normalization of `(1:ℂ)`. -/
def ro : Result q((1:ℝ)) :=
  let ino : Q(IsNat (1:ℝ) 1) := q(IsNat.mk (Nat.cast_one (R := _)).symm)
  Result.isNat q(AddGroupWithOne.toAddMonoidWithOne) (mkRawNatLit 1) ino

def evalReMul.core {x₁ x₂ y₁ y₂ : Q(ℝ)} (rx₁ : Result (u := 0) x₁)
    (rx₂ : Result (u := 0) x₂) (ry₁ : Result (u := 0) y₁) (ry₂ : Result (u := 0) y₂) :
    Option (Result (u := 0) q($x₁ * $x₂ - $y₁ * $y₂)) := do
  let i' : Q(Semiring ℝ) := q(Real.semiring)
  let i'' : Q(Ring ℝ) := q(Real.instRing)
  let A₁ ← evalMul.core q($x₁ * $x₂) q(HMul.hMul) _ _ i' rx₁ rx₂
  let A₂ ← evalMul.core q($y₁ * $y₂) q(HMul.hMul) _ _ i' ry₁ ry₂
  evalSub.core q($x₁ * $x₂ - $y₁ * $y₂) q(HSub.hSub) _ _ i'' A₁ A₂

def evalImMul.core {x₁ x₂ y₁ y₂ : Q(ℝ)} (rx₁ : Result (u := 0) x₁)
    (rx₂ : Result (u := 0) x₂) (ry₁ : Result (u := 0) y₁) (ry₂ : Result (u := 0) y₂) :
    Option (Result (u := 0) q($x₁ * $y₂ + $y₁ * $x₂)) := do
  let i' : Q(Semiring ℝ) := q(Real.semiring)
  let A₁ ← evalMul.core q($x₁ * $y₂) q(HMul.hMul) _ _ i' rx₁ ry₂
  let A₂ ← evalMul.core q($y₁ * $x₂) q(HMul.hMul) _ _ i' ry₁ rx₂
  evalAdd.core q($x₁ * $y₂ + $y₁ * $x₂) q(HAdd.hAdd) _ _ A₁ A₂

def evalNormSq.core {x y : Q(ℝ)} (rx : Result (u := 0) x) (ry : Result (u := 0) y) :
    Option (Result (u := 0) q($x * $x + $y * $y)) := do
  let i' : Q(Semiring ℝ) := q(Real.semiring)
  let X ← evalMul.core q($x * $x) q(HMul.hMul) _ _ i' rx rx
  let Y ← evalMul.core q($y * $y) q(HMul.hMul) _ _ i' ry ry
  evalAdd.core q($x * $x + $y * $y) q(HAdd.hAdd) q($x * $x) q($y * $y) X Y

#check pow_succ
def evalReInv.core {x y : Q(ℝ)} (rx : Result (u := 0) x) (ry : Result (u := 0) y) :
    Option (Result (u := 0) q($x / ($x * $x + $y * $y))) := do
  let i' : Q(Semiring ℝ) := q(Real.semiring)
  let i'' : Q(DivisionRing ℝ) := q(Field.toDivisionRing)
  let i''' : Q(CharZero ℝ) := q(StrictOrderedSemiring.toCharZero)
  let D ← evalNormSq.core rx ry
  let D' ← evalInv.core q(($x * $x + $y * $y)⁻¹) _ D i'' (some i''')
  evalMul.core q($x / ($x * $x + $y * $y)) q(HMul.hMul) _ _ i' rx D'

def evalImInv.core {x y : Q(ℝ)} (rx : Result (u := 0) x) (ry : Result (u := 0) y) :
    Option (Result (u := 0) q($x / ($x * $x + $y * $y))) := do
  let i' : Q(Ring ℝ) := q(Real.instRing)
  let i'' : Q(DivisionRing ℝ) := q(Field.toDivisionRing)
  let i''' : Q(CharZero ℝ) := q(StrictOrderedSemiring.toCharZero)
  let D ← evalNormSq.core rx ry
  let D' ← evalInv.core q(($x * $x + $y * $y)⁻¹) _ D i'' (some i''')
  let y' ← evalNeg.core q(-$y) q(Neg.neg) _ ry i'
  evalMul.core q(-$y / ($x * $x + $y * $y)) q(HMul.hMul) _ _ i' y' D'

partial def parse (z : Q(ℂ)) :
    MetaM (Σ a b : Q(ℝ), Result (u := 0) a × Result (u := 0) b × Q($z = ⟨$a, $b⟩)) := do
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
    pure ⟨q($x / ($x * $x + $y * $y)), q(-$y / ($x * $x + $y * $y)), A, B,
      q(show (_)⁻¹ = _ from split_inv $pf)⟩
  /- parse `z₁/z₂` -/
  | ~q($z₁ / $z₂) => parse q($z₁ * $z₂⁻¹)
  /- parse `-z` -/
  | ~q(-$w) =>
    let ⟨a, b, r, s, pf⟩ ← parse w
    let some A := evalNeg.core q(-$a) q(Neg.neg) a r q(Real.instRing) | throwError "zz"
    let some B := evalNeg.core q(-$b) q(Neg.neg) b s q(Real.instRing) | throwError "zz"
    pure ⟨q(-$a), q(-$b), A, B, q(Complex.ext
      (show (- $w).re = _ by simp_all) (show (- $w).im = _ by simp_all))⟩
  /- parse a subtraction `z₁ - z₂` -/
  | ~q($z₁ - $z₂) => parse q($z₁ + -$z₂)
  /- parse conjugate `conj z` -/
  | ~q(conj $w) =>
    let ⟨a, b, r, s, pf⟩ ← parse w
    let some B := evalNeg.core q(-$b) q(Neg.neg) b s q(Real.instRing) | throwError "zz"
    return ⟨q($a), q(-$b), r, B, q(extracted_2 _ _ _ $pf)⟩
  | ~q(@HPow.hPow ℂ ℕ ℂ instHPow $w $n) =>
    match n.nat? with
    | some 0 =>
      return ⟨q(1), q(0), ro, rz, (q(pow_zero $w) :)⟩
    | some 1 =>
      let ⟨a, b, r, s, pf⟩ ← parse w
      return ⟨q($a), q($b), r, s, (q(pow_one $w) :)⟩
      -- parse q((@HPow.hPow ℂ ℕ ℂ instHPow $w ($n - 1 : ℕ)) * $w)
    | _ => throwError "nnn"

  /- parse `(I:ℂ)` -/
  | ~q(Complex.I) =>
    pure ⟨q(0), q(1), rz, ro, q(split_I)⟩
  /- anything else needs to be on the list of atoms -/
  | _ =>
    -- let some n := Expr.nat? z | throwError "not natural"
    -- let ⟨rn, _⟩ ←  mkOfNat q(ℝ) q(inferInstance) q($n)
    try
      let ⟨q, n, d, pf⟩ ← Mathlib.Meta.NormNum.deriveRat (α := q(ℂ)) (u := 0) (_inst := q(inferInstance)) z
        <|> throwError "found the atom {z} which is not a rational numeral"

      let r : Q(ℝ) := q(Rat.cast ($n/$d : ℚ))
      let a ← Mathlib.Meta.NormNum.derive (u := 0) r
      trace[debug] "{a}"
      pure ⟨r, q(0), a, rz, q(extracted_1 $z $n $d $pf)⟩
        -- extract_goal
        -- obtain ⟨hd, hz⟩ := $pf
        -- -- obtain ⟨c, hc⟩ := isUnit_of_invertible (Nat.cast $d : ℂ)
        -- -- rw [hc.symm] at hz
        -- rw [invOf_units ⟨Nat.cast $d, (Nat.cast $d)⁻¹, by simp, by simp⟩ ] at hz
        -- simp at hz
        -- rw [← div_eq_mul_inv] at hz
        -- rw [hz]
        -- exact Complex.ext (by simp) (by simp)

    catch _ =>
      /- parse a constructor type -/
      match z with
      |~q(Complex.mk $a $b) =>
        trace[debug] "term {z} : we are in ⟨{a}, {b}⟩ constructor parsing"
        let ra ← derive (α := q(ℝ)) a
        let rb ← derive (α := q(ℝ)) b
        pure ⟨a, b, ra, rb, q(rfl)⟩
      | _ => throwError "found the atom {z} which is not a numeral"

#check pow_one
def normalize (z : Q(ℂ)) : MetaM (Σ a b : Q(ℝ), Q($z = ⟨$a, $b⟩)) := do
  let ⟨_a, _b, ra, rb, pf⟩ ← parse z
  let { expr := (a' : Q(ℝ)), proof? := (pf_a : Q($_a = $a')) } ← ra.toSimpResult | unreachable!
  let { expr := (b' : Q(ℝ)), proof? := (pf_b : Q($_b = $b')) } ← rb.toSimpResult | unreachable!
  return ⟨a', b', q(by simp_all)⟩

elab "norm_numI" : conv => do
  let z ← Conv.getLhs
  unless (q(ℂ) == (← inferType z)) do throwError "{z} is not a complex number"
  have z : Q(ℂ) := z
  let ⟨a, b, pf⟩ ← normalize z
  Conv.applySimpResult { expr := q(Complex.mk $a $b), proof? := some pf }

def proveEq (g : MVarId) : MetaM Unit := do
  let some ⟨α, a, b⟩ := (← g.getType).eq? | throwError "goal is not an equality"
  guard (← withReducibleAndInstances (isDefEq α q(ℂ))) <|> throwError "type of equality is not ℂ"
  let ⟨a₁, a₂, pf_a⟩ := ← normalize a
  let ⟨b₁, b₂, pf_b⟩ := ← normalize b
  trace[debug] "{a} simplifies to ⟨{a₁}, {a₂}⟩, {b} to {b₁}, {b₂}"
  trace[debug] "comparing {a₁} and {b₁}: {← withReducibleAndInstances (isDefEq a₁ b₁)}"
  guard (← (isDefEq a₁ b₁)) <|>
    throwError "Real-part disagreement: LHS normalizes to {a₁}, RHS normalizes to {b₁}"
  guard (← withReducibleAndInstances (isDefEq a₂ b₂)) <|>
    throwError "Imaginary-part disagreement: LHS normalizes to {a₂}, RHS normalizes to {b₂}"
  g.assign (← mkAppM ``eq_of_eq_of_eq #[pf_a, pf_b])

elab "norm_numI" : tactic => liftMetaFinishingTactic proveEq

end Mathlib.Tactic.NormNumI

set_option trace.debug true

open Complex
#synth HPow ℂ ℕ ℂ
example : (3 + 4 * I : ℂ)^1 = 3 + 4 * I := by norm_numI
example : (1:ℂ) = ⟨1, 0⟩ := by norm_numI
example : (I:ℂ) = 0 + 1 * I := by norm_numI
example : (1.5:ℂ) = ⟨3 / 2, 0⟩ := by conv_lhs => norm_numI

example : 0 + (1:ℂ) = 1 := by norm_numI
example : (1.0:ℂ) + 0 = 1 := by norm_numI
example : (1.0:ℂ) + 0.5 = 3/2 := by norm_numI
example : I + (3/2:ℂ) = 3/2 + I := by norm_numI

example : 1 * (2:ℂ) = 2 := by norm_numI

example : (1 + I) * (1 + I * I * I) = 2 := by norm_numI

example : (1 + 3.5 + I) * (1 + I) = 7 / 2 + 11 / 2 * I := by norm_numI

example : (3 + 4 * I)⁻¹ * (3 + 4 * I) = 1 := by norm_numI

-- example : (3 + I : ℂ)^2 = sorry := by conv_lhs => norm_numI
  -- conv_lhs => norm_numI
  -- exact Complex.ext (by simp; congr!; sorry) (by simp; congr!; sorry)
  -- conv_lhs => norm_numI
  -- exact Complex.ext (by simp; congr!; sorry) (by simp; congr!; sorry)

example : -1 / (1 + I) = (I - 1) / 2 := by norm_numI
  -- conv =>
  --   enter [2, 1]
  -- conv_lhs =>
  --   enter [2]; norm_numI

  -- sorry
example : (1 + I) * (1 - I) = 2 := by norm_numI

example : (1 + 2 * I) - (1 + 2 * I) = 0 := by norm_numI

example : (conj (3 + 4 * I) : ℂ) * (3 + 4 * I) = 25 := by norm_numI
