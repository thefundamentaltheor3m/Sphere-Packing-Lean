/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yunzhou Xie, Sidharth Hariharan
-/
module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.NormNum


/-!
# `norm_numI` for `ℂ`

This file defines a conv tactic `norm_numI` extending `norm_num` to handle expressions in `ℂ`.
The key idea is to rewrite a complex expression into `Complex.mk` form, then run `norm_num`
separately on the real and imaginary parts.

## Main declarations
* `Mathlib.Meta.NormNumI.parse` and `Mathlib.Meta.NormNumI.normalize`
* conv tactics `norm_numI` and `norm_numI_parse`
* `Mathlib.Tactic.NormNum.evalComplexEq`
-/

@[expose] public meta section


open Lean Meta Elab Qq Tactic Complex Mathlib.Tactic
open ComplexConjugate

namespace Mathlib.Meta.NormNumI

/-- Rewrite `I : ℂ` as `⟨0, 1⟩`. -/
theorem split_I : I = ⟨0, 1⟩ := rfl

/-- Rewrite `0 : ℂ` as `⟨0, 0⟩`. -/
theorem split_zero : (0 : ℂ) = ⟨0, 0⟩ := rfl

/-- Rewrite `1 : ℂ` as `⟨1, 0⟩`. -/
theorem split_one : (1 : ℂ) = ⟨1, 0⟩ := rfl

/-- Split an addition into componentwise addition in `Complex.mk` form. -/
theorem split_add {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ}
    (h₁ : z₁ = ⟨a₁, b₁⟩) (h₂ : z₂ = ⟨a₂, b₂⟩) :
    z₁ + z₂ = ⟨(a₁ + a₂), (b₁ + b₂)⟩ := by
  exact Ring.add_congr h₁ h₂ rfl

/-- Split a multiplication into real and imaginary parts in `Complex.mk` form. -/
theorem split_mul {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ} (h₁ : z₁ = ⟨a₁, b₁⟩) (h₂ : z₂ = ⟨a₂, b₂⟩) :
    z₁ * z₂ = ⟨(a₁ * a₂ - b₁ * b₂), (a₁ * b₂ + b₁ * a₂)⟩ := by
  exact Ring.mul_congr h₁ h₂ rfl

/-- Split an inverse into real and imaginary parts in `Complex.mk` form. -/
theorem split_inv {z : ℂ} {x y : ℝ} (h : z = ⟨x, y⟩) :
    z⁻¹ = ⟨x / (x * x + y * y), - y / (x * x + y * y)⟩ := by
  subst h
  apply Complex.ext <;> simp [normSq_apply]

/-- Split a negation into real and imaginary parts in `Complex.mk` form. -/
theorem split_neg {z : ℂ} {a b : ℝ} (h : z = ⟨a, b⟩) :
    -z = ⟨-a, -b⟩ := by
  subst h
  rfl

/-- Split a complex conjugate into real and imaginary parts in `Complex.mk` form. -/
theorem split_conj {w : ℂ} {a b : ℝ} (hw : w = ⟨a, b⟩) :
    conj w = ⟨a, -b⟩ := by
  rw [hw]
  rfl

/-- Rewrite a numeral in `ℂ` as `⟨n, 0⟩`. -/
theorem split_num (n : ℕ) [n.AtLeastTwo] :
    OfNat.ofNat (α := ℂ) n = ⟨OfNat.ofNat n, 0⟩ := rfl

/-- Rewrite scientific notation in `ℂ` as `⟨x, 0⟩`. -/
theorem split_scientific (m exp : ℕ) (x : Bool) :
    (OfScientific.ofScientific m x exp : ℂ) = ⟨(OfScientific.ofScientific m x exp : ℝ), 0⟩ :=
  rfl

/-- Transport an equality `z = ⟨a, b⟩` along equalities `a = a'` and `b = b'`. -/
theorem eq_eq {z : ℂ} {a b a' b' : ℝ} (pf : z = ⟨a, b⟩)
  (pf_a : a = a') (pf_b : b = b') :
  z = ⟨a', b'⟩ := by simp_all

/-- Combine componentwise equalities to conclude equality of two complex numbers. -/
theorem eq_of_eq_of_eq_of_eq {z w : ℂ} {az bz aw bw : ℝ} (hz : z = ⟨az, bz⟩) (hw : w = ⟨aw, bw⟩)
    (ha : az = aw) (hb : bz = bw) : z = w := by
  simp [hz, hw, ha, hb]

/-- If real parts differ, then the complex numbers differ. -/
theorem ne_of_re_ne {z w : ℂ} {az bz aw bw : ℝ} (hz : z = ⟨az, bz⟩) (hw : w = ⟨aw, bw⟩)
    (ha : az ≠ aw) : z ≠ w := by
  simp [hz, hw, ha]

/-- If imaginary parts differ, then the complex numbers differ. -/
theorem ne_of_im_ne {z w : ℂ} {az bz aw bw : ℝ} (hz : z = ⟨az, bz⟩) (hw : w = ⟨aw, bw⟩)
    (hb : bz ≠ bw) : z ≠ w := by
  simp [hz, hw, hb]

/-- Read off the real part from an equality `z = ⟨a, b⟩`. -/
theorem re_eq_of_eq {z : ℂ} {a b : ℝ} (hz : z = ⟨a, b⟩) : Complex.re z = a := by simp [hz]

/-- Read off the imaginary part from an equality `z = ⟨a, b⟩`. -/
theorem im_eq_of_eq {z : ℂ} {a b : ℝ} (hz : z = ⟨a, b⟩) : Complex.im z = b := by simp [hz]

/--
Parse a quoted complex expression into a witness `z = ⟨a, b⟩`.

This is used by `norm_numI` to expose real and imaginary parts that can be simplified by
`norm_num`.
-/
partial def parse (z : Q(ℂ)) :
    MetaM (Σ a b : Q(ℝ), Q($z = ⟨$a, $b⟩)) := do
  -- Syntactic `Complex.mk` case.
  -- We avoid Qq defeq-matching here, since structure eta means `Complex.mk _ _` would match
  -- *any* `z : ℂ`, causing nontermination in our `norm_num` extensions.
  if z.isAppOfArity ``Complex.mk 2 then
    let args := z.getAppArgs
    let a : Q(ℝ) := args[0]!
    let b : Q(ℝ) := args[1]!
    let pf ← mkEqRefl z
    return ⟨a, b, (show Q($z = ⟨$a, $b⟩) from pf)⟩
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
  /- parse an integer power: `w ^ (n : ℤ)` when `n` is a numeral -/
  | ~q(@HPow.hPow ℂ ℤ ℂ instHPow $w (-$n)) =>
    let ⟨a, b, pf⟩ ← parse q(($w ^ $n)⁻¹)
    let hpow : Q($w ^ (-$n) = ($w ^ $n)⁻¹) := q(zpow_neg (a := $w) $n)
    return ⟨a, b, q(Eq.trans $hpow $pf)⟩
  | ~q(@HPow.hPow ℂ ℤ ℂ instHPow $w (@OfNat.ofNat ℤ $n (@instOfNat $n))) =>
    let ⟨a, b, pf⟩ ← parse q($w ^ $n)
    let hpow : Q($w ^ (@OfNat.ofNat ℤ $n (@instOfNat $n)) = $w ^ $n) := q(by
      dsimp [OfNat.ofNat, instOfNat]
      exact zpow_natCast (a := $w) $n)
    return ⟨a, b, q(Eq.trans $hpow $pf)⟩
  | ~q(@HPow.hPow ℂ ℕ ℂ instHPow $w $n) =>
    let k? := n.nat?
    let some k :=
      k? <|> n.rawNatLit? | throwError "exponent {n} not handled by norm_numI"
    match k with
    | 0 => return ⟨q(1), q(0), (q(pow_zero $w) :)⟩
    | k + 1 =>
      let k' : Q(ℕ) := mkNatLit k
      parse q($w ^ $k' * $w)
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
  | _ => throwError "found the atom {z} which is not a numeral"

/-- Normalize the output of `parse` by running `norm_num` on the real and imaginary parts. -/
def normalize (z : Q(ℂ)) : MetaM (Σ a b : Q(ℝ), Q($z = ⟨$a, $b⟩)) := do
  let ⟨a, b, pf⟩ ← parse z
  let ra ← Mathlib.Meta.NormNum.derive (α := q(ℝ)) a
  let rb ← Mathlib.Meta.NormNum.derive (α := q(ℝ)) b
  let { expr := (a' : Q(ℝ)), proof? := (pf_a : Q($a = $a')) } ← ra.toSimpResult | unreachable!
  let { expr := (b' : Q(ℝ)), proof? := (pf_b : Q($b = $b')) } ← rb.toSimpResult | unreachable!
  return ⟨a', b', q(eq_eq $pf $pf_a $pf_b)⟩

/-- Extract and typecheck the LHS of the current conv goal as a quoted complex expression. -/
def getComplexLhs : TacticM Q(ℂ) := do
  let z ← Conv.getLhs
  unless (q(ℂ) == (← inferType z)) do throwError "{z} is not a complex number"
  have z : Q(ℂ) := z
  return z

/-- Conv tactic: rewrite a complex expression into `Complex.mk` form and simplify by `norm_num`. -/
elab "norm_numI" : conv => do
  let z ← getComplexLhs
  let ⟨a, b, pf⟩ ← normalize z
  Conv.applySimpResult { expr := q(Complex.mk $a $b), proof? := some pf }

-- Testing the `parse` function
/-- Conv tactic: rewrite a complex expression into `Complex.mk` form using `parse` only. -/
elab "norm_numI_parse" : conv => do
  let z ← getComplexLhs
  let ⟨a, b, pf⟩ ← parse z
  Conv.applySimpResult { expr := q(Complex.mk $a $b), proof? := some pf }

end NormNumI
namespace NormNum

/-- The `norm_num` extension which identifies expressions of the form `(z : ℂ) = (w : ℂ)`,
such that `norm_num` successfully recognises both the real and imaginary parts of both `z` and `w`.
-/
@[norm_num (_ : ℂ) = _] def evalComplexEq : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q Prop := ⟨⟩
  let .app (.app f z) w ← whnfR e | failure
  guard <| ← withNewMCtxDepth <| isDefEq f q(Eq (α := ℂ))
  have z : Q(ℂ) := z
  have w : Q(ℂ) := w
  haveI' : $e =Q ($z = $w) := ⟨⟩
  let ⟨az, bz, pfz⟩ ← NormNumI.parse z
  let ⟨aw, bw, pfw⟩ ← NormNumI.parse w
  let ⟨ba, ra⟩ ← deriveBool q($az = $aw)
  match ba with
  | true =>
    let ⟨bb, rb⟩ ← deriveBool q($bz = $bw)
    match bb with
    | true => return Result'.isBool true q(NormNumI.eq_of_eq_of_eq_of_eq $pfz $pfw $ra $rb)
    | false => return Result'.isBool false q(NormNumI.ne_of_im_ne $pfz $pfw $rb)
  | false => return Result'.isBool false q(NormNumI.ne_of_re_ne $pfz $pfw $ra)

/-- The `norm_num` extension which identifies expressions of the form `Complex.re (z : ℂ)`,
such that `norm_num` successfully recognises the real part of `z`.
-/
@[norm_num Complex.re _] def evalRe : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q ℝ := ⟨⟩
  let .proj ``Complex 0 z ← whnfR e | failure
  have z : Q(ℂ) := z
  haveI' : $e =Q (Complex.re $z) := ⟨⟩
  let ⟨a, _, pf⟩ ← NormNumI.parse z
  let r ← derive q($a)
  return r.eqTrans q(NormNumI.re_eq_of_eq $pf)

/-- The `norm_num` extension which identifies expressions of the form `Complex.im (z : ℂ)`,
such that `norm_num` successfully recognises the imaginary part of `z`.
-/
@[norm_num Complex.im _] def evalIm : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q ℝ := ⟨⟩
  let .proj ``Complex 1 z ← whnfR e | failure
  have z : Q(ℂ) := z
  haveI' : $e =Q (Complex.im $z) := ⟨⟩
  let ⟨_, b, pf⟩ ← NormNumI.parse z
  let r ← derive q($b)
  return r.eqTrans q(NormNumI.im_eq_of_eq $pf)

end Mathlib.Meta.NormNum
open Lean Elab Tactic in
/-- `norm_num1` conv tactic for complex numbers. -/
@[tactic Mathlib.Tactic.normNum1Conv] def normNum1ConvComplex : Tactic :=
  fun _ => withMainContext do
  let z ← Mathlib.Meta.NormNumI.getComplexLhs
  let ⟨a, b, pf⟩ ← Mathlib.Meta.NormNumI.normalize z
  Conv.applySimpResult { expr := q(Complex.mk $a $b), proof? := some pf }
