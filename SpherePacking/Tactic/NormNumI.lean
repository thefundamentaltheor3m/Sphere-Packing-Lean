/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yunzhou Xie, Sidharth Hariharan
-/
import Mathlib.Tactic.NormNum

import Mathlib.Data.Complex.Basic

open Lean Meta Elab Qq Tactic Complex Mathlib.Tactic
open ComplexConjugate

example : 1 + 1 = 2 ∧ 2 + 1 = 3 := by norm_num

namespace Mathlib.Meta
namespace NormNumI

theorem split_I : I = ⟨(0 : ℚ), (1 : ℚ)⟩ := by norm_cast

theorem split_zero : (0 : ℂ) = ⟨(0 : ℚ), (0 : ℚ)⟩ := by norm_cast

theorem split_one : (1 : ℂ) = ⟨(1 : ℚ), (0 : ℚ)⟩ := by norm_cast

theorem split_add {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℚ}
    (h₁ : z₁ = ⟨a₁, b₁⟩) (h₂ : z₂ = ⟨a₂, b₂⟩) :
    z₁ + z₂ = ⟨(a₁ + a₂ : ℚ), (b₁ + b₂ : ℚ)⟩ := by
  substs h₁ h₂
  simp [Complex.ext_iff]

theorem split_mul {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℚ} (h₁ : z₁ = ⟨a₁, b₁⟩) (h₂ : z₂ = ⟨a₂, b₂⟩) :
    z₁ * z₂ = ⟨(a₁ * a₂ - b₁ * b₂ : ℚ), (a₁ * b₂ + b₁ * a₂ : ℚ)⟩ :=
  Ring.mul_congr h₁ h₂ (by simp [Complex.ext_iff])

theorem split_inv {z : ℂ} {x y : ℚ} (h : z = ⟨x, y⟩) :
    z⁻¹ = ⟨(x / (x * x + y * y) : ℚ), (- y / (x * x + y * y) : ℚ)⟩ := by
  subst h
  rw [inv_def]
  exact Complex.ext (by simp [normSq_apply]; rfl) (by simp [normSq_apply, neg_div]; rfl)

theorem split_neg {z : ℂ} {a b : ℚ} (h : z = ⟨a, b⟩) :
    -z = ⟨(-a : ℚ), (-b : ℚ)⟩ := by
  subst h
  simp [Complex.ext_iff]

theorem split_conj {w : ℂ} {a b : ℚ} (hw : w = ⟨a, b⟩):
    conj w = ⟨a, (-b : ℚ)⟩ := by
  rw [hw]
  simp [Complex.ext_iff]

theorem split_num (n : ℕ) [n.AtLeastTwo]:
    OfNat.ofNat (α := ℂ) n = ⟨((OfNat.ofNat n) : ℚ), (0 : ℚ)⟩ := by norm_cast

theorem split_scientific (m exp : ℕ) (x : Bool) :
    (OfScientific.ofScientific m x exp : ℂ) = ⟨(OfScientific.ofScientific m x exp : ℚ), (0 : ℚ)⟩ :=
  by norm_cast

theorem eq_eq {z : ℂ} {a b a' b' : ℚ} (pf : z = ⟨a, b⟩)
  (pf_a : a = a') (pf_b : b = b') :
  z = ⟨a', b'⟩ := by simp_all

theorem eq_of_eq_of_eq_of_eq {z w : ℂ} {az bz aw bw : ℚ} (hz : z = ⟨az, bz⟩) (hw : w = ⟨aw, bw⟩)
    (ha : az = aw) (hb : bz = bw) : z = w := by
  simp [hz, hw, ha, hb]

theorem eq_of_eq_of_eq_and_eq {z w : ℂ} {az bz aw bw : ℚ} (hz : z = ⟨az, bz⟩) (hw : w = ⟨aw, bw⟩)
    (h : az = aw ∧ bz = bw) : z = w := eq_of_eq_of_eq_of_eq hz hw h.1 h.2

theorem neq_of_re_neq {z w : ℂ} {az bz aw bw : ℚ} (hz : z = ⟨az, bz⟩) (hw : w = ⟨aw, bw⟩)
    (ha : az ≠ aw) : z ≠ w := by
  simp [hz, hw, ha]

theorem neq_of_im_neq {z w : ℂ} {az bz aw bw : ℚ} (hz : z = ⟨az, bz⟩) (hw : w = ⟨aw, bw⟩)
    (hb : bz ≠ bw) : z ≠ w := by
  simp [hz, hw, hb]

theorem re_eq_of_eq {z : ℂ} {a b : ℚ} (hz : z = ⟨a, b⟩) : Complex.re z = a := by
  simp [hz]

theorem im_eq_of_eq {z : ℂ} {a b : ℚ} (hz : z = ⟨a, b⟩) : Complex.im z = b := by
  simp [hz]

set_option pp.showLetValues true
partial def parse (z : Q(ℂ)) :
    MetaM (Σ a b : Q(ℚ),  Q($z = ⟨$a, $b⟩)) := do
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
  | ~q($z₁ / $z₂) => do
    let ⟨a, b, pf⟩ ← parse q($z₁ * $z₂⁻¹)
    return ⟨q($a), q($b), q($pf)⟩
  /- parse `-z` -/
  | ~q(-$w) => do
    let ⟨a, b, pf⟩ ← parse w
    return ⟨q(-$a), q(-$b), q(split_neg $pf)⟩
  /- parse a subtraction `z₁ - z₂` -/
  | ~q($z₁ - $z₂) => parse q($z₁ + -$z₂)
  /- parse conjugate `conj z` -/
  | ~q(conj $w) =>
    let ⟨a, b, pf⟩ ← parse w
    return ⟨q($a), q(-$b), q(split_conj $pf)⟩
  /- parse natural number power -/
  | ~q(@HPow.hPow ℂ ℕ ℂ instHPow $w $n') =>
    let ⟨n, hn⟩ ← NormNum.deriveNat q($n') q(inferInstance)
    match n.natLit! with
    | 0 =>
      let _i : $n =Q 0 := ⟨⟩
      return ⟨q(1), q(0), q(show $w ^ $n' = _ from $(hn).out ▸ sorry)⟩
    | n + 1 =>
      parse q($w^$n * $w)
  /- parse integer power -/
  | ~q(@HPow.hPow ℂ ℤ ℂ instHPow $w $k) =>
    let ⟨k', hm⟩ ← NormNum.deriveInt q($k) q(inferInstance)
    match k'.intLit! with
    | Int.ofNat n =>
      let ⟨a, b, pf⟩ ← parse q(@HPow.hPow ℂ ℕ ℂ instHPow $w $n)
      let _i : $k' =Q $n := ⟨⟩
      return ⟨a, b, q(by
        dsimp [«$z»]
        rw [($hm).out]
        exact $pf)⟩
    | Int.negSucc n =>
      let ⟨a, b, pf⟩ ← parse q(($w ^ ($n + 1))⁻¹)
      let _i : $k' =Q Int.negSucc $n := ⟨⟩
      return ⟨a, b, q(by
        dsimp [«$z»]
        erw [($hm).out, zpow_negSucc]
        exact $pf)⟩
  /- parse `(I:ℂ)` -/
  | ~q(Complex.I) =>
    pure ⟨q(0), q(1), q(split_I)⟩
  /- parse `(0:ℂ)` -/
  | ~q(0) =>
    pure ⟨q(0), q(0), q(split_zero)⟩
  /- parse `(1:ℂ)` -/
  | ~q(1) =>
    pure ⟨q(1), q(0), q(split_one)⟩
  /- anything else needs to be on the list of atoms -/
  | ~q(OfNat.ofNat $en (self := @instOfNatAtLeastTwo ℂ _ _ $inst)) =>
    return ⟨q(OfNat.ofNat $en), q(0), q(split_num $en)⟩
  | ~q(OfScientific.ofScientific $m $x $exp) =>
    return ⟨q(OfScientific.ofScientific $m $x $exp), q(0), q(split_scientific _ _ _)⟩
  -- /- parse a constructor type -/
  -- |~q(Complex.mk $a $b) =>
  --   pure ⟨a, b, q(rfl)⟩
  | _ => throwError "found the atom {z} which is not a numeral"

def normalize (z : Q(ℂ)) : MetaM (Σ a b : Q(ℚ), Q($z = ⟨$a, $b⟩)) := do
  let ⟨a, b, pf⟩ ← parse z
  let ra ← Mathlib.Meta.NormNum.derive (α := q(ℚ)) a
  let rb ← Mathlib.Meta.NormNum.derive (α := q(ℚ)) b
  let { expr := (a' : Q(ℚ)), proof? := (pf_a : Q($a = $a')) } ← ra.toSimpResult | unreachable!
  let { expr := (b' : Q(ℚ)), proof? := (pf_b : Q($b = $b')) } ← rb.toSimpResult | unreachable!
  return ⟨a', b', q(eq_eq $pf $pf_a $pf_b)⟩

elab "norm_numI" : conv => do
  let z ← Conv.getLhs
  unless (q(ℂ) == (← inferType z)) do throwError "{z} is not a complex number"
  have z : Q(ℂ) := z
  let ⟨a, b, pf⟩ ← normalize z
  Conv.applySimpResult { expr := q(Complex.mk $a $b), proof? := some pf }

elab "norm_numI" : tactic => liftMetaFinishingTactic fun g ↦ do
  let tgt ← g.getType
  if let some (_, a, b) := tgt.eq? then
    let ⟨0, A, a⟩ ← inferTypeQ' a |
      throwError "norm_num tactic only works for complex numbers"
    let .defEq h := ← isDefEqQ q($A) q(ℂ) |
      throwError "norm_num tactic only works for complex numbers, not {A}"
    have b : Q(ℂ) := b
    let ⟨x₁, y₁, pf_a⟩ ← normalize a
    let ⟨x₂, y₂, pf_b⟩ ← normalize b
    -- Lean.logInfo "Proving eq"
    let ⟨iseqx, eqx⟩ ← NormNum.deriveBool q($x₁ = $x₂ ∧ $y₁ = $y₂)
    match iseqx with
    | true =>
      -- Lean.logInfo "Proved eq"
      let pf : Q($a = $b) := q(eq_of_eq_of_eq_and_eq $pf_a $pf_b $eqx)
      g.assign pf
    | _ =>
      throwError "LHS normalizes to {q(Complex.mk $x₁ $y₁)}, RHS normalizes to {q(Complex.mk $x₂ $y₂)}"
    -- if (x₁ == x₂) ∧ (y₁ == y₂) then
    --   let _ : $x₁ =Q $x₂ := ⟨⟩
    --   let _ : $y₁ =Q $y₂ := ⟨⟩
    --   let pf : Q($a = $b) := q(eq_of_eq_of_eq_of_eq $pf_a $pf_b rfl rfl)
    --   g.assign pf
    -- else
  -- else if let some (_, a, b) := tgt.ne? then
  --   let ⟨_, A, a⟩ ← inferTypeQ' a
  --   unless (← isDefEq A q(ℂ)) do
  --     throwError "norm_num tactic only works for complex numbers, not {A}"
  --   have a : Q(ℂ) := a
  --   have b : Q(ℂ) := b
  --   let ⟨x₁, y₁, pf_a⟩ ← normalize a
  --   let ⟨x₂, y₂, pf_b⟩ ← normalize b
  --   if heq : (x₁ == x₂) ∧ (y₁ == y₂) then
  --     throwError "LHS normalizes to {q(Complex.mk $x₁ $y₁)}, RHS normalizes to {q(Complex.mk $x₂ $y₂)}"
  --   else if hne : (x₁ != x₂) ∧ (y₁ == y₂) then
  --     let _ : ¬($x₁ =Q $x₂) := fun h ↦ by absurd hne.1; sorry
  --     -- have pf_re : x₁ ≠ x₂ := by
  --     --   rw [← bne_iff_ne]
  --     --   sorry
  --     -- We know x₁ ≠ x₂, so we can use this directly
  --     let pf : Q($a ≠ $b) := q(neq_of_re_neq $pf_a $pf_b sorry)
  --     g.assign pf
  --   else
  --     have pf_im : Q($y₁ ≠ $y₂) := tgt
  --     let pf : Q($a ≠ $b) := q(neq_of_im_neq $pf_a $pf_b $pf_im)
  --     g.assign pf
  else if let some (_, a, b) := tgt.ne? then
    let ⟨0, A, a⟩ ← inferTypeQ' a |
      throwError "norm_num tactic only works for complex numbers"
    let .defEq h := ← isDefEqQ q($A) q(ℂ) |
      throwError "norm_num tactic only works for complex numbers, not {A}"
    have b : Q(ℂ) := b
    let ⟨x₁, y₁, pf_a⟩ ← normalize a
    let ⟨x₂, y₂, pf_b⟩ ← normalize b
    -- Lean.logInfo "Proving eq"
    let ⟨iseqx, eqx⟩ ← NormNum.deriveBool q($x₁ = $x₂ ∧ $y₁ = $y₂)
    match iseqx with
    | true =>
      -- Lean.logInfo "Proved eq"
      let pf : Q($a = $b) := q(eq_of_eq_of_eq_and_eq $pf_a $pf_b $eqx)
      g.assign pf
    | _ =>
      throwError "LHS normalizes to {q(Complex.mk $x₁ $y₁)}, RHS normalizes to {q(Complex.mk $x₂ $y₂)}"
  else throwError "not `=` or `≠` goal"
  -- else if let some (α, a, b) := tgt.ne? then
  --   let ⟨u, A, a⟩ ← inferTypeQ' a
  --   unless (← isDefEq A q(ℂ)) do
  --     throwError "norm_num tactic only works for complex numbers, not {A}"
  --   have a : Q(ℂ) := a
  --   have b : Q(ℂ) := b
  --   let ⟨x₁, y₁, pf_a⟩ ← normalize a
  --   let ⟨x₂, y₂, pf_b⟩ ← normalize b
  --   throwError "LHS normalizes to {q(Complex.mk $x₁ $x₁)}, RHS normalizes to {q(Complex.mk $x₂ $y₂)}"
  -- else
  --   throwError "norm_num tactic only handles = or ≠ goals, not {tgt}!"

-- #conv norm_numI => (1.5 : ℂ)

-- set_option trace.debug true

#check norm_num
-- -- Testing the `parse` function
-- elab "norm_numI_parse" : conv => do
--   let z ← Conv.getLhs
--   unless (q(ℂ) == (← inferType z)) do throwError "{z} is not a complex number"
--   have z : Q(ℂ) := z
--   let ⟨a, b, pf⟩ ← parse z
--   Conv.applySimpResult { expr := q(Complex.mk $a $b), proof? := some pf }

example : (1 + 3.5 + I) * (1 + I) = 7 / 2 + 11 / 2 * I := by norm_numI
example : (3 + 4 * I)⁻¹ * (3 + 4 * I) = 1 := by norm_numI
example : -1 / (1 + I) = (I - 1) / 2 := by norm_numI
example : (1 + I) * (1 - I) = 2 := by norm_numI
example : (1 + 2 * I) - (1 + 2 * I) = 0 := by norm_numI
example : (conj (3 + 4 * I) : ℂ) * (3 + 4 * I) = 25 := by norm_numI
example : (3 + I : ℂ) ^ 2 = 8 + 6 * I := by norm_numI
example : (3 : ℂ) ^ 2 + (4 : ℂ) ^ 2 = 25 := by norm_numI

-- example : 2 = 3 := by norm_num

end NormNumI

-- #exit

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
  let ⟨ba, ra⟩ ←  withTraceNode `debug (fun x => return m!"{exceptEmoji x} norm_numI.evalComplexEq: z = {az} + {bz}i {q($az = $aw)}") do
    deriveBool q($az = $aw)
  trace[debug] "norm_numI.evalComplexEq output: {ba} {ra}"
  match ba with
  | true =>
    let ⟨bb, rb⟩ ← deriveBool q($bz = $bw)
    match bb with
    | true => return Result'.isBool true q(NormNumI.eq_of_eq_of_eq_of_eq $pfz $pfw $ra $rb)
    | false => return Result'.isBool false q(NormNumI.neq_of_im_neq $pfz $pfw $rb)
  | false => return Result'.isBool false q(NormNumI.neq_of_re_neq $pfz $pfw $ra)

/-- The `norm_num` extension which identifies expressions of the form `Complex.re (z : ℂ)`,
such that `norm_num` successfully recognises the real part of `z`.
-/
@[norm_num Complex.re _] def evalRe : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q ℚ := ⟨⟩
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
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q ℚ := ⟨⟩
  let .proj ``Complex 1 z ← whnfR e | failure
  have z : Q(ℂ) := z
  haveI' : $e =Q (Complex.im $z) := ⟨⟩
  let ⟨_, b, pf⟩ ← NormNumI.parse z
  let r ← derive q($b)
  return r.eqTrans q(NormNumI.im_eq_of_eq $pf)

end NormNum

end Mathlib.Meta

-- The tactic cannot handle the following, but this is a conscious design decision.
-- example: ⟨1, 0⟩ + ⟨38, 0⟩ - 1 = (⟨37, 0⟩ : ℂ) := by
--   conv_lhs => norm_numI
