/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import SpherePacking.Tactic.NormNumI
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Tactic.Ring

/-!
# `push_re_im` and `norm_exp_simp` tactics

`push_re_im` computes real and imaginary parts of complex expressions *symbolically*: it
replaces the fragile hand-rolled simp chains

```lean
simp only [norm_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero,
  sub_zero, Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, ...]
```

scattered through the repository with a single call that proves goals like
`(2 * ↑π * I * ↑n * ↑z).re = -(2 * π * ↑n * z.im)` outright.

The implementation extends the recursive splitter of `SpherePacking.Tactic.NormNumI` from
numeric atoms to *symbolic* atoms:

* `(↑r : ℂ)` for `r : ℝ` splits as `⟨r, 0⟩`;
* `(↑z : ℂ)` for `z : ℍ` splits as `⟨z.re, z.im⟩`;
* casts of `ℕ` and `ℤ` split as `⟨↑n, 0⟩`;
* `Complex.exp ↑x` for `x : ℝ` splits as `⟨Real.exp x, 0⟩`;
* any other atom `w : ℂ` falls back to `⟨w.re, w.im⟩`.

The result is exposed as two simprocs, `PushReIm.pushRe` and `PushReIm.pushIm`, rewriting
`w.re` and `w.im` to the symbolic real/imaginary part. Consequently the tactics compose
with the full `simp` infrastructure (extra lemmas, hypotheses, locations).

## Tactics

* `push_re_im` — normalize all `.re`/`.im` projections in the goal and finish cleaning up
  with `try ring_nf`. Supports `push_re_im [extraLemmas] at h ⊢`.
* `norm_exp_simp` — additionally rewrites `‖cexp w‖ = rexp w.re` (via `Complex.norm_exp`)
  and distributes norms over products first, so goals about `‖cexp (2 * π * I * n * z)‖`
  reduce to `rexp` of an explicit real expression. Same argument/location syntax.
-/

@[expose] public section

open Lean Meta Elab Qq Tactic Complex
open ComplexConjugate

namespace SpherePacking.PushReIm

open Mathlib.Meta.NormNumI

theorem split_ofReal (r : ℝ) : (r : ℂ) = ⟨r, 0⟩ := rfl

theorem split_natCast (n : ℕ) : (n : ℂ) = ⟨(n : ℝ), 0⟩ :=
  Complex.ext (by simp) (by simp)

theorem split_intCast (n : ℤ) : (n : ℂ) = ⟨(n : ℝ), 0⟩ :=
  Complex.ext (by simp) (by simp)

theorem split_coeUpperHalfPlane (z : UpperHalfPlane) : (z : ℂ) = ⟨z.re, z.im⟩ :=
  Complex.ext (by simp) (by simp)

theorem split_expOfReal (x : ℝ) : Complex.exp (x : ℂ) = ⟨Real.exp x, 0⟩ :=
  Complex.ext (by simp [Complex.exp_ofReal_re]) (by simp [Complex.exp_ofReal_im])

theorem split_atom (z : ℂ) : z = ⟨z.re, z.im⟩ := (Complex.eta z).symm

/--
Recursively split a complex expression into symbolic real and imaginary parts.

Returns `(⟨a, b, pf⟩, isAtom)` where `pf : z = ⟨a, b⟩` and `isAtom` records whether the
*top-level* expression was an opaque atom (so callers can avoid no-progress rewrites).
-/
meta partial def parse (e : Q(ℂ)) :
    MetaM ((Σ a b : Q(ℝ), Q($e = ⟨$a, $b⟩)) × Bool) := do
  match e with
  | ~q($z₁ + $z₂) =>
    let (⟨a₁, b₁, pf₁⟩, _) ← parse z₁
    let (⟨a₂, b₂, pf₂⟩, _) ← parse z₂
    pure (⟨q($a₁ + $a₂), q($b₁ + $b₂), q(split_add $pf₁ $pf₂)⟩, false)
  | ~q($z₁ * $z₂) =>
    let (⟨a₁, b₁, pf₁⟩, _) ← parse z₁
    let (⟨a₂, b₂, pf₂⟩, _) ← parse z₂
    pure (⟨q($a₁ * $a₂ - $b₁ * $b₂), q($a₁ * $b₂ + $b₁ * $a₂), q(split_mul $pf₁ $pf₂)⟩, false)
  | ~q($z⁻¹) =>
    let (⟨x, y, pf⟩, _) ← parse z
    pure (⟨q($x / ($x * $x + $y * $y)), q(-$y / ($x * $x + $y * $y)), q(split_inv $pf)⟩, false)
  | ~q($z₁ / $z₂) =>
    let (r, _) ← parse q($z₁ * $z₂⁻¹)
    pure (r, false)
  | ~q(-$w) =>
    let (⟨a, b, pf⟩, _) ← parse w
    pure (⟨q(-$a), q(-$b), q(split_neg $pf)⟩, false)
  | ~q($z₁ - $z₂) =>
    let (r, _) ← parse q($z₁ + -$z₂)
    pure (r, false)
  | ~q(conj $w) =>
    let (⟨a, b, pf⟩, _) ← parse w
    pure (⟨q($a), q(-$b), q(split_conj $pf)⟩, false)
  | ~q(@HPow.hPow ℂ ℕ ℂ instHPow $w $n) =>
    match n.nat? with
    | some 0 =>
      pure (⟨q(1), q(0), (q(pow_zero $w) :)⟩, false)
    | some (n + 1) =>
      let (r, _) ← parse q($w ^ $n * $w)
      pure (r, false)
    | none =>
      pure (⟨q(Complex.re $e), q(Complex.im $e), q(split_atom $e)⟩, true)
  | ~q(Complex.I) =>
    pure (⟨q(0), q(1), q(split_I)⟩, false)
  | ~q(OfNat.ofNat $n (self := _)) =>
    let some n' := n.rawNatLit? |
      pure (⟨q(Complex.re $e), q(Complex.im $e), q(split_atom $e)⟩, true)
    if n' == 0 then
      pure (⟨q(0), q(0), (q(split_zero) :)⟩, false)
    else if n' == 1 then
      pure (⟨q(1), q(0), (q(split_one) :)⟩, false)
    else
      let _i : Q(Nat.AtLeastTwo $n) ← synthInstanceQ q(Nat.AtLeastTwo $n)
      pure (⟨q(OfNat.ofNat $n), q(0), (q(split_num $n) :)⟩, false)
  | ~q(OfScientific.ofScientific $m $x $exp) =>
    pure (⟨q(OfScientific.ofScientific $m $x $exp), q(0), q(split_scientific _ _ _)⟩, false)
  | ~q(Complex.exp (Complex.ofReal $x)) =>
    pure (⟨q(Real.exp $x), q(0), q(split_expOfReal $x)⟩, false)
  | ~q(Complex.ofReal $r) =>
    pure (⟨q($r), q(0), q(split_ofReal $r)⟩, false)
  | ~q(UpperHalfPlane.coe $z) =>
    pure (⟨q(UpperHalfPlane.re $z), q(UpperHalfPlane.im $z), q(split_coeUpperHalfPlane $z)⟩,
      false)
  | ~q(Nat.cast $n) =>
    pure (⟨q(($n : ℝ)), q(0), q(split_natCast $n)⟩, false)
  | ~q(Int.cast $n) =>
    pure (⟨q(($n : ℝ)), q(0), q(split_intCast $n)⟩, false)
  | _ =>
    pure (⟨q(Complex.re $e), q(Complex.im $e), q(split_atom $e)⟩, true)

/-- Extract the argument of a `Complex.re`/`Complex.im` application, accepting both the
constant-application and the primitive-projection form. -/
meta def projArg? (e : Expr) (fieldName : Name) (idx : Nat) : MetaM (Option Expr) := do
  if e.isAppOfArity (`Complex ++ fieldName) 1 then
    return some e.appArg!
  match ← whnfR e with
  | .proj ``Complex i w => if i == idx then return some w else return none
  | e' =>
    if e'.isAppOfArity (`Complex ++ fieldName) 1 then
      return some e'.appArg!
    return none

/-- Simproc rewriting `w.re` to the symbolic real part of `w` (via `PushReIm.parse`).
Opaque atoms are left untouched. -/
simproc_decl pushRe (Complex.re _) := fun e => do
  let some w ← projArg? e `re 0 | return .continue
  have w : Q(ℂ) := w
  let (⟨a, _b, pf⟩, isAtom) ← parse w
  if isAtom then return .continue
  return .visit { expr := a, proof? := some q(re_eq_of_eq $pf) }

/-- Simproc rewriting `w.im` to the symbolic imaginary part of `w` (via `PushReIm.parse`).
Opaque atoms are left untouched. -/
simproc_decl pushIm (Complex.im _) := fun e => do
  let some w ← projArg? e `im 1 | return .continue
  have w : Q(ℂ) := w
  let (⟨_a, b, pf⟩, isAtom) ← parse w
  if isAtom then return .continue
  return .visit { expr := b, proof? := some q(im_eq_of_eq $pf) }

end SpherePacking.PushReIm

/-- `push_re_im` computes `.re`/`.im` projections of complex expressions symbolically
(splitting through `+`, `*`, `-`, `⁻¹`, `/`, `^`, `conj`, `I`, numerals, and coercions of
`ℝ`, `ℕ`, `ℤ`, `ℍ`, plus `cexp` of real coercions), then cleans up with `try ring_nf`.

* `push_re_im [foo, h]` adds extra simp lemmas (e.g. `(F z).im = 0` facts);
* `push_re_im at h ⊢` works at hypotheses. -/
syntax (name := pushReImTac) "push_re_im" (" [" Lean.Parser.Tactic.simpLemma,* "]")?
  (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| push_re_im $[$loc:location]?) => do
    let simpTac ← `(tactic| simp only [SpherePacking.PushReIm.pushRe,
        SpherePacking.PushReIm.pushIm,
        mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero, zero_sub,
        sub_self, neg_zero, neg_neg] $[$loc:location]?)
    let ringTac ← `(tactic| try ring_nf $[$loc:location]?)
    `(tactic| ($simpTac; $ringTac))
  | `(tactic| push_re_im [$ls,*] $[$loc:location]?) => do
    let simpTac ← `(tactic| simp only [SpherePacking.PushReIm.pushRe,
        SpherePacking.PushReIm.pushIm,
        mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero, zero_sub,
        sub_self, neg_zero, neg_neg, $ls,*] $[$loc:location]?)
    let ringTac ← `(tactic| try ring_nf $[$loc:location]?)
    `(tactic| ($simpTac; $ringTac))

/-- `norm_exp_simp` rewrites `‖cexp w‖` to `rexp w.re`, distributes norms over products,
and computes the real part `w.re` symbolically via `push_re_im`'s simprocs. Typical use:
goals about `‖cexp (2 * π * I * n * z)‖` for `z : ℍ` reduce to `rexp` of an explicit real
expression in `z.re`/`z.im`.

Supports `norm_exp_simp [extraLemmas] at h ⊢` like `push_re_im`. -/
syntax (name := normExpSimpTac) "norm_exp_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")?
  (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| norm_exp_simp $[$loc:location]?) => do
    let simpTac ← `(tactic| simp only [Complex.norm_exp, Complex.norm_exp_ofReal_mul_I,
        norm_mul, norm_div, norm_pow, norm_zpow, norm_inv, norm_neg, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs,
        SpherePacking.PushReIm.pushRe, SpherePacking.PushReIm.pushIm,
        mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero, zero_sub,
        sub_self, neg_zero, neg_neg, Real.exp_zero] $[$loc:location]?)
    let ringTac ← `(tactic| try ring_nf $[$loc:location]?)
    `(tactic| ($simpTac; $ringTac))
  | `(tactic| norm_exp_simp [$ls,*] $[$loc:location]?) => do
    let simpTac ← `(tactic| simp only [Complex.norm_exp, Complex.norm_exp_ofReal_mul_I,
        norm_mul, norm_div, norm_pow, norm_zpow, norm_inv, norm_neg, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs,
        SpherePacking.PushReIm.pushRe, SpherePacking.PushReIm.pushIm,
        mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero, zero_sub,
        sub_self, neg_zero, neg_neg, Real.exp_zero, $ls,*] $[$loc:location]?)
    let ringTac ← `(tactic| try ring_nf $[$loc:location]?)
    `(tactic| ($simpTac; $ringTac))
