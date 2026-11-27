/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
module

public import SpherePacking.Tactic.EndpointIntegrability.Basic
public import SpherePacking.Tactic.EndpointIntegrability.Scale
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Ring

/-!
# Exponents of the comparison functions of `endpoint_integrability`

The comparison functions of `endpoint_integrability` are `powExp a k u t = t ^ a * |log t| ^ k *
exp (u t)` (see `SpherePacking.Tactic.EndpointIntegrability.Scale`), along a *canonical filter*
`l`, `atTop` or `𝓝[>] 0`. This file classifies an exponent `u` along `l`, by `exponentBound?`:

1. The exponent is written as a polynomial in `t` with real degrees, `u t = ∑ cᵢ * t ^ pᵢ`, with
   degrees `pᵢ` and coefficients `cᵢ` free of `t`: `u t` is simplified by `simp only` with
   `exponentLemmas`, which computes in particular the real parts of complex exponents that are
   polynomials in `(t : ℂ)`, and with `abs_of_pos` for `0 < t`, which turns `|t|`, `‖t‖` and
   `|-t|` into `t`, and parsed into monomials (`t`, real powers `t ^ p`, `√t`, sums,
   differences, negations, products, quotients by monomials and numeral natural powers). A degree
   is a `Degree`: an expression with its value if `norm_num` evaluates it to a rational number.
   Integer degrees are added in products; a product of monomials whose degrees are not integers,
   neither being `0`, is not parsed, since the identity `t ^ p * t ^ q = t ^ (p + q)` would not be
   proved. Equal degrees, by value or else as expressions, are merged. The identity is proved for
   `0 < t` by `simp only` with `exponentLemmas`, `powerLemmas`, `abs_of_pos` and `Real.rpow_neg`,
   then `field_simp` and `ring1`, and holds eventually along `l`.
2. A degree is *singular* if `t ^ p` is unbounded along `l`: `0 < p` at `atTop`, `p < 0` at
   `𝓝[>] 0`. The sign of a numeral degree is decided from its value, and that of another degree is
   asked of the discharger. A monomial whose degree is proved not singular is bounded by
   `isBoundedUnder_le_mul_rpow_atTop` or `isBoundedUnder_le_mul_rpow_nhdsGT`. For the others the
   discharger is asked whether the coefficient is negative, when the degree is proved singular,
   or else nonpositive, in which case the monomial is bounded by
   `isBoundedUnder_le_mul_rpow_of_nonpos` (see `monomialBound?`).
3. If the degree of a monomial is proved singular and its coefficient `c` negative, `exp ∘ u`
   decays exponentially: `u t - c * t ^ p` is bounded above, with that monomial as witness
   (`ExponentBound.decay`). Otherwise `u` is bounded above (`ExponentBound.bounded`).
4. A monomial `d * t ^ q` which is not bounded as in 2, such as `c * t` in `c * t - t ^ 2` with
   no hypothesis on `c`, is *absorbed* by a decaying monomial `c₀ * t ^ p` of strictly more
   singular degree, `q < p` at `atTop`, `p < q` at `𝓝[>] 0`, whatever the sign of `d`:
   `c₀ / (2 * n) * t ^ p + d * t ^ q` is bounded above, for any `n`
   (`isBoundedUnder_le_mul_rpow_add_mul_rpow_atTop` and
   `isBoundedUnder_le_mul_rpow_add_mul_rpow_nhdsGT`). The comparison of the degrees is decided
   from their values if both are numerals, and otherwise asked of the discharger. The witness of
   the decay is then `(c₀ / 2) * t ^ p`, the other half of `c₀ * t ^ p` being shared among the
   `n` absorbed monomials (see `absorbMonomials?`). If a monomial is neither bounded nor
   absorbed, the exponent is not classified by `exponentBound?`.
5. The decision of a comparison function may instead resolve such an *unknown* monomial
   `c * t ^ p` by a condition on the sign of `c` left as a side goal (`exponentBoundLeaving?`,
   with a `SignResolution`; see `resolveSigns?`): `c ≤ 0`, which bounds the monomial whatever its
   degree (`MonomialBound.nonpos`), or, if the degree is proved singular, `c < 0`, which makes the
   monomial a witness of the decay (`MonomialBound.decay`). The witness, a monomial proved to
   decay or else the unknown monomial of singular degree which absorbs the most others, absorbs
   the unknown monomials of strictly less singular degree, as in 4, which then get no condition;
   the others get `c ≤ 0`. The bound is then assembled as in 3 and 4. The statement left is
   `0 < -c`, respectively `0 ≤ -c`, with the negation pushed inwards, such as `0 < n` for
   `c = -1 * n` (see `proveOrLeaveNonpos?`); if `norm_num` refutes it, the exponent is not
   classified. This is tried only where `exponentBound?` fails, and `exponentBound?`, used by the
   comparisons, never leaves a goal.

The decision of the integrability of a comparison function
(`SpherePacking.Tactic.EndpointIntegrability.Decide`) classifies its exponent; the comparison of
two comparison functions (`SpherePacking.Tactic.EndpointIntegrability.Compare`) classifies the
difference of their exponents.

This file also defines the canonical filters, `proveCondition?`, which proves conditions on the
exponents, such as `0 < ↑2 * 1`, by the discharger or `norm_num`, and `proveOrLeaveCondition?`,
which leaves a condition which is neither proved nor refuted as a side goal.
-/

@[expose] public section

open Lean Meta Elab Tactic Qq Filter Topology

namespace Mathlib.Tactic.EndpointIntegrability

/-! ### Canonical filters -/

/-- The filters along which the engine works. Both satisfy `∀ᶠ t in l, 0 < t`. -/
meta inductive CanonicalFilter where
  /-- The filter `atTop`. -/
  | atTop
  /-- The filter `𝓝[>] 0`. -/
  | nhdsGT

/-- The filter, as an expression. -/
meta def CanonicalFilter.toExpr : CanonicalFilter → Q(Filter ℝ)
  | .atTop => q(Filter.atTop)
  | .nhdsGT => q(𝓝[>] 0)

/-- A proof of `∀ᶠ t in l, 0 < t`, the hypothesis `hl` of the lemmas of the scale. -/
meta def CanonicalFilter.eventuallyPos : CanonicalFilter → Expr
  | .atTop => (q(eventually_gt_atTop 0) : Q(∀ᶠ t in Filter.atTop, (0 : ℝ) < t))
  | .nhdsGT => (q(self_mem_nhdsWithin) : Q(∀ᶠ t in 𝓝[>] 0, (0 : ℝ) < t))

/-- A proof of `Tendsto (fun t ↦ |log t|) l atTop`, the hypothesis `hlog` of the lemmas of the
scale which need `|log t|` not to vanish eventually, such as the product rules. -/
meta def CanonicalFilter.tendstoAbsLog : CanonicalFilter → Expr
  | .atTop => (q(tendsto_abs_atTop_atTop.comp Real.tendsto_log_atTop) :
      Q(Tendsto (fun t : ℝ ↦ |Real.log t|) Filter.atTop Filter.atTop))
  | .nhdsGT => (q(tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero) :
      Q(Tendsto (fun t : ℝ ↦ |Real.log t|) (𝓝[>] 0) Filter.atTop))

/-- The canonical filter `l`, if it is one, up to instances. -/
meta def CanonicalFilter.ofExpr? (l : Expr) : MetaM (Option CanonicalFilter) :=
  [CanonicalFilter.atTop, .nhdsGT].findM? fun c ↦
    withNewMCtxDepth <| withTransparency .instances <| isDefEq l c.toExpr

/-- Whether a degree `p` with value `q` is singular, `t ^ p` being unbounded along the filter:
`0 < q` at `atTop`, `q < 0` at `𝓝[>] 0`. -/
meta def CanonicalFilter.isSingular : CanonicalFilter → ℚ → Bool
  | .atTop, q => 0 < q
  | .nhdsGT, q => q < 0

/-- The condition that the degree `p` is singular: `0 < p` at `atTop`, `p < 0` at `𝓝[>] 0`. -/
meta def CanonicalFilter.singularCondition (l : CanonicalFilter) (p : Q(ℝ)) : Q(Prop) :=
  match l with
  | .atTop => q(0 < $p)
  | .nhdsGT => q($p < 0)

/-- The condition that the degree `p` is not singular: `p ≤ 0` at `atTop`, `0 ≤ p` at
`𝓝[>] 0`. -/
meta def CanonicalFilter.regularCondition (l : CanonicalFilter) (p : Q(ℝ)) : Q(Prop) :=
  match l with
  | .atTop => q($p ≤ 0)
  | .nhdsGT => q(0 ≤ $p)

/-! ### Conditions -/

/-- The simplification of the proposition `p` by `norm_num`. -/
meta def normNumSimp (p : Expr) : MetaM Simp.Result := do
  let ctx ← Simp.mkContext {} (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  Mathlib.Meta.NormNum.deriveSimp ctx (e := p)

/-- The real expression `e` simplified by `norm_num`, or `e` itself if `norm_num` fails, for
messages: `0 + -1` becomes `-1`. -/
meta def displaySimp (e : Expr) : MetaM Expr := do
  try return (← normNumSimp e).expr catch _ => return e

/-- The function `u : ℝ → ℝ` as `fun t ↦ u t`, with `u t` simplified by `displaySimp`, for
messages. -/
meta def displayFun (u : Expr) : MetaM Expr :=
  withLocalDeclD `t q(ℝ) fun t ↦ do mkLambdaFVars #[t] (← displaySimp (u.beta #[t]))

/-- A proof of the proposition `p`, such as `↑2 * -1 < 0`, by the discharger `disch`, or else by
`norm_num`, or by the discharger on the simplification of `p` by `norm_num`. -/
meta def proveCondition? (disch : TSyntax ``Parser.Tactic.tacticSeq) (p : Expr) :
    TacticM (Option Expr) := do
  if let some h ← discharge? disch p then return h
  let r ← normNumSimp p
  if r.expr.isConstOf ``True then return some (← mkOfEqTrue (← r.getProof))
  if r.expr == p || r.expr.isConstOf ``False then return none
  let some h ← discharge? disch r.expr | return none
  r.mkEqMPR h

/-- A proof of `p` with no side goal, by `proveCondition?`; otherwise the simplification of `p` by
`norm_num`: `none` if it is `False`, and otherwise a proof from a new side goal, the simplified
statement. -/
meta def proveOrLeaveCondition? (disch : TSyntax ``Parser.Tactic.tacticSeq) (p : Expr) :
    TacticM (Option (Expr × List MVarId)) := do
  if let some h ← proveCondition? disch p then return some (h, [])
  let r ← normNumSimp p
  if r.expr.isConstOf ``False then return none
  let g ← mkFreshExprSyntheticOpaqueMVar r.expr
  return some (← r.mkEqMPR g, [g.mvarId!])

/-! ### Degrees -/

/-- The degree `p` of a monomial `c * t ^ p`: a real expression free of `t`, with its value if it
is a numeral. -/
meta structure Degree where
  /-- The degree, free of `t`. -/
  expr : Q(ℝ)
  /-- The value of the degree, if `norm_num` evaluates it to a rational number. -/
  value? : Option ℚ

/-- The integer degree `n`, written `((n : ℤ) : ℝ)`, which `Real.rpow_intCast` turns into an
integer power. -/
meta def Degree.ofInt (n : Int) : Degree :=
  have n' : Q(ℤ) := Lean.toExpr n
  ⟨q(($n' : ℤ) : ℝ), some n⟩

/-- The degree `p`, with its value computed by `norm_num`, written as by `Degree.ofInt` if this
value is an integer. -/
meta def Degree.ofExpr (p : Q(ℝ)) : MetaM Degree := do
  let value? ← try pure (← Mathlib.Meta.NormNum.derive (α := (q(ℝ) : Q(Type))) p).toRat
    catch _ => pure none
  match value? with
  | some q => return if q.den == 1 then .ofInt q.num else ⟨p, some q⟩
  | none => return ⟨p, none⟩

/-- The degree `1 / 2` of `√t`, written as in `Real.sqrt_eq_rpow`. -/
meta def Degree.half : Degree := ⟨q(1 / 2), some (1 / 2)⟩

/-- Whether two degrees are equal: they have the same value, or else the same expression. -/
meta def Degree.beq (d₁ d₂ : Degree) : Bool :=
  match d₁.value?, d₂.value? with
  | some q₁, some q₂ => q₁ == q₂
  | _, _ => d₁.expr == d₂.expr

/-- The opposite of a degree. -/
meta def Degree.neg (d : Degree) : Degree :=
  match d.value? with
  | some q => if q.den == 1 then .ofInt (-q.num) else ⟨q(-$(d.expr)), some (-q)⟩
  | none => ⟨q(-$(d.expr)), none⟩

/-- The sum of two degrees, if one of them is `0` or both are integers. The sums of other degrees,
such as `1 / 2 + 1`, are not formed: the identity `t ^ p * t ^ q = t ^ (p + q)` is not proved. -/
meta def Degree.add? (d₁ d₂ : Degree) : Option Degree :=
  match d₁.value?, d₂.value? with
  | some 0, _ => some d₂
  | _, some 0 => some d₁
  | some q₁, some q₂ =>
    if q₁.den == 1 && q₂.den == 1 then some (.ofInt (q₁.num + q₂.num)) else none
  | _, _ => none

/-! ### Polynomials with real degrees -/

/-- A monomial `coeff * t ^ degree`, with `coeff` and `degree` free of `t`. -/
meta structure Monomial where
  /-- The coefficient, free of `t`. -/
  coeff : Q(ℝ)
  /-- The degree. -/
  degree : Degree

/-- The coefficient `1`. -/
meta def oneCoeff : Q(ℝ) := q(1)

/-- The product of two coefficients, omitting a factor `1`. -/
meta def mulCoeff (c₁ c₂ : Q(ℝ)) : Q(ℝ) :=
  if c₁ == oneCoeff then c₂ else if c₂ == oneCoeff then c₁ else q($c₁ * $c₂)

/-- The negation of a monomial. -/
meta def Monomial.neg (m : Monomial) : Monomial := ⟨q(-$(m.coeff)), m.degree⟩

/-- The inverse of a monomial. -/
meta def Monomial.inv (m : Monomial) : Monomial := ⟨q($(m.coeff)⁻¹), m.degree.neg⟩

/-- The monomial `m` as the function `fun t ↦ c * t ^ p`, simplified by `displaySimp`, for
messages. -/
meta def Monomial.display (m : Monomial) : MetaM Expr :=
  have c := m.coeff
  have p := m.degree.expr
  displayFun q(fun t : ℝ ↦ $c * t ^ $p)

/-- The product of two monomials, if the sum of their degrees is formed by `Degree.add?`. -/
meta def Monomial.mul? (m₁ m₂ : Monomial) : Option Monomial :=
  (m₁.degree.add? m₂.degree).map (⟨mulCoeff m₁.coeff m₂.coeff, ·⟩)

/-- The product of two polynomials, if the products of their monomials are formed. -/
meta def mulPolynomials? (p₁ p₂ : List Monomial) : Option (List Monomial) :=
  List.flatten <$> p₁.mapM fun m₁ ↦ p₂.mapM m₁.mul?

/-- The polynomial with the monomials of equal degree of `p` merged, in the order of their first
occurrence. -/
meta def mergePolynomial (p : List Monomial) : List Monomial :=
  p.foldl (init := []) fun acc m ↦
    if acc.any (·.degree.beq m.degree) then
      acc.map fun a ↦
        if a.degree.beq m.degree then ⟨q($(a.coeff) + $(m.coeff)), a.degree⟩ else a
    else acc ++ [m]

/-- The polynomial with real degrees in the free variable `t` equal to `e`, if `e` is built from
`t`, its real powers `t ^ p` and its square root `√t`, and expressions free of `t`, by sums,
differences, negations, products, quotients by monomials and numeral natural powers, as long as
the products of monomials are formed by `Monomial.mul?`. The monomials are not merged. -/
meta partial def polynomial? (t : Expr) (e : Q(ℝ)) : OptionT MetaM (List Monomial) := do
  if !e.containsFVar t.fvarId! then return [⟨e, .ofInt 0⟩]
  if e == t then return [⟨oneCoeff, .ofInt 1⟩]
  let monomial? (x : Q(ℝ)) : OptionT MetaM Monomial := do
    let [m] := mergePolynomial (← polynomial? t x) | failure
    return m
  let mul? (p₁ p₂ : List Monomial) : OptionT MetaM (List Monomial) := do
    let some p := mulPolynomials? p₁ p₂ | failure
    return p
  match_expr e with
  | HAdd.hAdd _ _ _ _ x y => return (← polynomial? t x) ++ (← polynomial? t y)
  | HSub.hSub _ _ _ _ x y => return (← polynomial? t x) ++ (← polynomial? t y).map (·.neg)
  | Neg.neg _ _ x => return (← polynomial? t x).map (·.neg)
  | HMul.hMul _ _ _ _ x y => mul? (← polynomial? t x) (← polynomial? t y)
  | HDiv.hDiv _ _ _ _ x y => mul? (← polynomial? t x) [(← monomial? y).inv]
  | Inv.inv _ _ x => return [(← monomial? x).inv]
  | Real.sqrt x => if x == t then return [⟨oneCoeff, .half⟩] else failure
  | HPow.hPow _ β _ _ x n =>
    if β.isConstOf ``Real && x == t && !n.containsFVar t.fvarId! then
      return [⟨oneCoeff, ← Degree.ofExpr n⟩]
    let some k := n.numeral? | failure
    unless β.isConstOf ``Nat do failure
    let p ← polynomial? t x
    (List.replicate k p).foldlM mul? [⟨oneCoeff, .ofInt 0⟩]
  | _ => failure

/-- The lemmas of the `simp only` call simplifying an exponent `u t` before it is parsed as a
polynomial: application of operations on functions, casts of numerals, real and imaginary parts
of complex numbers, including those of the powers `(t : ℂ) ^ n` and of the quotients by numerals
and reals, with the powers of products split by `mul_pow`, so that the real part of a polynomial
in `(t : ℂ)` with complex coefficients becomes a polynomial in `t`, the units of the operations,
and `‖x‖ = |x|` and `|-x| = |x|` for reals. The set is fixed: the default simp set is not
used. -/
meta def exponentLemmas : List Name :=
  [``Pi.add_apply, ``Pi.sub_apply, ``Pi.neg_apply, ``Pi.zero_apply, ``Pi.smul_apply,
    ``nsmul_eq_mul, ``smul_eq_mul, ``Nat.cast_ofNat, ``Nat.cast_one, ``Nat.cast_zero,
    ``Complex.add_re, ``Complex.sub_re, ``Complex.neg_re, ``Complex.mul_re, ``Complex.div_ofNat_re,
    ``Complex.div_ofReal_re, ``Complex.add_im, ``Complex.sub_im, ``Complex.neg_im,
    ``Complex.mul_im, ``Complex.ofReal_re, ``Complex.ofReal_im, ``Complex.re_ofReal_pow,
    ``Complex.im_ofReal_pow, ``mul_pow, ``Complex.I_re, ``Complex.I_im, ``Complex.re_ofNat,
    ``Complex.im_ofNat, ``Complex.one_re, ``Complex.one_im, ``mul_zero, ``zero_mul, ``mul_one,
    ``one_mul, ``sub_zero, ``zero_sub, ``add_zero, ``zero_add, ``neg_zero, ``Real.norm_eq_abs,
    ``abs_neg]

/-- The lemmas writing the powers `t ^ p` of a monomial with integer powers, natural powers and
inverses when `p` is an integer or a numeral: `t ^ ((n : ℤ) : ℝ)` becomes `t ^ n`, written with
natural powers and inverses, as do `t ^ (2 : ℝ)`, `t ^ (1 : ℝ)` and `t ^ (0 : ℝ)`; `√t` becomes
`t ^ (1 / 2)`. Together with `Real.rpow_neg` for `0 ≤ t`, they write both sides of the identity
of `proveIdentity?` with the same atoms. -/
meta def powerLemmas : List Name :=
  [``Real.rpow_intCast, ``Real.rpow_ofNat, ``Real.rpow_one, ``Real.rpow_zero, ``Real.sqrt_eq_rpow,
    ``zpow_neg, ``zpow_ofNat, ``zpow_one, ``zpow_zero]

/-- The simplification context of `exponentPolynomial?` and `proveIdentity?`, given a hypothesis
`ht : 0 < t`: `exponentLemmas`, the lemmas `extra`, `abs_of_pos ht`, so that `|t|`, `‖t‖` and
`|-t|` become `t` (both canonical filters satisfy `∀ᶠ t in l, 0 < t`), and, if `rpowNeg`,
`Real.rpow_neg` for `0 ≤ t`. -/
meta def exponentContext (extra : List Name) (ht : Expr) (rpowNeg : Bool) :
    MetaM Simp.Context := do
  let mut thms ← simpTheoremsOfNames (exponentLemmas ++ extra) (simpOnly := true)
  thms ← thms.add (.other `abs_of_pos) #[] (← mkAppM ``abs_of_pos #[ht])
  if rpowNeg then
    thms ← thms.add (.other `rpow_neg) #[] (← mkAppM ``Real.rpow_neg #[← mkAppM ``le_of_lt #[ht]])
  Simp.mkContext {} (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)

/-- The exponent `u` as a polynomial in `t` with real degrees, with merged degrees, if it is one,
after simplification by `exponentContext` for `0 < t`. The result of `simp only` is
beta-reduced, since `Pi.zero_apply` leaves the type `(fun _ ↦ ℝ) t` in the instance of the zero
it produces. -/
meta def exponentPolynomial? (u : Expr) : MetaM (Option (List Monomial)) :=
  withLocalDeclD `t q(ℝ) fun t ↦ do
  have t' : Q(ℝ) := t
  withLocalDeclD `ht q(0 < $t') fun ht ↦ do
    let ctx ← exponentContext [] ht false
    let (r, _) ← simp (mkApp u t) ctx
    return (← (polynomial? t (← Core.betaReduce r.expr)).run).map mergePolynomial

/-- A proof of `∀ t, 0 < t → S t = v t`, if it is proved by `simp only` with `exponentLemmas`,
`powerLemmas`, `abs_of_pos` for `0 < t` and `Real.rpow_neg` for `0 ≤ t`, then `field_simp` and
`ring1`. -/
meta def proveIdentity? (S v : Q(ℝ → ℝ)) : TacticM (Option Expr) := do
  let proof ← mkFreshExprMVar q(∀ t : ℝ, 0 < t → $S t = $v t)
  let closed ← attempt proof.mvarId! do
    let (#[_, ht], g) ← proof.mvarId!.introN 2 | return false
    g.withContext do
      let ctx ← exponentContext powerLemmas (.fvar ht) true
      let (some g, _) ← simpTarget g ctx | return true
      return (← evalTacticAt (← `(tactic| ((try field_simp) <;> ring1))) g).isEmpty
  if closed then instantiateMVars proof else return none

/-! ### Bounds on exponents -/

/-- How a monomial `c * t ^ p` of an exponent is bounded above along a canonical filter. -/
meta inductive MonomialBound where
  /-- The degree is not singular, with a proof `hp` of `p ≤ 0` at `atTop`, `0 ≤ p` at
  `𝓝[>] 0`. -/
  | regular (hp : Expr)
  /-- The coefficient is nonpositive, with a proof `hc` of `c ≤ 0`. -/
  | nonpos (hc : Expr)
  /-- The degree is singular and the coefficient negative, with proofs `hc` of `c < 0` and `hp`
  of `0 < p` at `atTop`, `p < 0` at `𝓝[>] 0`: `exp (c * t ^ p)` decays. -/
  | decay (hc hp : Expr)

/-- A proof of `IsBoundedUnder (· ≤ ·) l fun t ↦ c * t ^ p` for the monomial `m` bounded as in
`b`, by `isBoundedUnder_le_mul_rpow_atTop` or `isBoundedUnder_le_mul_rpow_nhdsGT` for a degree
which is not singular and `isBoundedUnder_le_mul_rpow_of_nonpos` otherwise. -/
meta def CanonicalFilter.boundMonomial (l : CanonicalFilter) (m : Monomial) :
    MonomialBound → MetaM Expr
  | .regular hp => match l with
    | .atTop => mkAppM ``isBoundedUnder_le_mul_rpow_atTop #[m.coeff, hp]
    | .nhdsGT => mkAppM ``isBoundedUnder_le_mul_rpow_nhdsGT #[m.coeff, hp]
  | .nonpos hc =>
    mkAppM ``isBoundedUnder_le_mul_rpow_of_nonpos #[l.eventuallyPos, hc, m.degree.expr]
  | .decay hc _ => do
    mkAppM ``isBoundedUnder_le_mul_rpow_of_nonpos
      #[l.eventuallyPos, ← mkAppM ``le_of_lt #[hc], m.degree.expr]

/-- A proof of `IsBoundedUnder (· ≤ ·) l S` for the sum `S` of the functions with the bounds `hs`,
by `isBoundedUnder_le_fun_add`; `S` is `fun _ ↦ 0` if there are none. -/
meta def boundSum (l : CanonicalFilter) : List Expr → MetaM Expr
  | [] =>
    have l : Q(Filter ℝ) := l.toExpr
    return q(isBoundedUnder_const (r := fun x₁ x₂ : ℝ ↦ x₁ ≤ x₂) (l := $l) (a := (0 : ℝ)))
  | [h] => return h
  | h :: hs => do mkAppM ``isBoundedUnder_le_fun_add #[h, ← boundSum l hs]

/-- A proof of `IsBoundedUnder (· ≤ ·) l v`, from the bounds `hs` of monomials whose sum is
eventually `v`. -/
meta def boundExponent? (l : CanonicalFilter) (v : Q(ℝ → ℝ)) (hs : List Expr) :
    TacticM (Option Expr) := do
  let hS ← boundSum l hs
  let some (S : Q(ℝ → ℝ)) := (← instantiateMVars (← inferType hS)).getAppArgs.back? | return none
  let some hid ← proveIdentity? S v | return none
  have lE : Q(Filter ℝ) := l.toExpr
  let heq ← mkExpectedTypeHint (← mkAppM ``Filter.Eventually.mono #[l.eventuallyPos, hid])
    q($S =ᶠ[$lE] $v)
  mkAppM ``isBoundedUnder_le_of_eventuallyEq #[heq, hS]

/-! ### Signs -/

/-- The lemmas pushing a negation inwards, so that `0 < -c` becomes a goal for `positivity`
when `c` is, for instance, `-π`, `-1 * b⁻¹`, or a sum such as `-2 * π + -π * r`, the coefficient
of the product `rexp (-2 * π * t) * rexp (-π * r * t)`, which becomes `2 * π + π * r`. -/
meta def negLemmas : List Name :=
  [``neg_add, ``neg_neg, ``neg_mul, ``mul_neg, ``one_mul, ``mul_one]

/-- The simplification of `0 < -c`, or of `0 ≤ -c` if not `strict`, by `simp only` with
`negLemmas`, which pushes the negation inwards: `0 < n` for `c = -1 * n`. -/
meta def negCondition (c : Q(ℝ)) (strict : Bool) : MetaM Simp.Result := do
  let p : Q(Prop) := if strict then q(0 < -$c) else q(0 ≤ -$c)
  return (← simp p (← Simp.Context.ofNames negLemmas (simpOnly := true))).1

/-- A proof of `c < 0`, or of `c ≤ 0` if not `strict`, from a proof `h` of the simplified
statement of `r = negCondition c strict`, by `neg_pos`, respectively `neg_nonneg`. -/
meta def ofNegCondition (c : Q(ℝ)) (strict : Bool) (r : Simp.Result) (h : Expr) :
    MetaM Expr := do
  let h ← r.mkEqMPR h
  if strict then
    have h : Q(0 < -$c) := h
    return q(neg_pos.mp $h)
  have h : Q(0 ≤ -$c) := h
  return q(neg_nonneg.mp $h)

/-- A proof of `c < 0`, or of `c ≤ 0` if not `strict`, by the discharger: asked as it is, then as
`0 < -c`, respectively `0 ≤ -c`, with the negation pushed inwards by `simp only` with
`negLemmas` (see `negCondition`). -/
meta def proveNonpos? (disch : TSyntax ``Parser.Tactic.tacticSeq) (c : Q(ℝ)) (strict : Bool) :
    TacticM (Option Expr) := do
  if let some h ← discharge? disch (if strict then q($c < 0) else q($c ≤ 0)) then return h
  let r ← negCondition c strict
  let some h ← discharge? disch r.expr | return none
  ofNegCondition c strict r h

/-- A proof of `c < 0`, or of `c ≤ 0` if not `strict`, with its side goals: the statement which
`proveNonpos?` asks of the discharger last, `negCondition c strict`, such as `0 < n` for
`c = -1 * n`, is proved or left by `proveOrLeaveCondition?`; `none` if `norm_num` refutes it. -/
meta def proveOrLeaveNonpos? (disch : TSyntax ``Parser.Tactic.tacticSeq) (c : Q(ℝ))
    (strict : Bool) : TacticM (Option (Expr × List MVarId)) := do
  let r ← negCondition c strict
  let some (h, goals) ← proveOrLeaveCondition? disch r.expr | return none
  return some (← ofNegCondition c strict r h, goals)

/-- A proof of the condition `p` on a degree with value `value?`: if the degree is a numeral, by
`norm_num` when `holds` is true of its value, and otherwise by the discharger. -/
meta def proveDegreeCondition? (disch : TSyntax ``Parser.Tactic.tacticSeq) (value? : Option ℚ)
    (holds : ℚ → Bool) (p : Q(Prop)) : TacticM (Option Expr) := do
  let some q := value? | discharge? disch p
  unless holds q do return none
  let r ← normNumSimp p
  unless r.expr.isConstOf ``True do return none
  return some (← mkOfEqTrue (← r.getProof))

/-- The bound of the monomial `m` along `l`: `MonomialBound.regular` if its degree is proved not
singular, `MonomialBound.decay` if it is proved singular and its coefficient negative, and
otherwise `MonomialBound.nonpos` if its coefficient is proved nonpositive. -/
meta def monomialBound? (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (m : Monomial) : TacticM (Option MonomialBound) := do
  let d := m.degree
  if let some hp ← proveDegreeCondition? disch d.value? (!l.isSingular ·)
      (l.regularCondition d.expr) then
    return some (.regular hp)
  if let some hp ← proveDegreeCondition? disch d.value? l.isSingular
      (l.singularCondition d.expr) then
    if let some hc ← proveNonpos? disch m.coeff true then return some (.decay hc hp)
  return (← proveNonpos? disch m.coeff false).map .nonpos

/-! ### Absorption of monomials -/

/-- The condition that the degree `p` is strictly more singular than the degree `q`: `q < p` at
`atTop`, `p < q` at `𝓝[>] 0`. -/
meta def CanonicalFilter.absorbCondition (l : CanonicalFilter) (p q : Q(ℝ)) : Q(Prop) :=
  match l with
  | .atTop => q($q < $p)
  | .nhdsGT => q($p < $q)

/-- The lemma by which a monomial `c * t ^ p` with `c < 0` absorbs a monomial `d * t ^ q` of less
singular degree along `l`. -/
meta def CanonicalFilter.absorbLemma : CanonicalFilter → Name
  | .atTop => ``isBoundedUnder_le_mul_rpow_add_mul_rpow_atTop
  | .nhdsGT => ``isBoundedUnder_le_mul_rpow_add_mul_rpow_nhdsGT

/-- Whether the monomial `w` may absorb the monomial `m` along `l`, as far as the values of the
degrees tell: false only if both degrees are numerals and that of `w` is not singular or not
strictly more singular than that of `m`. -/
meta def CanonicalFilter.mayAbsorb (l : CanonicalFilter) (w m : Monomial) : Bool :=
  match w.degree.value?, m.degree.value? with
  | some p, some q => l.isSingular p && l.isSingular (p - q)
  | _, _ => true

/-- A proof of the condition that the degree `p` is strictly more singular than the degree `q`
(see `CanonicalFilter.absorbCondition`): decided from their values if both are numerals, since
`p - q` is then singular exactly when the condition holds, and otherwise asked of the
discharger. -/
meta def proveAbsorbCondition? (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (p q : Degree) : TacticM (Option Expr) :=
  proveDegreeCondition? disch ((· - ·) <$> p.value? <*> q.value?) l.isSingular
    (l.absorbCondition p.expr q.expr)

/-- Proofs of `IsBoundedUnder (· ≤ ·) l fun t ↦ c / (2 * n) * t ^ p + d * t ^ q` for each of the
`n` monomials `d * t ^ q` of `ms`, absorbed by the monomial `w = c * t ^ p` with `hc : c < 0`, if
the degree of `w` is proved strictly more singular than each of theirs. Together they bound the
sum of the monomials `ms` and of `(c / 2) * t ^ p`. -/
meta def absorbMonomials? (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (w : Monomial) (hc : Expr) (ms : List Monomial) : TacticM (Option (List Expr)) := do
  have c : Q(ℝ) := w.coeff
  have hc : Q($c < 0) := hc
  have k : Q(ℝ) := ← mkNumeral q(ℝ) (2 * ms.length)
  let r ← normNumSimp q((0 : ℝ) < $k)
  unless r.expr.isConstOf ``True do return none
  have hk : Q((0 : ℝ) < $k) := ← mkOfEqTrue (← r.getProof)
  let hc' : Q($c / $k < 0) := q(div_neg_of_neg_of_pos $hc $hk)
  let mut hs := #[]
  for m in ms do
    let some hpq ← proveAbsorbCondition? l disch w.degree m.degree | return none
    hs := hs.push (← mkAppM l.absorbLemma #[hc', hpq, m.coeff])
  return some hs.toList

/-! ### Classification of exponents -/

/-- An upper bound of an exponent `u` along a canonical filter `l`. -/
meta inductive ExponentBound where
  /-- `fun t ↦ u t - c * t ^ p` is eventually bounded above, for a coefficient `c` and a singular
  degree `p`, with proofs `hc : c < 0`, `hp` that `p` is singular (`0 < p` at `atTop`, `p < 0` at
  `𝓝[>] 0`) and `hu` of the bound. -/
  | decay (c p hc hp hu : Expr)
  /-- `u` is eventually bounded above, with the proof `hu`. -/
  | bounded (hu : Expr)

/-- The upper bound of the exponent `u` along `l`, from its monomials `p`, with their bounds
`bounds` (`none` for a monomial which is not bounded):
* if every monomial is bounded, `ExponentBound.decay`, with the first monomial bounded by
  `MonomialBound.decay` as witness, or else `ExponentBound.bounded`;
* otherwise, `ExponentBound.decay` with the witness `(c / 2) * t ^ p`, for the first monomial
  `c * t ^ p` bounded by `MonomialBound.decay` whose degree is proved strictly more singular than
  that of each monomial which is not bounded (see `absorbMonomials?`). The witness is halved only
  then, so that the classification of the other exponents is unchanged. -/
meta def boundOfMonomials? (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (u : Q(ℝ → ℝ)) (p : List Monomial) (bounds : List (Option MonomialBound)) :
    OptionT TacticM ExponentBound := do
  let bounded : List (Monomial × MonomialBound) :=
    (p.zip bounds).filterMap fun (m, b) ↦ b.map (m, ·)
  if bounded.length == p.length then
    let hs ← bounded.mapM fun (m, b) ↦ l.boundMonomial m b
    let some i := bounded.findIdx? (· matches (_, .decay ..))
      | return .bounded (← OptionT.mk <| boundExponent? l u hs)
    let some (w, MonomialBound.decay hc hp) := bounded[i]? | failure
    have c : Q(ℝ) := w.coeff
    have deg : Q(ℝ) := w.degree.expr
    let hu ← OptionT.mk <| boundExponent? l q(fun t ↦ $u t - $c * t ^ $deg) (hs.eraseIdx i)
    return .decay c deg hc hp hu
  let unbounded := (p.zip bounds).filterMap fun (m, b) ↦ if b.isNone then some m else none
  for (w, b) in bounded, i in [:bounded.length] do
    let .decay hc hp := b | continue
    let habs? : Option (List Expr) ← (absorbMonomials? l disch w hc unbounded : TacticM _)
    let some habs := habs? | continue
    let hs ← (bounded.eraseIdx i).mapM fun (m, b) ↦ l.boundMonomial m b
    have c : Q(ℝ) := w.coeff
    have hc : Q($c < 0) := hc
    have deg : Q(ℝ) := w.degree.expr
    let hu? : Option Expr ←
      (boundExponent? l q(fun t ↦ $u t - $c / 2 * t ^ $deg) (hs ++ habs) : TacticM _)
    let some hu := hu? | continue
    return .decay q($c / 2) deg q(div_neg_of_neg_of_pos $hc two_pos) hp hu
  failure

/-- How the classification of an exponent may resolve an *unknown* monomial `c * t ^ p`, one which
`monomialBound?` does not bound and which is not absorbed: by absorbing it into a decaying monomial
of strictly more singular degree, or by a condition on the sign of `c` left as a side goal (see
`resolveSigns?`). -/
meta inductive SignResolution where
  /-- Not at all: the exponent is not classified. -/
  | none
  /-- For a term which is decided when its exponent is bounded above: by absorption into a
  monomial bounded by `MonomialBound.decay`, if there is one, and otherwise by the condition
  `c ≤ 0`, which bounds the monomial whatever its degree. -/
  | nonpos
  /-- As the decay of the exponent requires: by absorption into a witness of the decay, and
  otherwise by `c ≤ 0`; the witness is a monomial bounded by `MonomialBound.decay` or, if there is
  none, an unknown monomial whose degree is proved singular, with the condition `c < 0`. -/
  | decay

/-- The indices, among the indexed monomials `ms`, of those which the monomial `w` absorbs: those
than whose degree that of `w` is proved strictly more singular (see `proveAbsorbCondition?`). -/
meta def absorbedBy (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (w : Monomial) (ms : List (Nat × Monomial)) : TacticM (List Nat) :=
  ms.filterMapM fun (i, m) ↦ do
    return if (← proveAbsorbCondition? l disch w.degree m.degree).isSome then some i else none

/-- The bounds of the monomials `p`, given their bounds `bounds` by `monomialBound?`, with the
unknown monomials (`none`) resolved as `signs` allows, and the side goals left, in the order of the
monomials.

The *witness* is chosen among the candidates: the monomials bounded by `MonomialBound.decay`, or,
if there are none and `signs` is `SignResolution.decay`, the unknown monomials whose degree is
proved singular. It is the candidate which absorbs the most unknown monomials (see `absorbedBy`),
the first one in case of a tie; with numeral degrees, the most singular one. The unknown monomials
which it absorbs stay `none`, to be absorbed by `boundOfMonomials?`; a witness which is an unknown
monomial gets the condition `c < 0`, and every other unknown monomial the condition `c ≤ 0`, by
`proveOrLeaveNonpos?`. With no candidate, in the mode `SignResolution.nonpos`, every unknown
monomial gets `c ≤ 0`.

Fails if `signs` is `SignResolution.none`, if the decay requires a witness and there is no
candidate, or if `norm_num` refutes a condition. -/
meta def resolveSigns? (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (signs : SignResolution) (p : List Monomial) (bounds : List (Option MonomialBound)) :
    OptionT TacticM (List (Option MonomialBound) × List MVarId) := do
  if signs matches .none then failure
  let indexed := (p.zip bounds).zipIdx
  let unknown := indexed.filterMap fun ((m, b), i) ↦ if b.isNone then some (i, m) else none
  let mut candidates : Array (Nat × Monomial × Option Expr) := (indexed.filterMap
    fun ((m, b), i) ↦ if b matches some (.decay ..) then some (i, m, none) else none).toArray
  if candidates.isEmpty && signs matches .decay then
    for (i, m) in unknown do
      let hp? : Option Expr ← (proveDegreeCondition? disch m.degree.value? l.isSingular
        (l.singularCondition m.degree.expr) : TacticM _)
      if let some hp := hp? then candidates := candidates.push (i, m, some hp)
    if candidates.isEmpty then
      if ← isTracingEnabledFor `Tactic.endpoint_integrability then
        let degrees ← unknown.flatMapM fun (_, m) ↦ do
          return ([.text "; the degree of ", .expr (← m.display), .text " is not proved to \
            satisfy ", .expr (l.singularCondition m.degree.expr)] : List MsgPart)
        trace[Tactic.endpoint_integrability] "{← sentence <| [.text "the exponent is not proved to \
          decay: no monomial `c * t ^ p` has `c` proved negative and `t ^ p` proved unbounded at \
          this end"] ++ degrees}"
      failure
  let mut witness? : Option (Nat × Option Expr × List Nat) := none
  for (i, w, hp?) in candidates do
    let absorbed ← (absorbedBy l disch w (unknown.filter (·.1 != i)) : TacticM _)
    if witness?.all (·.2.2.length < absorbed.length) then witness? := some (i, hp?, absorbed)
  let mut result := #[]
  let mut goals := #[]
  for ((m, b), i) in indexed do
    if b.isSome then
      result := result.push b
      continue
    if witness?.any (·.2.2.contains i) then
      result := result.push none
      continue
    let hp? := witness?.bind fun (j, hp?, _) ↦ if i == j then hp? else none
    let r? : Option (Expr × List MVarId) ← proveOrLeaveNonpos? disch m.coeff hp?.isSome
    let some (hc, gs) := r?
      | have c : Q(ℝ) := ← displaySimp m.coeff
        let (cond, role) := if hp?.isSome then (q($c < 0), "makes the exponent decay")
          else (q($c ≤ 0), "is bounded above")
        trace[Tactic.endpoint_integrability] "{← sentence ["the monomial ", .expr (← m.display),
          s!" of the exponent {role} if ", .expr cond, ", which is false"]}"
        failure
    result := result.push (some (if let some hp := hp? then .decay hc hp else .nonpos hc))
    goals := goals ++ gs
  return (result.toList, goals.toList)

/-- The upper bound of the exponent `u` along `l`, with its side goals, if `u` is a polynomial with
real degrees each of whose monomials is bounded by `monomialBound?` or absorbed by a monomial
bounded by `MonomialBound.decay` (see `boundOfMonomials?`), with no side goal; failing it, if
`signs` is not `SignResolution.none`, with the unknown monomials resolved by absorption into a
witness of the decay or by conditions on their coefficients, left as side goals (see
`resolveSigns?`), and the bound assembled by `boundOfMonomials?` again. If this fails, the state
is restored: no goal is left behind.

With `SignResolution.none`, the monomials are bounded in order, and the classification fails at
the first one which is not bounded unless `CanonicalFilter.mayAbsorb` allows another monomial to
absorb it. -/
meta def exponentBoundLeaving? (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (signs : SignResolution) (u : Q(ℝ → ℝ)) : OptionT TacticM (ExponentBound × List MVarId) := do
  let some p ← exponentPolynomial? u
    | unless signs matches .none do
        trace[Tactic.endpoint_integrability] "{← sentence ["the exponent ", .expr (← displayFun u),
          " is not a polynomial in `t` with real degrees"]}"
      failure
  let mut bounds : Array (Option MonomialBound) := #[]
  for m in p, j in [:p.length] do
    let b : Option MonomialBound ← (monomialBound? l disch m : TacticM _)
    if b.isNone && signs matches .none &&
        !(p.zipIdx.any fun (w, i) ↦ i != j && l.mayAbsorb w m) then
      failure
    bounds := bounds.push b
  let bound? : Option ExponentBound ← (boundOfMonomials? l disch u p bounds.toList).run
  if let some bound := bound? then return (bound, [])
  let s ← Tactic.saveState
  let r? : Option (ExponentBound × List MVarId) ← (do
    let (bounds, goals) ← resolveSigns? l disch signs p bounds.toList
    let bound? : Option ExponentBound ← (boundOfMonomials? l disch u p bounds).run
    let some bound := bound?
      | trace[Tactic.endpoint_integrability] "{← sentence ["the bound of the exponent ",
          .expr (← displayFun u), " is not proved from the bounds of its monomials"]}"
        failure
    return (bound, goals) : OptionT TacticM _).run
  let some r := r? | s.restore; failure
  return r

/-- The upper bound of the exponent `u` along `l`, with no side goal: `exponentBoundLeaving?` with
`SignResolution.none`. The comparisons of the engine classify exponents by it. -/
meta def exponentBound? (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (u : Q(ℝ → ℝ)) : OptionT TacticM ExponentBound :=
  Prod.fst <$> exponentBoundLeaving? l disch .none u

end Mathlib.Tactic.EndpointIntegrability
