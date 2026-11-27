/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
module

public import SpherePacking.Tactic.EndpointIntegrability.Compare

/-!
# The rules of the comparison engine of `endpoint_integrability`

The rules of the engine of `SpherePacking.Tactic.EndpointIntegrability.Compare`, registered with
the attribute `endpoint_compare`. Each rule applies one lemma of the scale
`SpherePacking.Tactic.EndpointIntegrability.Scale`. A module which runs the engine must import
this one.

* The atoms `Real.exp g` and `Complex.exp z`, whose exponent `g`, respectively real part `z.re`,
  is a polynomial in `t` with real degrees (see `exponentPolynomial?`), and `Real.log t` (the
  logarithm of the variable itself), which are exact. The exponential of another exponent, such
  as `exp (sin t)`, is left to the continuity at `0` at `𝓝[>] 0` (see `continuousAtResult?`).
* Products `x * y`, natural powers `x ^ n` (`n` free of `t`; when the majorant of `x` is a sum,
  `n` must be a numeral and the power is expanded), integer powers `x ^ n` with `n` a numeral (as
  natural powers and their inverses), negations `-x`, norms `‖x‖`, absolute values `|x|` and the
  cast `ℝ → ℂ`, which are exact when their arguments are.
* Real powers `x ^ p` (`p` free of `t`), square roots `√x` and complex powers `(x : ℂ) ^ s` of a
  real `x` (`s` free of `t`), when the majorant of `x` is a comparison function `powExp a k u`
  (see `powerResult?`): exact, `Θ(powExp (p * a) (p * k) (p • u))` with `p` equal to
  `1 / 2`, respectively `s.re`, if the result of `x` is exact and `positivity` proves `0 ≤ x`,
  respectively `0 < x`, from `0 < t`; otherwise, for real powers if `0 ≤ p` is proved and for
  square roots, only `O`.
* Quotients `x / y`, bounded as `x * y⁻¹`. Inverses (see `invRule`): the inverse of a product,
  bounded as the product of the inverses, of a quotient `x / y`, as `y / x`, of a natural power,
  as the power of the inverse, and of an inverse, as the function itself, with no side condition,
  exact when the result they reduce to is; otherwise, or if a part is not bounded, the inverse of
  any expression whose result is exact, `Θ(powExp a k u)`, is exact, `Θ(powExp (-a) (-k) (-u))`.
  Thus `t⁻¹`, `(exp g)⁻¹`, `|log t|⁻¹` and `‖(t : ℂ) + I‖⁻¹` are exact.
* Sums `x + y` and differences `x - y`: exact if one summand dominates the other, or, for a real
  sum, if the summands have the same order and are nonnegative (see `dominantSum?`), and
  otherwise bounded by the sum of the majorants. Products of majorants are distributed over
  their sums, as in `isBigO_mul_of_isBigO_mul`.
* The bounded factors `Real.sin _` and `Real.cos _`, which are not exact. Along `𝓝[>] 0`, the
  engine itself bounds by `O(1)` any `e` continuous at `0`, after the rules.

At most one of these rules applies to an expression.

## Sums and their inverses

The engine knows the order of a sum only through exactness. In `x + y` or `x - y`, the summand
`x` dominates if its result is exact, `Θ(powExp a k u)`, and the majorant of `y` is a comparison
function `powExp b j v` with `powExp b j v =o[l] powExp a k u` (see `isLittleO?`); the sum is
then exact, `Θ(powExp a k u)`. The negligibility is decided from the exponent `v - u`, classified
by `exponentBound?`: it holds if `v - u` decays exponentially, or if it is bounded above and
either `b < a` at `atTop`, respectively `a < b` at `𝓝[>] 0`, or `b = a` and `j < k` (see
`logDominance?`), the conditions on the powers being proved by `proveCondition?` (the discharger,
then `norm_num`). Thus `1 + log t` is `Θ(log t)` at `atTop`.

If neither summand dominates, a sum `x + y`, but not a difference, is still exact if the result of
one summand is exact, `Θ(powExp a k u)`, the majorant of the other one is a comparison function
`powExp b j v` of the same order, `b = a` and `j = k` being proved by `proveCondition?` and
`v - u` being bounded above, and `positivity` proves that both summands are nonnegative from
`0 < t` (see `sameOrderSum?`): no cancellation is then possible. Thus `t ^ 2 + (1 + t) ^ 2` and
`t + 2 * t` are `Θ(t ^ 2)` and `Θ(t)`, but not `t ^ 2 + (1 - t) * t`, which is `t`, nor sums of
complex values. Otherwise, as in `1 + t ^ 2 * cos t ^ 2`, the sum is not exact.

The inverse of an exact sum `Θ(powExp a k u)`, as of any exact result, is
`Θ(powExp (-a) (-k) (-u))`. There is no rule for the inverse of a sum
which is not exact; at `𝓝[>] 0`, the continuity at `0` of the inverse is still tried as a bounded
factor. No sign condition is needed: `x + y` may vanish, or change sign, away from the end.
-/

@[expose] public section

open Lean Meta Elab Tactic Qq Asymptotics

namespace Mathlib.Tactic.EndpointIntegrability

/-! ### Helpers -/

/-- The `Result` of `e` from the result `r` of a subexpression with the same majorant `M`: the
lemma `theta?`, if any, concluding `(fun t ↦ e) =Θ[l] M` from `r.proof` when `r` is exact, and
otherwise the lemma `bigO` concluding `(fun t ↦ e) =O[l] M` from `r.isBigO`. -/
meta def sameMajorant (e : Expr) (r : Result) (bigO : Name) (theta? : Option Name := none) :
    CompareM Result := do
  if let some theta := theta?.filter fun _ ↦ r.exact then
    return ← mkResult e r.majorant (← mkAppM theta #[r.proof]) true
  mkResult e r.majorant (← mkAppM bigO #[← r.isBigO])

/-- A proof of `0 ≤ᶠ[l] M`. -/
meta def Majorant.nonneg : Majorant → CompareM Expr
  | .powExp a k u => do
    mkAppOptM ``eventually_nonneg_powExp #[← filterExpr, a, k, u, ← eventuallyPos]
  | .add m₁ m₂ => do mkAppM ``eventually_nonneg_add #[← m₁.nonneg, ← m₂.nonneg]

/-- A proof of `∀ᶠ t in l, 0 < e`, if `strict`, or of `∀ᶠ t in l, 0 ≤ e`, from a proof of
`∀ t, 0 < t → 0 < e`, respectively `0 ≤ e`, by `positivity`. -/
meta def eventuallyPositive? (e : Expr) (strict : Bool) : CompareM (Option Expr) := do
  have t : Q(ℝ) := (← read).var
  have e : Q(ℝ) := e
  let type ← mkForallFVars #[t] (← mkArrow q(0 < $t) (if strict then q(0 < $e) else q(0 ≤ $e)))
  let proof ← mkFreshExprMVar type
  let closed ← attempt proof.mvarId! do
    let (_, g) ← proof.mvarId!.introN 2
    return (← evalTacticAt (← `(tactic| positivity)) g).isEmpty
  unless closed do return none
  mkAppM ``Filter.Eventually.mono #[← eventuallyPos, ← instantiateMVars proof]

/-! ### Atoms -/

/-- The rule for the atoms `Real.exp g` and `Complex.exp z`: `isTheta_exp_powExp` and
`isTheta_cexp_powExp`, applied to the exponent, if the exponent `g`, respectively the real part
`z.re`, is a polynomial in `t` with real degrees, as parsed by `exponentPolynomial?`. Otherwise,
as for `exp (sin t)`, the exponent could not be classified, and the rule does not apply. -/
@[endpoint_compare Real.exp _, Complex.exp _]
meta def expRule : Rule where
  eval e := do
    let some (name, z, u) := match_expr e with
        | Real.exp z => some (``isTheta_exp_powExp, z, z)
        | Complex.exp z => some (``isTheta_cexp_powExp, z, mkApp (.const ``Complex.re []) z)
        | _ => none
      | return none
    if (← exponentPolynomial? (← lam u)).isNone then return none
    termResult e (← mkAppOptM name #[← filterExpr, ← lam z])

/-- The rule for the atom `Real.log t`: `isTheta_log_powExp`. Its inverse is given by
`invRule`. -/
@[endpoint_compare Real.log _]
meta def logRule : Rule where
  eval e := do
    let_expr Real.log y := e | return none
    unless y == (← read).var do return none
    termResult e (← mkAppOptM ``isTheta_log_powExp #[← filterExpr])

/-! ### Products and powers -/

/-- The product of two majorants, distributed over their sums: a majorant `p` and a proof of
`(fun t ↦ m₁ t * m₂ t) =O[l] p`, as in `isBigO_mul_of_isBigO_mul`. -/
meta partial def mulMajorants (m₁ m₂ : Majorant) : CompareM Result := do
  let t := (← read).var
  let e ← mkAppM ``HMul.hMul #[(mkApp m₁.toExpr t).headBeta, (mkApp m₂.toExpr t).headBeta]
  let distribute (name : Name) (r₁ r₂ : Result) : CompareM Result := do
    mkResult e (.add r₁.majorant r₂.majorant) (← mkAppM name
      #[← r₁.isBigO, ← r₂.isBigO, ← r₁.majorant.nonneg, ← r₂.majorant.nonneg])
  match m₁, m₂ with
  | .add m₁₁ m₁₂, _ => distribute ``isBigO_add_mul (← mulMajorants m₁₁ m₂) (← mulMajorants m₁₂ m₂)
  | _, .add m₂₁ m₂₂ => distribute ``isBigO_mul_add (← mulMajorants m₁ m₂₁) (← mulMajorants m₁ m₂₂)
  | .powExp a k u, .powExp b j v =>
    termResult e (← mkAppOptM ``isBigO_powExp_mul_powExp #[← filterExpr, a, b, k, j, u, v,
      ← eventuallyPos, ← tendstoAbsLog])

/-- The product `x * y` with results `r₁` and `r₂` for `x` and `y`: if both majorants are
comparison functions, `isTheta_mul_powExp` if both results are exact and `isBigO_mul_powExp`
otherwise; `isBigO_mul_of_isBigO_mul` if one of them is a sum. -/
meta def mulResults (e : Expr) (r₁ r₂ : Result) : CompareM Result := do
  if let (.powExp .., .powExp ..) := (r₁.majorant, r₂.majorant) then
    if r₁.exact && r₂.exact then
      return ← termResult e (← mkAppM ``isTheta_mul_powExp
        #[← eventuallyPos, ← tendstoAbsLog, r₁.proof, r₂.proof])
    return ← termResult e (← mkAppM ``isBigO_mul_powExp
      #[← eventuallyPos, ← tendstoAbsLog, ← r₁.isBigO, ← r₂.isBigO])
  let p ← mulMajorants r₁.majorant r₂.majorant
  mkResult e p.majorant
    (← mkAppM ``isBigO_mul_of_isBigO_mul #[← r₁.isBigO, ← r₂.isBigO, ← p.isBigO])

/-- The rule for products `x * y`. -/
@[endpoint_compare _ * _]
meta def mulRule : Rule where
  eval e := do
    let_expr HMul.hMul _ _ _ _ x y := e | return none
    mulResults e (← compare x) (← compare y)

/-- The power `x ^ n` of `x` with result `r`, for a numeral `n ≥ 1`, expanded into a product by
`isBigO_pow_one` and `isBigO_pow_succ`. -/
meta def expandPow (e x : Expr) (r : Result) (n : Nat) : CompareM Result := do
  let hx ← r.isBigO
  let mut acc ← mkResult (← mkAppM ``HPow.hPow #[x, mkNatLit 1]) r.majorant
    (← mkAppM ``isBigO_pow_one #[hx])
  for k in [1:n] do
    let p ← mulMajorants acc.majorant r.majorant
    acc ← mkResult (← mkAppM ``HPow.hPow #[x, mkNatLit (k + 1)]) p.majorant
      (← mkAppM ``isBigO_pow_succ #[acc.proof, hx, p.proof])
  mkResult e acc.majorant acc.proof

/-- The rule for natural powers `x ^ n`, with `n` free of `t`: `isTheta_pow_powExp` if the result
of `x` is exact, `isBigO_pow_powExp` otherwise. -/
@[endpoint_compare _ ^ (_ : ℕ)]
meta def powRule : Rule where
  eval e := do
    let_expr HPow.hPow _ β _ _ x n := e | return none
    unless β.isConstOf ``Nat do return none
    if ← dependsOnVar n then return none
    let r ← compare x
    if let .powExp .. := r.majorant then
      let name := if r.exact then ``isTheta_pow_powExp else ``isBigO_pow_powExp
      return ← termResult e (← mkAppM name #[← eventuallyPos, r.proof, n])
    let some k := n.numeral?.filter (0 < ·) | throwUnbounded (← tracedSentence do
      return ["no bound for the power ", e, " of a sum: its exponent is not a positive numeral"])
    expandPow e x r k

/-- The rule for integer powers `x ^ n` with `n` a numeral: as the natural power `x ^ n` if
`0 ≤ n` (`isTheta_zpow_natCast` or `isBigO_zpow_natCast`), and as the inverse `(x ^ (-n))⁻¹`
otherwise (`isTheta_zpow_neg_natCast` or `isBigO_zpow_neg_natCast`). -/
@[endpoint_compare _ ^ (_ : ℤ)]
meta def zpowRule : Rule where
  eval e := do
    let_expr HPow.hPow _ β _ _ x m := e | return none
    unless β.isConstOf ``Int do return none
    let some n ← getIntValue? m | return none
    let pow ← mkAppM ``HPow.hPow #[x, mkNatLit n.natAbs]
    if 0 ≤ n then
      return ← sameMajorant e (← compare pow) ``isBigO_zpow_natCast ``isTheta_zpow_natCast
    sameMajorant e (← compare (← mkAppM ``Inv.inv #[pow])) ``isBigO_zpow_neg_natCast
      ``isTheta_zpow_neg_natCast

/-- The result of a power `e` of `x`, given the result `r` of `x`, if its majorant is a comparison
function: `theta` applied to the proof of `r` and to the proof of
`∀ᶠ t in l, 0 < x` if `strict`, or `∀ᶠ t in l, 0 ≤ x` otherwise, if `r` is exact and
`eventuallyPositive?` proves this; otherwise `bigO?` applied to the proof of `Result.isBigO r`, if
it applies. -/
meta def powerResult? (e x : Expr) (r : Result) (strict : Bool)
    (theta : Expr → Expr → CompareM Expr) (bigO? : Expr → CompareM (Option Expr)) :
    CompareM (Option Result) := do
  let .powExp .. := r.majorant | return none
  if r.exact then
    if let some h ← eventuallyPositive? x strict then return ← termResult e (← theta r.proof h)
  let some proof ← bigO? (← r.isBigO) | return none
  termResult e proof

/-- The rule for real powers `x ^ p`, with `p` free of `t`, if the result of `x` is a comparison
function: `isTheta_rpow_powExp` if it is exact and `x` is eventually
nonnegative, and otherwise `isBigO_rpow_powExp` if `proveCondition?` proves `0 ≤ p`. -/
@[endpoint_compare (_ : ℝ) ^ (_ : ℝ)]
meta def rpowRule : Rule where
  eval e := do
    let_expr HPow.hPow α β _ _ x p := e | return none
    unless α.isConstOf ``Real && β.isConstOf ``Real do return none
    if ← dependsOnVar p then return none
    let r ← compare x
    let hl ← eventuallyPos
    powerResult? e x r false (fun hx h ↦ mkAppM ``isTheta_rpow_powExp #[hl, hx, h, p]) fun hx ↦ do
      have p : Q(ℝ) := p
      let some hp ← proveCondition? (← read).disch q(0 ≤ $p) | return none
      mkAppM ``isBigO_rpow_powExp #[hl, hx, hp]

/-- The rule for square roots `√x`, if the result of `x` is a comparison function:
`isTheta_sqrt_powExp` if it is exact and `x` is eventually nonnegative, and otherwise
`isBigO_sqrt_powExp`. -/
@[endpoint_compare Real.sqrt _]
meta def sqrtRule : Rule where
  eval e := do
    let_expr Real.sqrt x := e | return none
    let r ← compare x
    let hl ← eventuallyPos
    powerResult? e x r false (fun hx h ↦ mkAppM ``isTheta_sqrt_powExp #[hl, hx, h]) fun hx ↦
      some <$> mkAppM ``isBigO_sqrt_powExp #[hl, hx]

/-- The rule for complex powers `(x : ℂ) ^ s` of a real `x`, with `s` free of `t`:
`isTheta_cpow_powExp`, if the result of `x` is exact, a comparison function, and `x` is eventually
positive. The rule does not apply otherwise. -/
@[endpoint_compare (_ : ℂ) ^ (_ : ℂ)]
meta def cpowRule : Rule where
  eval e := do
    let_expr HPow.hPow α β _ _ y s := e | return none
    unless α.isConstOf ``Complex && β.isConstOf ``Complex do return none
    if ← dependsOnVar s then return none
    let_expr Complex.ofReal x := y | return none
    let r ← compare x
    let hl ← eventuallyPos
    powerResult? e x r true (fun hx h ↦ mkAppM ``isTheta_cpow_powExp #[hl, hx, h, s]) fun _ ↦
      return none

/-! ### Negations, norms, absolute values and casts -/

/-- The rule for `-x`: `Asymptotics.IsBigO.neg_left`, or `Asymptotics.IsTheta.neg_left`. -/
@[endpoint_compare -_]
meta def negRule : Rule where
  eval e := do
    let_expr Neg.neg _ _ x := e | return none
    sameMajorant e (← compare x) ``IsBigO.neg_left ``IsTheta.neg_left

/-- The rule for `‖x‖`: `Asymptotics.IsBigO.norm_left`, or `Asymptotics.IsTheta.norm_left`. -/
@[endpoint_compare ‖_‖]
meta def normRule : Rule where
  eval e := do
    let_expr Norm.norm _ _ x := e | return none
    sameMajorant e (← compare x) ``IsBigO.norm_left ``IsTheta.norm_left

/-- The rule for `|x|`: `Asymptotics.IsBigO.abs_left`, or `Asymptotics.IsTheta.abs_left`. -/
@[endpoint_compare |_|]
meta def absRule : Rule where
  eval e := do
    let_expr abs _ _ _ x := e | return none
    sameMajorant e (← compare x) ``IsBigO.abs_left ``IsTheta.abs_left

/-- The rule for the cast `(x : ℂ)` of a real `x`: `Complex.isBigO_ofReal_left`, or
`Complex.isTheta_ofReal_left`. -/
@[endpoint_compare Complex.ofReal _]
meta def ofRealRule : Rule where
  eval e := do
    let_expr Complex.ofReal x := e | return none
    let r ← compare x
    let name := if r.exact then ``Complex.isTheta_ofReal_left else ``Complex.isBigO_ofReal_left
    let iff ← mkAppOptM name #[none, none, none, ← filterExpr, ← lam x, r.majorant.toExpr]
    mkResult e r.majorant (← mkAppM ``Iff.mpr #[iff, r.proof]) r.exact

/-! ### Sums -/

/-- The dominance lemma along the filter when the difference of the exponents decays
exponentially. -/
meta def CanonicalFilter.decayDominance : CanonicalFilter → Name
  | .atTop => ``isLittleO_powExp_atTop_of_mul_rpow
  | .nhdsGT => ``isLittleO_powExp_nhdsGT_of_mul_rpow

/-- The dominance lemma along the filter when the difference of the exponents is bounded
above. -/
meta def CanonicalFilter.powerDominance : CanonicalFilter → Name
  | .atTop => ``isLittleO_powExp_atTop_of_lt
  | .nhdsGT => ``isLittleO_powExp_nhdsGT_of_lt

/-- The condition on the powers `a` and `b` for `powExp b j v =o[l] powExp a k u` when `v - u` is
bounded above: `b < a` at `atTop`, `a < b` at `𝓝[>] 0`. -/
meta def CanonicalFilter.dominanceCondition (l : CanonicalFilter) (a b : Q(ℝ)) : Q(Prop) :=
  match l with
  | .atTop => q($b < $a)
  | .nhdsGT => q($a < $b)

/-- A proof of `powExp b j v =o[l] powExp a k u` by `isLittleO_powExp_of_log_lt`, given the
bound `hw` of `v - u`, if `proveCondition?` proves `b = a` and `j < k`. -/
meta def logDominance? (a b k j u v hw : Expr) : CompareM (Option Expr) := do
  have a : Q(ℝ) := a
  have b : Q(ℝ) := b
  have j : Q(ℝ) := j
  have k : Q(ℝ) := k
  let some hab ← proveCondition? (← read).disch q($b = $a) | return none
  let some hjk ← proveCondition? (← read).disch q($j < $k) | return none
  mkAppOptM ``isLittleO_powExp_of_log_lt #[none, a, b, k, j, u, v, ← eventuallyPos,
    ← tendstoAbsLog, hab, hjk, hw]

/-- A proof of `m₂ =o[l] m₁` for comparison functions `m₁ = powExp a k u` and
`m₂ = powExp b j v`, decided by the classification of `fun t ↦ v t - u t` by `exponentBound?`:
by `CanonicalFilter.decayDominance` if it decays exponentially; if it is bounded above, by
`CanonicalFilter.powerDominance` if `proveCondition?` proves
`CanonicalFilter.dominanceCondition`, and otherwise by `logDominance?`. -/
meta def isLittleO? (m₁ m₂ : Majorant) : CompareM (Option Expr) := do
  let (.powExp a k u, .powExp b j v) := (m₁, m₂) | return none
  have u : Q(ℝ → ℝ) := u
  have v : Q(ℝ → ℝ) := v
  let l := (← read).filter
  let some bound ← (exponentBound? l (← read).disch q(fun t ↦ $v t - $u t)).run | return none
  match bound with
  | .decay c n hc hn hw => mkAppOptM l.decayDominance #[a, b, k, j, u, v, c, hc, n, hn, hw]
  | .bounded hw =>
    let some h ← proveCondition? (← read).disch (l.dominanceCondition a b) |
      logDominance? a b k j u v hw
    mkAppOptM l.powerDominance #[a, b, k, j, u, v, h, hw]

/-- A proof of `m₂ =O[l] m₁` for comparison functions `m₁ = powExp a k u` and
`m₂ = powExp b j v` of the same order, by `isBigO_powExp_of_eq`, if `fun t ↦ v t - u t` is bounded
above, as classified by `exponentBound?`, and `proveCondition?` proves `b = a` and `j = k`. -/
meta def isBigOSameOrder? (m₁ m₂ : Majorant) : CompareM (Option Expr) := do
  let (.powExp a k u, .powExp b j v) := (m₁, m₂) | return none
  have a : Q(ℝ) := a
  have b : Q(ℝ) := b
  have j : Q(ℝ) := j
  have k : Q(ℝ) := k
  have u : Q(ℝ → ℝ) := u
  have v : Q(ℝ → ℝ) := v
  let disch := (← read).disch
  let some hab ← proveCondition? disch q($b = $a) | return none
  let some hjk ← proveCondition? disch q($j = $k) | return none
  let some (.bounded hw) ← (exponentBound? (← read).filter disch q(fun t ↦ $v t - $u t)).run
    | return none
  mkAppOptM ``isBigO_powExp_of_eq #[none, a, b, k, j, u, v, ← eventuallyPos, hab, hjk, hw]

/-- The real sum `e` of `x` and `y`, with the results `r₁` and `r₂`, as `Θ` of the majorant of one
of them, if this result is exact, the majorant of the other one is a comparison function of the
same order (see `isBigOSameOrder?`), and `eventuallyPositive?` proves that both summands are
eventually nonnegative, so that no cancellation is possible: `isTheta_add_of_nonneg` if the result
of `x` is exact, `isTheta_add_of_nonneg_right` if that of `y` is. -/
meta def sameOrderSum? (e x y : Expr) (r₁ r₂ : Result) : CompareM (Option Result) := do
  unless r₁.exact || r₂.exact do return none
  let (.powExp .., .powExp ..) := (r₁.majorant, r₂.majorant) | return none
  unless (← instantiateMVars (← inferType x)).isConstOf ``Real do return none
  let some hx ← eventuallyPositive? x false | return none
  let some hy ← eventuallyPositive? y false | return none
  if r₁.exact then
    if let some h ← isBigOSameOrder? r₁.majorant r₂.majorant then
      return ← termResult e (← mkAppM ``isTheta_add_of_nonneg
        #[r₁.proof, ← mkAppM ``IsBigO.trans #[← r₂.isBigO, h], hx, hy])
  if r₂.exact then
    if let some h ← isBigOSameOrder? r₂.majorant r₁.majorant then
      return ← termResult e (← mkAppM ``isTheta_add_of_nonneg_right
        #[← mkAppM ``IsBigO.trans #[← r₁.isBigO, h], r₂.proof, hx, hy])
  return none

/-- The sum, or difference if `sub`, `e` of `x` and `y`, with the results `r₁` and `r₂`, as `Θ` of
the majorant of one of them, if this result is exact and the majorant of the other one is a
comparison function proved negligible by `isLittleO?`: `isTheta_add_left` or `isTheta_sub_left`
if `x` dominates, `isTheta_add_right` or `isTheta_sub_right` if `y` does. Otherwise, for a sum,
the summands may have the same order (see `sameOrderSum?`). -/
meta def dominantSum? (e x y : Expr) (sub : Bool) (r₁ r₂ : Result) : CompareM (Option Result) := do
  if r₁.exact then
    if let some h ← isLittleO? r₁.majorant r₂.majorant then
      let name := if sub then ``isTheta_sub_left else ``isTheta_add_left
      return ← termResult e (← mkAppM name #[r₁.proof, ← r₂.isBigO, h])
  if r₂.exact then
    if let some h ← isLittleO? r₂.majorant r₁.majorant then
      let name := if sub then ``isTheta_sub_right else ``isTheta_add_right
      return ← termResult e (← mkAppM name #[← r₁.isBigO, r₂.proof, h])
  if sub then return none
  sameOrderSum? e x y r₁ r₂

/-- The rule for sums `x + y` and differences `x - y`: an exact result if one of them dominates,
or, for a sum, if they have the same order and are nonnegative (see `dominantSum?`), and
otherwise the sum of the majorants, by `isBigO_add_of_nonneg` and `isBigO_sub_of_nonneg`. -/
@[endpoint_compare _ + _, _ - _]
meta def addRule : Rule where
  eval e := do
    let some (sub, x, y) := match_expr e with
        | HAdd.hAdd _ _ _ _ x y => some (false, x, y)
        | HSub.hSub _ _ _ _ x y => some (true, x, y)
        | _ => none
      | return none
    let r₁ ← compare x
    let r₂ ← compare y
    if let some r ← dominantSum? e x y sub r₁ r₂ then return r
    let name := if sub then ``isBigO_sub_of_nonneg else ``isBigO_add_of_nonneg
    mkResult e (.add r₁.majorant r₂.majorant) (← mkAppM name
      #[← r₁.isBigO, ← r₂.isBigO, ← r₁.majorant.nonneg, ← r₂.majorant.nonneg])

/-! ### Quotients and inverses -/

/-- The rule for quotients `x / y`, bounded as `x * y⁻¹`: `isTheta_div` if this result is exact,
`isBigO_div` otherwise. -/
@[endpoint_compare _ / _]
meta def divRule : Rule where
  eval e := do
    let_expr HDiv.hDiv _ _ _ _ x y := e | return none
    sameMajorant e (← compare (← mkAppM ``HMul.hMul #[x, ← mkAppM ``Inv.inv #[y]])) ``isBigO_div
      ``isTheta_div

/-- The inverse `e` of `x`, rewritten if `x` is a product, bounded as the product of the inverses
(`isTheta_inv_mul` if this result is exact, `isBigO_inv_mul` otherwise), a quotient `y / z`,
bounded as `z / y` (`isTheta_inv_div` or `isBigO_inv_div`), a natural power with exponent free of
`t`, bounded as the power of the inverse (`isTheta_inv_pow` or `isBigO_inv_pow`), or an inverse
`y⁻¹`, bounded as `y` (`isTheta_inv_inv` or `isBigO_inv_inv`); `none` otherwise. -/
meta def invRewrite? (e x : Expr) : CompareM (Option Result) := do
  match_expr x with
  | HMul.hMul _ _ _ _ y z =>
    let e' ← mkAppM ``HMul.hMul #[← mkAppM ``Inv.inv #[y], ← mkAppM ``Inv.inv #[z]]
    some <$> sameMajorant e (← compare e') ``isBigO_inv_mul ``isTheta_inv_mul
  | HDiv.hDiv _ _ _ _ y z =>
    some <$> sameMajorant e (← compare (← mkAppM ``HDiv.hDiv #[z, y])) ``isBigO_inv_div
      ``isTheta_inv_div
  | HPow.hPow _ β _ _ y n =>
    unless β.isConstOf ``Nat do return none
    if ← dependsOnVar n then return none
    some <$> sameMajorant e (← compare (← mkAppM ``HPow.hPow #[← mkAppM ``Inv.inv #[y], n]))
      ``isBigO_inv_pow ``isTheta_inv_pow
  | Inv.inv _ _ y => some <$> sameMajorant e (← compare y) ``isBigO_inv_inv ``isTheta_inv_inv
  | _ => return none

/-- The rule for inverses `x⁻¹`: first the rewriting of `invRewrite?`, which needs no side
condition; if it does not apply or declines, and the result of `x` is exact, `Θ(powExp a k u)`,
`isTheta_inv_of_isTheta_powExp`, giving `Θ(powExp (-a) (-k) (-u))`. If the rewriting declines and
the second step does not succeed, the rule declines with the message of the rewriting; if the
rewriting does not apply and the result of `x` is only an upper bound, it declines, saying so. -/
@[endpoint_compare _⁻¹]
meta def invRule : Rule where
  eval e := do
    let_expr Inv.inv _ _ x := e | return none
    let rewritten ← observe (invRewrite? e x)
    if let .ok (some r) := rewritten then return some r
    let exact ← observe do
      let r ← compare x
      unless r.exact do
        throwUnbounded (← tracedSentence do
          return ["no bound for the inverse ", e, ": it needs the exact order of ", x,
            ", and the tactic has only the upper bound ", ← r.majorant.display])
      let .powExp .. := r.majorant | return none
      some <$> termResult e (← mkAppM ``isTheta_inv_of_isTheta_powExp #[← eventuallyPos, r.proof])
    match exact, rewritten with
    | .ok (some r), _ => return some r
    | _, .error msg | .error msg, _ => throwUnbounded msg
    | .ok none, .ok _ => return none

/-! ### Bounded factors -/

/-- The bounded factors `Real.sin g` and `Real.cos g`: `isBigO_sin_powExp` and
`isBigO_cos_powExp`. -/
@[endpoint_compare Real.sin _, Real.cos _]
meta def trigRule : Rule where
  eval e := do
    let some (name, g) := match_expr e with
        | Real.sin g => some (``isBigO_sin_powExp, g)
        | Real.cos g => some (``isBigO_cos_powExp, g)
        | _ => none
      | return none
    termResult e (← mkAppOptM name #[← filterExpr, ← lam g])

end Mathlib.Tactic.EndpointIntegrability
