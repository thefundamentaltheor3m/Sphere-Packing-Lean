/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
module

public import SpherePacking.Tactic.EndpointIntegrability.Compare

/-!
# Integrability of the majorants of `endpoint_integrability`

Given a majorant `M` computed by the comparison engine along a filter `l`, `atTop` or `𝓝[>] 0`,
this file proves `IntegrableAtFilter M l`, term by term, by the decision lemmas of
`SpherePacking.Tactic.EndpointIntegrability.Scale`. A sum is integrable when its terms are, by
`MeasureTheory.IntegrableAtFilter.add`.

For a term `powExp a k u`, with a real power `k` of the logarithm:

1. The exponent `u` is classified by `exponentBound?`
   (see `SpherePacking.Tactic.EndpointIntegrability.Exponent`); if it is not, the signs of the
   coefficients are left to the user, as in the section below, and if this fails too, the term is
   not decided.
2. If `u t - c * t ^ p` is bounded above for a negative coefficient `c` and a singular real
   degree `p`, the term decays and is integrable by
   `integrableAtFilter_powExp_atTop_of_mul_rpow` or `integrableAtFilter_powExp_nhdsGT_of_mul_rpow`,
   whatever `a` and `k`.
3. If `u` is bounded above, the term is integrable by `integrableAtFilter_powExp_atTop_of_lt` or
   `integrableAtFilter_powExp_nhdsGT_of_lt` if `a < -1`, respectively `-1 < a`, whatever `k`; and,
   in the borderline case, by `integrableAtFilter_powExp_atTop_of_log_lt` or
   `integrableAtFilter_powExp_nhdsGT_of_log_lt` if `a = -1` and `k < -1`, as for
   `(t * log t ^ 2)⁻¹`.
4. The conditions are proved by `proveCondition?` (the discharger, then `norm_num`): first the
   condition on `a` of the third step; failing it, if `a = -1` is proved, the condition `k < -1`.
   The condition which is not proved, `k < -1` if `a = -1` is proved and the condition on `a`
   otherwise, is simplified by `norm_num`; if it becomes `False` the term is not decided,
   otherwise it is left as a side goal. Since `M` is only an upper bound, a false condition is not
   evidence that the integrand is not integrable: the endpoint goal is then left to the user.

The measurability of the exponent, needed by the decision lemmas, is proved by `fun_prop`.

## Signs of the coefficients

If the exponent is not classified because some monomials `c * t ^ p` are *unknown* (neither
bounded nor absorbed: the degree `p` is not proved non-singular, and `c` is proved neither negative
nor nonpositive), conditions on the signs of their coefficients are left as side goals instead
(`exponentBoundLeaving?`), as weak as the term allows:
* if the term is decided when `u` is merely bounded above, the condition on `a` of the third step
  being proved, or `a = -1` and `k < -1` both, then `c ≤ 0` is left for every unknown monomial,
  which bounds it whatever its degree, except those absorbed by a monomial proved to decay;
* otherwise the decay is needed: the witness of the decay is a monomial proved to decay or, if
  none is, an unknown monomial whose degree is proved singular, for which `c < 0` is left; if
  there is no such monomial, the term is not decided. Among the candidates, the witness is the one
  which absorbs the most unknown monomials (the first in case of a tie). The unknown monomials of
  degree strictly less singular than the witness's are absorbed by it and get no condition, and
  `c ≤ 0` is left for the others: thus `rexp (-a * t ^ 2 - b * t)` at `atTop` leaves `0 < a`
  only.

The statement left is `0 < -c`, respectively `0 ≤ -c`, with the negation pushed inwards, such as
`0 < n` for `c = -1 * n`, treated as the conditions of the fourth step: proved if `norm_num`
proves it, and if `norm_num` refutes it, no goal is left and the term is not decided; thus
`rexp (-n * t)` on `Ioi 0` leaves `0 < n` at `atTop`. Within a term, the conditions on the signs
come first, in the order of the monomials. No such condition is left where `exponentBound?`
classifies the exponent, nor by the comparisons of the engine, which use `exponentBound?` only.

## Boundedness

For an integrable factor of the integrand, the cofactor need only be bounded at the end:
`proveBounded?` proves `M =O[l] fun _ ↦ 1` for a majorant `M`, term by term, by the boundedness
lemmas of `SpherePacking.Tactic.EndpointIntegrability.Scale`, with the same classification of the
exponent and the same treatment of the conditions as above: a term with exponential decay is
bounded; otherwise, with `u` bounded above, the term is bounded if `a < 0` at `atTop`, `0 < a` at
`𝓝[>] 0` (whatever `k`), or if `k ≤ 0` and `a ≤ 0`, respectively `0 ≤ a`. The conditions are
tried in this order: the strict condition on `a`; failing it, if `k ≤ 0` is proved, the condition
`a ≤ 0` (respectively `0 ≤ a`); failing it, if `a = 0` is proved, the condition `k ≤ 0`; and
otherwise the strict condition on `a`. The last condition tried is left as a side goal, after
simplification by `norm_num`, unless it simplifies to `False`: thus `t ^ (-s)` at `atTop` leaves
`0 ≤ s`. The signs of the coefficients are left as above, the term being decided when `u` is
bounded above if the strict condition on `a` is proved, or `k ≤ 0` and the weak condition on `a`
both: thus the cofactor `rexp (-n * t)` at `atTop` leaves `0 ≤ n`. The measurability of the
exponent is not needed.
-/

@[expose] public section

open Lean Meta Elab Tactic Qq MeasureTheory

namespace Mathlib.Tactic.EndpointIntegrability

/-! ### Messages -/

/-- The sentence `the power name = v of base does not satisfy cond name`, if `refuted`, and
`… is not proved to satisfy …` otherwise, for messages (see `sentence`): the condition `cond` is
printed applied to a variable named `name`, and the value `v` simplified by `displaySimp`. -/
meta def powerMessage (name : Name) (v : Expr) (base : String) (cond : Q(ℝ) → Q(Prop))
    (refuted : Bool) : MetaM (List MsgPart) := do
  let c ← withLocalDeclD name q(ℝ) fun x ↦ ppExpr (cond x)
  let status := if refuted then "does not satisfy" else "is not proved to satisfy"
  return [.text "the power ", .code s!"{name} = {← ppExpr (← displaySimp v)}",
    .text s!" of {base} {status} ", .code (toString c)]

/-- `powerMessage`, refuted if `norm_num` refutes `cond v`. -/
meta def powerStatus (name : Name) (v : Q(ℝ)) (base : String) (cond : Q(ℝ) → Q(Prop)) :
    MetaM (List MsgPart) := do
  let refuted ← try pure ((← normNumSimp (cond v)).expr.isConstOf ``False) catch _ => pure false
  powerMessage name v base cond refuted

/-- The reason `msg` why a term with the exponent `u`, bounded above but not proved to decay, is
not decided, a condition on a power which `norm_num` refutes, followed by the remark that the
exponent is not proved to decay unless it is `0`, for messages. -/
meta def refutedCondition (u : Expr) (msg : List MsgPart) : MetaM MessageData := do
  let decay ← withLocalDeclD `t q(ℝ) fun t ↦ do
    if (← displaySimp (u.beta #[t])).numeral? == some 0 then return ([] : List MsgPart)
    return [.text ", and its exponent ", .expr (← displayFun u), .text " is not proved to decay"]
  sentence (msg ++ decay)

/-! ### Decision -/

/-- The condition on the power `a` for the integrability of `powExp a k u` with `u` bounded above:
`a < -1` at `atTop`, `-1 < a` at `𝓝[>] 0`. -/
meta def CanonicalFilter.powerCondition (l : CanonicalFilter) (a : Q(ℝ)) : Q(Prop) :=
  match l with
  | .atTop => q($a < -1)
  | .nhdsGT => q(-1 < $a)

/-- The decision lemma for `powExp a k u` with `u` bounded above. -/
meta def CanonicalFilter.powerLemma : CanonicalFilter → Name
  | .atTop => ``integrableAtFilter_powExp_atTop_of_lt
  | .nhdsGT => ``integrableAtFilter_powExp_nhdsGT_of_lt

/-- The decision lemma for `powExp a k u` with `u` bounded above, `a = -1` and `k < -1`. -/
meta def CanonicalFilter.logLemma : CanonicalFilter → Name
  | .atTop => ``integrableAtFilter_powExp_atTop_of_log_lt
  | .nhdsGT => ``integrableAtFilter_powExp_nhdsGT_of_log_lt

/-- The decision lemma for `powExp a k u` with exponential decay. -/
meta def CanonicalFilter.decayLemma : CanonicalFilter → Name
  | .atTop => ``integrableAtFilter_powExp_atTop_of_mul_rpow
  | .nhdsGT => ``integrableAtFilter_powExp_nhdsGT_of_mul_rpow

/-- A proof of a term with the exponent `u`, with its side goals, by `ofBound` from the
classification of `u` by `exponentBound?`, with no new goal; failing it, by `ofBound` from the
classification of `u` by `exponentBoundLeaving?`, which leaves conditions on the signs of the
coefficients, with `SignResolution.nonpos` if `bounded` holds (the term is decided when `u` is
bounded above), and `SignResolution.decay` otherwise. The side goals are the conditions on the
signs, in the order of the monomials, then those of `ofBound`; if `ofBound` fails after the
conditions are left, the state is restored. If the classification fails where the decay is needed,
the trace reports first why it is (`whyDecay`). -/
meta def proveWithExponent? (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (u : Q(ℝ → ℝ)) (bounded : TacticM Bool)
    (ofBound : ExponentBound → OptionT TacticM (Expr × List MVarId))
    (whyDecay : TacticM (List MsgPart)) :
    OptionT TacticM (Expr × List MVarId) := do
  let bound? : Option ExponentBound ← (exponentBound? l disch u).run
  if let some bound := bound? then return ← ofBound bound
  let signs := if ← bounded then .nonpos else .decay
  let s ← Tactic.saveState
  let leaving := (exponentBoundLeaving? l disch signs u).run
  let (bound, signGoals) ← OptionT.mk <| if signs matches .decay then
      traceFailureFirst (nest := false) leaving do
        sentence <| [.text "its exponent ", .expr (← displayFun u), .text " must decay, since "] ++
          (← whyDecay)
    else leaving
  let r? : Option (Expr × List MVarId) ← (ofBound bound).run
  let some (h, goals) := r? | s.restore; failure
  return (h, signGoals ++ goals)

/-- A proof of `IntegrableAtFilter (powExp a k u) l`, with its side goals, if the term is
decided (see the module documentation): the conditions on the signs of the coefficients of `u`
(see `proveWithExponent?`), the term being decided when `u` is bounded above if `proveCondition?`
proves the condition on `a`, or `a = -1` and `k < -1`, then the condition on a power. The power
`k` of the logarithm matters only in the borderline case `a = -1`. -/
meta def proveTerm? (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (a k u : Expr) : OptionT TacticM (Expr × List MVarId) := do
  have u : Q(ℝ → ℝ) := u
  have a : Q(ℝ) := a
  have k : Q(ℝ) := k
  let hum? : Option Expr ← proveFunProp? disch q(Measurable $u)
  let some hum := hum?
    | trace[Tactic.endpoint_integrability] "{← sentence ["the exponent ", ← displayFun u,
        " is not proved measurable by `fun_prop`"]}"
      failure
  let bounded : TacticM Bool := do
    if (← proveCondition? disch (l.powerCondition a)).isSome then return true
    if (← proveCondition? disch q($a = -1)).isNone then return false
    return (← proveCondition? disch q($k < -1)).isSome
  let whyDecay : TacticM (List MsgPart) := do
    if (← proveCondition? disch q($a = -1)).isSome then
      return [.text "the power of `t` is `-1`, and "] ++
        (← powerStatus `k k "`|log t|`" fun x ↦ q($x < -1))
    powerStatus `a a "`t`" l.powerCondition
  let refuted (msg : TacticM (List MsgPart)) : OptionT TacticM (Expr × List MVarId) := do
    trace[Tactic.endpoint_integrability] "{← refutedCondition u (← msg)}"
    failure
  proveWithExponent? l disch u bounded (whyDecay := whyDecay) fun
  | .decay c n hc hn hu => return (← mkAppOptM l.decayLemma #[a, k, u, hum, c, hc, n, hn, hu], [])
  | .bounded hu => do
    let ha? : Option Expr ← proveCondition? disch (l.powerCondition a)
    if let some ha := ha? then
      return (← mkAppOptM l.powerLemma #[a, k, u, hum, ha, hu], [])
    let ha? : Option Expr ← proveCondition? disch q($a = -1)
    if let some ha := ha? then
      let r? : Option (Expr × List MVarId) ← proveOrLeaveCondition? disch q($k < -1)
      let some (hk, goals) := r?
        | return ← refuted do
            return [.text "the power of `t` is `-1`, and "] ++
              (← powerMessage `k k "`|log t|`" (fun x ↦ q($x < -1)) true)
      return (← mkAppOptM l.logLemma #[a, k, u, hum, ha, hk, hu], goals)
    let r? : Option (Expr × List MVarId) ← proveOrLeaveCondition? disch (l.powerCondition a)
    let some (ha, goals) := r?
      | return ← refuted (powerMessage `a a "`t`" l.powerCondition true)
    return (← mkAppOptM l.powerLemma #[a, k, u, hum, ha, hu], goals)

/-- The term `powExp a k u` of a sum, by `prove`, the trace reporting first, if it fails, that the
term is not proved `what`. -/
meta def proveSummand? (what : String) (a k u : Expr)
    (prove : OptionT TacticM (Expr × List MVarId)) : OptionT TacticM (Expr × List MVarId) :=
  OptionT.mk <| traceFailureFirst prove.run do
    sentence ["the term ", ← displayTermFun a k u, s!" of the bound is not proved {what}:"]

/-- A proof of `IntegrableAtFilter M l` for the majorant `M`, with its side goals, from left to
right, if every term is decided; the first term which is not decided is reported by the trace, if
`M` is a sum (see `proveSummand?`). -/
meta def proveMajorant? (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (inSum : Bool) : Majorant → OptionT TacticM (Expr × List MVarId)
  | .powExp a k u =>
    if inSum then proveSummand? "integrable" a k u (proveTerm? l disch a k u)
    else proveTerm? l disch a k u
  | .add m₁ m₂ => do
    let (h₁, g₁) ← proveMajorant? l disch true m₁
    let (h₂, g₂) ← proveMajorant? l disch true m₂
    return (← mkAppM ``IntegrableAtFilter.add #[h₁, h₂], g₁ ++ g₂)

/-! ### Boundedness -/

/-- The strict condition on the power `a` for the boundedness of `powExp a k u` with `u` bounded
above: `a < 0` at `atTop`, `0 < a` at `𝓝[>] 0`. -/
meta def CanonicalFilter.boundCondition (l : CanonicalFilter) (a : Q(ℝ)) : Q(Prop) :=
  match l with
  | .atTop => q($a < 0)
  | .nhdsGT => q(0 < $a)

/-- The weak condition on the power `a` for the boundedness of `powExp a k u` with `u` bounded
above and `k ≤ 0`: `a ≤ 0` at `atTop`, `0 ≤ a` at `𝓝[>] 0`. -/
meta def CanonicalFilter.weakBoundCondition (l : CanonicalFilter) (a : Q(ℝ)) : Q(Prop) :=
  match l with
  | .atTop => q($a ≤ 0)
  | .nhdsGT => q(0 ≤ $a)

/-- The weak condition on `a` from a proof `h` of `a = 0`. -/
meta def CanonicalFilter.weakBoundOfEq (l : CanonicalFilter) (a : Q(ℝ)) (h : Q($a = 0)) : Expr :=
  match l with
  | .atTop => q(le_of_eq $h)
  | .nhdsGT => q(ge_of_eq $h)

/-- The boundedness lemma for `powExp a k u` with `u` bounded above and the strict condition on
`a`. -/
meta def CanonicalFilter.boundLemma : CanonicalFilter → Name
  | .atTop => ``isBigO_powExp_one_atTop_of_lt
  | .nhdsGT => ``isBigO_powExp_one_nhdsGT_of_lt

/-- The boundedness lemma for `powExp a k u` with `u` bounded above, the weak condition on `a`
and `k ≤ 0`. -/
meta def CanonicalFilter.weakBoundLemma : CanonicalFilter → Name
  | .atTop => ``isBigO_powExp_one_atTop_of_le
  | .nhdsGT => ``isBigO_powExp_one_nhdsGT_of_le

/-- The boundedness lemma for `powExp a k u` with exponential decay. -/
meta def CanonicalFilter.decayBoundLemma : CanonicalFilter → Name
  | .atTop => ``isBigO_powExp_one_atTop_of_mul_rpow
  | .nhdsGT => ``isBigO_powExp_one_nhdsGT_of_mul_rpow

/-- A proof of `powExp a k u =O[l] fun _ ↦ 1`, with its side goals, if the term is decided (see
the module documentation): the conditions on the signs of the coefficients of `u` (see
`proveWithExponent?`), the term being decided when `u` is bounded above if `proveCondition?`
proves the strict condition on `a`, or `k ≤ 0` and the weak condition on `a`, then the condition
on a power. -/
meta def proveBoundedTerm? (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (a k u : Expr) : OptionT TacticM (Expr × List MVarId) := do
  have u : Q(ℝ → ℝ) := u
  have a : Q(ℝ) := a
  have k : Q(ℝ) := k
  let bounded : TacticM Bool := do
    if (← proveCondition? disch (l.boundCondition a)).isSome then return true
    if (← proveCondition? disch q($k ≤ 0)).isNone then return false
    return (← proveCondition? disch (l.weakBoundCondition a)).isSome
  let whyDecay : TacticM (List MsgPart) := do
    if (← proveCondition? disch q($k ≤ 0)).isSome then
      return ← powerStatus `a a "`t`" l.weakBoundCondition
    return (← powerStatus `a a "`t`" l.boundCondition) ++ [.text ", and "] ++
      (← powerStatus `k k "`|log t|`" fun x ↦ q($x ≤ 0))
  let refuted (msg : TacticM (List MsgPart)) : OptionT TacticM (Expr × List MVarId) := do
    trace[Tactic.endpoint_integrability] "{← refutedCondition u (← msg)}"
    failure
  proveWithExponent? l disch u bounded (whyDecay := whyDecay) fun
  | .decay c n hc hn hu => return (← mkAppOptM l.decayBoundLemma #[a, k, u, c, hc, n, hn, hu], [])
  | .bounded hu => do
    let ha? : Option Expr ← proveCondition? disch (l.boundCondition a)
    if let some ha := ha? then
      return (← mkAppOptM l.boundLemma #[a, k, u, ha, hu], [])
    let hk? : Option Expr ← proveCondition? disch q($k ≤ 0)
    if let some hk := hk? then
      let r? : Option (Expr × List MVarId) ← proveOrLeaveCondition? disch (l.weakBoundCondition a)
      let some (ha, goals) := r?
        | return ← refuted (powerMessage `a a "`t`" l.weakBoundCondition true)
      return (← mkAppOptM l.weakBoundLemma #[a, k, u, ha, hk, hu], goals)
    let ha? : Option Expr ← proveCondition? disch q($a = 0)
    if let some ha := ha? then
      let r? : Option (Expr × List MVarId) ← proveOrLeaveCondition? disch q($k ≤ 0)
      let some (hk, goals) := r?
        | return ← refuted do
            return [.text "the power of `t` is `0`, and "] ++
              (← powerMessage `k k "`|log t|`" (fun x ↦ q($x ≤ 0)) true)
      return (← mkAppOptM l.weakBoundLemma #[a, k, u, l.weakBoundOfEq a ha, hk, hu], goals)
    let r? : Option (Expr × List MVarId) ← proveOrLeaveCondition? disch (l.boundCondition a)
    let some (ha, goals) := r?
      | return ← refuted (powerMessage `a a "`t`" l.boundCondition true)
    return (← mkAppOptM l.boundLemma #[a, k, u, ha, hu], goals)

/-- A proof of `M =O[l] fun _ ↦ 1` for the majorant `M`, with its side goals, from left to right,
if every term is decided: a sum is bounded when its terms are, by `Asymptotics.IsBigO.add`. The
first term which is not decided is reported by the trace, if `M` is a sum (see
`proveSummand?`). -/
meta def proveBounded? (l : CanonicalFilter) (disch : TSyntax ``Parser.Tactic.tacticSeq)
    (inSum : Bool) : Majorant → OptionT TacticM (Expr × List MVarId)
  | .powExp a k u =>
    if inSum then proveSummand? "bounded" a k u (proveBoundedTerm? l disch a k u)
    else proveBoundedTerm? l disch a k u
  | .add m₁ m₂ => do
    let (h₁, g₁) ← proveBounded? l disch true m₁
    let (h₂, g₂) ← proveBounded? l disch true m₂
    return (← mkAppM ``Asymptotics.IsBigO.add #[h₁, h₂], g₁ ++ g₂)

end Mathlib.Tactic.EndpointIntegrability
