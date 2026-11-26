/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
-- The derivative / differentiability lemmas (and their `simp`, `fun_prop` tags) that the fallback
-- and the closers rely on for `pow`, `sin`, `cos`, `sinh`, `cosh`, …; they used to come
-- transitively through a derivative oracle's imports.
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import SpherePacking.Tactic.ChangeVar.Circle
public meta import Mathlib.Lean.Meta.Simp
public meta import Mathlib.Tactic.Ring
public meta import Mathlib.Tactic.FieldSimp
public meta import Mathlib.Tactic.FunProp
public meta import Mathlib.Tactic.Positivity
public meta import Mathlib.Tactic.DefEqTransformations
public meta import Mathlib.Tactic.NormNum.Core
public meta import Qq

/-!
# `change_var`: substitution in interval and set integrals

## What it does: the names `ψ`, `ψ'`, `g`

`change_var` applies the substitution rule (u-substitution)

```
∫ x in a..b, F x = ∫ u in ψ a..ψ b, g u      when   F x = ψ' x * g (ψ x)
```

and every name in the tactic is a piece of this formula:

* `F` is the integrand of the goal, a function of the old variable `x`;
* `ψ` is the new variable as a function of the old one, `u = ψ x`: it is what one writes after
  `change_var u =` (here `u` is only a label);
* `ψ'` is the derivative of `ψ`, computed by the tactic or given as a proof with `using h`;
* `g` is the **new integrand**, a function of `u`: what `F` becomes once written in terms of
  `u`, after taking out the factor `ψ'`. Equivalently, `F` is `ψ'` times `g` composed with `ψ`,
  which is why the code also calls `g` the *outer function*.

Example. In `∫ x in 0..1, 2 * x * exp (x ^ 2)` take `u = x ^ 2`: then `ψ' x = 2 * x` and
`F x = ψ' x * exp (ψ x)`, so `g = exp` and the goal becomes `∫ x in 0 ^ 2..1 ^ 2, rexp x = …`
(the bounds are `ψ a`, `ψ b`, not simplified; the binder keeps the name of the lemma, see
*Usage*):

```
change_var u = x ^ 2 with fun u => Real.exp u   -- g given; obligations left as goals
change_var! u = x ^ 2                            -- g found by the tactic (factor search)
```

When the integrand does not contain `ψ'` literally, `g` absorbs the constant: for
`∫ x * (x ^ 2 + 1) ^ 3` with `u = x ^ 2 + 1`, `F x = 2 * x * (1 / 2 * (x ^ 2 + 1) ^ 3)`, so
`g = fun u => 1 / 2 * u ^ 3`. `with g` is mandatory in the rigid form; `change_var!` and
`change_var?` search `g` when it is omitted, and `change_var?` reports the `g` it found. A wrong
`g` is not an error: the obligation `ceq` (`F = ψ' • g ∘ ψ` on the domain) stays open, and false.

`g` plays the same role in the other modes:

* **set mode**: `F x = |ψ' x| • g (ψ x)` on `s`, and `∫ x in s, F x = ∫ u in ψ '' s, g u` (or
  `∫ u in T, g u` with `onto T`);
* **circle mode**: `ψ t = circleMap c R (α * t)` runs over the circle and `g` is the integrand of
  the contour integral: `F t = ψ' t * g (ψ t)` with `ψ' t = α * (ψ t - c) * I`, and
  `∫ t in 0..T, F t = ∮ z in C(c, R), g z`. For `∫ θ in 0..2π, cos θ` with `z = exp (θ * I)`,
  `cos θ = (z + z⁻¹) / 2` and `ψ' θ = I * z`, so `g z = (z + z⁻¹) / 2 / (I * z)`.

## Files: a Mathlib-only core, and the derivative oracle

`change_var` is made of:

* `SpherePacking/Tactic/ChangeVar/Core.lean` (this file) depends on **Mathlib only**, and on no
  oracle: the three forms, the three modes, the search for `g`, the obligations and their closers,
  the suggestions of `change_var?`; `SpherePacking/Tactic/ChangeVar/Circle.lean` holds the circle
  lemmas;
* `SpherePacking/Tactic/Test/ChangeVar.lean` tests this file alone (its only other import is
  Mathlib's `sleep_heartbeats`, for the budgets), and also serves as usage examples;
* a **derivative oracle** is an optional plug-in, declared in its own file with
  `@[change_var_oracle]` and tested in its own test file (see *Derivative oracles* below).

The one step that needs more than Mathlib is computing an *explicit* derivative `ψ'`: the search
for `g` needs it as an expression, and so does the `deriv` obligation when it is closed
automatically. Both go through one function, `deriveAt`, which asks the registered oracles, then
falls back to `fun_prop` and an opaque `deriv ψ x`. Without an oracle, derivatives are given with
`using h` (or come from the fallback). **Oracles are activated silently**, by importing the file
that declares them, even transitively; `change_var?` names the source of each derivative, and the
option `changeVar.derivOracles` (default `true`) switches every oracle off.

## Usage: a rigid tactic, an automatic one, an explaining one

```
change_var u = ψ with g                  -- rigid: one rewrite, every obligation left as a goal
change_var (disch := tac) u = ψ with g   -- rigid, `tac` tried on each obligation
change_var u = ψ with g using h          -- `h` proves `deriv` (any form): no goal `deriv`
change_var! u = ψ [with g] [using h]     -- automatic: ψ', search for g, obligations attempted
change_var? u = ψ [with g] [using h]     -- change_var! + report + an equivalent explicit script
change_var u = ψ onto T with g           -- set integral `∫ x in s, F x` ↦ `∫ u in T, g u`
```

The goal and the type of `ψ` select the mode:

* **real mode**: an interval integral `∫ x in a..b, F x` and `ψ : ℝ`;
* **circle mode**: an interval integral `∫ t in 0..T, F t` and `ψ : ℂ`, a circle parametrisation
  (`I ^ t`, `exp (t * I)`, `circleMap c R (α * t)`);
* **set mode**: no interval integral, a set integral `∫ x in s, F x` (Lebesgue measure) and
  `ψ : ℝ`. `onto T` belongs to this mode only, and is accepted by all three forms.

The only option, `(disch := tac)`, comes right after the name, in the rigid form only (the
discharger of `change_var!` and `change_var?` is built in). The data clauses follow `ψ`, in the
order `onto T` (set mode), `with g`, `using h`.

**`using h`** (all three forms, real and set modes; refused in circle mode, which has no
derivative obligation) gives the proof of `deriv`: `h : ∀ x ∈ [[a, b]], HasDerivAt ψ (ψ' x) x`,
or `∀ x ∈ s, HasDerivWithinAt ψ (ψ' x) s x` in set mode. The derivative `ψ'` is read off its
type; `h` may be a term or a `by` block. This follows Mathlib's `using` clauses
(`apply_fun f using P` with `P : Injective f`, `lift e to t using h`): `using` gives the proof
of a side condition that the tactic would otherwise prove itself or leave as a goal, and a
`using` term that does not fit is an **error**, never a reason to fall back to the automation.
So in `change_var!`, `using h` replaces the derivative oracles (the search for `g` uses the given
`ψ'`), and a wrong `h` stops the call with the elaboration error (`Type mismatch …`, or the error
of the `by` block), instead of silently differentiating `ψ` another way.

The tactic acts on the *first* `∫ x in a..b, F x` of the goal (outermost, then leftmost), or, if
there is none, on the first `∫ x in s, F x`. `ψ` is elaborated with the integral's own binder
name in scope, so write it in that variable (`change_var u = x ^ 2` for `∫ x in …`). The name on
the left is a label for the reader only: `u` by convention for a real variable, `z` for the
point `ψ t` on the circle in circle mode. It is not bound, and the new integral keeps the binder
name of the lemma (`∫ x in ψ a..ψ b, g x`, `∮ z in C(c, R), g z`, `∫ x in T, g x`). `g` given with
`with` is elaborated in the user's context (the integration variable is *not* in scope; a `g`
with holes is refused).
**Checks before any work.** The call is refused with an explicit error, before the goal is touched,
when the goal has neither an interval nor a set integral (or only integrals under a binder that
depend on its variable: `intro` first), when `ψ` does not elaborate, has holes, does not depend on
the integration variable (a constant `ψ` has derivative `0`) or is neither real nor complex, or when
`onto T` is given on an interval integral or has holes; in circle mode, when the lower bound is not
`0` or `ψ` is not a recognised parametrisation; in set mode, when `ψ` is not real or the measure is
not `volume`. Each check, with its exact message, is pinned in
`SpherePacking/Tactic/Test/ChangeVar.lean` (see *Edge cases*), except the refusal of a non-real `ψ`
in set mode (*not pinned*).

## Mathlib conventions

The split follows Mathlib's conventions. Mathlib's "flexible" linter
(`Mathlib/Tactic/Linter/FlexibleLinter.lean`) separates *rigid* tactics (specific input,
predictable output, like `rw`) from *flexible* ones (like `simp`), whose output should not be fed
to rigid tactics; the suffix `!` marks a more aggressive variant (`congr!`, `ring1!`), `?` a
variant that suggests an explicit script (`simp?`, `exact?`); side goals are left to the user or
to an explicit discharger (`gcongr`, `fun_prop (disch := …)`) and handled with `case`. Hence:

* `change_var u = ψ with g` is rigid. It searches nothing and proves nothing: it rewrites with a
  congruence lemma and the substitution lemma and returns their hypotheses as the tagged goals of
  *Obligations*. (Circle mode still recognises the parametrisation, which it needs to state the
  lemma, and casts a real integral to `ℂ`.) `with g` is mandatory: without it the call does not
  parse (`expected 'with'`); nothing is searched or sent to an oracle behind the user's back. To
  have `g` searched, use `change_var!`.
* The automation is available as named tactics (*Dischargers*), usable by hand on one
  obligation or as the `disch` of the rigid form. The rigid form has *no* default discharger: it
  attempts nothing unless `(disch := tac)` is given. `tac` is one tactic, tried on every
  obligation in turn (`deriv` first); there is no per-obligation option. To treat obligations
  differently, either leave them and use `case hv => …`, or give a `first` whose alternatives
  only succeed on their own kind of goal (`(disch := first | change_var_deriv | fun_prop)`): an
  alternative that fails on a goal costs nothing, the goal simply stays open. The built-in
  closers of `change_var!` are the "default discharger" of the automatic form; as a discharger
  for the rigid form they are `change_var_disch`.
* `change_var!` is the flexible form: it computes `ψ'` (or reads it off `using h`), searches `g`
  when it is not given, and attempts every obligation.
* `change_var?` runs `change_var!`, reports what was found and which obligations were closed, and
  suggests an equivalent call that replays without search *and without any oracle*: the rigid form
  with `g` explicit, `(disch := change_var_side)`, and `deriv` proved `using by` the explicit chain
  of Mathlib derivative lemmas behind the derivative found (or `fun_prop`, for the opaque fallback).
  With an oracle that differentiates `log` (premise `x ≠ 0` from the domain `[1, e]`):
  ```
  change_var (disch := change_var_side) u = Real.log x with fun (u : ℝ) => u using by
    intro x hx
    have hne : x ≠ 0 := by change_var_domain
    have hd := HasDerivAt.log (hasDerivAt_id' x) hne
    change HasDerivAt (fun (x : ℝ) => Real.log x) (1 / x) x
    exact hd
  ```
  The `using` proof is elaborated before the rewrite, so `ψ'` is known when `change_var_side` meets
  `hv` and `ceq` (a `case deriv` *after* the call would come too late: `disch` runs during the call,
  and `hv`, `ceq` would still mention the unassigned `?ψ'`). The script is replayed before it is
  suggested, *with the oracles switched off*, and its constants must all come from the modules
  this file depends on (an oracle could return a proof using lemmas of its own library: such a
  script would need that library). When no script qualifies, the suggestion is the compact form
  `change_var (disch := change_var_disch) … with g`, which is **not** oracle-free:
  `change_var_deriv` calls the oracles again on replay. A `using h` given to `change_var?` is kept
  as is. Circle mode has no derivative: the suggestion is
  `change_var (disch := change_var_side) z = ψ with g`. The text is aligned on the column of the
  call.

## Obligations

Each mode rewrites with two Mathlib theorems (see *Trust model*); their hypotheses become tagged
goals, which come after the main goal in this order:

```
real    deriv  ∀ x ∈ [[a, b]], HasDerivAt ψ (?ψ' x) x       (rigid, without `using`)
        hv     ContinuousOn ?ψ' [[a, b]]
        hg     ContinuousOn g (ψ '' [[a, b]])
        ceq    EqOn F (fun x => ?ψ' x • (g ∘ ψ) x) [[a, b]]
        ψ'     ℝ → ℝ                                         (data goal, same condition)
circle  hα     α ≠ 0
        hT     α * T = 2 * π
        ceq    EqOn F (fun t => α * (deriv γ (α * t) * g (γ (α * t)))) [[0, T]],
               where γ = circleMap c R
set     deriv  ∀ x ∈ s, HasDerivWithinAt ψ (?ψ' x) s x        (all forms, without `using`)
        hs     MeasurableSet s
        hinj   Set.InjOn ψ s
        himg   ψ '' s = T                                    (with `onto` only)
        ceq    EqOn F (fun x => |?ψ' x| • g (ψ x)) s
        ψ'     ℝ → ℝ                                         (data goal, same condition)
```

`?ψ'` is a metavariable, assigned by the proof of `deriv`: prove `deriv` first (by hand or with
`change_var_deriv`), since `hv` and `ceq` mention `?ψ'`. The data goal `ψ'` then disappears. With
`using h`, `deriv` is proved by `h` and `ψ'` is the derivative stated by `h`: there is neither a
goal `deriv` nor a data goal, in any form. Without `using`: in `change_var!` on an interval
integral, `ψ'` is computed *before* the rewrite, so real mode has neither `deriv` nor `ψ'`, and a
derivative that cannot be computed makes the call fail; set mode always goes through the goal
`deriv` (closed by `change_var_deriv` in `change_var!`).

## Dischargers: what proves what

The automation is layered; each layer only calls the layers below it.

```
layer  tactic             proves                    made of
3      change_var_disch   any obligation            first | change_var_deriv | change_var_side
2      change_var_deriv   deriv (real or set mode)  the derivative oracles, fallback `fun_prop`;
                                                    then `tidy`
       change_var_deriv?  the same, and suggests    the chain of Mathlib lemmas found by
                          it as an explicit script  the oracle, see `derivScript`; bridged to a
                                                    stated ψ' by norm_num | ring | simp |
                                                    field_simp
       change_var_side    any other obligation      the closers below, tried in the order real,
                                                    circle, set
       change_var_abs     `|e| ↦ ±e` in a goal      0 ≤ e by positivity | change_var_domain, else
                                                    0 ≤ -e by positivity
1      change_var_domain  0 < e, 0 ≤ e, e ≠ 0,      positivity | change_var_bounds | ne_of_gt/lt +
                          e < 0, e ≤ 0              assumption | simp [*, Real.sqrt_eq_zero'] |
                                                    fail
0      change_var_bounds  the same, from `x ∈ S`    bounds of `S` (Icc … Iio, uIcc, uIoc), their
                          hypotheses                sign by positivity / norm_num
```
The closers behind `change_var_side` (`closeRealSideGoals`, `closeCircleSideGoals`,
`closeSetSideGoals`), by obligation. Each alternative either closes its goal or leaves no trace.

```
real    hv, hg  fun_prop; else pointwise: `ContinuousAt` at each x (hv) or at each ψ x (hg), with
                `0 < x` or `x ≠ 0` by change_var_domain, then fun_prop (disch := change_var_domain)
        ceq     intro; simp only [comp, smul]; done | ring1 | push_cast; ring1 | field_simp; ring1
circle  hα      positivity
        hT      ring1 | field_simp; ring1
        ceq     unfold circleMap (and cos, sin into exp); field_simp; ring1, reducing I ^ 2, …
set     hs      exact measurableSet_Icc | … | exact measurableSet_uIoc
        hinj    intro a _ b _ h; simpa using h | simp only at h; linarith
                | field_simp at h; linarith
        ceq     intro; change_var_abs (needs ?ψ' assigned); then as the real ceq, plus push_cast;
                field_simp
        himg    simp; done | simp; norm_num; done          (a cheap attempt; needs an inverse of ψ)
```

`change_var_domain` is where the domain of integration enters the proofs. It runs

* in `withRealVarIn` (real mode of `change_var!`, `change_var_deriv`, the search for `g` in set
  mode, the scripts of `derivScript`), which adds `hpos : 0 < x` or `hneg : x < 0`, and
  `hne : x ≠ 0`, when `change_var_domain` proves them from `hx : x ∈ domain`, so that an oracle
  can close the premises of its rules (`x ≠ 0` for `log x`) from the local context;
* as the discharger of the `fun_prop` fallback of the derivative (`deriveAt`);
* in the pointwise continuity closers of `hv`, `hg`;
* in `change_var_abs`, for `0 ≤ e`;
* in set mode, to decide whether `ψ' ≤ 0` before searching `g` (`|ψ'| = -ψ'`).

When each part runs, by form and mode:

```
                    real                      circle                    set
rigid               nothing                   nothing                   nothing
rigid + disch       tac on deriv, hv, hg,     tac on hα, hT, ceq        tac on deriv, hs, hinj,
                    ceq                                                 himg, ceq
change_var! / ?     ψ' computed (as           g = F / (dz/dt) with z =  ψ' computed to search g
                    change_var_deriv does),   ψ t; circle closers on    with ±ψ'; then the rigid
                    g searched; real          hα, hT, ceq               form with disch :=
                    closers on hv, hg, ceq                              change_var_disch
any form + using h  no oracle: ψ' and its     refused (no derivative)   no oracle: ψ' and its
                    proof come from h; no                               proof come from h; no goal
                    goal deriv                                          deriv
```
In every case the obligations are attempted one at a time, `deriv` first, each through `runClosed`
(own budget `changeVar.sideGoalHeartbeats`, no error recovery, no `sorry`, state restored on
failure); goals that existed before the call are never touched; an obligation that is not closed
stays as a goal, in the order of *Obligations*. `change_var!` and `change_var (disch :=
change_var_disch) … with g` (the compact rigid replay) perform the same rewrite and normally close
the same goals. Two differences: on an interval integral, `change_var!` fails when `ψ'` cannot be
computed, where the rigid form leaves `deriv` open; and `change_var_side` tries the closers of all
three modes on each goal, `change_var!` (real and circle modes) only those of its own mode.

## Edge cases
Expected behaviour in unusual situations, pinned with their exact messages by `#guard_msgs` in
`SpherePacking/Tactic/Test/ChangeVar.lean`, except the rows that need an oracle (in the oracle's
test file, `SpherePacking/Tactic/Test/ChangeVarSymLean.lean` for SymLean's, when it is imported) and
what is marked *not pinned*. Two outcomes only: an **error** (the goal is untouched), or **success
with obligations left open** (never a silent `sorry`; a `?ψ'` assigned by a closer is still checked
through `deriv`).

```
situation                                     expected behaviour
---------------------------------------------------------------------------------------------
refusals (see Checks before any work)         error, goal untouched (a non-real ψ in set mode:
                                                *not pinned*)
ψ written in another variable than the        elaboration error (`Unknown identifier`), goal
  integral's binder                             untouched
rigid form without `with g`                   parse error `expected 'with'` (*not pinned*:
                                                `#guard_msgs` cannot catch a parse error)
`g` with holes                                error "the outer function … has holes"
`ψ` with holes / `onto T` with holes          error "the new variable … has holes" / "the image
                                                set … has holes"
the only integrals are under a binder and     error "the only integrals of the goal are under a
  use its variable (`∀ y, ∫ x in 0..y, …`)      binder …; introduce it first (`intro`)"
other goals of the user, also when the main   untouched (only the main goal is beta-reduced)
  goal is closed by `rfl`

derivative: no oracle applies, fun_prop       ψ' = deriv ψ x (opaque, reported as fallback);
  proves differentiability                      `g` found only if `deriv ψ x` is a factor of
                                                the integrand, else error "could not write the
                                                integrand as …"; `hv` usually left open
derivative: no oracle applies, fun_prop       change_var!: error "could not differentiate",
  fails                                         with fun_prop's explanation
                                              rigid + change_var_disch: `deriv`, and the goals
                                                that mention ?ψ' (`hv`, `ceq`), left open; data
                                                goal `ψ'` last
`deriv` not proved, but `ceq` fixes ?ψ'       `ceq`'s closer may assign ?ψ' by unification
  (`f' x * f x ^ 2` against `?ψ' x * f x ^ 2`,  (here `f'`): sound, `deriv` still states it
  `f`, `f'` opaque)                             and stays to be proved
`deriv` left as `sorry`                       ?ψ' unassigned: data goal `ψ'` remains
ψ' given, equal but written differently       change_var_deriv: error "the computed
  (x + x for 2 * x)                             derivative … does not match the derivative
                                                stated in the goal …", with both derivatives
                                                (compared up to definitional unfolding, not up
                                                to ring);
                                                change_var_deriv? bridges it
                                                (`congr_deriv … (by ring)`) and succeeds
ψ' given and wrong (3 * x)                    change_var_deriv: the same error;
                                                change_var_deriv?: the same error, without
                                                the warning (*not pinned*)
`using h`, h of the wrong type                error `Type mismatch` (the expected type shows
                                                ?ψ'), in every form: no fallback to the oracles
`using by …` whose script fails               the error of the script; the call stops
`using h` in circle mode                      error: no derivative obligation there

`g` given and wrong                           no error: the rewrite holds for any `g`; `ceq`
                                                is left open (and false); change_var? reports
                                                `left open [ceq]`
more than 8 candidate factors                 error: the search for g is bounded; give g

`disch` fails on every obligation             no error: all obligations left open
`(disch := sorry)`                            the same: runClosed refuses proofs with sorry
slow `disch` or closer                        cut by its budget, the obligation left open;
                                                raise `changeVar.sideGoalHeartbeats` by hand

set mode, ψ not injective on s                `hinj` (false) left open; `ceq` too when
  (x ^ 2 on Ioc (-1) 1)                         |ψ'| ≠ ψ' on part of s

change_var?: no explicit `deriv` script       (*not pinned*) the suggestion is the compact
  replays                                       `change_var (disch := change_var_disch) … with g`
                                                (change_var_deriv calls the oracles)
```

## Trust model

Every form performs the same rewrite (`rewrite`, then `rfl` on the main goal, as `rw` does), with
two Mathlib theorems:

1. a congruence lemma, which replaces the integrand `F` by a candidate:
   `intervalIntegral.integral_congr` with `fun x => ψ' x • g (ψ x)` (real mode) or
   `fun t => α * (deriv γ (α t) * g (γ (α t)))` (circle mode),
   `MeasureTheory.setIntegral_congr_fun` with `fun x => |ψ' x| • g (ψ x)` (set mode). Its
   hypothesis, `F = candidate` on the domain, is the obligation `ceq` (plus `hs` in set mode);
2. the change-of-variables theorem itself, whose hypotheses are the other obligations: `deriv`,
   `hv`, `hg` (real mode: `intervalIntegral.integral_deriv_smul_comp'`), `hα`, `hT` (circle mode:
   `ChangeVar.intervalIntegral_circleMap_reparam'`) or `deriv`, `hs`, `hinj` (set mode:
   `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`, read right to left; with
   `onto T` a last rewrite by the goal `himg : ψ '' s = T`).

The forms differ only in what happens around that rewrite (see *Dischargers*): the rigid form
computes and attempts nothing unless a `disch` tactic is given; `change_var!`/`change_var?`
compute `ψ'` (or take it, with its proof, from `using h`), search `g` when it is not given, and
attempt the obligations.

Nothing computed is trusted: every search result enters the proof only through an obligation,
and an attempt that fails leaves its goal to the user, never assumed. Only the goals created by
the call are touched (`rewriteAndClose`), never other goals of the user. So a wrong search result
can only make the tactic fail or leave an unprovable goal; it can never produce a false theorem.
Every closed goal is checked by the kernel.

## Real mode, step by step (`realMode`)
Goal: `∫ x in a..b, F x = …`, `ψ : ℝ → ℝ`. The rigid form performs step 4 only, then runs its
`disch`, if any, as in step 5. `change_var!` runs all steps. On their own, `change_var_deriv` runs
steps 1–2 on the goal `deriv`, and `change_var_side` step 5 on one obligation. With `using h`, steps
1–2 are replaced by `h` in every form: `ψ'` is read off its type, `h` is the proof.

1. **Context.** A fresh real `x` and `hx : x ∈ [[a, b]]` are introduced (`withRealVarIn`, which
   accepts any interval as domain), with the `let`s `hpos`/`hneg`, `hne` when `change_var_domain`
   proves the sign of `x` (see *Dischargers*). Best effort: these facts come from
   `change_var_bounds` only (`positivity` ignores `hx`), so an interval containing `0`, or with
   bounds of no provable sign, gives none, and premises such as `x ≠ 0` then stay unproved
   (`change_var!` falls back to the opaque `deriv` or fails; `using h` is the way out).
2. **Derivative.** `deriveAt` asks the registered derivative oracles for `HasDerivAt ψ v x` (see
   *Derivative oracles*). If no oracle applies (or `changeVar.derivOracles` is `false`, or none is
   imported), the fallback proves
   `DifferentiableAt ℝ ψ x` with `fun_prop (disch := change_var_domain)` and uses `v = deriv ψ x`
   (correct but opaque, so the search of step 3 rarely succeeds with it). The derivative is then
   normalised by `tidy` (`norm_num` + unit/zero lemmas) *with a proof*, moved along by
   `HasDerivAt.congr_deriv`, so that every later step and every obligation sees `2 * x` rather
   than `↑2 * x ^ (2 - 1) * 1 + 0`.
3. **Outer function.** `findOuter?` looks for `g` with `F x = v • g (ψ x)`, see its docstring
   (factor search, pruned by the opaque symbols of `v`). With `with g` the search is skipped and
   the user's `g` is used as is.
4. **Rewrite** (all forms). `integral_congr` (obligation `ceq`) and
   `intervalIntegral.integral_deriv_smul_comp'`:
   `(∀ x ∈ [[a, b]], HasDerivAt ψ (v x) x) → ContinuousOn v [[a, b]] →
    ContinuousOn g (ψ '' [[a, b]]) → ∫ x in a..b, v x • g (ψ x) = ∫ u in ψ a..ψ b, g u`.
   We use the primed version on purpose: the unprimed one asks for `Continuous g` on all of `ℝ`,
   which fails for `g = u⁻¹` or `g = (1 + u)⁻¹` even when the image `ψ '' [[a, b]]` stays away from
   the singularity. In the rigid form `v` is the metavariable `?ψ'` and the first hypothesis is
   the goal `deriv`; in `change_var!` both come from steps 1–2.
5. **Obligations** `hv`, `hg`, `ceq`, by the real closers (`closeRealSideGoals`), each on its own
   through `runClosed`.

## Circle mode, step by step (`complexMode`)

Goal: `∫ t in 0..T, F t = …` with `F : ℝ → ℂ` (a real integral is first cast to `ℂ` with
`Complex.ofReal_injective` and `intervalIntegral.integral_ofReal`, after the checks of step 1).
All forms run steps 1 and 3; step 2 runs only when `g` is not given (`change_var!`), step 4 in
`change_var!` (or through the `disch` of the rigid form). There is no derivative obligation:
`deriv (circleMap c R)` is rewritten by `deriv_circleMap` inside `ceq`.

1. **Shape** (`circleShape`, before any rewriting). The lower bound must be `0` (compared at
   reducible transparency). `matchCircle?` recognises `ψ t = circleMap c R (α * t)` through one
   of the lemmas `circleMap_self`, `I_cpow_ofReal` (`I ^ t = circleMap 0 1 (π/2 · t)`),
   `exp_ofReal_mul_I_eq_circleMap` (`exp (t I) = circleMap 0 1 (1 · t)`), `circleMap_one_mul`.
   `α` may be negative (with `T < 0`).
2. **Outer function** (only without `with g`). `autoCircleG` rewrites `F t` so that it only
   depends on `ψ t` (casts pushed, `cos`, `sin` unfolded into exponentials,
   `exp (-x) = (exp x)⁻¹`), abstracts `ψ t` as `z`, and divides by `dz/dt = α (z - c) I`:
   `g z = F / (α (z - c) I)`.
3. **Rewrite.** `integral_congr` (obligation `ceq`) and
   `ChangeVar.intervalIntegral_circleMap_reparam'`
   (`α ≠ 0 → α T = 2π → ∫ t in 0..T, α (γ' (α t) g (γ (α t))) = ∮ z in C(c, R), g z`),
   obligations `hα`, `hT`.
4. **Obligations** `hα`, `hT`, `ceq`, by the circle closers (`closeCircleSideGoals`); in `ceq`,
   powers of `I` (`I ^ 2 = -1`, …) are reduced after `ring_nf` because `ring` treats `I` as an
   opaque atom.

The circle integral is then typically finished with `circle_rational` (not part of this
project).

## Set mode, step by step (`setMode`)

Goal: `∫ x in s, F x = …` (with respect to `volume`), `ψ : ℝ → ℝ`. The rigid form needs `g` and
performs step 1; `change_var!` adds steps 0 and 2. With `using h`, `ψ'` and the proof of `deriv`
come from `h` (in step 0 and step 1), and there is no goal `deriv`.

0. **Outer function** (`change_var!` without `with g`). `ψ'` is computed as in real mode (steps
   1–2, with `hx : x ∈ s`); if `ψ' ≤ 0` is provable on `s`, `|ψ'|` is `-ψ'` and the factor search
   (`findOuter?`) runs with `-ψ'` first, otherwise with `ψ'` first. This `ψ'` serves the search
   only; without `using`, the proof gets its derivative from the goal `deriv`.
1. **Rewrite** (all forms). `MeasureTheory.setIntegral_congr_fun` replaces `F` by
   `fun x => |?ψ' x| • g (ψ x)` (obligations `hs`, `ceq`), then
   `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`, read from right to left, turns
   `∫ x in s, |ψ' x| • g (ψ x)` into `∫ u in ψ '' s, g u` (obligations `deriv`, `hs`, `hinj`;
   `hs` is one goal shared by both lemmas). With `onto T`, `ψ '' s` is then rewritten to `T`
   (obligation `himg`).
2. **Obligations** (`change_var!`): the rigid form's `disch` is `change_var_disch`, so `deriv` goes
   to `change_var_deriv` (a `HasDerivAt`, with the domain facts of `x ∈ s`, turned into
   `HasDerivWithinAt`) and the others to `change_var_side`. In practice `himg` often stays (it needs
   an inverse of `ψ`), as does `ceq` when the integrand mentions `ψ x` only up to algebra under an
   opaque function (the integrands of `MagicFunction/a/IntegralEstimates`, see
   `SpherePacking/Tactic/Test/ChangeVar.lean`).
**Why a separate mode and not one framework for both.** The rigid skeleton is shared: elaboration of
`ψ` and `g`, the metavariable `?ψ'` with its `deriv` goal and trailing data goal, tagged
obligations, `rewriteAndClose` with `disch`, budgets and the report. What differs is the lemma
behind the rewrite, and with it the obligations: the interval lemma (`integral_deriv_smul_comp'`)
needs continuity of `ψ'` and of `g` on the image but neither injectivity nor `|ψ'|`, and computes
the new bounds `ψ a`, `ψ b`; the set lemma needs injectivity, works with `HasDerivWithinAt` on `s`,
and its image `ψ '' s` must be named (`himg`). An interval integral could be sent to set mode
(`intervalIntegral.integral_of_le`), at the price of these extra obligations, so both lemmas are
kept. The set lemma is what non-compact substitutions need, e.g. `s = 1 / t` from `Ioc 0 1` to `Ici
1` (`MagicFunction/a/IntegralEstimates`, see `SpherePacking/Tactic/Test/ChangeVar.lean`).

## Determinism and fail fast

* **Deterministic.** No clock, randomness, IO or concurrency is used here. Lean's heartbeats count
  allocations, not time, so every budget below is reproducible. Checked: the same file compiled
  several times gives byte-identical messages. (An oracle must be deterministic too; its file
  documents it.)
* **Fail fast.** Cheap checks come first (*Checks before any work*), and every potentially slow step
  runs under its own heartbeat budget (`withBudget`), read from an option, in the unit of
  `set_option maxHeartbeats`:
  - `changeVar.sideGoalHeartbeats` (50000): each attempt on one obligation (a closer, a `disch`);
  - `changeVar.ringHeartbeats` (10000): one `ring1` attempt of the search for `g`, each small sign
    proof (`proveSign`, `change_var_abs`, the sign of `ψ'` in set mode);
  - `changeVar.searchHeartbeats` (100000): the whole search for `g` (up to `2 ^ 8` `ring1`
    attempts), so that it is bounded as a whole;
  - `changeVar.fallbackHeartbeats` (50000): the `fun_prop` fallback, the replay of a suggestion.
  This matters because `try`, `first` and `catch` do *not* catch exhausted heartbeats
  (`Core.tryCatch` rethrows runtime exceptions): without budgets a single slow alternative consumed
  the whole budget of the user's command and failed `change_var` as a whole. With them, a slow
  obligation is just left open. Each budget is capped by what remains of the enclosing limit (the
  user's, or an enclosing step's), so nested budgets compose as a minimum and the user's limit is
  enforced inside the steps; `0` removes a per-step cap, while a user `maxHeartbeats 0` keeps the
  caps (they make failures fast); only heartbeats are converted into the error "step budget
  exhausted (option n)", an exhausted `maxRecDepth` propagates as itself. Lean stores
  `maxHeartbeats` multiplied by 1000 in `Core.Context.maxHeartbeats`, a unit mismatch that is easy
  to get wrong. Pinned in `SpherePacking/Tactic/Test/ChangeVar.lean` (*Heartbeat budgets*, with
  `sleep_heartbeats`): the cut of a slow step, `0`, a user `maxHeartbeats 0`, a tighter user limit,
  the error naming the option; the propagation of `maxRecDepth` is *not pinned*. When the default is
  too small, raise the option by hand: e.g. `ceq` on `(x + b + c) ^ 16 * (x - b + c) ^ 16` against
  `((x + c) ^ 2 - b ^ 2) ^ 16` needs more than 50000 for `ring1` and closes with `set_option
  changeVar.sideGoalHeartbeats 150000`; with the exponent 18, `maxHeartbeats` must be raised too,
  since it bounds every step. Such thresholds depend on the speed of Mathlib's `ring`, `simp`,
  `field_simp`, `fun_prop`, so the test of this case is kept commented out in the test file
  (re-tune it by hand if those tactics change).

## Implementation notes (choices and Lean pitfalls met while testing)

* **Module system.** Every file of the `ChangeVar` library is a `module`, so that fully modular
  projects can import it. Two kinds of imports: `public import` for the files whose *lemmas* appear
  in the proofs the tactic builds at the user's site (`IntegrationByParts`, `Log.Deriv`, `Sqrt`,
  `Deriv.Pow`, `Trigonometric.Deriv`, `Trigonometric.DerivHyp`, `Circle`, whose lemmas are in a
  `public section`), and `public meta import` for the files whose *code* runs while the tactic
  elaborates (`Ring`, `FieldSimp`, `FunProp`, `Positivity`, `NormNum`, `DefEqTransformations`,
  `Mathlib.Lean.Meta.Simp`, and `Qq`). All the code is in a `public meta section`.
  `SpherePacking/Tactic/Test/ChangeVar.lean` is itself a `module`.
* **Qq for the terms over `ℝ` (and `ℂ`).** The statements and proof terms whose type is fixed are
  written as typed quotations, `q(HasDerivAt $ψ $v $x)`, instead of `mkAppM` calls:
  `derivStatement`, the domain facts of `withRealVarIn`, `pinAndTidy`, the `fun_prop` fallback of
  `deriveAt`, the obligations `hs`, `hinj`, `himg` of set mode, `g` in circle mode. An ill-typed
  construction is then a compile-time error, and these terms no longer go through `mkAppM`'s
  unification at run time (see *`mkAppM` and outer metavariables*). The code that is polymorphic
  (`factors`, `castIfC`, `boundFacts`, `signFromBounds`, `change_var_bounds`, `change_var_abs`: any
  ordered field, or ℝ and ℂ alike) and the recognition of integrals (an arbitrary value type and
  measure) stay at the level of `Expr`. Two rules keep the behaviour identical, each pinned by a
  test: binders are still made by `withLocalDeclD` with the integral's own name (a quotation
  `q(∀ x ∈ …)` would fix the name `x`), and `ψ' x` is still beta-reduced. The `have e : Q(T) := e`
  that give a type to an `Expr` argument are unchecked assertions (Qq's convention): they are
  only made where the type is fixed by construction.
* **The automation depends on the import closure.** The closers and the fallback call `simp`,
  `fun_prop`, `positivity`, `norm_num`, whose lemma sets are what is imported. This file imports the
  derivative files it relies on (`Deriv.Pow`, `Log.Deriv`, `Sqrt`, `Trigonometric.Deriv`,
  `Trigonometric.DerivHyp`): they used to come transitively through an oracle's library, and without
  them `fun_prop` could not differentiate `sin` or `cosh` (found when the core was separated; `sin`
  pinned in `SpherePacking/Tactic/Test/ChangeVar.lean`). A user's own imports can only add lemmas,
  never remove these.
* **Derivative oracles as an attribute.** As Mathlib's `@[positivity]` extensions: the names of
  the declarations tagged `@[change_var_oracle]` are kept in a persistent environment extension
  (so importing the tagged declaration is what activates it), and evaluated with `evalConstCheck`
  when `deriveAt` runs. A library that cannot be a dependency of this one (an external CAS) adds
  an oracle by importing this file and tagging one `meta` definition; nothing here names it.
* **Expected type of oracle proofs.** A proof built with the power rule has the *inferred* type
  `HasDerivAt ((fun x => x) ^ 2) …` (a pointwise power of functions). `rw` then fails to match
  `fun x => x ^ 2` syntactically. `mkExpectedTypeHint` pins the type to `HasDerivAt ψ v x`.
* **`ring1`, never `ring`, inside `first`.** `ring` that fails to close a goal falls back to
  `ring_nf` and *succeeds*, so `first | ring | …` stops at the wrong alternative.
* **`withReducible` in `matchCircle?`.** Unifying `α * t =?= t` at default transparency unfolds
  real multiplication (Cauchy sequences) and times out; at reducible transparency it fails fast.
* **`apply`, not `refine`, in `change_var_domain`.** `refine` elaborates its term with error
  recovery: a type mismatch is *logged* and the alternative of `first` counts as a success.
  `change_var_domain` also runs outside `runClosed` (inside `fun_prop`, or called by the user), so
  it must fail cleanly by itself; the closers may use `refine`, since they only run through
  `runClosed`.
* **A final `fail` in `change_var_domain`.** When `fun_prop` runs a discharger whose last
  alternative is `…; done` and that fails, the error was reported by `fun_prop` and the goal
  admitted; ending `first` with `fail` makes the failure clean.
* **No `·` inside the automation.** `·` recovers from errors (logs them, admits the goal), so a
  failing branch would look successful; the branches use `rotate_left` instead.
* **Hygiene in quotations.** In `` `(tactic| rintro ⟨x, _, rfl⟩) `` the `rfl` pattern becomes a
  hygienic identifier and is treated as a variable name; `subst h` is used instead.
* **An oracle may read the main goal's context** (`withMainContext`). That is why
  `withRealVar(In)` installs an auxiliary main goal created *inside* the new binders (and after
  the `let`s).
* **Side goals are identified by `MVarId`, not by tag.** Tags (`ceq`, `hv`, …) are shared with
  goals left by earlier calls, and `all_goals` would also run on unrelated goals of the user.
  The same holds for the main goal: its final beta-reduction is done on the `MVarId` that
  `rewriteAndClose` identified, not by a tactic on "the first goal", which is one of the user's
  goals when the main goal was closed by `rfl` (found by review; regression tests in
  `SpherePacking/Tactic/Test/ChangeVar.lean`).
* **`kabstract` at reducible transparency** (search for `g`, circle mode): the match is meant to be
  syntactic; at default transparency a near miss (`-(1 * t)` against `-1 * t`) unfolds real
  arithmetic and times out. For the same reason `ψ t` and the integrand are normalised alike.
* **Error recovery inside `Tactic.run`.** By default a failing tactic run through `Tactic.run` is
  *recovered*: its error is logged and the goal closed by `sorry`, so the call reports success.
  Every attempt on an obligation and every sign proof goes through `runClosed` (`withoutRecover`,
  no `sorry`, no leftover metavariable, state and message log restored on failure); the
  `fun_prop` fallback of `deriveAt` uses `withoutRecover` and a `sorry` check directly, to keep
  `fun_prop`'s own error message.
* **`mkAppM` and outer metavariables.** `mkAppM` works at a deeper metavariable depth and cannot
  assign metavariables (universe levels included) created before the call; lemma arguments are
  therefore unified by hand at the current depth (`boundFacts`, `iffMpr`), and instance
  arguments that unification leaves open are synthesised.
* **Eager `(← …)` in `do` conditions.** In `if c && (← f x) then`, `f x` runs *before* `c` is
  tested; a monadic test calling `getArg!` there panicked on goals of other shapes. Such tests
  are pure (`isZero` in `change_var_bounds`).
* **`done` first in the `ceq` closer.** With a clean derivative `simp only` often closes `ceq` by
  itself, and a following `ring1` would then fail on "no goals".
* **`?ψ'` is a data goal, placed last.** Hidden from the goal list, an unassigned `?ψ'` (e.g.
  when `deriv` is left as `sorry`) made Lean report "don't know how to synthesize" five times at
  the end of the proof. Listed last, like the data goals of `apply` and `refine`, it disappears
  once `deriv` is proved and can be closed by `sorry` otherwise. It is a *natural* metavariable,
  so the proof of `deriv` assigns it by unification; that is why `deriv` must be proved before
  `hv` and `ceq`, which mention it.
* **`(disch := …)` right after the name.** Written after `with g`, it parsed as a named argument
  of the term `g`; the configuration goes where Mathlib puts it (`simp (disch := …)`).
* **`rewrite`, then `rfl` on the main goal.** `rw` closes the main goal by `rfl` when the two
  sides become equal (typical after `himg`), and the goal list then no longer starts with it. The
  modes call `rewrite`, which never closes it, and `rewriteAndClose` tries `with_reducible rfl` on
  the main goal at the end, as `rw` would.
* **Implicit arguments given explicitly.** Left implicit, the `f'` of
  `integral_image_eq_integral_abs_deriv_smul` got its own metavariable, and unification assigned
  `?ψ'` to it rather than the converse: the goals showed an anonymous `?m` instead of `?ψ'`.
  `(f := ψ) (f' := ?ψ')` are passed explicitly.
* **`onto` is a keyword clause, hence a reserved token.** `onto T` follows the term `ψ`; were
  `onto` an ordinary identifier, `ψ onto T` would parse as an application. Declaring the atom
  `" onto "` reserves `onto` as a keyword in importing files (it is not an identifier anywhere in
  Mathlib, only a word in comments). Data goes in keyword clauses (`onto`,
  `with`, `using`, as in Mathlib's `apply_fun … using`, `gcongr … with`); `(name := …)` options are
  configuration, here only `(disch := tac)`.
* **Suggestions follow the user's notations.** `change_var?` prints `g` with the notations open
  where it runs (`rexp` with `open Real`, `Real.exp` otherwise), with binder types, so that the
  suggested call replays verbatim in the same file.
* **No hygiene marks in suggestions.** Names written inside a quotation (`` `(tactic| case deriv
  => …) ``) get macro scopes and print as `deriv✝`, which does not replay; every name of a
  suggestion is built with `mkIdent`.
* **Numerals in printed proofs.** `hasDerivAt_const x 2` leaves the type of `2` free, so it would
  elaborate in `ℕ`; printed numeral arguments are ascribed (`(2 : ℝ)`) unless they are natural
  numbers.
-/

public meta section

namespace ChangeVar

open Lean Meta Elab Tactic Qq

/-- An interval integral `intervalIntegral f a b μ`. Its arguments are
`[E, inst, inst, f, a, b, μ]`; `f` is at index 3, the bounds at 4 and 5. -/
def isIntervalIntegral (e : Expr) : Bool :=
  e.isAppOfArity ``intervalIntegral 7

/-- A set integral `∫ x in s, F x ∂μ`, i.e. `MeasureTheory.integral (μ.restrict s) F`. Its
arguments are `[α, E, inst, inst, mα, μ.restrict s, F]`: the restricted measure at index 5
(`Measure.restrict` with arguments `[α, mα, μ, s]`), `F` at index 6. -/
def isSetIntegral (e : Expr) : Bool :=
  e.isAppOfArity ``MeasureTheory.integral 7 &&
    (e.getArg! 5).isAppOfArity ``MeasureTheory.Measure.restrict 4

/-- The common skeleton of the integral finders: the first subterm of `e` (pre-order traversal,
so the outermost/leftmost one) that satisfies `p` *and has no loose bound variable*. `Expr.find?`
also descends under binders (`∀ y, ∫ x in 0..y, …`), where a match may mention the bound `y` as
a loose bound variable: such a term is not a valid expression on its own, and using it gave an
internal `unexpected bound variable` error. These matches are skipped; `changeVarCore` reports
them when nothing else is found. -/
def findClosed? (p : Expr → Bool) (e : Expr) : Option Expr :=
  e.find? fun s => p s && !s.hasLooseBVars

/-- First interval integral of `e` that is a closed term (see `findClosed?`). -/
def findIntervalIntegral? (e : Expr) : Option Expr :=
  findClosed? isIntervalIntegral e

/-- First set integral of `e` that is a closed term (see `findClosed?`). -/
def findSetIntegral? (e : Expr) : Option Expr :=
  findClosed? isSetIntegral e

/-- Run `k` with a fresh real variable `x`.

A derivative oracle may call `withMainContext`, i.e. work in the local context of the *main goal*,
not in the ambient `MetaM` context. To make `x` visible to it we temporarily replace the
goal list by a dummy goal `True` created inside the binder, and restore the real goals afterwards
(also on failure, `try … finally`). -/
def withRealVar {α : Type} (n : Name) (k : Expr → TacticM α) : TacticM α :=
  withLocalDeclD n (mkConst ``Real) fun x => do
    let saved ← getGoals
    let aux ← mkFreshExprMVar (mkConst ``True)
    setGoals [aux.mvarId!]
    try k x finally setGoals saved

/-- Heartbeat budget of each attempt on one obligation (a closer, a `disch` tactic, a sign proof of
`withRealVarIn`), in the unit of `set_option maxHeartbeats`; `0` removes this per-step cap. Budgets
only make failures fast: a step that succeeds within its budget behaves exactly as without it. -/
register_option changeVar.sideGoalHeartbeats : Nat := {
  defValue := 50000
  descr := "change_var: heartbeat budget of each attempt on one obligation (0: no per-step cap)"
}

/-- Heartbeat budget of one `ring1` attempt of the search for `g`, and of each small sign proof
(`proveSign`, `change_var_abs`, the sign of `ψ'` in set mode); `0` removes this per-step cap. -/
register_option changeVar.ringHeartbeats : Nat := {
  defValue := 10000
  descr := "change_var: heartbeat budget of one ring1 attempt or sign proof (0: no per-step cap)"
}

/-- Heartbeat budget of the whole search for `g` (`findOuter?`: up to `2 ^ 8` `ring1` attempts),
so that it is bounded as a whole and not only attempt by attempt; `0` removes this cap. -/
register_option changeVar.searchHeartbeats : Nat := {
  defValue := 100000
  descr := "change_var: heartbeat budget of the whole search for g (0: no cap)"
}

/-- Heartbeat budget of the `fun_prop` fallback of the derivative, and of the replay of a script
suggested by `change_var?`; `0` removes this per-step cap. -/
register_option changeVar.fallbackHeartbeats : Nat := {
  defValue := 50000
  descr := "change_var: heartbeat budget of the fun_prop fallback and of replays (0: no cap)"
}

/-- Run `k` with its own heartbeat budget, read from the option `opt` (in the unit of
`set_option maxHeartbeats`; `Core.Context.maxHeartbeats` stores it multiplied by 1000, see
`getMaxHeartbeats` in Lean core), counted from now, and turn the exhaustion of *that* budget into an
ordinary error naming the option.

Why: `try`, `first` and `catch` do not catch *runtime* exceptions (exhausted heartbeats, maximal
recursion depth; see `Core.tryCatch` in Lean core). Without a budget, one slow alternative would
consume the whole budget of the user's command and make `change_var` fail as a whole, after a long
time, instead of failing that alternative quickly and moving on (fail fast).

How it composes:
* the budget is capped by what remains of the *enclosing* limit (the user's `maxHeartbeats`, or an
  enclosing step's budget): when less remains than the step would get, `k` runs under the enclosing
  limit unchanged, so nested budgets compose as a minimum and the user's limit is enforced inside
  the step, with Lean's own error;
* a step budget of `0` removes this per-step cap; a user `maxHeartbeats 0` does *not* remove it
  (the caps exist to fail fast, and an unbounded closer could otherwise run forever);
* only an exhausted heartbeat budget is converted; an exhausted `maxRecDepth` propagates as itself.

Heartbeats count allocations, not time, so budgets keep the tactic deterministic. -/
def withBudget {α : Type} (opt : Lean.Option Nat) (k : TacticM α) : TacticM α := do
  let n := opt.get (← getOptions)
  let step := n * 1000
  let c ← readThe Core.Context
  let now ← IO.getNumHeartbeats
  -- What remains of the enclosing limit; `none` if it is unlimited.
  let remaining? : Option Nat :=
    if c.maxHeartbeats == 0 then none else some (c.maxHeartbeats - (now - c.initHeartbeats))
  if step == 0 || remaining?.any (· ≤ step) then return ← k
  withTheReader Core.Context (fun c => { c with initHeartbeats := now, maxHeartbeats := step }) <|
    tryCatchRuntimeEx k fun e =>
      if e.isMaxHeartbeat then
        throwError "change_var: step budget exhausted ({opt.name} {n}); raise it with \
          `set_option {opt.name} <n>`"
      else throw e

/-- Run the tactic `tac` on the goal `g` alone, within the budget of option `opt` (see
`withBudget`), and report whether it *really* closed it.

Three safeguards, all found necessary by testing:
* `withoutRecover`: by default a failing tactic inside `Tactic.run` is *recovered*: its error is
  logged and the goal is closed by `sorry`, so `Tactic.run` reports no remaining goal although
  the tactic failed (e.g. `first | positivity | (norm_num; done)` on the false `0 < -1`);
* the proof must contain neither `sorry` nor an unassigned metavariable;
* on failure, the state *and the message log* are restored, so a failed attempt leaves no
  trace. -/
def runClosed (g : MVarId) (tac : TacticM Unit) (opt : Lean.Option Nat) : TacticM Bool := do
  let s ← saveState
  let log ← Core.getMessageLog
  let fail : TacticM Bool := do s.restore; Core.setMessageLog log; return false
  try
    let rest ← withBudget opt do pure (← Tactic.run g (withoutRecover tac))
    let pf ← instantiateMVars (mkMVar g)
    if rest.isEmpty && !pf.hasSorry && !pf.hasExprMVar then return true
    fail
  catch _ => fail

/-- A bound on a variable, read off a membership hypothesis: `proof : bound ≤ x` (or `<`, or the
reverse for an upper bound). -/
structure BoundFact where
  proof : Expr
  var : Expr
  bound : Expr
  isLower : Bool
  isStrict : Bool

/-- The bounds on `x` given by a hypothesis `h : x ∈ S`, for `S` one of
`Icc Ico Ioc Ioo Ici Iic Ioi Iio` (through `Set.mem_Icc`, …) or `uIcc uIoc` (unfolded first to
`Icc (a ⊓ b) (a ⊔ b)`, `Ioc (min a b) (max a b)`). Other hypotheses give no bound. -/
def boundFacts (h : Expr) : MetaM (Array BoundFact) := do
  let ty := (← instantiateMVars (← inferType h)).consumeMData
  unless ty.isAppOfArity ``Membership.mem 5 do return #[]
  let x := ty.getArg! 4
  let mut S := ty.getArg! 3
  let mut h := h
  -- `uIcc`/`uIoc` are definitions over `Icc`/`Ioc`: unfold, keeping the proof by a type hint.
  if S.isAppOf ``Set.uIcc || S.isAppOf ``Set.uIoc then
    let some S' ← unfoldDefinition? S | return #[]
    S := S'.headBeta
    h ← mkExpectedTypeHint h (← mkAppM ``Membership.mem #[S, x])
  let some n := S.getAppFn.constName? | return #[]
  let lemmas := [(``Set.Icc, ``Set.mem_Icc), (``Set.Ico, ``Set.mem_Ico), (``Set.Ioc, ``Set.mem_Ioc),
    (``Set.Ioo, ``Set.mem_Ioo), (``Set.Ici, ``Set.mem_Ici), (``Set.Iic, ``Set.mem_Iic),
    (``Set.Ioi, ``Set.mem_Ioi), (``Set.Iio, ``Set.mem_Iio)]
  let some (_, L) := lemmas.find? (·.1 == n) | return #[]
  -- Instantiate the arguments of `Set.mem_*` (`x ∈ S ↔ bounds`) with metavariables and unify
  -- its left-hand side with the type of `h` here (not through `mkAppM`, which works at a deeper
  -- metavariable depth and cannot assign these metavariables, universe levels included).
  let c ← mkConstWithFreshMVarLevels L
  let (mvs, _, iff) ← forallMetaTelescopeReducing (← inferType c)
  let some (lhs, rhs) := iff.iff? | return #[]
  unless ← isDefEq lhs (← inferType h) do return #[]
  let p ← instantiateMVars (mkApp4 (mkConst ``Iff.mp) lhs rhs (mkAppN c mvs) h)
  -- `p` proves an inequality or a conjunction of two; split it.
  let mut todo := #[p]
  let mut out := #[]
  while h' : todo.size > 0 do
    let q := todo.back
    todo := todo.pop
    let t ← instantiateMVars (← inferType q)
    if t.isAppOfArity ``And 2 then
      todo := todo.push (← mkAppM ``And.left #[q]) |>.push (← mkAppM ``And.right #[q])
    else if t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4 then
      let strict := t.isAppOfArity ``LT.lt 4
      let (l, r) := (t.getArg! 2, t.getArg! 3)
      if r == x then out := out.push ⟨q, x, l, true, strict⟩
      else if l == x then out := out.push ⟨q, x, r, false, strict⟩
  return out

/-- Prove a sign condition on a bound (`0 < b`, `0 ≤ b`, `b < 0`, `b ≤ 0`): `positivity` (on `-b`
for a negative bound), or `norm_num` (with `⊔`/`⊓` split) for numerical bounds such as
`(-2) ⊔ (-1) < 0`, within a small budget (`runClosed`). `none` on failure. -/
def proveSign (ty : Expr) : TacticM (Option Expr) := do
  let g ← mkFreshExprMVar ty
  let tac ← `(tactic| first
    | positivity
    -- `b < 0` / `b ≤ 0` as `0 < -b` / `0 ≤ -b` (e.g. `b = -exp 1`)
    | (apply neg_pos.mp; (try simp only [neg_neg]); positivity)
    | (apply neg_nonneg.mp; (try simp only [neg_neg]); positivity)
    | (norm_num [sup_lt_iff, sup_le_iff, lt_inf_iff, le_inf_iff]; done))
  if ← runClosed g.mvarId! (evalTactic tac) changeVar.ringHeartbeats then
    return some (← instantiateMVars g)
  return none

/-- `L.mpr p` for an iff lemma `L : … → (a ↔ b)` and `p : b`, with the arguments of `L` found by
unification at the current metavariable depth (`mkAppM` cannot assign metavariables created
outside it, universe levels included). `none` if `p` does not fit. -/
def iffMpr (L : Name) (p : Expr) : MetaM (Option Expr) := do
  let c ← mkConstWithFreshMVarLevels L
  let (mvs, bis, iff) ← forallMetaTelescopeReducing (← inferType c)
  let some (lhs, rhs) := iff.iff? | return none
  unless ← isDefEq rhs (← inferType p) do return none
  -- Instance arguments that do not occur in `rhs` (e.g. `[AddLeftStrictMono α]` of `neg_pos`)
  -- are not assigned by unification: synthesise them.
  for (m, bi) in mvs.zip bis do
    if bi.isInstImplicit && !(← m.mvarId!.isAssigned) then
      let some inst ← (try some <$> synthInstance (← inferType m) catch _ => pure none)
        | return none
      m.mvarId!.assign inst
  let pf ← instantiateMVars (mkApp4 (mkConst ``Iff.mpr) lhs rhs (mkAppN c mvs) p)
  return if pf.hasExprMVar then none else some pf

/-- `0 < e` or `e < 0` (`pos := true`/`false`) from the bound facts on `e`, or `none`. -/
def signFromBounds (facts : Array BoundFact) (e : Expr) (pos : Bool) : TacticM (Option Expr) := do
  let zero ← mkNumeral (← inferType e) 0
  for f in facts do
    unless ← withReducible (isDefEq f.var e) do continue
    if pos && f.isLower then
      -- `0 < l ≤ x` or `0 ≤ l < x`
      if f.isStrict then
        if let some hl ← proveSign (← mkAppM ``LE.le #[zero, f.bound]) then
          return some (← mkAppM ``lt_of_le_of_lt #[hl, f.proof])
      if let some hl ← proveSign (← mkAppM ``LT.lt #[zero, f.bound]) then
        return some (← mkAppM ``lt_of_lt_of_le #[hl, ← if f.isStrict then
          mkAppM ``le_of_lt #[f.proof] else pure f.proof])
    if !pos && !f.isLower then
      -- `x ≤ u < 0` or `x < u ≤ 0`
      if f.isStrict then
        if let some hu ← proveSign (← mkAppM ``LE.le #[f.bound, zero]) then
          return some (← mkAppM ``lt_of_lt_of_le #[f.proof, hu])
      if let some hu ← proveSign (← mkAppM ``LT.lt #[f.bound, zero]) then
        return some (← mkAppM ``lt_of_le_of_lt #[← if f.isStrict then
          mkAppM ``le_of_lt #[f.proof] else pure f.proof, hu])
  return none

/-- Close `0 < e`, `0 ≤ e`, `e ≠ 0`, `-e ≠ 0`, `0 < -e`, `e < 0` or `e ≤ 0` from the bounds that
membership hypotheses `x ∈ S` in the local context give on `e` (see `boundFacts`). Fails, without
changing anything, when no bound applies.

This is the only part of `change_var_domain` that uses the domain. `positivity` never reads
hypotheses, and it refuses the shapes `e < 0`, `e ≤ 0` outright ("not a positivity goal"); here
the bound itself must have a sign that `positivity` or `norm_num` proves (`proveSign`). Best
effort: a strict sign needs a strict bound or a bound of strict sign (`x ≤ 0` on `Ioc (-1) 0` is
not found), and bounds that are not numerals or `positivity`-provable give nothing.

The proof is assembled from order lemmas (`lt_of_lt_of_le`, `ne_of_gt`, `neg_pos`, …), so no
tactic block can report an error halfway. -/
elab "change_var_bounds" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let mut facts := #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail do facts := facts ++ (← boundFacts d.toExpr)
  if facts.isEmpty then throwError "change_var_bounds: no membership hypothesis with a bound"
  -- Pure on purpose: in `do` notation `c && (← f x)` runs `f x` *before* testing `c`, so a
  -- monadic test here would evaluate `getArg!` on targets of the wrong shape (and panic).
  let isZero (e : Expr) : Bool :=
    e.numeral? == some 0 || (e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).rawNatLit? == some 0)
  -- `e ≠ 0` (also `-e ≠ 0`): from `0 < e` or `e < 0`.
  let ne? (e : Expr) : TacticM (Option Expr) := do
    if let some p ← signFromBounds facts e true then return some (← mkAppM ``ne_of_gt #[p])
    if let some p ← signFromBounds facts e false then return some (← mkAppM ``ne_of_lt #[p])
    return none
  let proof? : Option Expr ← do
    if target.isAppOfArity ``Ne 3 && isZero (target.getArg! 2) then
      let e := target.getArg! 1
      if e.isAppOfArity ``Neg.neg 3 then
        match ← ne? (e.getArg! 2) with
        | some p => iffMpr ``neg_ne_zero p
        | none => pure none
      else ne? e
    else if target.isAppOfArity ``LT.lt 4 && isZero (target.getArg! 2) then
      let e := target.getArg! 3
      if e.isAppOfArity ``Neg.neg 3 then
        match ← signFromBounds facts (e.getArg! 2) false with
        | some p => iffMpr ``neg_pos p
        | none => pure none
      else signFromBounds facts e true
    else if target.isAppOfArity ``LE.le 4 && isZero (target.getArg! 2) then
      match ← signFromBounds facts (target.getArg! 3) true with
      | some p => pure (some (← mkAppM ``le_of_lt #[p]))
      | none => pure none
    -- `e < 0`, `e ≤ 0` (negative domains, e.g. `hneg : x < 0` on `[[-2, -1]]`): `positivity` does
    -- not handle these shapes at all ("not a positivity goal"), so this is their only route.
    else if target.isAppOfArity ``LT.lt 4 && isZero (target.getArg! 3) then
      signFromBounds facts (target.getArg! 2) false
    else if target.isAppOfArity ``LE.le 4 && isZero (target.getArg! 3) then
      match ← signFromBounds facts (target.getArg! 2) false with
      | some p => pure (some (← mkAppM ``le_of_lt #[p]))
      | none => pure none
    else pure none
  let some p := proof? |
    let shown := facts.toList.map fun f =>
      let rel := if f.isStrict then "<" else "≤"
      if f.isLower then m!"{f.bound} {rel} {f.var}" else m!"{f.var} {rel} {f.bound}"
    throwError "change_var_bounds: the bounds{indentD (MessageData.joinSep shown ", ")}\nread from \
      the hypotheses `x ∈ S` do not give{indentExpr target}\n(the sign of a bound must follow by \
      `positivity` or `norm_num`; a strict sign needs a strict bound or a bound of strict sign)"
  let p ← instantiateMVars p
  if p.hasExprMVar || p.hasSorry then
    throwError "change_var_bounds: incomplete proof for{indentExpr target}"
  unless ← isDefEq (← inferType p) target do
    throwError "change_var_bounds: proof of the wrong type for{indentExpr target}"
  goal.assign p
  replaceMainGoal []

/-- Discharger for the side conditions met while differentiating and checking continuity:
`0 < e`, `0 ≤ e`, `e ≠ 0`. Alternatives, in order:

1. `positivity` (no hypotheses used): `x ^ 2 + 1 ≠ 0`, `0 < exp x`, …;
2. `change_var_bounds`: the bounds given by a hypothesis `x ∈ S` (`S` an interval: `Icc`, `Ioc`,
   `Ici`, `Ioi`, `uIcc`, …), whose sign is proved by `positivity` or `norm_num`. This gives `0 < x`
   on `[[1, e]]` or `Ioc 0 1`, and `x < 0`, `x ≠ 0`, `-x ≠ 0` on `[[-2, -1]]` (`positivity` alone
   never gives these: it ignores hypotheses and refuses `x < 0`);
3. an assumption `0 < e` or `e < 0` (e.g. the `hpos` of `withRealVarIn`) for `e ≠ 0`;
4. `simp` with all hypotheses and `√e = 0 ↔ e ≤ 0`, for goals like `2 * √x ≠ 0`;
5. `fail`.

`apply` is used instead of `refine` so that a goal of the wrong shape fails the alternative (see
the module notes), and the final `fail` keeps `fun_prop` from reporting a failed `done` as an
error. -/
macro "change_var_domain" : tactic => `(tactic| first
  | positivity
  | change_var_bounds
  | (apply ne_of_gt; assumption)
  | (apply ne_of_lt; assumption)
  | (simp [*, Real.sqrt_eq_zero']; done)
  | fail)

/-- `withRealVar` for real mode: the fresh `x` comes with `hx : x ∈ dom`, the domain on which the
derivative is needed (`Set.uIcc a b` for `integral_deriv_smul_comp'`; the set `s` in set mode
and in `change_var_deriv`, any interval understood by `boundFacts` giving sign facts).

When `change_var_domain` proves `0 < x` (resp. `x < 0`), `hpos : 0 < x` (resp. `hneg : x < 0`) and
`hne : x ≠ 0` are added as `let`-bound locals: an oracle closes the premises of its rules (`x ≠ 0`
for `HasDerivAt.log`) with tactics such as `assumption`, `positivity`, `linarith`, which see the
local context but cannot use `hx`.
They are `let`s, not hypotheses, because their values are known: abstracting them with
`mkLambdaFVars` turns them into `let` expressions inside the proof, so the final proof term only
quantifies over `x` and `hx`.

`k` receives `x` and the array of binders to abstract over (`x`, `hx` and the `let`s, if any).
The auxiliary main goal is created inside all binders so that an oracle reading the main goal's
context sees them. -/
def withRealVarIn {α : Type} (n : Name) (dom : Expr) (k : Expr → Array Expr → TacticM α) :
    TacticM α :=
  have dom : Q(Set ℝ) := dom
  withLocalDeclD n q(ℝ) fun x => do
    have x : Q(ℝ) := x
    withLocalDeclD `hx q($x ∈ $dom) fun hx => do
      let saved ← getGoals
      let run (bs : Array Expr) : TacticM α := do
        let aux ← mkFreshExprMVar (mkConst ``True)
        setGoals [aux.mvarId!]
        k x bs
      try
        -- Try `0 < x`, then `x < 0`; the first that `change_var_domain` proves becomes a `let`.
        let tryProve (ty : Expr) : TacticM (Option Expr) := do
          let hp ← mkFreshExprMVar ty
          let tac ← `(tactic| change_var_domain)
          if ← runClosed hp.mvarId! (evalTactic tac) changeVar.sideGoalHeartbeats then
            return some (← instantiateMVars hp)
          return none
        if let some hpv ← tryProve q(0 < $x) then
          withLetDecl `hpos q(0 < $x) hpv fun hpos => do
            have hpos : Q(0 < $x) := hpos
            withLetDecl `hne q($x ≠ 0) q(LT.lt.ne' $hpos) fun hnef =>
              run #[x, hx, hpos, hnef]
        else if let some hnv ← tryProve q($x < 0) then
          withLetDecl `hneg q($x < 0) hnv fun hneg => do
            have hneg : Q($x < 0) := hneg
            withLetDecl `hne q($x ≠ 0) q(LT.lt.ne $hneg) fun hnef =>
              run #[x, hx, hneg, hnef]
        else run #[x, hx]
      finally setGoals saved


/-- Factors of a product, used by the search for the outer function.

`a * b ↦ factors a ++ factors b`, and, so that quotients and signs can be matched factor by
factor, `a / b ↦ factors a ++ (factors b)⁻¹`, `(a * b)⁻¹ ↦ a⁻¹, b⁻¹`, `-a ↦ -1 :: factors a`.
These are rewritings of the *search* only: the identity finally used is checked by `ring1` in
`ceq`, so the splitting just has to be sound up to `ring`, which it is. -/
partial def factors (e : Expr) : MetaM (List Expr) := do
  if e.isAppOfArity ``HMul.hMul 6 then
    return (← factors (e.getArg! 4)) ++ (← factors (e.getArg! 5))
  if e.isAppOfArity ``HDiv.hDiv 6 then
    return (← factors (e.getArg! 4)) ++
      (← (← factors (e.getArg! 5)).mapM fun f => mkAppM ``Inv.inv #[f])
  if e.isAppOfArity ``Inv.inv 3 then
    return ← (← factors (e.getArg! 2)).mapM fun f => mkAppM ``Inv.inv #[f]
  if e.isAppOfArity ``Neg.neg 3 then
    let m ← mkAppM ``Neg.neg #[← mkNumeral (← inferType e) 1]
    return m :: (← factors (e.getArg! 2))
  return [e]

/-- `e₁ * e₂ * … * eₙ` (left-nested), or the numeral `1 : ty` for the empty list (a numeral, not
`One.one`, so that it prints as `1` in reports and suggestions). -/
def mkProd (ty : Expr) : List Expr → MetaM Expr
  | [] => mkNumeral ty 1
  | e :: es => es.foldlM (fun acc f => mkAppM ``HMul.hMul #[acc, f]) e

/-- `(e : ℂ)` when the integrand is complex-valued, `e` otherwise. The derivative `v` is always
real; it is cast before being compared with factors of a complex integrand. -/
def castIfC (isC : Bool) (e : Expr) : MetaM Expr :=
  if isC then mkAppM ``Complex.ofReal #[e] else pure e

/-- Search only: does `ring1` (possibly after `push_cast`) prove `lhs = rhs`? The state is always
restored, so no proof is kept; the identity is proved again later, as part of `ceq`. -/
def ringEq (lhs rhs : Expr) : TacticM Bool := do
  let s ← saveState
  let g ← mkFreshExprMVar (← mkEq lhs rhs)
  let ok ← runClosed g.mvarId! (evalTactic (← `(tactic| first | ring1 | (push_cast; ring1))))
    changeVar.ringHeartbeats
  s.restore
  return ok

/-! ### Derivative oracles: the extension point

The only step of `change_var` that this file cannot do with Mathlib alone is computing an
*explicit* derivative `ψ'` (the search for `g` needs it as an expression, and so do the scripts of
`change_var?`). It is delegated to *derivative oracles*: declarations of type `DerivOracle` tagged
`@[change_var_oracle]`, in any file that imports this one (as Mathlib's `@[positivity]`
extensions). An oracle receives `ψ` and a point `x` (in the context built by `withRealVarIn`, with
the domain facts) and returns a value `v` with a proof of `HasDerivAt ψ v x`, or `none`. This file
registers none; without any, only the `fun_prop` fallback of `deriveAt` remains (an opaque
`deriv ψ x`). Nothing an oracle returns is trusted: its proof is checked by the kernel like any
other, and every derivative enters the change of variables through an obligation.

**Activation is silent.** An oracle is active as soon as the file that declares it is imported,
directly or *transitively*: importing a library that happens to import an oracle changes what
`change_var!`, `change_var_deriv` and `change_var?` compute (an explicit `ψ'` instead of the
opaque `deriv`), with no change in the user's file. The report of `change_var?` names the source of
the derivative, and the option `changeVar.derivOracles` switches every oracle off. -/

/-- A derivative oracle for `change_var`, registered with `@[change_var_oracle]`. -/
structure DerivOracle where
  /-- Shown in the report of `change_var?` as the source of the derivative. -/
  name : String
  /-- Given `ψ` (a function) and a point `x`, an explicit derivative `v` with a proof of
  `HasDerivAt ψ v x`, or `none` when the oracle does not apply. -/
  run : Expr → Expr → TacticM (Option (Expr × Expr))

/-- The declarations tagged `@[change_var_oracle]`, in import order, then in declaration order. -/
initialize derivOracleExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/-- `@[change_var_oracle]` registers a declaration of type `ChangeVar.DerivOracle` (a `meta`
definition, global) as a derivative oracle of `change_var`. Every file that imports the tagged
declaration, even transitively, uses it (see *Derivative oracles*). -/
initialize registerBuiltinAttribute {
  name := `change_var_oracle
  descr := "registers a derivative oracle for change_var (of type ChangeVar.DerivOracle)"
  applicationTime := .afterCompilation
  add := fun declName _ kind => do
    ensureAttrDeclIsMeta `change_var_oracle declName kind
    unless kind == AttributeKind.global do
      throwError "invalid attribute 'change_var_oracle', must be global"
    modifyEnv (derivOracleExt.addEntry · declName)
}

/-- The registered derivative oracles, evaluated from their declarations. -/
def registeredOracles : TacticM (Array DerivOracle) := do
  let env ← getEnv
  let opts ← getOptions
  (derivOracleExt.getState env).mapM fun n =>
    IO.ofExcept <| unsafe env.evalConstCheck DerivOracle opts ``DerivOracle n

/-- Whether `change_var` uses the registered derivative oracles (default `true`). With `false`, a
derivative is either given with `using h` or obtained from the `fun_prop` fallback (opaque
`deriv ψ x`), exactly as when no oracle is imported. -/
register_option changeVar.derivOracles : Bool := {
  defValue := true
  descr := "whether change_var uses the registered derivative oracles (@[change_var_oracle])"
}

/-- Why the derivative oracles gave no explicit derivative: switched off by the option, none
imported, or every registered one tried without success (named). -/
def fallbackReason (enabled : Bool) (tried : Array String) : String :=
  if !enabled then "derivative oracles switched off by `changeVar.derivOracles`"
  else if tried.isEmpty then "no derivative oracle imported"
  else s!"derivative oracles tried without success: {", ".intercalate tried.toList}"

/-- For a derivative from the `fun_prop` fallback (source `src` from `deriveAt`), why it is
opaque and what to do, appended to the messages that need an explicit `ψ'`; empty otherwise. -/
def fallbackHint (src : String) : MessageData :=
  if !src.startsWith "fallback" then m!"" else
  let remedy :=
    if (src.splitOn "switched off").length > 1 then
      ", or switch the oracles back on (`set_option changeVar.derivOracles true`)"
    else if (src.splitOn "no derivative oracle imported").length > 1 then
      ", or import a derivative oracle"
    else ""
  let why := (src.splitOn "; ").getD 1 ""
  m!"\n(`ψ'` is the opaque `deriv` of the `fun_prop` fallback: {why}. Give the derivative with \
    `using h`{remedy}.)"

/-- The source of a derivative for the report of `change_var?`: for the fallback, its reason on a
line of its own (so that a long reason does not break the line of the derivative). -/
def srcLine (src : String) : MessageData :=
  match src.splitOn "; " with
  | [what, why] => m!"{what})\n  (no explicit derivative: {why}"
  | _ => m!"{src}"

/-- Derivative of `ψ` at `x` with a proof of `HasDerivAt ψ v x`, and the name of its source (for
the report of `change_var?`).
First the registered derivative oracles, in order (unless `changeVar.derivOracles` is `false`),
which return an explicit `v` (e.g. `2 * x ^ (2 - 1) * 1`). Their output is not
normalised; the callers (`realMode` and `setMode` in `change_var!`, `change_var_deriv`) clean it
with `tidy`. If none applies, the fallback proves differentiability with `fun_prop` (premises by
`change_var_domain`) and returns the opaque `v = deriv ψ x`: the change of variables is still
correct, but the search for `g` then succeeds only when `deriv ψ x` is a factor of the integrand;
otherwise give `g` with `with`, or the derivative with `using h`. -/
def deriveAt (ψ x : Expr) : TacticM (Expr × Expr × String) := do
  let enabled := changeVar.derivOracles.get (← getOptions)
  let mut tried : Array String := #[]
  if enabled then
    for oracle in ← registeredOracles do
      if let some (v, p) ← oracle.run ψ x then
        return (v, p, oracle.name)
      tried := tried.push oracle.name
  -- Why there is no explicit derivative: shown in the report and in the messages that follow.
  let reason := fallbackReason enabled tried
  have ψ : Q(ℝ → ℝ) := ψ
  have x : Q(ℝ) := x
  let hd ← mkFreshExprMVar q(DifferentiableAt ℝ $ψ $x)
  -- Not `runClosed`: on failure we want `fun_prop`'s own explanation in the error.
  let rest ← try withBudget changeVar.fallbackHeartbeats do
      pure (← Tactic.run hd.mvarId! (withoutRecover <|
        evalTactic (← `(tactic| fun_prop (disch := change_var_domain)))))
    catch e => throwError "change_var: could not differentiate{indentExpr ψ}\n\
      on the integration domain ({reason}; then `fun_prop` said:\
      {indentD e.toMessageData})"
  unless rest.isEmpty && !(← instantiateMVars hd).hasSorry do
    throwError "change_var: could not differentiate{indentExpr ψ}"
  have hd : Q(DifferentiableAt ℝ $ψ $x) := ← instantiateMVars hd
  return (q(deriv $ψ $x), q(DifferentiableAt.hasDerivAt $hd),
    s!"fallback: `fun_prop` differentiability, opaque `deriv`; {reason}")

/-- Arithmetic heads: the symbols `ring` normalises. Every other head (`Real.exp`, `Real.sin`,
`Real.log`, …) is an opaque atom for `ring`. -/
def arithHeads : List Name :=
  [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HPow.hPow, ``Neg.neg, ``Inv.inv,
    ``HSMul.hSMul, ``OfNat.ofNat, ``Complex.ofReal, ``Nat.cast, ``Int.cast]

/-- The non-arithmetic head symbols of the subterms of `e` that contain the variable `x`
(e.g. `{Real.exp}` for `exp (x ^ 2) * x`). -/
partial def opaqueHeads (x : FVarId) (e : Expr) : NameSet :=
  if !e.containsFVar x then {} else
  match e with
  | .app .. =>
    let here := match e.getAppFn.constName? with
      | some n => if arithHeads.contains n then {} else ({} : NameSet).insert n
      | none => {}
    e.getAppArgs.foldl (fun acc a => acc.append (opaqueHeads x a)) here
  | .lam _ t b _ | .forallE _ t b _ => (opaqueHeads x t).append (opaqueHeads x b)
  | .mdata _ b => opaqueHeads x b
  | _ => {}

/-- Search an outer function `g` with `body = v • g (ψ x)`.

Algorithm:
1. Split `body` and `v` into factors (`factors`) and separate those that depend on `x` (`bx`,
   `vx`) from constants (`bc`, `vc`).
2. Prune: a factor of `bx` containing an opaque symbol (`exp`, `sin`, …) that does not occur in
   `vx` cannot be part of a product `ring1`-equal to `∏ vx` (for `ring` these symbols are atoms,
   and atoms do not cancel: `a * a⁻¹ = 1` is false at `a = 0`). Such factors always go to the
   remainder. Only the other factors, the candidates, are enumerated.
3. Enumerate the subsets `sel` of the candidates (at most `2^8`; more candidates are refused) and
   keep the first one with `∏ sel = ∏ vx` according to `ring1`: these factors are "the
   derivative".
4. Form `q = (∏ bc / ∏ vc) * ∏ (bx \ sel)`: the constant ratio between the integrand and `v`, times
   the remaining factors. For `x * (x ^ 2 + 1) ^ 3` with `v = 2 * x` this is `1 / 2 * (x²+1)³`.
5. Abstract `ψ x` in `q` (`kabstract` at reducible transparency, a syntactic match; for a
   complex integrand also the pushed-cast form of `↑(ψ x)`). If the result no longer mentions
   `x`, it is `g` (as a function of a real `u`, cast to `ℂ` when needed). `ψ x` need not occur:
   a constant integrand gives a constant `g`.

Nothing here is trusted: a wrong `g` only produces an unprovable `ceq`. -/
def findOuter? (x ψx body v : Expr) : TacticM (Option Expr) :=
  withBudget changeVar.searchHeartbeats do
    let ty ← inferType body
    let isC := ty.isConstOf ``Complex
    let dep (e : Expr) : Bool := e.containsFVar x.fvarId!
    let (bx, bc) := (← factors body).partition dep
    let (vx, vc) := (← factors v).partition dep
    let vxT ← castIfC isC (← mkProd (mkConst ``Real) vx)
    let vHeads : NameSet := vx.foldl (fun acc f => acc.append (opaqueHeads x.fvarId! f)) {}
    let (cand, fixed) := bx.partition fun f =>
      (opaqueHeads x.fvarId! f).toList.all vHeads.contains
    let n := cand.length
    if n > 8 then
      throwError "change_var: the integrand has {n} factors that could be part of ψ'; the search \
        for g tries at most 8 (2^8 subsets). Give g with `change_var … with g`."
    -- In a complex integrand `ψ x` appears cast, either as `↑(ψ x)` or with the cast pushed inside.
    let pats ← if isC then do
        let c ← mkAppM ``Complex.ofReal #[ψx]
        let r ← simpOnlyNames [``Complex.ofReal_pow, ``Complex.ofReal_mul, ``Complex.ofReal_add,
          ``Complex.ofReal_sub, ``Complex.ofReal_neg, ``Complex.ofReal_div, ``Complex.ofReal_inv] c
        pure #[r.expr, c]
      else pure #[ψx]
    for mask in List.range (2 ^ n) do
      let pick := (List.range n).zip cand
      let sel := (pick.filter fun p => (mask >>> p.1) % 2 == 1).map (·.2)
      let rest := (pick.filter fun p => (mask >>> p.1) % 2 == 0).map (·.2) ++ fixed
      unless ← ringEq (← mkProd ty sel) vxT do continue
      let k ← mkAppM ``HDiv.hDiv #[← mkProd ty bc, ← castIfC isC (← mkProd (mkConst ``Real) vc)]
      let q ← mkAppM ``HMul.hMul #[k, ← mkProd ty rest]
      for p in pats do
        let a ← withReducible (kabstract q p)
        if !a.containsFVar x.fvarId! then
          return some (← withLocalDeclD `u (mkConst ``Real) fun u => do
            mkLambdaFVars #[u] (a.instantiate1 (← castIfC isC u)))
    return none

/-- Recognise `ψ t = circleMap c R (α * t)` and return `(c, R, α)`.

Each lemma `L` in the list has the shape `∀ …, lhs = circleMap c R (α * t)` with the real
parameter `t` as its last argument. We instantiate the arguments with metavariables, assign the
last one to `t`, and unify `lhs` with `ψ t` at *reducible* transparency (see the module notes:
default transparency unfolds real arithmetic and times out). The state is restored between
attempts. -/
def matchCircle? (t body : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  for L in [``ChangeVar.circleMap_self, ``ChangeVar.I_cpow_ofReal,
      ``ChangeVar.exp_ofReal_mul_I_eq_circleMap, ``ChangeVar.circleMap_one_mul] do
    let s ← saveState
    let (mvs, _, ty) ← forallMetaTelescopeReducing (← inferType (mkConst L))
    if let some last := mvs.back? then
      if ← isDefEq last t then
        if let some (_, lhs, rhs) := ty.eq? then
          if ← withReducible (isDefEq lhs body) then
            let rhs ← instantiateMVars rhs
            if rhs.isAppOfArity ``circleMap 3 then
              let arg := rhs.getArg! 2
              if arg.isAppOfArity ``HMul.hMul 6 then
                return some (rhs.getArg! 0, rhs.getArg! 1, arg.getArg! 4)
    s.restore
  return none

/-- Arithmetic cleanup with a proof: `norm_num` evaluates numeral subterms (`2 - 1 ↦ 1`,
`2 / 2 ↦ 1`, `↑(2 : ℝ) ↦ (2 : ℂ)`) and a few `simp` lemmas remove units and zeros (`a * 1`,
`a + 0`, `a ^ 1`). Returns the original expression with a trivial result when nothing applies. -/
def tidy (e : Expr) : MetaM Simp.Result := do
  let ctx ← Simp.Context.ofNames [``add_zero, ``zero_add, ``mul_zero, ``zero_mul, ``mul_one,
    ``one_mul, ``div_one, ``pow_one, ``zero_sub, ``sub_zero, ``Nat.cast_ofNat, ``Nat.cast_one,
    ``Complex.ofReal_ofNat, ``Complex.ofReal_one] true
  try Mathlib.Meta.NormNum.deriveSimp ctx (useSimp := true) (e := e)
  catch _ => pure { expr := e }

/-- `tidy` under the binders of a function `fun u => …`, without proof. Used on the searched `g`
only: whatever form results is re-checked by `ceq`. -/
def tidyFun (g : Expr) : MetaM Expr :=
  lambdaTelescope g fun xs b => do mkLambdaFVars xs (← tidy b).expr

/-- Pin an oracle's proof `p0` to the type `HasDerivAt ψ v0 x` (its inferred type may use `f ^ n`
on functions, see the module notes), clean `v0` with `tidy` *with a proof*, and move the proof
along (`HasDerivAt.congr_deriv`): returns the clean `v` and a proof of `HasDerivAt ψ v x`. Shared by
`realMode` and `change_var_deriv`. -/
def pinAndTidy (ψ x v0 p0 : Expr) : MetaM (Expr × Expr) := do
  have ψ : Q(ℝ → ℝ) := ψ
  have x : Q(ℝ) := x
  have v0 : Q(ℝ) := v0
  have p0 : Q(HasDerivAt $ψ $v0 $x) := ← mkExpectedTypeHint p0 q(HasDerivAt $ψ $v0 $x)
  let vs ← tidy v0
  have v : Q(ℝ) := vs.expr
  have e : Q($v0 = $v) := ← vs.getProof
  return (v, q(HasDerivAt.congr_deriv $p0 $e))

/-- Run the rewrite `rw`, then the optional `closer?` on the side goals (the obligations), and
return the report line. `closer?` is the real or circle closers in `change_var!`, `change_var_disch`
in set mode, the user's `disch` in the rigid form, and `none` otherwise.

* The side goals are `extra` (goals created before the rewrite, e.g. `deriv`, attempted first since
  they fix metavariables that the others mention) followed by the goals that `rw` created: present
  after it and not before, except the new main goal (the first one). Identifying them by tag
  (`ceq`, `hv`, …) would also catch goals with the same tag left by an earlier call, and running
  the closer with `all_goals` on the whole goal list would silently close unrelated goals of the
  user (both found by an independent review).
* Each side goal is attempted alone through `runClosed` (own budget, no error recovery, no
  `sorry`, state restored on failure).
* `trailing` (the data goal `?ψ'`) is never attempted and is put last, if still unassigned.

The goal list is rebuilt as: main goal, open side goals, other goals of the user, trailing.
Also returns the tags of the side goals that were closed (for the suggestion of `change_var?`). -/
def rewriteAndClose (rw : TacticM Unit) (closer? : Option (TacticM Unit))
    (extra : List MVarId := []) (trailing : List MVarId := []) (betaMain : Bool := false) :
    TacticM (MessageData × List Name) := do
  let before ← getGoals
  rw
  let after := (← getGoals).filter (!trailing.contains ·)
  -- `extra` (e.g. `deriv`) first: it fixes metavariables that the other side goals mention.
  let sides := extra ++ ((after.drop 1).filter fun g => !before.contains g && !extra.contains g)
  let main := after.take 1
  let rest := (after.drop 1).filter fun g => !sides.contains g
  if let some closer := closer? then
    -- One side goal at a time, each with its own budget, through `runClosed`: a slow or failing
    -- attempt leaves its goal open, untouched, and does not prevent the others.
    for g in sides do
      discard <| runClosed g closer changeVar.sideGoalHeartbeats
  let left ← sides.filterM fun g => return !(← g.isAssigned)
  -- `trailing` (the data metavariable `?ψ'`) comes last, as `apply` and `refine` do with data
  -- goals: it disappears once `deriv` is proved, and stays assignable (e.g. by `sorry`) otherwise.
  let tail ← trailing.filterM fun g => return !(← g.isAssigned)
  -- The rewrite used `rewrite`, which never closes the main goal (so `after.take 1` is it); like
  -- `rw`, now try `rfl` on it (e.g. when the two sides became equal).
  let main ← main.filterM fun m => do
    let s ← saveState
    try
      let rest ← Tactic.run m (evalTactic (← `(tactic| with_reducible rfl)))
      if rest.isEmpty then return false
      s.restore; return true
    catch _ => s.restore; return true
  -- With `betaMain`, beta-reduce the main goal (the new bounds `ψ a`, `ψ b` are a lambda
  -- applied to a point). Only this goal, identified above: not "the first goal of the list",
  -- which is one of the user's goals when the main goal was closed by `rfl` and every side goal
  -- was closed.
  let main ← if !betaMain then pure main else main.mapM fun m => do
    let ty ← instantiateMVars (← m.getType)
    let ty' ← Core.betaReduce ty
    if ty' == ty then return m
    m.replaceTargetDefEq ty'
  setGoals (main ++ left ++ rest ++ tail)
  let mut closed : List Name := []
  let mut open_ : List Name := []
  for g in sides do
    let t := (← g.getTag).eraseMacroScopes
    if left.contains g then open_ := open_ ++ [t] else closed := closed ++ [t]
  let how := if closer?.isSome then "" else " (no attempt made)"
  return (m!"side goals: closed {closed}, left open {open_}{how}", closed)

/-- Elaborate the outer function given with `with g`, in the user's context (not under the
binders `x`, `hx`, `hpos`, `hne` introduced by the tactic, which would shadow the user's names and
leak free variables into the goal). Holes are refused, since nothing would solve them; an
elaboration error already reported aborts quietly. -/
def elabUserG (s : Term) (expected? : Option Expr) (what : String := "the outer function") :
    TacticM Expr := do
  let g ← instantiateMVars (← elabTerm s expected?)
  if g.hasSyntheticSorry then throwAbortTactic
  if g.hasExprMVar then
    throwError "change_var: {what}{indentExpr g}\nhas holes; give it completely"
  return g

/-- A fresh data metavariable `?ψ' : ℝ → ℝ` (tag `ψ'`) for the derivative of the rigid form, with
its report line. -/
def freshDerivMVar : TacticM (Expr × MessageData) := do
  let realTy := mkConst ``Real
  let v ← mkFreshExprMVar (← mkArrow realTy realTy) (userName := `ψ')
  v.mvarId!.setTag `ψ'
  return (v, m!"derivative: ψ' = ?ψ', fixed by the proof of the goal `deriv` \
    (e.g. `change_var_deriv`)")

/-- The statement of the obligation `deriv` for the derivative `v : ℝ → ℝ` (possibly a
metavariable): `∀ x ∈ S, HasDerivAt ψ (v x) x`, or `∀ x ∈ S, HasDerivWithinAt ψ (v x) S x`
(`within`, set mode). -/
def derivStatement (S ψfun v : Expr) (within : Bool) (xn : Name) : MetaM Expr := do
  have S : Q(Set ℝ) := S
  have ψ : Q(ℝ → ℝ) := ψfun
  -- The binders are made by `withLocalDeclD`, with the integral's own name `xn` (a quotation
  -- `q(∀ x ∈ …)` would fix the name `x`); only the body is a quotation.
  withLocalDeclD xn q(ℝ) fun x => do
    have x : Q(ℝ) := x
    withLocalDeclD `hx q($x ∈ $S) fun hx => do
      -- `ψ' x` beta-reduced, as the user would write it (`v` may be a lambda).
      have vx : Q(ℝ) := v.beta #[x]
      let c : Q(Prop) :=
        if within then q(HasDerivWithinAt $ψ $vx $S $x) else q(HasDerivAt $ψ $vx $x)
      mkForallFVars #[x, hx] c

/-- Elaborate the proof `h` given with `using h` against the statement of `deriv` with a fresh
`?ψ'`, and return the derivative it determines (as a function) and the proof.

As Mathlib's `apply_fun … using P` and `lift … using h`, a `using` clause that does not fit is an
error, never a reason to fall back to the automation: a type mismatch is reported as such, an
error inside a `by` block is reported by that block (and the call stops), and a proof that leaves
the derivative undetermined is refused. -/
def elabDerivProof (hStx : Term) (S ψfun : Expr) (within : Bool) (xn : Name) :
    TacticM (Expr × Expr) := do
  let realTy := mkConst ``Real
  let v ← mkFreshExprMVar (← mkArrow realTy realTy) (userName := `ψ')
  let ty ← derivStatement S ψfun v within xn
  let h ← instantiateMVars (← Tactic.elabTermEnsuringType hStx ty)
  if h.hasSyntheticSorry then throwAbortTactic
  let v ← instantiateMVars v
  let ty ← instantiateMVars ty
  if v.hasExprMVar || h.hasExprMVar then
    throwError "change_var: the `using` proof{indentExpr h}\ndoes not determine the derivative; \
      it should prove{indentExpr ty}"
  -- Pin the type to the stated `deriv`: a proof built from `HasDerivAt.pow` infers `ψ` as a power
  -- of functions (`(fun x => x) ^ 2`), and the rewrite would then look for that form.
  return (v, ← mkExpectedTypeHint h ty)

/-- The built-in attempts on the obligations of real mode (`hv`, `hg`, `ceq`), used by
`change_var!` and by `change_var_side` (see the table in the module docstring, *Dischargers*). It is
always run on one goal through `runClosed`, so an alternative either closes its goal or leaves
no trace, and an unclosed goal is left untouched for the user. -/
def closeRealSideGoals : TacticM Unit := do
  evalTactic (← `(tactic| all_goals try (first
    -- `ceq : EqOn F (fun x => v x • g (ψ x)) [[a, b]]`: pointwise ring identity. With a clean
    -- `v`, `simp only` often closes it by itself, hence `done` first.
    | (intro x _
       simp only [Function.comp_apply, smul_eq_mul, Complex.real_smul]
       first | done | ring1 | (push_cast; ring1) | (field_simp; ring1))
    -- `hv`, `hg` when everything is globally continuous.
    | fun_prop
    -- `hv : ContinuousOn v [[a, b]]` pointwise, with `0 < x` available (e.g. `v = x⁻¹`).
    -- The anonymous hypothesis is introduced by `refine` and proved first (`rotate_left`).
    | (intro x hx
       refine (fun _ : 0 < x => ?_) ?_
       rotate_left
       change_var_domain
       refine ContinuousAt.continuousWithinAt ?_
       fun_prop (disch := change_var_domain))
    -- `hv` pointwise with `x ≠ 0` (negative domains, e.g. `v = x⁻¹` on `[[-2, -1]]`).
    | (intro x hx
       refine (fun _ : x ≠ 0 => ?_) ?_
       rotate_left
       change_var_domain
       refine ContinuousAt.continuousWithinAt ?_
       fun_prop (disch := change_var_domain))
    -- `hv` pointwise without a sign of `x`.
    | (intro x _
       refine ContinuousAt.continuousWithinAt ?_
       fun_prop (disch := change_var_domain))
    -- `hg : ContinuousOn g (ψ '' [[a, b]])`: a point of the image is `ψ x`; continuity of `g` at
    -- `ψ x`, with `0 < x` when available (e.g. `g = u⁻¹`, `ψ x = log x`, needs `x ≠ 0` first).
    | (rintro _ ⟨x, hx, h⟩
       subst h
       refine (fun _ : 0 < x => ?_) ?_
       rotate_left
       change_var_domain
       refine ContinuousAt.continuousWithinAt ?_
       beta_reduce
       fun_prop (disch := (beta_reduce; change_var_domain)))
    -- `hg` with `x ≠ 0` (negative domains, e.g. `g = u⁻¹` at `u = x ^ 2` on `[[-2, -1]]`).
    | (rintro _ ⟨x, hx, h⟩
       subst h
       refine (fun _ : x ≠ 0 => ?_) ?_
       rotate_left
       change_var_domain
       refine ContinuousAt.continuousWithinAt ?_
       beta_reduce
       fun_prop (disch := (beta_reduce; change_var_domain)))
    -- `hg` pointwise without a sign of `x` (e.g. `g = (1 + u)⁻¹` at `u = exp x`: `positivity`).
    | (rintro _ ⟨x, _, h⟩
       subst h
       refine ContinuousAt.continuousWithinAt ?_
       beta_reduce
       fun_prop (disch := (beta_reduce; change_var_domain))))))

/-- How a call treats its obligations: `rigid` (`change_var … with g`) leaves them to the user,
except for those the optional `disch` tactic closes; `auto` (`change_var!`, `change_var?`)
computes `ψ'`, searches `g` and runs the built-in closers (those of its mode in real and circle
mode, `change_var_disch` in set mode). -/
inductive Mode where
  | rigid (disch? : Option (TacticM Unit))
  | auto

/-- What a mode returns: the outer function used, the report lines, the tags of the obligations
that were closed, and, in real and set mode, what the `deriv` script of `change_var?` needs (the
domain, `ψ`, whether the goal is `HasDerivWithinAt`, the binder name). -/
structure Outcome where
  g : Expr
  lines : Array MessageData
  closed : List Name
  deriv? : Option (Expr × Expr × Bool × Name)

/-- Real mode of `change_var` (see the module docstring for the full pipeline).

`F` is the integrand as a lambda, `ψfun` the new variable as a lambda, `a b` the bounds, `xn` the
binder name, `gStx?` the outer function given with `with` (required in rigid mode). Returns the
outer function actually used and the report lines.

* **rigid:** no derivative is computed. `ψ'` is a fresh metavariable `?ψ'` and the hypothesis of the
  substitution lemma becomes the goal `deriv : ∀ x ∈ [[a, b]], HasDerivAt ψ (?ψ' x) x`. Proving it
  (by hand, or with `change_var_deriv`) *fixes* `?ψ'`, which the goals `hv` and `ceq` mention: prove
  `deriv` first.
* **auto:** `ψ'` is computed (`deriveAt`, `tidy`), `g` is searched when not given, and the side
  goals are attempted with `closeRealSideGoals`. -/
def realMode (F ψfun a b : Expr) (xn : Name) (gStx? : Option Term) (mode : Mode)
    (using? : Option Term := none) : TacticM Outcome := do
  let gUser? ← gStx?.mapM (elabUserG · none)
  let dom : Q(Set ℝ) := Id.run do
    have a : Q(ℝ) := a; have b : Q(ℝ) := b
    q(Set.uIcc $a $b)
  -- The derivative and its proof, when given with `using h` (all forms).
  let given? ← using?.mapM (elabDerivProof · dom ψfun false xn)
  -- `(v, H, g, report on ψ, report on ψ', extra goals, trailing data goals)`
  let (vfun, H, gfun, ψf, vLine, extra, trailing) ← match mode with
    | .rigid _ => do
      let some g := gUser? | throwError "change_var: the rigid form needs `with g`; use \
        `change_var!` to search for g"
      let ψf ← withRealVar xn fun x => ppExpr (ψfun.beta #[x])
      match given? with
      | some (v, h) =>
        -- `deriv` is proved by `h`: no goal `deriv`, no data goal.
        pure (v, h, g, ψf, m!"derivative: ψ' = {v}  (given with `using`)", [], [])
      | none =>
        let (v, vLine) ← freshDerivMVar
        let hderiv ← mkFreshExprSyntheticOpaqueMVar (← derivStatement dom ψfun v false xn)
          (tag := `deriv)
        pure (v, hderiv, g, ψf, vLine, [hderiv.mvarId!], [v.mvarId!])
    | .auto => do
      let (vfun, H, gfun, ψf, vf, src, gsrc) ← withRealVarIn xn dom fun x bs => do
        let ψx := ψfun.beta #[x]
        -- `v` and, unless given with `using`, its proof `p` at `x`.
        let (v, p?, src) ← match given? with
          | some (vfun, _) => pure (vfun.beta #[x], none, "given with `using`")
          | none => do
            let (v0, p0, src) ← deriveAt ψfun x
            -- An oracle's derivative may be unnormalised (`↑2 * x ^ (2 - 1) * 1 + 0`): clean it
            -- with a proof (`pinAndTidy`), so that the search, the report and the side goals
            -- `ceq`, `hv` all see the clean `v`.
            let (v, p) ← pinAndTidy ψfun x v0 p0
            pure (v, some p, src)
        let (gfun, gsrc) ← match gUser? with
          | some g => pure (g, "given with `with`")
          | none => do
            let some g ← findOuter? x ψx (F.beta #[x]) v
              | let hint := if p?.isNone then m!"" else fallbackHint src
                throwError "change_var: could not write the integrand as{indentExpr v}\n\
                  • g ({ψx}); give it with `change_var … with g`{hint}"
            pure (← tidyFun g, "found by the factor search")
        -- `H : ∀ x (hx : x ∈ [[a, b]]), HasDerivAt ψ (v x) x`, with the `let`s of
        -- `withRealVarIn` inlined. `ψ x` and `ψ' x` are pretty-printed here, while `x` is in
        -- scope.
        let H ← match given?, p? with
          | some (_, h), _ => pure h
          | none, some p => mkLambdaFVars bs p
          | none, none => throwError "change_var: no derivative proof (internal)"
        return (← mkLambdaFVars #[x] v, H, gfun, ← ppExpr ψx,
          ← ppExpr (← instantiateMVars v), src, gsrc)
      pure (vfun, H, gfun, ψf,
        m!"derivative: ψ' = {vf}  ({srcLine src})\nouter function: g = {gfun}  ({gsrc})", [], [])
  let ψS ← Term.exprToSyntax ψfun
  let vS ← Term.exprToSyntax vfun
  let gS ← Term.exprToSyntax gfun
  let HS ← Term.exprToSyntax H
  let closer? := match mode with
    | .rigid disch? => disch?
    | .auto => some closeRealSideGoals
  -- One rewrite, two theorems. New goals: main, then `deriv` (rigid mode), `hv`, `hg`, `ceq`.
  -- `?ψ'` is a trailing data goal, fixed by the proof of `deriv`.
  let (sideLine, closed) ←
      rewriteAndClose (closer? := closer?) (extra := extra) (trailing := trailing)
        (betaMain := true) do
    evalTactic (← `(tactic|
      rewrite [intervalIntegral.integral_congr (g := fun x => ($vS x) • ($gS ∘ $ψS) x) ?ceq,
        intervalIntegral.integral_deriv_smul_comp' (fun x hx => $HS x hx) ?hv ?hg]))
  let lines := #[
    m!"change_var, real mode: u = {ψf}",
    vLine,
    m!"rewrite: `intervalIntegral.integral_congr` (ceq: integrand = ψ' • g ∘ ψ on [[a, b]])",
    m!"substitution: `intervalIntegral.integral_deriv_smul_comp'` (deriv: ψ' derivative of ψ on \
      [[a, b]]; hv: ψ' continuous on [[a, b]]; hg: g continuous on ψ '' [[a, b]])",
    sideLine]
  return { g := gfun, lines, closed, deriv? := some (dom, ψfun, false, xn) }

/-- Outer function for circle mode: `g z = F t / (α (z - c) I)` where `z = ψ t`.

`F t` is first rewritten so that it is a function of `ψ t` alone: casts are pushed
(`↑(cos t) = cos ↑t`, …), `Complex.cos`/`Complex.sin` are *unfolded* to their definitions
`(exp (z I) ± exp (-z I)) / 2…` with `deltaExpand` (they are definitions, so `simpOnlyNames`,
which only takes theorems, cannot do it), and `exp (-x)` becomes `(exp x)⁻¹`. Then `ψ t` is
abstracted (it need not occur: a constant integrand is a constant `g`). If `t` still occurs, the
integrand is not a function of `ψ t` and the user must give `g`. The division by `α (z - c) I`
is `dz/dt`: `d/dt circleMap c R (α t) = α (z - c) I`.

`ψ t` goes through the same normalisation as the integrand (otherwise `neg_mul` turns
`-1 * t` into `-(1 * t)` in one and not in the other), and the abstraction runs at reducible
transparency: at default transparency `kabstract` would try to unify the two forms by unfolding
real arithmetic and time out. -/
def autoCircleG (F ψfun c α : Expr) (tn : Name) : TacticM Expr :=
  withRealVar tn fun t => do
    let normalise (e : Expr) : TacticM Expr := do
      let r ← simpOnlyNames [``Complex.ofReal_div, ``Complex.ofReal_add, ``Complex.ofReal_sub,
        ``Complex.ofReal_mul, ``Complex.ofReal_neg, ``Complex.ofReal_inv, ``Complex.ofReal_pow,
        ``Complex.ofReal_one, ``Complex.ofReal_ofNat, ``Complex.ofReal_cos, ``Complex.ofReal_sin]
        e
      let e ← deltaExpand r.expr fun n => n == ``Complex.cos || n == ``Complex.sin
      return (← simpOnlyNames [``neg_mul, ``Complex.exp_neg] e).expr
    let Ft ← normalise (F.beta #[t])
    let ψt ← normalise (ψfun.beta #[t])
    let a ← withReducible (kabstract Ft ψt)
    if a.containsFVar t.fvarId! then
      throwError "change_var: the integrand{indentExpr Ft}\nis not a function of {ψt} \
        alone; give `g` with `change_var … with g`"
    have c : Q(ℂ) := c
    have α : Q(ℝ) := α
    withLocalDeclD `z q(ℂ) fun z => do
      have z : Q(ℂ) := z
      -- `F / (dz/dt)`, with `dz/dt = α (z - c) I`.
      have Fz : Q(ℂ) := a.instantiate1 z
      mkLambdaFVars #[z] q($Fz / ((($α : ℝ) : ℂ) * (($z - $c) * Complex.I)))

/-- The built-in attempts on the obligations of circle mode (`hα`, `hT`, `ceq`), used by
`change_var!` and by `change_var_side`; same contract as `closeRealSideGoals`. -/
def closeCircleSideGoals : TacticM Unit := do
  evalTactic (← `(tactic| all_goals try (first
    -- `hα` (`π / 2 ≠ 0`, `1 ≠ 0`, …)
    | positivity
    -- `hT` (`1 * (2 * π) = 2 * π`, `π / 2 * 4 = 2 * π`, …)
    | ring1
    | (field_simp; ring1)
    -- `ceq` for algebraic integrands (`I ^ t` parametrisation).
    | (intro t _
       simp only [deriv_circleMap, circleMap, ChangeVar.I_cpow_ofReal, zero_add,
         Complex.ofReal_one, one_mul]
       field_simp
       ring1)
    -- `ceq` for trigonometric integrands: unfold `cos`, `sin` into exponentials, clear
    -- denominators, and reduce powers of `I`, which `ring` sees as an opaque atom.
    | (intro t _
       simp only [deriv_circleMap, circleMap, zero_add, Complex.ofReal_one, one_mul,
         Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub,
         Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_cos,
         Complex.ofReal_sin, Complex.cos, Complex.sin, neg_mul, Complex.exp_neg]
       field_simp
       first | ring1 |
         (ring_nf; simp only [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]; ring1)))))

/-- The checks of circle mode that need no rewriting: lower bound `0` (compared at reducible
transparency, so `1 - 1` is refused at once rather than unfolded) and the shape of `ψ`. Run
*before* a real integral is cast to `ℂ`, so that a wrong call fails without touching the goal.
Returns `(c, R, α)`. -/
def circleShape (I ψfun : Expr) (tn : Name) : TacticM (Expr × Expr × Expr) := do
  -- The reparametrisation lemma integrates over `[0, T]` with `α T = 2π`.
  unless ← withReducible (isDefEq (I.getArg! 4) q((0 : ℝ))) do
    throwError "change_var: circle mode needs the lower bound 0 (compared up to reducible \
      unfolding), not{indentExpr (I.getArg! 4)}"
  withRealVar tn fun t => do
    let some r ← matchCircle? t (ψfun.beta #[t])
      | throwError "change_var: {ψfun} is not one of I ^ (t : ℂ), exp (t * I), \
          circleMap c R (α * t)"
    return r

/-- Circle mode of `change_var` (see the module docstring). `I` is the interval integral
`∫ t in 0..T, F t` (complex-valued), `ψfun` the parametrisation, `mode` as in `realMode` (circle
mode has no derivative goal: `deriv (circleMap c R)` is rewritten by `deriv_circleMap`).
Returns the outer function used and the report lines. The searched `g` is *not* tidied: the
`eq` goal of a following `circle_rational` is stated in terms of it, and keeping its raw form
keeps that goal predictable. -/
def complexMode (I ψfun : Expr) (tn : Name) (shape : Expr × Expr × Expr) (gStx? : Option Term)
    (mode : Mode) : TacticM Outcome := do
  let F := I.getArg! 3
  let (c, R, α) := shape
  let (gfun, gsrc) ← match gStx? with
    | some s => pure (← elabUserG s (← mkArrow (mkConst ``Complex) (mkConst ``Complex)),
        "given with `with`")
    | none => pure (← autoCircleG F ψfun c α tn,
        "integrand in terms of z = ψ t, divided by dz/dt = α (z - c) I")
  let gS ← Term.exprToSyntax gfun
  let cS ← Term.exprToSyntax c
  let RS ← Term.exprToSyntax R
  let αS ← Term.exprToSyntax α
  let TS ← Term.exprToSyntax (I.getArg! 5)
  -- New goals, in order: main (now a circle integral), `hα : α ≠ 0`, `hT : α * T = 2 * π`,
  -- `ceq`.
  let closer? := match mode with
    | .rigid disch? => disch?
    | .auto => some closeCircleSideGoals
  let (sideLine, closed) ← rewriteAndClose (closer? := closer?) do
    evalTactic (← `(tactic|
      rewrite [intervalIntegral.integral_congr (g := fun t => (($αS : ℝ) : ℂ) *
            (deriv (circleMap $cS $RS) ($αS * t) * $gS (circleMap $cS $RS ($αS * t)))) ?ceq,
        ChangeVar.intervalIntegral_circleMap_reparam' $gS $cS $RS $αS $TS ?hα ?hT]))
  let lines := #[
    m!"change_var, circle mode: ψ t = circleMap {c} {R} ({α} * t)",
    m!"outer function: g = {gfun}  ({gsrc})",
    m!"rewrite: `intervalIntegral.integral_congr` (ceq: integrand = α γ'(α t) g (γ (α t)))",
    m!"substitution: `ChangeVar.intervalIntegral_circleMap_reparam'` (hα: α ≠ 0; \
      hT: α * T = 2π)",
    sideLine]
  return { g := gfun, lines, closed, deriv? := none }

/-- `change_var_abs` removes the absolute values `|e|` of the goal (the `|ψ'|` of set mode) by
proving the sign of `e`: `0 ≤ e` by `positivity` or `change_var_domain` (which uses `x ∈ s` from the
context), then `abs_of_nonneg`; otherwise `e ≤ 0`, as `0 ≤ -e` after pushing the negation inside
(`neg_div`, `neg_neg`, …) and `positivity`, then `abs_of_nonpos`. Each sign proof runs through
`runClosed` (budget `changeVar.ringHeartbeats`). Only `|e|` without metavariables are treated, so
in set mode `deriv` must be proved first (it assigns `?ψ'`). Fails if some `|e|` has no provable
sign. -/
elab "change_var_abs" : tactic => withMainContext do
  let rec findAbs? (e : Expr) : Option Expr :=
    e.find? fun t => t.isAppOfArity ``abs 4 && !(t.getArg! 3).hasLooseBVars &&
      !(t.getArg! 3).hasExprMVar
  for _ in [0:8] do
    let target ← instantiateMVars (← getMainTarget)
    let some a := findAbs? target | return
    let e := a.getArg! 3
    let zero ← mkNumeral (← inferType e) 0
    let tryProve (ty : Expr) (tac : TacticM Unit) : TacticM (Option Expr) := do
      let g ← mkFreshExprMVar ty
      if ← runClosed g.mvarId! tac changeVar.ringHeartbeats then return some (← instantiateMVars g)
      return none
    if let some h ← tryProve (← mkAppM ``LE.le #[zero, e])
        (evalTactic (← `(tactic| first | positivity | change_var_domain))) then
      let hS ← Term.exprToSyntax h
      evalTactic (← `(tactic| rw [abs_of_nonneg $hS]))
    else if let some h ← tryProve (← mkAppM ``LE.le #[e, zero]) (do
        evalTactic (← `(tactic| apply neg_nonneg.mp))
        evalTactic (← `(tactic| try simp only [neg_div, neg_neg, neg_mul, mul_neg, neg_sub]))
        evalTactic (← `(tactic| positivity))) then
      let hS ← Term.exprToSyntax h
      evalTactic (← `(tactic| rw [abs_of_nonpos $hS]))
    else
      throwError "change_var_abs: no sign found for{indentExpr e}\n(neither `0 ≤ e` by \
        `positivity` or `change_var_domain`, nor `e ≤ 0` by `positivity` on `-e`)"

/-- The built-in attempts on the obligations of set mode (`hs`, `hinj`, `ceq`, `himg`), used by
`change_var_side`, hence by `change_var!` on set integrals (through `change_var_disch`); same
contract as `closeRealSideGoals`. The goal `himg` (`ψ '' s = T`) only gets a cheap `simp` attempt
(it closes e.g. `(1 - ·) '' Ioc 0 1 = Ico 0 1`, not `(2 * ·) '' Ioc 0 1 = Ioc 0 2` nor `(1 / ·) ''
Ioc 0 1 = Ici 1`); a general method needs an inverse of `ψ`. -/
def closeSetSideGoals : TacticM Unit := do
  evalTactic (← `(tactic| all_goals try (first
    -- `hs : MeasurableSet s` for the intervals
    | (first
        | exact measurableSet_Icc
        | exact measurableSet_Ico
        | exact measurableSet_Ioc
        | exact measurableSet_Ioo
        | exact measurableSet_Ici
        | exact measurableSet_Iic
        | exact measurableSet_Ioi
        | exact measurableSet_Iio
        | exact measurableSet_uIcc
        | exact measurableSet_uIoc)
    -- `hinj : Set.InjOn ψ s`, for injective-by-algebra `ψ` (`2 * x`, `1 / x`, `x + c`, …)
    | (intro a _ b _ h
       first | (simpa using h) | (simp only at h; linarith) | (field_simp at h; linarith))
    -- `ceq : EqOn F (fun x => |ψ' x| • g (ψ x)) s`: remove `|ψ'|`, then as in real mode.
    | (intro x _
       beta_reduce
       change_var_abs
       simp only [Function.comp_apply, smul_eq_mul, Complex.real_smul, neg_mul, Complex.ofReal_neg]
       first
         | done
         | ring1
         | (push_cast; ring1)
         | (field_simp; ring1)
         | (push_cast; field_simp; done)
         | (push_cast; field_simp; ring1))
    -- `himg : ψ '' s = T`: a cheap attempt only (see the docstring).
    | (simp; done)
    | (simp; norm_num; done))))

/-- Read a goal `∀ x ∈ S, HasDerivAt ψ (ψ' x) x` or `∀ x ∈ S, HasDerivWithinAt ψ (ψ' x) S x`:
the binder name, `S`, `ψ`, whether it is the `HasDerivWithinAt` form, and the stated `ψ'` as a
function unless it is still a metavariable. `tac` names the tactic in the error. -/
def derivGoal (tac : String) (ty : Expr) : TacticM (Name × Expr × Expr × Bool × Option Expr) := do
  let shapeErr : TacticM Unit := throwError "{tac}: expected a goal \
    `∀ x ∈ S, HasDerivAt ψ (ψ' x) x`, got{indentExpr ty}"
  let .forallE xn xTy body _ := ty | shapeErr; throwError "unreachable"
  unless xTy.isConstOf ``Real do shapeErr
  -- Read `S` and `ψ` under a temporary `x`; neither may depend on it.
  withLocalDeclD xn xTy fun x0 => do
    let .forallE _ memTy concl _ := body.instantiate1 x0 | shapeErr; throwError "unreachable"
    unless memTy.isAppOfArity ``Membership.mem 5 && !concl.hasLooseBVars &&
        (concl.isAppOfArity ``HasDerivAt 10 || concl.isAppOfArity ``HasDerivWithinAt 11) do
      shapeErr
    let S := memTy.getArg! 3
    let f := concl.getArg! 7
    if S.containsFVar x0.fvarId! || f.containsFVar x0.fvarId! then shapeErr
    -- The stated derivative `ψ' x`, as a function, unless it is still a metavariable.
    let v := concl.getArg! 8
    let given? ← if v.getAppFn.isMVar then pure none else some <$> mkLambdaFVars #[x0] v.headBeta
    return (xn, S, f, concl.isAppOfArity ``HasDerivWithinAt 11, given?)

/-- `change_var_deriv` proves a goal `∀ x ∈ S, HasDerivAt ψ (ψ' x) x` (the goal `deriv` of the rigid
`change_var`, real mode) or `∀ x ∈ S, HasDerivWithinAt ψ (ψ' x) S x` (set mode), where `ψ'` may be a
metavariable, which it then fixes. It computes the derivative exactly as `change_var!` does:
`withRealVarIn` (a fresh `x` with `x ∈ S`, and `0 < x` / `x < 0` when `change_var_domain` proves
them), the derivative oracles, the `fun_prop` fallback, and `tidy` (normalisation with a proof).
It fails if the computed derivative does not match a `ψ'` that is already given. -/
elab "change_var_deriv" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let (xn, S, f, within, given?) ← derivGoal "change_var_deriv" ty
  let (H, vfun) ← withRealVarIn xn S fun x bs => do
    let (v0, p0, _) ← deriveAt f x
    let (v, p) ← pinAndTidy f x v0 p0
    -- Within a set (set mode): `HasDerivAt.hasDerivWithinAt`, the set given explicitly.
    let p : Expr := if within then Id.run do
        have f : Q(ℝ → ℝ) := f; have x : Q(ℝ) := x; have v : Q(ℝ) := v; have S : Q(Set ℝ) := S
        have p : Q(HasDerivAt $f $v $x) := p
        q(HasDerivAt.hasDerivWithinAt (s := $S) $p)
      else p
    return (← mkLambdaFVars bs p, ← mkLambdaFVars #[x] v)
  unless ← isDefEq (← inferType H) ty do
    let stated := match given? with
      | some g => m!"the derivative stated in the goal{indentExpr g}"
      | none => m!"the goal"
    throwError "change_var_deriv: the computed derivative{indentExpr vfun}\ndoes not match \
      {stated}\n(compared up to definitional unfolding, not up to `ring`: if they are equal, \
      `change_var_deriv?` bridges them; otherwise the stated derivative is wrong)"
  goal.assign H
  replaceMainGoal []

/-! ### An explicit, oracle-independent proof of `deriv`

An oracle's proof of `HasDerivAt ψ v x` is typically a chain of Mathlib lemmas (`HasDerivAt.add`,
`HasDerivAt.comp`, `Real.hasDerivAt_exp`, `HasDerivAt.log`, …), with side premises (`x ≠ 0`,
`0 < x ^ 2 + 1`) proved by tactics or by the `let`s of `withRealVarIn`. `derivScript` prints that
proof as a script that replays without the oracle:

```
intro x hx
have hne : x ≠ 0 := by change_var_domain          -- only the domain facts the proof uses
have hd := HasDerivAt.log (hasDerivAt_id' x) hne  -- the chain of Mathlib lemmas
change HasDerivAt (fun x => Real.log x) (1 / x) x -- fixes ?ψ' (only when it is unassigned)
exact hd
```

When the derivative is already stated in the goal (`change_var_deriv?` on `HasDerivAt ψ (x + x) x`),
there is no `change`, and the bridge below goes to the stated form. (`change` rather than `show`:
it does alter the goal, assigning `?ψ'`, and Mathlib's `linter.style.show` asks for `change` there.)
The chain is stated with `have`, without expected type: `HasDerivAt.mul` is stated for the pointwise
product `c * d` of functions, and elaborating it against `fun x => 2 * x` unfolds the numeral `2`
into its Cauchy structure (the same pitfall as in *Expected type of oracle proofs*). When a premise
needs the expected type to be elaborated (`by positivity` under `HasDerivAt.sqrt`,
`DifferentiableAt.hasDerivAt (by fun_prop …)`), the chain is written inline after `change` instead:
both variants are built and the first that replays is suggested. Each lemma is printed with its
explicit arguments only (Lean infers the others); each premise is printed as the local fact it used,
or as `(by tac)` with the first of `positivity`, `norm_num`, `linarith`, `nlinarith`,
`change_var_domain`, `fun_prop (disch := change_var_domain)` that proves it (the `fun_prop` fallback
of `deriveAt` thus appears as `DifferentiableAt.hasDerivAt (by fun_prop (disch :=
change_var_domain))`). When the oracle's value is not already clean, `HasDerivAt.congr_deriv hd (by
norm_num)` (or `ring`, `simp`, `field_simp`) bridges it to the normalised one stated by `change`; a
numeral argument whose type the lemma leaves free is ascribed (`hasDerivAt_const x (2 : ℝ)`),
otherwise it would default to `ℕ`. The script is then replayed on a fresh `deriv` goal
(`checkDerivScript`, with the oracles off) before it is suggested; if no variant replays,
`change_var_deriv?` falls back to `change_var_deriv` (if that closes the goal, a warning gives the
reason why no script was built; if it fails, only its error is shown) and `change_var?` to the
compact `(disch := change_var_disch)` form, with an information message giving the reason. -/

/-- Delaborate `e`, beta-reduced, with binder types (so that it re-elaborates on its own). -/
def delabT (e : Expr) : MetaM Term := do
  let e ← Core.betaReduce (← instantiateMVars e)
  withOptions (fun o => o.setBool `pp.funBinderTypes true) (PrettyPrinter.delab e)

/-- Parenthesise a term unless it is an identifier or a numeral. -/
def parenT (t : Term) : MetaM Term :=
  if t.raw.isIdent || t.raw.isOfKind numLitKind then pure t else `(($t))

/-- The first tactic of `tacs` that closes a fresh goal of type `ty` (through `runClosed`), or
`none`. The state is restored in all cases. -/
def firstClosing (ty : Expr) (tacs : List (TSyntax `tactic)) :
    TacticM (Option (TSyntax `tactic)) := do
  for tac in tacs do
    let s ← saveState
    let g ← mkFreshExprMVar ty
    let ok ← runClosed g.mvarId! (evalTactic tac) changeVar.sideGoalHeartbeats
    s.restore
    if ok then return some tac
  return none

/-- The tactics tried on a premise of a derivative rule, in this order. The second component
says whether the tactic may use the domain facts `hpos`/`hneg`/`hne` (then the script declares
them). -/
def premiseTactics : TacticM (List (TSyntax `tactic × Bool)) := do
  return [(← `(tactic| positivity), false), (← `(tactic| norm_num), false),
    (← `(tactic| linarith), true), (← `(tactic| nlinarith), true),
    (← `(tactic| change_var_domain), false),
    (← `(tactic| fun_prop (disch := change_var_domain)), false)]

/-- Which domain facts of `withRealVarIn` a printed proof needs: the local facts it names, or
all of them (`all`) when a premise was proved by `linarith`/`nlinarith`, which may use any. -/
structure CtxUse where
  names : NameSet := {}
  all : Bool := false

/-- Print a proof of `HasDerivAt …` built from lemma applications as a term: the lemma, its
explicit arguments (derivative proofs recursively, premises as a local fact or `(by tac)`, other
arguments delaborated). Records in `use` the domain facts the term needs. Fails on any other
shape. All names are built with `mkIdent`, so the printed term has no hygiene marks. -/
partial def renderProof (use : IO.Ref CtxUse) (e : Expr) : TacticM Term := do
  let e := e.consumeMData
  if e.isFVar then
    let n ← e.fvarId!.getUserName
    use.modify fun u => { u with names := u.names.insert n }
    return mkIdent n
  let fn := e.getAppFn
  let .const c _ := fn | throwError "renderProof: not a lemma application{indentExpr e}"
  let args := e.getAppArgs
  let info ← getFunInfoNArgs fn args.size
  let mut out : Array Term := #[]
  for h : i in [0:args.size] do
    let explicit := if h' : i < info.paramInfo.size then info.paramInfo[i].binderInfo.isExplicit
      else true
    unless explicit do continue
    let a := args[i]
    let ty ← instantiateMVars (← inferType a)
    if ← isProp ty then
      if ty.isAppOf ``HasDerivAt || ty.isAppOf ``HasDerivWithinAt || a.consumeMData.isFVar then
        out := out.push (← parenT (← renderProof use a))
      else
        let cands ← premiseTactics
        let some tac ← firstClosing ty (cands.map (·.1))
          | throwError "renderProof: no tactic proves the premise{indentExpr ty}"
        if (cands.find? (·.1 == tac)).any (·.2) then use.modify ({ · with all := true })
        out := out.push (← `((by $tac:tactic)))
    else
      let t ← delabT a
      -- A bare numeral would default to `ℕ` where the lemma leaves its type free
      -- (`hasDerivAt_const x 2`): ascribe its type.
      if (t.raw.isOfKind numLitKind || t.raw.isOfKind ``Lean.Parser.Term.scientific) &&
          !ty.isConstOf ``Nat then
        out := out.push (← `(($t : $(← delabT ty))))
      else
        out := out.push (← parenT t)
  return Syntax.mkApp (mkIdent c) out

/-- Replay `script` on a fresh goal `∀ x ∈ S, HasDerivAt ψ (v x) x` (or `HasDerivWithinAt`), as
the rigid form states it (`v` given, or a fresh metavariable `?v`), and report whether it closes
it. The state is restored. -/
def checkDerivScript (S f : Expr) (within : Bool) (xn : Name)
    (script : TSyntax ``Lean.Parser.Tactic.tacticSeq) (v? : Option Expr := none) :
    TacticM Bool := do
  let s ← saveState
  let realTy := mkConst ``Real
  let v ← match v? with
    | some v => pure v
    | none => mkFreshExprMVar (← mkArrow realTy realTy)
  let ty ← derivStatement S f v within xn
  let g ← mkFreshExprSyntheticOpaqueMVar ty
  -- Replayed with every derivative oracle switched off: a suggested script must not need one.
  let ok ← withOptions (fun o => o.setBool `changeVar.derivOracles false) <|
    runClosed g.mvarId! (evalTactic script) changeVar.fallbackHeartbeats
  s.restore
  return ok

/-- The modules that this file (`SpherePacking.Tactic.ChangeVar.Core`) depends on, itself included,
computed from the import graph of the environment: what a suggested script may use. A derivative
oracle may build its proof from lemmas of its own library; a script containing them would only
replay where that library is imported, so `derivScript` refuses it. -/
def coreModules (env : Environment) : NameSet := Id.run do
  let names := env.header.moduleNames
  let some start := env.getModuleIdxFor? ``deriveAt | return {}
  let idx : Std.HashMap Name Nat := names.foldl (init := {}) fun m n => m.insert n m.size
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[names[start.toNat]!]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some i := idx[n]? then
      for imp in env.header.moduleData[i]!.imports do
        todo := todo.push imp.module
  return seen

/-- The constants of `e` that come from modules outside `coreModules` (declarations of the current
file are allowed). -/
def foreignConstants (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let core := coreModules env
  return e.getUsedConstants.filter fun c =>
    match env.getModuleIdxFor? c with
    | some i => !core.contains env.header.moduleNames[i.toNat]!
    | none => false

/-- An explicit script proving `∀ x ∈ S, HasDerivAt ψ (ψ' x) x` (or `HasDerivWithinAt ψ … S x`)
without any oracle, see the section docstring; checked by replay. Returns the script and the
derivative it proves, as a function: `target?` if given, the normalised one (`tidy`) otherwise.

* `explicitV = false` (goal `deriv` with the metavariable `?ψ'`): the script states the
  derivative with `change`, which assigns `?ψ'`.
* `explicitV = true` (the derivative is stated in the goal, e.g. `change_var_deriv?` on
  `HasDerivAt ψ (x + x) x`): no `change`; the bridge goes from the oracle's value to the stated one.

The reason, when no script can be built or none replays. -/
def derivScript (S f : Expr) (within : Bool) (xn : Name) (target? : Option Expr := none)
    (explicitV : Bool := false) :
    TacticM (Except MessageData (TSyntax ``Lean.Parser.Tactic.tacticSeq × Expr)) := do
  let s ← saveState
  let built? : Except MessageData (List (TSyntax ``Lean.Parser.Tactic.tacticSeq) × Expr) ← try
      withRealVarIn xn S fun x bs => do
        let (v0, p0, _) ← deriveAt f x
        let v0 ← instantiateMVars v0
        let v ← match target? with
          | some t => pure (t.beta #[x])
          | none => instantiateMVars (← tidy v0).expr
        -- The derivative as a function of `x` alone (not of the domain facts `hpos`, `hne`).
        if bs[1:].toArray.any (fun b => v.containsFVar b.fvarId!) then
          throwError "derivScript: the derivative mentions the domain facts"
        let vfun ← mkLambdaFVars #[x] v
        let use ← IO.mkRef ({} : CtxUse)
        -- Oracle-independence: the proof may only use what this file itself depends on.
        let foreign ← foreignConstants (← instantiateMVars p0)
        unless foreign.isEmpty do
          throwError "derivScript: the proof uses constants outside the core's dependencies: \
            {foreign}"
        let chain ← renderProof use (← instantiateMVars p0)
        let hd := mkIdent `hd
        let bridge? ← if v0 == v then pure none else do
          let eqTacs := [← `(tactic| norm_num), ← `(tactic| ring), ← `(tactic| simp),
            ← `(tactic| field_simp)]
          let some tac ← firstClosing (← mkEq v0 v) eqTacs
            | throwError "derivScript: cannot bridge the two forms of the derivative"
          pure (some tac)
        -- The final term, from a proof `p` of `HasDerivAt ψ v0 x`.
        let finish (p : Term) : TacticM Term := do
          let mut t := p
          if let some tac := bridge? then
            t ← `($(mkIdent ``HasDerivAt.congr_deriv) $(← parenT t) (by $tac:tactic))
          if within then t ← `($(mkIdent ``HasDerivAt.hasDerivWithinAt) $(← parenT t))
          return t
        let concl : Q(Prop) := Id.run do
          have f : Q(ℝ → ℝ) := f; have S : Q(Set ℝ) := S
          have x : Q(ℝ) := x; have v : Q(ℝ) := v
          if within then q(HasDerivWithinAt $f $v $S $x) else q(HasDerivAt $f $v $x)
        let showT ← delabT concl
        let u ← use.get
        let lets ← bs[2:].toArray.filterMapM fun b => do
          let d ← b.fvarId!.getDecl
          return if u.all || u.names.contains d.userName then some d else none
        -- `hx` is only needed by `change_var_domain` when a domain fact is declared.
        let xI := mkIdent xn
        let mut tacs : Array (TSyntax `tactic) := #[← if lets.isEmpty then
            `(tactic| intro $xI:ident _) else `(tactic| intro $xI:ident $(mkIdent `hx):ident)]
        for d in lets do
          tacs := tacs.push
            (← `(tactic| have $(mkIdent d.userName):ident : $(← delabT d.type) :=
              by change_var_domain))
        let showTac ← `(tactic| change $showT)
        -- Two variants, tried in this order by the replay. (1) The chain stated alone (`have`),
        -- without expected type: Mathlib states `HasDerivAt.mul` for the pointwise product
        -- `c * d` of functions, and unifying it with `fun x => 2 * x` unfolds the real numeral
        -- `2` (to `{ cauchy := 2 }`); `exact` then compares the functions by unfolding, which
        -- succeeds. (2) The chain inline, under `change`: premises proved by `by …` whose type
        -- only the expected type fixes (`DifferentiableAt.hasDerivAt (by fun_prop …)`) need it.
        let showTacs := if explicitV then #[] else #[showTac]
        let v1 := tacs ++ #[← `(tactic| have $hd:ident := $chain)] ++ showTacs ++
          #[← `(tactic| exact $(← finish hd))]
        let v2 := tacs ++ showTacs ++ #[← `(tactic| exact $(← finish chain))]
        pure (.ok ([← `(Lean.Parser.Tactic.tacticSeq| $v1*),
          ← `(Lean.Parser.Tactic.tacticSeq| $v2*)], vfun))
    catch e => pure (.error e.toMessageData)
  s.restore
  let .ok (scripts, vfun) := built? | return .error (match built? with | .error m => m | _ => m!"")
  for script in scripts do
    if ← checkDerivScript S f within xn script (if explicitV then some vfun else none) then
      return .ok (script, vfun)
  return .error m!"no script built from the proof of the derivative replays (with the oracles off)"

/-- Suggest the tactics `tacs`, one per line, as replacement text for `ref`. The text is given as
a string, aligned by hand on the column where `ref` starts: a `tacticSeq` given as syntax is
formatted as an indented block starting on a new line, so applying it added a line break and
an extra level of indentation. Aligning on the column (not on the line's indentation) also
fits a replacement after `case deriv =>` on the same line. -/
def suggestTactics (ref : Syntax) (tacs : Array (TSyntax `tactic))
    (usingBy : Array (TSyntax `tactic) := #[]) : TacticM Unit := do
  let some range := ref.getRange? | throwError "change_var?: no position for the suggestion"
  let (_, column) := TryThis.getIndentAndColumn (← getFileMap) range
  let w := TryThis.getInputWidth (← getOptions)
  let mut lines : Array String := #[]
  for t in tacs do
    lines := lines.push ((← PrettyPrinter.ppTactic t).pretty w column column)
  let mut text := String.intercalate ("\n".pushn ' ' column) lines.toList
  -- `using by` followed by a script: written by hand, the script two columns deeper (the
  -- pretty-printer puts `by` on its own line, at the column of the script).
  unless usingBy.isEmpty do
    text := text ++ " using by"
    for t in usingBy do
      text := text ++ "\n".pushn ' ' (column + 2) ++
        (← PrettyPrinter.ppTactic t).pretty w (column + 2) (column + 2)
  TryThis.addSuggestion ref { suggestion := .string text }

/-- `change_var_deriv?` proves the goal `deriv` like `change_var_deriv`, and suggests the explicit,
oracle-independent script that does the same (see `derivScript`). When no such script can be
built, it falls back to plain `change_var_deriv`: if that closes the goal, a warning gives the
reason why no script was built; if it fails, only its error is shown. -/
elab tk:"change_var_deriv?" : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  let (xn, S, f, within, given?) ← derivGoal "change_var_deriv?" ty
  match ← derivScript S f within xn given? (explicitV := given?.isSome) with
  | .ok (script, _) =>
    evalTactic script
    -- `tacticSeq` → `tacticSeq1Indented` → the separated list of tactics.
    suggestTactics tk (script.raw[0][0].getSepArgs.map (⟨·⟩))
  | .error reason =>
    -- If `change_var_deriv` fails too, its own error says why (no duplicate in a warning); if it
    -- succeeds, say why no explicit script was suggested.
    evalTactic (← `(tactic| change_var_deriv))
    logWarningAt tk m!"change_var_deriv?: no explicit script could be built ({reason}); the goal \
      was closed by `change_var_deriv`, which calls the derivative oracles"

/-- `change_var_side` closes one obligation of `change_var` other than `deriv` (`hv`, `hg`, `ceq`,
`hα`, `hT`, `hs`, `hinj`, `himg`) with the closers of `change_var!`: `closeRealSideGoals`, then
`closeCircleSideGoals`, then `closeSetSideGoals`, each through `runClosed` with the budget
`changeVar.sideGoalHeartbeats`. It does not look at the mode: the first family that closes the goal
wins. It fails without changing anything when none does. -/
elab "change_var_side" : tactic => withMainContext do
  let g ← getMainGoal
  for closer in [closeRealSideGoals, closeCircleSideGoals, closeSetSideGoals] do
    if ← runClosed g closer changeVar.sideGoalHeartbeats then
      replaceMainGoal []
      return
  throwError "change_var_side: could not close{indentExpr (← g.getType)}\n(tried the closers of \
    real, circle and set mode, each within `changeVar.sideGoalHeartbeats`)"

/-- `change_var_disch` is `first | change_var_deriv | change_var_side`: the automation of
`change_var!` as a discharger for the rigid form, `change_var (disch := change_var_disch) u = ψ with
g`. Run on each obligation in turn, it proves `deriv` with `change_var_deriv` (fixing `?ψ'`) and the
others with `change_var_side`. -/
macro "change_var_disch" : tactic => `(tactic| first | change_var_deriv | change_var_side)

/-- Set mode of `change_var`: `∫ x in s, F x` (Lebesgue measure) becomes `∫ u in ψ '' s, g u`, or
`∫ u in T, g u` with `onto T`.

It reads `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` from right to left:
`MeasurableSet s → (∀ x ∈ s, HasDerivWithinAt ψ (ψ' x) s x) → InjOn ψ s →
 ∫ u in ψ '' s, g u = ∫ x in s, |ψ' x| • g (ψ x)`, after
`MeasureTheory.setIntegral_congr_fun` (`MeasurableSet s → EqOn F G s → ∫ x in s, F = ∫ x in s, G`)
has replaced `F` by the candidate `fun x => |ψ' x| • g (ψ x)`.

Same skeleton as the rigid real mode (`realMode`), in all forms: `ψ'` is the data metavariable
`?ψ'`, fixed by the proof of the goal `deriv`, and the obligations are tagged goals, in the order
main, `deriv` (`∀ x ∈ s, HasDerivWithinAt ψ (?ψ' x) s x`), `hs` (`MeasurableSet s`, shared by
both lemmas), `hinj` (`Set.InjOn ψ s`), `himg` (`ψ '' s = T`, with `onto` only), `ceq`
(`EqOn F (|ψ'| • g ∘ ψ) s`), then the data goal `ψ'`. With `using h`, `ψ'` is read off `h`, and
there is neither a goal `deriv` nor a data goal. Compared with the interval lemma,
there is no continuity obligation, but injectivity and the absolute value of the derivative
appear, and the image of `s` must be named: that is why interval integrals keep their own mode. -/
def setMode (J ψfun : Expr) (xn : Name) (gStx? : Option Term) (mode : Mode)
    (onto? : Option Term) (using? : Option Term := none) : TacticM Outcome := do
  let μr := J.getArg! 5
  let s := μr.getArg! 3
  unless (μr.getArg! 2).isAppOf ``MeasureTheory.MeasureSpace.volume do
    throwError "change_var: set mode needs the Lebesgue measure (`volume`), not{indentExpr
      (μr.getArg! 2)}"
  let realTy := mkConst ``Real
  let E := J.getArg! 1
  -- The derivative and its proof, when given with `using h` (all forms).
  let given? ← using?.mapM (elabDerivProof · s ψfun true xn)
  -- `g`: given, or (automatic mode only) searched with `|ψ'|` written as `-ψ'` when `ψ' ≤ 0` is
  -- provable on `s` (domain facts in context), as `ψ'` otherwise; the search is untrusted, `ceq`
  -- checks the result.
  let F := J.getArg! 6
  let (g, gsrc) ← match gStx?, mode with
    | some gStx, _ => pure (← elabUserG gStx (← mkArrow realTy E), "given with `with`")
    | none, .rigid _ => throwError "change_var: the rigid form needs `with g`"
    | none, .auto => do
      let g? ← withRealVarIn xn s fun x _ => do
        let (v, src) ← match given? with
          | some (vfun, _) => pure (vfun.beta #[x], "given with `using`")
          | none => do let (v0, _, src) ← deriveAt ψfun x; pure ((← tidy v0).expr, src)
        let ψx := ψfun.beta #[x]
        have v : Q(ℝ) := v
        let negV : Q(ℝ) := q(-$v)
        let nonpos ← do
          let goal ← mkFreshExprMVar q($v ≤ 0)
          runClosed goal.mvarId! (do
            evalTactic (← `(tactic| apply neg_nonneg.mp))
            evalTactic (← `(tactic| try simp only [neg_div, neg_neg, neg_mul, mul_neg, neg_sub]))
            evalTactic (← `(tactic| first | positivity | change_var_domain)))
            changeVar.ringHeartbeats
        let order := if nonpos then [negV, v] else [v, negV]
        for w in order do
          let w := (← tidy w).expr
          if let some g ← findOuter? x ψx (F.beta #[x]) w then return some g
        -- The search failed: say on what (the integrand, `ψ'` and its source, both signs).
        let signs := if nonpos then "-ψ' then ψ' (ψ' ≤ 0 on the set)" else "ψ' then -ψ'"
        throwError "change_var: could not write the integrand{indentExpr (F.beta #[x])}\nas \
          |ψ'| • g ({ψx}) with ψ' ={indentExpr v}\n({src}; tried {signs}); give g with \
          `… with g`{fallbackHint src}"
      let some g := g? | throwError "change_var: could not write the integrand as \
          |ψ'| • g (ψ x); give g with `… with g`"
      pure (← tidyFun g, "found by the factor search (with ±ψ')")
  let disch? : Option (TacticM Unit) ← match mode with
    | .rigid d => pure d
    | .auto => pure (some (evalTactic (← `(tactic| change_var_disch))))
  let T? ← onto?.mapM fun T => do
    let T ← instantiateMVars (← elabTerm T q(Set ℝ))
    if T.hasSyntheticSorry then throwAbortTactic
    -- As for `g` and `ψ`: nothing would solve a hole, and the goal is not touched yet.
    if T.hasExprMVar then
      throwError "change_var: the image set{indentExpr T}\nhas holes; give it completely"
    return T
  -- The derivative: given with `using` (then `deriv` is proved), or the data metavariable `?ψ'`
  -- with the goal `deriv`.
  let (v, vLine, trailing, hderiv, derivGoals) ← match given? with
    | some (v, h) => pure (v, m!"derivative: ψ' = {v}  (given with `using`)", [], h, [])
    | none => do
      let (v, vLine) ← freshDerivMVar
      let hd ← mkFreshExprSyntheticOpaqueMVar (← derivStatement s ψfun v true xn) (tag := `deriv)
      pure (v, vLine, [v.mvarId!], hd, [hd.mvarId!])
  have sQ : Q(Set ℝ) := s
  have ψQ : Q(ℝ → ℝ) := ψfun
  let hs ← mkFreshExprSyntheticOpaqueMVar q(MeasurableSet $sQ) (tag := `hs)
  let hinj ← mkFreshExprSyntheticOpaqueMVar q(Set.InjOn $ψQ $sQ) (tag := `hinj)
  let himg? ← T?.mapM fun T => do
    have T : Q(Set ℝ) := T
    mkFreshExprSyntheticOpaqueMVar q($ψQ '' $sQ = $T) (tag := `himg)
  let ψS ← Term.exprToSyntax ψfun
  let vS ← Term.exprToSyntax v
  let gS ← Term.exprToSyntax g
  let HS ← Term.exprToSyntax hderiv
  let hsS ← Term.exprToSyntax hs
  let hinjS ← Term.exprToSyntax hinj
  let (sideLine, closed) ← rewriteAndClose (closer? := disch?)
      (extra := derivGoals ++ [hs.mvarId!, hinj.mvarId!] ++ (himg?.map (·.mvarId!)).toList)
      (trailing := trailing) (betaMain := true) do
    evalTactic (← `(tactic|
      rewrite [MeasureTheory.setIntegral_congr_fun $hsS (g := fun x => |$vS x| • $gS ($ψS x)) ?ceq,
        ← MeasureTheory.integral_image_eq_integral_abs_deriv_smul (f := $ψS) (f' := $vS) $hsS $HS
          $hinjS $gS]))
    if let some himg := himg? then
      let himgS ← Term.exprToSyntax himg
      evalTactic (← `(tactic| rewrite [$himgS:term]))
  let ψf ← withRealVar xn fun x => ppExpr (ψfun.beta #[x])
  let lines := #[
    m!"change_var, set mode: u = {ψf} on {s}; outer function: g = {g}  ({gsrc})",
    vLine,
    m!"rewrite: `MeasureTheory.setIntegral_congr_fun` (hs: s measurable; ceq: integrand = \
      |ψ'| • g ∘ ψ on s)",
    m!"substitution: `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` (deriv: ψ' \
      derivative of ψ within s; hs; hinj: InjOn ψ s){if T?.isSome then m!"; himg: ψ '' s = T"
      else m!""}",
    sideLine]
  return { g, lines, closed, deriv? := some (s, ψfun, true, xn) }

/-- Substitution in the first interval integral of the goal, or else the first set integral:
`∫ x in a..b, F x = ∫ u in ψ a..ψ b, g u` when `F x = ψ' x * g (ψ x)`. Here `ψ` is the new
variable (`u = ψ x`, written after `change_var u =`), `ψ'` its derivative, and `g` the new
integrand, a function of `u` (for `∫ 2 * x * exp (x ^ 2)` and `u = x ^ 2`, `g = exp`). See the
module docstring (sections *What it does*, *Obligations* and *Dischargers*).

* `change_var u = ψ with g` (rigid): one rewrite, no search, no automation. It leaves the tagged
  obligations, to be handled with `case … => …`:
  real mode `deriv`, `hv`, `hg`, `ceq`; circle mode `hα`, `hT`, `ceq`; set mode `deriv`, `hs`,
  `hinj`, `himg` (with `onto`), `ceq`. Prove `deriv` first: it fixes the derivative `?ψ'`.
* `change_var (disch := tac) u = ψ with g`: the same, with `tac` tried on each obligation, as in
  `simp (disch := …)`.
* `change_var! u = ψ [onto T] [with g] [using h]` (automatic): derivative by the derivative
  oracles if any is imported (activated silently by any import, even transitive;
  `set_option changeVar.derivOracles false` turns them off; `fun_prop` otherwise), search for `g`
  when it is not given, obligations attempted with the built-in closers.
* `… using h` (all three forms, real and set modes): `h` proves `deriv` (`∀ x ∈ [[a, b]], HasDerivAt
  ψ (ψ' x) x`, or `HasDerivWithinAt ψ (ψ' x) s x` on a set), and `ψ'` is read off its type. No goal
  `deriv`; in `change_var!` it replaces the oracles. A `using` proof that does not fit is an error,
  as in Mathlib's `apply_fun … using`.
* `change_var? u = ψ [onto T] [with g] [using h]`: as `change_var!`, plus a report and an
  equivalent call without search or oracle: `change_var (disch := change_var_side) u = ψ with g
  using by …`, the `by` block an explicit chain of Mathlib lemmas, replayed with the oracles off
  before being suggested; when no such script replays, the compact
  `change_var (disch := change_var_disch) … with g`, which is not oracle-free; a `using h` given
  by the user is kept; in circle mode `(disch := change_var_side)` without `using`.
* `onto T` (set integrals `∫ x in s, F x` only, all three forms) names the image `ψ '' s`,
  with the extra obligation `himg : ψ '' s = T`.
Named automation: `change_var_disch` (`first | change_var_deriv | change_var_side`) on any
obligation, `change_var_deriv` on `deriv` (`change_var_deriv?` to see its proof as Mathlib lemmas),
`change_var_side` on the others, `change_var_abs` to remove `|ψ'|`, `change_var_domain` for `0 < e`,
`e ≠ 0` from `x ∈ S` hypotheses, `change_var_bounds` for the same from the bounds of `x ∈ S` only.
Budgets: options `changeVar.*Heartbeats` (see `withBudget`). -/
syntax (name := changeVar) "change_var " ("(" &"disch" " := " tacticSeq ") ")?
  ident " = " term (" onto " term)? " with " term (" using " term)? : tactic

@[inherit_doc changeVar]
syntax (name := changeVarBang) "change_var! " ident " = " term (" onto " term)?
  (" with " term)? (" using " term)? : tactic

@[inherit_doc changeVar]
syntax (name := changeVarQ) "change_var? " ident " = " term (" onto " term)?
  (" with " term)? (" using " term)? : tactic

/-- Elaborate the new variable `ψ` in the integral's binder name `xn` (a fresh real variable),
with the checks shared by all modes, before the goal is touched: an elaboration error already
reported stops quietly; holes are refused (nothing would solve them); a constant `ψ` is refused
(its derivative is `0`, so `g` would be `F / 0`). Returns `ψ` as a function and its type. -/
def elabNewVar (ψ : Term) (xn : Name) : TacticM (Expr × Expr) := do
  let (ψfun, ψty) ← withRealVar xn fun x => do
    let ψx ← instantiateMVars (← elabTerm ψ none)
    return (← mkLambdaFVars #[x] ψx, ← inferType ψx)
  if ψfun.hasSyntheticSorry then throwAbortTactic
  if ψfun.hasExprMVar then
    throwError "change_var: the new variable{indentExpr ψfun}\nhas holes; give it completely"
  if !ψfun.bindingBody!.hasLooseBVars then
    throwError "change_var: {ψfun} does not depend on the integration variable `{xn}`"
  return (ψfun, ψty)

/-- Shared implementation of the three forms: selects the mode from the type of `ψ`, runs it, and
returns the outer function used and the report. -/
def changeVarCore (ψ : Term) (g? : Option Term) (mode : Mode) (onto? : Option Term := none)
    (using? : Option Term := none) : TacticM Outcome := withMainContext do
  let target ← getMainTarget
  let some I := findIntervalIntegral? target
    | -- No interval integral: set mode (all three forms).
      let some J := findSetIntegral? target
        | -- Integrals under a binder only (see `findClosed?`), or none at all.
          if (target.find? fun s => isIntervalIntegral s || isSetIntegral s).isSome then
            throwError "change_var: the only integrals of the goal are under a binder (`∀`, \
              `fun`, …) and depend on its variable; introduce it first (`intro`)"
          throwError "change_var: no interval integral and no set integral in the goal"
      let F0 := J.getArg! 6
      let xn := match F0 with | .lam n .. => n | _ => `x
      let (ψfun, ψty) ← elabNewVar ψ xn
      unless ψty.isConstOf ``Real do
        throwError "change_var: set mode needs a real new variable, not {ψty}"
      setMode J ψfun xn g? mode onto? using?
  if onto?.isSome then
    throwError "change_var: `onto T` is for set integrals `∫ x in s, F x`; an interval \
      integral `∫ x in a..b` goes to `∫ u in ψ a..ψ b`"
  let F0 := I.getArg! 3
  -- Reuse the integral's binder name so that the user can write `ψ` in it.
  let xn := match F0 with | .lam n .. => n | _ => `x
  let F ← withRealVar xn fun x => mkLambdaFVars #[x] (F0.beta #[x])
  let (ψfun, ψty) ← elabNewVar ψ xn
  -- The type of `ψ` selects the mode.
  if ψty.isConstOf ``Real then
    realMode F ψfun (I.getArg! 4) (I.getArg! 5) xn g? mode using?
  else if ψty.isConstOf ``Complex then
    if using?.isSome then
      throwError "change_var: circle mode has no derivative obligation; `using` is for real and \
        set modes"
    -- Cheap checks first (fail fast, goal untouched on failure).
    let shape ← circleShape I ψfun xn
    -- A real integral is cast: `∫ F = w ↔ ↑(∫ F) = ↑w` and `↑(∫ F) = ∫ ↑F`.
    let mut pre : Array MessageData := #[]
    if (← inferType I).isConstOf ``Real then
      try
        evalTactic (← `(tactic|
          (apply Complex.ofReal_injective; rw [← intervalIntegral.integral_ofReal])))
      catch _ =>
        throwError "change_var: circle mode on a real integral needs a goal `∫ … = value` with \
          the integral alone on the left-hand side (it is cast to ℂ first)"
      pre := #[m!"real integral cast to ℂ (`Complex.ofReal_injective`, \
        `intervalIntegral.integral_ofReal`)"]
    let some I' ← withMainContext do pure (findIntervalIntegral? (← getMainTarget))
      | throwError "change_var: lost the integral after casting to ℂ"
    let o ← complexMode I' ψfun xn shape g? mode
    return { o with lines := pre ++ o.lines }
  else
    throwError "change_var: the new variable must be real or complex, not {ψty}"

elab_rules : tactic
  | `(tactic| change_var $[(disch := $d:tacticSeq)]? $_:ident = $ψ:term $[onto $T:term]?
      with $g:term $[using $h]?) => do
    let disch? : Option (TacticM Unit) := d.map fun d => evalTactic d
    discard <| changeVarCore ψ (some g) (.rigid disch?) T h

elab_rules : tactic
  | `(tactic| change_var! $_:ident = $ψ:term $[onto $T:term]? $[with $g?]? $[using $h]?) =>
    do discard <| changeVarCore ψ g? .auto T h

elab_rules : tactic
  | `(tactic| change_var?%$tk $u:ident = $ψ:term $[onto $T:term]? $[with $g?]?
      $[using $h?]?) => do
    let main ← getMainGoal
    let o ← changeVarCore ψ g? .auto T h?
    logInfoAt tk (MessageData.joinSep o.lines.toList "\n")
    -- Suggest an equivalent script without search and without any oracle: the rigid call with `g`
    -- explicit, `(disch := change_var_side)`, and the derivative proved by `using`: the user's own
    -- `h`, or `by` the explicit chain of Mathlib lemmas (`derivScript`). Since `using` is
    -- elaborated before the rewrite, `ψ'` is known when `change_var_side` meets `hv` and `ceq`.
    -- Without an explicit script, the compact form `(disch := change_var_disch)`. Circle mode has
    -- no derivative: `(disch := change_var_side)`. Binder types are printed so that the suggestion
    -- re-elaborates without an expected type.
    let delabB (e : Expr) : TermElabM Term :=
      withOptions (fun o => o.setBool `pp.funBinderTypes true) (PrettyPrinter.delab e)
    let gT ← delabB o.g
    let some (S, f, within, xn) := o.deriv? | do
      suggestTactics (← getRef)
        #[← `(tactic| change_var (disch := change_var_side) $u:ident = $ψ with $gT)]
    -- The user's own `using h` is kept as is.
    if let some h := h? then
      let tac ← match T with
        | some T =>
          `(tactic| change_var (disch := change_var_side) $u:ident = $ψ onto $T with $gT using $h)
        | none => `(tactic| change_var (disch := change_var_side) $u:ident = $ψ with $gT using $h)
      suggestTactics (← getRef) #[tac]
      return
    match ← main.withContext (derivScript S f within xn) with
    | .ok (script, _) =>
      let tac ← match T with
        | some T => `(tactic| change_var (disch := change_var_side) $u:ident = $ψ onto $T with $gT)
        | none => `(tactic| change_var (disch := change_var_side) $u:ident = $ψ with $gT)
      -- `tacticSeq` → `tacticSeq1Indented` → the separated list of tactics.
      suggestTactics (← getRef) #[tac] (usingBy := script.raw[0][0].getSepArgs.map (⟨·⟩))
    | .error reason =>
      logInfoAt tk m!"no explicit `deriv` script ({reason}): the suggestion uses \
        `change_var_disch`, which calls the derivative oracles again on replay"
      let tac ← match T with
        | some T => `(tactic| change_var (disch := change_var_disch) $u:ident = $ψ onto $T with $gT)
        | none => `(tactic| change_var (disch := change_var_disch) $u:ident = $ψ with $gT)
      suggestTactics (← getRef) #[tac]

end ChangeVar

end
