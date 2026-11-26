/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import SpherePacking.Tactic.ChangeVar.Core
-- `sleep_heartbeats` (testing only), for the heartbeat budgets.
public import Mathlib.Util.SleepHeartbeats

/-! # `change_var`: tests and usage examples (the core, without oracles)

One test per behaviour of `change_var`, each wrapped in `#guard_msgs`, so any change of behaviour
or message fails it; read in order, they are also the usage examples of the tactic. This file
imports `SpherePacking.Tactic.ChangeVar.Core` only: it tests the tactic on Mathlib alone, with no
derivative oracle, so derivatives are given with `using h` (or are the opaque `deriv` of the
`fun_prop` fallback). Each oracle has its own test file, for the behaviour it adds (e.g.
`SpherePacking/Tactic/Test/ChangeVarSymLean.lean`). The file is a `module`, built with the
project.

Most tests state the expected result as the right-hand side: `change_var` closes the goal by `rfl`
only if it produces exactly that integral. -/

open Complex MeasureTheory Set

-- Many tests run a tactic on several goals at once on purpose (`trace_state`, `all_goals sorry`,
-- `guard_target` after `change_var`): they show which obligations remain open.
set_option linter.style.multiGoal false
open scoped Real

/-! ## Real mode: `∫ x in a..b, ψ' x * g (ψ x) = ∫ u in ψ a..ψ b, g u` -/

-- The derivative given `using` a Mathlib lemma; `g = exp` found by the search.
#guard_msgs in
example :
    ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = ∫ u in (0 : ℝ) ^ 2..(1 : ℝ) ^ 2, Real.exp u := by
  change_var! u = x ^ 2 using fun x _ => hasDerivAt_pow 2 x

-- `ψ'` is not a factor: `g` absorbs the constant `1 / 2`.
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * (x ^ 2 + 1) ^ 3 =
    ∫ u in (0 : ℝ) ^ 2 + 1..(1 : ℝ) ^ 2 + 1, 1 / 2 * u ^ 3 := by
  change_var! u = x ^ 2 + 1 using fun x _ => ((hasDerivAt_id' x).pow 2).add_const 1

-- `ψ' = -sin x`: the sign is found by the search.
#guard_msgs in
example : ∫ x in (0 : ℝ)..π, Real.sin x * Real.exp (Real.cos x) =
    ∫ u in Real.cos 0..Real.cos π, -1 * Real.exp u := by
  change_var! u = Real.cos x using fun x _ => Real.hasDerivAt_cos x

-- `g = u⁻¹ / 2` is continuous on the image `[1, 2]` only, which is all the lemma asks.
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x / (x ^ 2 + 1) =
    ∫ u in (0 : ℝ) ^ 2 + 1..(1 : ℝ) ^ 2 + 1, 1 / 2 * u⁻¹ := by
  change_var! u = x ^ 2 + 1 using fun x _ => ((hasDerivAt_id' x).pow 2).add_const 1

-- A ℂ-valued integrand (the substitution lemma is vector-valued).
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, 2 * (x : ℂ) * Complex.exp ((x : ℂ) ^ 2 * Complex.I) =
    ∫ u in (0 : ℝ) ^ 2..(1 : ℝ) ^ 2, Complex.exp ((u : ℂ) * Complex.I) := by
  change_var! u = x ^ 2 using fun x _ => hasDerivAt_pow 2 x

/-! ## Circle mode: `∫ t in 0..T, F t = ∮ z in C(c, R), g z` -/

-- `I ^ t = circleMap 0 1 (π / 2 * t)`: `[0, 4]` is one turn.
#guard_msgs in
example :
    ∫ t in (0 : ℝ)..4, (π / 2 : ℂ) * Complex.I * Complex.I ^ (t : ℂ) * (Complex.I ^ (t : ℂ))⁻¹ =
      ∮ z in C(0, 1),
        (π : ℂ) / 2 * Complex.I * z * z⁻¹ / (((π / 2 : ℝ) : ℂ) * ((z - 0) * Complex.I)) := by
  change_var! z = Complex.I ^ (t : ℂ)

-- A real trigonometric integral: cast to `ℂ`, `cos θ = (z + z⁻¹) / 2` found; the circle integral
-- is then evaluated by `circle_rational` (not available in a module).
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∫ θ in (0 : ℝ)..2 * π, 1 / (5 + 4 * Real.cos θ) = 2 * π / 3 := by
  change_var! z = Complex.exp ((θ : ℂ) * Complex.I)
  guard_target = (∮ z in C(0, 1), 1 / (5 + 4 * ((z + z⁻¹) / 2)) / (((1 : ℝ) : ℂ) * ((z - 0) *
    Complex.I))) = ((2 * π / 3 : ℝ) : ℂ)
  sorry

/-! ## Set mode: `∫ x in s, |ψ' x| • g (ψ x) = ∫ u in ψ '' s, g u` -/

-- Rigid form: every obligation by hand.
#guard_msgs in
example : ∫ x in Ioc (0 : ℝ) 1, 2 * Real.exp (2 * x) = ∫ u in Ioc (0 : ℝ) 2, Real.exp u := by
  change_var u = 2 * x onto Ioc 0 2 with fun u : ℝ => Real.exp u
  case deriv => intro x _; exact ((hasDerivAt_id' x).const_mul 2).hasDerivWithinAt
  case hs => exact measurableSet_Ioc
  case hinj => intro a _ b _ h; simpa using h
  case himg =>
    ext y; constructor
    · rintro ⟨x, ⟨h0, h1⟩, rfl⟩; exact ⟨by simp only; linarith, by simp only; linarith⟩
    · rintro ⟨h0, h1⟩; exact ⟨y / 2, ⟨by linarith, by linarith⟩, by simp only; ring⟩
  case ceq => intro x _; simp only [mul_one, smul_eq_mul]; rw [abs_of_pos (by norm_num)]

-- Automatic, decreasing `ψ`, derivative `using`: `g` found with `-ψ'`, every obligation closed.
#guard_msgs in
example : ∫ x in Ioc (0 : ℝ) 1, Real.exp (1 - x) = ∫ u in Ico (0 : ℝ) 1, Real.exp u := by
  change_var! u = 1 - x onto Ico 0 1 using
    fun x _ => ((hasDerivAt_id' x).const_sub 1).hasDerivWithinAt

-- `x ↦ x ^ 2` on `(-1, 1]` is not injective: `hinj` (false) stays open, and so does `ceq`, since
-- `|2 * x| = 2 * x` fails for `x < 0`.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∫ x in Ioc (-1 : ℝ) 1, 2 * x * Real.exp (x ^ 2) = 0 := by
  change_var! u = x ^ 2 with fun u => Real.exp u using
    fun x _ => (hasDerivAt_pow 2 x).hasDerivWithinAt
  case hinj => sorry
  case ceq => sorry
  sorry

-- The substitution `s = 1 / t` of `MagicFunction/a/IntegralEstimates`, from `Ioc 0 1` to `Ici 1`
-- (`φ₀''` abstracted as `φ`), the derivative given `using`: `hs`, `hinj` closed by
-- `change_var_side`; `himg` and `ceq` (algebra under the opaque `φ`) by hand.
#guard_msgs in
example (φ : ℂ → ℂ) (r : ℝ) :
    ∫ t in Ioc (0 : ℝ) 1, -Complex.I * φ (-1 / (Complex.I * t)) * t ^ 2 * Complex.exp (-π * r * t) =
      ∫ s in Ici (1 : ℝ), -Complex.I * φ (Complex.I * s) * (s ^ (-4 : ℤ)) *
        Complex.exp (-π * r / s) := by
  change_var (disch := change_var_side) s = 1 / t onto Ici 1 with
    fun s : ℝ => -Complex.I * φ (Complex.I * s) * ((s : ℂ) ^ (-4 : ℤ)) * Complex.exp (-π * r / s)
    using fun x hx =>
      ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id' x) (ne_of_gt hx.1)).hasDerivWithinAt
  case himg =>
    ext y; constructor
    · rintro ⟨x, ⟨h0, h1⟩, rfl⟩; exact (one_le_div h0).2 h1
    · intro hy
      have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
      exact ⟨1 / y, ⟨one_div_pos.2 hy0, (div_le_one hy0).2 hy⟩, one_div_one_div y⟩
  case ceq =>
    intro t ht
    obtain ⟨ht0, -⟩ := ht
    have h1 : |(0 * t - 1 * 1) / t ^ 2| = 1 / t ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]; norm_num
    have h3 : -1 / (Complex.I * t) = Complex.I * ((1 / t : ℝ) : ℂ) := by
      have : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0.ne'
      field_simp; push_cast; field_simp; simp [Complex.I_sq]
    simp only [h1, h3, Complex.real_smul]
    have : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0.ne'
    push_cast
    simp only [zpow_neg]
    field_simp

/-! ## The derivative: oracles, the `fun_prop` fallback, a given `ψ'`

Without an oracle (none is imported here), `change_var!` falls back to `fun_prop` and the opaque
`deriv ψ x`; with `using h` the derivative is the one `h` states. -/

-- No oracle, but `fun_prop` proves differentiability from `hf`: the derivative is the opaque
-- `deriv f x`. `g` is still found when `deriv f x` is a factor of the integrand; `hv` (continuity
-- of `deriv f`, which `hf` does not give) stays open.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∫ x in (0 : ℝ)..1, deriv f x * Real.exp (f x) = Real.exp (f 1) - Real.exp (f 0) := by
  change_var! u = f x
  case hv => sorry
  sorry

-- The same fallback, but `deriv f x` is not a factor of the integrand: no `g` is found, and the
-- message says what to do.
/--
error: change_var: could not write the integrand as
  deriv (fun x ↦ f x) x
• g (f x); give it with `change_var … with g`
(`ψ'` is the opaque `deriv` of the `fun_prop` fallback: no derivative oracle imported. Give the derivative with `using h`, or import a derivative oracle.)
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : ∫ x in (0 : ℝ)..1, Real.exp (f x) = 0 := by
  change_var! u = f x

-- Neither an oracle nor `fun_prop`: `change_var!` fails, with `fun_prop`'s explanation.
/--
error: change_var: could not differentiate
  fun x ↦ f x
on the integration domain (no derivative oracle imported; then `fun_prop` said:
  `fun_prop` was unable to prove `DifferentiableAt ℝ (fun x ↦ f x) x`
  ⏎
  Issues:
    No theorems found for `f` in order to prove `DifferentiableAt ℝ (fun x ↦ f x) x`)
-/
#guard_msgs in
example (f : ℝ → ℝ) : ∫ x in (0 : ℝ)..1, Real.exp (f x) = 0 := by
  change_var! u = f x

-- The rigid form with `change_var_disch` does not fail: `deriv` stays open, `?ψ'` stays unassigned
-- (no closer assigns it here: `ceq` does not unify with `?ψ' x * g (ψ x)`; compare the next
-- test), so `hv` and `ceq`, which mention it, stay open too, and the data goal `ψ'` comes last.
-- `hg` does not mention `?ψ'` and is closed.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (f : ℝ → ℝ) : ∫ x in (0 : ℝ)..1, Real.exp (f x) = 0 := by
  change_var (disch := change_var_disch) u = f x with fun u => Real.exp u
  case deriv => sorry
  case hv => sorry
  case ceq => sorry
  case ψ' => exact fun _ => 0
  sorry

-- `deriv` cannot be proved, but the closer of `ceq` assigns `?ψ' := f'` by unification
-- (`f' x * f x ^ 2` against `?ψ' x * (f x) ^ 2`): sound, since `deriv` now states
-- `HasDerivAt f (f' x) x` and stays to be proved, as does `hv`.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (f f' : ℝ → ℝ) : ∫ x in (0 : ℝ)..1, f' x * f x ^ 2 = ∫ u in f 0..f 1, u ^ 2 := by
  change_var (disch := change_var_disch) u = f x with fun u : ℝ => u ^ 2
  case deriv =>
    guard_target =ₛ ∀ x ∈ uIcc 0 1, HasDerivAt (fun x => f x) (f' x) x
    sorry
  case hv => sorry

-- `deriv` left as `sorry`: `?ψ'` is never assigned, the data goal `ψ'` remains.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * Real.exp (x ^ 2) = 0 := by
  change_var u = x ^ 2 with fun u => Real.exp u / 2
  case deriv => sorry
  case hv => sorry
  case hg => sorry
  case ceq => sorry
  case ψ' => exact fun x => 2 * x
  sorry

/-! ## No oracle: `using h`, or the opaque fallback

On a plain `x ^ 2`, `change_var!` cannot find `g` from the opaque `deriv`, and says what to do;
`using h` is enough, and the named automation proves `deriv` through `fun_prop` (opaque). -/

-- No oracle: `ψ'` is the opaque `deriv` of the `fun_prop` fallback, `g` cannot be found, and the
-- message says what to do.
/--
error: change_var: could not write the integrand as
  deriv (fun x ↦ x ^ 2) x
• g (x ^ 2); give it with `change_var … with g`
(`ψ'` is the opaque `deriv` of the `fun_prop` fallback: no derivative oracle imported. Give the derivative with `using h`, or import a derivative oracle.)
-/
#guard_msgs in
example :
    ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = ∫ u in (0 : ℝ) ^ 2..(1 : ℝ) ^ 2, Real.exp u := by
  change_var! u = x ^ 2

-- With the derivative given `using` a Mathlib lemma, the automatic form needs no oracle.
#guard_msgs in
example :
    ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = ∫ u in (0 : ℝ) ^ 2..(1 : ℝ) ^ 2, Real.exp u := by
  change_var! u = x ^ 2 using fun x _ => hasDerivAt_pow 2 x

-- Rigid with the named automation: `change_var_deriv` proves `deriv` through `fun_prop`, so
-- `ψ' = deriv (fun x => x ^ 2)` stays opaque and `ceq` is left open.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example :
    ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = ∫ u in (0 : ℝ) ^ 2..(1 : ℝ) ^ 2, Real.exp u := by
  change_var (disch := change_var_disch) u = x ^ 2 with fun u : ℝ => Real.exp u
  case ceq => sorry

-- Trigonometric functions without an oracle: the core imports their derivative files, so
-- `fun_prop` proves `deriv` (opaque `deriv sin`), `hv` and `hg`; `ceq` stays open because the
-- derivative is opaque (a `simp` pass on `deriv` would close it: planned).
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example :
    ∫ x in (0 : ℝ)..1, Real.cos x * Real.sin x ^ 2 = ∫ u in Real.sin 0..Real.sin 1, u ^ 2 := by
  change_var (disch := change_var_disch) u = Real.sin x with fun u : ℝ => u ^ 2
  case ceq => sorry

/-! ## The forms: rigid, `disch`, `using`, explaining -/

-- Rigid, every obligation by hand; `deriv` first (it fixes `?ψ'`).
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, Real.exp (2 * x) = ∫ u in 2 * (0 : ℝ)..2 * 1, 1 / 2 * Real.exp u := by
  change_var u = 2 * x with fun u : ℝ => 1 / 2 * Real.exp u
  case deriv => intro x _; exact (hasDerivAt_id' x).const_mul 2
  case hv => fun_prop
  case hg => fun_prop
  case ceq =>
    intro x _
    simp only [Function.comp_apply, smul_eq_mul]
    ring

-- Rigid, the derivative given `using` a Mathlib lemma, the rest by `change_var_side`.
#guard_msgs in
example :
    ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = ∫ u in (0 : ℝ) ^ 2..(1 : ℝ) ^ 2, Real.exp u := by
  change_var (disch := change_var_side) u = x ^ 2 with fun u : ℝ => Real.exp u
    using fun x _ => hasDerivAt_pow 2 x

-- Automatic with `using`: no oracle is needed, `g` is searched with the given `ψ'`.
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * (x ^ 2 + 1) ^ 3 =
    ∫ u in (0 : ℝ) ^ 2 + 1..(1 : ℝ) ^ 2 + 1, 1 / 2 * u ^ 3 := by
  change_var! u = x ^ 2 + 1 using fun x _ => ((hasDerivAt_id' x).pow 2).add_const 1

-- That suggestion, replayed verbatim: no search, no oracle.
#guard_msgs in
example :
    ∫ x in (1 : ℝ)..Real.exp 1, Real.log x / x = ∫ u in Real.log 1..Real.log (Real.exp 1), u := by
  change_var (disch := change_var_side) u = Real.log x with fun (u : ℝ) => u using by
    intro x hx
    have hne : x ≠ 0 := by change_var_domain
    have hd := HasDerivAt.log (hasDerivAt_id' x) hne
    change HasDerivAt (fun (x : ℝ) => Real.log x) (1 / x) x
    exact hd

-- `disch` is one tactic for all obligations; a `first` whose alternatives only fit their own kind
-- of goal acts as a per-obligation choice. Here `change_var_deriv` takes `deriv`, `fun_prop` takes
-- `hv` and `hg`, and nothing fits `ceq`, which stays open.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * Real.exp (x ^ 2) = 0 := by
  change_var (disch := first | change_var_deriv | fun_prop) u = x ^ 2 with fun u => Real.exp u / 2
  case ceq => sorry
  sorry

-- An opaque function: the derivative is `deriv f x`, proved by `fun_prop`. `hv` (continuity of
-- `deriv f`) is not closed, by `change_var!` nor by the replay.
/--
info: change_var, real mode: u = f x
derivative: ψ' = deriv (fun x ↦ f x) x  (fallback: `fun_prop` differentiability, opaque `deriv`)
  (no explicit derivative: no derivative oracle imported)
outer function: g = fun u ↦ rexp u  (found by the factor search)
rewrite: `intervalIntegral.integral_congr` (ceq: integrand = ψ' • g ∘ ψ on [[a, b]])
substitution: `intervalIntegral.integral_deriv_smul_comp'` (deriv: ψ' derivative of ψ on [[a, b]]; hv: ψ' continuous on [[a, b]]; hg: g continuous on ψ '' [[a, b]])
side goals: closed [hg, ceq], left open [hv]
---
info: Try this:
  [apply] change_var (disch := change_var_side) u = f x with fun (u : ℝ) ↦ rexp u using by
      intro x _
      change HasDerivAt (fun (x : ℝ) ↦ f x) (deriv (fun (x : ℝ) ↦ f x) x) x
      exact DifferentiableAt.hasDerivAt (by fun_prop (disch := change_var_domain))
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∫ x in (0 : ℝ)..1, deriv f x * Real.exp (f x) = Real.exp (f 1) - Real.exp (f 0) := by
  change_var? u = f x
  case hv => sorry
  sorry

-- In `change_var!`/`change_var?`, `using h` replaces the oracles: `ψ'` is read off `h` (here the
-- raw `↑2 * x ^ (2 - 1) * 1`), the search for `g` uses it, and the suggestion keeps `h`.
/--
info: change_var, real mode: u = x ^ 2 + 1
derivative: ψ' = ↑2 * x ^ (2 - 1) * 1  (given with `using`)
outer function: g = fun u ↦ 1 / 2 * u ^ 3  (found by the factor search)
rewrite: `intervalIntegral.integral_congr` (ceq: integrand = ψ' • g ∘ ψ on [[a, b]])
substitution: `intervalIntegral.integral_deriv_smul_comp'` (deriv: ψ' derivative of ψ on [[a, b]]; hv: ψ' continuous on [[a, b]]; hg: g continuous on ψ '' [[a, b]])
side goals: closed [hv, hg, ceq], left open []
---
info: Try this:
  [apply] change_var (disch := change_var_side) u = x ^ 2 + 1 with fun (u : ℝ) ↦ 1 / 2 * u ^ 3 using
      fun x _ => ((hasDerivAt_id' x).pow 2).add_const 1
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * (x ^ 2 + 1) ^ 3 = 15 / 8 := by
  change_var? u = x ^ 2 + 1 using fun x _ => ((hasDerivAt_id' x).pow 2).add_const 1
  sorry

-- Rigid form: no goal `deriv`, no data goal `ψ'`; only `hv`, `hg`, `ceq` (here left to the user).
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * (x ^ 2 + 1) ^ 3 = 15 / 8 := by
  change_var u = x ^ 2 + 1 with fun u : ℝ => 1 / 2 * u ^ 3
    using fun x _ => ((hasDerivAt_id' x).pow 2).add_const 1
  case hv => sorry
  case hg => sorry
  case ceq => sorry
  sorry

-- `change_var?` in the core: the suggestion never calls an oracle. With the opaque fallback, the
-- `deriv` script is `fun_prop`'s proof; `hv` (continuity of `deriv f`) stays open, by
-- `change_var!` and by the replay.
/--
info: change_var, real mode: u = f x
derivative: ψ' = deriv (fun x ↦ f x) x  (fallback: `fun_prop` differentiability, opaque `deriv`)
  (no explicit derivative: no derivative oracle imported)
outer function: g = fun u ↦ rexp u  (found by the factor search)
rewrite: `intervalIntegral.integral_congr` (ceq: integrand = ψ' • g ∘ ψ on [[a, b]])
substitution: `intervalIntegral.integral_deriv_smul_comp'` (deriv: ψ' derivative of ψ on [[a, b]]; hv: ψ' continuous on [[a, b]]; hg: g continuous on ψ '' [[a, b]])
side goals: closed [hg, ceq], left open [hv]
---
info: Try this:
  [apply] change_var (disch := change_var_side) u = f x with fun (u : ℝ) ↦ rexp u using by
      intro x _
      change HasDerivAt (fun (x : ℝ) ↦ f x) (deriv (fun (x : ℝ) ↦ f x) x) x
      exact DifferentiableAt.hasDerivAt (by fun_prop (disch := change_var_domain))
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∫ x in (0 : ℝ)..1, deriv f x * Real.exp (f x) = ∫ u in f 0..f 1, Real.exp u := by
  change_var? u = f x
  case hv => sorry

-- Circle mode has no derivative: the suggestion is the rigid call with `change_var_side`.
/--
info: change_var, circle mode: ψ t = circleMap 1 2 (1 * t)
outer function: g = fun z ↦
  2 * I * z * (z - 1)⁻¹ / (↑1 * ((z - 1) * I))  (integrand in terms of z = ψ t, divided by dz/dt = α (z - c) I)
rewrite: `intervalIntegral.integral_congr` (ceq: integrand = α γ'(α t) g (γ (α t)))
substitution: `ChangeVar.intervalIntegral_circleMap_reparam'` (hα: α ≠ 0; hT: α * T = 2π)
side goals: closed [hα, hT, ceq], left open []
---
info: Try this:
  [apply] change_var (disch := change_var_side) z = circleMap 1 2 t with fun (z : ℂ) ↦
      2 * I * z * (z - 1)⁻¹ / (↑1 * ((z - 1) * I))
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∫ t in (0 : ℝ)..2 * π, (2 : ℂ) * Complex.I * circleMap 1 2 t * (circleMap 1 2 t - 1)⁻¹ =
    0 := by
  change_var? z = circleMap 1 2 t
  sorry

-- Set mode: `onto` and the user's `using` proof are kept in the suggestion.
/--
info: change_var, set mode: u = 1 - x on Ioc 0 1; outer function: g = fun u ↦ rexp u  (found by the factor search (with ±ψ'))
derivative: ψ' = fun x ↦ -1  (given with `using`)
rewrite: `MeasureTheory.setIntegral_congr_fun` (hs: s measurable; ceq: integrand = |ψ'| • g ∘ ψ on s)
substitution: `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` (deriv: ψ' derivative of ψ within s; hs; hinj: InjOn ψ s); himg: ψ '' s = T
side goals: closed [hs, hinj, himg, ceq], left open []
---
info: Try this:
  [apply] change_var (disch := change_var_side) u = 1 - x onto Ico 0 1 with fun (u : ℝ) ↦ rexp u using
      fun x _ => ((hasDerivAt_id' x).const_sub 1).hasDerivWithinAt
-/
#guard_msgs in
example : ∫ x in Ioc (0 : ℝ) 1, Real.exp (1 - x) = ∫ u in Ico (0 : ℝ) 1, Real.exp u := by
  change_var? u = 1 - x onto Ico 0 1 using
    fun x _ => ((hasDerivAt_id' x).const_sub 1).hasDerivWithinAt

-- `change_var_deriv?` without an oracle: the script proves the opaque `deriv` (here closed by
-- `norm_num`), and states it with `change` since `?ψ'` is unassigned.
/--
info: Try this:
  [apply] intro x _
                  change HasDerivAt (fun (x : ℝ) ↦ x ^ 2) (deriv (fun (x : ℝ) ↦ x ^ 2) x) x
                  exact DifferentiableAt.hasDerivAt (by norm_num)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = 0 := by
  change_var u = x ^ 2 with fun u : ℝ => Real.exp u
  case deriv => change_var_deriv?
  all_goals sorry

-- `change_var_deriv?` against a stated derivative: Mathlib's `simp` lemmas on `deriv` bridge the
-- opaque fallback to `2 * x` (`congr_deriv … (by norm_num)`).
/--
info: Try this:
  [apply] intro x _
    exact HasDerivAt.congr_deriv (DifferentiableAt.hasDerivAt (by norm_num)) (by norm_num)
-/
#guard_msgs in
example : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x => x ^ 2) ((fun x => 2 * x) x) x := by
  change_var_deriv?

/-! ## Sign facts on the domain

The facts `0 < x`, `x < 0`, `x ≠ 0` used by an oracle's premises and by the closers come from the
bounds of the domain (`change_var_bounds`), not from `positivity`. -/

-- `positivity` ignores hypotheses and refuses `x < 0` outright; the sign comes from the bounds,
-- read by `change_var_bounds`.
/--
error: not a positivity goal
-/
#guard_msgs in
example (x : ℝ) (_hx : x ∈ uIcc (-2 : ℝ) (-1)) : x < 0 := by positivity

#guard_msgs in
example (x : ℝ) (hx : x ∈ uIcc (-2 : ℝ) (-1)) : x < 0 ∧ x ≠ 0 ∧ x ≤ 0 := by
  refine ⟨by change_var_domain, by change_var_domain, by change_var_bounds⟩

-- Best effort: no sign on an interval containing `0`.
/--
error: change_var_bounds: the bounds
  x ≤ 1, -1 ≤ x
read from the hypotheses `x ∈ S` do not give
  x < 0
(the sign of a bound must follow by `positivity` or `norm_num`; a strict sign needs a strict bound or a bound of strict sign)
-/
#guard_msgs in
example (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) : x < 0 := by change_var_bounds

/-! ## Errors, open obligations, guarantees -/

/-- error: change_var: no interval integral and no set integral in the goal -/
#guard_msgs in
example (x : ℝ) : x = x := by change_var! u = x ^ 2

/-- error: change_var: fun x ↦ 3 does not depend on the integration variable `x` -/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by change_var! u = (3 : ℝ)

/--
error: change_var: circle mode needs the lower bound 0 (compared up to reducible unfolding), not
  1
-/
#guard_msgs in
example : ∫ t in (1 : ℝ)..2, Complex.exp ((t : ℂ) * Complex.I) = 0 := by
  change_var! z = Complex.exp ((t : ℂ) * Complex.I)

set_option pp.mvars false in
/--
error: change_var: the new variable
  fun x ↦ x * ?_ x
has holes; give it completely
-/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
  change_var u = x * _ with fun u : ℝ => u

/--
error: change_var: the only integrals of the goal are under a binder (`∀`, `fun`, …) and depend on
its variable; introduce it first (`intro`)
-/
#guard_msgs in
example : ∀ y : ℝ, ∫ x in (0 : ℝ)..y, x = y ^ 2 / 2 := by
  change_var! u = x ^ 2

-- A `using` proof of the wrong statement is an error, with no fallback to an oracle.
/--
error: Type mismatch
  hasDerivAt_id' x
has type
  HasDerivAt (fun x ↦ x) 1 x
but is expected to have type
  HasDerivAt (fun x ↦ x ^ 2 + 1) (?ψ' x) x
---
error: unsolved goals
⊢ ∫ (x : ℝ) in 0..1, x * (x ^ 2 + 1) ^ 3 = 15 / 8
-/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * (x ^ 2 + 1) ^ 3 = 15 / 8 := by
  change_var! u = x ^ 2 + 1 using fun x _ => hasDerivAt_id' x

-- A wrong `g` is not an error: `ceq` is left open, and false.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * Real.exp (x ^ 2) = 0 := by
  change_var! u = x ^ 2 with fun u => Real.exp u
  case ceq => sorry
  sorry

-- A failing discharger is not an error, and `sorry` as a discharger closes nothing.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * Real.exp (x ^ 2) = 0 := by
  change_var (disch := sorry) u = x ^ 2 with fun u => Real.exp u / 2
  case deriv => sorry
  case hv => sorry
  case hg => sorry
  case ceq => sorry
  case ψ' => exact fun x => 2 * x
  sorry

/-- error: change_var: the new variable must be real or complex, not ℕ -/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by change_var! u = Nat.floor x

-- `ψ` is written in the integral's own variable (`t` here, not `x`).
/--
error: Unknown identifier `x`
---
error: unsolved goals
⊢ ∫ (t : ℝ) in 0..1, t = 1 / 2
-/
#guard_msgs in
example : ∫ t in (0 : ℝ)..1, t = 1 / 2 := by change_var! u = x ^ 2

/--
error: change_var: `onto T` is for set integrals `∫ x in s, F x`; an interval integral `∫ x in a..b` goes to `∫ u in ψ a..ψ b`
-/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by change_var! u = x ^ 2 onto Icc 0 1

/--
error: change_var: fun t ↦ ↑t ^ 2 is not one of I ^ (t : ℂ), exp (t * I), circleMap c R (α * t)
-/
#guard_msgs in
example : ∫ t in (0 : ℝ)..2, (t : ℂ) = 0 := by change_var! z = (t : ℂ) ^ 2

/--
error: change_var: circle mode on a real integral needs a goal `∫ … = value` with the integral alone on the left-hand side (it is cast to ℂ first)
-/
#guard_msgs in
example : 1 + ∫ t in (0 : ℝ)..2 * π, Real.cos t = 1 := by change_var! z = exp ((t : ℂ) * I)

/--
error: change_var: set mode needs the Lebesgue measure (`volume`), not
  μ
-/
#guard_msgs in
example (μ : Measure ℝ) : ∫ x in Ioc (0 : ℝ) 1, x ∂μ = 0 := by change_var! u = 2 * x

set_option pp.mvars false in
/--
error: change_var: the outer function
  fun u ↦ ?_ u
has holes; give it completely
-/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by change_var u = x ^ 2 with fun u => _

set_option pp.mvars false in
/--
error: change_var: the image set
  Ioc 0 ?_
has holes; give it completely
-/
#guard_msgs in
example : ∫ x in Ioc (0 : ℝ) 1, 2 * Real.exp (2 * x) = ∫ u in Ioc (0 : ℝ) 2, Real.exp u := by
  change_var u = 2 * x onto Ioc 0 _ with fun u : ℝ => Real.exp u

/--
error: change_var: the only integrals of the goal are under a binder (`∀`, `fun`, …) and depend on
its variable; introduce it first (`intro`)
-/
#guard_msgs in
example : ∀ y : ℝ, ∫ x in Ioc (0 : ℝ) y, x = y ^ 2 / 2 := by
  change_var! u = 2 * x

/--
error: change_var: the integrand has 9 factors that could be part of ψ'; the search for g tries at most 8 (2^8 subsets). Give g with `change_var … with g`.
-/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * x * x * x * x * x * x * x * x = 0 := by
  change_var! u = x ^ 2

/-- error: change_var: circle mode has no derivative obligation; `using` is for real and set modes -/
#guard_msgs in
example : ∫ θ in (0 : ℝ)..2 * π, Real.cos θ = 0 := by
  change_var! z = exp ((θ : ℂ) * I) using fun x _ => hasDerivAt_id' x

-- Goals that existed before the call are never touched, even when the main goal is closed.
#guard_msgs in
example : (∫ x in Ioc (0 : ℝ) 1, Real.exp (1 - x) = ∫ u in Ico (0 : ℝ) 1, Real.exp u)
    ∧ (fun y : ℝ => y + 1) 2 = 3 := by
  refine ⟨?_, ?_⟩
  change_var! u = 1 - x onto Ico 0 1 using
    fun x _ => ((hasDerivAt_id' x).const_sub 1).hasDerivWithinAt
  guard_target =ₛ (fun y : ℝ => y + 1) 2 = 3
  norm_num

-- The main goal stays open: it is beta-reduced (bounds `ψ a`, `ψ b`), the user's goal is not.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : (∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = Real.exp 1 - 1)
    ∧ (fun y : ℝ => y + 1) 2 = 3 := by
  refine ⟨?_, ?_⟩
  change_var! u = x ^ 2 using fun x _ => hasDerivAt_pow 2 x
  guard_target =ₛ ∫ (x : ℝ) in 0 ^ 2..1 ^ 2, Real.exp x = Real.exp 1 - 1
  sorry
  guard_target =ₛ (fun y : ℝ => y + 1) 2 = 3
  norm_num


-- A wrong `g` is reported as `left open [ceq]` by `change_var?`.
/--
info: change_var, real mode: u = x ^ 2
derivative: ψ' = ↑2 * x ^ (2 - 1)  (given with `using`)
outer function: g = fun u ↦ rexp u  (given with `with`)
rewrite: `intervalIntegral.integral_congr` (ceq: integrand = ψ' • g ∘ ψ on [[a, b]])
substitution: `intervalIntegral.integral_deriv_smul_comp'` (deriv: ψ' derivative of ψ on [[a, b]]; hv: ψ' continuous on [[a, b]]; hg: g continuous on ψ '' [[a, b]])
side goals: closed [hv, hg], left open [ceq]
---
info: Try this:
  [apply] change_var (disch := change_var_side) u = x ^ 2 with fun (u : ℝ) ↦ rexp u using fun x _ =>
      hasDerivAt_pow 2 x
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * Real.exp (x ^ 2) = 0 := by
  change_var? u = x ^ 2 with fun u => Real.exp u using fun x _ => hasDerivAt_pow 2 x
  case ceq => sorry
  sorry

-- A `using by …` whose script fails: the script's own error, and the call stops.
/--
error: Type mismatch
  hasDerivAt_id' x
has type
  HasDerivAt (fun x ↦ x) 1 x
but is expected to have type
  HasDerivAt (fun x ↦ x ^ 2 + 1) (?ψ' x) x
---
error: unsolved goals
⊢ ∫ (x : ℝ) in 0..1, x * (x ^ 2 + 1) ^ 3 = 15 / 8
-/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * (x ^ 2 + 1) ^ 3 = 15 / 8 := by
  change_var! u = x ^ 2 + 1 using by intro x _; exact hasDerivAt_id' x

/-! ## Binder names and statement shapes

The statements built by the tactic keep the integral's own binder name (`t` here, not `x`) and
their exact shape, in every mode: regression tests for the code that builds them (converted to
Qq quotations, which would otherwise fix the binder name). -/

-- Rigid real mode over `t`: `deriv` quantifies over `t`.
/--
trace: ⊢ ∫ (x : ℝ) in 0 ^ 2..1 ^ 2, rexp x = 0

case deriv
⊢ ∀ t ∈ uIcc 0 1, HasDerivAt (fun t ↦ t ^ 2) (?ψ' t) t

case hv
⊢ ContinuousOn ?ψ' (uIcc 0 1)

case hg
⊢ ContinuousOn (fun u ↦ rexp u) ((fun t ↦ t ^ 2) '' uIcc 0 1)

case ceq
⊢ EqOn (fun t ↦ 2 * t * rexp (t ^ 2)) (fun x ↦ ?ψ' x • ((fun u ↦ rexp u) ∘ fun t ↦ t ^ 2) x) (uIcc 0 1)

case ψ'
⊢ ℝ → ℝ
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∫ t in (0 : ℝ)..1, 2 * t * Real.exp (t ^ 2) = 0 := by
  change_var u = t ^ 2 with fun u : ℝ => Real.exp u
  trace_state
  all_goals sorry

-- Rigid set mode over `t`: the five obligations and their exact statements.
/--
trace: case deriv
⊢ ∀ t ∈ Ioc 0 1, HasDerivWithinAt (fun t ↦ 2 * t) (?ψ' t) (Ioc 0 1) t

case hs
⊢ MeasurableSet (Ioc 0 1)

case hinj
⊢ InjOn (fun t ↦ 2 * t) (Ioc 0 1)

case himg
⊢ (fun t ↦ 2 * t) '' Ioc 0 1 = Ioc 0 2

case ceq
⊢ EqOn (fun t ↦ 2 * rexp (2 * t)) (fun x ↦ |?ψ' x| • rexp (2 * x)) (Ioc 0 1)

case ψ'
⊢ ℝ → ℝ
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∫ t in Ioc (0 : ℝ) 1, 2 * Real.exp (2 * t) = ∫ u in Ioc (0 : ℝ) 2, Real.exp u := by
  change_var u = 2 * t onto Ioc 0 2 with fun u : ℝ => Real.exp u
  trace_state
  all_goals sorry

-- The expected type of a `using` proof quantifies over `t` too.
/--
error: Type mismatch
  hasDerivAt_id' t
has type
  HasDerivAt (fun x ↦ x) 1 t
but is expected to have type
  HasDerivAt (fun t ↦ t ^ 2 + 1) (?ψ' t) t
---
error: unsolved goals
⊢ ∫ (t : ℝ) in 0..1, t * (t ^ 2 + 1) ^ 3 = 15 / 8
-/
#guard_msgs in
example : ∫ t in (0 : ℝ)..1, t * (t ^ 2 + 1) ^ 3 = 15 / 8 := by
  change_var! u = t ^ 2 + 1 using fun t _ => hasDerivAt_id' t

-- Circle mode compares the lower bound with `0` at reducible transparency: `1 - 1` is refused at
-- once rather than unfolded.
/--
error: change_var: circle mode needs the lower bound 0 (compared up to reducible unfolding), not
  1 - 1
-/
#guard_msgs in
example : ∫ t in (1 - 1 : ℝ)..2 * π, Complex.exp ((t : ℂ) * Complex.I) = 0 := by
  change_var! z = Complex.exp ((t : ℂ) * Complex.I)

-- The fallback over `t`: the report and the suggested script use `t`.
/--
info: change_var, real mode: u = f t
derivative: ψ' = deriv (fun t ↦ f t) t  (fallback: `fun_prop` differentiability, opaque `deriv`)
  (no explicit derivative: no derivative oracle imported)
outer function: g = fun u ↦ rexp u  (found by the factor search)
rewrite: `intervalIntegral.integral_congr` (ceq: integrand = ψ' • g ∘ ψ on [[a, b]])
substitution: `intervalIntegral.integral_deriv_smul_comp'` (deriv: ψ' derivative of ψ on [[a, b]]; hv: ψ' continuous on [[a, b]]; hg: g continuous on ψ '' [[a, b]])
side goals: closed [hg, ceq], left open [hv]
---
info: Try this:
  [apply] change_var (disch := change_var_side) u = f t with fun (u : ℝ) ↦ rexp u using by
      intro t _
      change HasDerivAt (fun (t : ℝ) ↦ f t) (deriv (fun (t : ℝ) ↦ f t) t) t
      exact DifferentiableAt.hasDerivAt (by fun_prop (disch := change_var_domain))
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∫ t in (0 : ℝ)..1, deriv f t * Real.exp (f t) = ∫ u in f 0..f 1, Real.exp u := by
  change_var? u = f t
  case hv => sorry

/-! ## Heartbeat budgets

Every potentially slow step runs under a budget read from an option (unit of `maxHeartbeats`):
`changeVar.sideGoalHeartbeats` (each attempt on one obligation), `changeVar.ringHeartbeats`,
`changeVar.searchHeartbeats` (the whole search for `g`), `changeVar.fallbackHeartbeats`. A budget is
capped by what remains of the enclosing limit, `0` removes a per-step cap, and a user
`maxHeartbeats 0` keeps the caps. `sleep_heartbeats` makes a discharger slow on purpose. -/

-- A discharger slower than its budget is cut: every obligation stays open, nothing fails.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option changeVar.sideGoalHeartbeats 1000 in
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example :
    ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = ∫ u in (0 : ℝ) ^ 2..(1 : ℝ) ^ 2, Real.exp u := by
  change_var (disch := (sleep_heartbeats 2000; change_var_side)) u = x ^ 2 with
    fun u : ℝ => Real.exp u using fun x _ => hasDerivAt_pow 2 x
  case hv => sorry
  case hg => sorry
  case ceq => sorry

-- With the per-step cap removed (and no user limit), the same slow discharger succeeds.
set_option maxHeartbeats 0 in
set_option changeVar.sideGoalHeartbeats 0 in
#guard_msgs in
example :
    ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = ∫ u in (0 : ℝ) ^ 2..(1 : ℝ) ^ 2, Real.exp u := by
  change_var (disch := (sleep_heartbeats 60000; change_var_side)) u = x ^ 2 with
    fun u : ℝ => Real.exp u using fun x _ => hasDerivAt_pow 2 x

-- A user `maxHeartbeats 0` does not remove the per-step caps (they make failures fast).
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 0 in
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example :
    ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = ∫ u in (0 : ℝ) ^ 2..(1 : ℝ) ^ 2, Real.exp u := by
  change_var (disch := (sleep_heartbeats 60000; change_var_side)) u = x ^ 2 with
    fun u : ℝ => Real.exp u using fun x _ => hasDerivAt_pow 2 x
  case hv => sorry
  case hg => sorry
  case ceq => sorry

-- The user's limit is enforced inside a step, with Lean's own error, when it is the tighter one.
set_option maxHeartbeats 3000 in
/--
error: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (3000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example :
    ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = ∫ u in (0 : ℝ) ^ 2..(1 : ℝ) ^ 2, Real.exp u := by
  change_var (disch := (sleep_heartbeats 5000; change_var_side)) u = x ^ 2 with
    fun u : ℝ => Real.exp u using fun x _ => hasDerivAt_pow 2 x

-- The whole search for `g` has its own budget; exhausting it is an error naming the option.
set_option changeVar.searchHeartbeats 1 in
/--
error: change_var: step budget exhausted (changeVar.searchHeartbeats 1); raise it with `set_option changeVar.searchHeartbeats <n>`
-/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * (x ^ 2 + 1) ^ 3 = 0 := by
  change_var! u = x ^ 2 + 1 using fun x _ => ((hasDerivAt_id' x).pow 2).add_const 1


-- A natural case where the default budget is too small and a larger one works (`ceq` needs
-- `ring1` to expand `(x + b + c) ^ 16 * (x - b + c) ^ 16 = ((x + c) ^ 2 - b ^ 2) ^ 16`) is kept
-- below, commented out, for two reasons.
-- * It is a threshold test calibrated on the speed of Mathlib's `ring`, not on `change_var`:
--   measured at one Mathlib revision, inside `change_var`, `ring1` on this identity needs between
--   30000 and 40000 heartbeats for the exponent 14 and between 50000 and 150000 for 16. A change
--   in `ring` (or `simp`, `field_simp` in the other closers) moves the threshold, and with this
--   project's weekly Mathlib bumps the test would turn the build red while `change_var` did not
--   change.
-- * It is a load test: the pair costs about a minute of build time.
-- The budget mechanism itself is pinned above by the `sleep_heartbeats` tests, which do not depend
-- on the speed of any tactic. To check the natural case by hand, uncomment the pair and, if the
-- first test closes `ceq` (or the second fails to), move the exponent. With the exponent 18,
-- raising `changeVar.sideGoalHeartbeats` alone is not enough: the declaration then exceeds the
-- user's `maxHeartbeats` (200000), which bounds every step, so `maxHeartbeats` must be raised too.
/-
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (b c : ℝ) : ∫ x in (0 : ℝ)..1, (x + b + c) ^ 16 * (x - b + c) ^ 16 =
    ∫ u in (0 : ℝ) + 1..(1 : ℝ) + 1, ((u - 1 + c) ^ 2 - b ^ 2) ^ 16 := by
  change_var (disch := change_var_side) u = x + 1 with fun u : ℝ => ((u - 1 + c) ^ 2 - b ^ 2) ^ 16
    using fun x _ => (hasDerivAt_id' x).add_const 1
  case ceq => sorry

-- The same with the budget of one obligation raised by hand: `ceq` is closed.
set_option changeVar.sideGoalHeartbeats 150000 in
#guard_msgs in
example (b c : ℝ) : ∫ x in (0 : ℝ)..1, (x + b + c) ^ 16 * (x - b + c) ^ 16 =
    ∫ u in (0 : ℝ) + 1..(1 : ℝ) + 1, ((u - 1 + c) ^ 2 - b ^ 2) ^ 16 := by
  change_var (disch := change_var_side) u = x + 1 with fun u : ℝ => ((u - 1 + c) ^ 2 - b ^ 2) ^ 16
    using fun x _ => (hasDerivAt_id' x).add_const 1
-/
