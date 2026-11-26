/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import SpherePacking.Tactic.ChangeVar.SymLean

/-! # `change_var` with SymLean's derivative oracle: tests

What `SpherePacking.Tactic.ChangeVar.SymLean` adds to the core (whose behaviour is tested, without
any oracle, in `SpherePacking/Tactic/Test/ChangeVar.lean`): explicit derivatives computed by
SymLean's checked rule engine, so that `change_var!` finds `g` without `using`, `change_var_deriv` /
`change_var_disch` prove `deriv`, and `change_var?` suggests a script made of the Mathlib lemmas
behind SymLean's proof. Each test is wrapped in `#guard_msgs`. The file is a `module`, built with
the project.

The oracle is active because this file imports `SpherePacking.Tactic.ChangeVar.SymLean`:
**activation is silent**, by import, even transitive. The report of `change_var?` names the source
of the derivative, and `changeVar.derivOracles` switches the oracle off (last section). -/

open Complex MeasureTheory Set
open scoped Real


-- Many tests run a tactic on several goals at once on purpose (`trace_state`, `all_goals sorry`,
-- `guard_target` after `change_var`): they show which obligations remain open.
set_option linter.style.multiGoal false

/-! ## Real mode: `ψ'` computed by SymLean, `g` searched with it -/

-- `ψ' = 2 * x` is a factor of the integrand: `g = exp`.
#guard_msgs in
example :
    ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = ∫ u in (0 : ℝ) ^ 2..(1 : ℝ) ^ 2, Real.exp u := by
  change_var! u = x ^ 2

-- `ψ'` is not a factor: `g` absorbs the constant `1 / 2`.
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * (x ^ 2 + 1) ^ 3 =
    ∫ u in (0 : ℝ) ^ 2 + 1..(1 : ℝ) ^ 2 + 1, 1 / 2 * u ^ 3 := by
  change_var! u = x ^ 2 + 1

-- `ψ' = -sin x`: the sign is found by the search.
#guard_msgs in
example : ∫ x in (0 : ℝ)..π, Real.sin x * Real.exp (Real.cos x) =
    ∫ u in Real.cos 0..Real.cos π, -1 * Real.exp u := by
  change_var! u = Real.cos x

-- `√` on `[1, 4] ∌ 0` (SymLean's premise `x ≠ 0` from the domain).
#guard_msgs in
example : ∫ x in (1 : ℝ)..4, Real.exp (Real.sqrt x) / Real.sqrt x =
    ∫ u in Real.sqrt 1..Real.sqrt 4, 2 * Real.exp u := by
  change_var! u = Real.sqrt x

-- A negative domain: `x ≠ 0` on `[-2, -1]` from the bounds (`change_var_bounds`).
#guard_msgs in
example : ∫ x in (-2 : ℝ)..(-1), Real.exp (1 / x) / x ^ 2 =
    ∫ u in 1 / (-2 : ℝ)..1 / (-1 : ℝ), -1 * Real.exp u := by
  change_var! u = 1 / x

-- `g = u⁻¹ / 2` is continuous on the image `[1, 2]` only, which is all the lemma asks.
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x / (x ^ 2 + 1) =
    ∫ u in (0 : ℝ) ^ 2 + 1..(1 : ℝ) ^ 2 + 1, 1 / 2 * u⁻¹ := by
  change_var! u = x ^ 2 + 1

-- A ℂ-valued integrand (the substitution lemma is vector-valued).
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, 2 * (x : ℂ) * Complex.exp ((x : ℂ) ^ 2 * Complex.I) =
    ∫ u in (0 : ℝ) ^ 2..(1 : ℝ) ^ 2, Complex.exp ((u : ℂ) * Complex.I) := by
  change_var! u = x ^ 2

/-! ## Set mode -/

-- Automatic, decreasing `ψ`: `g` found with `-ψ'`, every obligation closed (even `himg`).
#guard_msgs in
example : ∫ x in Ioc (0 : ℝ) 1, Real.exp (1 - x) = ∫ u in Ico (0 : ℝ) 1, Real.exp u := by
  change_var! u = 1 - x onto Ico 0 1

-- Sphere-Packing-Lean's `s = 1 / t` from `Ioc 0 1` to `Ici 1` (`φ₀''` abstracted as `φ`):
-- `deriv`, `hs`, `hinj` automatic; `himg` and `ceq` (algebra under the opaque `φ`) by hand.
#guard_msgs in
example (φ : ℂ → ℂ) (r : ℝ) :
    ∫ t in Ioc (0 : ℝ) 1, -Complex.I * φ (-1 / (Complex.I * t)) * t ^ 2 * Complex.exp (-π * r * t) =
      ∫ s in Ici (1 : ℝ), -Complex.I * φ (Complex.I * s) * (s ^ (-4 : ℤ)) *
        Complex.exp (-π * r / s) := by
  change_var! s = 1 / t onto Ici 1 with
    fun s : ℝ => -Complex.I * φ (Complex.I * s) * ((s : ℂ) ^ (-4 : ℤ)) * Complex.exp (-π * r / s)
  case himg =>
    ext y; constructor
    · rintro ⟨x, ⟨h0, h1⟩, rfl⟩; exact (one_le_div h0).2 h1
    · intro hy
      have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
      exact ⟨1 / y, ⟨one_div_pos.2 hy0, (div_le_one hy0).2 hy⟩, one_div_one_div y⟩
  case ceq =>
    intro t ht
    obtain ⟨ht0, -⟩ := ht
    have h1 : |-1 / t ^ 2| = 1 / t ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]; norm_num
    have h3 : -1 / (Complex.I * t) = Complex.I * ((1 / t : ℝ) : ℂ) := by
      have : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0.ne'
      field_simp; push_cast; field_simp; simp [Complex.I_sq]
    simp only [h1, h3, Complex.real_smul]
    have : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0.ne'
    push_cast
    simp only [zpow_neg]
    field_simp

-- `x ↦ x ^ 2` on `(-1, 1]`: `deriv` and `hs` are closed, `hinj` (false) stays open, and so does
-- `ceq`, since `|2 * x| = 2 * x` fails for `x < 0`. Without `onto`, the new domain is the image.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∫ x in Ioc (-1 : ℝ) 1, 2 * x * Real.exp (x ^ 2) = 0 := by
  change_var! u = x ^ 2
  case hinj => sorry
  case ceq => sorry
  sorry

/-! ## The named automation, and `change_var_deriv` against a stated `ψ'` -/

-- Rigid with the named automation as discharger.
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * (x ^ 2 + 1) ^ 3 =
    ∫ u in (0 : ℝ) ^ 2 + 1..(1 : ℝ) ^ 2 + 1, 1 / 2 * u ^ 3 := by
  change_var (disch := change_var_disch) u = x ^ 2 + 1 with fun u : ℝ => 1 / 2 * u ^ 3

-- `change_var_deriv` compares its derivative with a given `ψ'` up to definitional unfolding only,
-- not up to `ring`: an equal derivative written differently (`x + x` for `2 * x`) is refused with
-- the same message as a wrong one (`3 * x`). `change_var_deriv?` bridges it (below); or prove it
-- by hand.
/--
error: change_var_deriv: the computed derivative
  fun x ↦ 2 * x
does not match the derivative stated in the goal
  fun x ↦ x + x
(compared up to definitional unfolding, not up to `ring`: if they are equal, `change_var_deriv?` bridges them; otherwise the stated derivative is wrong)
-/
#guard_msgs in
example : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x => x ^ 2) ((fun x => x + x) x) x := by
  change_var_deriv

/--
error: change_var_deriv: the computed derivative
  fun x ↦ 2 * x
does not match the derivative stated in the goal
  fun x ↦ 3 * x
(compared up to definitional unfolding, not up to `ring`: if they are equal, `change_var_deriv?` bridges them; otherwise the stated derivative is wrong)
-/
#guard_msgs in
example : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x => x ^ 2) ((fun x => 3 * x) x) x := by
  change_var_deriv

/-! ## The explaining forms: the report names the oracle, the suggestion does not need it -/

-- The explaining form: its suggestion is printed with the names visible from a module.
/--
info: change_var, real mode: u = Real.log x
derivative: ψ' = 1 / x  (SymLean's checked derivative rules)
outer function: g = fun u ↦ u  (found by the factor search)
rewrite: `intervalIntegral.integral_congr` (ceq: integrand = ψ' • g ∘ ψ on [[a, b]])
substitution: `intervalIntegral.integral_deriv_smul_comp'` (deriv: ψ' derivative of ψ on [[a, b]]; hv: ψ' continuous on [[a, b]]; hg: g continuous on ψ '' [[a, b]])
side goals: closed [hv, hg, ceq], left open []
---
info: Try this:
  [apply] change_var (disch := change_var_side) u = Real.log x with fun (u : ℝ) ↦ u using by
      intro x hx
      have hne : x ≠ 0 := by change_var_domain
      have hd := HasDerivAt.log (hasDerivAt_id' x) hne
      change HasDerivAt (fun (x : ℝ) ↦ Real.log x) (1 / x) x
      exact hd
-/
#guard_msgs in
example :
    ∫ x in (1 : ℝ)..Real.exp 1, Real.log x / x = ∫ u in Real.log 1..Real.log (Real.exp 1), u := by
  change_var? u = Real.log x

-- `change_var_deriv?` bridges SymLean's derivative to a stated one written differently.
/--
info: Try this:
  [apply] intro x _
    have hd := HasDerivAt.add (HasDerivAt.pow (hasDerivAt_id' x) 2) (hasDerivAt_const x (1 : ℝ))
    exact HasDerivAt.congr_deriv hd (by ring)
-/
#guard_msgs in
example : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x => x ^ 2 + 1) ((fun x => x + x) x) x := by
  change_var_deriv?

-- `change_var_deriv?` on the `deriv` goal of the rigid form (derivative still `?ψ'`): the script
-- states the derivative with `change`. The text continues the line of `case deriv =>`.
/--
info: Try this:
  [apply] intro x _
                  have hd :=
                    HasDerivAt.add (HasDerivAt.pow (hasDerivAt_id' x) 2) (hasDerivAt_const x (1 : ℝ))
                  change HasDerivAt (fun (x : ℝ) ↦ x ^ 2 + 1) (2 * x) x
                  exact HasDerivAt.congr_deriv hd (by norm_num)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∫ x in (0 : ℝ)..1, x * (x ^ 2 + 1) ^ 3 = 15 / 8 := by
  change_var u = x ^ 2 + 1 with fun u : ℝ => 1 / 2 * u ^ 3
  case deriv => change_var_deriv?
  case hv => sorry
  case hg => sorry
  case ceq => sorry
  sorry

/-! ## Guarantees -/

-- Goals that existed before the call are never touched, even when the main goal is closed.
#guard_msgs in
example : (∫ x in Ioc (0 : ℝ) 1, Real.exp (1 - x) = ∫ u in Ico (0 : ℝ) 1, Real.exp u)
    ∧ (fun y : ℝ => y + 1) 2 = 3 := by
  refine ⟨?_, ?_⟩
  change_var! u = 1 - x onto Ico 0 1
  guard_target =ₛ (fun y : ℝ => y + 1) 2 = 3
  norm_num

-- The main goal stays open: it is beta-reduced (new bounds `ψ a`, `ψ b` shown reduced), the
-- user's other goal is not.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : (∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = Real.exp 1 - 1)
    ∧ (fun y : ℝ => y + 1) 2 = 3 := by
  refine ⟨?_, ?_⟩
  change_var! u = x ^ 2
  guard_target =ₛ ∫ (x : ℝ) in 0 ^ 2..1 ^ 2, Real.exp x = Real.exp 1 - 1
  sorry
  guard_target =ₛ (fun y : ℝ => y + 1) 2 = 3
  norm_num

/-! ## Switching the oracle off -/

-- With `changeVar.derivOracles false`, the oracle imported here is not used: the behaviour is the
-- core's (opaque fallback), whatever the imports.
set_option changeVar.derivOracles false in
/--
error: change_var: could not write the integrand as
  deriv (fun x ↦ x ^ 2) x
• g (x ^ 2); give it with `change_var … with g`
(`ψ'` is the opaque `deriv` of the `fun_prop` fallback: derivative oracles switched off by `changeVar.derivOracles`. Give the derivative with `using h`, or switch the oracles back on (`set_option changeVar.derivOracles true`).)
-/
#guard_msgs in
example :
    ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = ∫ u in (0 : ℝ) ^ 2..(1 : ℝ) ^ 2, Real.exp u := by
  change_var! u = x ^ 2

/-! ## Domain facts given to the oracle

The oracle closes the premises of its rules (`x ≠ 0` for `log`, `1 / x`) from the facts
`0 < x` / `x < 0` and `x ≠ 0` that `withRealVarIn` derives from the domain; the explicit script
declares the ones it uses. Regression tests for the code that builds these facts. -/

-- A strict positive lower bound: `x ≠ 0` from `0 < x`.
/--
info: Try this:
  [apply] intro x hx
    have hne : x ≠ 0 := by change_var_domain
    have hd := HasDerivAt.log (hasDerivAt_id' x) hne
    exact HasDerivAt.congr_deriv hd (by norm_num)
-/
#guard_msgs in
example : ∀ x ∈ Ioc (0 : ℝ) 1, HasDerivAt (fun x => Real.log x) ((fun x => 1 / x) x) x := by
  change_var_deriv?

-- A strict negative upper bound: `x ≠ 0` from `x < 0`.
/--
info: Try this:
  [apply] intro x hx
    have hne : x ≠ 0 := by change_var_domain
    have hd := HasDerivAt.div (hasDerivAt_const x (1 : ℝ)) (hasDerivAt_id' x) hne
    exact HasDerivAt.congr_deriv hd (by ring)
-/
#guard_msgs in
example : ∀ x ∈ Ico (-1 : ℝ) 0, HasDerivAt (fun x => 1 / x) ((fun x => -(x ^ 2)⁻¹) x) x := by
  change_var_deriv?

-- A bound given by an expression whose sign `positivity` proves.
/--
info: Try this:
  [apply] intro x hx
    have hne : x ≠ 0 := by change_var_domain
    have hd := HasDerivAt.log (hasDerivAt_id' x) hne
    exact HasDerivAt.congr_deriv hd (by norm_num)
-/
#guard_msgs in
example : ∀ x ∈ Icc (Real.exp 1) 3, HasDerivAt (fun x => Real.log x) ((fun x => 1 / x) x) x := by
  change_var_deriv?

-- A domain containing `0`: no fact, the oracle's premise fails, then `fun_prop` too.
/--
error: change_var: could not differentiate
  fun x ↦ Real.log x
on the integration domain (derivative oracles tried without success: SymLean's checked derivative rules; then `fun_prop` said:
  `fun_prop` was unable to prove `DifferentiableAt ℝ (fun x ↦ Real.log x) x`
  ⏎
  Issues:
    Failed to prove necessary assumption `x ≠ 0` when applying theorem `Real.differentiableAt_log`.
    Failed to prove necessary assumption `x ≠ 0` when applying theorem `DifferentiableAt.log`.)
-/
#guard_msgs in
example : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivAt (fun x => Real.log x) ((fun x => 1 / x) x) x := by
  change_var_deriv?

-- A non-strict upper bound `0`: `x = 0` is in the domain, so no fact either.
/--
error: change_var: could not differentiate
  fun x ↦ 1 / x
on the integration domain (derivative oracles tried without success: SymLean's checked derivative rules; then `fun_prop` said:
  `fun_prop` was unable to prove `DifferentiableAt ℝ (fun x ↦ 1 / x) x`
  ⏎
  Issues:
    Failed to prove necessary assumption `x ≠ 0` when applying theorem `DifferentiableAt.fun_div`.)
-/
#guard_msgs in
example : ∀ x ∈ Ioc (-1 : ℝ) 0, HasDerivAt (fun x => 1 / x) ((fun x => -(x ^ 2)⁻¹) x) x := by
  change_var_deriv?

-- Over `t`: the facts are about `t`, and the script introduces `t`.
/--
info: change_var, real mode: u = Real.log t
derivative: ψ' = 1 / t  (SymLean's checked derivative rules)
outer function: g = fun u ↦ u  (found by the factor search)
rewrite: `intervalIntegral.integral_congr` (ceq: integrand = ψ' • g ∘ ψ on [[a, b]])
substitution: `intervalIntegral.integral_deriv_smul_comp'` (deriv: ψ' derivative of ψ on [[a, b]]; hv: ψ' continuous on [[a, b]]; hg: g continuous on ψ '' [[a, b]])
side goals: closed [hv, hg, ceq], left open []
---
info: Try this:
  [apply] change_var (disch := change_var_side) u = Real.log t with fun (u : ℝ) ↦ u using by
      intro t hx
      have hne : t ≠ 0 := by change_var_domain
      have hd := HasDerivAt.log (hasDerivAt_id' t) hne
      change HasDerivAt (fun (t : ℝ) ↦ Real.log t) (1 / t) t
      exact hd
-/
#guard_msgs in
example :
    ∫ t in (1 : ℝ)..Real.exp 1, Real.log t / t = ∫ u in Real.log 1..Real.log (Real.exp 1), u := by
  change_var? u = Real.log t
