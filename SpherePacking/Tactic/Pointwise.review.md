# Metaprogram review — `pointwise`

**Target:** `SpherePacking/Tactic/Pointwise.lean` (the `pointwise` macro and the
`pointwise_simps` attribute set) + `SpherePacking/Tactic/PointwiseAttr.lean`.
**Reviewer method:** metaprogram-review skill. Build green; adversarial tests run with
`lake env lean`; axioms and a candidate fix empirically verified.

---

## 1. Summary

**Specification** (*authored*, docstring lines 14–41, 70–77): a one-word replacement for
the idiom `ext z; simp only [Pi.mul_apply, Pi.add_apply, …, smul_eq_mul]; ring` used to
prove pointwise identities between functions (typically `ℍ → ℂ`). Forms:
`pointwise`, `pointwise [extraLemmas]`, `pointwise using tac`, and the combination.
Expands to `ext z; simp only [pointwise_simps (, extraLemmas)]; (try ring | tac)`.

**Overall:** A clean, useful convenience macro built on a well-curated simp set, following
the recommended "register a simp set + thin macro" shape. It is genuinely used (~21 call
sites across 6 files: `FG`, `RamanujanIdentities`, `Eisenstein`, both `JacobiTheta`
files, `SpherePacking`). Soundness is clean; macro hygiene is handled correctly. There is
one real completeness gap with a verified one-line fix.

**Top findings:**
1. **(MAJOR, completeness)** `pointwise` fails on a pointwise identity whose sides are
   already applied lambdas — e.g. `(fun z => f z + g z) = (fun z => g z + f z)` — because
   after `ext` there is nothing for `simp only [pointwise_simps]` to rewrite, and the
   *un-`try`ed* `simp only` throws `no progress` before `ring` runs. Fix: `try` the
   `simp only`. Verified below.
2. **(MINOR, faithfulness)** The prose "proves pointwise identities between functions"
   over-claims relative to the literal `simp`-must-make-progress behavior (see #1).
3. **(SUGGESTION, ergonomics)** No `pointwise at h`; the introduced binder `z` is
   hygienic and cannot be named from a `using` clause.

---

## 2. Specification assessment

**Specificity — clean.** One focused job: evaluate function-space algebra pointwise and
close by `ring`. The `using` and `[…]` extensions are dependent refinements, not bundled
independent features.

**Necessity & Novelty — a convenience wrapper, appropriately scoped.** This is not a novel
algorithm — `ext z; simp [Pi.*]; ring` is the pre-existing idiom, and `pointwise` packages
it. That is exactly the right verdict for this proposal: the *durable* value is the curated
`pointwise_simps` set (robust to Mathlib simp-lemma churn) plus a uniform entry point, and
shipping it as `register_simp_attr` + a thin `macro` is the idiomatic Lean way (matches
`continuity`/`measurability` in spirit). No stronger novelty argument is needed given the
call-site count. No finding.

**Applicability — strong.** ~21 real call sites across 6 non-test files, plus 12 curated
lemmas in the set. The motivating idiom (proposal cites ~30 sites, 295 `Pi.*_apply`
occurrences) is real.

---

## 3. Findings by criterion

### Soundness — clean
`#print axioms` on `pointwise`'s output = `[propext, Classical.choice, Quot.sound]`. Pure
macro over `ext`/`simp`/`ring`; nothing escapes the kernel. No finding.

### Completeness — one real gap
- **(MAJOR)** *Already-applied lambdas fail.* Consider a genuine pointwise identity whose
  two sides are explicit lambdas over the point:
  ```lean
  example (f g : ℍ → ℂ) : (fun z => f z + g z) = (fun z => g z + f z) := by pointwise
  -- error: `simp` made no progress
  ```
  After `ext z` (with beta), the goal is `f z + g z = g z + f z`; there is no `Pi.*_apply`
  to fire, so `simp only [pointwise_simps]` errors with `no progress`, and — because it is
  *not* wrapped in `try` — the macro aborts before `ring`. Even `pointwise using ring`
  fails, for the same reason (the `simp` precedes the closer). Both confirmed (appendix).
  This is squarely inside the documented purpose ("prove pointwise identities between
  functions").

  **Fix (verified):** wrap the simp:
  ```lean
  | `(tactic| pointwise) => `(tactic| (ext z; (try simp only [pointwise_simps]); try ring))
  ```
  With this, the example closes via `ring`, the "does nothing" case is tolerated, and the
  non-funext failure guarantee is preserved because it comes from `ext` failing (see
  Test line 106 / appendix F), not from `simp`. I verified all four cases: original fails,
  `using ring` fails, fixed form closes it, and `(1:ℂ)=1` still fails under the fixed
  expansion. Apply the same `try` to all four `macro_rules` branches (including the
  `using`-form, so `ext z; (try simp only …); ($tac)`).

### Documentation, Faithfulness & Referencing — good, one nuance
Docstrings on the syntax, the attribute, and the file are thorough, with all four call
forms exemplified and the "no `pointwise at h`, use the set directly" limitation stated.

- **(MINOR, faithfulness)** The prose "`pointwise` proves pointwise identities between
  functions" is broader than the implementation (which additionally requires the `simp`
  set to make progress). After the #1 fix the prose becomes accurate; until then, either
  fix the code (preferred) or note "requires at least one function-space operation to
  unfold".

### Error Messages — acceptable, minor noise
- Non-funext goals fail at `ext` with a reasonable message. For #1's case the message is
  the generic `` `simp` made no progress ``, which is misleading (the goal *is* provable);
  the #1 fix removes it.
- **(MINOR)** When `try ring` fails, `ring` still prints its `Try this: ring_nf …`
  suggestion (observed on `f z * f z = g z * g z`). This is `ring`'s own behavior under
  `try`, not `pointwise`'s fault, but it is user-visible noise. No action needed unless the
  author wants to suppress it (e.g. `first | ring | skip` does not help; it is inherent).

### Readability & Maintainability — clean
Small, obvious macro; the attribute lives in its own file with a clear rationale comment
(attribute can't be used in its declaring file). The `# shake: keep` import annotation is
correct. No finding.

### User-friendliness — good, with two small gaps
- `[extraLemmas]` (unfold local defs / use hypotheses) and `using tac` (custom closer) are
  both supported and tested — good ergonomics.
- **(SUGGESTION)** No `pointwise at h` form; the docstring redirects to
  `simp only [pointwise_simps] at h`. A `location` parameter (as `push_re_im`,
  `slash_simp`, `res_simp` all have in this same PR) would make the family uniform.
- **(SUGGESTION)** The `ext z` binder name is hardcoded and macro-hygienic, so a `using`
  clause cannot refer to the introduced point (`pointwise using (exact h z)` fails —
  appendix C). This is usually fine, but if referencing the point is ever wanted, accept an
  optional binder name: `pointwise (x)` → `ext x`. Low priority.

### Efficiency — clean
Thin macro; cost is that of `ext`/`simp only`/`ring`. On the two-argument case
(`ℍ → ℍ → ℂ`) it succeeds because `ring` mops up the residual function-level commutativity
after a single `ext` (appendix A). No finding.

---

## 4. Adversarial test appendix

`import SpherePacking.Tactic.Pointwise` (+ `UpperHalfPlane.Basic`). ✓ = as expected.

| # | Test | Expected | Actual |
|---|------|----------|--------|
| axcheck | `#print axioms` of `f*g=g*f` proof | ≤ 3 std | `[propext, Classical.choice, Quot.sound]` ✓ |
| A | `f g : ℍ→ℍ→ℂ ⊢ f*g = g*f` (2-arg) | close | closed ✓ (ring finishes after one `ext`) |
| B | `z : ℍ` already in context; `f*g=g*f` | close, no capture | closed ✓ (hygiene: introduced `z` distinct) |
| C | `pointwise using (exact h z)` | fail (hygienic `z`) | fails ✓ |
| D | `(f+g)*h - h*f = g*h` (nested) | close | closed ✓ |
| E | `f*f=g*g` then `rw[h]` | pointwise leaves goal, then closes | ✓ (`try ring` leaves `f z*f z=g z*g z`) |
| F | `(1:ℂ)=1` with `fail_if_success pointwise` | fail at `ext` | fails ✓ |
| G | `c•(f+g) = c•f+c•g` | close | closed ✓ |
| **H** | `(fun z=>f z+g z) = (fun z=>g z+f z)` | close (pointwise identity) | **`simp` made no progress** ✗ → MAJOR #1 |
| fix-1 | H under `ext z; (try simp only [pointwise_simps]); try ring` | close | closed ✓ |
| fix-2 | `(1:ℂ)=1` under fixed expansion | fail | fails ✓ (guarantee preserved) |
