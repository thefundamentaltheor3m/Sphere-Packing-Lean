# Metaprogram review — `positivity` extensions for `Complex.re` / `Complex.im`

**Target:** `SpherePacking/Tactic/Positivity.lean` — the `PositivityExt`s `evalComplexRe`
and `evalComplexIm`, plus their eleven support lemmas.
**Reviewer method:** metaprogram-review skill. Build green; adversarial tests via
`lake env lean`; axioms empirically verified.

---

## 1. Summary

**Specification** (*authored*, docstring lines 11–29, 72–92): `positivity` extensions that
prove `0 </≤/≠ 0` for `Complex.re`/`Complex.im` of the concrete shapes appearing in this
repo — most importantly `0 < (I * ↑t).im` (from `0 < t`), which is the membership proof for
imaginary-axis points `⟨I * t, by positivity⟩ : ℍ`. Handled: `(↑t).re`, `(↑t).im`,
`(I * w).im`, `(w * I).im`, `I.im`, `(↑z).im` for `z : ℍ` — with the `I*w`/`w*I` cases
recursing into `w.re`.

**Overall:** The **best-engineered** metaprogram in this PR. It extends `positivity` through
the official `PositivityExt` API (not a bespoke tactic), uses `Qq` matching idiomatically,
factors every proof obligation into a named, independently-checkable lemma, and fails
gracefully on everything out of scope. Soundness clean; all in-scope cases pass; all
adversarial negative cases fail cleanly. This is exactly the shape a Mathlib PR would want.
No MAJOR/CRITICAL findings.

**Top notes:**
1. **(SUGGESTION, scope)** `re`/`im` of **`Nat`/`Int` casts** to ℂ (`((n:ℕ):ℂ).re`) are not
   handled (they are not `Complex.ofReal`). Out of documented scope, but a natural
   companion; cheap to add.
2. **(NIT)** The `| _, _, _ => throwError "not Complex.re"` fallthrough is unreachable
   (the ext is keyed on `Complex.re _ : ℝ`); returning `.none` would be marginally more
   defensive than throwing.

---

## 2. Specification assessment

**Specificity — clean.** Two extensions, each doing one thing: real parts of real
coercions, and imaginary parts of the `I`-multiplied / coercion shapes. Precisely scoped
to the goals that actually arise. Not splittable in any meaningful way (they are already
two separate `@[positivity …]` handlers).

**Necessity & Novelty — exemplary.** This is the *textbook* way to add capability: rather
than a new tactic that duplicates `positivity`, it plugs into `positivity` so the new
shapes compose with everything positivity already knows and with the recursive `core`
call. There is no existing Mathlib extension for `Complex.im`/`re` of these shapes, and the
`0 < (I * ↑t).im` membership obligation is genuinely needed (it is what makes
`res_simp`/`ResToImagAxis_apply_of_pos` and ~25 `⟨I*t, by positivity⟩` sites work). Strong
necessity; correctly flagged as an upstreaming candidate.

**Applicability — strong.** Imported by `ResToImagAxis.lean` (hence transitively available
repo-wide); underpins ~25 imaginary-axis point constructions and is a precondition for
`res_simp`. Real, load-bearing.

---

## 3. Findings by criterion

### Soundness — clean
`#print axioms` on `0 < (I * ↑t).im` proved by `positivity` = `[propext, Classical.choice,
Quot.sound]`. Every branch returns a proof built from a named lemma (`im_I_mul_pos`,
`re_ofReal_pos`, …), each proved by `simpa`/`▸`; the kernel checks the result. No finding.

### Completeness — clean within scope
All eight in-scope shapes and the ℍ-point construction pass (appendix). Correctness of the
recursion confirmed: `(I * ↑(t^2+1)).im` succeeds by recursing into `(↑(t^2+1)).re` →
`t^2+1`. No in-scope failures.

### Documentation, Faithfulness & Referencing — clean
The docstring enumerates *exactly* the handled shapes and notes the recursion and the
upstreaming intent; the per-lemma names are self-documenting. Implementation matches
documentation in both directions. No finding.

### Error Messages / Failure behavior — clean (graceful)
Every out-of-scope shape returns `.none`, so `positivity` proceeds to its standard
`failed to prove positivity/nonnegativity/nonzeroness` message rather than crashing.
Verified on five negative cases (appendix A–E): `(I*↑t).im` with no fact on `t`, `(I*I).im`,
`(I*(I*↑t)).im`, `0 < (↑t).im` (only `0 ≤` is true), and the nat-cast case. All fail
cleanly. No finding.

### Readability & Maintainability — clean, one nit
Small, well-named lemmas; idiomatic `Qq` matching; `assertInstancesCommute` used correctly.

- **(NIT)** In both extensions the final `| _, _, _ => throwError "not Complex.re"` (resp.
  `im`) is unreachable because the `@[positivity Complex.re _]` registration guarantees
  `u = 0`, `α = ℝ`. Positivity extensions conventionally return `.none` for
  "not my shape"; throwing here is harmless (dead branch) but returning `.none` is the more
  defensive idiom. Trivial.

### User-friendliness — clean
There is nothing for the user to learn: `positivity` simply becomes more capable. The
`⟨I * t, by positivity⟩` idiom is the intended ergonomic and it works. No finding.

### Efficiency — clean
Each call is a constant number of pattern matches plus one recursive `core` call on a
strictly smaller term; no measurable cost. No finding.

---

## 4. Adversarial test appendix

`import SpherePacking.Tactic.Positivity`. ✓ = as expected.

| # | Test | Expected | Actual |
|---|------|----------|--------|
| axcheck | `#print axioms` of `0 < (I*↑t).im` proof | ≤ 3 std | `[propext, Classical.choice, Quot.sound]` ✓ |
| in-1 | `0 < t ⊢ 0 < (I*↑t).im` | close | closed ✓ |
| in-2 | `0 < t ⊢ 0 < (↑t*I).im` | close | closed ✓ |
| in-3 | `⊢ 0 < (I*↑(t^2+1)).im` (recursion) | close | closed ✓ |
| in-4 | `z:ℍ ⊢ 0 < (↑z).im` | close | closed ✓ |
| in-5 | `t≠0 ⊢ (I*↑t).im ≠ 0` | close | closed ✓ |
| in-6 | `⊢ 0 ≤ (↑t).im` | close | closed ✓ |
| in-7 | `⊢ 0 < I.im` | close | closed ✓ |
| in-8 | `0 < t ⊢ 0 < (↑t).re` | close | closed ✓ |
| point | `(⟨I*t, by positivity⟩ : ℍ)` construction | typecheck | ✓ (`rfl`) |
| A | `(I*↑t).im` with no fact on `t` | fail | fails cleanly ✓ |
| B | `0 < (I*I).im` (=0) | fail | fails cleanly ✓ (recursion into `re I` → none) |
| C | `0 < (I*(I*↑t)).im` | fail | fails cleanly ✓ (`re (I*t)` unhandled) |
| D | `0 < (↑t).im` (=0) | fail | fails cleanly ✓ (only `0 ≤` provable) |
| E | `0 ≤ ((n:ℕ):ℂ).re` (nat cast) | (probe) | fails — out of scope → SUGGESTION #1 |
