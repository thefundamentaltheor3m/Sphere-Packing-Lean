# Metaprogram review — `summability`

**Target:** `SpherePacking/Tactic/Summability.lean` — the `summability` macro, the
`@[fun_prop]` tagging of `Summable` + 12 closure/leaf lemmas, and the helper
`summable_cast_mul_geometric_of_norm_lt_one`.
**Reviewer method:** metaprogram-review skill. Build green; adversarial tests via
`lake env lean`; axioms, timeouts, and the documented workaround empirically verified.

---

## 1. Summary

**Specification** (*authored*, docstring lines 15–41, 72–76): register `Summable` as a
`fun_prop` predicate (following the repo's `ResToImagAxis.Real` precedent) with its
algebraic closure lemmas and geometric-series leaves; `summability` is `fun_prop` with the
discharger `first | assumption | positivity | norm_num`. `summability (disch := tac)`
overrides it. Reindexing (ℕ↔ℕ+↔ℤ) is explicitly out of scope, and bare `↑n * r^n` and the
`cexp` leaf are documented as not tagged (to avoid unifier timeouts).

**Overall:** On its in-scope goals the tactic works well and reads cleanly, and the design
(predicate + closure lemmas tagged for `fun_prop`) is the right idiom. Soundness is clean,
and — contrary to my hypothesis — the global `@[fun_prop] Summable` tagging does **not**
slow ordinary continuity `fun_prop` calls (goal-directed). However there are two serious
problems: the tactic has **zero production adoption**, and its documented workaround for
the most common out-of-scope shape (`↑n * r^n`) **times out**.

**Top findings:**
1. **(MAJOR, faithfulness/robustness)** The docstring instructs: "For bare-form goals,
   `have` this lemma into the context before calling `summability`." This **times out**
   (whnf, default 200k heartbeats) — verified on both the pure `↑n * r^n` goal and a
   realistic compound `f n + ↑n * r^n`. Any goal *containing* a bare `↑n * r^n` subterm is
   effectively unusable with `summability`, and the escape hatch as written does not work.
2. **(MAJOR, applicability)** `summability` is **never called in production** — every
   non-test occurrence of the word is a comment. Only the `@[fun_prop]` tagging is
   (potentially) load-bearing; the tactic name is exercised solely in tests.
3. **(MINOR, error behavior)** Even the plain out-of-scope call `summability` on `↑n * r^n`
   does not fail fast — it burns the full heartbeat budget then errors with a `isDefEq`
   timeout, rather than a quick, legible failure.

---

## 2. Specification assessment

**Specificity — clean.** One job: prove `Summable` goals compositionally. The
discharger and `(disch := …)` override are appropriate refinements.

**Necessity & Novelty — good idiom, correct precedent.** Registering `Summable` with
`fun_prop` is exactly the "extend an existing tactic via its extension point" path the
skill favors, and it mirrors the repo's own `ResToImagAxis.Real` trick. The `summability`
name is a thin alias (`fun_prop (disch := …)`); the real deliverable is the tag set. That
is a legitimate design — no finding on novelty per se.

**Applicability — weak (headline).** Grep shows **0** production call sites of the
`summability` tactic (all matches are comments in `FG`, `LPBound`, `Derivative`,
`EisensteinAsymptotics`, …). The `Summable`-heavy files exist (the proposal cites 196
`Summable` occurrences), but they do not call `summability`. Either (a) wire the tactic
into those proofs (the real validation, and where the timeout issue #1 must be confronted),
or (b) if the tag set is the intended contribution, say so and consider whether the macro
alias earns its name. As shipped, the tactic is exercised only by its own test file.

---

## 3. Findings by criterion

### Soundness — clean
`#print axioms` on `summability`'s output (`↑n^3 * r^n` summable) =
`[propext, Classical.choice, Quot.sound]`. `fun_prop` produces kernel-checked terms. No
finding.

### Completeness — in-scope good; a dangerous out-of-scope edge
- In scope, everything works: closure (`add`/`neg`/`sub`/`mul_left`/`mul_right`/`div_const`/
  `const_smul`), geometric and `↑n^k · r^n` leaves, norm variants, `Fin`-indexed, and
  compound combinations — all pass (appendix, and `Test/Summability.lean`).
- **(MAJOR) The documented workaround times out.** The docstring says bare `↑n * r^n`
  goals should be handled by `have summable_cast_mul_geometric_of_norm_lt_one hr;
  summability`. Both of these **time out at `whnf` (200k heartbeats)** (appendix W1, W2):
  ```lean
  -- times out:
  have h := summable_cast_mul_geometric_of_norm_lt_one hr; summability
  -- times out even with a summable f alongside:
  Summable (fun n => f n + (n:ℂ) * r ^ n)   -- via have + summability
  ```
  Root cause is the one the docstring itself names: `fun_prop` tries to reconcile the bare
  `↑n` against the tagged `summable_pow_mul_geometric_of_norm_lt_one`'s `↑n ^ ?k`, and the
  `ℂ`-instance-tower unification explodes. Crucially, *not tagging* the bare lemma does not
  prevent this — the explosion comes from the `_pow_mul_` lemma matching the bare subterm,
  and having the exact lemma in context does not short-circuit it. **Recommendation:**
  correct the docstring — a goal containing a bare `↑n * r^n` subterm must **not** be given
  to `summability`; use `exact summable_cast_mul_geometric_of_norm_lt_one hr` (pure case) or
  decompose with `Summable.add`/`.mul_left` manually (compound case), exactly as
  `Test/Summability.lean`'s own `combined` section does (it uses the term directly, never
  `by summability`). If a `summability`-compatible path is wanted, investigate constraining
  the `_pow_mul_` leaf (e.g. a dedicated simproc/`fun_prop` transition that requires a
  literal exponent, or `fun_prop` transparency limits) so the bare shape fails fast instead
  of exploding.

### Documentation, Faithfulness & Referencing — thorough but with the broken workaround
The file is unusually well-documented: the untagged lemmas, their rationale (isDefEq
timeouts), the reindexing-out-of-scope note, and the `cexp` guidance are all spelled out,
and the `ResToImagAxis.Real` precedent is credited. The single but serious defect is #1:
the prescribed bare-form workaround does not work. Fix the prose.

### Error Messages — slow failure on the bad shape
- **(MINOR)** `summability` on `↑n * r^n` (without the `have`) also **times out** rather
  than failing quickly (appendix). A user probing whether `summability` handles a shape
  pays a full heartbeat budget to find out "no". This is intrinsic to the `fun_prop`
  unification explosion; the mitigation is documentation (#1) plus, ideally, the leaf
  constraint suggested above.

### Readability & Maintainability — clean
The tag list is grouped and legible; the helper lemma carries a precise docstring. The two
`macro_rules` (default vs. `(disch := …)`) are minimal. No finding.

### User-friendliness — good where it works
`summability` and `summability (disch := norm_num [abs_of_pos])` both behave. The discharger
default (`assumption | positivity | norm_num`) covers the real side conditions (`‖r‖ < 1`
by assumption, `0 < c` by positivity). Name is accurate. The rough edge is entirely the
`↑n * r^n` timeout (#1).

### Efficiency — clean in scope; catastrophic on the bad shape
In-scope goals close quickly. **Positive check:** I profiled `Continuous (fun x => x^2 +
sin x) := by fun_prop` with the global `@[fun_prop] Summable` tags loaded — 9.8 ms, no
regression, confirming the tagging does not pollute unrelated goal-directed `fun_prop`
runs. The only efficiency cliff is the `↑n * r^n` timeout (#1/#3).

---

## 4. Adversarial test appendix

`import SpherePacking.Tactic.Summability`. ✓ = as expected.

| # | Test | Expected | Actual |
|---|------|----------|--------|
| axcheck | `#print axioms` of `↑n^3·r^n` summable | ≤ 3 std | `[propext, Classical.choice, Quot.sound]` ✓ |
| in-1 | `(2:ℂ)·f n − g n/3` (closure) | close | closed ✓ |
| in-2 | `r^n`, `‖r‖<1` | close | closed ✓ |
| in-3 | `f : Fin 37 → ℂ` | close | closed ✓ |
| bare | `↑n · r^n` with `fail_if_success summability` | fast fail | **isDefEq timeout (200k)** → MINOR #3 |
| W1 | docstring workaround: `have lemma; summability` on `↑n·r^n` | close | **whnf timeout (200k)** → MAJOR #1 |
| W2 | `have lemma; summability` on `f n + ↑n·r^n` | close | **whnf timeout (200k)** → MAJOR #1 |
| non | `Summable (fun n => ↑n)` (divergent) | fail | fails (no timeout; shape doesn't match `_·r^n`) ✓ |
| funprop | `Continuous (x^2 + sin x)` by `fun_prop`, tags loaded | no regression | 9.8 ms ✓ (global tagging benign) |

(The `cexp`-shaped probe was a malformed goal — `ℂ`/`ℍ` `HMul` type error on my part — and
is excluded.)

**Adoption grep (evidence for MAJOR #2):** `summability` tactic = 0 production call sites
(all textual matches are comments); exercised only in `Test/Summability.lean`.
