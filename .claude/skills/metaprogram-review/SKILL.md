---
name: metaprogram-review
description: >
  Review a Lean 4 metaprogram (tactic, elaborator, macro, command, or attribute) and
  produce specific, actionable feedback. Use when asked to review, critique, audit, or
  evaluate a tactic or other metaprogram. Review-only: it inspects source code and runs
  adversarial tests, then reports criticisms and concrete improvement suggestions — it
  never modifies the code under review.
argument-hint: "<file, declaration, or tactic name to review>"
---

# Metaprogram Review

Review a Lean 4 metaprogram and deliver specific, actionable feedback. The subject is
typically a tactic, but may be an elaborator, macro, command, attribute, or derive
handler. The review proceeds in four steps — identify the specification (Step 1),
criticize the specification (Step 2), inspect the source (Step 3), and adversarially
test (Step 4) — and reports findings against the criteria below.

## Ground rules

- **Never modify the metaprogram under review.** This skill produces a review, not a
  patch. Do not edit, refactor, or "fix" the reviewed code, even trivially. Concrete
  suggestions belong in the report (as prose or illustrative snippets), not in the
  working tree.
- **Criticism must come with a suggestion.** Every finding should tell the author what
  to do about it: a sketch of an alternative implementation, a pointer to an existing
  Mathlib/core idiom or declaration, a proposed error message, a renaming, a doc fix.
  A finding with no path forward is incomplete.
- **Two review targets: the specification, and the implementation against it.** The
  specification — what the metaprogram is supposed to do (Step 1) — is itself under
  review in Step 2. The implementation (Steps 3–4) is judged only against that
  specification: never fault the implementation for failing at something the
  specification does not claim — though do review how gracefully it fails there (see
  Error Messages). If the *scope itself* is drawn badly, raise that as specification
  criticism, never as an implementation defect.
- The criteria below are strong guidelines and desired outcomes, not hard-wired
  directives, and they are not exhaustive. Use judgment: weigh, reorder, or extend
  them as the specific metaprogram demands, and say so in the report when you do.
- Scratch test files go in a temporary directory outside the repository (or are
  cleaned up afterwards). Never commit test scaffolding or leave it in the tree.

## Step 1 — Identify the target and infer the intended specification

1. Resolve the argument to concrete source: the file(s) defining the metaprogram, its
   syntax declarations, elaborators, and supporting definitions. If no argument was
   given and the target is not obvious from conversation context, ask.
2. Produce the **specification**: a statement of what the metaprogram is supposed to
   do, for whom, and within what scope. If the author already ships a verbose
   specification (detailed docstrings, a design note, a documented scope), adopt it —
   no inference needed. Otherwise infer it from docstrings, `/-- ... -/` doc comments
   on the syntax and implementation, README/doc pages, and any development-driving
   test cases or examples the author provided (test files, `example`s in the source,
   PR description) — and label it as *inferred* in the report. State the specification
   in a few sentences at the top of the report: it is the yardstick for Completeness
   and Faithfulness, and the boundary for adversarial testing.
3. Identify the nearest existing alternatives in core Lean and Mathlib (tactics or
   combinations of tactics that cover similar ground). You will need these for
   Step 2's necessity assessment and for Efficiency.

## Step 2 — Criticize the specification

Review the specification itself before touching the implementation: a flawless
implementation of a badly-scoped or unnecessary metaprogram is still a bad
metaprogram. If the specification was inferred rather than explicitly authored, frame
these findings as questions to the author where appropriate. Assess:

1. **Specificity.** The tactic should do select, specific things well rather than
   claim a scope too broad to implement efficiently. It should be *irreducible*: not
   splittable into two independent tactics that could or ought to ship separately.
   Bundling independent, disjoint functionalities is a defect; *dependent* composition
   (one step feeding the next in service of one clear goal) is fine. The test is focus
   and precision of purpose, not raw power.

2. **Necessity & Novelty.** Does the tactic do anything new? If its functionality is
   completely subsumed by an existing tactic, there must be a very strong argument for
   its existence (e.g. substantially better performance within its specific scope).
   Actively explore whether the tactic would be better shipped as an extension of an
   existing tactic (an extra syntax form, a simp set, an extension point, an
   attribute); if that is viable, suggest it concretely.

3. **Applicability.** The tactic should have genuine uses. Look for evidence:
   realistic examples in the docs or tests, goals that actually arise in the
   project's or Mathlib's development. A tactic exquisitely engineered for goals
   nobody has is not worth its maintenance cost — say so if that is what you find.

Evidence for these findings can also come later, from Step 4: adversarial probes just
outside the documented scope are legitimate here — if natural neighboring goals that
users will obviously expect fall outside the specification, that is specification
criticism (a scope drawn wrongly), even though it is never an implementation defect.

## Step 3 — Source inspection

Go through the source line by line. Do not skim: metaprogram bugs live in the details
(missing `withContext`, unassigned metavariables, transparency settings, missed
`instantiateMVars`). While reading, keep the full criteria list in mind, and watch in
particular for:

- **Kernel-trust red flags** (→ Soundness). These are *triggers to verify*, not
  verdicts: seeing one means you must run the `#print axioms` check in Step 4 on a
  representative output before judging severity — it is that check, not a lexical hit,
  that decides soundness. What genuinely lets a proof escape the kernel: `sorry` /
  `sorryAx`; `native_decide` and anything resting on the compiler-trust axioms it
  introduces (`Lean.ofReduceBool`, and its `Nat` companion); `set_option
  debug.skipKernelTC true`, which literally disables the kernel type-check; new `axiom`
  declarations the tactic introduces or depends on; adding declarations through paths
  that skip the kernel (note that `Lean.addDecl` *is* the kernel type-check — the
  concern is code that side-steps it, e.g. unchecked `modifyEnv` or `Environment.add`);
  and asserting an `Expr` has a type the kernel would reject. The reliable check does
  not depend on memorizing axiom names: `#print axioms` on an output should list
  *nothing beyond* what the destination repository permits — by default the standard
  three (`propext`, `Classical.choice`, `Quot.sound`), but infer the actual axiom
  policy of the repository the tactic is destined for (some projects permit additional
  axioms; some are stricter) and judge against that. Treat any name outside the
  permitted set as a flag and identify what introduced it. By contrast, `unsafe` /
  `partial` / `@[implemented_by]` / `@[extern]` in the tactic's *own implementation* do
  **not** compromise soundness on their own — the kernel still re-checks the produced
  proof term. They matter only when their results are what the kernel is asked to
  trust (e.g. feeding a compiled evaluation into a `native_decide`-style path). Flag
  them for a closer look, but do not rate them CRITICAL without a contaminated axiom
  check.
- **Correctness hazards**: metavariable context discipline (`withMainContext`,
  `instantiateMVars`, goals assigned exactly once), universe polymorphism handled or
  explicitly out of scope, `whnf`/transparency choices, error-prone matching on
  expression structure that misses `mdata`/annotations, macro/quotation hygiene
  (captured identifiers, `mkFreshUserName`/`mkFreshExprMVar` where fresh names are
  needed), uncaught exceptions.
- **Untyped expression wrangling** (→ Readability, Maintainability): where the code
  builds or matches raw `Expr`s at length, explore whether `Qq`
  (https://github.com/leanprover-community/quote4) could make it easier to read,
  maintain, review, and sanity-check. `Qq` lets expressions be constructed and matched
  in a typed style — a sort of meta-elaboration at the expression level, so terms that
  would not type-check are rejected when the metaprogram is compiled rather than
  misbehaving when the tactic runs. If it looks viable, *suggest* adopting it (with a
  sketch of one converted site) — do not insist: `Qq` is not always viable or sensible
  (highly dynamic types and universe gymnastics can fight it), so judge each site
  skeptically on whether it would actually simplify matters.
- **Structural quality** (→ Readability, Specificity, Maintainability): dead code,
  duplicated logic, God-functions doing several unrelated jobs, missing docstrings on
  public declarations, naming that violates Lean/Mathlib conventions, magic constants,
  linter suppressions without justification.

Record findings with precise locations (`file:line`) as you go.

## Step 4 — Adversarial testing

Write and run test cases designed to stretch the tactic to the limits of its
**specified** scope. The goal is to find inputs that are legitimately within scope
but make the tactic fail, misbehave, or degrade — never to demand abilities the
specification does not claim.

**Feasibility gate — check this before anything else.** Adversarial testing depends on
being able to build and run the project, which for a Mathlib-based project can be slow
or infeasible in a review session. First confirm the environment is ready: fetch the
build cache if available (`lake exe cache get`) and get a clean `lake build` (or reuse
existing `.olean`s). If the project cannot be built or Lean cannot be run here — no
toolchain, cold build that will not finish, repeated timeouts — **do not stall and do
not invent results.** Degrade gracefully: perform the review from Steps 2–3 alone, and
state explicitly in the report that adversarial testing was not performed and that the
test-dependent criteria (Completeness, Efficiency, and the output soundness check) are
therefore *not empirically verified*. **Never fabricate `#print axioms` output,
heartbeat counts, or test results you did not actually observe** — an unrun test is a
gap to disclose, not a number to guess.

Once the build is green, create a scratch file that imports the project's root module
(run it with `lake env lean`, which supplies `LEAN_PATH`; keep it in a temporary
directory outside the repo or a gitignored path). Import the project's own modules
rather than a bare `import Mathlib` if the project's conventions forbid the latter.

**First, re-run every development-driving example the author provided** — the test
cases, `example`s, and worked goals collected in Step 1. Each must still pass. This is
the cheapest, highest-signal check of Completeness and the one the author cares about
most; do it before inventing any adversarial case. A regression here — an example the
tactic is documented and intended to handle but now fails — is the most severe
Completeness finding, ranked above generic in-scope failures. Then probe further, as
applicable:

- **Boundary inputs within scope**: deeply nested expressions; many/zero hypotheses;
  shadowed or inaccessible names; `let` bindings; binders; metavariables in the goal;
  universe-polymorphic and dependently-typed instances of the claimed scope; large
  terms.
- **Environment interference**: unusual local contexts, competing instances,
  hypotheses that almost-but-not-quite match.
- **Soundness check on outputs**: for representative successful runs, check
  `#print axioms` on the resulting theorem — nothing beyond the repository's permitted
  axiom set (by default `propext`, `Classical.choice`, `Quot.sound`) should appear (a
  subset, or an empty list, is perfectly sound — a `decide`/`rfl`-backed proof may use
  none of them). Flag any name outside that allowlist, especially `sorryAx` or
  `Lean.ofReduceBool`. Separately, scrutinize `Classical.choice` even though it is a
  standard axiom: if it appears in the tactic's outputs, investigate whether choice is
  genuinely necessary for the tactic's proper functioning. If it enters only as an
  artifact of implementation convenience and the proofs could be produced without it,
  flag that and suggest the choice-free construction.
- **Performance under stress**: confirm in-scope examples succeed at the default
  `maxHeartbeats`; use Mathlib's `#count_heartbeats in` to measure, and compare
  against the nearest existing alternative on the same goals.
- **Failure behavior**: run out-of-scope and near-miss inputs *not* to fault the
  tactic for failing, but (a) to evaluate whether its error messages explain why it is
  unsuitable there, and (b) as evidence for Step 2 — if goals users will naturally
  expect sit just outside the specification, question the scope, not the
  implementation.

Run the tests (e.g. `lake env lean` on the scratch file) and record, for every test:
the exact code, what was expected, and what actually happened. Failed adversarial
tests are findings; passed ones are evidence for the report. Clean up scratch files
afterwards.

## Implementation review criteria

The specification-level criteria (Specificity, Necessity & Novelty, Applicability)
live in Step 2. The implementation is assessed against these:

1. **Soundness.** The tactic must not leave the kernel: every proof it produces must
   be kernel-checked, resting on nothing beyond the axioms the destination repository
   permits (by default `propext`, `Classical.choice`, `Quot.sound`). The decisive test
   is the `#print axioms` check on representative outputs (Step 4); the kernel-trust
   red flags from Step 3 tell you *where to point that check*, not what the verdict
   is. A **confirmed** escape — a contaminated axiom set, a demonstrated
   `sorry`/native-trust path, or a kernel-skipping environment write — is `CRITICAL`.
   A red flag you could not verify (e.g. the build would not run) is a `MAJOR`
   "unverified soundness risk" to disclose, not a CRITICAL verdict; do not rate
   soundness CRITICAL on a lexical match alone. Beyond the binary escape question,
   assess axiom *hygiene*: outputs that pull in `Classical.choice` (or other permitted
   axioms) unnecessarily deserve a finding with a suggested choice-free construction.

2. **Completeness.** The tactic should work everywhere it is supposed to — the full
   specified scope, including all development-driving test cases provided by the
   author. A regression in one of those author-provided cases is the most severe
   completeness finding (rank it above generic in-scope failures); other in-scope
   failures found by adversarial testing also land here.

3. **Documentation, Faithfulness & Referencing.** The tactic should be well-documented,
   and the implementation and documentation should match in both directions: nothing
   documented but unimplemented, nothing implemented but undocumented (surprise
   behaviors, undocumented preconditions or configuration). Docstrings should exist on
   the syntax and on public declarations, with usage examples and — where applicable —
   at least a short description of the algorithm used. A mismatch can be fixed
   on either side — say which side you recommend. **Referencing:** a non-trivial
   algorithm should cite its source — the paper, the prior tactic, or the Mathlib
   precedent it is based on — and borrowed ideas or lemmas should be attributed. Flag
   missing attribution and point to the reference that should be cited.

4. **Error Messages.** When the tactic fails, it should fail with comprehensive,
   concise error messages that explain *why it is unsuitable* for the goal at hand —
   not a bare `failed` or a leaked internal exception. Judge this on the failure
   behavior observed in adversarial testing. Where messages are poor, propose concrete
   replacement wording.

5. **Readability & Maintainability.** A human with reasonable Lean metaprogramming
   expertise should be able to read and maintain the source unaided. Expect best
   software-engineering practice where possible: small focused definitions, meaningful
   names following Lean/Mathlib naming and style conventions, comments where the code
   alone cannot carry the intent, no needless cleverness. Where lengthy raw-`Expr`
   manipulation hurts readability, consider whether typed quotation via `Qq` would
   help (see Step 3), and suggest it if so.

6. **User-friendliness.** The design should make the tactic easy to use and to combine
   with existing infrastructure. Consider — as illustrative possibilities, not a
   checklist to insist on — `using`/`with` clauses to interface with lemmas,
   `[-, -, -]` argument lists for supplying hypotheses, an `@[...]` attribute for
   registering lemmas used by default, `?_`-style handling of metavariables, or a
   configurable recursion depth. These idioms are tactic-specific; for a macro,
   command, attribute, or elaborator, judge the corresponding ergonomics instead (call
   syntax, option/config surface, sensible defaults, composability with existing
   commands). The name should accurately reflect what the metaprogram does. Judge the
   ergonomics a working mathematician would experience.

7. **Efficiency.** The tactic should perform its task reasonably efficiently: users
   should never need to raise `maxHeartbeats` for in-scope goals, and it should not,
   in principle, be slower than other reusable methods that accomplish the same task.
   Support claims with `#count_heartbeats` comparisons from Step 4.

## Report format

Deliver the review as a single structured report:

1. **Summary.** The specification (one or two sentences, marked *authored* or
   *inferred*), an overall assessment, and the two or three findings that matter most.
2. **Specification assessment.** The Step 2 verdicts — Specificity, Necessity &
   Novelty, Applicability — including any scope criticisms surfaced by out-of-scope
   adversarial probes.
3. **Findings by criterion.** For each implementation criterion with findings: the
   finding, evidence (`file:line` or a test case), why it matters, and a **concrete
   suggestion** for the author. Label severity: `CRITICAL` (a confirmed soundness
   escape), `MAJOR` (breaks the contract: completeness, faithfulness, efficiency at
   scale, an unverified soundness risk, or a specification found unnecessary or
   misconceived), `MINOR` (quality: readability, error-message wording, axiom
   hygiene), `SUGGESTION` (design directions: extensions, ergonomics, `Qq` adoption,
   spec refinements). Skip criteria with nothing to report, or note them briefly as
   clean.
4. **Adversarial test appendix.** Every test run, with exact code, expected outcome,
   and actual outcome — including the passes, so the author can see what was covered
   and reuse the cases as a regression suite.

Be specific and actionable throughout: name declarations, quote lines, propose exact
wordings and signatures. The author should be able to act on every finding without
asking what you meant.
