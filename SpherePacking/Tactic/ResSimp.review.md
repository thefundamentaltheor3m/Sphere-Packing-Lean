# Metaprogram review — `res_simp`

**Target:** the `res_simp` macro, defined in `SpherePacking/ModularForms/ResToImagAxis.lean`
(lines 49–65), with support lemmas `ResToImagAxis_apply_of_pos` /
`ResToImagAxis_apply_of_nonpos`. (Report placed in `SpherePacking/Tactic/` per the review
request; the source itself is not in the `Tactic/` directory.)
**Reviewer method:** metaprogram-review skill. Build green; adversarial tests via
`lake env lean`; axioms and a candidate discharger fix empirically verified.

---

## 1. Summary

**Specification** (*authored*, docstring lines 49–54): `res_simp` rewrites
`F.resToImagAxis t` and `ResToImagAxis F t` to `F ⟨I * t, _⟩`, discharging the side
condition `0 < t` with `positivity` (so it fires whenever `0 < t` is in context or
`positivity` can derive it, e.g. from `1 ≤ t`). Supports `res_simp [extraLemmas]` and
`res_simp at h ⊢`. Expands to
`simp (disch := positivity) only [resToImagAxis_apply, resToImagAxis_eq_resToImagAxis,
ResToImagAxis_apply_of_pos (, extras)] (loc)`.

**Overall:** A small, correct conditional-simp macro. It is well-matched to its actual 18
call sites (across `Delta.lean`, `JacobiTheta/Basic.lean`, `ResToImagAxis.lean`), all of
which `intro t ht` a literal `ht : 0 < t` from the `ResToImagAxis.Real`/`.Pos` predicate
before calling it — so `positivity` discharges trivially. Soundness clean. The only
substantive point is a mismatch between the *proposal's* stated discharge reach and what
`positivity` actually does; it does not affect current usage.

**Top findings:**
1. **(MINOR/SUGGESTION, robustness)** The proposal (#4) advertised the `positivity`
   discharger firing from `t ∈ Ioi 0` and `t₀ ≤ t` with `0 < t₀` ("the common situation in
   the asymptotics files"). Neither is handled — `positivity` does no hypothesis
   transitivity or `Ioi`-unfolding (verified). No current call site needs it, so this is
   robustness/future-proofing, not a live bug. Fix: `disch := first | positivity | linarith`
   (+ a `Set.mem_Ioi` unfold for the membership case).
2. **(MINOR, UX)** The two unconditional lemmas always fire on dot-notation goals, so on a
   non-derivable-`0 < t` goal `res_simp` leaves a *partially rewritten* `ResToImagAxis F t`
   residual rather than failing cleanly.

---

## 2. Specification assessment

**Specificity — clean.** One precise job: fire the conditional `ResToImagAxis_apply_of_pos`
rewrite with an automatic `0 < t` discharge. Not splittable.

**Necessity & Novelty — a justified convenience macro.** The value is the `(disch :=
positivity)` integration: a bare `@[simp] ResToImagAxis_apply_of_pos` would rely on simp's
default discharger for `0 < t` and, more importantly, would fire globally and unbidden on
every `ResToImagAxis F t` subterm. Packaging it as an opt-in tactic with a positivity
discharger is the cleaner design. Reasonable necessity; the novelty is modest (a
`simp`-with-discharger wrapper), which is appropriate here. No finding.

**Applicability — good.** 18 call sites, and the shape (`intro t ht; res_simp [localDef]`)
is stereotyped and real.

**Scope note (proposal vs. implementation).** The proposal claimed the discharger would
cover `t ∈ Ioi 0` and `t₀ ≤ t ∧ 0 < t₀`. Adversarial tests show `positivity` covers
neither (§3 Completeness). Because every actual site supplies `0 < t` directly, this is a
spec-vs-reality gap, not a functional defect — but the docstring (which only claims
`0 < t`-in-context and `1 ≤ t`) is the accurate description; keep it, and consider the
discharger upgrade in #1 so the proposal's intent is actually met if such hypotheses ever
appear.

---

## 3. Findings by criterion

### Soundness — clean
`#print axioms` on `res_simp`'s output = `[propext, Classical.choice, Quot.sound]`. Pure
macro over `simp`. No finding.

### Completeness — matches real usage; two documented-elsewhere gaps
- All author examples (`Test/ResSimp.lean`) and the real call-site shape pass.
- **(MINOR/SUGGESTION)** `t₀ ≤ t` (with `0 < t₀`) and `t ∈ Set.Ioi 0` are **not**
  discharged: `res_simp` leaves the goal `ResToImagAxis F t = F ⟨I*t, _⟩` unrewritten
  (appendix B, C). Verified root cause: `positivity` cannot chain `0 < t₀ ≤ t` and does not
  unfold `Ioi` membership, whereas `first | positivity | linarith` proves the former
  (appendix). Concrete upgrade:
  ```lean
  simp (disch := first | positivity | linarith) only [ … ]
  ```
  and, if `Ioi` is wanted, prepend a `simp only [Set.mem_Ioi] at *` or add a discharger
  arm `(try simp only [Set.mem_Ioi] at *) <;> linarith`. Low priority until a site needs it.

### Documentation, Faithfulness & Referencing — good
Docstrings on the tactic, both support lemmas, and the definition. Faithful: the docstring
scopes the discharge to `0 < t`-in-context / `1 ≤ t`, exactly what is delivered (it does
not repeat the proposal's over-broad `Ioi`/transitivity claim). `ResToImagAxis_apply_of_pos`
is aptly flagged as "the workhorse rewrite of `res_simp`". No finding.

### Error Messages / Failure behavior — one UX wart
- **(MINOR)** `res_simp` includes two *unconditional* rewrites
  (`resToImagAxis_apply`, `resToImagAxis_eq_resToImagAxis`) that turn dot-notation into
  `ResToImagAxis F t`. On a goal `F.resToImagAxis t = …` where `0 < t` is *not*
  positivity-derivable, these fire (progress made) but the key conditional rewrite does
  not, leaving a confusing half-rewritten `ResToImagAxis F t = F ⟨I*t, _⟩` residual and an
  `unsolved goals` error rather than a clean "res_simp: could not prove `0 < t`". The clean
  `fail_if_success` guarantee in the test file holds only because that example uses the
  `ResToImagAxis F t` spelling (no dot notation → no lemma fires → clean no-progress
  failure). *Suggestion:* document that `res_simp` may leave a `ResToImagAxis`-form residual
  when positivity fails, or gate all three lemmas behind the discharge (harder with simp).

### Readability & Maintainability — clean
Two short `macro_rules`, minor duplication of the lemma list between the `[…]` and bare
forms (three lemmas — far less severe than `push_re_im`'s four-fold duplication; not worth
a simp-set here). No finding.

### User-friendliness — good
`[extraLemmas]` (used everywhere as `res_simp [Δ, H₂, …]` to unfold the modular-form
definition in the same pass) and `at`-location are both supported. Name is accurate. No
finding.

### Efficiency — clean
Three-lemma `simp only`; negligible. No finding.

---

## 4. Adversarial test appendix

`import SpherePacking.ModularForms.ResToImagAxis`. ✓ = as expected.

| # | Test | Expected | Actual |
|---|------|----------|--------|
| axcheck | `#print axioms` of `res_simp` output | ≤ 3 std | `[propext, Classical.choice, Quot.sound]` ✓ |
| A | `1 ≤ t ⊢ F.resToImagAxis t = F ⟨I*t,_⟩` | close | closed ✓ (positivity derives `0<t`) |
| B | `0 < t₀, t₀ ≤ t ⊢ …` (transitivity) | (probe) | **not rewritten** (positivity can't chain) → MINOR #1 |
| C | `t ∈ Ioi 0 ⊢ …` | (probe) | **not rewritten** (no `Ioi` unfold) → MINOR #1 |
| D | `0 < t₀ ⊢ F.resToImagAxis (t₀^2+1) = …` | close | closed ✓ (positivity on compound) |
| E | `res_simp at h` | rewrite hyp | ✓ |
| F | `ResToImagAxis F t = 0`, `fail_if_success res_simp` | clean fail | fails ✓ (no lemma fires on the `ResToImagAxis` spelling) |
| disch | `positivity` vs `first\|positivity\|linarith` on `0<t` from `0<t₀,t₀≤t` | positivity fails, fallback wins | ✓ (fix verified) |
