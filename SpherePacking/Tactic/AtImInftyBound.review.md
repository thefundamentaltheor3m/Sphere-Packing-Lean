# Metaprogram review — `eventually_im_infty`, `isbigo_im_infty`, and `@[bound]` curation

**Target:** the `eventually_im_infty` and `isbigo_im_infty` macros in
`SpherePacking/ForMathlib/AtImInfty.lean` (lines 21–47), together with the `@[bound]`
attribute curation on 7 lemmas (`exp_lems.lean`, `ForMathlib/Real.lean`, `Eisenstein.lean`).
(Report placed in `SpherePacking/Tactic/`; sources are not in `Tactic/`.) This corresponds
to proposal #6.
**Reviewer method:** metaprogram-review skill. Build green; adversarial tests via
`lake env lean`; axioms empirically verified.

---

## 1. Summary

**Specification** (*authored*, docstrings): `eventually_im_infty A with z hz` turns
`∀ᶠ z in atImInfty, p z` into `p z` given `hz : A ≤ z.im` (bare form leaves the
`∀ z, A ≤ z.im → p z` goal); `isbigo_im_infty C A with z hz` reduces `f =O[atImInfty] g`
to `‖f z‖ ≤ C * ‖g z‖`. The `@[bound]` curation tags workhorse inequalities so Mathlib's
`bound` closes estimate leaves.

**Overall:** All three pieces are individually sound and correct. But this is the
**weakest proposal in the PR on necessity/applicability**: the two macros are one-line
`refine` sugar over the (genuinely useful) `Filter.eventually_atImInfty` lemma, used a
combined **3 times**, and the `@[bound]` tags are used in **zero production proofs** — only
in the test file. The value here is largely prospective infrastructure.

**Top findings:**
1. **(MAJOR, applicability)** Combined adoption is minimal: `eventually_im_infty` ×2,
   `isbigo_im_infty` ×1, and `bound` used **only in `Test/AtImInftyBound.lean`** (verified
   by grep). The tactics are engineered ahead of demand.
2. **(MINOR, spec — grab-bag)** Proposal #6 bundles three loosely-coupled things (two
   intro macros + attribute curation) that share only the "estimate plumbing" theme.
3. **(MINOR, attribute hygiene)** Very specific lemmas (`norm_tsum_logDeriv_expo_le`,
   `norm_tsum_logDeriv_expo_le_of_norm_le`) are tagged with the *global* `@[bound]`
   attribute; passing them explicitly at use sites would keep the global rule set lean.

---

## 2. Specification assessment

**Specificity — mild bundling.** Proposal #6 is a grab-bag: (a) `eventually_im_infty`,
(b) `isbigo_im_infty`, (c) `@[bound]` tagging. (a) and (b) are a coherent family (both
reduce an `atImInfty` filter goal to a pointwise `A ≤ z.im → …` obligation, and (b) reuses
(a)'s `eventually_atImInfty` characterization), so grouping those two is fine. The
`@[bound]` curation is a genuinely separate concern (making a *different*, existing tactic
smarter) and only shares the "asymptotics" theme. Not a serious defect, but the three
pieces would be cleaner as two independent contributions.

**Necessity & Novelty — low.** The macros are thin `refine` wrappers:
`eventually_im_infty A with z hz` ≡ `refine eventually_atImInfty.mpr ⟨A, fun z hz => ?_⟩`.
The **reusable asset is the lemma** `Filter.eventually_atImInfty`
(`(∀ᶠ x in atImInfty, p x) ↔ ∃ A, ∀ z, A ≤ z.im → p z`), which is a legitimate ForMathlib
addition. The macro saves one line. `isbigo_im_infty` additionally prepends
`rw [isBigO_iff]` — again one line saved. This is acceptable sugar, but the novelty is
minimal and does not by itself justify much maintenance cost.

**Applicability — weak (the headline finding).** Grep across the repo:
- `eventually_im_infty`: **2** non-test call sites.
- `isbigo_im_infty`: **1** non-test call site.
- `bound` (the tactic the curation exists to serve): **0** production call sites — it
  appears *only* in `Test/AtImInftyBound.lean`.

The proposal's premise ("229 `atImInfty`/`IsBigO` sites … Mathlib's `bound` used exactly
once, underexploited") is plausible, but the delivered infrastructure has not yet been
turned on in those sites. Recommendation: either (a) land a follow-up that actually
*applies* `bound`/`eventually_im_infty` at the estimate sites the proposal cites (which
would validate the design and is the real payoff), or (b) if that is out of scope now,
keep the `Filter.eventually_atImInfty` lemma and the general-purpose `@[bound]` leaves and
consider deferring the macros until there is demand. As it stands the macros risk being
"engineered for goals nobody (yet) has."

---

## 3. Findings by criterion

### Soundness — clean
`#print axioms` on both an `eventually_im_infty` proof and a `bound` proof
(`exp (-2π) < 1/2`) = `[propext, Classical.choice, Quot.sound]`. Macros are pure `refine`
sugar; `bound` produces kernel-checked terms. No finding.

### Completeness — clean within (the small) scope
All author examples pass: `eventually_im_infty` with and without `with`, the bare form
leaving `∀ z, A ≤ z.im → …`, `isbigo_im_infty` with `with`, and all six `@[bound]` leaf
examples (`r/(1-r)³ ≤ 8r`, `‖q‖`-version, `‖cexp(2πiz)‖ < 1`, etc.). No in-scope failures.

### Documentation, Faithfulness & Referencing — good for macros; thin for the curation
- The macros have clear docstrings with both the `with` and bare behaviors. Faithful.
- **(MINOR)** The `@[bound]` curation has no central documentation of *what* was tagged and
  *why*; the rationale is spread across attribute annotations at 3 files. A one-paragraph
  note (e.g. in a `Tactic/`-level doc or the test file header, which partially does this)
  listing the curated leaves and the intended `bound` usage would help future maintainers
  decide what may be safely added/removed.

### Error Messages / Failure behavior — acceptable
- Wrong filter (`∀ᶠ … in ⊤`) fails with a `Type mismatch` showing `atImInfty` vs the actual
  filter (appendix A) — informative enough to diagnose.
- Non-`eventually`/non-`IsBigO` goals fail cleanly (appendix B, C).
No finding, though a bespoke `"eventually_im_infty: goal is not `∀ᶠ _ in atImInfty, _`"`
would be marginally friendlier (would require an `elab` instead of a `macro`; likely not
worth it at this adoption level).

### Readability & Maintainability — clean, one hygiene note
The macros are trivially readable. `Filter.eventually_atImInfty` and
`Filter.tendsto_im_atImInfty` are clean lemmas.

- **(MINOR, attribute hygiene)** `norm_tsum_logDeriv_expo_le` and `_of_norm_le` are niche,
  problem-specific bounds; tagging them `@[bound]` injects them into the *global* `bound`
  rule set, so `bound` will consider them on every unrelated bound goal repo-wide (a small
  but real cost, and a surprise if one fires unexpectedly). Prefer `bound [norm_tsum_…]` at
  the (currently zero) sites that need them, reserving global `@[bound]` for the
  general-purpose leaves (`exp_neg_two_pi_lt_half`, `div_one_sub_pow_three_le`,
  `exp_upperHalfPlane_lt_one`).

### User-friendliness — fine, one small gap
`with z hz` requires *both* identifiers; a `with z` form (auto-naming the `A ≤ z.im`
hypothesis, or `_`) would be a minor convenience. Low priority. Names are accurate.

### Efficiency — clean
`refine`/`rw` sugar; the `bound` calls close at default heartbeats. No finding.

---

## 4. Adversarial test appendix

`import SpherePacking.ForMathlib.AtImInfty` (+ `exp_lems`, `Eisenstein`, `Real`). ✓ = as expected.

| # | Test | Expected | Actual |
|---|------|----------|--------|
| axcheck | `#print axioms` of `eventually_im_infty` proof | ≤ 3 std | `[propext, Classical.choice, Quot.sound]` ✓ |
| axcheck2 | `#print axioms` of `bound` proof (`exp(-2π)<1/2`) | ≤ 3 std | `[propext, Classical.choice, Quot.sound]` ✓ |
| ev-with | `eventually_im_infty 2 with z hz` | reduce | ✓ |
| ev-bare | `eventually_im_infty 1` then `intro z _hz k` | leave `∀ z, …` | ✓ |
| A | `eventually_im_infty` on `∀ᶠ … in ⊤` | fail (wrong filter) | Type mismatch `atImInfty` vs `⊤` ✓ (informative) |
| B | `eventually_im_infty` on `True` | fail | fails cleanly ✓ |
| bo-with | `isbigo_im_infty 3 1 with z hz` | reduce to `‖f z‖ ≤ …` | ✓ |
| C | `isbigo_im_infty` on `True` | fail | fails cleanly ✓ |
| bound-1 | `r/(1-r)³ ≤ 8r` `by bound` | close | ✓ |
| bound-2 | `‖q‖/(1-‖q‖)³ ≤ 8‖q‖` `by bound` | close | ✓ |
| bound-3 | `‖cexp(2πiz)‖ < 1` `by bound` | close | ✓ |

**Adoption grep (evidence for MAJOR #1):** `eventually_im_infty` = 2 sites,
`isbigo_im_infty` = 1 site, `bound` tactic = 0 production sites (test-only).
