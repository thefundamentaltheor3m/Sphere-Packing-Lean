# Metaprogram review — `d_nf`

**Target:** `SpherePacking/Tactic/DNf.lean` (the `d_nf` macro) +
`SpherePacking/Tactic/DNfAttr.lean` (the `d_simps` set).
**Reviewer method:** metaprogram-review skill. Build green; adversarial tests via
`lake env lean`; axioms and a candidate fix empirically verified.

---

## 1. Summary

**Specification** (*authored*, docstring lines 14–52): a normalizer for the quasimodular
differential ring `(ℂ[E₂,E₄,E₆], D)`. `d_nf` runs a three-phase pipeline:
(1) `simp (disch := fun_prop) only [d_simps]` — unfold `serre_D`, push `D` through the
algebra (Leibniz/linearity, `MDiff` side goals via `fun_prop`), substitute the base
derivatives (`ramanujan_E₂/E₄/E₆`, `D_H₂/H₃/H₄`); (2) `pointwise`; (3)
`(try field_simp (disch := norm_num)); try ring`. `d_nf [foo]` adds simp lemmas to both
phases. This is **stage 1** of the two-stage proposal; the stage-2 `MvPolynomial` decision
procedure is *not* implemented (and the docstring correctly does not claim it).

**Overall:** A sound, useful pipeline macro over a well-curated `d_simps` set (13 lemmas,
tagged at their definition sites). Used at 4 call sites; `FG.lean:128` additionally uses
the structural phase alone. Soundness clean. As shipped it is a convenience pipeline
(like `pointwise`), not the novel differential-`ring` envisioned in stage 2. One
completeness limitation, same class as the `pointwise` finding, with a verified fix.

**Top findings:**
1. **(MINOR, completeness)** The first `simp only [d_simps]` is not wrapped in `try`, so a
   differential-ring identity with **no `D`/`serre_D` to unfold** (e.g. `a * b = b * a`,
   `E₄*E₆ = E₆*E₄`) fails with `simp made no progress`, even though `pointwise; ring`
   would close it. Fix: `try` the structural simp. Verified.
2. **(DOC, faithfulness)** `d_nf` is not all-or-nothing: on a goal it cannot fully close
   it leaves a *partially transformed* open goal (via the progress-making structural simp)
   rather than failing cleanly. Worth a docstring sentence.
3. **(SUGGESTION)** Stage 2 (the Kaneko–Zagier reflection to `MvPolynomial (Fin 3) ℂ`)
   remains the high-value novelty; the shipped tactic is a wrapper.

---

## 2. Specification assessment

**Specificity — clean.** A dependent pipeline (unfold `D` → pointwise → clear denominators
→ `ring`) aimed at one goal family. Not a bundle of independent tactics. The two simp
phases plus closers all serve the single "verify a differential-ring identity" purpose.

**Necessity & Novelty — convenience wrapper as shipped; the novelty is deferred.** Stage 1
is `simp only [d_simps]; pointwise; field_simp; ring` packaged with a curated attribute
set — the same convenience/maintainability pattern as `pointwise`, and a legitimate one
(the `d_simps` set is the durable asset, robust to churn, populated at definition sites).
But it is important to state plainly: **the genuinely novel object** — a `ring`-analogue
that *decides* identities in the free differential algebra by reflecting into
`MvPolynomial (Fin 3) ℂ` and applying the Ramanujan derivation — is **not implemented**.
The docstring is honest (it describes only the pipeline), so this is not a faithfulness
defect; it is a note that d_nf's current necessity rests on convenience, not capability
beyond `simp`+`ring`. If stage 2 is out of scope for this PR, say so in the docstring so a
future contributor knows the ceiling.

**Applicability — adequate.** 4 direct call sites plus the structural-phase-only use at
`FG.lean:128` (`simp (disch := fun_prop) only [d_simps, F_aux]`). That last site is
informative: the author preferred the bare structural simp there over full `d_nf`,
suggesting the fixed `pointwise`/`field_simp`/`ring` tail is not always the right closer.
Not a defect, but evidence the pipeline's tail is somewhat rigid (see #2).

---

## 3. Findings by criterion

### Soundness — clean
`#print axioms` on `d_nf`'s output (`D (E₄+E₆) = D E₄ + D E₆`) =
`[propext, Classical.choice, Quot.sound]`. Pure macro over `simp`/`pointwise`/`field_simp`/
`ring`, all kernel-checked. No finding.

### Completeness — one limitation (+ one dispelled false alarm)
- **(MINOR)** *No-`D` identities fail.* `example (a b : ℍ → ℂ) : a * b = b * a := by d_nf`
  errors with `` `simp` made no progress `` because phase (1) finds no `d_simps` rewrite
  and is not `try`-guarded (appendix A). Any pure ring identity among the generators with
  no derivative present (`E₄ * E₆ = E₆ * E₄`) hits this. **Fix (verified):**
  ```lean
  | `(tactic| d_nf) => `(tactic|
      ((try simp (disch := fun_prop) only [d_simps]);
       try pointwise using ((try field_simp (disch := norm_num)); try ring)))
  ```
  With the structural simp `try`-guarded, `a * b = b * a` routes to `pointwise; ring` and
  closes; the genuine D-goal `D (E₄^2) = 2 E₄ D E₄` still closes; and a non-function scalar
  goal still fails gracefully (the inner `ext` fails, is swallowed, goal left for the
  caller). All three verified (appendix). This is the same class as the `pointwise`
  no-progress finding — consider fixing both together.
- **Dispelled false alarm (no soundness issue):** my probe
  `fail_if_success d_nf` on the *false* goal `D (E₄+E₆) = D E₄` reported "d_nf succeeded".
  This is **not** d_nf proving a falsehood — phase (1) makes progress (`D_add`) and leaves
  a modified *open* goal without throwing, so `fail_if_success` (which only checks
  non-throwing) misfires. The axiom check and the transformed-but-open residual confirm
  soundness. It does, however, motivate #2.

### Documentation, Faithfulness & Referencing — good, one addition
Docstrings are thorough and honest about scope (stage 1 only, `[foo]` extends both phases,
`fun_prop` discharges `MDiff`). `d_simps` documents where its lemmas are tagged.

- **(DOC)** Add one sentence that `d_nf` may leave a partially-normalized open goal when
  it cannot finish (it is `simp`+`try`-based, not atomic), so users know to inspect the
  residual rather than assume failure. Optionally note the no-`D` limitation (or apply the
  #1 fix and drop the caveat).

### Error Messages — inherits the generic simp message
On out-of-pipeline goals the user sees `` `simp` made no progress `` (from phase 1) or a
leftover open goal. The #1 fix removes the former. The `ring`-under-`try` `Try this:
ring_nf` suggestion also surfaces (as in `pointwise`); inherent, low priority.

### Readability & Maintainability — clean
Compact; the `tacticSeq` splice for the closer is idiomatic. `d_simps` is tagged at
definition sites (the `@[simp, d_simps]` on the Ramanujan lemmas is a nice touch — one
attribute list, two consumers). The `# shake: keep` annotations are correct. No finding.

### User-friendliness — good, one coupling note
`d_nf [foo]` threading extra lemmas into *both* phases is the right ergonomic (unfold a
local def once, used everywhere). **Coupling note:** `d_nf` calls `pointwise`, so it
inherits the latter's already-applied-lambda no-progress behavior; in practice phase (1)
makes progress first, so the leak is dodged (appendix E closes). Fixing `pointwise`'s
`simp` `try` (see that review) also hardens `d_nf`.

### Efficiency — clean
The author examples and adversarial D-goals close at default heartbeats; the `fun_prop`
discharger only runs on `MDiff` side goals. No finding. (Stage 2, if ever built, would be
where a genuine efficiency story — `ring_nf` on reflected polynomials vs. repeated `simp`
— would matter.)

---

## 4. Adversarial test appendix

`import SpherePacking.Tactic.DNf` + `RamanujanIdentities`. ✓ = as expected.

| # | Test | Expected | Actual |
|---|------|----------|--------|
| axcheck | `#print axioms` of `D(E₄+E₆)=DE₄+DE₆` | ≤ 3 std | `[propext, Classical.choice, Quot.sound]` ✓ |
| A | `a b : ℍ→ℂ ⊢ a*b=b*a` (no `D`) | (probe) | **`simp` made no progress** → MINOR #1 |
| B | `D (E₄^2) = 2 E₄ D E₄` | close | closed ✓ |
| C | `serre_D 10 E₄ = D E₄ - 5·6⁻¹·E₂·E₄` | close | closed ✓ |
| D | `fail_if_success d_nf` on false `D(E₄+E₆)=DE₄` | (probe) | d_nf left transformed open goal (not a false proof) — test-design flaw, → DOC #2 |
| E | `D(E₄+E₆) = fun z => (DE₆) z + (DE₄) z` | close | closed ✓ (pointwise no-progress bug dodged: phase 1 makes progress) |
| fix-A | A under `try`-structural + pointwise | close | closed ✓ |
| fix-B | B under fixed expansion | close | closed ✓ |
| fix-scalar | `(1:ℂ)=1` under fixed expansion | close/fail gracefully | closed by simp reflexivity ✓ (no crash) |
