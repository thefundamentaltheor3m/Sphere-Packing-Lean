# Metaprogram review — `push_re_im` / `norm_exp_simp`

**Target:** `SpherePacking/Tactic/PushReIm.lean` (the `PushReIm.parse` splitter, the
`pushRe`/`pushIm` simprocs, and the `push_re_im` / `norm_exp_simp` macros).
**Reviewer method:** metaprogram-review skill (spec → spec-criticism → source → adversarial).
Build green; adversarial tests run with `lake env lean`; axioms and timings empirically
verified.

---

## 1. Summary

**Specification** (*authored*, docstring lines 14–48, 176–228): `push_re_im` computes
`.re`/`.im` projections of complex expressions *symbolically* by recursively splitting
through `+`, `*`, `-`, `⁻¹`, `/`, nat-`^`, `conj`, `I`, numerals and the coercions
`ℝ, ℕ, ℤ, ℍ → ℂ` (plus `cexp` of a real coercion), leaving genuinely opaque atoms `w`
as `⟨w.re, w.im⟩`, then finishing with `try ring_nf`. `norm_exp_simp` additionally
rewrites `‖cexp w‖ = rexp w.re` and distributes norms over products. Both accept
`[extraLemmas]` and a `location`.

**Overall:** A well-designed, genuinely novel tactic that is the strongest of the nine in
this PR. It cleanly extends the pre-existing `NormNumI` splitter to symbolic atoms via
two `simproc`s, so it composes with the whole `simp` infrastructure for free. Soundness
is clean (standard three axioms), all fourteen author examples pass, and `norm_exp_simp`
is *faster* than the hand-rolled chain it replaces. The findings are all quality-level.

**Top findings:**
1. **(MINOR, maintainability)** The base simp-lemma list is duplicated **four times**
   across the `macro_rules`. Factor it into a `register_simp_attr push_re_im_simps` set —
   exactly the pattern this same PR uses for `pointwise_simps`/`d_simps`/`slash_simps`.
2. **(MINOR, error message)** Out-of-scope inputs (e.g. `zpow`) fail with the bare
   `simp made no progress`, which does not hint at what is unsupported.
3. **(SUGGESTION, scope)** `zpow` (`z ^ (k : ℤ)`) and `cexp` of a non-`ofReal` argument
   are the obvious neighboring goals; consider documenting them explicitly as out of
   scope or extending the splitter.

---

## 2. Specification assessment

**Specificity — clean.** The tactic does one precise thing (normalize `.re`/`.im`) and
`norm_exp_simp` is a *dependent* composition on top of it (norm-of-exp rewriting feeding
the same simprocs), not an independent second tactic bundled in. The `simproc` core
(`pushRe`/`pushIm`) is the irreducible unit and both macros are thin wrappers over it —
good factoring.

**Necessity & Novelty — clean, genuinely new.** There is no Mathlib tactic that pushes
`Complex.re`/`Complex.im` through a symbolic expression tree. The status quo is precisely
the fragile `simp only [mul_re, ofReal_re, I_re, mul_im, …]` chain the docstring quotes,
which is what this replaces. Delivering it as `simproc`s (rather than a monolithic
`elab`) is the right call: it means `push_re_im [h] at h₂ ⊢` and interaction with other
simp lemmas come for free. Attribution to `NormNumI` is present and correct (line 28, 57).

**Applicability — strong.** The proposal cites 15+ occurrences of the exact chain and 47
`norm_exp` sites; the canonical goal `‖cexp (2πi n z)‖ = rexp (-2π n z.im)` is exercised
directly (Test lines 68–72). This is real, recurring work.

**Scope boundary (from adversarial probing).** Two natural neighbors fall outside the
claimed scope:
- `((z:ℂ) ^ (2:ℤ)).im` — integer powers (`zpow`) are not split (test B below).
- `cexp w` for a non-`ofReal` `w` is treated as an atom (correct, and `norm_exp_simp`
  still handles the *norm* via `Complex.norm_exp`, test C).

Neither is an implementation defect — the docstring only claims nat-`^` and `cexp` of a
real coercion. `zpow` of `z : ℍ` does arise in modular-forms work (`denom^(-k)`), so a
one-line `~q(@HPow.hPow ℂ ℤ ℂ _ $w $n)` arm (for literal `n`) would be a natural, cheap
extension. Low priority — flag as a documented limitation at minimum.

---

## 3. Findings by criterion

### Soundness — clean
`#print axioms` on representative outputs of both tactics yields exactly
`[propext, Classical.choice, Quot.sound]` (test appendix, axcheck1/axcheck2). The
proof terms are built from the `split_*` lemmas via `Qq` and checked by the kernel; no
`sorry`, `native_decide`, `Environment` writes, or new axioms. No finding.

### Completeness — clean
All fourteen author examples (`Test/PushReIm.lean`) pass at default heartbeats. Adversarial
in-scope goals (deeply nested products, `let`-bindings, nat powers up to `^20`,
`conj` of a product, division, subtraction of casts, `cexp (2:ℂ)`) all succeed
(appendix). No regressions or in-scope failures found.

### Documentation, Faithfulness & Referencing — very good, one nuance
Docstrings are exemplary: file-level `/-!` with the motivating chain, per-declaration
docs, `parse`'s return contract documented (the `isAtom` flag), and syntax-level docs
with `[…]`/`at` examples. Referencing to `NormNumI` is explicit.

- **(MINOR, faithfulness)** The Test file advertises that `push_re_im` "Fails (rather
  than silently succeeding) when there is nothing to push" (Test line 58). This holds
  when `simp only` makes no progress, but a *reflexive* goal `X = X` with an opaque atom
  (e.g. `(cexp w).re = (cexp w).re`) is closed by `simp`'s built-in reflexivity even
  though no real pushing happened (test D). This is harmless (the goal is true), but the
  "always fails when nothing to push" phrasing is slightly too strong. *Suggestion:* soften
  the comment to "fails when the goal is not closable and no `.re`/`.im` can be pushed".

### Error Messages — one finding
- **(MINOR)** On out-of-scope input the user sees the generic
  `` `simp` made no progress `` (test B, `zpow`). It does not say *what* was unsupported.
  Because `push_re_im` is a `macro` expanding to `simp only [pushRe, pushIm, …]`, the
  simprocs themselves are the only place a targeted message could be emitted, and they
  currently `return .continue` silently on atoms. *Suggestion:* either (a) accept the
  generic message but document "`push_re_im` only splits `nat`-powers; for `zpow` use …",
  or (b) if a friendlier message is wanted, wrap the macro body so that a no-progress
  `simp` is caught and re-thrown as `"push_re_im: no .re/.im projection could be
  simplified (note: integer powers and cexp of non-real arguments are not split)"`.

### Readability & Maintainability — one real finding
- **(MINOR, maintainability — highest-value fix)** The `macro_rules` duplicate the base
  simp-lemma list **four times**: `push_re_im` with and without `[…]` (lines 187–199),
  and `norm_exp_simp` with and without `[…]` (lines 211–228). The eleven cleanup lemmas
  (`mul_zero … neg_neg`) appear verbatim in all four; the `norm_exp_simp` norm-lemma block
  appears twice. A future edit must touch up to four sites in sync. *Suggestion:* mirror
  the PR's own established pattern — register a simp-set:
  ```lean
  register_simp_attr push_re_im_simps          -- in a PushReImAttr.lean
  attribute [push_re_im_simps] pushRe pushIm mul_zero zero_mul mul_one one_mul
    add_zero zero_add sub_zero zero_sub sub_self neg_zero neg_neg
  ```
  then each macro rule collapses to
  `simp only [push_re_im_simps $[, $ls]?] $[$loc]?; try ring_nf $[$loc]?`, and
  `norm_exp_simp` adds a second `norm_exp_simps` set for the norm lemmas. This removes all
  four copies and makes the tactic user-extensible via `@[push_re_im_simps]`, matching
  `pointwise`/`d_nf`/`slash_simp`.
- **(SUGGESTION, minor)** `parse` returns `(… × Bool)` but every recursive caller
  discards the `Bool` (`let (r, _) ← parse …`); only the two simprocs read it. This is a
  fine performance choice (computing `isAtom` inline is free), but the pervasive `_`
  pattern is noise. An alternative is to drop the `Bool` from `parse` and have each
  simproc test atomicity directly (`if a == q(Complex.re $w) && b == q(Complex.im $w)`),
  though the current form is defensible; leaving as-is is acceptable.
- **Positive:** `projArg?` (lines 144–154) correctly handles *both* the constant-application
  form `Complex.re w` and the primitive-projection form `.proj ``Complex 0 w` (via
  `whnfR`). This is exactly the `mdata`/projection robustness the skill looks for — nicely
  done.

### User-friendliness — good
`[extraLemmas]` and `location` are both supported and tested (`push_re_im [hF]`,
`push_re_im at h`). The `simproc` design means the tactic composes with any surrounding
`simp`. Names are accurate. No finding.

### Efficiency — clean (better than the baseline)
`norm_exp_simp` on the canonical `n, z` goal profiles at ~7.7 ms tactic execution vs
~30 ms for the hand-rolled `rw [norm_exp]; simp only […]; ring_nf` chain (appendix, test
G) — roughly **4× faster**. `push_re_im` on `w ^ 20` stays ~7 ms because `Expr` hash-consing
keeps the parsed real/imag parts shared (linear unique nodes) rather than materializing the
exponential expansion. The only theoretical risk is a *non-reflexive* goal on a very high
literal power forcing `ring_nf` to expand the shared tree, but no such goal is in scope.
No finding.

---

## 4. Adversarial test appendix

All run via `lake env lean` against `import SpherePacking.Tactic.PushReIm`. ✓ = behaved as
expected.

| # | Test | Expected | Actual |
|---|------|----------|--------|
| axcheck1 | `#print axioms` of `(2πI z).re = -(2π z.im)` proof | ≤ 3 std axioms | `[propext, Classical.choice, Quot.sound]` ✓ |
| axcheck2 | `#print axioms` of `‖cexp …‖ = rexp …` proof | ≤ 3 std axioms | `[propext, Classical.choice, Quot.sound]` ✓ |
| nested | `(((z+I)*(z-I)+I*z).re = 1 + z.re^2 - z.im - z.im^2` | close | closed ✓ (my first hand-computed RHS omitted the `+1`; tactic was right) |
| let | `(let w := (z:ℂ); w*I).re = -z.im` | close | closed ✓ |
| div | `((I:ℂ)/2).im = 1/2` | close | closed ✓ |
| A | `(w^3).im = 3*w.re^2*w.im - w.im^3` (symbolic atom, nat pow) | close | closed ✓ |
| B | `((z:ℂ)^(2:ℤ)).im = 2*z.re*z.im` (**zpow**) | fail (out of scope) | `` `simp` made no progress `` ✓ (generic msg → MINOR) |
| C | `‖cexp (2:ℂ)‖ = rexp 2` (cexp of numeric, not `ofReal`) | close | closed ✓ (norm rewritten, `2.re = 2`) |
| D | `(cexp w).re = (cexp w).re` (reflexive, atom) | — | closed by simp reflexivity ✓ (→ faithfulness nuance) |
| E | `w.re = 1` with `fail_if_success push_re_im` | tactic fails | fails ✓ (documented no-progress path) |
| F | `(I*(z:ℂ)).re + z.im = 0` | close | closed ✓ |
| G | timing: `norm_exp_simp` vs manual chain on `n,z` goal | comparable | 7.7 ms vs 30 ms — **faster** ✓ |
| pow20 | `(w^20).re = (w^20).re` timing | not blow up | 7.4 ms ✓ (Expr sharing) |

Boundary probes that turned out to be *my* test-design errors (all revealed the tactic is
*more* capable than assumed, none are tactic bugs): `w^5`, `zpow`, and `cexp w` inside
reflexive `X = X` goals were closed by `simp`/`ring_nf` reflexivity rather than failing.
