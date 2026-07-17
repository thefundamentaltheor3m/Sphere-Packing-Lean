# Metaprogram review — `fin_vec_simp`

**Target:** `SpherePacking/Tactic/FinVecSimp.lean` — the `fin_vec_simp` macro
(`norm_num +decide [≈22 Matrix/Fin unfolding lemmas]`).
**Reviewer method:** metaprogram-review skill. Build green; adversarial tests via
`lake env lean`; axioms (incl. the `+decide` soundness question) empirically verified.

---

## 1. Summary

**Specification** (*authored*, docstring lines 13–29): evaluate goals about `Fin`-indexed
vector/matrix literals (`![…]`, `!![…]`) — matrix products, `vecMul`/`mulVec`/`dotProduct`,
entrywise equalities (via `← Matrix.ext_iff`/`funext_iff`/`Fin.forall_fin_succ`), and
`∑ i : Fin n` — by bundling the standard `Matrix.cons_val`/`vecMul_cons`/`Fin.sum_univ_succ`
recursion lemmas into one `norm_num +decide` call. Works over any commutative ring with
numeric literals, including `ℝ`/`ℂ`/abstract fields where `decide` alone is unavailable,
and is immune to `Fin.sum_univ_eight`-style renamings. `fin_vec_simp [foo] at h ⊢`
supported. For fully-literal `ℚ`/`ℤ` goals `decide +kernel` may still be preferable
(proof terms grow large).

**Overall:** Sound and effective within scope. The key soundness question — does `+decide`
escape the kernel? — is answered **no**: it uses the kernel `decide` (verified: outputs
carry only the standard three axioms, no `Lean.ofReduceBool`). All in-scope shapes pass,
including the abstract-field case, and false goals are safely left as `⊢ False` (never
proved). Two quality findings: heavy lemma-list duplication, and partial adoption (the E8
boilerplate it was designed to kill is mostly still present).

**Top findings:**
1. **(MINOR, maintainability)** The ≈22-lemma unfolding list is duplicated verbatim across
   the two `macro_rules` (≈44 lines). Register a `@[fin_vec_simps]` set (as the PR does for
   `pointwise`/`d_nf`/`slash_simp`) and collapse both rules to
   `norm_num +decide [fin_vec_simps $[, $ls]?] $[$loc]?`.
2. **(SUGGESTION, applicability)** Only 2 of E8.lean's boilerplate sites adopted it;
   `decide +kernel` (line 339) and the ~8 `simpa [vecMul_eq_sum, Fin.sum_univ_eight, …]`
   clones (lines 407–422) — the proposal's headline target — remain. Finish the migration
   to validate the tactic (and retire the fragile `Fin.sum_univ_eight` lemmas).

---

## 2. Specification assessment

**Specificity — clean.** One coherent job: reduce `Fin`-literal matrix/vector goals to
evaluated entries. The several operations (product, `vecMul`, `dotProduct`, sums, entrywise
eq) are all the *same* underlying `cons_val`-recursion, so this is dependent composition,
not a bundle.

**Necessity & Novelty — a justified interim macro.** It genuinely beats the alternatives on
two axes the docstring names: it works over `ℝ`/`ℂ`/abstract fields (where `decide` is
unavailable — verified) and is robust to `Fin.sum_univ_eight`-style renames (unlike the
hand-rolled `simp` sets it replaces). The proposal's more ambitious form (a `norm_num`
extension / simproc over `Matrix.vecMul` etc.) is *not* built; this is the "cheaper interim
variant" the proposal itself described, which is a reasonable scope choice. Necessity is
adequate; the ceiling (a real simproc) is noted for the future (esp. dim-24 Leech, where
`decide +kernel` will not scale).

**Applicability — real but under-realized.** 2 call sites (`E8.lean:288, 337`). The
proposal's motivating target — the eight `simpa [… vecMul_eq_sum, Fin.sum_univ_eight …]`
clones and the ℚ-specific `decide +kernel` — is largely *not* migrated (see #2). The tactic
works; it just has not yet displaced the boilerplate it was written for.

---

## 3. Findings by criterion

### Soundness — clean (the `+decide` is fine)
This was the flagged risk. `#print axioms` on both a `+decide`-backed ℚ product
(`!![0,1;1,0]²=1`) and a `norm_num`-backed ℝ cast goal =
`[propext, Classical.choice, Quot.sound]` — **no `Lean.ofReduceBool`**, confirming this is
kernel `decide` (which the kernel re-checks), not `native_decide`. False goals are reduced
to `⊢ False` and **left open**, never closed (verified: `!![1,2;3,4]*1 = !![1,2;3,5]` yields
`unsolved goals ⊢ False`, not a proof). No finding.

### Completeness — clean within scope
All author examples plus adversarial probes pass: ℚ/ℤ/ℂ literal products, `vecMul`/`mulVec`
with symbolic entries, `dotProduct`, `∑ i : Fin 4`, entrywise `.map`/`Rat.cast` equality,
and — notably — the **abstract field** case `{R : Type*} [Field R]` (where `decide` cannot
run and `norm_num` carries it). An 8×8 identity product closes in ~10 ms. No in-scope
failures.

### Documentation, Faithfulness & Referencing — clean
The docstring is honest and precise: it states the operation set, the abstract-field
support, the renaming-robustness, and — importantly — the `decide +kernel`-is-better-for-
literal-`ℚ`/`ℤ` tradeoff with the "proof terms grow large" caveat. Implementation matches.
No finding.

### Error Messages / Failure behavior — acceptable
On a false or unfinishable goal the user gets the residual (`⊢ False`, or a partially
reduced entrywise goal) rather than a bespoke message — standard `norm_num`/`simp`
behavior, and `⊢ False` is in fact a useful signal that the identity is false. No action
needed.

### Readability & Maintainability — one real finding
- **(MINOR)** The ≈22-lemma list (`← Matrix.ext_iff, funext_iff, Fin.forall_fin_succ, …,
  smul_eq_mul`) is written out **twice** (lines 42–52 and 54–64), differing only by the
  trailing `$ls,*`. This is the largest verbatim duplication in the PR's tactics. Extract a
  `register_simp_attr fin_vec_simps` (in a `FinVecSimpAttr.lean`, matching the PR's own
  convention) and reduce both rules to one `norm_num +decide [fin_vec_simps $[, $ls]?]`.
  Bonus: users could then extend the recipe with `@[fin_vec_simps]`.

### User-friendliness — good
`[extraLemmas]` (used as `fin_vec_simp [E8Matrix]` / `[E8Inverse]` to unfold the definition
in-pass) and `at`-location are supported and tested. Name is apt. No finding.

### Efficiency — clean in scope, with a documented ceiling
Tested cases (incl. 8×8 identity) are fast. The `+decide` path can produce large proof
terms for fully-literal high-dimension matrices; the docstring already steers such cases to
`decide +kernel`. For the eventual dim-24 material, the promised simproc would be the real
answer. No finding beyond what the docstring already discloses.

---

## 4. Adversarial test appendix

`import SpherePacking.Tactic.FinVecSimp`. ✓ = as expected.

| # | Test | Expected | Actual |
|---|------|----------|--------|
| axcheck | `#print axioms` of `+decide` ℚ product | ≤ 3 std, no native | `[propext, Classical.choice, Quot.sound]` ✓ |
| axcheck_real | `#print axioms` of ℝ `.map Rat.cast` eq | ≤ 3 std | `[propext, Classical.choice, Quot.sound]` ✓ |
| in-1 | `!![1,2;3,4] * 1 = !![1,2;3,4]` | close | closed ✓ |
| in-2 | `![a,b] ᵥ* !![0,1;1,0] = ![b,a]` (symbolic) | close | closed ✓ |
| in-3 | `∑ i:Fin 4, ![1,2,3,4] i = 10` | close | closed ✓ |
| field | `{R}[Field R] ![a,b] ᵥ* 1 = ![a,b]` (no decide) | close | closed ✓ (norm_num path) |
| complex | `!![1,0;0,1]² = 1` over ℂ | close | closed ✓ |
| false | `!![1,2;3,4]*1 = !![1,2;3,5]` | not proved | `⊢ False` left open ✓ (sound) |
| 8×8 | `(1:Matrix (Fin 8)(Fin 8) ℚ)*1 = 1` | close, fast | ~10 ms ✓ |

(The initial `axcheck_real` failure was my own `ℝ`-vs-`ℚ` type annotation error, corrected
above.)
