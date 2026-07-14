# Tactic Proposals for Sphere-Packing-Lean

Suggestions for new custom tactics (and tactic-adjacent infrastructure) to improve code quality,
based on a read-through of the codebase at commit `d80a24c` (2026-07-06): 87 `.lean` files,
~18.5k lines. All occurrence counts below come from grepping that commit.

**Context.** The repo already ships two custom tactics in `SpherePacking/Tactic/` —
`tendsto_cont` (compositional limit proving via `fun_prop`) and `norm_num_i` (normalization of
complex-number expressions to `⟨re, im⟩` form) — with tests under `Tactic/Test/`. The proposals
below follow the same conventions. With the post-Gauss refactoring effort focused on golfing and
maintainability, the ranking criterion here is (impact ÷ implementation effort): how many existing
proof sites a tactic compresses, and how much it hardens the code against Mathlib churn.

---

## 1. `push_re_im` — symbolic re/im/norm computation (extension of NormNumI)

**Evidence.** The most repeated fragile pattern in the repo is the "compute the real part of a
complex product by hand" simp chain:

```lean
simp only [norm_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero,
  sub_zero, Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one,
  sub_self, coe_re, coe_im, zero_sub, Real.exp_lt_one_iff, Left.neg_neg_iff]
```

This chain (or a near-variant) appears 15+ times (`ModularForms/exp_lems.lean`,
`ModularForms/ResToImagAxis.lean`, `ModularForms/EisensteinAsymptotics.lean`, the JacobiTheta
files), and there are 47 `norm_exp` sites overall, most of which want the same conclusion:
`‖cexp (2 * π * I * n * z)‖ = rexp (-2 * π * n * z.im)`. Each occurrence is a maintenance
liability — the lemma lists break whenever Mathlib renames or re-prioritizes simp lemmas.

**Design.** `NormNumI` already recursively splits ℂ-expressions into `⟨a, b⟩` form, but only over
numeric atoms. Extend the splitter to *symbolic* atoms:

- `(↑r : ℂ)` for `r : ℝ` ↦ `⟨r, 0⟩`;
- `(↑z : ℂ)` for `z : ℍ` ↦ `⟨z.re, z.im⟩` (via `coe_re`/`coe_im`);
- `I` ↦ `⟨0, 1⟩` (already present);
- casts of `ℕ`, `ℕ+`, `ℤ` ↦ `⟨↑n, 0⟩`;
- unknown atoms `w : ℂ` ↦ `⟨w.re, w.im⟩` as a fallback.

The result is a `push_re_im` tactic that proves goals like
`(2 * ↑π * I * ↑n * ↑z).re = -(2 * π * n * z.im)` in one call, and a thin derived tactic
`norm_exp_simp` that rewrites `‖cexp w‖` to `rexp w.re` and then runs `push_re_im` on the
exponent. Real/imaginary parts stay in normalized `ring_nf` form, so `positivity`/`linarith` can
take over directly.

**Payoff.** Kills every occurrence of the chain above; makes the eight structurally identical
`ResToImagAxis.Real.{neg, add, mul, smul, pow, inv, div, const}` closure proofs one-liners;
robust against Mathlib simp-set churn. Also a clean Mathlib upstreaming candidate.

**Effort.** Medium — the recursive infrastructure exists in `NormNumI.lean`; the work is adding
atom cases and a norm-of-exp wrapper, plus a test file.

---

## 2. `pointwise` — extensionality + Pi-apply normalization

**Evidence.** 295 occurrences of `Pi.{mul, add, sub, smul, pow, neg, div}_apply` across the repo,
and ~30 instances of the exact idiom

```lean
ext z
simp [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul]
ring
```

e.g. `MLDE_F`, `MLDE_G`, `serre_D_10_G`, `Δ_fun_theta` in `ModularForms/FG.lean`, plus many sites
in `Derivative.lean` and `E2.lean`.

**Design.** A registered simp attribute plus a three-line macro:

```lean
register_simp_attr pointwise_simps
-- tag: Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.pow_apply,
--      Pi.neg_apply, Pi.div_apply, Pi.one_apply, Pi.zero_apply, smul_eq_mul,
--      Function.comp_apply, Complex.real_smul, ...

macro "pointwise" : tactic =>
  `(tactic| (ext z; simp only [pointwise_simps]; try ring))
```

Variants worth having: `pointwise at h`, and `pointwise using field_simp` for goals with
denominators (e.g. `logderiv_mul_eq`-style lemmas).

**Payoff.** Immediate golf across ~30 proofs; new pointwise identities become one-word proofs.

**Effort.** Low — an afternoon including the `Tactic/Test/` file. Recommended as the first thing
to build.

---

## 3. `d_nf` — normalizer (eventually decision procedure) for the quasimodular differential ring

**Evidence.** The `FG.lean` / `RamanujanIdentities.lean` layer computes in the differential ring
(ℂ[E₂, E₄, E₆], D) by hand. The recurring proof shape is:

```lean
simp (disch := fun_prop) only [serre_D_eq, D_add, D_sub, D_mul, D_sq, D_cube,
  ramanujan_E₂, ramanujan_E₄, ramanujan_E₆]
ext z
simp [Pi.mul_apply, ...]
field_simp (disch := norm_num)
ring
```

(see `F_aux`, `MLDE_F`, `MLDE_G`, `serre_D_10_F/G`). Separately, the `D_add` / `D_sub` / `D_smul`
lemmas in `Derivative.lean` (lines ~96–140) are 15-line calc blocks repeating the same
"linearity of `deriv` through `∘ ofComplex`" argument.

**Design — stage 1 (cheap).** A `@[d_simps]` attribute collecting the Leibniz/linearity lemmas for
`D` and `serre_D` together with the Ramanujan identities, and a macro

```lean
macro "d_nf" : tactic =>
  `(tactic| (simp (disch := fun_prop) only [d_simps]; pointwise; try field_simp; try ring))
```

so every MLDE-style verification becomes one word, with holomorphy side goals discharged by
`fun_prop` (all the `MDiff` closure lemmas are already `@[fun_prop]`-tagged).

**Design — stage 2 (ambitious).** By Kaneko–Zagier, ℂ[E₂, E₄, E₆] is a *free* polynomial algebra,
and `D` acts on it by the Ramanujan system. Hence any D/`serre_D` identity among quasimodular
forms is decidable: reflect both sides into `MvPolynomial (Fin 3) ℂ` (variables ↦ E₂, E₄, E₆),
apply the formal derivation

```
D E₂ = (E₂² − E₄)/12,   D E₄ = (E₂E₄ − E₆)/3,   D E₆ = (E₂E₆ − E₄²)/2,
```

and compare `ring_nf` normal forms of the reflected polynomials. Soundness needs one semantic
lemma (evaluation at E₂, E₄, E₆ commutes with the derivation — exactly the Ramanujan identities)
plus algebraic independence for completeness of the *negative* direction (not needed if the tactic
only claims to prove true identities). This would be a genuine `ring`-analogue for differential
polynomial rings — nothing like it exists in Mathlib — and it directly serves the remaining
`FG_ineq_*`-to-linear-constraints work.

**Effort.** Stage 1 low; stage 2 a serious but well-scoped metaprogramming project.

---

## 4. `res_simp` — conditional simp for `resToImagAxis` instead of dite-unfolding

**Evidence.** ~49 sites unfold the definition manually:

```lean
simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
```

(15 of them are this *exact* line). Every use site re-threads the positivity hypothesis into the
`dite` by hand.

**Design.** One conditional simp lemma plus a discharging macro:

```lean
@[simp] lemma resToImagAxis_apply_of_pos (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    F.resToImagAxis t = F ⟨I * t, by simp [ht]⟩ := by
  simp [Function.resToImagAxis, ResToImagAxis, ht]

macro "res_simp" : tactic =>
  `(tactic| simp (disch := positivity) only [resToImagAxis_apply_of_pos,
      Function.resToImagAxis_apply, Function.resToImagAxis_eq_resToImagAxis])
```

The `positivity` discharger makes the rewrite fire even when `0 < t` is only *derivable* (from
`t ∈ Ioi 0`, `1 ≤ t`, `t₀ ≤ t` with `0 < t₀`, ...), which is the common situation in the
asymptotics files. Depends on proposal 5 for full effectiveness.

**Effort.** Low.

---

## 5. `positivity` extension for upper-half-plane atoms

**Evidence.** ~41 manual `have : 0 < ... .im` hypotheses and ~45 explicit constructions of points
`⟨I * t, by simp [ht]⟩ : ℍ` scattered through the ModularForms and MagicFunction directories. The
recently upstreamed `im_pnat_div_pos` shows this lemma family is wanted in Mathlib too.

**Design.** Extensions against the `Mathlib.Tactic.Positivity.Core` API handling:

- `z.im` for `z : ℍ` (close with `UpperHalfPlane.im_pos`);
- `(I * (↑t : ℂ)).im` and `((↑t : ℂ) * I).im` given `0 < t` (recursive positivity call on `t`);
- `(γ • z).im` for `γ` in `SL(2, ℤ)` / `GL(2, ℝ)⁺` (via `UpperHalfPlane.im_smul_eq_div_normSq`).

**Payoff.** Point constructions become uniform `⟨_, by positivity⟩`; powers the dischargers in
proposals 4 and 6; upstreamable in the spirit of `ForMathlib/`.

**Effort.** Low–medium (~100 lines plus tests).

---

## 6. Estimate-layer plumbing: `@[bound]` curation + `eventually_im_infty` intro macro

**Evidence.** 229 `atImInfty` / `IsBigO` sites. The proofs share a rigid shape — e.g.
`E₂_sub_one_isBigO_exp` in `EisensteinAsymptotics.lean`:

```lean
rw [Asymptotics.isBigO_iff]
refine ⟨192, Filter.eventually_atImInfty.mpr ⟨1, fun z hz => ?_⟩⟩
...
have hexp_lt_half : Real.exp (-2 * π) < 1 / 2 := by
  have : 1 < 2 * π := by nlinarith [pi_gt_three]
  ...
```

followed by hand-rolled inequality chains (`nlinarith [pi_gt_three]`, exp-monotonicity, geometric
bounds). Mathlib's `bound` tactic is used exactly once in the whole repo — underexploited rather
than inapplicable.

**Design.** Three cheap pieces:

1. Tag the repo's workhorse inequalities with `@[bound]`: `norm_exp_two_pi_I_le_exp_neg_two_pi`,
   `exp_upperHalfPlane_lt_one`, the `‖q‖ / (1 - ‖q‖)^3` bounds, `Real.exp_lt_one_iff`-style facts,
   so `bound` closes the leaf goals of estimate chains.
2. A filter-intro macro: `eventually_im_infty A with z hz` expanding to
   `refine Filter.eventually_atImInfty.mpr ⟨A, fun z hz => ?_⟩`.
3. Optionally, an `isbigo_exp_decay` tactic reducing `f =O[atImInfty] fun τ => rexp (-c * τ.im)`
   to the explicit `∃ C A, ∀ z, A ≤ z.im → ‖f z‖ ≤ C * rexp (-c * z.im)` form in one step.

**Effort.** Low; mostly attribute curation. High reuse across the asymptotics files.

---

## 7. `summability` — register `Summable` with `fun_prop` (or an aesop rule set)

**Evidence.** 196 `Summable` occurrences, with highly stereotyped side goals:
`Summable fun n => ↑n ^ k * q ^ n` for `‖q‖ < 1`, closure under `add` / `mul_left` / `const`,
and ℕ ↔ ℕ+ ↔ ℤ reindexing (the purpose of `tendstolems.lean`).

**Design.** The repo already demonstrates the key trick: `ResToImagAxis.Real` is a *nonstandard
predicate registered with `fun_prop`*, with compositional closure lemmas tagged `@[fun_prop]`.
`Summable f` has exactly the function-property shape `fun_prop` wants. Tag `Summable.add`,
`Summable.mul_left`, `summable_geometric_of_norm_lt_one`,
`summable_pow_mul_geometric_of_norm_lt_one`, `Summable.comp_injective`, and the repo's reindexing
lemmas, and expose

```lean
macro "summability" : tactic => `(tactic| fun_prop)
```

(or, fallback design, an aesop rule set à la `continuity` / `measurability`). The `‖q‖ < 1` side
conditions route to `norm_exp_simp` + `positivity` from proposals 1 and 5.

**Effort.** Low–medium; mostly lemma tagging and testing which goal shapes `fun_prop` transitions
handle.

---

## 8. Fin-vector/matrix evaluator for `E8.lean`

**Evidence.** `Basic/E8.lean` proves `E8Inverse_mul_E8Matrix_rat` by `decide +kernel` (slow,
ℚ-specific), contains eight consecutive clones of

```lean
simpa [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse] using this
```

and several `norm_num [Fin.forall_fin_succ, E8Matrix]` calls.

**Design.** A `norm_num` extension (or simproc) evaluating `Matrix.vecMul`, `Matrix.mulVec`,
`dotProduct`, `Matrix.det` of triangular literals, and `∑ i : Fin n` over `![...]` / `!![...]`
literals by structural recursion through the `Matrix.cons_val` lemmas, over any commutative ring.
A cheaper interim variant is a `fin_vec_simp` macro bundling the standard unfolding set with
`norm_num`.

**Payoff.** Faster and more robust than `decide +kernel`; immune to Mathlib renaming
`Fin.sum_univ_eight`-style lemmas. Becomes important if the dimension-24 material (Leech lattice,
`Fin 24`) lands in this repo — kernel `decide` will not survive 24×24.

**Effort.** Medium.

---

## 9. `slash_simp` — slash-action unfolding with automatic `denom` discharge

**Evidence.** `SlashActionAuxil.lean` is 310 lines; 60 `SlashInvariantForm` references repo-wide;
`have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z` is re-derived at each use site
(`Derivative.lean` lines 494, 513, 548, 584, ...).

**Design.** A `@[slash_simps]` set (`ModularForm.slash_def`, `modular_slash_S_apply`,
`modular_slash_T_apply`, `denom` arithmetic, `σ`-action lemmas) wrapped in a macro that runs
`field_simp` with a discharger firing `UpperHalfPlane.denom_ne_zero` (and `zpow_ne_zero` over it)
automatically. Tightens `ResToImagAxis.SlashActionS` and the transformation-law material in
`PhiTransform.lean` / `SerreDerivativeSlash.lean`.

**Effort.** Low–medium.

---

## Infrastructure notes

**Module system.** The repo is on Lean v4.30.0 with the module system; tactics must follow the
`TendstoCont` pattern (`public meta import` for tactic dependencies, `meta` sections for
elaboration code, paired test file in `SpherePacking/Tactic/Test/`).

**Upstreaming.** Proposals 1, 5, and 7 are natural Mathlib candidates in the spirit of
`ForMathlib/` — upstreaming shares the maintenance burden and benefits the broader modular-forms
formalization effort.

**Suggested order of attack.**

| Priority | Proposal | Effort | Sites affected |
|---|---|---|---|
| 1 | `pointwise` (#2) | low | ~300 |
| 2 | `res_simp` + ℍ `positivity` ext (#4, #5) | low | ~90 |
| 3 | `push_re_im` / `norm_exp_simp` (#1) | medium | ~60 |
| 4 | `@[bound]` curation + `eventually_im_infty` (#6) | low | ~230 (leaf goals) |
| 5 | `summability` (#7) | low–medium | ~200 (side goals) |
| 6 | `d_nf` stage 1 (#3) | low | ~15 large proofs |
| 7 | `slash_simp` (#9) | low–medium | ~60 |
| 8 | Fin-vector evaluator (#8) | medium | E8.lean (+ dim 24) |
| 9 | `d_nf` stage 2 (#3) | high | MLDE layer, future FG work |

The first two rows are achievable in a day or two each and would already visibly golf `FG.lean`,
`ResToImagAxis.lean`, and the asymptotics files; `d_nf` stage 2 is the research-grade project — a
`ring` for the Kaneko–Zagier differential ring — with the highest ceiling.
