# AnotherIntegral/A vs AnotherIntegral/B — Structural Analysis & Refactor Plan

## Scope and measured sizes

Root: `SpherePacking/MagicFunction/g/CohnElkies/AnotherIntegral/`
(subtree total ~8880 lines — somewhat more than the 4350 mentioned in the task; the user
count appears to have missed `Parametric.lean`, `Continuation.lean`, `Representation.lean`,
and the `A/IntegralLemmas.lean`/`A/Core.lean` helpers, but these are all part of the
parallel machinery.)

| Side | File | Lines |
|---|---|---|
| shared | `Common.lean` | 131 |
| shared | `ContinuationCommon.lean` | 47 |
| shared | `ContinuationGeneric.lean` | 70 |
| A | `A/Core.lean` | 41 |
| A | `A/IntegralLemmas.lean` | 146 |
| A | `A/Parametric.lean` | 378 |
| A | `A/Continuation.lean` | 185 |
| A | `A/Representation.lean` | 388 |
| A | `A/APrimeExtension.lean` | 936 |
| A | `A/Cancellation/Integrability.lean` | 864 |
| A | `A/Cancellation/ImagAxis.lean` | 596 |
| A | `A/Cancellation/LargeImagApprox.lean` | 547 |
| B | `B/AnotherIntegral.lean` | 223 |
| B | `B/Parametric.lean` | 229 |
| B | `B/Continuation.lean` | 170 |
| B | `B/Cancellation.lean` | 356 |
| B | `B/PsiICancellation.lean` | 628 |
| B | `B/BPrimeExtension.lean` | 677 |
| B | `B/ThetaAxis/HExpansions.lean` | 930 |
| B | `B/ThetaAxis/InvH2Sq.lean` | 739 |
| B | `B/ThetaAxis/QExpansion.lean` | 600 |
| | **Total** | **8881** |

"Assemble + reduce" files on both sides (everything except the **asymptotics**,
`A/Cancellation/*` and `B/ThetaAxis/*`) come to **~4108 lines** (A: 2074, B: 2034).
The remaining ~4770 lines are in the asymptotic machinery for `φ₀/φ₂/φ₄` (A side)
and `Θ₂/Θ₃/Θ₄/H₂/H₃/H₄/ψI` (B side).

## 1. Mathematical structure (what both sides actually prove)

Both branches are proving the same abstract skeleton:

1. Define an integrand `<x>AnotherIntegrand : ℝ → ℝ → ℂ` and its integral on `(0,∞)`
   (`aAnotherIntegrand`, `bAnotherIntegrand`).
2. Define a complex-parameter variant `<x>AnotherIntegrandC : ℂ → ℝ → ℂ` and integral
   `<x>AnotherIntegralC : ℂ → ℂ`, show it is `AnalyticOnNhd ℂ · rightHalfPlane`
   (`Parametric.lean` on each side).
3. Build an analytic extension of the real function (`aPrimeC`/`bPrimeC`, in
   `APrimeExtension.lean`/`BPrimeExtension.lean`).
4. Assemble the RHS analytically via `<x>AnotherRHS : ℂ → ℂ` and conclude by
   analytic continuation from the `u > 2` identity (`Continuation.lean` on each side,
   plus the shared `ContinuationGeneric.lean` wrapper).
5. Derive the `u > 2` identity from the Laplace representation by subtracting out
   the explicit "correction" terms (`Representation.lean` for A,
   `AnotherIntegral.lean` for B).
6. Prove integrability of the integrand for all `u > 0`. On A this is split into
   three files under `A/Cancellation/`. On B it is split into one Cancellation file
   plus the `PsiICancellation.lean` + `ThetaAxis/*` chain.

The "3–4 atomic substitutions" the user mentions are exactly:

| Role | A side | B side |
|---|---|---|
| algebraic bracket | `aAnotherBase t` | `bAnotherBase t` |
| integrand | `aAnotherIntegrand u t` | `bAnotherIntegrand u t` |
| complex integrand | `aAnotherIntegrandC u t` | `bAnotherIntegrandC u t` |
| complex integral | `aAnotherIntegralC u` | `bAnotherIntegralC u` |
| analytic extension | `aPrimeC u` (sum of `Iᵢ'C`) | `bPrimeC u` (sum of `Jᵢ'C`) |
| complex RHS | `aAnotherRHS u` | `bAnotherRHS u` |
| eigenvalue sign | `4 * I * sin²(πu/2)` | `-4 * I * sin²(πu/2)` |
| pole term | `36/(π³(u-2))` | `1/(π(u-2))` |
| sub-polynomial terms | `-8640/(π³u²) + 18144/(π³u)` | `144/(π u)` |
| modular obj. on imag. axis | `φ₀''(I/t)`, `φ₂'(it)`, `φ₄'(it)` | `ψI'(I·t)` (→ `H_j`, `Θ_j`) |

From a Lean-engineering standpoint, items 1–4 above are **almost identical**
modulo these substitutions, while items 5–6 are where the genuine mathematical
differences live (the cancellation identities and asymptotic analysis are truly
different because the modular forms are different).

## 2. File-by-file parallelism audit

### 2.1 `A/Core.lean` (41) vs B (in-lined in `B/AnotherIntegral.lean`)

A keeps the real integrand in its own module to break import cycles; B does not,
because B's complex development doesn't import the real definition. The A/Core.lean
content is just:

```
def aAnotherIntegrand (u t : ℝ) : ℂ :=
  (bracket(t) - 36/π² * exp(2πt) + 8640/π · t - 18144/π²) * exp(-π u t)
def aAnotherIntegral (u : ℝ) : ℂ := ∫ t in Ioi 0, aAnotherIntegrand u t
```

Asymmetric but small. ~20 lines of shared skeleton could replace both definitions.

### 2.2 `A/IntegralLemmas.lean` (146) vs `A/IntegralLemmas.lean` imported by B

`A/IntegralLemmas.lean` provides six lemmas in `(f, Cf, integrability)` triplets:
- `integral_exp_neg_pi_mul_Ioi_complex` + `integrableOn_exp_neg_pi_mul_Ioi_complex`
- `integral_mul_exp_neg_pi_mul_Ioi_complex` + `integrableOn_mul_exp_neg_pi_mul_Ioi_complex`
- `integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex` + `integrableOn_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex`

`B/AnotherIntegral.lean` imports and reuses these directly (see
`B/AnotherIntegral.lean:4`: `public import ... A.IntegralLemmas`). Already
deduplicated — no further savings possible here without promoting the file to
the shared root.

### 2.3 `A/Parametric.lean` (378) vs `B/Parametric.lean` (229)

**Same theorem; different proof strategy.** Both establish:

- `xAnotherIntegrandC_ofReal` / `xAnotherIntegralC_ofReal`: restriction to reals
- `xAnotherIntegralC_analyticOnNhd`: analyticity on `rightHalfPlane`

by the same `hasDerivAt_integral_of_dominated_loc_of_deriv_le` pattern.

A builds an explicit pointwise dominating function using an `hmul_exp` lemma
for the "trade" `t * exp(-c*t) ≤ (2/c) * exp(-(c/2)*t)`; B factors the
integrand as `base(t) * ratio(x,t)` and uses `bAnotherBase_integrable_exp`
(from the B/Cancellation.lean) directly. B's approach is shorter because B
already has the weighted integrability lemma as a theorem, whereas A
re-derives domination inline.

Concrete parallelism: lines A:99–374 closely mirror lines B:63–225, both
roughly 270 lines. Both set up:
- a `base` bound,
- a `ratio`/`exp` decay factor,
- `hF_int`, `hF_meas`, `hF'_meas`,
- a `bound` dominating function + `h_bound`, `h_diff`,
- finally `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

**Refactor potential**: expose a single helper
`analyticOnNhd_parametric_integrand` taking:
- `base : ℝ → ℂ`, `(base_continuous : ContinuousOn base (Ioi 0))`,
- `base_integrable_exp : ∀ u > 0, IntegrableOn (base · exp(-π u t))  (Ioi 0)`,
- `base_integrable_mul_exp : ∀ u > 0, IntegrableOn (t · base · exp(-π u t)) (Ioi 0)`,

and produce `AnalyticOnNhd ℂ (fun u : ℂ => ∫ t in Ioi 0, base t * exp(-π u t)) rightHalfPlane`.

Estimated savings: **~350–400 lines** (keep only the integrability proofs per
side; the analyticity machinery collapses to one or two `simpa` calls).
**Confidence: HIGH** — the B side already phrases things in terms of
`bAnotherBase_integrable_*` lemmas, so the abstraction is already visible.

### 2.4 `A/Continuation.lean` (185) vs `B/Continuation.lean` (170)

These are **near clones**. The shared file `ContinuationGeneric.lean:40` already
abstracts the core pattern as `analytic_continuation_of_gt2`. Each of A/B then:

- defines `<x>AnotherRHS : ℂ → ℂ` (A:45–51, B:45–48);
- proves `<x>AnotherRHS_analyticOnNhd` (A:53–118, B:50–102 — both routine
  `analyticOnNhd_const.div/mul/add` chains, only the pole terms differ);
- proves `exists_<x>'_analytic_extension` producing `<x>PrimeC` (A:127–134, B:117–129);
- a `public theorem <x>Radial_eq_another_integral_analytic_continuation_of_gt2`
  wrapper (A:147–181, B:142–166) that is essentially 3 lines of genuine code
  plus a `let rhsR := …` to assemble the real RHS.

Total shared scaffolding is about **170 lines** out of the combined 355,
differing only in the specific fractions that appear.

**Refactor potential**: promote `<x>AnotherRHS` into a functor taking the
pole-term function `poleC : ℂ → ℂ` and its analyticity/`ofReal` witnesses,
then derive `xAnotherRHS_analyticOnNhd` and the continuation wrapper from a
shared lemma. Save **~120 lines across the two files**. **Confidence: HIGH.**

Note: `analytic_continuation_of_gt2` already exists in
`ContinuationGeneric.lean:40`. It covers the identity-theorem step but still
asks each side for `h_extension`, `h_rhs_analytic`, `h_rhs_ofReal` — i.e. all
the scaffolding for the RHS. A second-layer wrapper,
`another_integral_continuation_pkg`, could take just `value`, `rhsR`, and a
decomposition `rhsR r = prefactor(r) * (pole(r) + integral(r))` along with
the `hu > 2` identity, producing the analytic continuation directly. This is
the key deduplication lever.

### 2.5 `A/Representation.lean` (388) vs `B/AnotherIntegral.lean` (223)

Both prove "the `u > 2` identity via Laplace subtraction". The A side is longer
because it has a heavy `corrIntegral_eval` lemma (A:28–200, ~172 lines) that
evaluates
`∫ (c36·exp(2πt) - c8640·t + c18144) * exp(-πut)`
by expanding into three Laplace integrals. B's correction is simpler — only
two terms `(144 + exp(2πt))` — so it's only ~40 lines of inlined evaluation
(B:141–180).

Additionally, A has an `assemble_another_integral` helper (A:202–218) that B
inlines with `ring_nf` at B:182–185.

The two are **structurally identical**. One could share a
`corrIntegral_sum_eval` lemma that, given `n ∈ {0,1,2,3}` real constants and
a family of integrability + integral-evaluation premises, evaluates
`∫ (Σᵢ cᵢ · tⁱ · exp(kᵢπt)) * exp(-πut)` to a rational function of `u, π`.
With three pieces precomputed, both A (3 pieces) and B (2 pieces) become
three-line specializations.

**Refactor potential**: **~150 lines savings** (most of A's `corrIntegral_eval`
collapses; B stays roughly the same size but uses the shared lemma).
**Confidence: MEDIUM** — the algebraic manipulation is easy to get wrong
when generalizing `field_simp [...]` steps across different denominator
shapes.

### 2.6 `A/APrimeExtension.lean` (936) vs `B/BPrimeExtension.lean` (677) — the giants

Both files build `<x>PrimeC = I₁'C + I₂'C + I₃'C + I₄'C + I₅'C + I₆'C` (A) or
`J₁'C + ... + J₆'C` (B), prove `(<x>PrimeC_ofReal)`, and prove
`(<x>PrimeC_analyticOnNhd rightHalfPlane)`.

Structural shape (from Grep):

| Step | A (for `Iᵢ'C`, `i=1..6`) | B (for `Jᵢ'C`, `i=1..6`) |
|---|---|---|
| Interval pieces 1,3,5 | shared `base₁`/`k₁,k₃,k₅`, proven one-time | each `Jᵢ'C` proven separately with its own `base`, `k` lets |
| Interval pieces 2,4 | shared `base₂, k₂` / `base₄, k₄` | — |
| Tail piece (6) | `I₆'C_differentiableAt` with heavy `hasDerivAt` plumbing | `J₆'C_differentiableOn` with a `maxHeartbeats 1000000` block |
| Combining | `aPrimeC_analyticOnNhd` sum-of-6 | `bPrimeC_analyticOnNhd` sum-of-6 |

On A, pieces 1/3/5 share a common `base₁` and three `k` parametrizations.
On B, pieces 1/2/3/4/5 each rebuild their `base` and `k` from scratch
(see `B/BPrimeExtension.lean:239, 276, 307, 344, 378`). The A organization
is already partially factored; B's pieces 1,2,3,4,5 share the structure
`base(t) = ψT' (zⱼ' t)` (with a special case for `ψI'` at piece 5) and
`k(t) = π·I·zⱼ' t`. This is **the biggest concrete saving in the subtree**.

Internal parallelism of `Iᵢ'C_differentiableAt` / `Jᵢ'C_differentiable` (A:318–
350 resp. B:239–435):

Both have a common template
```
let base : ℝ → ℂ := …
let k    : ℝ → ℂ := …
obtain ⟨C, hC⟩ := bound_existence_lemma
...apply differentiableAt_intervalIntegral_mul_exp...
```

On B, pieces 1–5 are **five nearly-identical copies** of this 37-line block
(B:239–434). The only differences across those five are:
- the `z` function (`z₁', z₂', z₃', z₄', z₅'`),
- the `ψ` function (`ψT', ψT', ψT', ψT', ψI'`),
- the norm bound (`2π, 3π, 2π, 3π, π`),
- a `(-1)` or `(-2)` prefactor on piece 4/5.

On A, pieces 1,3,5 share `base₁` and 2/4 share an `arg₂`/`arg₄` pattern
(A:540–643) that is **also 5 near-copies** of a common bound-and-differentiate
template modulo (a) the `arg` function and (b) the `k` polynomial.

**Refactor potential** (the single biggest win):

Define a helper
```
lemma differentiableAt_intervalIntegral_from_components
    {z : ℝ → ℂ} {ψ : ℂ → ℂ} (Mψ : ℝ) (Cz : ℝ)
    (hz_cont : Continuous z)
    (hψ_cont_on_range : ContinuousOn ψ {w : ℂ | 0 < w.im})
    (hz_im : ∀ t ∈ Ι (0:ℝ) 1, 0 < (z t).im)
    (hz_norm : ∀ t ∈ Ι (0:ℝ) 1, ‖z t‖ ≤ Cz)
    (hψ_bdd : ∀ t ∈ Ι (0:ℝ) 1, ‖ψ (z t)‖ ≤ Mψ)
    (u0 : ℂ) :
  DifferentiableAt ℂ
    (fun u : ℂ => ∫ t in (0:ℝ)..1, ψ (z t) * Complex.exp (π * I * u * z t)) u0
```
that bundles `base := ψ ∘ z`, `k t := π * I * z t`, bound composition,
and final application of `differentiableAt_intervalIntegral_mul_exp`.

Then `J₁'C_differentiable` through `J₅'C_differentiable` become 3-line
specializations each, roughly 40 lines total instead of ~200.

A's `I₁'C_differentiableAt`, `I₃'C_differentiableAt`, `I₅'C_differentiableAt`
can each become a 4-line specialization against `base₁` + a custom `k`.
A's `I₂'C_differentiableAt`, `I₄'C_differentiableAt` would need a small
generalization to allow `k(t) = a + b · t + c` (not just `a + b · z(t)`),
but that's a trivial extension.

Estimated savings: **~300 lines from `B/BPrimeExtension.lean`** and
**~150 lines from `A/APrimeExtension.lean`**, total **~450**.
**Confidence: HIGH** — the templates are already visible in the code;
it's a mechanical extraction of a shared lemma.

Additional win: the "tail" piece (`I₆'C`/`J₆'C`) is ~240 lines on each side
with a ~75% common outline (`μ = volume.restrict (Ici 1)`, parametric
integral with exponential decay, `Integrable.mono'` with a
`t * exp(-(π·ε)·t)` dominator). One could factor a `tail_differentiableAt`
lemma taking the base function bound as input, saving another ~120 lines.
**Confidence: MEDIUM-HIGH.**

### 2.7 A Cancellation subtree vs B PsiICancellation/Cancellation/ThetaAxis subtree

This is where the mathematics genuinely differs, so savings here are
mostly "shared infrastructure" rather than direct clones. Still, there
are concrete overlaps.

**A/Cancellation/ImagAxis.lean** (596) sets up the zI point, exp bounds,
Δ/E₄ remainder bounds. The machinery
- `zI t ht : ℍ`, `qParam_zI`, `modular_S_smul_zI`, `norm_φ₀_imag_le`,
  `exp_neg_two_pi_lt_one`, `q_le_q1`, `cuspFunction_qParam_eq`,
  `qExpansionFormalMultilinearSeries_partialSum_n` for n=1,2,3,
  `exists_E4_sub_one_bound`, `exists_Delta_sub_q_bound`, etc.

is **entirely absent** from the B side, which instead builds a separate
asymptotics chain over `Θⱼ`/`Hⱼ`.

**Shared infrastructure candidates** (both A and B could use):
- `cuspFunction_qParam_eq`, `qExpansionFormalMultilinearSeries_partialSum_*`
  (generic about modular forms on ℍ via `qParam`, not specific to A's
  `φ₀`/`φ₂`/`φ₄`);
- exp bound lemmas `exp_neg_two_pi_lt_one`, `q_le_q1`,
  `exp_neg_two_pi_le_exp_neg_pi`, `exp_neg_three_pi_le_exp_neg_pi`,
  `exp_neg_five_pi_le_exp_neg_pi` etc. (B redefines these in
  `B/PsiICancellation.lean:48–61`);
- the `ResToImagAxis.zI` helper (A has it; B rederives inline at multiple
  places);
- `norm_add_add_add_le`, `norm_pow4_sub_le` (B/ThetaAxis/HExpansions.lean:29,33)
  — these are pure analysis lemmas that would fit in `Common.lean`.

**A/Cancellation/LargeImagApprox.lean** (547) and
**B/ThetaAxis/{HExpansions,InvH2Sq,QExpansion}.lean** (730+930+600=2260)
are proof-heavy files about asymptotic expansions of different modular
forms. They can share helpers but their content is not parallel.

**A/Cancellation/Integrability.lean** (864) vs **B/Cancellation.lean** (356):

These **are parallel** in structure. Both have:

1. a boundedness result on `Ioi 0` (A's `aAnotherIntegrand_integrableOn_Ioc`
   for the near-zero compact range; B's `exists_bound_norm_bAnotherBase_Ioi`
   for the full `(0,∞)`),
2. tail domination by a polynomial-times-exponential integrable function
   (A's `aAnotherIntegrand_integrableOn_Ici` using `integrable_of_isBigO_exp_neg`;
   B's `bAnotherBase_integrable_exp`/`_mul_exp` using similar asymptotic
   arguments),
3. the final `Integrable.mono'` closure.

B is half the length because B uses `exists_bound_norm_bAnotherBase_Ioi` — a
single `O(1)` bound — whereas A uses a `t²·exp(-2πt)` bound for large `t`
which requires more work to set up. That difference is essential (the
`ψI'(it)` cancellation gives `O(exp(-πt))`, so a uniform bound suffices,
whereas `φ₀''(I/t)` requires the cancellation via the S-transform).

**Refactor potential**: extract a `continuousOn_oIoc_integrableOn` helper
and a `dominatedOn_Ici_integrableOn` helper that each side can call.
Savings: **~150 lines** from A/Cancellation/Integrability.lean (reduce the
`AEStronglyMeasurable` boilerplate at A:492–521 and A:803–831 — nearly
identical in structure — to a single `ContinuousOn.aestronglyMeasurable`
call); **~30 lines** from B/Cancellation.lean. Total: **~180 lines**,
**confidence: MEDIUM**.

## 3. File pairs diffed in detail

### Pair 1: `A/Continuation.lean` vs `B/Continuation.lean`

- A:45–51 defines `aAnotherRHS`; B:45–48 defines `bAnotherRHS`. Both are
  `(±4 I) * sin²(πu/2) * (pole_terms + integral)`.
- A:53–118 proves `aAnotherRHS_analyticOnNhd`; B:50–102 proves `bAnotherRHS_analyticOnNhd`.
  Both follow the identical template:
  ```
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hu_ne0 : ∀ u ∈ ACDomain, u ≠ 0 := …
  have hsin_arg : AnalyticOnNhd ℂ (fun u : ℂ => (π : ℂ) * u / 2) ACDomain := …
  have hsin : AnalyticOnNhd ℂ (sin ∘ (…)) ACDomain := …
  have hsin_sq : AnalyticOnNhd ℂ ((sin …)^2) ACDomain := hsin.pow 2
  have hI : AnalyticOnNhd ℂ <x>AnotherIntegralC ACDomain := …
  <pole-term analyticity — 3 terms on A, 2 on B>
  have hinner : AnalyticOnNhd ℂ (sum of terms) ACDomain := …
  simpa [<x>AnotherRHS] using (hconst.mul hsin_sq).mul hinner
  ```
  This is ~50 lines of identical scaffolding except for the specific pole
  terms. A shared lemma
  `analyticOnNhd_anotherRHS_prefactor (pole : ℂ → ℂ) (hpoleAnalytic : AnalyticOnNhd ℂ pole ACDomain) (hpoleOfReal : …) (integralC : ℂ → ℂ) (hintAnalytic : AnalyticOnNhd ℂ integralC rightHalfPlane) (sign : ℂ) : AnalyticOnNhd ℂ (fun u => sign * I * sin²(πu/2) * (pole u + integralC u)) ACDomain`
  would save ~90 lines across the two files.
- A:127–134 / B:117–129: literally identical except for `a'`/`b'` and
  `aPrimeC`/`bPrimeC`.
- A:147–181 / B:142–166: the final wrapper, each ~25 lines, each just
  packages the input theorem in terms of the complex RHS and applies
  `analytic_continuation_of_gt2`. **These could be a single shared lemma.**

**Concrete action**: replace both `{A,B}/Continuation.lean` with thin files
(maybe 40 lines each) referring to a new
`AnotherIntegral/ContinuationWrapper.lean` taking
`(polePart : ℂ → ℂ, integralC : ℂ → ℂ, sign : ℂ, …)`. Savings: **~150 lines**,
**confidence: HIGH**.

### Pair 2: `A/Parametric.lean` (378) vs `B/Parametric.lean` (229)

Both prove `<x>AnotherIntegralC_analyticOnNhd rightHalfPlane`. The common
ingredient needed is:

1. `base : ℝ → ℂ` continuous on `(0,∞)`, with
2. `IntegrableOn (fun t => base t * exp(-π u t)) (Ioi 0)` for all real `u > 0`,
3. `IntegrableOn (fun t => t · base t · exp(-π u t)) (Ioi 0)` for all real `u > 0`.

Given these, the analyticity follows by
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` with a standard bound
`bound(t) := π · ‖t · base(t)‖` (valid on the ball `Metric.ball u (Re u / 2)`).

A:99–374 builds all this from scratch with:
- AEStronglyMeasurability of the integrand at every z (A:122–155) — 33 lines
  of `fun_prop`-style setup that B condenses into a 10-line
  `hbase_int.aestronglyMeasurable` invocation (B:107–113).
- An explicit `hmul_exp` trade lemma at A:166–188 that is the same as what
  B accomplishes via `hratio_norm_le_one` at B:115–132.
- `hF_int`, `hbound`, `hdiff` three-step structure — same on both sides.

A shared lemma
```
theorem analyticOnNhd_integral_base_exp
    {base : ℝ → ℂ}
    (hbase_cont : ContinuousOn base (Set.Ioi 0))
    (hbase_int : ∀ u > 0, IntegrableOn (fun t => base t * Real.exp (-π * u * t)) (Ioi 0))
    (hbase_mul_int : ∀ u > 0,
       IntegrableOn (fun t => t * base t * Real.exp (-π * u * t)) (Ioi 0)) :
  AnalyticOnNhd ℂ
    (fun u : ℂ => ∫ t in Ioi 0, base t * Complex.exp (-(π : ℂ) * u * (t : ℂ)))
    rightHalfPlane
```
would render both `Parametric.lean` files down to a one-liner each,
aside from defining `<x>AnotherBase` and wiring up the integrability
hypotheses (which already exist as theorems on B and can be established
on A via `aAnotherIntegrand_integrable_of_pos` after a minor rephrasing).

Savings: **~450 lines** (A: ~320, B: ~170).
**Confidence: HIGH.**

### Pair 3: `A/APrimeExtension.lean` — block `I₁'C`/`I₃'C`/`I₅'C` (318–350) vs `B/BPrimeExtension.lean` — block `J₁'C`–`J₅'C` (239–435)

The mechanical-copy-count champions.

A's block (33 lines per lemma × 3 = ~100 lines): each uses `base₁`,
`k_i`, `base₁_bound`, `base₁_continuousOn`, `k_i_continuousOn`, `k_i_bound`
then one `differentiableAt_intervalIntegral_mul_exp` call. These already
factor out the bound logic, so the three lemmas are small.

B's block (37 lines per lemma × 5 = ~185 lines): no shared `base`. Each
lemma redoes:
```
let base t := ψT'/ψI' (zⱼ' t)
let k t := π * I * zⱼ' t
hbase_cont := continuousOn_ψT'_comp zⱼ' …
obtain ⟨Mψ, hMψ⟩ := exists_bound_norm_ψT'_zⱼ'
hbase_bound := …
hk_bound := norm_pi_mul_I_mul_le …
apply differentiableAt_intervalIntegral_mul_exp
hEq : (fun u => ∫ …) = Jⱼ'C := by funext; simp
```

A factoring of the form
```
lemma J_piece_differentiable
    {ψ : ℂ → ℂ} {z : ℝ → ℂ} {Mψ Cz : ℝ}
    (hψ_cont : … ) (hz_cont : Continuous z) (hz_im : …)
    (hz_norm : ∀ t ∈ Ι 0 1, ‖z t‖ ≤ Cz)
    (hψ_bound : ∀ t ∈ Ι 0 1, ‖ψ (z t)‖ ≤ Mψ) :
  Differentiable ℂ (fun u : ℂ => ∫ t in (0:ℝ)..1,
      ψ (z t) * Complex.exp (π * Complex.I * u * z t))
```
lets each `Jⱼ'C_differentiable` become ~8 lines. Savings on B alone:
**~140 lines**. A side already mostly factored; can still save ~60 lines
by applying the same abstraction to `I₂'C`/`I₄'C`.

## 4. Proposed refactor, phase by phase

Each phase targets a specific savings estimate and confidence. Listed in
order of increasing risk. All proposed new files live under
`AnotherIntegral/Common/` or `AnotherIntegral/`.

### Phase 1 (low risk): `AnotherIntegral/Common/AnalyticityWrapper.lean` (new, ~80 lines)

Content: the generic `analyticOnNhd_integral_base_exp` theorem described
in Pair 2 above.

Consumers:
- `A/Parametric.lean` (378 → ~60 lines): savings **~320 lines**.
- `B/Parametric.lean` (229 → ~50 lines): savings **~180 lines**.

Risks: A's integrability witnesses are packaged around `aAnotherIntegrand`
(real-valued coefficients folded in), so a minor adapter is needed
to rephrase `aAnotherIntegrand_integrable_of_pos` in terms of
`aAnotherBase` + `exp`. This is trivial since `aAnotherIntegrand_eq` at
`A/Parametric.lean:72` already equates the two.

**Net: +80 new, -500 old ⇒ ~420 lines. Confidence: HIGH.**

### Phase 2 (low risk): `AnotherIntegral/Common/ContinuationWrapper.lean` (new, ~100 lines)

Content: a packaged form of `analytic_continuation_of_gt2` that takes
`(value : ℝ → ℂ, prefactor : ℂ → ℂ, poleC : ℂ → ℂ, integralC : ℂ → ℂ)`,
produces the final real-side equality, and does the
`<x>AnotherRHS_analyticOnNhd` proof via a shared
`analyticOnNhd_polePart_prefactor_times_integral` lemma.

Consumers:
- `A/Continuation.lean` (185 → ~40 lines): savings **~145 lines**.
- `B/Continuation.lean` (170 → ~35 lines): savings **~135 lines**.

Risks: A has three pole terms; B has two. The shared lemma will likely
take `pole : ℂ → ℂ` as a parameter with the analyticity proved once per
side (still shorter than the current 60-line proofs).

**Net: +100 new, -280 old ⇒ ~180 lines. Confidence: HIGH.**

### Phase 3 (medium risk): `AnotherIntegral/Common/IntervalIntegralMul.lean` (new, ~150 lines)

Content: the `J_piece_differentiable` / `I_piece_differentiable` helper
from Pair 3, plus a tail-integral variant for `I₆'C`/`J₆'C`.

Consumers:
- `A/APrimeExtension.lean` (936 → ~650): savings **~290 lines**.
- `B/BPrimeExtension.lean` (677 → ~350): savings **~325 lines**.

Risks: the `I₂'C`/`I₄'C` cases use a more complex `k(t)` with three
affine pieces instead of one. The helper would need a generic
`k : ℝ → ℂ` with `ContinuousOn` and a uniform-bound hypothesis, which is
exactly what `differentiableAt_intervalIntegral_mul_exp` in
`AnotherIntegral/Common.lean:29` already requires, so no further
abstraction is needed there. The save on A would be mostly around the
many `base_continuousOn`/`k_continuousOn` boilerplate lemmas, not the
final differentiability calls.

Also, the `I₆'C`/`J₆'C` tail piece has non-trivial divergence (`φ₀''(I·t)`
decay on A vs `ψS.resToImagAxis` decay on B). The helper should take the
tail decay hypothesis as input.

**Net: +150 new, -615 old ⇒ ~465 lines. Confidence: MEDIUM-HIGH.**

### Phase 4 (medium risk): `AnotherIntegral/Common/RepresentationAlgebra.lean` (new, ~80 lines)

Content: `corrIntegral_eval_of_coeffs_list` taking a list of
`(coefficient, polynomial exponent, exp shift)` tuples and evaluating
the weighted sum of Laplace integrals, plus the `assemble_another_integral`
glue.

Consumers:
- `A/Representation.lean` (388 → ~200): savings **~190 lines**.
- `B/AnotherIntegral.lean` (223 → ~170): savings **~50 lines**.

Risks: the output is a rational function in `u` that must be massaged
back into the specific form appearing in each main theorem; this can
be tedious (`field_simp`/`ring`-style maneuvers for each denominator
shape).

**Net: +80 new, -240 old ⇒ ~160 lines. Confidence: MEDIUM.**

### Phase 5 (medium-low risk): consolidate exp-lemma helpers

Currently `exp_neg_*_le_exp_neg_*` lemmas are repeated in A and B:
- A/Cancellation/ImagAxis.lean:80, 84, 114, 117
- A/Cancellation/LargeImagApprox.lean:31
- B/PsiICancellation.lean:32–61
- B/ThetaAxis/QExpansion.lean:40–43

Move all generic `exp(a·π·t) ≤ exp(b·π·t)` lemmas (6–8 of them) into
`AnotherIntegral/Common.lean` (currently 131 lines, already has
`exp_neg_two_pi_lt_one` at line 80).

Savings: **~60 lines** (spread over three files). **Confidence: HIGH.**

### Phase 6 (lower risk but smaller): Cancellation wrappers

Extract two generic integrability helpers used by both
`A/Cancellation/Integrability.lean` and `B/Cancellation.lean`:

1. `integrableOn_Ioc_of_continuousOn_bound` taking a continuous function
   and a uniform bound on `(0,1]`, producing `IntegrableOn`.
2. `integrableOn_Ici_of_bigO_exp` taking a function `O(exp(-c·t))` on
   `[1,∞)` and producing `IntegrableOn`.

Both are essentially rewrappings of existing mathlib lemmas with our
specific constants.

Savings: **~80 lines** (A: 60, B: 20). **Confidence: HIGH.**

## 5. Summary: total recoverable savings

| Phase | Delta | Confidence |
|---|---|---|
| 1. AnalyticityWrapper | **~420 lines** | HIGH |
| 2. ContinuationWrapper | **~180 lines** | HIGH |
| 3. IntervalIntegralMul | **~465 lines** | MEDIUM-HIGH |
| 4. RepresentationAlgebra | **~160 lines** | MEDIUM |
| 5. Exp-lemma consolidation | **~60 lines** | HIGH |
| 6. Cancellation integrability wrappers | **~80 lines** | HIGH |
| **Realistic total** | **~1365 lines** | |

If Phases 1–3+5 (the HIGH confidence ones) alone are executed the
savings are already **~1125 lines** — the subtree would drop from
**~8880 → ~7750**, roughly a 13% reduction. Executing all six phases
puts the reduction at **~15%**.

Note that this is below the "1500 lines" target the user asked for,
because the A/Cancellation/* and B/ThetaAxis/* asymptotic-analysis files
(~4800 lines combined) have genuinely distinct mathematical content
(different modular forms, different q-expansions). The other ~4000
lines of A+B are highly parallel and are exactly where the savings
live.

## 6. Risks & constraints

1. **Import layering**: `A/Cancellation/*` is imported via
   `A/Parametric.lean` which is imported by `A/Continuation.lean` which is
   imported by `A/Representation.lean`. The Phase-1/2 wrappers would sit
   at the `AnotherIntegral/Common/` level (below `A/` and `B/`), which
   already works — `Common.lean` and `ContinuationCommon.lean` are
   already there. No cycle.

2. **`module` + `public import` directives**: Every file uses the
   `module` system with `public import …`. Any new wrapper file must
   be `public import`ed by the consumer; test that `aPrimeC_analyticOnNhd`
   and `bPrimeC_analyticOnNhd` remain `public` after the refactor
   (they currently are).

3. **Heartbeats and `maxHeartbeats` blocks**: `J₆'C_differentiableOn` at
   `B/BPrimeExtension.lean:436` already sets `maxHeartbeats 1000000`.
   Abstracting across `I₆'C`/`J₆'C` may still need per-call
   heartbeats; budget for this explicitly.

4. **Definitional transparency of `<x>PrimeC`**: both `aPrimeC` and
   `bPrimeC` are `public def` in their respective extension files. They
   are consumed by `IntegralReps/...` in the `g.CohnElkies.Defs` layer
   via the `<x>PrimeC_ofReal` lemmas. Any refactor of
   `APrimeExtension.lean`/`BPrimeExtension.lean` must preserve these two
   public lemmas bit-for-bit (their statement only, not proof).

5. **`field_simp` / `ring_nf` brittleness in Phase 4**: The correction-
   integral evaluations rely on `field_simp [Real.pi_ne_zero, ...]`
   closing routine rational-function identities. Generalizing that
   across A's 3-term and B's 2-term sums is where most of the risk sits.

## 7. Concrete file path references

For each planned new file:

- `SpherePacking/MagicFunction/g/CohnElkies/AnotherIntegral/Common.lean`
  (exists, 131 lines) — **add** generic exp inequality lemmas (Phase 5).
- `SpherePacking/MagicFunction/g/CohnElkies/AnotherIntegral/Common/AnalyticityWrapper.lean`
  (**new**, Phase 1) — the parametric-integral analyticity theorem.
- `SpherePacking/MagicFunction/g/CohnElkies/AnotherIntegral/Common/ContinuationWrapper.lean`
  (**new**, Phase 2) — or extend `ContinuationGeneric.lean:40` in place
  (currently 70 lines; can grow to ~160).
- `SpherePacking/MagicFunction/g/CohnElkies/AnotherIntegral/Common/IntervalIntegralMul.lean`
  (**new**, Phase 3) — the `J_piece_differentiable` helper.
- `SpherePacking/MagicFunction/g/CohnElkies/AnotherIntegral/Common/RepresentationAlgebra.lean`
  (**new**, Phase 4) — the Laplace-subtraction lemma.
- `SpherePacking/MagicFunction/g/CohnElkies/AnotherIntegral/Common/CancellationWrappers.lean`
  (**new**, Phase 6) — the integrability wrappers.

For each file that shrinks:

| File | Current | After (est.) | Δ |
|---|---|---|---|
| `A/Parametric.lean` | 378 | ~60 | −318 |
| `B/Parametric.lean` | 229 | ~50 | −179 |
| `A/Continuation.lean` | 185 | ~40 | −145 |
| `B/Continuation.lean` | 170 | ~35 | −135 |
| `A/APrimeExtension.lean` | 936 | ~650 | −286 |
| `B/BPrimeExtension.lean` | 677 | ~350 | −327 |
| `A/Representation.lean` | 388 | ~200 | −188 |
| `B/AnotherIntegral.lean` | 223 | ~170 | −53 |
| `A/Cancellation/Integrability.lean` | 864 | ~800 | −64 |
| `B/Cancellation.lean` | 356 | ~340 | −16 |
| **New common files** | 0 | ~450 | +450 |
| **Net** | | | **−1261** |

This is a realistic lower bound. Optimistically (bringing Phase 4's full
scope into scope) the number climbs to **~1400–1500**.
