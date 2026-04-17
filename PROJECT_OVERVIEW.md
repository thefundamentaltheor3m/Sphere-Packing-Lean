---
title: "Sphere-Packing-Lean: radical-deduplication overview"
generated: 2026-04-17
---

# Project Overview — Radical Deduplication

## Executive Summary

**Current state:** 269 `.lean` files, 54,873 lines, proves
`SpherePackingConstant 8 = E8Packing.density` with a clean axiom footprint
(`propext`, `Classical.choice`, `Quot.sound`) and no `sorry`/`admit`.

**User's stated goal:** reduce to ~20-30k lines by aggressively generalising
over the `I₁-I₆` / `J₁-J₆` duplicate families and extracting API.

**Honest assessment of what's achievable:**

| Tier | Net savings | Resulting total | Effort |
|---|---:|---:|---|
| All five analyses fully executed (high-confidence only) | **~6,500 lines** | ~48,400 | 3-5 days |
| Same + medium-confidence items | **~9,500 lines** | ~45,400 | 1-2 weeks |
| Same + upstream 4-5 PRs to mathlib absorbed | **~11,200 lines** | ~43,700 | 2-3 months (mathlib review) |
| Reaching 30k | would require radical restructuring (see "Beyond the plan" §) |

The bulk of the remaining 43-45k is **genuine mathematical content** — the
CohnElkies bound, the magic-function construction, the blueprint's modular
identities (`F·G`, Ramanujan, Jacobi `H₂+H₄=H₃`), the E8 lattice packing,
and asymptotic analyses (`A_E_sq_coeff`, `L10OverAsymptotics`). Reaching
20-30k would require either (a) a major upstream push to mathlib for the
`F·G`/`D`/Jacobi-theta blueprint, or (b) an architectural rewrite of the
radial magic-function construction (e.g., defining it once abstractly in
terms of a `MagicFunctionData` structure and deriving both `a` and `b` as
instances — the earlier Phase 5 only partially did this).

## Statistics

| Metric | Value |
|---|---:|
| `.lean` files | 269 |
| Total lines | 54,873 |
| Largest directory (`MagicFunction/g/CohnElkies/`) | 10,200 |
| Second largest (`MagicFunction/a/` + `MagicFunction/b/`) | ~12,800 |
| Third largest (`ModularForms/`) | 5,873 |

Per-agent identified savings (mid-range of each agent's estimate):

| Cluster | Mid savings | Detailed report |
|---|---:|---|
| I/J families (`a/`, `b/`, contour, Eigenfunction) | **~4,500** | `.claude-analysis/I_J_families.md` |
| ModularForms (mathlib replacement + FG dedup) | **~1,525** | `.claude-analysis/modularForms.md` |
| AnotherIntegral A/B | **~1,325** | `.claude-analysis/anotherIntegral_AB.md` |
| LaplaceA/B | **~950** | `.claude-analysis/laplace_AB.md` |
| ForMathlib / Integration / LPBound (no upstream) | **~760** | `.claude-analysis/mathlib_replacements.md` |
| **Total mid-range** | **~9,060** | → 45,800 lines |

---

## Top Findings by Cluster

### 1. I/J Families — the biggest single win (~4,500 lines)

The `a/` and `b/` subtrees plus their Eigenfunction developments total ~7,800
lines of near-sign-flipped parallel proofs. Phase 5 of the earlier plan
unified the Schwartz-assembly layer but left the core proof infrastructure
duplicated.

**Concrete refactor (7 sub-steps, targeting 4,500-line reduction):**

1. **New `MagicFunction/Common/IciOneIntegrand.lean`** (~150 lines) absorbing the common `Ici 1` half-line integral machinery currently duplicated between `a/IntegralEstimates/I5.lean`, `I6.lean`, `Integration/SmoothIntegralIciOne.lean`, and the decay half of `DecayI1.lean`. → ~300 lines saved.

2. **New `Integration/SmoothIntegralIoo01.lean`** (~120 lines) unifying `SmoothI24Common.lean` and `SmoothJ24Common.lean`. → ~150 lines.

3. **Sign-polymorphic `PermJ12FourierHypotheses` in `Contour/PermJ12Fourier.lean`** retires the 10-file `a/Eigenfunction/PermI12*` family (1,222 lines → ~400 after unification). → **~800 lines**. *This is the single biggest win.*

4. **New `Contour/PermI5.lean`** (~200 lines) consolidating `PermI5Main` + `PermJ5Main`. → ~350 lines.

5. **Extending `Common/SchwartzAssembly.lean`** + retiring `a/SmoothI6.lean`'s local `hasDerivAt_integral_gN_of_gt_neg2` (already in `SmoothIntegralIciOne`). → ~100 lines.

6. **Decay unification**: `DecayI1.lean` + decay half of `I6.lean` → one generic `decay_of_iteratedDeriv_eq_integral_pow_mul` extension. → ~200 lines.

7. **I2/I4 sign-unified variant**: `I24Common.lean` extension to absorb the few remaining sign differences. → ~100 lines.

**Recommended ordering** (least-to-most disruptive): 1, 2, 5, 6, 7 first; 3 and 4 last.

**Risks:** `DiffContOnCl` generalisation (item 3), heartbeat budgets on the `SmoothIntegralIciOne` reuse.

### 2. ModularForms — mathlib has caught up (~1,500 lines)

Mathlib's modular-forms library expanded significantly since the project
started. Three files can shrink dramatically by delegating to mathlib:

1. **`Delta.lean` 606 → ~300** using `Mathlib.NumberTheory.ModularForms.DedekindEta` (now has `ModularForm.eta`, `eta_ne_zero`, `logDeriv_eta_eq_E2`, `multipliableLocallyUniformlyOn_eta`). Local `Delta_boundedfactor` and `Delta_cuspFuntion_eq` + helpers are largely subsumed.

2. **`SummableLemmas/QExpansion.lean` 716 → ~400** using mathlib's `EisensteinSeries.QExpansion`, `contDiffOn_tsum_cexp`, `iteratedDerivWithin_tsum_cexp_eq`. The local `exp_series_ite_deriv_uexp2`, `tsum_uexp_contDiffOn`, `aut_bound_on_comp` families are re-proven mathlib.

3. **`EisensteinBase.lean` 845 → ~550** — `q_exp_unique` (line 199) is `HasFPowerSeriesAt.eq_formalMultilinearSeries`; `Ek_q_exp` can use mathlib's `eisensteinSeries_qExpansion`; `bernoulli'_five/six` and `riemannZeta_six` may already be upstream.

4. **`SummableLemmas/Basic.lean` 116 → ~25** — eight of its lemmas are direct mathlib aliases (`int_sum_neg`, `summable_neg`, `tsum_pnat_eq_tsum_succ3`, etc.).

5. **Internal FG dedupe (~150-280 lines)**: `F_eq_FReal` / `G_eq_GReal` / `FmodGReal_eq_div` are structurally identical; three copies of "exp bound on imag axis" across `EisensteinBase`, `FG/Positivity`, `FG/L10OverAsymptotics`.

6. **`SerreDerivativeSlash.lean:77` vs `Derivative/Ramanujan.lean:221`** — two separate proofs of `serre_D 1 E₂` slash-invariance. Consolidate.

**Genuinely project-specific (keep as-is):** `FG/*`, `DimensionFormulas`, `Lv1Lv2Identities`, `ThetaDerivIdentities`, `JacobiTheta/DeltaIdentity`, `ResToImagAxis`, `antiSerreDerPos`, `Derivative/Ramanujan`, `D₂` correction term.

### 3. AnotherIntegral A/B — structural parallel (~1,300 lines)

The `g/CohnElkies/AnotherIntegral/A/` (3,503 lines) and `B/` (5,100 lines)
subtrees share a 4,108-line "assembly" layer (Parametric + Continuation +
Representation + Extension) that differs only by 3-4 atomic substitutions:
`aAnotherBase`↔`bAnotherBase`, `φ₀''/φ₂'/φ₄'`↔`ψI'/Θⱼ/Hⱼ`, sign `+4I`↔`-4I`,
pole terms.

**Six proposed refactors (total ~1,300 lines):**

1. **`AnalyticityWrapper`** for `aAnotherIntegralC_analyticOnNhd` / `bAnotherIntegralC_analyticOnNhd`. **~420 lines** (HIGH confidence).
2. **`ContinuationWrapper`** for `<x>AnotherRHS_analyticOnNhd` + continuation glue. **~180 lines** (HIGH).
3. **`IntervalIntegralMul`** helper replacing 5 near-copies of `Jⱼ'C_differentiable` (B:239-435) and three of `Iⱼ'C_differentiableAt` (A:318-350). **~465 lines** (MED-HIGH).
4. **`RepresentationAlgebra`** sharing `corrIntegral_eval`. **~160 lines** (MED).
5. **Consolidate** 6-8 `exp_neg_*_le_exp_neg_*` lemmas. **~60 lines** (HIGH).
6. **Extract** 2 integrability wrappers. **~80 lines** (HIGH).

**What's genuinely distinct (~4,900 lines):** The asymptotic-analysis files
(`A/Cancellation/*`, `B/ThetaAxis/*`, `B/PsiICancellation.lean`) carry
different modular forms, different q-expansions, and different decay rates.
Savings there are limited to extracted helpers.

### 4. LaplaceA/B — A wasn't modernized (~950 lines)

LaplaceA is 2,236 lines, LaplaceB is 1,523 — a 713-line gap. Only ~250-350
lines is genuine math asymmetry (A's integrand has a `w²` tail from the
`φ₀(S•w)·w²` S-transform); the remaining **~650 lines is pure "A hasn't
been modernized"** — B's `bContourWeight/bContourIntegrand*` abstraction
(in `ContourIdentities.lean`) has no A counterpart, and A inlines 4 copies
of `‖cexp‖ = exp(-πut)` computations that B already shares.

**Six-step refactor plan (R1-R6):**

| Step | Target | Saves | Conf |
|---|---|---:|---|
| R1 | Weight-common: introduce `aContourWeight` mirroring B's `bContourWeight` | 100 | HIGH |
| R2 | Rect-deform driver: 5 near-identical `hRect*` applications → one helper | 160 | MED |
| R3 | Integrability helpers: 3 shared lemmas | 200 | HIGH |
| R4 | Unified modular bound: `exists_phi2'_phi4'_bound_exp` + `exists_ψI_bound_exp` | 200 | MED |
| R5 | Parametrisation helper: collapse 6 separate per-side parametrisations | 100 | HIGH |
| R6 | Shift identities: small consolidation | 20 | HIGH |

**Prerequisite for R2/R4**: split `LaplaceB/LaplaceRepresentation.lean`
(918 lines — a monolith containing strip bounds, integrability, 2 rect-Cauchy
applications, 6 parametrisations, final algebra) into files mirroring A's
3-file architecture.

**Quick wins:** R1 + R3 + R5 = **~400 lines, no-regret**.

### 5. ForMathlib / Integration / LPBound — mathlib has most of this (~760 lines, +940 via upstream)

**Immediate deletable (no upstream needed, ~760 lines):**

- `ComplexI.lean` (15) — `Complex.I_mul_I` wrapper
- `VolumeOfBalls.lean` (26) — `Metric.measure_ball_pos`, `MeasureTheory.measure_ball_lt_top` cover it
- `IntervalIntegral.lean` (29), `IntegralProd.lean` (31), `FunctionsBoundedAtInfty.lean` (15) — 1-2 line wrappers
- `RadialSchwartz/Multidimensional.lean`'s `hasFDerivAt_norm_sq` → mathlib's `HasFDerivAt.norm_sq`
- 8 Integration duplicate wrapper pairs (~150 lines combined)
- 4 modular-form helper files merge into one (~75 lines gain)

**Mathlib equivalents found** (direct replacements):
- `ENNReal.tsum_const`, `ENNReal.tsum_one` (direct analogs of `ENat.lean`)
- `Set.encard_iUnion_of_finite` (replaces local `Encard` work)
- `ModularGroup.S_mul_S_eq` (duplicated as `modular_S_sq`)
- `Complex.norm_exp_ofReal_mul_I`, `HasFDerivAt.norm_sq`, `norm_iteratedFDeriv_mul_le`, `norm_iteratedFDeriv_eq_norm_iteratedDeriv`, `IsCompact.exists_isMaxOn`, `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`, `Real.summable_pow_mul_exp_neg_nat_mul`

**`LPBound.lean` (605)** is two giant theorems. ~60 lines of `LinearProgrammingBound'` is pure `Real.toNNReal`/`ENNReal` coercion bookkeeping; the 92-line `hSummable` block deserves extraction as a named helper.

**Upstream PR candidates (additional ~940 lines if accepted):**
- `CauchyGoursat/OpenRectangular.lean` (260) — real mathematics, mathlib-worthy
- `ENat.lean` + parts of `Encard.lean` (~130)
- `BoundsOnIcc` / `IntegrablePowMulExp` / `SigmaBounds` / `DerivHelpers` / `ContDiffOnByDeriv` bundle (~200)
- `FourierLinearEquiv.lean` (60)
- `Cusps.lean` (35)

---

## Prioritised Action Plan

Seven phases, sequenced by dependency and difficulty.

### Phase 9 — Quick no-regret wins (~1,200 lines, 1-2 days)

- Delete the 8 trivial ForMathlib wrappers
- Replace project lemmas with existing mathlib equivalents (grep-and-sub)
- Apply `SummableLemmas/Basic` mathlib-alias deletions
- Merge four modular-form helper files
- Consolidate the two duplicated `serre_D 1 E₂` slash-invariance proofs
- Fix LPBound coercion bookkeeping (extract named helper from `calc_steps_part2`)

### Phase 10 — Delta + SummableLemmas + EisensteinBase modernization (~1,500 lines, 3-5 days)

- `Delta.lean` → delegate to `Mathlib.NumberTheory.ModularForms.DedekindEta` (606 → ~300)
- `SummableLemmas/QExpansion.lean` → use `EisensteinSeries.QExpansion` + `contDiffOn_tsum_cexp` (716 → ~400)
- `EisensteinBase.lean` → use `HasFPowerSeriesAt.eq_formalMultilinearSeries` and `eisensteinSeries_qExpansion` (845 → ~550)
- Internal FG dedup (F_eq_FReal / G_eq_GReal / "exp bound on imag axis" × 3)

### Phase 11 — LaplaceA/B quick wins (~400 lines, 2-3 days)

- R1 (weight-common for A mirroring B's `bContourWeight`)
- R3 (3 shared integrability helpers)
- R5 (parametrisation helper)
- *Do not yet attempt R2/R4* — those require splitting LaplaceB first.

### Phase 12 — AnotherIntegral A/B unification (~1,300 lines, 1-2 weeks)

- Phase 1 `AnalyticityWrapper` (~420 lines, HIGH conf)
- Phase 2 `ContinuationWrapper` (~180 lines, HIGH)
- Phase 5 `exp_neg_*_le` consolidation (~60, HIGH)
- Phase 6 integrability wrappers (~80, HIGH)
- Phase 3 `IntervalIntegralMul` (~465, MED-HIGH)
- Phase 4 `RepresentationAlgebra` (~160, MED)

### Phase 13 — I/J family unification (~4,500 lines, 2-3 weeks — the biggest lift)

Sequencing inside this phase matters (least-to-most disruptive):

- Step A (~300): `Common/IciOneIntegrand.lean` — easiest, no downstream impact
- Step B (~150): `Integration/SmoothIntegralIoo01.lean` merging `SmoothI24Common` + `SmoothJ24Common`
- Step C (~100): Retire `a/SmoothI6.lean`'s local `hasDerivAt_integral_gN_of_gt_neg2`
- Step D (~200): `DecayI1.lean` + decay half of `I6.lean` unified via extended `decay_of_iteratedDeriv_eq_integral_pow_mul`
- Step E (~100): `I24Common.lean` sign-unified variant
- Step F (~350): `Contour/PermI5.lean` new
- **Step G (~800)**: Sign-polymorphic `PermJ12FourierHypotheses` → retire 10-file `a/Eigenfunction/PermI12*` family. Highest risk, highest reward.

### Phase 14 — LaplaceB split + R2/R4 (~450 lines, 3-5 days)

- Split `LaplaceB/LaplaceRepresentation.lean` (918) into 3 files mirroring A
- R2 rect-deform driver (~160)
- R4 unified modular bound (~200)

### Phase 15 (optional) — Mathlib upstream PRs (~940 lines, 2-3 months wall-clock)

- `CauchyGoursat/OpenRectangular.lean` (260) PR
- `ENat` / `Encard` helpers PR
- `BoundsOnIcc`/`IntegrablePowMulExp`/`SigmaBounds`/`DerivHelpers`/`ContDiffOnByDeriv` bundle PR
- `FourierLinearEquiv` PR
- `Cusps` PR

---

## Beyond the plan — reaching 30k

The five analyses collectively save ~9-11k lines, taking us to **~44-46k**.
Going further requires more radical moves:

### Option α: Rewrite the magic-function construction abstractly (~6k savings)

Phase 5 of the earlier plan proposed a `MagicFunctionData` structure
parameterising the entire 6-integral decomposition. It was only partially
implemented. A full implementation would:

- Define `MagicFunctionData` bundling: 6 modular forms, eigenvalue, sign prefactors
- Instantiate `a` via `MagicFunctionData` with `(φ₀'', +1, +2)` and `b` with
  `(ψT'/ψI'/ψS', −1, −2)`
- Derive ALL 6-integral infrastructure (integrands, bounds, Fourier
  permutation, Schwartz decay, special values) generically
- `a/*` and `b/*` each shrink to ~30-line instantiation files

This is a 1-2 month architectural project. It would genuinely reach ~38-40k.

### Option β: Mathlib-absorb the entire blueprint identities (~3-5k savings)

The Ramanujan identities, Jacobi `H₂+H₄=H₃`, Lv1Lv2Identities, and theta
derivative identities are all standard. Upstream to mathlib in 4-6 PRs.
3-6 months wall-clock for review.

### Option γ: Asymptotics restructure (~2-3k savings)

`L10OverAsymptotics.lean` (756), `A_E_sq_coeff` bounds (in PolyFourierCoeffBound),
and the `norm_φ₀_le` decay proof share machinery. A generic "modular form
whose q-expansion has polynomial coefficients is bounded by C·exp(-2π·Im z)"
lemma could replace hundreds of lines of hand-rolled bounds.

### Combined: Options α + β + γ

- 46k − 6k − 4k − 2.5k ≈ **33.5k lines** — near the top of the user's range.

**Reaching 20k** would require either abandoning parts of the formalization
(the explicit E8 lattice density? the LP-bound proof?) or a multi-year
mathlib integration effort. 20k is not realistic for a standalone project
that proves this theorem from scratch.

---

## References

Detailed per-cluster analyses (all in `.claude-analysis/`):
- `I_J_families.md` — 7-sub-step refactor, 4,500 lines (~8 pp)
- `modularForms.md` — 5-phase plan, 1,180-1,870 lines (~9 pp)
- `anotherIntegral_AB.md` — 6 phases, 1,260-1,400 lines (~12 pp)
- `laplace_AB.md` — R1-R6 plan, 800-1,100 lines (~10 pp)
- `mathlib_replacements.md` — per-file mathlib equivalents (~5 pp)

Each has concrete file:line references, difficulty estimates, and risk
sections. **Start with Phase 9 (quick wins) before tackling anything structural.**
