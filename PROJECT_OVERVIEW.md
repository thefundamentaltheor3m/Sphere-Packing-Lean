# Project Overview: Sphere-Packing-Lean

Generated: 2026-05-17
Branch: `cleanup-magic-function-a`
Toolchain: `leanprover/lean4:v4.30.0-rc2`
Mathlib: `54f98fd67e63d316ddc3452ae31e18b2283be6e1` (master)

## Executive Summary

This is a Lean 4 formalization of Viazovska's E8 sphere packing theorem. The project sits at **26,456 lines across 59 files** (post-cleanup, ~52% reduction from the original ~54k). The main theorem `SpherePacking.MainTheorem` is **axiom-clean** (`propext`, `Classical.choice`, `Quot.sound`) and **sorry-free**. The codebase is organized around the Cohn–Elkies linear-programming bound, two Fourier-eigenfunction Schwartz constructions (the `+1`-eigenfunction `a` and the `-1`-eigenfunction `b`), a modular forms library, and the `E8` lattice itself.

After Phase 1 inventorying (~225 declarations across 60 files) and Phase 2 analysis (mathlib audit, duplications, generalizations, API design, junk identification), the headline findings are:

1. **The biggest single-batch refactor is collapsing `J1Smooth`/`J5Smooth` into `J15Common`** (~120–150 lines, Medium difficulty). The two namespaces in `MagicFunction/b/Schwartz/Basic.lean` are structural twins of each other and could be parametrized in the same way `SmoothJ24Common` already parametrizes `J₂`/`J₄`.
2. **The single highest-leverage-per-minute fix is adding `@[fun_prop]` to the five `continuous_z_i'` lemmas** in `MagicFunction/IntegralParametrisations.lean`. There is direct evidence of the user manually working around its absence (`have := continuous_z₁'; … fun_prop`).
3. **Total estimated savings across all Phase 2 findings**: ~700–900 lines, with significant qualitative improvements from `fun_prop` tagging, mathlib idiom alignment, and contour-deformation abstraction.

## Statistics

| Metric | Value |
|---|---|
| `.lean` files | 59 |
| Total lines | 26,456 |
| Total declarations (Phase 1 estimate) | ~225 |
| `sorry` count | 0 |
| Files using module system (`@[expose]`) | 39 |
| Main theorem | `SpherePacking.MainTheorem` (`UpperBound.lean:2466`) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| Largest files | `IntegralLemmas.lean` (2580), `a/Schwartz/Basic.lean` (2561), `UpperBound.lean` (2471) |

### Per-directory breakdown (sorted by size)

| Directory | Lines | Role |
|---|---|---|
| `MagicFunction/a/` | ~6,200 | `+1`-Fourier eigenfunction (Schwartz, decay, smoothness, special values, contour deformations) |
| `MagicFunction/b/` | ~3,900 | `-1`-Fourier eigenfunction (parallel structure to `a/`) |
| `MagicFunction/g/` | ~4,400 | Cohn–Elkies magic function `g = c₁·a + c₂·b`; "another integral" representations |
| `ModularForms/` | ~5,800 | E_k, Δ, Jacobi theta, slash actions, Ramanujan identities, cusp forms |
| `CohnElkies/` | ~2,300 | LP bound proof (`LinearProgrammingBound`, `periodic_constant_eq_constant`) |
| `Contour/` | ~700 | Möbius-inversion contour, `WedgeSetContour` |
| `Integration/` | ~550 | Measure helpers, scalar one-forms, differentiation under integral |
| `ForMathlib/` | ~600 | Helpers that ought to upstream (Gaussian integrals, decay bounds, cutoffs) |
| `Basic/` | ~1,000 | `SpherePacking` / `PeriodicSpherePacking` structures, density |
| `Tactic/` | ~500 | `NormNumI`, `FunPropExt`, `TendstoCont` |
| `UpperBound.lean` | 2,471 | Top-level: assembles everything into `MainTheorem` |

### Top-level public API (the "goal surface")

```lean
theorem SpherePacking.MainTheorem : SpherePackingConstant 8 = E8Packing.density
theorem SpherePackingConstant_le_E8Packing_density : SpherePackingConstant 8 ≤ E8Packing.density
theorem LinearProgrammingBound : SpherePackingConstant d ≤ … (Cohn–Elkies)
theorem periodic_constant_eq_constant : PeriodicSpherePackingConstant d = SpherePackingConstant d
theorem E8Packing_density : E8Packing.density = ENNReal.ofReal π ^ 4 / 384
theorem eig_a : 𝓕 a = a       -- a is +1-Fourier-eigenfunction
theorem eig_b : 𝓕 b = -b      -- b is -1-Fourier-eigenfunction
theorem a_zero : a 0 = -8640·I/π
theorem b_zero : b 0 = 0
theorem g_real, g_real_fourier : both real-valued
theorem g_nonpos_of_norm_sq_ge_two, fourier_g_nonneg : sign conditions
theorem scaledMagic_cohnElkies₁'/₂' : packaged Cohn–Elkies conditions
```

---

## Part 1: Mathlib API Audit

The single most impactful analysis: where does the project hand-roll things mathlib already has, or use an API-poor mathlib choice where an API-rich one is available?

### Audit Finding 1: `IteratedDeriv_smul` duplicates mathlib's `iteratedDeriv_const_smul_field`
- **Location**: `ModularForms/QExpansionLemmas.lean:64–71`
- **Action**: Replace with `iteratedDeriv_const_smul_field` (`Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas`).
- **Saves**: ~8 lines. **Difficulty**: Low.

### Audit Finding 2: `exists_upper_bound_on_Icc` / `exists_lower_bound_pos_on_Icc` duplicate `IsCompact.exists_*`
- **Location**: `ForMathlib/DerivHelpers.lean:52–62`; callers at `MagicFunction/b/PsiBounds.lean:382,618,623,627`, `Integration/Measure.lean:241`, `DerivHelpers.lean:278`.
- **Action**: Inline `IsCompact.exists_bound_of_continuousOn isCompact_Icc …` (mathlib) at the 5 call sites; delete the wrappers.
- **Saves**: ~12 lines (plus uniformization with existing direct uses elsewhere). **Difficulty**: Low.

### Audit Finding 3: `Filter.eventually_atImInfty` is mathlib's `UpperHalfPlane.atImInfty_mem`
- **Location**: `ForMathlib/ModularFormsHelpers.lean:22–26`; 4 callers (`ResToImagAxis.lean:80,229,276`, `MagicFunction/b/Schwartz/Basic.lean:1213`).
- **Action**: Delete the wrapper; switch callers to `UpperHalfPlane.atImInfty_mem _` (already used elsewhere in the project).
- **Saves**: ~5 lines. **Difficulty**: Low.

### Audit Finding 4: `D_isZeroAtImInfty_of_bounded` re-proves `D_tendsto_zero_of_isBoundedAtImInfty`
- **Location**: `ModularForms/Derivative/Basic.lean:256–275`. Comment in code already admits the duplication: *"This overlaps with `D_tendsto_zero_of_isBoundedAtImInfty`; kept for backward compatibility."*
- **Action**: Replace the body with the Tendsto version (defeq via `IsZeroAtImInfty = Tendsto _ _ (𝓝 0)`).
- **Saves**: ~14 lines. **Difficulty**: Low.

### Audit Finding 5: `tendsto_resToImagAxis_atImInfty` uses ε–δ instead of `Tendsto.comp`
- **Location**: `ModularForms/ResToImagAxis.lean:75–87`
- **Action**: Replace 11-line ε–δ block with `hF.comp (Tendsto (·) atTop atImInfty)`. Pattern already used cleanly at `JacobiTheta/DeltaIdentity.lean:138,182,225`.
- **Saves**: ~10 lines. **Difficulty**: Medium.

### Audit Finding 6: `E₂_isZeroAtImInfty_sub_one` ε–δ in `EisensteinBase.lean`
- **Location**: `ModularForms/EisensteinBase.lean:373–410` (38 lines).
- **Action**: Reformulate as `Tendsto E₂ atImInfty (𝓝 1)` via `Real.exp_neg_atTop_nhds_zero.comp tendsto_im_atImInfty` + tsum-norm bound.
- **Saves**: ~25 lines. **Difficulty**: Medium.

### Audit Finding 7: `isBoundedAtImInfty_of_tendsto` rebuilds a standard fact
- **Location**: `ModularForms/FG/L10OverAsymptotics.lean:254–268`
- **Action**: Replace 15-line body with `BoundedAtFilter.of_tendsto h` or `(h.norm).isBoundedUnder_le`.
- **Saves**: ~15 lines. **Difficulty**: Low–Medium (mathlib lemma name uncertain — needs verification).

### Audit Finding 8: `iteratedDeriv_eq_of_hasDerivAt_succ` / `contDiff_of_hasDerivAt_succ`
- **Location**: `ForMathlib/DerivHelpers.lean:97–111`
- **Action**: Likely shrinkable to 1–2 lines using `contDiff_of_differentiable_iteratedDeriv` (already used) plus standard `iteratedDeriv_succ` machinery.
- **Saves**: ~15 lines if direct equivalent exists. **Difficulty**: Medium (uncertain — needs loogle).

### Audit Finding 9: Missing `@[fun_prop]` tags on ~20 `_contDiff` / `_holo` lemmas (HIGH LEVERAGE)
- **Locations**: Across `MagicFunction/a/Schwartz/Basic.lean` (lines 226, 236, 250, 260, 264, 275, 279, 283, 295, 303, 311, 1756, 1791, 1828, 1971), `b/Schwartz/Basic.lean`, `ModularForms/Derivative/SerreD.lean:61`, `Derivative/Basic.lean:41`, `FG/Basic.lean:110,116,122`.
- **Action**: Add `@[fun_prop]` to each named `Continuous`/`ContDiff`/`Differentiable`/`MDifferentiable` lemma about a project-defined function. Currently downstream uses write manual `.comp`/`.mul` chains in `IntegralLemmas.lean`, `tendsto_top_phi2`, etc.
- **Impact**: Each tag unlocks automated discharge in 5–10 caller sites. **Difficulty**: Low (mechanical).

### Audit Finding 10: `_def` / `_eq` simp lemmas use eta-expanded form
- **Location**: `MagicFunction/a/Schwartz/Basic.lean:93–97` (`Φᵢ_def`), 136–141 (`Iᵢ_eq`), similar in `Cancellation.lean:1042`.
- **Action**: Rewrite as fully-applied `Φ₁ r t = …` instead of `Φ₁ r = fun t => …`. Mathlib's idiomatic `simp` form.
- **Difficulty**: Low.

### Audit Finding 11: Mixed `IsBounded` / `Bornology.IsBounded` usage
- **Location**: `CohnElkies/LPBound.lean:207,460,833,906,1097`, `Basic/PeriodicPacking/Aux.lean:389,408,412`.
- **Action**: Standardize on `Bornology.IsBounded` (or open `Bornology`).
- **Difficulty**: Low (consistency only).

### Audit Finding 12: Manual ε–δ in `tendsto_top_phi2`
- **Location**: `MagicFunction/a/Schwartz/Basic.lean:2456–2490` (35 lines).
- **Action**: Replace with `MeasureTheory.tendsto_integral_of_dominated_convergence` plus `Tendsto.comp`.
- **Saves**: ~20 lines. **Difficulty**: Medium.

### Audit Finding 13: `continuous_comp_upperHalfPlane_mk` re-derives `Continuous.upperHalfPlaneMk`
- **Location**: `Integration/Measure.lean:231–236`
- **Action**: Inline at call sites: `(hψT.comp (hz.upperHalfPlaneMk him)).congr …`.
- **Difficulty**: Low.

### Audit Finding 14: `tendsto_im_atImInfty` could use `tendsto_comap_iff` + mathlib's `tendsto_coe_atImInfty`
- **Location**: `ForMathlib/ModularFormsHelpers.lean:28–31`
- **Action**: Shorten proof, or upstream to mathlib.
- **Difficulty**: Low.

### Audit Finding 15: `Filter.limUnder_eq_iff` chain in `qExpansion_smul2`
- **Location**: `ModularForms/QExpansionLemmas.lean:80–100` (20-line block).
- **Action**: Rewrite via `Tendsto.const_mul` + `Periodic.cuspFunction_apply_of_tendsto` (or similar).
- **Saves**: ~10 lines. **Difficulty**: Medium.

**Audit subtotal**: ~150 lines saved, plus large qualitative gains from `fun_prop` tagging and replacing 4+ hand-rolled ε–δ blocks with idiomatic `Tendsto.comp`.

---

## Part 2: Moral Duplications

Pairs of lemmas/definitions that prove or define essentially the same thing in slightly different ways.

### Dup Finding 1: `pow_mul_exp_neg_pi_bounded` is a special case of `exists_bound_pow_mul_exp_neg_mul`
- **A**: `MagicFunction/a/Schwartz/Basic.lean:834` (specializes `b = π`).
- **B**: `MagicFunction/b/PsiBounds.lean:399` (general `b > 0`).
- **Action**: Delete A; replace its single use with `B (k := k) (b := π) Real.pi_pos`.
- **Saves**: ~20 lines. **Difficulty**: Low.

### Dup Finding 2: `decay'` for `I₁'` re-derives `exists_bound_pow_mul_exp_neg_mul` inline
- **Location**: `MagicFunction/a/Schwartz/Basic.lean:1445–1455`
- **Action**: Replace inline `obtain ⟨Cpow, hCpow⟩` block with `obtain ⟨Cpow, hCpow⟩ := exists_bound_pow_mul_exp_neg_mul (k := k) (b := 1) one_pos`.
- **Saves**: ~10 lines. **Difficulty**: Low.

### Dup Finding 3: `SmoothI24Common.coeff` and `SmoothJ24Common.coeff` are character-identical
- **A**: `MagicFunction/a/Schwartz/Basic.lean:1669` ; **B**: `MagicFunction/b/Schwartz/Basic.lean:785`
- **Action**: Promote to `Integration/Measure.lean` (`SmoothIntegralCommon`); both `SmoothI24Common`/`SmoothJ24Common` open it.
- **Saves**: ~8 lines. **Difficulty**: Low.

### Dup Finding 4: `integral_phase_gaussian` is `integral_phase_gaussian_even (k := 4)`
- **A**: `MagicFunction/a/Eigenfunction/FourierPermutations.lean:222`. **B**: `ForMathlib/DerivHelpers.lean:447`.
- **Action**: Delete A; rewrite its single caller to use B at `k := 4`. (B-side already uses B directly.)
- **Saves**: ~8 lines. **Difficulty**: Low.

### Dup Finding 5: `integral_rexp_neg_pi_mul_sq_norm` defined twice
- **A**: `MagicFunction/a/Eigenfunction/FourierPermutations.lean:525`. **B**: `MagicFunction/b/Eigenfunction/FourierPermutations.lean:133`.
- **Action**: Delete one (promote to `ForMathlib`).
- **Saves**: ~4 lines. **Difficulty**: Low.

### Dup Finding 6: `I₁_apply`–`I₆_apply` / `J₃_apply`–`J₆_apply` restate `fCut_apply_of_nonneg`
- **A**: `MagicFunction/a/Eigenfunction/FourierPermutations.lean:119–130`. **B**: `MagicFunction/b/Eigenfunction/FourierPermutations.lean:918–929`.
- **Action**: Either inline `simp [Xⱼ, fCut_apply_of_nonneg, sq_nonneg]` at call sites or extract a generic `radial_apply` from `RadialSchwartz.Bridge`.
- **Saves**: ~24 lines. **Difficulty**: Low–Medium.

### Dup Finding 7: `I6Smooth` re-derives `IntegralEstimates.I₆` machinery
- **Location**: `MagicFunction/a/Schwartz/Basic.lean:1892–1976` vs `IntegralEstimates.I₆` at lines 1502, 1504, 1509, 1531.
- **Action**: Route `I6Smooth` through `SmoothIntegralIciOne` (already partially bridged via `gN_eq_sharedGN`); remove the redundant `coeff`/`gN`/measurability/integrability.
- **Saves**: ~40 lines. **Difficulty**: Medium.

### Dup Finding 8: `J5Smooth.exists_bound_norm_ψI'_z₅'` mirrors `exists_bound_norm_ψT'_z₁'_of`
- **A**: `MagicFunction/b/Schwartz/Basic.lean:479–490`. **B**: `MagicFunction/b/PsiBounds.lean:470–486`.
- **Action**: Generalize B over the parametrisation `z`; invoke from both sites. Same applies to `continuousOn_ψT'_z₁'_of`.
- **Saves**: ~14 lines. **Difficulty**: Low.

### Dup Finding 9: `J5Change.g` (b-side) and `I₅.g` (a-side) parallel change of variables
- **A**: `MagicFunction/a/Eigenfunction/FourierPermutations.lean:47–61`. **B**: `MagicFunction/b/Eigenfunction/FourierPermutations.lean:935–990`.
- **Action**: Extract shared "inverse change of variables for an `I/J₅`-style integral over `Ioc 0 1`" lemma.
- **Saves**: ~30–40 lines. **Difficulty**: Medium.

### Dup Finding 10: `fourier_eq_curveIntegral_segment_of` is a special case of `fourier_J_eq_curveIntegral_of`
- **A**: `MagicFunction/a/Eigenfunction/FourierPermutations.lean:802–827`. **B**: `MagicFunction/b/Eigenfunction/FourierPermutations.lean:480–524`.
- **Action**: Delete A; have its two callers invoke B directly.
- **Saves**: ~28 lines. **Difficulty**: Medium.

### Dup Finding 11: `ψT'_z₁'_eq` and `ψI'_z₅'_eq` share their proof skeleton
- **A**: `MagicFunction/b/Schwartz/Basic.lean:278`. **B**: `MagicFunction/b/Schwartz/Basic.lean:454`.
- **Action**: Factor a private helper `aux_ψZ_eq` taking the modular relation `ψ_? z = ψS (g • z) * (z + s)^k`.
- **Saves**: ~15–25 lines. **Difficulty**: Medium.

### Dup Finding 12: `decay_J₁'_norm_gN_bound` and `decay_J₅'_norm_gN_bound` are bit-for-bit identical mod 3 hypotheses (HIGH LEVERAGE)
- **A**: `MagicFunction/b/Schwartz/Basic.lean:338–367`. **B**: `MagicFunction/b/Schwartz/Basic.lean:521–550`.
- **Action**: Extract `decay_J_norm_gN_bound_of` parametrized by `(z, ψ, modular_rewrite)`. Their parents `decay_J₁'` / `decay_J₅'` (lines 370–403 and 553–587) also share ~30 lines of tail proof.
- **Saves**: ~50–60 lines. **Difficulty**: Medium.

### Dup Finding 13: `J1Smooth` and `J5Smooth` are structural twins (HIGHEST LEVERAGE)
- **Location**: `MagicFunction/b/Schwartz/Basic.lean:251–407` (J1Smooth) vs lines 412–591 (J5Smooth).
- **Action**: Build a single `J15Common` skeleton (parametrized over `z, ψ`, modular rewrite, `ψS` bound), specialize twice. Mirrors the existing `SmoothJ24Common` pattern.
- **Saves**: ~80–100 lines. **Difficulty**: Medium–High.

### Dup Finding 14: Local `def μ` aliases in `J1`/`J5`/`J6Smooth` reduplicate measure setup
- **Location**: `MagicFunction/b/Schwartz/Basic.lean:99–100, 261, 423`
- **Action**: Drop local `def μ` aliases; use `μIciOne`/`μIoo01` directly throughout. Or hoist the `attribute [irreducible]` + `IsFiniteMeasure` instance into `Integration/Measure.lean`.
- **Saves**: ~8 lines. **Difficulty**: Low.

### Dup Finding 15: `f0` strip contour (a-side) re-derives generic `rect_deform_of_tendsto_top` (b-side)
- **A**: `MagicFunction/a/Schwartz/Basic.lean:2210–2360` (a-side concrete `f0` + `rect_f0` + `strip_identity_f0`).
- **B**: `MagicFunction/b/Schwartz/Basic.lean:597–695` (`Complex.hzero` + `rect_deform_of_tendsto_top` generic).
- **Action**: Refactor a-side `rect_f0`/`strip_identity_f0` to invoke B's generic packaging.
- **Saves**: ~30–50 lines. **Difficulty**: Medium–High.

**Duplications subtotal**: ~350–450 lines saveable. Top 3 by leverage: Finding 13 (J1/J5 twin collapse, ~100 lines), Finding 12 (decay parallel collapse, ~55 lines), Finding 7 (I6Smooth merge, ~40 lines).

---

## Part 3: Generalization Opportunities

Declarations stated at a specific type when the proof works more generally.

### Gen Finding 1: `integral_gaussian_rexp` / `integrable_gaussian_rexp` (dim-8 specialization)
- **Location**: `ForMathlib/DerivHelpers.lean:466, 471`
- **Action**: Delete; the file already has `integral_gaussian_rexp_even` for `Fin (2*k)`. Use that at `k := 4` at the 4 call sites (`MagicFunction/a/Eigenfunction/FourierPermutations.lean:174,177,215,528`, `b/.../FourierPermutations.lean:1166,1203`).
- **Difficulty**: Low.

### Gen Finding 2: `ae_norm_phase_le_one` — measure parameter unused
- **Location**: `ForMathlib/DerivHelpers.lean:352`
- **Action**: Inline at 4 call sites as `(norm_phase_eq_one _ _).le |>.eventually`, or generalize to take `(μ : Measure V)` explicitly.
- **Difficulty**: Low.

### Gen Finding 3: `nonneg_of_nonneg_le_mul` hardcoded to `ℝ`
- **Location**: `ForMathlib/DerivHelpers.lean:92` (5 call sites).
- **Action**: Generalize to `{α : Type*} [LinearOrderedSemifield α]`, or inline `nonneg_of_mul_nonneg_left (ha.trans h) hb` at each site.
- **Difficulty**: Low.

### Gen Finding 4: `abs_le_abs_add_of_mem_ball` could be normed-group version
- **Location**: `ForMathlib/DerivHelpers.lean:80`
- **Action**: Replace `|·|` (real abs) with `‖·‖` over `SeminormedAddCommGroup`. Mathlib may already have it (`Metric.norm_le_of_mem_ball`).
- **Difficulty**: Low.

### Gen Finding 5: `Continuous.integral_zero_iff_zero_of_nonneg` carries unused `NormedAddCommGroup E`
- **Location**: `CohnElkies/LPBound.lean:692`
- **Action**: Drop the `[NormedAddCommGroup E]` constraint from the section variables (only `[TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]` and the measure-positivity instances are actually used).
- **Difficulty**: Low.

### Gen Finding 6: `exists_upper_bound_on_Icc` / `exists_lower_bound_pos_on_Icc` → mathlib
- **Location**: `ForMathlib/DerivHelpers.lean:52, 59`
- **Action**: See Audit Finding 2. Use `IsCompact.exists_isMaxOn` / `IsCompact.exists_forall_le'` from mathlib directly.
- **Difficulty**: Low.

### Gen Finding 7: `integrableOn_pow_mul_exp_neg_mul_Ici` could generalize lower bound `1` → arbitrary `a > 0`
- **Location**: `ForMathlib/DerivHelpers.lean:43`
- **Action**: Generalize signature to `(n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) → IntegrableOn … (Set.Ici a) volume`.
- **Difficulty**: Low.

### Gen Finding 8: `coordCube` / `cubeLattice` family — NEGATIVE FINDING
- **Location**: `CohnElkies/LPBound.lean:127–229`
- **Status**: Already maximally general over `d : ℕ` within the `EuclideanSpace ℝ (Fin d)` framework. No easy win.

### Gen Finding 9: `prod_muIoc01_eq_restrict` wraps `Measure.prod_restrict`
- **Location**: `Integration/Measure.lean:129`
- **Action**: Inline at the single call site (`a/Eigenfunction/FourierPermutations.lean:479`) using `Measure.prod_restrict` directly.
- **Difficulty**: Low.

### Gen Finding 10: `Filter.eventually_atImInfty` / `tendsto_im_atImInfty` already maximally general
- **Status**: NEGATIVE — likely already in mathlib under `UpperHalfPlane.atImInfty_mem` / `UpperHalfPlane.tendsto_im_atImInfty`. Audit / upstream.

### Gen Finding 11: `iteratedDeriv_eq_of_hasDerivAt_succ` / `contDiff_of_hasDerivAt_succ` hardcoded to `ℝ`
- **Location**: `ForMathlib/DerivHelpers.lean:97, 106`
- **Action**: Generalize to `{𝕜 : Type*} [NontriviallyNormedField 𝕜]`.
- **Difficulty**: Medium (uncertain — needs verifying mathlib's `contDiff_of_differentiable_iteratedDeriv` is generic).

### Gen Finding 12: `decay_iteratedFDeriv_mul_of_bound_left` codomain `ℂ` → `NormedField`
- **Location**: `ForMathlib/DerivHelpers.lean:157`
- **Action**: Generalize to `{𝕜 : Type*} [NormedField 𝕜] [NormedSpace ℝ 𝕜]`.
- **Difficulty**: Medium.

**Generalizations subtotal**: ~30–50 lines saveable (mostly via deletion/inlining), plus reusable API for downstream callers.

---

## Part 4: API Improvements (Top 5)

Highest-leverage missing API additions.

### API Finding 1: `J1Smooth`/`J5Smooth` consolidation (LARGEST DEDUP OPPORTUNITY)
- **Pattern repeated in**: `b/Schwartz/Basic.lean` `J1Smooth` (lines 251–407, ~156 lines) and `J5Smooth` (lines 412–591, ~179 lines). Both define `μ, coeff, hf, gN, coeff_norm_le, continuous_coeff, continuousOn_hf, exists_bound_norm_hf, hasDerivAt_integral_gN, decay_J?'_norm_gN_bound, contDiff_J?', decay_J?'`. The two blocks differ only in `(z, ψ, modular_rewrite)`.
- **Proposed**: A `J15Common` namespace mirroring `SmoothJ24Common`, packaging `(z, ψ, modular_rewrite)`.
- **Total savings**: ~120–150 lines. **Difficulty**: Medium.

### API Finding 2: Add `@[fun_prop]` to `continuous_z₁'`–`continuous_z₅'` (HIGHEST LEVERAGE PER MINUTE)
- **Location**: `MagicFunction/IntegralParametrisations.lean:164–181`
- **Justification**: 27 call sites. Smoking gun at `b/Schwartz/Basic.lean:299, 447, 448` — the author writes `have := continuous_z₁'; unfold coeff; fun_prop` because `fun_prop` cannot find these lemmas.
- **Risk**: Low (canonical `fun_prop` setup).

### API Finding 3: Add `@[simp]` to `im_z₂'_eq_one`, `im_z₄'_eq_one`
- **Location**: `MagicFunction/IntegralParametrisations.lean:56, 58`
- **Justification**: Top-level `(z₂' t).im = 1` (no hypothesis); 20 callers use `by simpa using im_z₂'_pos_all t` workaround.
- **Risk**: Low — RHS `1` strictly simpler than LHS.

### API Finding 4: Rename `aux_3, aux_5, aux_6, aux_8, aux_10, aux_11` and mark `private`
- **Location**: `MagicFunction/a/Schwartz/Basic.lean:393–432` (and uses at 461, 464, 468, 471, 479, 491–493, 502, 519, all inside `DivDiscBoundOfPolyFourierCoeff`).
- **Justification**: The numeric gaps (`3, 5, 6, 8, 10, 11`) hint at historical removals. Renamed names like `summable_fouterm_shifted`, `tprod_one_sub_rexp_neg_pi_pos`, etc., make the proof readable.
- **Risk**: Low (pure readability).

### API Finding 5: Consider `@[fun_prop]` on `φ₀''_holo`, `φ₂''_holo`, `Φᵢ'_holo`, `Φᵢ'_contDiffOn_ℂ`
- **Location**: `a/Schwartz/Basic.lean:226, 236, 250, 264, 260, 275, 283`
- **Justification**: 40+ usages across project, almost all writing manual `.continuousOn.comp` chains. `DifferentiableOn ℂ f ℍ₀` on a fixed set is a less canonical `fun_prop` setup — try on one lemma first and benchmark.
- **Risk**: Medium — benchmark before mass-applying.

**Non-findings**: `Submodule.E8` companion lemmas are subsumed by `Submodule` API; `coordCube`/`cubeLattice` already have all needed instances; `IsFiniteMeasure μ` instances are declared at each `Smooth` namespace; `fCutSchwartz`/`fCut_apply_of_nonneg` boilerplate is explicit by design.

---

## Part 5: Junk / Removable

Concrete dead code, wrappers, and duplicates with grep evidence.

### Junk Tier 1 (≥10 lines each, Low risk)

**Junk Finding 1**: `IsCuspForm.lean:32–57` — 5 unused mathlib aliases (`ModForm_mk`, `CuspForm_to_ModularForm`, `IsCuspForm_to_CuspForm`, `CuspForm_to_ModularForm_Fun_coe`, `CuspFormSubmodule`). Project-wide external uses: 0. **Delete ~30 lines.**

**Junk Finding 13**: `ResToImagAxis.lean:89–101` — three dead `@[grind =]` lemmas `resToImagAxis_im_{add,mul,smul}`. No call sites. **Delete ~13 lines.**

**Junk Finding 8**: `Derivative/Basic.lean:259–275` — `D_isZeroAtImInfty_of_bounded` and `D_tendsto_zero_of_isBoundedAtImInfty` are acknowledged duplicates in the codebase itself. Consolidate. **Save ~15 lines.** (See also Audit Finding 4.)

### Junk Tier 2 (5–10 lines, Low risk)

**Junk Finding 6**: `QExpansionLemmas.lean:64` — `IteratedDeriv_smul`, single-use, 8 lines. Inline. (See Audit Finding 1.)
**Junk Finding 3**: `MultipliableLemmas.lean:52` — `tprod_ne_zero`, dead public helper, 7 lines.
**Junk Finding 7**: `QExpansionLemmas.lean:110` — `cuspFunction_congr_funLike`, single-use, 5 lines.
**Junk Finding 5**: `QExpansionLemmas.lean:59` — `qExpansion_mul_coeff`, dead docstring-advertised wrapper, 5 lines.
**Junk Finding 2**: `MultipliableLemmas.lean:22` — `Complex.summable_nat_multipliable_one_add`, single-use TODO wrapper, 5 lines.

### Junk Sub-Tier (≤4 lines each)

- **Finding 4**: `Multipliable_pow` (`MultipliableLemmas.lean:60`) — borderline; 1-line body.
- **Finding 9**: `tendsto_rpow_mul_resToImagAxis_of_isBigO_exp` (`ResToImagAxis.lean:255`) — used once internally; mark `private`.
- **Finding 10**: Stale docstring bullet `cuspForm_rpow_mul_resToImagAxis_tendsto_zero` (`ResToImagAxis.lean:25`) — lemma deleted, bullet remains.
- **Finding 11**: `modular_negI_smul` (`SlashActionAuxil.lean:78`) — single internal use, not `private`.
- **Finding 12**: `ResToImagAxis.Pos.add` (`ResToImagAxis.lean:187`) — dead public helper; superseded by `EventuallyPos.add`.
- **Finding 14**: `hasDerivAt_re_resToImagAxis` (`AntiSerreDerPos.lean:75`) — single-file public wrapper.
- **Finding 18**: `serre_D_eq` (`SerreD.lean:37`) — `rfl` wrapper, single use.
- **Finding 19**: `MDifferentiableAt_DifferentiableAt` (`Derivative/Basic.lean:34`) — 1-line bridge.
- **Finding 20**: `deriv_num`, `deriv_moebius`, `deriv_denom_zpow` (`SlashFormula.lean:30–77`) — visibility-only fix (`private`).

### Notes on workaround code

- **`ForMathlib/DerivHelpers.lean:32–40`** contains explicit v4.29.1 workarounds (`instance : ContinuousSMul ℝ ℂ` and `ContDiffOn.restrict_scalars_C_to_R`). On v4.30.0-rc2 with mathlib master, these *may* now be obsolete — requires a `lake build` test with them removed.
- **No `sorry`, `#check`, `#print`, `FIXME`, or commented-out code blocks anywhere in `SpherePacking/`.** The only `TODO` is on `MultipliableLemmas.lean:22` (Junk Finding 2).

**Junk subtotal**: ~115–140 lines safely deletable.

---

## Recommended Action Plan

### Priority 1 — Quick Wins (≤1 hour each, can do today)

| Action | Saves | Difficulty |
|---|---|---|
| Add `@[fun_prop]` to `continuous_z₁'`–`continuous_z₅'` (API #2) | qualitative | 5 min |
| Add `@[simp]` to `im_z₂'_eq_one`, `im_z₄'_eq_one` (API #3) | small but unlocks `simp` | 5 min |
| Delete `IsCuspForm.lean` mathlib aliases (Junk #1) | 30 | 10 min |
| Delete `resToImagAxis_im_{add,mul,smul}` (Junk #13) | 13 | 5 min |
| Inline single-use `IteratedDeriv_smul`, `cuspFunction_congr_funLike`, etc. (Junk #2,3,5,6,7) | 30 | 30 min |
| Delete `integral_gaussian_rexp` / `integrable_gaussian_rexp` dim-8 (Gen #1, Dup #5) | 8 | 15 min |
| Delete `integral_phase_gaussian` (a-side) (Dup #4) | 8 | 10 min |
| Replace `pow_mul_exp_neg_pi_bounded` with general version (Dup #1) | 20 | 10 min |
| Replace `exists_upper_bound_on_Icc` callers with `IsCompact.exists_*` (Audit #2, Gen #6) | 12 | 30 min |
| Drop docstring bullet `cuspForm_rpow_mul_resToImagAxis_tendsto_zero` (Junk #10) | 1 | 1 min |

**Priority 1 total**: ~125 lines saved + significant `fun_prop`/`simp` automation gains. **Time**: ~2.5 hours.

### Priority 2 — API Improvements (significant impact)

| Action | Saves | Difficulty |
|---|---|---|
| Add `@[fun_prop]` to ~20 `_contDiff`/`_holo` lemmas (Audit #9, API #5) | qualitative | 1–2 hours |
| Rename + `private` the `aux_*` helpers in `DivDiscBound` (API #4) | 0 (readability) | 30 min |
| Migrate `D_isZeroAtImInfty_of_bounded` callers to `D_tendsto_zero_*` (Audit #4, Junk #8) | 14 | 30 min |
| Add `I₁_apply`–`I₆_apply` `@[simp]` and `Φ₅_def` (API #5) | small | 15 min |
| Delete duplicate `integral_rexp_neg_pi_mul_sq_norm` (Dup #5) | 4 | 5 min |
| Promote `SmoothI24Common.coeff` = `SmoothJ24Common.coeff` to shared (Dup #3) | 8 | 15 min |

**Priority 2 total**: ~30 lines + large qualitative gains. **Time**: ~3 hours.

### Priority 3 — Generalizations (mathematical thought)

| Action | Saves | Difficulty |
|---|---|---|
| Drop unused `NormedAddCommGroup E` from `Continuous.integral_zero_iff_zero_of_nonneg` (Gen #5) | trivial | 15 min |
| Generalize `nonneg_of_nonneg_le_mul` to `LinearOrderedSemifield` (Gen #3) | trivial | 15 min |
| Generalize `iteratedDeriv` helpers to `NontriviallyNormedField` (Gen #11) | trivial | 30 min |
| Generalize `integrableOn_pow_mul_exp_neg_mul_Ici` to `Ici a` (Gen #7) | small | 15 min |
| Generalize `decay_iteratedFDeriv_mul_of_bound_left` codomain (Gen #12) | small | 1 hour |
| Replace ε–δ in `tendsto_resToImagAxis_atImInfty` with `Tendsto.comp` (Audit #5) | 10 | 1 hour |
| Reformulate `E₂_isZeroAtImInfty_sub_one` as `Tendsto` (Audit #6) | 25 | 1.5 hours |
| Refactor `tendsto_top_phi2` to use DCT (Audit #12) | 20 | 1.5 hours |
| Rewrite `Filter.limUnder` block in `qExpansion_smul2` (Audit #15) | 10 | 1 hour |

**Priority 3 total**: ~65 lines + better API surface for downstream callers. **Time**: ~7 hours.

### Priority 4 — Structural Changes (major refactoring)

| Action | Saves | Difficulty |
|---|---|---|
| **Consolidate `J1Smooth`/`J5Smooth` into `J15Common`** (Dup #13, API #1) | 120–150 | Medium — 3–4 hours |
| Collapse `decay_J₁'_norm_gN_bound` / `decay_J₅'_norm_gN_bound` (Dup #12) | 50–60 | Medium — 2 hours |
| Merge `I6Smooth` with `IntegralEstimates.I₆` (Dup #7) | 40 | Medium — 2 hours |
| Extract `J5Change` change-of-variables to shared (Dup #9) | 30–40 | Medium — 2 hours |
| Delete `fourier_eq_curveIntegral_segment_of`, use generic version (Dup #10) | 28 | Medium — 1 hour |
| Refactor a-side `f0` strip contour to use `rect_deform_of_tendsto_top` (Dup #15) | 30–50 | Medium–High — 3 hours |
| Generalize parametric `ψT'_z₁'_eq` / `ψI'_z₅'_eq` (Dup #11) | 15–25 | Medium — 1 hour |

**Priority 4 total**: ~330–400 lines. **Time**: ~14 hours.

---

## Aggregate Impact

| Priority | Lines saved | Time | Risk |
|---|---|---|---|
| P1 (Quick wins) | ~125 | ~2.5h | Low |
| P2 (API improvements) | ~30 + qualitative | ~3h | Low |
| P3 (Generalizations) | ~65 | ~7h | Medium |
| P4 (Structural refactors) | ~330–400 | ~14h | Medium |
| **Total** | **~550–620 lines** (~2–2.5% further reduction) | ~26h | — |

The project is already mathlib-quality in its broad strokes (no sorries, axiom-clean, well-structured, post-cleanup). The remaining work is overwhelmingly about **idiom alignment** (`fun_prop` tags, `Tendsto.comp` over ε–δ, `IsCompact.exists_*` over `Icc` wrappers) and **finishing the `a`/`b` parameterisation** (J1/J5 collapse mirrors what's already done for J2/J4).

### Highest-leverage next move

If you can only do one thing: **Add `@[fun_prop]` to the five `continuous_z_i'` lemmas in `MagicFunction/IntegralParametrisations.lean`.** It is a 5-minute change, has direct evidence of being needed (manual `have := continuous_z₁'; … fun_prop` workarounds), and unlocks downstream automation across ~20 call sites.

If you have one afternoon: **execute Priority 1 in full** (~125 lines saved, ~2.5 hours, low risk).

If you have a week: **Priority 1 + Priority 4 J15Common refactor** (~275 lines saved, demonstrates the abstraction pattern already established by `SmoothJ24Common`).
