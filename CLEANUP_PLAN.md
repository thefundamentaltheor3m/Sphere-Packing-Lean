# Sphere-Packing-Lean Cleanup Plan (Ambitious / Mathlib-Quality)

## Context

The gauss2-cleanup branch (PR #391) is a working copy of the Gauss E8 optimality formalization. Goal: make this mathlib-quality with clean, reusable API. The project has 169 files, ~59,400 lines, ~2,200 declarations, zero sorries.

The duplication analysis found **~5,000-6,000 lines** of saveable code, primarily from:
- a/ vs b/ parallel module structure (~2,000+ lines)
- Internal I1-I6 / J1-J6 repetition (~1,000+ lines across both)
- Laplace A vs B parallel development (~600 lines)
- Dead code (~1,200 lines -- much more than initially estimated)

---

## Phase 1: Dead Code Removal (~1,200 lines saved)

### 1a: Delete dead files (15 files, ~1,161 lines)

Confirmed dead via grep: zero external references to any declaration in these files.

| File | Lines | Reason |
|------|-------|--------|
| `ForMathlib/Asymptotics.lean` | 50 | Trivial wrappers around `IsBigO.mul`/`IsBigO.pow` |
| `ForMathlib/Cardinal.lean` | 14 | Single `rfl` lemma, unused |
| `ForMathlib/Finsupp.lean` | 10 | `linearCombination_eq_sum` unused |
| `ForMathlib/InnerProductSpace.lean` | 35 | 4 lemmas, none used outside file |
| `ForMathlib/Real.lean` | 13 | `rpow_ne_one` unused |
| `ForMathlib/Vec.lean` | 28 | `cons_val_five/six/seven` unused |
| `ForMathlib/Fourier.lean` | 61 | `HasFourierSeries`, `Has2PiFourierSeries` -- 0 external uses |
| `ForMathlib/InvPowSummability.lean` | 327 | 0 external references to any declaration |
| `ModularForms/uniformcts.lean` | 79 | All declarations commented out |
| `ModularForms/riemannZetalems.lean` | 35 | Duplicates `Cauchylems.lean:26` |
| `ModularForms/Cauchylems.lean` | 277 | 0 external references (all decls dead) |
| `ModularForms/Icc_Ico_lems.lean` | 76 | Only `Icc_succ` used, and only by dead `Cauchylems.lean` |
| `ModularForms/limunder_lems.lean` | 48 | All 5 declarations unused externally |
| `ModularForms/equivs.lean` | 48 | `negEquiv`, `succEquiv`, `swap_equiv` all unused; import only needed for transitive mathlib deps |
| `Tactic/NormNumI_Scratch.lean` | 60 | Not imported by anything |

For each: delete the file, remove from `SpherePacking.lean`, fix any importing files (replace with direct mathlib imports where needed, e.g. `equivs.lean`'s mathlib imports in `SummableLemmas/Basic.lean`).

Remove corresponding imports from `SpherePacking.lean` and any importing files.

### 1b: Delete unused declarations within files
- `E2.lean`: Delete `G₂`, `D₂` + 5 helpers (unused externally)
- `b/psi.lean`: Delete `ModularGroup.I`
- `Delta.lean`: Inline `CuspForm_apply` as `rfl`
- `DimensionFormulas.lean`: Delete `qExpansion_coe_smul`, `_cusp`, `_sub`
- `Segments.lean`: Delete `z₁line_def` through `z₄line_def` (redundant rfl simp)
- `FunctionsBoundedAtInfty.lean`: Delete `IsBoundedAtImInfty.neg` alias

### 1c: Inline trivial wrappers
- `DimensionFormulas.lean`: Inline `mcast_apply` -> `rfl`
- `a/Integrability/ComplexIntegrands.lean`: Inline `zero_not_mem_upperHalfPlaneSet` -> `by simp`

### 1d: Deduplicate definitions
- `CuspFormIsoModforms.lean` vs `DimensionFormulas.lean`: Keep `mul_Delta_map` + 4 companions in `CuspFormIsoModforms.lean`, delete dupes from `DimensionFormulas.lean`, add import
- Audit `RamanujanIdentities.lean` vs `Derivative.lean` for consolidation

**Verify**: `lake build`

---

## Phase 2: Naming Convention Fixes

### 2a: `ForMathlib/InvPowSummability.lean` (project-wide rename)
| Old | New |
|-----|-----|
| `Inv_Pow_Norm_Summable_Over_Set_Euclidean` | `invPowNormSummable` |
| `Exists_Inv_Pow_Norm_Summable_Over_Set_Euclidean` | `exists_invPowNormSummable` |
| `Summable_of_Inv_Pow_Summable` | `summable_of_invPowSummable` |
| `Summable_of_Inv_Pow_Summable'` | `summable_of_invPowSummable'` |
| `Summable_Inverse_Powers_of_Finite_Orbits` | `summable_inversePowers_of_finiteOrbits` |
| `IsDecayingMap` | `IsDecayingOn` (keep capital -- it is a def/predicate) |

Grep all occurrences project-wide and rename.

**Verify**: `lake build`

---

## Phase 3: Internal Deduplication within a/ (~520 lines saved)

### 3a: Create `a/Schwartz/SmoothI24Common.lean` (new, ~80 lines)
Extract the shared pattern from `SmoothI2.lean` (134 lines) and `SmoothI4.lean` (137 lines):
- Parameterize by `(z : R -> C)`, `(hz_continuous)`, `(hz_norm_le_two)`, `(hz_im_pos)`, `(prefactor : C)`
- Provide `contDiff_of_eq_I0_mul` and `decay_of_eq_I0_of_coeff_re_mul`
- Reduce SmoothI2 and SmoothI4 to ~15-line specializations
- **Saves ~180 lines**

### 3b: Create `a/IntegralEstimates/I24Common.lean` (new, ~200 lines)
Extract from `I2.lean` (277 lines) and `I4.lean` (236 lines):
- Parameterize by `(sign : C)` (+1 or -1) and `(param : R -> C)` (`t+I` or `-t+I`)
- Shared: `coeff`, `gN`, `coeff_norm_le`, `g_norm_bound_uniform`, `iteratedDeriv_eq_integral_gN`, `decay'`
- Reduce I2 and I4 to ~25-line specializations
- **Saves ~180 lines**

### 3c: Merge `I1.lean` and `I3.lean` bounding proofs
- Extract `bounding_aux_phase` parameterized by phase factor
- **Saves ~80 lines**

### 3d: Merge `PermI12FourierIntegrableI1/I2` shared kernel pattern
- Extract shared "slice integrability + norm bound" helper
- **Saves ~60-80 lines**

**Verify**: `lake build`

---

## Phase 4: Internal Deduplication within b/ (~520 lines saved)

Apply the same patterns as Phase 3 to the b/ module:

### 4a: b/ already has `SmoothJ24Common.lean` -- verify J2 and J4 are fully using it
- If not fully delegating, reduce further

### 4b: Create `b/IntegralEstimates/` shared abstractions (if not already factored)
- The b/ module may not have IntegralEstimates files in the same structure
- Audit and extract where applicable

### 4c: Merge `PermJ12FourierJ1Kernel` / `PermJ12FourierJ2` shared patterns
- Same "slice integrability + norm bound" helper as Phase 3d

### 4d: Factor `b/SpecialValues.lean` `J2'_J4_eq_neg_J6'_zero` (~254 lines)
- Extract the Cauchy-Goursat rectangle deformation into a reusable lemma

**Verify**: `lake build`

---

## Phase 5: Cross-Module a/ vs b/ Unification (~2,000 lines saved)

This is the biggest win. The a/ and b/ modules differ by only 3 atomic substitutions:
1. Modular form: `phi0''` (with Mobius) vs `psiT'`/`psiI'`/`psiS'`
2. Eigenvalue sign: +1 vs -1
3. Sign on integral 6: `+2` vs `-2`

### 5a: Create shared `MagicFunction/Common/` module

#### `Common/Definitions.lean` (~100 lines)
Parameterize the 6-integral structure:
```lean
structure MagicFunctionData where
  /-- The modular form for integrals 1-4 (on segments z1'-z4') --/
  modForm14 : C -> C
  /-- The modular form for integral 5 (on z5') --/
  modForm5 : C -> C
  /-- The modular form for integral 6 (on z6') --/
  modForm6 : C -> C
  /-- Sign prefactor for integral 6 --/
  sign6 : C  -- +2 or -2
  /-- Fourier eigenvalue --/
  eigenvalue : C  -- +1 or -1
```

Define generic versions of:
- `Phi_k'` (complex integrands) parameterized by `MagicFunctionData`
- `Phi_k` (real integrands via composition with `z_k'`)
- `I_k'` (scalar integrals)
- `radialSum` (the sum I1'+...+I6')
- `I_k` (radial functions on R^8)

#### `Common/SchwartzBasic.lean` (~150 lines)
The `Schwartz/Basic.lean` pattern (currently ~85% identical between a/ and b/):
- Generic smoothness/decay collection
- Generic `SchwartzIntegrals` construction (6 x `fCutSchwartz` + `schwartzMap_multidimensional`)
- Generic `FourierEigenfunctions` sum definition
- `eq_sum_integrals_RadialFunctions` and `_SchwartzIntegrals` theorems

#### `Common/FourierPermutations.lean` (~60 lines)
Parameterize by eigenvalue `epsilon`:
- `perm_12 : F(I1+I2) = epsilon*(I3+I4)`
- `perm_34 : F(I3+I4) = epsilon*(I1+I2)`
- `perm_56 : F(I5) = epsilon*I6, F(I6) = epsilon*I5`
- `eig : F(sum) = epsilon * sum`

#### `Common/ContourDeformation.lean` (~40 lines)
Both a/ and b/ use identical contour deformation on wedgeSet:
- `diffContOnCl_wedgeSet_of` (already exists in Contour/)
- `fderivWithin_scalarOneForm_wedgeSet_symm_of` (already exists)
- The perm_12_contour assembly is ~90% identical

#### `Common/FourierKernel.lean` (~80 lines)
Shared pattern for Fubini kernel integrability:
- Generic `permKernel` definition
- Generic `integrable_permKernel_slice`
- Generic `integral_norm_bound` (parameterized by the contour Gaussian parameter)

### 5b: Reduce a/ and b/ to thin specialization layers

Each a/ file becomes a ~15-30 line file that:
1. Instantiates `MagicFunctionData` with `phi0''`, +1, +2
2. Provides the modular-form-specific bounds (the ~20% that differs)
3. Delegates everything else to `Common/`

Each b/ file similarly instantiates with `psiT'`/`psiI'`/`psiS'`, -1, -2.

### 5c: Expected file changes
| Current a/ file | Action |
|----------------|--------|
| `a/Basic.lean` (409 lines) | Reduce to ~40 lines (instantiation + a_eq lemmas) |
| `a/Schwartz/Basic.lean` (470 lines) | Reduce to ~50 lines |
| `a/Eigenfunction/FourierPermutations.lean` (69 lines) | Reduce to ~15 lines |
| `a/Eigenfunction/PermI12ContourMain.lean` (56 lines) | Reduce to ~15 lines |
| `a/Eigenfunction/PermI12ContourAux.lean` (84 lines) | Reduce to ~20 lines |
| `a/Eigenfunction/PermI5Main.lean` (252 lines) | Reduce to ~40 lines |

Same reductions for corresponding b/ files.

**Verify**: `lake build`

---

## Phase 6: Laplace A/B Shared Abstractions (~600 lines saved)

### 6a: Generic Laplace convergence lemma (~100 lines saved)
Create `g/CohnElkies/LaplaceCommon.lean`:
```lean
theorem integrableOn_laplace_of_bounded_near_zero_exp_growth
    (kernel : R -> C)
    (h_near_zero : exists M, forall t in Ioc 0 1, ||kernel t|| <= M)
    (h_growth : exists C A, forall t >= A, ||kernel t|| <= C * exp(2*pi*t))
    (hu : 2 < u) :
    IntegrableOn (fun t => kernel t * exp(-pi*u*t)) (Ioi 0)
```

### 6b: Generic parametric-integral analyticity (~130 lines saved)
Create `g/CohnElkies/AnotherIntegral/ParametricAnalyticity.lean`:
```lean
theorem analyticOnNhd_parametric_laplace_exp
    (base : R -> C)
    (hbase_int : forall u > 0, IntegrableOn (fun t => base t * exp(-pi*u*t)) (Ioi 0))
    (hbase_mul_int : forall u > 0, IntegrableOn (fun t => t * base t * exp(-pi*u*t)) (Ioi 0)) :
    AnalyticOnNhd C (fun u => integral over Ioi 0 of base t * exp(-pi*u*t)) rightHalfPlane
```

### 6c: Generic analytic continuation wrapper (~125 lines saved)
Create `g/CohnElkies/AnotherIntegral/ContinuationGeneric.lean`:
- Absorbs the shared `ACDomain` + `frequently_eq_near_three` + `eqOn_of_preconnected` pattern

### 6d: Factor `bRadial_eq_laplace_psiI_main` (880 lines)
Extract the rectangle deformation into a `LaplaceB/TailDeformation.lean` module (matching a/'s architecture), reducing the main proof to ~150 lines.

**Verify**: `lake build`

---

## Phase 7: File Splitting (1000+ line files)

### 7a: Split `ModularForms/Derivative.lean` (1475 lines) into:
- `Derivative/Basic.lean` -- D operator definition, linearity, Leibniz
- `Derivative/SerreD.lean` -- Serre derivative definition and properties
- `Derivative/SlashFormula.lean` -- D_slash and E₂_slash
- `Derivative/Equivariance.lean` -- serre_D_slash_equivariant
- `Derivative/Ramanujan.lean` -- Ramanujan identities
- `Derivative/AntiSerreDerPos.lean` -- the monotonicity criterion

### 7b: Split `ModularForms/JacobiTheta.lean` (1338 lines) into:
- `JacobiTheta/Basic.lean` -- Theta₂/₃/₄ definitions and basic properties
- `JacobiTheta/SlashActions.lean` -- H₂/H₃/H₄ transformation formulas
- `JacobiTheta/Positivity.lean` -- imaginary-axis positivity
- `JacobiTheta/DeltaIdentity.lean` -- Delta_eq_H₂_H₃_H₄

### 7c: Split `MagicFunction/PolyFourierCoeffBound.lean` (905 lines) into:
- `PolyFourierCoeffBound/Basic.lean` -- DivDiscBound definition and main theorem
- `PolyFourierCoeffBound/AECoefficients.lean` -- A_E_sq_coeff computations
- `PolyFourierCoeffBound/Application.lean` -- norm_φ₀_le

**Verify**: `lake build`

---

## Phase 8: Mathlib Style Polish

### 8a: File naming (snake_case for all files)
Rename to mathlib conventions:
- `Cauchylems.lean` -> `CauchyLemmas.lean`
- `clog_arg_lems.lean` -> `ClogArgLemmas.lean`
- `exp_lems.lean` -> `ExpLemmas.lean`
- `limunder_lems.lean` -> `LimUnderLemmas.lean`
- `logDeriv_lems.lean` -> `LogDerivLemmas.lean`
- `multipliable_lems.lean` -> `MultipliableLemmas.lean`
- `tendstolems.lean` -> `TendstoLemmas.lean`
- `upperhalfplane.lean` -> `UpperHalfPlane.lean` (capitalize)
- `iteratedderivs.lean` -> `IteratedDerivs.lean`
- `Icc_Ico_lems.lean` -> `IccIcoLemmas.lean`
- `Eisensteinqexpansions.lean` -> `EisensteinQExpansions.lean`

### 8b: Add module docstrings
Every file should have a top-level `/-- ... -/` module docstring explaining its role.

### 8c: Ensure all public API has docstrings
Key theorems (`MainTheorem`, `LinearProgrammingBound`, `eig_a`, `eig_b`, `g_cohnElkies1`, `g_cohnElkies2`) should have clear docstrings.

**Verify**: `lake build`

---

## Execution Order & Commits

| Step | Phase | Commit message | Risk |
|------|-------|---------------|------|
| 1 | 1 (dead code) | `chore: remove dead code and unused declarations` | Low |
| 2 | 2 (naming) | `chore: fix naming conventions to mathlib style` | Low |
| 3 | 3 (a/ internal dedup) | `refactor: extract shared abstractions within MagicFunction/a` | Medium |
| 4 | 4 (b/ internal dedup) | `refactor: extract shared abstractions within MagicFunction/b` | Medium |
| 5 | 5 (a/ vs b/ unification) | `refactor: unify MagicFunction a/ and b/ via Common module` | High |
| 6 | 6 (Laplace shared) | `refactor: extract shared Laplace integral abstractions` | High |
| 7 | 7 (file splitting) | `refactor: split large files into focused modules` | Medium |
| 8 | 8 (style polish) | `style: mathlib naming and docstrings` | Low |

## Estimated Total Impact

| Phase | Lines saved (estimated) | Actual |
|-------|------------|--------|
| 1 (dead code + dedup defs) | ~1,200 | ✅ 1,227 |
| 2 (dedup defs) | ~75 | ✅ 245 |
| 3 (naming conventions + file renames) | 0 (rename only) | ✅ done |
| 4a (SmoothI24Common) | ~180 | ✅ ~20 (structural win) |
| 4b (I1/I3 bounding merge) | ~80 | (skipped - analysis overstated) |
| 4c (I2/I4 IntegralEstimates common) | ~180 | (not yet - heavy refactor) |
| 4d (Fourier kernel shared) | ~60-80 | (not yet) |
| 5 (a/ vs b/ unification) | ~2,000 | (not yet) |
| 6 (Laplace shared) | ~600 | (not yet) |
| 7 (file splitting) | 0 | (not yet) |
| 8 (style polish) | 0 | (not yet) |

## Actual Progress

- **33+ commits** on gauss2-cleanup (PR #391)
- Starting: 59,366 lines
- Current: 55,746 lines
- **Net: -3,620 lines** (~6.1% of project)
- All builds pass; no behavioral changes

### Cleanup completed in this session

10 commits on `gauss2-cleanup` (PR #391):
1. Phase 1a: delete 15 dead files (1,161 lines)
2. Phase 1b: delete unused declarations within files (36 lines)
3. Phase 1c: inline trivial wrappers (14 lines)
4. Phase 2a: deduplicate `mul_Delta_map` definitions (88 lines)
5. Phase 2b: remove dead `RamanujanIdentities.lean` (157 lines)
6. Phase 3: rename 12 files to mathlib naming conventions + sort imports
7. Phase 4a: extract `SmoothI24Common` for a/ SmoothI2/I4 (structural)
8. Documentation update
9. Phase 4b (partial): remove commented-out dead code blocks (135 lines)
10. Additional dead-code/inline cleanup (30 lines)

## Honest Assessment: Reaching 20k Lines

The target is ~37,000 lines reduction (from current 57,084 to 20,000).
This is beyond what mechanical cleanup can achieve. It requires:

1. **Mathematical proof rewriting**: The largest proofs in the project
   are ~200-900 lines each (`bRadial_eq_laplace_psiI_main` is 880 lines,
   `ramanujan_E₂'` is 195 lines, many others in the 100-400 range).
   Shortening these requires mathematical insight to find cleaner
   arguments.

2. **True a/ vs b/ module unification** (Phase 5 proper): Design a
   `MagicFunctionData` structure parameterizing:
   - The modular form (`phi0''` vs `psiT'/psiI'/psiS'`)
   - Eigenvalue sign (+1 vs -1)
   - Integral signs
   And rewrite ~150 declarations in both a/ and b/ to use it.

3. **Mathematical consolidation**: Many "parallel" proofs in a/ and b/
   differ only by sign/parametrization. Unifying them requires careful
   design of typeclass-based abstractions.

4. **Proof golfing by a mathematician**: The 1,276 public declarations
   and ~2,500 total declarations include many with 10-30 line proofs
   that could be 1-5 lines with better tactics/lemma choices.

Rough estimates of potential savings (per mathematician's focused work):
- Phase 5 full unification: 2,000-4,000 lines
- Phase 6 Laplace abstractions: 600-1,000 lines
- Large proof simplifications: 5,000-10,000 lines
- Mathematical API cleanup: 3,000-5,000 lines
- Total: ~15,000-20,000 lines achievable with focused mathematical work.

Even with aggressive cleanup, reaching exactly 20k lines from the
current Gauss formalization would likely require rewriting entire
sections. A more realistic target might be 35-40k lines.

## Remaining Work (for follow-up PRs)

- **Phase 5 full** (a/ vs b/ unification, ~2,000 lines): Design shared
  `MagicFunction/Common/` module with `MagicFunctionData` parameter.
- **Phase 6** (Laplace A/B shared abstractions, ~600 lines).
- **Phase 7** (split `Derivative.lean` 1475 lines, `JacobiTheta.lean`
  1338 lines, `PolyFourierCoeffBound.lean` 905 lines into sub-modules).
- **Phase 8** (mathlib style polish: docstrings, formatting).
- **Phase 9** (new): Aggressive proof golfing by a mathematician.
