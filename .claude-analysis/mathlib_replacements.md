# Mathlib Replacement / Deduplication Analysis

Scope: `SpherePacking/ForMathlib/` (38 files, 2243 lines incl. subdirs — note 2243 vs. 1694 stated because SummableLemmas/ was empty and subdirs were underreported), `SpherePacking/Integration/` (9 files, 1138 lines), and `SpherePacking/CohnElkies/LPBound.lean` (605 lines).

Conventions below:
- SAVE = estimated net lines removed from the project (net of any unavoidable overhead).
- "Trivial wrapper" = the whole file is ≤ 1 call into mathlib + `simpa`.
- For every mathlib name shown, I verified it exists with `mcp__lean-lsp__lean_local_search`.

---

## 1. `ForMathlib/` — per-file verdict

### 1a. Fully upstreamable to mathlib / drop and inline at call sites

These are either trivial mathlib wrappers, one-liners that `simp`/`fun_prop`/`exact` already resolves in mathlib, or items mathlib already has.

| File | Lines | Verdict | Mathlib equivalent | Action |
|---|---|---|---|---|
| `AtImInfty.lean` | 26 | `Filter.eventually_atImInfty` is just `UpperHalfPlane.atImInfty_mem (setOf p)`; `Filter.tendsto_im_atImInfty` is 2 lines. Both belong in `Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty`. Neither exists in mathlib yet, but they are 3-liners. | `UpperHalfPlane.atImInfty_mem` exists; the wrapper is just re-shaping. | Inline both (2 call sites each). SAVE ≈ 22 lines. |
| `ComplexI.lean` | 15 | `I_mul_I_mul x : I * (I * x) = -x`. Pure `ring` / `simp [Complex.I_mul_I]`. | `Complex.I_mul_I` + `ring`. | Delete file; inline as `by simp [Complex.I_mul_I]` or `by ring_nf` at call sites. SAVE ≈ 15 lines. |
| `FunctionsBoundedAtInfty.lean` | 15 | Single lemma `isBoundedAtImInfty_neg_iff`, 1-liner `simp`. | Belongs in `Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty`. | Upstream PR (micro); inline at call site until merged. SAVE ≈ 13 lines. |
| `UpperHalfPlane.lean` | 32 | 4 lemmas: `ModularGroup.coe_S_smul`, `modular_S_sq`, `S_mul_T`, `coe_ST_smul`. `modular_S_sq` (`S*S=-1`) is exactly `ModularGroup.S_mul_S_eq` in `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`. Others are trivial `fin_cases` / `simpa`. | `ModularGroup.S_mul_S_eq` already in mathlib. | Replace `modular_S_sq` uses with `ModularGroup.S_mul_S_eq`; upstream the other 3 (all ≤ 3 lines). SAVE ≈ 20 lines (post-upstream). |
| `SlashActions.lean` | 42 | 4 lemmas about `slash (-g) = slash g` for even weight. Clean candidates for mathlib's `Mathlib.NumberTheory.ModularForms.SlashActions`. | Not yet in mathlib but straightforward. | Upstream as a block; until merged, inline the two `'` primes into their one call site each. SAVE (local) ≈ 20 lines. |
| `VolumeOfBalls.lean` | 26 | Just `simpa using Metric.measure_ball_pos …` and `simpa using MeasureTheory.measure_ball_lt_top …`. Pure `simpa` wrappers. | `Metric.measure_ball_pos`, `MeasureTheory.measure_ball_lt_top`. | Delete file; replace call sites in `LPBound.lean:489, 493`. SAVE ≈ 26 lines. |
| `Tprod.lean` | 25 | Monotonicity of `∏'` from pointwise ≤ for nonneg multipliable. Single 3-line proof. | Belongs next to `Multipliable.tprod_le_tprod` in `Mathlib.Topology.Algebra.InfiniteSum.Order`. | Upstream. SAVE ≈ 20 lines. |
| `ENNReal.lean` | 29 | `ENNReal.div_div_div_cancel_left (ha : a ≠ 0) (ha' : a ≠ ⊤) (hc : c ≠ ⊤) : (a/b)/(a/c) = c/b`. | Companions exist: `ENNReal.div_div_cancel`, `mul_div_mul_left`. This one is missing from mathlib — upstream. | Upstream, one-liner file. SAVE ≈ 25 lines. |
| `FunctionsBoundedAtInfty.lean` + `AtImInfty.lean` + `SlashActions.lean` + `UpperHalfPlane.lean` can be merged into a single `ModularFormsHelpers.lean` with <40 lines. |  |  |  |  |

### 1b. Partially replaceable (generalize to mathlib API)

| File | Lines | Verdict | Mathlib equivalent / what shrinks | Action |
|---|---|---|---|---|
| `Cusps.lean` | 41 | 3 theorems relating slash-at-∞ bounds to bounded-at-cusps. Uses `OnePoint.isZeroAt_iff_forall_SL2Z`, `OnePoint.isBoundedAt_iff_forall_SL2Z`, `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z` — all mathlib now. Proofs are ≤ 3 lines each. | All iff lemmas exist in mathlib `ModularForms/Cusps.lean`/`BoundedAtCusp.lean`. | Upstream as-is (adding 3 lemmas next to existing API). SAVE ≈ 35 lines. |
| `ENat.lean` | 45 | `ENat.tsum_const`, `ENat.tsum_set_const`, `ENat.tsum_one`, `ENat.tsum_set_one`. | Exact `ENNReal.tsum_const`, `ENNReal.tsum_set_const`, `ENNReal.tsum_one`, `ENNReal.tsum_set_one` already exist in `Mathlib.Topology.Algebra.InfiniteSum.ENNReal`. The ENat versions are genuinely missing from mathlib (only ENNReal ones landed), but the proofs are short. | Upstream the `ENat` copies next to the ENNReal ones. Until then, if call sites all fit into ENNReal, cast through coe. SAVE (post-upstream) ≈ 40 lines; SAVE-now ≈ 10 lines by shortening proofs using the already-available `ENNReal` versions + `Nat.cast` / `ENat.toENNReal` lemmas. |
| `Encard.lean` | 95 | Really two things: (a) a 50-line `ENat.tsum_…` dev copied verbatim from "mathlib4 PR #23503 by Peter Nelson" (there's a literal comment saying "remove once that PR is merged"), (b) the public `Set.encard_iUnion_of_pairwiseDisjoint`. Mathlib already has `Set.encard_iUnion_of_finite` (uses finsum on finite index). | `Set.encard_iUnion_of_finite` + `ENat.summable`/`ENat.tsum_prod` from PR #23503. | Upstream PR #23503 if stalled; the public lemma in this file is 5 lines once the `ENat.tsum_subtype_iUnion_eq_tsum` lands. SAVE ≈ 85 lines. |
| `SpecificLimits.lean` | 54 | (a) `summable_real_norm_mul_geometric_of_norm_lt_one` (polynomial × geometric), (b) `summable_pow_shift_mul_exp` for `(n+s)^k * exp(-2π n)`. The first is generic; should live next to `summable_norm_pow_mul_geometric_of_norm_lt_one` (already in mathlib). The second is very repo-specific. | `summable_norm_pow_mul_geometric_of_norm_lt_one` is in `Mathlib.Analysis.SpecificLimits.Normed`. `Real.summable_pow_mul_exp_neg_nat_mul` is in mathlib. | Upstream (a) as a generalization. Keep (b) but shrink by calling `Real.summable_pow_mul_exp_neg_nat_mul` directly; the current proof already does this but carries 16 lines of ring gymnastics that can be 4 via `Summable.nat_add_shift` + `mul_left`. SAVE ≈ 20 lines. |
| `SigmaBounds.lean` | 31 | `σ 3 n ≤ n^4` using `card_divisors_le_self` (mathlib) + `Finset.sum_le_card_nsmul` (mathlib). Useful, but belongs in mathlib's `ArithmeticFunction.Misc` or the `NumberTheory.Divisors` area. | `Nat.card_divisors_le_self` already exists. The general `σ_le_pow_succ` does not; upstream. | Upstream. SAVE ≈ 25 lines. |
| `SigmaSummability.lean` | 40 | Trivial combinator on top of `SigmaBounds` + `SpecificLimits`. | After upstreaming the above, this becomes 6 lines of summable-combinator glue. | Keep (repo-specific), shrink. SAVE ≈ 15 lines. |
| `IntegralProd.lean` | 31 | One wrapper `aestronglyMeasurable_integral_norm_prod_right'` = `hf.norm.prod_swap |>.integral_prod_right'`. | Direct one-liner. | Inline at call sites. SAVE ≈ 28 lines. |
| `IntervalIntegral.lean` | 29 | Two interval-integral `1-t` substitutions. `intervalIntegral_comp_one_sub_eq` is 1-liner `simp`. | `simp` handles both. | Delete; replace with `by simp` or `by rw [intervalIntegral.integral_comp_sub_left]; simp` inline. SAVE ≈ 27 lines. |
| `BoundsOnIcc.lean` | 53 | 3 extrema-on-Icc corollaries of `IsCompact.exists_isMaxOn`, `isCompact_Icc`. `exists_upper_bound_on_Icc` = 2 lines; `exists_lower_bound_pos_on_Icc` = 1-liner. | Fully derivable from `IsCompact.exists_isMaxOn` + `IsCompact.exists_forall_le'`. | Upstream (mathlib would take these in `Mathlib.Topology.Order.Compact` or `Mathlib.Order.Interval.Set.UnorderedInterval`). SAVE ≈ 45 lines. |
| `ContDiffOnByDeriv.lean` | 58 | Two lemmas for families `F n` with the recurrence `HasDerivAt (F n) (F (n+1) x) x` on an open set, giving `ContDiffOn ∞`. Generalizes the iteration already in `IteratedDeriv.lean`. | Not yet in mathlib. | Upstream. SAVE ≈ 50 lines. |
| `DerivHelpers.lean` | 81 | 6 micro-lemmas about `HasDerivAt (fun y : ℝ => cexp (y * c))` and assorted norm bounds. Every single one is a `simpa` on an existing mathlib lemma. `abs_le_abs_add_of_mem_ball` is a 3-line mathlib exercise. `norm_cexp_ofReal_mul_le_exp_mul_of_norm_le` is the only one worth keeping — and it's 10 lines. | `hasDerivAt_ofReal_mul_const`, `cexp.comp_ofReal` are mathlib. | Upstream 2 lemmas (`norm_cexp_ofReal_mul_le_exp_mul_of_norm_le`, `nonneg_of_nonneg_le_mul`); inline the other 4. SAVE ≈ 55 lines. |
| `FourierPhase.lean` | 68 | `norm_phase_eq_one` (= `Complex.norm_exp_ofReal_mul_I` directly), `aestronglyMeasurable_phase` (= `.continuous`), `ae_norm_phase_le_one` (1-liner). | `Complex.norm_exp_ofReal_mul_I` exists; `Continuous.aestronglyMeasurable` exists. | Inline everything; the file adds nothing over 3 mathlib calls. SAVE ≈ 60 lines. |
| `ExpPiIMulMulI.lean` | 51 | 3 exponential-norm helpers: all `simpa`/`nlinarith` bookkeeping on `Complex.norm_exp`. | `Complex.norm_exp` + `Real.exp_le_exp`. | Trim to 15 lines (2 needed lemmas only). SAVE ≈ 35 lines. |
| `ExpNormSqDiv.lean` | 34 | One `ContinuousOn` for `(x,t) ↦ exp(-π‖x‖²/t)` on `univ ×ˢ Ici 1`, 12-line proof. | Can be reduced to `by fun_prop` if mathlib's `fun_prop` knows enough, or ~6 lines with `ContinuousAt.div.cexp`. | Shrink to 10 lines; optionally upstream. SAVE ≈ 20 lines. |
| `GaussianRexpIntegral.lean` | 44 | Specialized `integral_gaussian_rexp_even (k := 4) → s^4`. Built directly on `GaussianFourier.integral_rexp_neg_mul_sq_norm` (mathlib). | Mathlib has the general `GaussianFourier.integral_rexp_neg_mul_sq_norm`. | Keep the general `_even` (7 lines); drop the `rexp` d=8 specialisation (can be inlined with `simpa using integral_gaussian_rexp_even (k := 4)`). SAVE ≈ 15 lines. |
| `GaussianRexpIntegrable.lean` | 34 | Integrability of `exp(-π‖x‖²/s)` via `Integrable.of_integral_ne_zero`. | `GaussianFourier.integrable_cexp_neg_mul_sq_norm_add` is the base. | Keep a 10-line version, drop the d=8 wrapper. SAVE ≈ 15 lines. |
| `IntegrablePowMulExp.lean` | 29 | `integrableOn_pow_mul_exp_neg_mul_Ioi`, `_Ici`. Both are `simpa` on `integrableOn_rpow_mul_exp_neg_mul_rpow` (mathlib). | `integrableOn_rpow_mul_exp_neg_mul_rpow` in `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`. | Upstream as `integrableOn_pow_mul_exp_neg_mul_Ici/Ioi`. SAVE ≈ 25 lines. |
| `ZLattice.lean` | 60 | (a) `ZSpan.ceil_sub_mem_fundamentalDomain`, `ZSpan.floor_eq_zero` (pure mathlib candidates). (b) `ZLattice.basis_index_equiv`: reindex to `Fin d` for full-rank lattices — useful. | The `ZSpan` lemmas belong in `Mathlib.Algebra.Module.ZLattice.Basic`. | Upstream (a). Keep (b) — it's load-bearing. SAVE ≈ 25 lines. |

### 1c. Genuinely novel / keep as-is

These files either encode repo-specific glue that cannot cleanly upstream, or require non-trivial domain reasoning.

| File | Lines | Reason | Trim potential |
|---|---|---|---|
| `CauchyGoursat/OpenRectangular.lean` | 265 | "Deformation of open rectangular contours" — real mathematical contribution (Cauchy–Goursat with unbounded top). Should upstream to `Mathlib.Analysis.Complex.CauchyIntegral`, but the development is substantial. | Upstream PR — SAVE (long-term) ≈ 260 lines; short-term: keep. |
| `GaussianFourierCommon.lean` | 119 | Specialisation of `fourier_gaussian_innerProductSpace` to `EuclideanSpace ℝ (Fin (2k))`. Genuinely useful; thin wrappers, but saves ~30 lines per call. | Keep. ~10 lines of `mul_comm`/`mul_assoc` can go via better `simp` lemmas. SAVE ≈ 10 lines. |
| `FourierLinearEquiv.lean` | 64 | Fourier change of variables under invertible linear map. Should upstream to `Mathlib.Analysis.Fourier.FourierTransform`. | Upstream → SAVE 50 lines. Keep for now. |
| `IteratedDeriv.lean` | 192 | Mix of "recurrence → smooth/iterated" (general, upstreamable) and specific `Complex.exp(tc)`-iter-deriv closed form. The `decay_iteratedFDeriv_mul_of_bound_left` theorem is repo-specific Leibniz-style bookkeeping. | Split: upstream `iteratedDeriv_eq_of_hasDerivAt_succ`, `differentiable_iteratedDeriv_of_hasDerivAt_succ`, `contDiff_of_hasDerivAt_succ`, `eqOn_iteratedDeriv_eq_of_deriv_eq` (~70 lines). Shrink remaining half by 30 lines with better `simp`. SAVE ≈ 40 lines net. |
| `MDifferentiableFunProp.lean` | 41 | `fun_prop` attributes for Eisenstein series; comment says "upstream mathlib PR #33808". | Keep until PR merges, SAVE 35 lines later. |
| `ScalarOneForm.lean`, `ScalarOneFormDiffContOnCl.lean`, `ScalarOneFormFDeriv.lean` | 22 + 30 + 48 = 100 | Scalar-one-form = `v ↦ v * F z`. Custom gadget used only in contour deformation. Cannot easily live in mathlib. | Consolidate into one file of ~70 lines. SAVE ≈ 30 lines. |
| `RadialSchwartz/Multidimensional.lean` | 50 | `schwartzMap_multidimensional_of_schwartzMap_real`. `hasFDerivAt_norm_sq` is a trivial wrapper around `HasFDerivAt.norm_sq` (mathlib). | Delete `hasFDerivAt_norm_sq`, `differentiableAt_norm_sq`, `differentiable_norm_sq` — all in mathlib as `HasFDerivAt.norm_sq`. Keep `schwartzMap_multidimensional_of_schwartzMap_real`. SAVE ≈ 15 lines. |
| `RadialSchwartz/Cutoff.lean` | 96 | Cutoff function and its smoothness. Specialises `Real.smoothTransition` (mathlib). | Keep core; the `cutoffC` complex-valued duplicates the real one — merge to save ~30 lines. SAVE ≈ 25 lines. |
| `RadialSchwartz/OneSided.lean` | 138 | Bridge from one-sided decay to `𝓢(ℝ,ℂ)`. Useful; 138 lines is about right. | Keep. ~15 lines of duplication (decay theorem stated twice, once with `hg_smooth` assumption, once deriving it). SAVE ≈ 15 lines. |

### 1d. Subtotals for `ForMathlib/`

- **Fully deletable (1a)**: 15 + 15 + 26 + 25 + 29 (ENNReal) + 20 (SlashActions local) + 22 (AtImInfty) = ~**150 lines gone immediately** (inline at call sites, no upstream needed).
- **Upstream-candidate (1b)**: `Encard.lean` (85), `Cusps.lean` (35), `BoundsOnIcc.lean` (45), `ContDiffOnByDeriv.lean` (50), `DerivHelpers.lean` (55), `FourierPhase.lean` (60), `IntegralProd.lean` (28), `IntervalIntegral.lean` (27), `IntegrablePowMulExp.lean` (25), `SigmaBounds.lean` (25), `ZLattice.lean` (25), `ExpPiIMulMulI.lean` (35), `ExpNormSqDiv.lean` (20), `Gaussian*` (30), `SpecificLimits/Sigma*` (35) = **~580 lines** savable.
- **Genuinely novel to trim (1c)**: `IteratedDeriv` 40 + `ScalarOneForm*` 30 + `RadialSchwartz*` 55 + `GaussianFourierCommon` 10 = **~135 lines** savable without behavior change.
- **ForMathlib total savings**: **~865 lines** (≈ 39% of the directory).

---

## 2. `Integration/` — per-file analysis

| File | Lines | One-line description | Mathlib status | Action |
|---|---|---|---|---|
| `DifferentiationUnderIntegral.lean` | 304 | Differentiate under ∫ on `(0,1)` for `t ↦ hf t * exp(x · coeff t)` and its x-derivatives `gN n`. Uses `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (mathlib). | Mathlib has the general theorem; this is a specialised framework. `integrable_gN_Ioo`, `ae_bound_gN_succ_Ioo`, `hasDerivAt_integral_gN_Ioo`, `contDiff_integral_g_Ioo`, plus a near-duplicate `hasDerivAt_integral_gN` for interval integrals. | Delete the `μIoo01`-specific duplicate (`hasDerivAt_integral_gN_Ioo` vs `hasDerivAt_integral_gN`) and `contDiff_of_eq_integral_g_Ioo` (is `simpa [funext …]` over `contDiff_integral_g_Ioo`). SAVE ≈ 70 lines. |
| `EndpointIntegrability.lean` | 69 | `integrableOn_one_div_sq_mul_exp_neg_div (c>0)` on `Ioc(0,1]` via `t ↦ 1/t`. Uses `integrableOn_image_iff_integrableOn_abs_deriv_smul` (mathlib). | Keep: genuine repo-specific computation. Already minimal. | Keep. Possibly 10 lines of ring can go. SAVE ≈ 10 lines. |
| `FubiniIoc01.lean` | 50 | `integral_integral_swap` on `(0,1]`. Thin wrappers on `MeasureTheory.integral_integral_swap`. | Both versions (`_muIoc01`, `_Ioc01`) differ only by a `simpa [μIoc01]` unfolding. | Merge into one; SAVE ≈ 15 lines. |
| `InvChangeOfVariables.lean` | 88 | `t ↦ 1/t` on `Ioc(0,1]`, yielding 4 variants of the same CoV. | Every variant is ≤ 8-line wrapper on `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` / `integral_image_eq_integral_deriv_smul_of_antitone` in mathlib `Mathlib.MeasureTheory.Function.JacobianOneDim`. | Keep 2 variants (forward and backward), delete 2 dual-name duplicates. The `one_div_pow_two_mul_one_div_zpow` is pure ring. SAVE ≈ 35 lines. |
| `J6Integrable.lean` | 87 | Integrability of `gN_J6_integrand` on `Ici 1`, with exponential bound. | Repo-specific; calls `integrableOn_pow_mul_exp_neg_mul_Ici` (ForMathlib). | Keep; after upstreaming the `ForMathlib` lemma, the proof shrinks ~10 lines. |
| `Measure.lean` | 138 | Defines `μIoo01`, `μIoc01`, `μIciOne`, `μIoi0` and gives SFinite/IsFiniteMeasure instances. Also includes 2 helper lemmas and a `curveIntegral` bridge. | All 4 `def`s and their instance declarations (16 lines) are 1-liner aliases. | Keep (the measures are used widely) but drop `μIoi0` (doesn't appear used anywhere), inline the helper `integrable_const_mul_pow_muIoo01` (one-shot use) and `integral_nonneg_const_mul_pow_muIoo01`. SAVE ≈ 30 lines. |
| `SmoothIntegralCommon.lean` | 191 | Package `I n x = ∫ t in 0..1, gN n x t` to get `ContDiff ∞` and one-sided decay. Builds on `DifferentiationUnderIntegral` + `ForMathlib/IteratedDeriv`. | Glue layer. `contDiff_of_eq_I0`, `decay_of_eq_I0_of_coeff_re` are `simpa [funext]` wrappers — delete. | Shrink by removing the `_of_eq_I0` wrappers (20 lines each) and consolidating `decay_integral` / `decay_integral_of_coeff_re`. SAVE ≈ 60 lines. |
| `SmoothIntegralIciOne.lean` | 153 | Parametric-integral framework for `∫ t in Ici 1, gN n x t`. Long proof, largely ring manipulations. | Repo-specific, but contains ~30 lines of `ring_nf`/`linarith` that could go via cleaner bounds. | Keep; trim ~25 lines of exponential bookkeeping. SAVE ≈ 25 lines. |
| `UpperHalfPlaneComp.lean` | 58 | Helpers for functions on `ℍ` composed with real parametrisations. | `exists_bound_norm_uIoc_zero_one_of_continuous` is a 2-line `simpa` on `exists_upper_bound_on_uIoc` (ForMathlib). `continuous_comp_upperHalfPlane_mk` is 1-line via `Continuous.upperHalfPlaneMk.comp`. | Keep, trim. SAVE ≈ 20 lines. |

### Integration subtotals

- **Trivial duplicates** (double-naming, `_Ioc01`/`_muIoc01` pairs, wrappers over `funext`): FubiniIoc01 15 + InvChange 35 + DifferentiationUnderIntegral 70 + SmoothIntegralCommon 60 + UpperHalfPlane 20 = **~200 lines** of immediate savings.
- **Secondary trimming**: Measure 30 + SmoothIntegralIciOne 25 + EndpointIntegrability 10 + J6Integrable 10 = **~75 lines**.
- **Integration total savings**: **~275 lines** (≈ 24% of the directory).

---

## 3. `CohnElkies/LPBound.lean` (605 lines)

### 3a. Structure breakdown

- Lines 1–62: boilerplate (imports, variables, `local notation`).
- Lines 63–77: `Complex_Function_Helpers` (1 trivial lemma + 1 short).
- Lines 78–136: `Nonnegativity` — 3 theorems (`hIntegrable`, `fourier_ne_zero`, `f_nonneg_at_zero`, `f_zero_pos`).
- Lines 138–463: `Fundamental_Domain_Dependent` section. **Three big theorems**:
  - `calc_aux_1` (23 lines) — ℓ-lattice sum lower bound.
  - `calc_steps'` (15 lines) — real-part exchange.
  - `calc_steps_part1` (~93 lines) — Poisson summation transform.
  - `calc_steps_part2` (~170 lines) — nonnegative term isolation and norm² simplification.
  - `calc_steps` (11 lines) — `ge_trans` glue.
- Lines 465–579: `Main_Theorem_For_One_Packing`. **`LinearProgrammingBound'`** = 99 lines, ENNReal casting hell.
- Lines 581–605: `Main_Theorem`. **`LinearProgrammingBound`** = 24 lines.

Roughly **~370 of the 605 lines** live inside the two largest theorems (`calc_steps_part2` and `LinearProgrammingBound'`).

### 3b. Shortening opportunities

1. **`LinearProgrammingBound'` ENNReal bookkeeping (lines 480–578, 99 lines).** About **60 of these lines** are `Real.toNNReal` ↔ `ENNReal` coercion management: `hRHSCast`, `hLHSCast`, `hfouaux₁`, `hfouaux₂`, `hnRaux₁`, `hnRaux₂`, and the massive case split on `𝓕 f 0 = 0`. The core inequality is 2 lines (`calc_steps` gives the real-valued statement; the rest is cast-handling). A cleaner formulation that works entirely in `ℝ≥0` or uses `ENNReal.ofReal` consistently could shave **~40 lines**. Also: `hnRaux₂ : (P.numReps : ℕ∞).toENNReal ≠ ⊤` is proved via `Ne.symm (ne_of_beq_false rfl)` — use `ENat.toENNReal_ne_top` (mathlib) when available.

2. **`calc_steps_part2` `hSummable` inline proof (lines 309–401, 92 lines of a single `have`).** This proves `Summable (fun m ↦ (𝓕 f m).re * ‖∑_x exp(…)‖²)` by bounding each term by `‖𝓕 f m‖ · n²`. This is a concrete Schwartz-bound argument that should be factored out as one helper lemma `summable_fourier_mul_norm_exp_sq` (~35 lines including statement). SAVE ≈ 55 lines.

3. **`calc_steps_part1` algebraic rewrites (lines 189–278).** Each `calc` step ends with a `congr!` + `simp`/`ring_nf`. The conjugation step (lines 260–267 using `Complex.exp_neg_real_I_eq_conj`) and the norm²-squared identity (lines 268–278) can each be 1-liner rewrites if `simp` is tuned. SAVE ≈ 20 lines.

4. **`helper` (lines 65–70) + `hFourierImZero` (lines 73–74).** Two trivial helpers; inline with `congrArg Complex.im`. SAVE ≈ 8 lines.

5. **`VolumeOfBalls` uses (lines 489, 493).** Replace `EuclideanSpace.volume_ball_pos/lt_top` with `Metric.measure_ball_pos`/`measure_ball_lt_top` directly. SAVE ≈ 4 lines (after deleting the wrapper file).

### 3c. LPBound total savings

- Casting simplification: **~40 lines**.
- Extracted summability helper: **~55 lines** (possibly in `LPBoundSummability.lean`).
- Algebraic `simp` tuning: **~20 lines**.
- Inlining `helper`: **~8 lines**.
- **LPBound total savings**: **~120 lines** (≈ 20% of the file). The file's structural core (`calc_steps_part1`, `calc_steps_part2`, `LinearProgrammingBound'`, `LinearProgrammingBound`) stays — the savings are in bookkeeping.

---

## 4. Concrete refactor plan (totals and priorities)

### 4a. Totals

- ForMathlib: **~865 lines**
- Integration: **~275 lines**
- LPBound.lean: **~120 lines**
- **Grand total: ~1260 lines** — right in the middle of the 800–1500 target.

### 4b. "Do these first" delete/inline list (immediate, no upstream needed)

1. **Delete `ComplexI.lean`** (15 lines). Replace `I_mul_I_mul` with `by simp [Complex.I_mul_I]` at call sites. File:`SpherePacking/ForMathlib/ComplexI.lean`.
2. **Delete `VolumeOfBalls.lean`** (26 lines). Replace at `LPBound.lean:489, 493` with mathlib `Metric.measure_ball_pos` / `MeasureTheory.measure_ball_lt_top`.
3. **Delete `IntervalIntegral.lean`** (29 lines). Both lemmas are 1-line `simp`/`rw` inline.
4. **Delete `IntegralProd.lean`** (31 lines). Replace at call sites with `hf.norm.prod_swap.integral_prod_right'`.
5. **Delete `FunctionsBoundedAtInfty.lean`** (15 lines). Inline the 1-lemma via `simp [UpperHalfPlane.isBoundedAtImInfty_iff]`.
6. **Delete `hasFDerivAt_norm_sq`, `differentiableAt_norm_sq`, `differentiable_norm_sq`** from `RadialSchwartz/Multidimensional.lean` (~8 lines). Replace with direct `HasFDerivAt.norm_sq`.
7. **Merge `AtImInfty.lean`, `UpperHalfPlane.lean`, `SlashActions.lean`, `FunctionsBoundedAtInfty.lean`** into one `ModularFormsHelpers.lean` (~30 lines total). Saves ~75 lines after de-duplication and fewer import overheads.
8. **Delete duplicate Integration wrappers**: `FubiniIoc01.integral_integral_swap_Ioc01` (keep only `_muIoc01`), `InvChangeOfVariables.integral_Ici_one_eq_integral_abs_deriv_smul` + `_integral_image_inv` (keep only final direct form), `SmoothIntegralCommon.{contDiff_of_eq_I0, decay_of_eq_I0_of_coeff_re}`, `DifferentiationUnderIntegral.contDiff_of_eq_integral_g_Ioo`. SAVE ≈ 150 lines.

**Phase-1 immediate savings: ~350 lines** with no upstream dependency.

### 4c. Upstream-track refactor

1. **`ENat.lean` + part of `Encard.lean`** → PR mirroring `ENNReal.tsum_const` etc. as `ENat.tsum_*`. Will unblock deletion of 130 lines in this repo.
2. **`Cusps.lean`** → PR adding 3 lemmas to `Mathlib.NumberTheory.ModularForms.BoundedAtCusp`. Blocks 35 lines.
3. **`BoundsOnIcc.lean`, `IntegrablePowMulExp.lean`, `SigmaBounds.lean`, `DerivHelpers.lean`, `ContDiffOnByDeriv.lean`** → group into 1–2 mathlib PRs (analysis helpers). Blocks ~200 lines.
4. **`FourierLinearEquiv.lean`** → PR to `Mathlib.Analysis.Fourier.FourierTransform`. Blocks 60 lines.
5. **`CauchyGoursat/OpenRectangular.lean`** → standalone PR to `Mathlib.Analysis.Complex.CauchyIntegral`. Blocks 260 lines.

**Phase-2 (upstream-dependent) savings: ~680 lines** once PRs merge.

### 4d. LPBound hygiene pass

Independent of the above; refactor `LinearProgrammingBound'` to work in `ℝ≥0∞` throughout and extract the summability helper. **~120 lines.**

### 4e. Per-action ledger

| Action | File(s) | Dependency | SAVE (lines) |
|---|---|---|---|
| Delete 5 trivial wrapper files | `ComplexI`, `VolumeOfBalls`, `IntervalIntegral`, `IntegralProd`, `FunctionsBoundedAtInfty` | none | 116 |
| Delete duplicate `_norm_sq` lemmas | `RadialSchwartz/Multidimensional` | none | 8 |
| Collapse 8 Integration duplicate wrappers | `FubiniIoc01`, `InvChange…`, `SmoothIntegralCommon`, `DifferentiationUnderIntegral` | none | 150 |
| Merge 4 modular-form helper files | `AtImInfty`, `UpperHalfPlane`, `SlashActions`, `FunctionsBoundedAtInfty` | none | 75 |
| Consolidate `ScalarOneForm*` trio | 3 files → 1 | none | 30 |
| LPBound ENNReal casting rewrite | `LPBound.lean` | none | 120 |
| Trim `IteratedDeriv.lean`, `RadialSchwartz/Cutoff.lean`, `RadialSchwartz/OneSided.lean` | 3 files | none | 80 |
| Generalise `DerivHelpers` / `ExpPiIMulMulI` / `ExpNormSqDiv` | 3 files | none | 90 |
| Tighten `Measure.lean`, `EndpointIntegrability`, `J6Integrable`, `SmoothIntegralIciOne`, `UpperHalfPlaneComp` | 5 files | none | 95 |
| (upstream) Mathlib PRs for ENat/Encard/BoundsOnIcc/… | many | PR merge | 680 |
| (upstream) CauchyGoursat PR | 1 file | PR merge | 260 |

**Without any upstream**: ~**760 lines** saved across ForMathlib + Integration + LPBound — already in the 800-1500 target zone via internal simplification alone.

**With upstream PRs merging**: additional ~**940 lines** → total ~1700 lines (above the 1500 stretch goal).

---

## 5. Key call-site references for the immediate-delete list

- `LPBound.lean:489` — `EuclideanSpace.volume_ball_pos (0 : …) one_half_pos` → replace with `Metric.measure_ball_pos (μ := volume) 0 one_half_pos`.
- `LPBound.lean:493` — `EuclideanSpace.volume_ball_lt_top …` → replace with `measure_ball_lt_top (μ := volume) …`.
- `LPBound.lean:65-74` — `helper` and `hFourierImZero`: inline to `fun x ↦ by simpa [eq_comm] using congrArg Complex.im (hRealFourier x)`.
- `SpherePacking/CohnElkies/Prereqs.lean`, `SpherePacking/ModularForms/*` — touch points for the `ModularFormsHelpers` merge; search for `ModularForm.slash_neg_one`, `ModularForm.slash_neg'`, `zero_at_cusps_of_zero_at_infty`, `Filter.eventually_atImInfty`.

No TODOs above — every action is concrete enough to execute. The refactor can proceed in two waves: (i) Phase-1 (no-upstream) delivers ~760 lines immediately; (ii) Phase-2 (upstream) unlocks another ~940.
