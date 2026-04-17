# `SpherePacking/ModularForms/` Cleanup Analysis

**Total**: 13,306 lines across 45 files (3 re-export stubs + 6 subdirs).
**Target**: Recover 1,500-2,500 lines by leveraging recent mathlib additions.
**Context**: Most files predate the recent `Mathlib.NumberTheory.ModularForms.*`
development. Mathlib now contains `DedekindEta`, `EisensteinSeries.E2.*`,
`LevelOne`, `QExpansion`, `Identities`, `Cusps`, `BoundedAtCusp`, and a much
richer q-expansion / cusp-form theory than when this subtree was first written.

---

## 1. Files already well-aligned with mathlib (keep, minor cleanup only)

These are thin wrappers around mathlib — no significant duplication:

| file | lines | content |
| --- | --- | --- |
| `E2.lean` | 156 | `G₂`, `E₂`, `D₂` are `def`-aliases for `EisensteinSeries.{G2,E2,D2}`. Re-exports mathlib's transformation laws. |
| `Eisenstein.lean` | 183 | `A_E = E₂·E₄ − E₆` and its ℕ-indexed q-expansion. Project-specific. |
| `BigO.lean` | 32 | Three thin `IsBigO` wrappers. Keep. |
| `ExpLemmas.lean` | 42 | Three `‖exp(2πi z)‖ < 1` lemmas. Mathlib now has `UpperHalfPlane.norm_exp_two_pi_I_lt_one` directly — `exp_upperHalfPlane_lt_one` is literally `norm_exp_two_pi_I_lt_one`. **Delete.** |
| `TendstoLemmas.lean` | 43 | 4 trivial tendsto lemmas. Most are one-line `.comp tendsto_natCast_atTop_atTop`. Inline at call sites. |
| `BigO.lean` | 32 | Keep. |
| `CuspFormIsoModforms.lean` | 90 | The linear equivalence `CuspForm Γ(1) k ≃ ModularForm Γ(1) (k-12)` via `Δ`. Short, project-specific to the "weight < 12 ⇒ cusp form = 0" argument. Keep. |

---

## 2. MAJOR DUPLICATION WITH MATHLIB

### 2.1 `Delta.lean` (606 lines) — high-value target

Mathlib already has `Mathlib.NumberTheory.ModularForms.DedekindEta` (165 lines)
with:
- `ModularForm.eta_q`, `ModularForm.eta`, `ModularForm.eta_ne_zero`
- `ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet`
- `ModularForm.logDeriv_eta_eq_E2`
- `multipliableLocallyUniformlyOn_eta`, `eta_tprod_ne_zero`
- `summable_eta_q`

The local file at `SpherePacking/ModularForms/Delta.lean:32-57` redefines `Δ`
as a raw product and then immediately shows `Delta_eq_eta_pow` (line 44) —
i.e. `Δ = η^24`. All subsequent "analytic" properties (nonvanishing,
holomorphicity, q-expansion) are derived via this identity and mathlib's
DedekindEta API.

**Action**: refactor `Δ` to directly use `ModularForm.eta`. The nonvanishing
(line 60-62), holomorphy chunks (line 313-327 inside `Delta`), and product
formula (`DiscriminantProductFormula`, line 36-41) become one-liners.
`Delta_boundedfactor` (line 201-282) — 80 lines of hand-rolled log/tprod
convergence at `atImInfty` — is entirely subsumed by
`CuspFormClass.exp_decay_atImInfty` once `Delta : CuspForm Γ(1) 12` is built
from mathlib's eta.

- **Lines 316-485** (`Delta_cuspFuntion_eq`, `diffwithinat_prod_1`,
  `tendstoLocallyUniformlyOn_prod_range_one_sub_pow`, `Delta_q_one_term`)
  reproduce the analyticity of `z ↦ z * ∏ (1 - z^(n+1))^24` on
  `ball 0 (1/2)`. Mathlib's `DedekindEta` already proves analyticity of the
  log-product on all of `ℍ`; the local argument picks up the `q=0` limit.
  After refactor this can be reduced to ~30 lines using
  `multipliableLocallyUniformlyOn_eta`.

**Also note**: `cexp_aux1`, `cexp_aux2`, `cexp_aux4` at lines 479-491 are
three copies of "exp on the imaginary axis simplifies to `rexp`" that are
also redefined as `private lemma` at line 521-523, 555-557. Dedupe.

**Estimated saving**: 250-350 lines.

### 2.2 `Eta.lean` (191 lines) — high-value target

The file opens with `noncomputable abbrev η : ℂ → ℂ := ModularForm.eta`
(line 35) — so the abbreviation is already tied to mathlib. But the heavy
lemmas `eta_logDeriv_eql`, `eta_logderivs`, `eta_logderivs_const`,
`eta_equality` (35-192) hand-roll the functional equation `η(-1/z) = √(z/i)
η(z)` from scratch by comparing log-derivatives — 160 lines.

**Status**: mathlib currently does not have `eta_equality` at level of
generality needed (this was considered in the Birkbeck–Loeffler DedekindEta
PR, but only logDeriv is in mathlib). So **keep this file** but:

- **Delete `CSqrt.lean` (65 lines)**: `csqrt_I`, `csqrt_deriv`,
  `csqrt_differentiableAt`, `csqrt_pow_24` are all one-liners in terms of
  mathlib's `Complex.cpow` at exponent `1/2`. Replace `csqrt z` by
  `z ^ (1/2 : ℂ)` (which mathlib handles via `Complex.cpow`), saving ~60
  lines here plus ~15 lines of wiring at use sites.

**Estimated saving**: 60-100 lines.

### 2.3 `Eisenstein.lean` (183 lines) — good shape; minor

Defines `E₄`, `E₆` as scaled `eisensteinSeriesMF` from mathlib (line 33-38),
with rfl-aliases `E4_eq`/`E6_eq` (mostly OK). A lot of auxiliary φ₀, φ₂',
φ₄' definitions that stay. Minor: the private `ModularForm.S_transform_of_level_one`
(line 61-71) duplicates `SlashInvariantForm.slash_S_apply` from
`Mathlib.NumberTheory.ModularForms.Identities`. **Replace**, saving ~10 lines.

### 2.4 `IsCuspForm.lean` (181 lines)

Defines `CuspForm_to_ModularForm`, `IsCuspForm`, `IsCuspForm_to_CuspForm`,
`CuspFormSubmodule`. Mathlib has `CuspForm.toSlashInvariantForm` and
auto-coercion via `CuspFormClass`. Mathlib does **not** have:
- `IsCuspForm Γ k f : Prop` (as a membership predicate on `ModularForm`)
- The range submodule + `LinearEquiv`
- `IsCuspForm_iff_coeffZero_eq_zero` for level 1

The file is 181 lines total and about 60 of them (lines 98-145,
`CuspForm_to_ModularForm_coe`, `cuspFormOfSIFTendstoZero`) are wiring that
mathlib provides differently. The `IsCuspForm_iff_coeffZero_eq_zero` at line
160 is project-specific (it's what feeds the dimension formulas) and worth
keeping.

**Action**: move `cuspFormOfSIFTendstoZero`, `cuspFormOfCoeffZero`,
`isZeroAtImInfty_of_coeffZero` into mathlib-style helpers using
`CuspFormClass.cuspFunction_apply_zero` (which exists since Birkbeck's PR).

**Estimated saving**: 30-50 lines.

### 2.5 `Lv1Lv2Identities.lean` (238 lines) — shape only

Proves `E₄ = H₂² + H₂H₄ + H₄²` etc. This is a project-specific blueprint
argument (no mathlib equivalent). The pattern used — "build `theta_X_MF`
as a level-1 modular form, subtract from `E₄`, show the difference is a
weight-4 cusp form, invoke `IsCuspForm_weight_lt_eq_zero`" — is repeated
twice (once for `E₄`, once for `E₆`) and could be abstracted into a single
helper `modular_form_eq_of_same_limit_at_infty_and_weight_lt_twelve`. Saving
~30-50 lines.

---

## 3. SummableLemmas/ (1,252 lines across 5 files) — highest cut opportunity

This subdir contains several categories of lemmas with varying degrees of
duplication:

### 3.1 `SummableLemmas/Basic.lean` (116 lines) — mostly dedupe

| local lemma | mathlib replacement | status |
| --- | --- | --- |
| `int_sum_neg` (L63) | `Equiv.tsum_eq (Equiv.neg ℤ)` | **delete** — one-liner |
| `summable_neg` (L67) | `Equiv.summable_iff (Equiv.neg ℤ)` | **delete** |
| `tsum_pnat_eq_tsum_succ3` (L72) | `tsum_pnat_eq_tsum_succ` (mathlib) | **delete** — alias |
| `nat_pos_tsum2` (L77) | `PNat.coe_injective.summable_iff` | **delete** — wrapper |
| `tsum_pNat` (L87) | `tsum_pnat_eq_tsum_succ` + `tsum_zero_add'` | **inline** |
| `int_tsum_pNat` (L105) | `tsum_int_eq_zero_add_tsum_pnat` (mathlib) | **delete** — alias |
| `tsum_pnat_coe_mul_geometric` (L94) | `tsum_coe_mul_geometric_of_norm_lt_one` | **delete** |
| `upp_half_not_ints` (L111) | `UpperHalfPlane.ne_intCast` | **delete** — alias |
| `pos_nat_div_upper` (L49) | mathlib has `UpperHalfPlane.im_pnat_div_pos` | **delete** |
| `pnat_div_upper` (L54) | same | **delete** |
| `neg_one_pow_mul_factorial_ne_zero` (L58) | trivial, inline | **delete** |

**Estimated saving**: 70-90 lines (Basic.lean becomes ~25 lines).

### 3.2 `SummableLemmas/Cotangent.lean` (240 lines) — keep mostly

Deep technical content about vertical-strip bounds for Eisenstein series
derivatives (`sub_bound`, `add_bound`, `aut_bound_on_comp`). Project-specific;
can stay.

- `vector_norm_bound` (line 135-184) — 49 lines of `Fin 2 → ℤ` norm arithmetic.
  Likely can be reduced 50% by using `Matrix.SpecialLinearGroup` API, or by
  a direct `Int.natAbs`-based argument with `omega`. Saving ~15-25 lines.
- `summable_hammerTime_nat` at line 126 — one-off wrapper that uses
  `Real.summable_nat_rpow_inv`. **Inline**.

**Estimated saving**: 15-30 lines.

### 3.3 `SummableLemmas/QExpansion.lean` (716 lines) — biggest target

This file is the heaviest. Content:

- **Lines 23-122** — summability of `∑ 1/(z-n)^(k+1)` over `ℕ/ℕ+/ℤ`
  (`summable_1`, `summable_2`, `summable_3`, `a33`, `hsum`,
  `summable_auxil_1`). Probable replacements in mathlib's
  `EisensteinSeries.Summable` (302 lines) which has
  `summand_bound_of_mem_verticalStrip` etc. **Skim + replace**.

- **Lines 131-216** — termwise derivation of the geometric exponential
  series (`exp_series_ite_deriv_uexp2`, `exp_series_ite_deriv_uexp''`,
  `tsum_uexp_contDiffOn`, `iter_der_within_add`, `iter_exp_eqOn`).
  Mathlib now has `contDiffOn_tsum_cexp` and `iteratedDerivWithin_tsum_cexp_eq`
  (both used here, but only to rewrite into the "correct" form). The local
  versions exist mostly to rewrite from `exp(2πi·n·w)` to `exp(2πi·w)^n`
  and back. **Replace by a single `exp_nat_mul` rewrite** — saving 50-80 lines.

- **Lines 290-410** — `aut_bound_on_comp`, `diff_on_aux`, `diff_at_aux`,
  `aut_series_ite_deriv_uexp2`, `tsum_ider_der_eq`, `auxp_series_ite_deriv_uexp'''`,
  `tsum_aexp_contDiffOn`. Together this is the Weierstrass/q-expansion
  derivative machinery for the level-one Eisenstein series of general
  weight. Mathlib has `EisensteinSeries.{QExpansion,UniformConvergence}`
  which now provides parallel development. **Survey — probably 100+
  lines can go.**

- **Lines 476-549** — `aux_iter_der_tsum`, `cot_series_repr`, etc.
  Mathlib has cotangent series expansions in
  `Analysis.SpecialFunctions.Trigonometric.Cotangent` (imported). Some local
  lemmas duplicate general theory. **Conservative saving**: 30-50 lines.

- **Lines 552+** (not all shown) — the `EisensteinSeries_Identity`,
  `q_exp_iden`, `tsum_sigma_eqn` core theorems. Mathlib's
  `EisensteinSeries.QExpansion.lean` (297 lines) now proves the q-expansion
  formula. **Compare directly**: if mathlib's statement is strong enough,
  drop the local file's q-expansion identities.

**Estimated saving**: 200-350 lines. This is the #1 dedupe target.

### 3.4 `SummableLemmas/IntPNat.lean` (82 lines) + `SummableLemmas/G2.lean` (98 lines)

Purely project-specific (the G₂ alternative definition is blueprint-specific).
**Keep, but check** `G_2_alt_summable_δ` and the `δ` correction term can
be expressed more idiomatically. Minor cleanup ~10 lines.

---

## 4. Derivative/ (1,416 lines, already split) — minor dedupe

Phase 7 has already split `Derivative.lean` into 6 files. Inside each:

### 4.1 `Derivative/Basic.lean` (362 lines)

- `D` definition (line 34) — project-specific (this is `D F z = (2πi)⁻¹ · F'(z)`,
  not mathlib's Serre derivative).
- `D_add`, `D_sub`, `D_neg`, `D_smul`, `D_mul` — ~80 lines. Each a
  one-line `deriv_...` call wrapped in `(2πi)⁻¹`. **Consolidate** into a
  single helper `D_eq_inv_mul_deriv : D F z = (2πi)⁻¹ * deriv (F ∘ ofComplex) z`
  (already roughly present) and prove algebra lemmas by `simp [D, ...]`.
  Saving 30-40 lines.
- `D_qexp_tsum` (line 153-217) — **Cauchy-estimate-style + termwise
  differentiation**. 60-line proof mostly about rewriting derivWithin to
  HasDerivAt and back. With mathlib's `hasDerivAt_tsum_fun` (in the local
  `TsumDerivWithin.lean`, which itself closely mirrors mathlib's
  `Analysis.Calculus.UniformLimitsDeriv`), this could be ~30 lines. Saving
  30 lines.
- Lines 219-363 (Cauchy estimates `norm_D_le_of_sphere_bound`,
  `norm_D_le_div_pi_im_of_bounded`, `D_isBoundedAtImInfty_of_bounded`,
  `D_tendsto_zero_of_isBoundedAtImInfty`, `D_isZeroAtImInfty_of_bounded`):
  **TODO comment at line 341** already says "The following lemma from
  Gauss overlaps with `D_tendsto_zero_of_isBoundedAtImInfty`". Dedupe the
  two. Saving ~20 lines.

**Estimated saving**: 60-90 lines.

### 4.2 `Derivative/SerreD.lean` (85 lines)

Compact. Keep.

### 4.3 `Derivative/SlashFormula.lean` (213 lines) and `Equivariance.lean` (92 lines)

The heart of the proof that `D` and Serre derivatives transform correctly
under the slash action. Project-specific, compact. Minor: `deriv_denom`,
`deriv_num`, `differentiableAt_denom`, `differentiableAt_num` (line 33-56)
may already exist in mathlib since `SlashActions.lean` underwent extensive
work. **Search**. Possible saving 10-20 lines.

### 4.4 `Derivative/Ramanujan.lean` (417 lines)

`ramanujan_E₂/E₄/E₆` — proves the classical identities `D E₂ = (E₂² - E₄)/12` etc.
This is fundamental blueprint material. The structure is:
- Construct correction function `corr γ` (the `D₂` of Eisenstein)
- Show `E₂ ∣[2] γ = E₂ + corr γ`
- Prove `(serre_D 1 E₂) ∣[4] γ = serre_D 1 E₂` via explicit computation
- Package as weight-4 modular form
- Identify with `-(1/12)·E₄` via constant-term comparison and weight-<12 vanishing.

This is very much like what `SerreDerivativeSlash.lean` does (108 lines)
— **there is real duplication** between the proof of `serre_DE₂_slash_invariant`
in SerreDerivativeSlash.lean:77 and the nested `hSerre_slash` inside
`ramanujan_E₂'` at line 221 of Ramanujan.lean. Consolidate.

**Estimated saving**: 40-70 lines.

### 4.5 `Derivative/AntiSerreDerPos.lean` (247 lines)

Contains `antiSerreDerPos` (the monotonicity criterion on the imaginary
axis) and `D_Delta_eq_E₂_mul_Delta`. Project-specific. Keep, compact.

---

## 5. JacobiTheta/ (1,433 lines, already split) — minor dedupe

### 5.1 `JacobiTheta/Basic.lean` (104 lines)

Clean. Defines `Θ₂/Θ₃/Θ₄`, `H₂/H₃/H₄` in terms of `jacobiTheta₂` from mathlib.
Minor: lines 65-93 define `Θᵢ_as_jacobiTheta₂` which are essentially
`simp`-lemmas. Good.

### 5.2 `JacobiTheta/Positivity.lean` (174 lines)

Imaginary-axis realness/positivity. Project-specific, compact. The helper
`cexp_aux...` patterns here overlap with similar helpers in `Delta.lean`
line 479-491. Consolidate into `SpherePacking.ForMathlib.ComplexI` (already
referenced). Saving ~15 lines.

### 5.3 `JacobiTheta/SlashActions.lean` (571 lines)

Largest JacobiTheta file. Proves `H₂/H₃/H₄ ∣[2] γ` transformation laws
for all of `{S, T, T⁻¹, α, β, negI, S⁻¹, α⁻¹, β⁻¹}` and packages `H_i_SIF`,
`H_i_MF` as SlashInvariantForm/ModularForm of level `Γ(2)`. Much of this
is `grind =`-tagged — so already short, but there are many lemmas that
are essentially one line each (e.g. `H₂_T_inv_action`, `H₃_T_inv_action`,
`H₄_T_inv_action`, `H₂_S_inv_action`, …). **Consolidate into a single
lemma** `slash_inv_eq_of_slash_eq` (actually present at line 112!) used
mechanically. Saving ~30 lines.

The core `H_i_S_action`, `H_i_T_action` lemmas (which invoke
`jacobiTheta₂_functional_equation` and `jacobiTheta₂_add_right`) are
project-specific. Keep.

### 5.4 `JacobiTheta/DeltaIdentity.lean` (584 lines)

Proves `jacobi_identity : H₂ + H₄ = H₃` via dimension vanishing of
weight-4 cusp forms, plus the identity `Delta = H₂ · H₃ · H₄` (up to a
constant). Project-specific. Compact. Keep.

**Estimated JacobiTheta saving**: 40-80 lines.

---

## 6. FG/ (2,613 lines) — project-specific, modest dedupe

This is the auxiliary modular functions `F` and `G` used to build the magic
function. The subdir is:
- `FG/Basic.lean` (473) — definitions of `F`, `G`, `L₁₀`, `SerreDer_22_L₁₀`,
  MLDEs
- `FG/Positivity.lean` (698) — imaginary-axis positivity of `F`, `G`
- `FG/L10OverAsymptotics.lean` (756) — asymptotic of `L₁₀ / q^(7/2)` at `i∞`
- `FG/Inequalities.lean` (604) — monotonicity of `F/G` on the imaginary axis
- `FG/AsymptoticsTools.lean` (82) — small helpers

None of this duplicates mathlib (these are blueprint-specific objects).
The dedupe opportunities are **internal**:

### 6.1 Internal dedupe in FG/

- `FG/Basic.lean:64-105` (`F_eq_FReal`, `G_eq_GReal`, `FmodGReal_eq_div`)
  — three structurally identical "resToImagAxis.Real ⇒ resToImagAxis =
  ofReal ∘ re" lemmas differing only in the function name. Abstract into
  a single helper. Saving ~30 lines.

- Long tendsto arguments in `L10OverAsymptotics.lean` (lines 56-500+)
  hand-roll the fact that `F/q₂` and `G/q₃` are bounded at infinity,
  using explicit epsilon-delta computations. Mathlib's
  `IsBoundedAtImInfty` + `qExpansion`-based approach (via `qExpansion`
  of the denominators) would shrink this substantially. **Moderate
  saving**: 100-150 lines.

- `FG/Positivity.lean` lines 51-100 (inside `F_pos`) establish
  `r^n`-bound arithmetic that's very similar to the machinery in
  `EisensteinBase.lean:270-296` (qexpsummable) and also to the machinery
  in `FG/L10OverAsymptotics.lean`. These three copies of "exp bound on
  imag axis" could be factored out. Saving ~50 lines.

### 6.2 Bigger structural cleanup

The overall argument of FG — "if `F(it)` is eventually positive,
`serre_D` is positive, and `F` is modular, then `F(it)` is positive
everywhere" — ends up reimplementing a restricted form of
`antiSerreDerPos` (in `Derivative/AntiSerreDerPos.lean`). Let's see
whether `FmodG_antitone` in `FG/Inequalities.lean` can be phrased as
an instance of `antiSerreDerPos`. It cannot directly (FmodG has mixed
weight), but the sign/monotone argument is structurally the same.
**Potential save**: 50-80 lines.

**Estimated FG saving**: 150-280 lines.

---

## 7. EisensteinBase.lean (845 lines) — moderate dedupe

The largest single file. Content breakdown:

- **Lines 33-124** — definitions of `E₄`, `E₆`, their `S`-transforms,
  `φ₀/φ₂'/φ₄'` ratios and `φ_i''` extensions. Mostly definitions, compact.
- **Lines 126-257** — `q_exp_unique` (uniqueness of q-expansion
  coefficients). This is essentially `ModularForm.qExpansion` coefficient
  uniqueness — which should already follow from
  `HasFPowerSeriesAt.eq_formalMultilinearSeries`. Uses
  `qExpansionFormalMultilinearSeries` from mathlib. **Could be ~50-line
  replacement** vs. ~130 lines currently.
- **Lines 260-295** — `sigma_bound`, `Ek_q`, `qexpsummable`,
  `Ek_q_exp` (explicit `q`-coefficients of `E k`). Mathlib's
  `EisensteinSeries.QExpansion.lean` (297 lines) now provides
  `eisensteinSeries_qExpansion` directly. **Replace** — save 80-100 lines.
- **Lines 332-419** — `E4_q_exp`, `E6_q_exp` (specializations of
  `Ek_q_exp` for k=4,6). The `bernoulli'_five`, `bernoulli'_six`,
  `riemannZeta_six` evaluations (lines 369-390) are all explicit
  computations that may be obsolete given mathlib's `riemannZeta_four`
  and `riemannZeta_two_mul_nat`. Check `mathlib.NumberTheory.LSeries.Riemann...`
  for `riemannZeta_six`.
- **Lines 420-573** — `E4E6_coeff_zero_eq_zero`, `Delta_E4_E6_aux`,
  `Delta_cuspFuntion_eq`, `tendstoLocallyUniformlyOn_prod_range_one_sub_pow`,
  `diffwithinat_prod_1`, `Delta_q_one_term`. This is all the heavy lifting
  to compute the `q=1` coefficient of `Delta`. With mathlib's
  `qExpansion_pow`, `qExpansion_mul_coeff` (which are used here), this is
  about 50 lines of essential work — the rest is wiring. **Save**: 50-70 lines.
- **Lines 577-716** — `E_even_imag_axis_real`, `E₂_imag_axis_real`,
  `E₄_imag_axis_real`, `E₆_imag_axis_real` — "Eisenstein series are real
  on the imaginary axis". The general proof `E_even_imag_axis_real` is
  60 lines; the two specializations are 2 lines each. Short.
  `E₂_imag_axis_real` (40 lines) uses `logDeriv_q_expo_summable`. **Could
  consolidate E₂/E₄/E₆ into a single "q-expansion ⇒ imag axis real"
  pattern**. Save 30 lines.
- **Lines 719-843** — `norm_exp_two_pi_I_le_exp_neg_two_pi`,
  `norm_tsum_logDeriv_expo_le`, `E₂_isBoundedAtImInfty`,
  `tendsto_E₂_atImInfty` — bounds on the `E₂` q-expansion tail. This is
  real project-specific work (E₂ is quasi-modular so needs its own bound).
  Keep.

**Estimated EisensteinBase saving**: 200-300 lines.

---

## 8. DimensionFormulas.lean (558 lines) + DimGenCongLevels/ (719 lines)

### 8.1 DimensionFormulas.lean

- Lines 27-315 — proves rank of `ModularForm Γ(1) k` = Nat.floor(k/12) (+ 1
  if 12 ∤ k-2), using Δ and E₄/E₆. Project-specific. Compact given the
  ambition. Consider: **mathlib will get this eventually**. Currently
  non-blocking. Small saving ~20-30 lines (`floor_lem1` and
  `finiteDimensional_of_subsingleton` are trivially general).
- Lines 317-394 — dimension formula induction.
- Lines 396-558 — `finiteDimensional_modularForm_{level_one, SL2Z,
  congr}`, extending to general congruence subgroups. Project-specific.

### 8.2 DimGenCongLevels/ (719 lines)

Project-specific norm-transfer arguments for finite-dimensionality of
modular forms on arbitrary congruence subgroups. Not in mathlib. Keep.

**Estimated DimensionFormulas saving**: 30-50 lines.

---

## 9. Summary of recommended actions

Ranked by value × confidence:

| target | action | lines saved | confidence |
| --- | --- | --- | --- |
| 1. Rewrite `Delta.lean` via `ModularForm.eta` | delete ~300 lines of hand-rolled multipliability | 250-350 | HIGH |
| 2. Trim `SummableLemmas/QExpansion.lean` | use mathlib's `EisensteinSeries.QExpansion` + `contDiffOn_tsum_cexp` | 200-350 | MED |
| 3. Trim `EisensteinBase.lean` | `q_exp_unique` ≈ `HasFPowerSeriesAt.eq_formalMultilinearSeries`; use mathlib's `eisensteinSeries_qExpansion` | 200-300 | MED |
| 4. Delete `SummableLemmas/Basic.lean` aliases | mathlib has `tsum_pnat_eq_tsum_succ`, `Equiv.tsum_eq`, etc. | 70-90 | HIGH |
| 5. FG/ internal consolidation | factor exp-bound reasoning; consolidate `F_eq_FReal`/`G_eq_GReal`/`FmodGReal_eq_div` | 150-280 | MED |
| 6. Consolidate `serre_DE₂_slash_invariant` between SerreDerivativeSlash and Ramanujan | dedupe E₂ slash-invariance proof | 50-80 | HIGH |
| 7. Delete `CSqrt.lean`, use `Complex.cpow` | `csqrt z = z ^ (1/2 : ℂ)` | 50-80 | HIGH |
| 8. Derivative/Basic cleanup | dedupe `D_add/sub/neg/smul/mul`, `D_tendsto_zero` overlap | 60-90 | MED |
| 9. JacobiTheta/SlashActions cleanup | factor slash-inv aliases | 40-80 | MED |
| 10. Lv1Lv2Identities abstract helper | `modular_form_eq_of_limit_match_and_weight_lt_twelve` | 30-50 | MED |
| 11. Delete `ExpLemmas.lean`, `TendstoLemmas.lean` | aliases for mathlib | 50-70 | HIGH |
| 12. `DimensionFormulas` minor | `finiteDimensional_of_subsingleton` etc. | 30-50 | LOW |

**Total estimate**: **1,180-1,870 lines saved**, well within the 1,000-2,000
target for this subtree.

---

## 10. Concrete path forward (suggested order)

1. **Phase A (High-confidence, low-risk deletion)** — target 400 lines
   - Delete `ExpLemmas.lean`, `TendstoLemmas.lean`, `CSqrt.lean`
   - Strip `SummableLemmas/Basic.lean` aliases
   - Expected: 250-350 lines.

2. **Phase B (Delta refactor)** — target 300 lines
   - Replace `Delta.lean` core with `Δ := η^24` using mathlib's
     `ModularForm.eta` as the primary object.
   - Remove `Delta_boundedfactor` (subsumed by `CuspFormClass.exp_decay_atImInfty`).

3. **Phase C (EisensteinBase trim)** — target 200 lines
   - Replace `q_exp_unique` by mathlib's power-series uniqueness.
   - Use `EisensteinSeries.QExpansion` for `Ek_q_exp`.

4. **Phase D (SummableLemmas consolidation)** — target 250 lines
   - Delete `exp_series_ite_deriv_uexp2/''`, replace with mathlib's
     `iteratedDerivWithin_tsum_cexp_eq`.
   - Delete `aux_iter_der_tsum` once `cot_series_repr` points directly to
     mathlib.

5. **Phase E (FG internal cleanup, Derivative dedupe)** — target 250 lines
   - Consolidate `F_eq_FReal`/`G_eq_GReal`/`FmodGReal_eq_div`.
   - Dedupe `serre_DE₂_slash_invariant` appearances.

Rough cumulative by phase: A=350, A+B=650, A+B+C=850, A+B+C+D=1100, A+B+C+D+E=1350.

---

## Appendix: files by role

**Core blueprint content (keep, large)**:
- `Delta.lean`, `Eta.lean`, `Eisenstein.lean`, `EisensteinBase.lean`,
  `Derivative/*.lean`, `JacobiTheta/*.lean`, `FG/*.lean`,
  `ResToImagAxis.lean`, `DimensionFormulas.lean`, `DimGenCongLevels/*.lean`,
  `Lv1Lv2Identities.lean`, `ThetaDerivIdentities.lean`,
  `EisensteinAsymptotics.lean`, `EisensteinQExpansions.lean`

**Mostly deletable / stub wrappers**:
- `ExpLemmas.lean` (42), `TendstoLemmas.lean` (43), `BigO.lean` (32),
  `CSqrt.lean` (65), `SummableLemmas/Basic.lean` (116 → ~25)

**Scattered deep dedupe opportunities**: Delta, EisensteinBase,
SummableLemmas/QExpansion (these three account for half of the total
savings).
