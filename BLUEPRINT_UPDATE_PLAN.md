# Blueprint Update Plan

Analysis of the main parts of the formalized proof that are still missing from the blueprint,
comparing the Lean sources under `SpherePacking/` with the declarations currently referenced by
the blueprint (`blueprint/lean_decls`). Items already covered by the blueprint (E₂ transformation
laws, Lv1/Lv2 identities, Jacobi theta positivity, F/G inequalities, Serre derivative basics) are excluded.

**Note on recent additions**: Previous sessions have added:
- ✅ **Basics on contour integration** section
- ✅ **Radial Schwartz functions** section

## 1. Schwartz-property machinery for `a` and `b` — ✅ DONE

The blueprint now mirrors the formal proof structure for the Schwartz estimates of `a` and `b`.
The implementation is split into three pieces:

### 1a. Radial Schwartz bridge (separate blueprint section) — ✅ IMPLEMENTED

**Status**: Completed in previous sessions. The new "Radial Schwartz functions" section
([radial-schwartz.tex](blueprint/src/subsections/radial-schwartz.tex)) covers:
- Abstract definition of smooth transition functions (`def:smooth-transition`)
- Mathlib realization via `smoothTransition` (remark with `def:radial-cutoff`)
- Cutoff profiles globally Schwartz (`lemma:cutoff-mul-decay`)
- Schwartz packaging of a profile (`def:fCutSchwartz`)
- Radial lift to `ℝ^d` (`thm:schwartz-multidimensional`)

Declarations covered: `RadialSchwartz.Bridge.fCutSchwartz`, `RadialSchwartz.cutoffC`,
`schwartzMap_multidimensional_of_schwartzMap_real`.

### 1b. Integration infrastructure (separate blueprint section) — ✅ IMPLEMENTED

Content of `SpherePacking/Integration/Measure.lean`: scalar one-form utilities, convenience
measures on standard intervals (`μIoc01`, `μIoo01`, `μIciOne`, `μIoi0`), inversion
change-of-variables on `(0,1]` (`integral_Ici_one_eq_integral_abs_deriv_smul`), and
differentiation under the integral sign — `hasDerivAt_integral_gN_Ioo`,
`contDiff_integral_g_Ioo` (on `(0,1)`) and `SmoothIntegralIciOne.hasDerivAt_integral_gN`
(on `[1,∞)`).

- **Fits into:** a new dedicated blueprint section.
- Important implementation note: this section packages the inversion change-of-variables lemma and the differentiation-under-the-integral-sign results needed for the radial profiles.

### 1c. Smoothness of the integrals `I₁'`–`I₆'`, `J₁'`–`J₆'` — ✅ IMPLEMENTED

Smoothness (and decay of all derivatives) of the contour integrals defining the radial profiles
of `a` and `b`, in `SpherePacking/MagicFunction/a/Schwartz/Basic.lean` and
`SpherePacking/MagicFunction/b/Schwartz/Basic.lean`.

- **Fits into:** `blueprint/src/subsections/construct-a-b.tex` as a new subsection.
- Important implementation note: this subsection records both smoothness and the derivative decay estimates used to package the radial Schwartz functions.

## 2. Unlinked blueprint items — ✅ VERIFIED

The items that were previously listed here are now linked in `blueprint/src/subsections/construct-a-b.tex` with `\lean{}` and `\leanok`:

- `lem:integral-bound`
- `lem:bound-I1-I3-I5`
- `lem:bound-I2-I4-I6`
- `lemma:bound-J1-J3-J5`
- `lemma:bound-J2-J4-J6`
- `cor:phi0-near-0-infty`
- `cor:psiI-near-0-infty`

No remaining unlinked items were found in this group.

## 3. Fourier eigenfunction proof structure (`â = a`, `b̂ = −b`) — ✅ DONE

The final propositions `prop:a-fourier` and `prop:b-fourier` are already in the blueprint, and
the contour permutation theorems they depend on are also present in the contour-integration
section. The blueprint now covers the full proof chain needed for the Fourier eigenfunction
argument, including the Gaussian Fourier transform under the integral and the curve-integral
rewrites of the `Iₖ` / `Jₖ` terms.

- **Fits into:** `construct-a-b.tex` (proofs of `prop:a-fourier` / `prop:b-fourier`), using the
  new contour-integration section (`thm:perm-contour-pos` / `thm:perm-contour-neg`).

## 4. q-expansion machinery — ✅ DONE

The blueprint now includes the q-expansion subsection in `modular-forms.tex`, and the explicit
coefficient formulas for `E4_q_exp` and `E6_q_exp` are folded into `lemma:Ek-Fourier` rather than
stated as separate blueprint items. The remaining separate q-expansion statement is the tsum
identity `A_E_eq_tsum` used later in the $\varphi$-bounds:

- `A_E_eq_tsum` (for `E₂E₄ − E₆`) in
  `SpherePacking/ModularForms/EisensteinQExpansions.lean`;
- supporting summability / termwise-derivative theory in
  `SpherePacking/ModularForms/QExpansionLemmas.lean`,
  `SpherePacking/ModularForms/MultipliableLemmas.lean`,
  `SpherePacking/ModularForms/TsumDerivWithin.lean`.
- **Fits into:** `modular-forms.tex` as a new subsection.
- Important implementation note: the supporting Lean lemmas come from `QExpansionLemmas.lean`, `MultipliableLemmas.lean`, and `TsumDerivWithin.lean`, which provide the summability and termwise-differentiation infrastructure for the q-series manipulations.

## 5. Cusp form theory behind the dimension formulas — ✅ DONE

The blueprint now includes a dedicated cusp-form subsection in `modular-forms.tex` covering the
predicate, the decay-at-infinity constructor, the level-one `q`-coefficient criterion, the
transport equivalences, the discriminant identities, the division-by-`\Delta` equivalence, and
the dimension consequences.

### 5a. Basic cusp-form infrastructure

- `def:IsCuspForm` / `SpherePacking.ModularForms.IsCuspForm`, the level-one cusp-form predicate.
- `cuspFormOfSIFTendstoZero`, the constructor that turns a slash-invariant holomorphic function
   with vanishing limit at `i\infty` into a cusp form.
- `IsCuspForm_iff_coeffZero_eq_zero`, the level-one criterion identifying cusp forms with
   vanishing constant `q`-coefficient.
- The bridge result `IsCuspForm_weight_lt_eq_zero`, which is the concrete zero criterion used in
   the later dimension arguments.

### 5b. Division by `\Delta`

- `cuspForm_Gamma_one_equiv_SL` and `modularForm_Gamma_one_equiv_SL`, the transport equivalences
   between the project’s `\Gamma(1)` objects and Mathlib’s `\mathcal{S}\mathcal{L}` versions.
- `CuspForms_iso_Modforms`, the main equivalence `CuspForm \Gamma(1) k \simeq ModularForm
   \Gamma(1) (k - 12)` given by division by `\Delta`.
- The discriminant input needed for that equivalence:
   `Delta_apply_eq_one_div_1728_mul_E4_pow_three_sub_E6_sq` and `Delta_q_exp_two`.
- A short explanatory remark that `\Delta` is the weight-12 cusp form used to shift cusp forms
   down by 12 in weight.

### 5c. Dimension consequences

- `cuspform_weight_lt_12_zero`, showing that the cusp-form space vanishes below weight 12.
- `cuspform_weight_12_finrank_one`, showing that the weight-12 cusp-form space is one-dimensional.
- `IsCuspForm_weight_lt_eq_zero`, the concrete vanishing statement for level-one modular forms
   that are cusp forms.
- The blueprint corollary `thm:lvl1_dims` / `cor:dim-mf`, which packages the low-weight dimension
   formulas used later in the modular-form arguments.

- **Fits into:** `modular-forms.tex` as a new subsection after the q-expansion material.

## 6. Restriction to the imaginary axis — ❌ NOT IMPLEMENTED

The `ResToImagAxis` framework (`SpherePacking/ModularForms/ResToImagAxis.lean`) — reduction of
modular-form estimates to `t ↦ f(it)`, with growth/decay transfer lemmas like
`tendsto_rpow_mul_resToImagAxis_of_isBigO_exp` — is used throughout the positivity arguments
(blueprint sections 6.5 / 8) but never introduced in the blueprint.

- **Fits into:** `modular-forms.tex` or `modform-ineq.tex`.

## 7. Laplace-transform integral representations (proof detail) — ❌ NOT IMPLEMENTED

`prop:a-another-integral` / `prop:b-another-integral` link the final theorems, but the
substantial intermediate layer in
`SpherePacking/MagicFunction/g/CohnElkies/AnotherIntegral/` (vertical-line rewrites,
integrability of the subtracted-singularity integrands, term-by-term Laplace evaluations) has no
blueprint counterpart.

- Key theorems: `aRadial_eq_laplace_phi0_main`, `aRadial_eq_another_integral_main`,

  `bRadial_eq_laplace_psiI_main`, `bRadial_eq_another_integral_main` (linked), plus their
  supporting lemmas (unlinked).
- **Fits into:** `construct-a-b.tex`.

## 8. Add H₂/H₃/H₄ dependency chain to the blueprint — ✅ DONE

Goal: make the dependency graph explicitly show how the `H₂`, `H₃`, `H₄` layer feeds the
positivity / psi-bound machinery and then the final upper-bound arguments.

**Status**: Implemented in the blueprint by strengthening explicit dependency edges:
- `cor:theta-pos` now explicitly depends on `def:H2-H3-H4` in `modular-forms.tex`.
- `lemma:F-G-phi-psi-identities` now explicitly depends on `lemma:lv1-lv2-identities` in `modform-ineq.tex`.
- `prop:H3-fourier` now explicitly depends on `def:H2-H3-H4`, `lemma:theta-modular`, and `lemma:theta-transform-S-T` in `modular-forms.tex`.
- The downstream chain to the final upper-bound layer remains wired through
   `prop:ineqA` / `prop:ineqB` → `thm:g1` → `thm:g`.

**Not yet in blueprint declarations (kept for later decision)**:
- `H₃_tendsto_atImInfty`
- `H₃_ne_zero`

### 8f. Proof-based declaration inventory (compact)

Method: declarations were collected by scanning Lean statements/proofs for occurrences of `H₂`, `H₃`, `H₄` (excluding private declarations), then intersecting with `blueprint/lean_decls` to keep the list blueprint-relevant.

#### Declarations depending on `H₂` (already in blueprint: ✅)

- ✅ `Delta_eq_H₂_H₃_H₄`
- ✅ `F`
- ✅ `G`
- ✅ `G_pos`
- ✅ `H₂`
- ✅ `H₂_MF`
- ✅ `H₂_SIF`
- ✅ `H₂_S_action`
- ✅ `H₂_T_action`
- ✅ `H₂_imag_axis_pos`
- ✅ `H₃_S_action`
- ✅ `H₄_S_action`
- ✅ `H₄_imag_axis_pos`
- ✅ `IsCuspForm_iff_coeffZero_eq_zero`
- ✅ `MLDE_F`
- ✅ `MLDE_G`
- ✅ `SerreDer_22_L₁₀_pos`
- ✅ `h`
- ✅ `isBoundedAtImInfty_H_slash`
- ✅ `jacobi_identity`
- ✅ `serre_D_two_H₂`
- ✅ `serre_D_two_H₄`
- ✅ `ψI_eq`
- ✅ `ψS_eq'`
- ✅ `ψT_eq`

#### Declarations depending on `H₃` (already in blueprint: ✅)

- ✅ `Delta_eq_H₂_H₃_H₄`
- ✅ `H₂_MF`
- ✅ `H₂_SIF`
- ✅ `H₂_S_action`
- ✅ `H₂_T_action`
- ✅ `H₃`
- ✅ `H₃_MF`
- ✅ `H₃_SIF`
- ✅ `H₃_S_action`
- ✅ `H₃_T_action`
- ✅ `H₄_T_action`
- ✅ `IsCuspForm_iff_coeffZero_eq_zero`
- ✅ `h`
- ✅ `isBoundedAtImInfty_H_slash`
- ✅ `jacobi_identity`
- ✅ `ψI_eq`
- ✅ `ψS_eq'`
- ✅ `ψT_eq`

#### Declarations depending on `H₄` (already in blueprint: ✅)

- ✅ `Delta_eq_H₂_H₃_H₄`
- ✅ `F`
- ✅ `G`
- ✅ `G_pos`
- ✅ `H₂_S_action`
- ✅ `H₂_T_action`
- ✅ `H₂_imag_axis_pos`
- ✅ `H₃_MF`
- ✅ `H₃_SIF`
- ✅ `H₃_S_action`
- ✅ `H₃_T_action`
- ✅ `H₄`
- ✅ `H₄_MF`
- ✅ `H₄_SIF`
- ✅ `H₄_S_action`
- ✅ `H₄_T_action`
- ✅ `H₄_imag_axis_pos`
- ✅ `IsCuspForm_iff_coeffZero_eq_zero`
- ✅ `MLDE_G`
- ✅ `h`
- ✅ `isBoundedAtImInfty_H_slash`
- ✅ `jacobi_identity`
- ✅ `serre_D_two_H₂`
- ✅ `serre_D_two_H₄`
- ✅ `ψI_eq`
- ✅ `ψS_eq'`
- ✅ `ψT_eq`

### 8a. Inventory the exact Lean declarations (no blueprint edit yet)

- Source files to mine for declaration names:
   - `SpherePacking/ModularForms/JacobiTheta/SlashActions.lean`
   - `SpherePacking/ModularForms/JacobiTheta/DeltaIdentity.lean`
   - `SpherePacking/ModularForms/ThetaDerivIdentities.lean`
   - `SpherePacking/ModularForms/Lv1Lv2Identities.lean`
   - `SpherePacking/ModularForms/FG/Basic.lean`, `.../FG/Inequalities.lean`, `.../FG/Positivity.lean`
   - `SpherePacking/MagicFunction/b/PsiBounds.lean`
   - `SpherePacking/UpperBound.lean`
- Build a short table: declaration name → current blueprint label (if any) → target blueprint label.
- Mark declarations already present in `blueprint/lean_decls` to avoid duplicate theorem statements.

### 8b. Add or refine blueprint nodes for the H-layer in modular-forms chapter

- File target: `blueprint/src/subsections/modular-forms.tex`.
- Add a compact subsection (or paragraph block) for the `H₂/H₃/H₄` identities used downstream.
- For each new/updated item:
   - add `\lean{...}` with the exact declaration name,
   - add `\leanok`,
   - add `\uses{...}` edges from prerequisites (slash-action / theta-derivative / delta-identity inputs).
- Avoid creating isolated nodes: every new `H` item must have at least one incoming and one outgoing `\uses` edge.

### 8c. Wire the downstream dependencies in inequalities/positivity chapters

- File target: `blueprint/src/subsections/modform-ineq.tex`.
- Update theorem/corollary blocks that consume `H₂/H₃/H₄`-based facts so they explicitly include
   `\uses{...}` references to the new modular-forms H-layer items.
- Ensure the path `H₂/H₃/H₄` → positivity inequalities → psi bounds is visible in the graph.

### 8d. Connect to the final upper-bound statements

- File targets: `blueprint/src/subsections/cohn-elkies.tex` and/or `blueprint/src/subsections/main-result.tex`
   (depending on where the final inequalities are currently stated).
- Add missing `\uses{...}` links from upper-bound statements back to the psi/positivity results that depend on `H₂/H₃/H₄`.
- Keep this minimal: only add edges that correspond to actual Lean dependencies used in `SpherePacking/UpperBound.lean`.

### 8e. Validation checklist

- Rebuild: `make web`.
- Check that no new unlinked theorem nodes appear in the relevant sections.
- Open `blueprint/web/dep_graph_document.html` and verify there is a visible path from the H-layer
   nodes to the upper-bound nodes.
- If a node remains disconnected, either add the missing `\uses` edge or drop the node from the blueprint.

## Suggested priority (open tasks, re-evaluated)

1. **Item 8 (H₂/H₃/H₄ dependency chain)**
   - Highest blueprint impact right now: it directly improves dependency-graph connectivity from modular-forms identities to positivity/psi bounds and the final upper-bound layer.
2. **Item 6 (ResToImagAxis blueprint section)**
   - Foundational for many modular-form estimates already used in positivity arguments; adding it next reduces fragmentation in sections 6.5/8.
3. **Maryna 3 (disconnected lemma resolution)**
   - Should be resolved immediately after Item 6, because the decision (remove/keep+link/inline) depends on which dependent modular-form items are added.
4. **Item 7 (Laplace-transform intermediate layer)**
   - Important proof detail, but less urgent for current dependency graph coherence than Items 8 and 6.
5. **Maryna 2 (generalization of contour-integration theorems in Lean)**
   - Valuable abstraction cleanup, but primarily a Lean-refactor task rather than a blocking blueprint-linking gap.
6. **Future 5 (periodic\_constant\_eq\_constant blueprint proof)**
   - New blueprint content with no immediate blocking dependencies for current modular-form/upper-bound path.
7. **Future 6 (Poisson summation blueprint proof)**
   - Broad addition, best done after the currently active dependency/documentation gaps are closed.
8. **Maryna 1 (contDiffOn\_family review decision)**
   - Keep pending until collaborator discussion; this remains intentionally last because it is a policy/maintainability decision, not a current blueprint blocker.

## Maryna's comments

After reviewing the first updated version of the blueprint I have noticed the following issues
1. **contDiffOn_family_infty_of_hasDerivAt** — 🔄 PENDING REVIEW

   Theorem SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt should be inlined. This theorem is used in:
   - [SpherePacking/MagicFunction/a/Schwartz/Basic.lean](SpherePacking/MagicFunction/a/Schwartz/Basic.lean) — in the private theorem `I₆'_contDiffOn_Ioi_neg2` (line 1915), which supports the public theorem `cutoffC_mul_I₆'_contDiff`
   - [SpherePacking/MagicFunction/b/Schwartz/Basic.lean](SpherePacking/MagicFunction/b/Schwartz/Basic.lean) — in the public theorem `contDiffOn_J₆'_Ioi_neg1` (line 167)

   **Decision**: Keep it for now; to be reviewed with colleagues on whether it should remain, be inlined, or be removed.
2. **Generalization of contour-integration theorems** — ❌ NOT IMPLEMENTED

   These theorems currently parameterize over families of functions depending on `r`:
   - [SpherePacking/Contour/MobiusInv/WedgeSetContour.lean](SpherePacking/Contour/MobiusInv/WedgeSetContour.lean#L264): `curveIntegral_segment_eq_neg_curveIntegral_segment_map'_of`
   - `SpherePacking.MobiusInv.curveIntegral_segment_neg_inv`
   - [SpherePacking/Contour/MobiusInv/WedgeSetContour.lean](SpherePacking/Contour/MobiusInv/WedgeSetContour.lean#L505): `perm_J12_contour_h1`
   - `SpherePacking.Contour.perm_J12_contour_h2`
   - `SpherePacking.perm_J12_contour_mobiusInv_wedgeSet`
   - `SpherePacking.perm_I12_contour_mobiusInv_wedgeSet`

   **Suggestion**: State these results for a single pair of functions `Ψ, Ψ' : ℂ → ℂ` instead of families depending on `r`. The family versions would then follow trivially by instantiation. This would make the theorems more abstract and reusable.
3. **Disconnected lemma** — 🔄 ANALYSIS COMPLETE, OPTIONS PENDING

   Theorem `SpherePacking.Integration.InvChangeOfVariables.integral_Ici_one_eq_integral_abs_deriv_smul` ([integration-infrastructure.tex](blueprint/src/subsections/integration-infrastructure.tex#L11), labeled `lemma:inv-change-of-variables`) is not referenced by any other blueprint item (no blueprint theorem has `\uses{lemma:inv-change-of-variables}`).

   **Facts**:
   - It's used in the Lean code by `Complete_Change_of_Variables` theorems in [SpherePacking/MagicFunction/a/Eigenfunction.lean](SpherePacking/MagicFunction/a/Eigenfunction.lean#L61), [SpherePacking/MagicFunction/b/Eigenfunction.lean](SpherePacking/MagicFunction/b/Eigenfunction.lean#L1015), and [SpherePacking/MagicFunction/a/Schwartz/Basic.lean](SpherePacking/MagicFunction/a/Schwartz/Basic.lean#L1210)
   - But those theorems are not in the blueprint
   - The lemma itself is simple and could be inlined at its usage sites or made private

   **Options**:
   - Remove from blueprint (if it's only scaffolding)
   - Keep but add a `\uses{}` directive from a dependent blueprint item once that item is added
   - Inline the proof at usage sites

4. The blueprint statement of definition RadialSchwartz.cutoffC should be corrected. It is not mathematically correct. Instead of "the cut-off function" we should say that a function chi is a smooth transition function if it satisfies the conditions listed in the definition. In Mathlib, an explicit example of the smooth transition function is constructed. I suggest giving an abstract definition of a smooth transition function and then separately giving an explicit example from Mathlib. This will be mathematically consistent.

   **Detailed analysis**:
   The current blueprint definition in [radial-schwartz.tex](blueprint/src/subsections/radial-schwartz.tex#L10) incorrectly refers to "**the** smooth transition function" as if there is a unique one. This is not mathematically precise.

   **Current blueprint statement (incorrect)**:
   ```
   Let χ : ℝ → ℝ be the smooth transition function with
   χ(r) = 0 for r ≤ -1/2,   χ(r) = 1 for r ≥ 0,
   ```

   **Proposed fix**:
   1. Add an abstract definition: "A smooth transition function is a $C^\infty$ function $\chi : \mathbb{R} \to [0,1]$ such that..."
   2. Then separately state: "In the formalization, we use the specific smooth transition function $\chi(r) = \operatorname{smoothTransition}(2r + 1)$ provided by Mathlib, which satisfies [concrete properties]."

   This separates the abstract property from the concrete Mathlib instantiation, making the statement mathematically consistent with the Lean code structure in [SpherePacking/ForMathlib/DerivHelpers.lean](SpherePacking/ForMathlib/DerivHelpers.lean#L240).

   **Status**: ✅ Fixed. The blueprint has been updated:
   - Introduced `def:smooth-transition` as an abstract definition of smooth transition functions
   - Added a separate `remark` labeled `def:radial-cutoff` explaining the Mathlib realization
   - Updated all `\uses{}` directives to reference the correct definition labels
   - See [radial-schwartz.tex](blueprint/src/subsections/radial-schwartz.tex#L10) for the updated blueprint section

## Future directions — ❌ NOT STARTED

5. Include proof of theorem periodic_constant_eq_constant to the blueprint. Include it as a new subsection in the section "Density of packings".
6. Include proof of the Poisson summation formula. It can be included in the section "Facts from Fourier Analysis"

---

## Implementation Status Summary

| Item | Status | Notes |
|------|--------|-------|
| **Section: Contour integration basics** | ✅ IMPLEMENTED | Added in previous sessions |
| **Section: Radial Schwartz functions** | ✅ IMPLEMENTED | Added in previous sessions |
| 1. Schwartz machinery (a,b) | ✅ DONE | Radial bridge, integration infrastructure, and smoothness packages are documented in the blueprint |
| 2. Unlinked items | ✅ VERIFIED | All previously listed items are linked in `construct-a-b.tex` with `\lean{}` and `\leanok` |
| 3. Fourier eigenfunction | ✅ DONE | Final propositions and contour permutation theorems are linked in the blueprint |
| 4. q-expansion | ✅ DONE | `E4_q_exp` and `E6_q_exp` are folded into `lemma:Ek-Fourier`; `A_E_eq_tsum` remains separate |
| 5. Cusp form theory | ✅ DONE | Added the cusp-form subsection and the low-weight dimension consequences to the modular-forms blueprint |
| Maryna 4: Smooth transition | ✅ FIXED | Split into abstract def + Mathlib remark |
| 8. H₂/H₃/H₄ dependency chain | ✅ DONE | Added explicit `\uses{}` edges in `modular-forms.tex` and `modform-ineq.tex`; path to upper-bound statements is now explicit |
| 6. ResToImagAxis | ❌ NOT IMPLEMENTED | Priority 2: introduce restriction-to-imaginary-axis framework in modular forms / inequalities blueprint |
| Maryna 3: Disconnected lemma | 🔄 ANALYSIS DONE | Priority 3: decide remove vs keep-with-link vs inline after ResToImagAxis integration |
| 7. Laplace-transform | ❌ NOT IMPLEMENTED | Priority 4: add missing intermediate AnotherIntegral proof layer in `construct-a-b.tex` |
| Maryna 2: Contour theorems | ❌ NOT IMPLEMENTED | Priority 5: Lean-level abstraction refactor to single `Ψ, Ψ'` statements |
| Future 5: periodic_constant | ❌ NOT STARTED | Priority 6: add proof subsection in density-of-packings chapter |
| Future 6: Poisson summation | ❌ NOT STARTED | Priority 7: add proof subsection in Fourier-analysis chapter |
| Maryna 1: contDiffOn_family | 🔄 PENDING | Priority 8: awaiting colleague review; keep theorem as-is for now |

## Suggested changes to the Lean files

1. **Generalization of contour-integration theorems** — ❌ NOT IMPLEMENTED

   The contour-integration theorems currently parameterize over families of functions depending on `r`.
   They should be generalized to a single pair of functions `Ψ, Ψ' : ℂ → ℂ`, with the family versions
   following by instantiation.
