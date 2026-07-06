# Blueprint Update Plan

Analysis of the main parts of the formalized proof that are still missing from the blueprint,
comparing the Lean sources under `SpherePacking/` with the declarations currently referenced by
the blueprint (`blueprint/lean_decls`). Items already covered by the blueprint (E₂ transformation
laws, Lv1/Lv2 identities, Jacobi theta positivity, F/G inequalities, Serre derivative basics,
contour integration section) are excluded.

## 1. Schwartz-property machinery for `a` and `b` (biggest gap)

The blueprint states `prop:a-schwartz` / `prop:b-schwartz` and the decay-bound lemmas, but the
actual proof structure is absent. This splits into three steps:

### 1a. Radial Schwartz bridge (separate blueprint section)

Packaging a smooth fast-decaying radial profile on `ℝ` as a Schwartz function on `ℝ⁸` via
composition with `‖x‖²` (`RadialSchwartz.Bridge.fCutSchwartz`,
`schwartzMap_multidimensional_of_schwartzMap_real`; only mentioned in passing prose in
`fourier-analysis.tex`).

- **Fits into:** a new dedicated blueprint section.

### 1b. Integration infrastructure (separate blueprint section)

Content of `SpherePacking/Integration/Measure.lean`: scalar one-form utilities, convenience
measures on standard intervals (`μIoc01`, `μIoo01`, `μIciOne`, `μIoi0`), inversion
change-of-variables on `(0,1]` (`integral_Ici_one_eq_integral_abs_deriv_smul`), and
differentiation under the integral sign — `hasDerivAt_integral_gN_Ioo`,
`contDiff_integral_g_Ioo` (on `(0,1)`) and `SmoothIntegralIciOne.hasDerivAt_integral_gN`
(on `[1,∞)`).

- **Fits into:** a new dedicated blueprint section.

### 1c. Smoothness of the integrals `I₁'`–`I₆'`, `J₁'`–`J₆'`

Smoothness (and decay of all derivatives) of the contour integrals defining the radial profiles
of `a` and `b`, in `SpherePacking/MagicFunction/a/Schwartz/Basic.lean` and
`SpherePacking/MagicFunction/b/Schwartz/Basic.lean`.

- **Fits into:** `blueprint/src/subsections/construct-a-b.tex`.

## 2. Unlinked blueprint items

Several existing items have **no `\lean{}` link** even though the mathematics is formalized:

- `lem:integral-bound`
- `lem:bound-I1-I3-I5`
- `lem:bound-I2-I4-I6`
- `lemma:bound-J1-J3-J5`
- `lemma:bound-J2-J4-J6`
- `cor:phi0-near-0-infty`
- `cor:psiI-near-0-infty`

Cheap wins: find the corresponding declarations and add the links (plus `\leanok`).

## 3. Fourier eigenfunction proof structure (`â = a`, `b̂ = −b`)

`prop:a-fourier` / `prop:b-fourier` link only the final theorems `eig_a` / `eig_b`. The
multi-step proof in `SpherePacking/MagicFunction/a/Eigenfunction.lean` and
`SpherePacking/MagicFunction/b/Eigenfunction.lean` — Gaussian Fourier transform under the
integral, rewriting each `Iₖ` / `Jₖ` as a curve integral, and applying the contour permutation
identities — has no intermediate blueprint items.

- **Fits into:** `construct-a-b.tex` (proofs of `prop:a-fourier` / `prop:b-fourier`), using the
  new contour-integration section (`thm:perm-contour-pos` / `thm:perm-contour-neg`).

## 4. q-expansion machinery

The blueprint has `lemma:Ek-Fourier`, but not the products and derived expansions used for the
φ-bounds:

- `E4_q_exp`, `E6_q_exp`, `A_E_eq_tsum` (for `E₂E₄ − E₆`) in
  `SpherePacking/ModularForms/EisensteinQExpansions.lean`;
- supporting summability / termwise-derivative theory in
  `SpherePacking/ModularForms/QExpansionLemmas.lean`,
  `SpherePacking/ModularForms/MultipliableLemmas.lean`,
  `SpherePacking/ModularForms/TsumDerivWithin.lean`.
- **Fits into:** `modular-forms.tex`.

## 5. Cusp form theory behind the dimension formulas

`thm:lvl1_dims` links `ModularForm.dimension_level_one`, but the underlying development is
invisible in the blueprint:

- the isomorphism `S_k ≅ M_{k−12}` via division by `Δ`
  (`SpherePacking/ModularForms/CuspFormIsoModforms.lean`);
- the `IsCuspForm` predicate (`SpherePacking/ModularForms/IsCuspForm.lean`);
- `SpherePacking/ModularForms/DimensionFormulas.lean`.
- **Fits into:** `modular-forms.tex`.

## 6. Restriction to the imaginary axis

The `ResToImagAxis` framework (`SpherePacking/ModularForms/ResToImagAxis.lean`) — reduction of
modular-form estimates to `t ↦ f(it)`, with growth/decay transfer lemmas like
`tendsto_rpow_mul_resToImagAxis_of_isBigO_exp` — is used throughout the positivity arguments
(blueprint sections 6.5 / 8) but never introduced in the blueprint.

- **Fits into:** `modular-forms.tex` or `modform-ineq.tex`.

## 7. Laplace-transform integral representations (proof detail)

`prop:a-another-integral` / `prop:b-another-integral` link the final theorems, but the
substantial intermediate layer in
`SpherePacking/MagicFunction/g/CohnElkies/AnotherIntegral/` (vertical-line rewrites,
integrability of the subtracted-singularity integrands, term-by-term Laplace evaluations) has no
blueprint counterpart.

- Key theorems: `aRadial_eq_laplace_phi0_main`, `aRadial_eq_another_integral_main`,
  `bRadial_eq_laplace_psiI_main`, `bRadial_eq_another_integral_main` (linked), plus their
  supporting lemmas (unlinked).
- **Fits into:** `construct-a-b.tex`.

## Suggested priority

1. Items **1–3**: the analytic infrastructure for `a` and `b` follows the formal proof most
   closely and benefits most from blueprint items.
2. Items **4–6**: self-contained additions to the modular forms section.
3. Item **7**: proof-detail expansion, lower priority.
