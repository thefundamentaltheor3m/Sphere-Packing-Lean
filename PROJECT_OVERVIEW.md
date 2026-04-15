# Project Overview: Sphere-Packing-Lean

Generated: 2026-04-14

## Executive Summary

This project formalizes the proof that the E8 lattice achieves the optimal sphere packing density in dimension 8, following Viazovska's breakthrough proof. The main theorem (`MainTheorem.lean`) states `SpherePackingConstant 8 = E8Packing.density = pi^4/384`.

The proof chain is: (1) Define sphere packings and their density, show periodic = general packing constant; (2) Construct the E8 lattice and compute its density; (3) Establish the Cohn-Elkies linear programming bound via Poisson summation; (4) Construct Viazovska's magic function g from modular forms (Eisenstein series, Jacobi theta, the discriminant Delta); (5) Prove g satisfies the Cohn-Elkies sign conditions (g(x) <= 0 for ||x|| >= sqrt(2), Fourier(g)(x) >= 0 everywhere); (6) Plug into the LP bound to get the upper bound matching E8 density.

The project spans **169 Lean files, ~59,400 lines, ~2,200 declarations, and zero sorries**.

## Statistics

| Module | Files | Lines | Declarations | Long proofs (>30 lines) |
|--------|-------|-------|-------------|------------------------|
| Basic + E8 + top-level | 14 | 3,327 | ~193 | 12 |
| ForMathlib | 47 | 2,981 | ~175 | 6 |
| CohnElkies | 14 | 3,165 | ~107 | 10 |
| Contour | 16 | 2,000 | ~75 | 3 |
| Integration | 9 | 1,138 | ~58 | 5 |
| Tactic | 7 | 1,203 | ~51 | 2 |
| ModularForms | 53 | 14,956 | ~620 | 25+ |
| MagicFunction/a | 37 | ~8,000 | ~350 | 15+ |
| MagicFunction/b | 29 | ~7,000 | ~220 | 20+ |
| MagicFunction/g | 46 | 15,254 | ~350 | 25+ |
| **Total** | **169** | **~59,400** | **~2,200** | **~120** |

- Sorries: **0**
- Moral duplications found: ~5
- Removable/dead code files: ~4
- Naming convention violations: ~3 identifiers

---

## Part 1: Project Architecture

### Critical Dependency Chain

```
Submodule.E8 --> E8Lattice --> E8Packing --> E8Packing_density (= pi^4/384)
                                                     |
       scaledMagic --> LinearProgrammingBound --> SpherePackingConstant_le_E8Packing_density
            |                     |                          |
            g                 Poisson                   MainTheorem
           / \              Summation              (SpherePackingConstant 8 = E8Packing.density)
          a   b                                          
         / \   \                                   periodic_constant_eq_constant
       eig_a  a_zero   eig_b, b_zero           (PeriodicSpherePackingConstant = SpherePackingConstant)
```

### Module Roles

- **Basic/**: Sphere packing definitions, density formula, periodic = general constant
- **E8/**: E8 lattice definition, unimodularity, density computation
- **CohnElkies/**: Linear programming bound via Poisson summation
- **Contour/**: Contour deformation infrastructure (Mobius inversion, wedge set, Poincare lemma)
- **Integration/**: Differentiation under the integral sign, change of variables
- **Tactic/**: Custom tactics (`tendsto_cont`, `norm_numI`, `fun_prop` extensions)
- **ModularForms/**: Eisenstein series, Jacobi theta, Delta, Serre derivative, dimension formulas, FG inequalities
- **MagicFunction/a**: Eigenfunction a (Fourier eigenvalue +1), 6 contour integrals I1-I6
- **MagicFunction/b**: Eigenfunction b (Fourier eigenvalue -1), 6 contour integrals J1-J6
- **MagicFunction/g**: Viazovska's magic function g = linear combination of a and b, sign conditions

---

## Part 2: Longest Proofs (Decomposition Candidates)

| Rank | Declaration | Lines | File |
|------|------------|-------|------|
| 1 | `bRadial_eq_laplace_psiI_main` | ~880 | g/CohnElkies/LaplaceB/LaplaceRepresentation |
| 2 | `exists_bound_norm_psiI'_mul_I_sub_exp_add_const_Ici_one` | ~540 | g/AnotherIntegral/B/PsiICancellation |
| 3 | `exists_phi0_cancellation_bound` | ~400 | g/AnotherIntegral/A/Cancellation/Integrability |
| 4 | `aLaplaceIntegral_convergent` | ~370 | g/CohnElkies/LaplaceA/Basic |
| 5 | `exists_bound_norm_psiS_resToImagAxis_exp_Ici_one` | ~319 | b/Schwartz/PsiExpBounds/PsiSDecay |
| 6 | `hw_tail_bound` | ~300 | g/AnotherIntegral/B/ThetaAxis/InvH2Sq |
| 7 | `exists_bound_norm_H2_resToImagAxis_sub_two_terms_Ici_one` | ~280 | g/AnotherIntegral/B/ThetaAxis/HExpansions |
| 8 | `negDE₂_pos` | ~275 | ModularForms/FG/Positivity |
| 9 | `bLaplaceIntegral_convergent` | ~275 | g/CohnElkies/LaplaceB/Basic |
| 10 | `fourier_g_eq_integral_B_of_ne_two` | ~280 | g/CohnElkies/IntegralB |
| 11 | `J2'_J4_eq_neg_J6'_zero` | ~254 | b/SpecialValues |
| 12 | `fourier_g_eq_integral_B` (limit extension) | ~240 | g/CohnElkies/IntegralB |
| 13 | `perm_I₅` | ~220 | a/Eigenfunction/PermI5Main |
| 14 | `exists_periodicSpherePacking_sep_one_density_gt_of_lt_density` | ~217 | Basic/PeriodicPacking/BoundaryControl |
| 15 | `mFourierCoeff_descended` | ~198 | CohnElkies/PoissonSummation |

---

## Part 3: Dead Code and Removable Declarations

### Files to Remove

1. **`ModularForms/uniformcts.lean`** -- All declarations commented out. Dead file.
2. **`ForMathlib/Asymptotics.lean`** -- Both declarations (`mul_isBigO_mul`, `isBigO_pow`) are literal wrappers around `IsBigO.mul` and `IsBigO.pow`. Remove entirely.
3. **`ModularForms/riemannZetalems.lean`** (15 lines) -- Contains only `zeta_two_eqn` which duplicates the one in `Cauchylems.lean`.

### Declarations to Remove/Inline

4. **`ForMathlib/Cardinal.lean`** -- Single `rfl` lemma `Cardinal.aux`. Remove if unused.
5. **`ModularForms/RamanujanIdentities.lean`** -- Appears to duplicate Ramanujan identity proofs from `Derivative.lean`. Audit for consolidation.

### Pending Mathlib PRs (Remove When Merged)

6. **`ForMathlib/Encard.lean`** (~232 lines, ~42 declarations) -- Porting results from mathlib PR #23503 (Peter Nelson). Remove once merged.
7. **`ForMathlib/MDifferentiableFunProp.lean`** -- `fun_prop` attribute pending PR #33808.

---

## Part 4: Naming Convention Issues

The following identifiers use non-standard capitalization for mathlib:

1. `Inv_Pow_Norm_Summable_Over_Set_Euclidean` -- should be `invPowNormSummableOverSetEuclidean` or restructured
2. `Exists_Inv_Pow_Norm_Summable_Over_Set_Euclidean` -- same
3. `Summable_of_Inv_Pow_Summable` / `Summable_of_Inv_Pow_Summable'` -- should be `summable_of_invPowSummable`
4. `Summable_Inverse_Powers_of_Finite_Orbits` -- should be `summable_inversePowers_of_finite_orbits`
5. `IsDecayingMap` -- acceptable as a Prop/predicate, but the module convention should be consistent

All in `ForMathlib/InvPowSummability.lean`.

---

## Part 5: Key API Summary

### Core Definitions
- `SpherePacking`, `PeriodicSpherePacking`, `SpherePackingConstant`, `PeriodicSpherePackingConstant`
- `Submodule.E8`, `E8Lattice`, `E8Packing`
- `scaledMagic` (the function fed into LinearProgrammingBound)
- `g` (Viazovska's magic function), `a` (Fourier eigenvalue +1), `b` (eigenvalue -1)
- `D` (normalized derivative), `serre_D` (Serre derivative)
- `psiI`, `psiT`, `psiS` (weight -2 modular functions)
- `phi₀`, `phi₀''` (weight 0 modular function and its extension)
- `H₂`, `H₃`, `H₄` (squared Jacobi theta functions)
- `ResToImagAxis` (restriction to positive imaginary axis)

### Central Theorems
- `MainTheorem`: `SpherePackingConstant 8 = E8Packing.density`
- `periodic_constant_eq_constant`: periodic and general packing constants agree
- `LinearProgrammingBound`: Cohn-Elkies LP bound
- `poissonSummation_lattice`: Poisson summation for Z-lattices
- `eig_a`: `Fourier(a) = a`; `eig_b`: `Fourier(b) = -b`
- `g_cohnElkies1`: `g(x) <= 0` for `||x|| >= sqrt(2)`
- `g_cohnElkies2`: `Fourier(g)(x) >= 0`
- `FG_inequality_1/2`: positivity/ordering of F and G modular forms
- `antiSerreDerPos`: monotonicity criterion via Serre derivative
- `jacobi_identity`: `H₂ + H₄ = H₃`
- `Delta_eq_H₂_H₃_H₄`: discriminant as theta product

### Custom Tactics
- `tendsto_cont`: automated limit-composition prover (DFS on `Tendsto` hypotheses + `fun_prop`)
- `norm_numI`: complex number arithmetic in `Complex.mk` form
- `fun_prop` extensions: `MDifferentiable`, `Summable`, `HasSum`, `Integrable`

---

## Part 6: Files > 1000 Lines (Split Candidates)

| File | Lines | Content |
|------|-------|---------|
| ModularForms/Derivative.lean | 1475 | D operator, Serre derivative, slash formula, Ramanujan identities |
| ModularForms/JacobiTheta.lean | 1338 | Theta functions, slash actions, positivity, Delta identity |
| MagicFunction/a/SpecialValues.lean | 1049 | a(0) computation via contour deformation |
| MagicFunction/g/CohnElkies/AnotherIntegral/A/APrimeExtension.lean | 936 | Analytic extension of a' |
| MagicFunction/g/CohnElkies/AnotherIntegral/B/ThetaAxis/HExpansions.lean | 930 | Theta q-expansion bounds |
| MagicFunction/g/CohnElkies/LaplaceB/LaplaceRepresentation.lean | 922 | b' Laplace representation |
| MagicFunction/PolyFourierCoeffBound.lean | 905 | Fourier coefficient bounds |
| ModularForms/EisensteinBase.lean | 879 | Eisenstein q-expansions and basic properties |
| MagicFunction/g/CohnElkies/AnotherIntegral/A/Cancellation/Integrability.lean | 864 | Cancellation integrability |
| MagicFunction/g/CohnElkies/IntegralB.lean | 846 | Fourier(g) integral formula |
| ModularForms/SummableLemmas/QExpansion.lean | 783 | Q-expansion summability |
| MagicFunction/g/CohnElkies/LaplaceA/StripBounds.lean | 786 | Strip growth bounds |

---

## Recommended Action Plan

### Priority 1: Quick Wins (removable dead code)

1. **Delete `ModularForms/uniformcts.lean`** -- All commented out, no active declarations.
2. **Delete `ForMathlib/Asymptotics.lean`** -- Trivial wrappers around existing mathlib API.
3. **Delete `ModularForms/riemannZetalems.lean`** -- Duplicates `Cauchylems.lean`.
4. **Audit `ModularForms/RamanujanIdentities.lean`** for consolidation with `Derivative.lean`.
5. **Delete `ForMathlib/Cardinal.lean`** if unused.

### Priority 2: Naming and Style

6. Rename identifiers in `ForMathlib/InvPowSummability.lean` to mathlib conventions.
7. Clean up non-standard file names: `clog_arg_lems.lean`, `upperhalfplane.lean`, `Cauchylems.lean`, `tendstolems.lean`, `limunder_lems.lean` (use PascalCase).

### Priority 3: Proof Decomposition (high impact)

8. **`bRadial_eq_laplace_psiI_main`** (~880 lines): Extract the 6 contour-piece deformations as separate lemmas.
9. **`exists_bound_norm_psiI'_mul_I_sub_exp_add_const_Ici_one`** (~540 lines): Factor into per-theta-function bounds.
10. **`exists_phi0_cancellation_bound`** (~400 lines): Split into E4, E6, Delta remainder bounds.
11. **`negDE₂_pos`** (~275 lines): Extract the interval-checking arithmetic into helper lemmas.

### Priority 4: File Splitting

12. **`Derivative.lean`** (1475 lines): Split into `D.lean` (basic D operator), `SerreD.lean` (Serre derivative), `DSlash.lean` (slash formula), `Ramanujan.lean` (Ramanujan identities).
13. **`JacobiTheta.lean`** (1338 lines): Split into `JacobiTheta/Basic.lean`, `JacobiTheta/SlashActions.lean`, `JacobiTheta/Positivity.lean`, `JacobiTheta/DeltaIdentity.lean`.

### Priority 5: Mathlib Upstream (when PRs merge)

14. Remove `ForMathlib/Encard.lean` when PR #23503 merges.
15. Remove `ForMathlib/MDifferentiableFunProp.lean` when PR #33808 merges.
16. Upstream small ForMathlib lemmas: `Vec.lean`, `InnerProductSpace.lean`, `ComplexI.lean`, `BoundsOnIcc.lean`.
