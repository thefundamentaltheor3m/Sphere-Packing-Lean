/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Init
public import Lean.Meta.Tactic.Simp

/-!
# The `d_simps` simp set

The simp set backing the `d_nf` tactic (defined in `SpherePacking.Tactic.DNf`): the
linearity/Leibniz rules of the normalized derivative `D` and the Serre derivative
`serre_D` on `ℍ → ℂ`, together with the base derivative facts of the quasimodular
generators (the Ramanujan identities for `E₂`, `E₄`, `E₆` and the theta analogues
`D_H₂`, `D_H₃`, `D_H₄`).

The attribute lives in its own file because an attribute cannot be used in the same file
where it is declared; the lemmas are tagged at their definition sites
(`SpherePacking.ModularForms.Derivative`, `SpherePacking.ModularForms.RamanujanIdentities`,
`SpherePacking.ModularForms.JacobiTheta.Derivative`).
-/

public meta section

/-- Simp set of the `d_nf` tactic: linearity and Leibniz rules for `D`/`serre_D` together
with the base derivatives of the quasimodular generators (`ramanujan_E₂/E₄/E₆`,
`D_H₂/H₃/H₄`). Side conditions (`MDiff _`) are discharged with `fun_prop`. -/
register_simp_attr d_simps
