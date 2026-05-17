module
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import SpherePacking.ModularForms.SummableLemmas.Basic
public import SpherePacking.ModularForms.SummableLemmas.QExpansion

/-!
# Multipliability lemmas for product expansions

This file records basic `Multipliable` and `tprod` lemmas used in modular form product
expansions (notably eta and delta product formulas).

## Main statements
* `MultipliableEtaProductExpansion`
* `MultipliableDeltaProductExpansion_pnat`
* `Multipliable_pow`
-/

open scoped BigOperators Real
open UpperHalfPlane Complex

/-- A basic nonvanishing lemma for the factors in the eta product on `ℍ`. -/
public theorem term_ne_zero (z : ℍ) (n : ℕ) :
    1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑z) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  simpa [h.symm] using exp_upperHalfPlane_lt_one_nat z n

/-- The eta product factors `∏ (1 - exp(2π i (n+1) z))` form a convergent infinite product. -/
public lemma MultipliableEtaProductExpansion (z : ℍ) :
    Multipliable (fun (n : ℕ) => (1 - cexp (2 * π * Complex.I * (n + 1) * z))) := by
  refine (Complex.multipliable_of_summable_log
    (Complex.summable_log_one_add_of_summable (f := fun n : ℕ ↦
      -cexp (2 * π * Complex.I * (n + 1) * z)) ?_)).congr ?_
  · rw [← summable_norm_iff]
    simpa using summable_exp_pow z
  intro n
  simp [sub_eq_add_neg]

/-- A `ℕ+`-indexed variant of `MultipliableEtaProductExpansion`. -/
public lemma MultipliableEtaProductExpansion_pnat (z : ℍ) :
    Multipliable (fun (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z))) := by
  refine (multipliable_pnat_iff_multipliable_succ
    (f := fun n : ℕ ↦ (1 - cexp (2 * π * Complex.I * n * z)))).2 ?_
  simpa using MultipliableEtaProductExpansion z

/-- If `f` is multipliable, then so is `fun i => f i ^ n`. -/
public lemma Multipliable_pow {ι : Type*} (f : ι → ℂ) (hf : Multipliable f) (n : ℕ) :
    Multipliable (fun i => f i ^ n) := by
  simpa using hf.map (g := powMonoidHom n) (hg := by simpa using continuous_pow n)

/-- The delta product factors `∏ (1 - exp(2π i n z))^24` form a convergent infinite product. -/
public lemma MultipliableDeltaProductExpansion_pnat (z : ℍ) :
    Multipliable (fun (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z)) ^ 24) :=
  Multipliable_pow _ (MultipliableEtaProductExpansion_pnat z) 24

