module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# `ContDiffOn` from a derivative recursion

If a family `F n` satisfies the recursion

`HasDerivAt (F n) (F (n + 1) x) x`

on an open set `s`, then each `F n` is `C^m` on `s` for all finite `m`, hence `C^∞`.

This helper avoids duplicating the same `ContDiffOn` induction in multiple magic-function files.

## Main statements
* `SpherePacking.ForMathlib.contDiffOn_family_nat_of_hasDerivAt`
* `SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt`
-/

namespace SpherePacking.ForMathlib

open scoped ContDiff

noncomputable section

/--
If `F n` satisfies `HasDerivAt (F n) (F (n + 1) x) x` on an open set `s`, then each `F n` is
`ContDiffOn` of order `m` on `s`, for every finite `m`.
-/
public lemma contDiffOn_family_nat_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → ℝ → E} {s : Set ℝ} (hs : IsOpen s)
    (hF : ∀ n : ℕ, ∀ x : ℝ, x ∈ s → HasDerivAt (F n) (F (n + 1) x) x) :
    ∀ m : ℕ, ∀ n : ℕ, ContDiffOn ℝ m (F n) s := by
  have hdiff : ∀ n : ℕ, DifferentiableOn ℝ (F n) s :=
    fun n _ hx => (hF n _ hx).differentiableAt.differentiableWithinAt
  intro m
  induction m with
  | zero =>
      intro n
      exact contDiffOn_zero.2 (hdiff n).continuousOn
  | succ m ih =>
      intro n
      refine
        (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := F n) (s := s) (n := m) hs).2
          ⟨hdiff n, by simp,
            (ih (n + 1)).congr fun x hx => by simpa using (hF n x hx).deriv⟩

/-- Upgrade `contDiffOn_family_nat_of_hasDerivAt` to the `C^∞` statement. -/
public theorem contDiffOn_family_infty_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → ℝ → E} {s : Set ℝ} (hs : IsOpen s)
    (hF : ∀ n : ℕ, ∀ x : ℝ, x ∈ s → HasDerivAt (F n) (F (n + 1) x) x) (n : ℕ) :
    ContDiffOn ℝ ∞ (F n) s := by
  simpa [contDiffOn_infty] using fun m =>
    contDiffOn_family_nat_of_hasDerivAt (F := F) (s := s) hs hF m n

end

end SpherePacking.ForMathlib
