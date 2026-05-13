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
* `SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt`
-/

namespace SpherePacking.ForMathlib

open scoped ContDiff

noncomputable section

/-- If `F n` satisfies `HasDerivAt (F n) (F (n + 1) x) x` on an open set `s`, then each `F n` is
`ContDiffOn ℝ ∞` on `s`. -/
public theorem contDiffOn_family_infty_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → ℝ → E} {s : Set ℝ} (hs : IsOpen s)
    (hF : ∀ n : ℕ, ∀ x : ℝ, x ∈ s → HasDerivAt (F n) (F (n + 1) x) x) (n : ℕ) :
    ContDiffOn ℝ ∞ (F n) s := by
  have hdiff k : DifferentiableOn ℝ (F k) s :=
    fun _ hx => (hF k _ hx).differentiableAt.differentiableWithinAt
  have hnat : ∀ m : ℕ, ∀ k : ℕ, ContDiffOn ℝ m (F k) s := by
    intro m
    induction m with
    | zero => intro k; exact contDiffOn_zero.2 (hdiff k).continuousOn
    | succ m ih =>
        intro k
        refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := F k) (s := s) (n := m) hs).2
          ⟨hdiff k, by simp, (ih (k + 1)).congr fun x hx => by simpa using (hF k x hx).deriv⟩
  simpa [contDiffOn_infty] using fun m => hnat m n

end

end SpherePacking.ForMathlib
