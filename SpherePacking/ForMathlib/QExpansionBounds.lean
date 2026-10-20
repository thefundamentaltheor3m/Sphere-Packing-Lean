/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import SpherePacking.ForMathlib.QSeriesBounds

/-!
# Pointwise bounds from canonical q-expansions

Specialise the coefficient-level bounds of `SpherePacking.ForMathlib.QSeriesBounds` to the
canonical `qExpansion` coefficients of a 1-periodic holomorphic function bounded at infinity.
Summability of the weighted coefficient norms at every positive reference height follows from
`hasSum_qExpansion`, so no separate summability or series-identity hypothesis is needed.
-/

@[expose] public section

open Real Complex
open scoped Manifold

namespace UpperHalfPlane

/-- The weighted `q`-coefficients of a 1-periodic holomorphic function bounded at infinity
are summable at every positive reference height. -/
lemma summable_norm_qExpansion_mul_exp {F : ℍ → ℂ}
    (hper : Function.Periodic (F ∘ ofComplex) 1) (hhol : MDiff F)
    (hbdd : IsBoundedAtImInfty F) {c : ℝ} (hc : 0 < c) :
    Summable fun m : ℕ ↦ ‖(qExpansion 1 F).coeff m‖ * rexp (-(2 * π * c) * m) := by
  let zc : ℍ := ⟨c * Complex.I, by simpa using hc⟩
  refine (hasSum_qExpansion one_pos hper hhol hbdd zc).summable.norm.congr fun m ↦ ?_
  rw [norm_smul, norm_pow, Function.Periodic.norm_qParam, div_one, ← Real.exp_nat_mul]
  congr 2
  simp [zc]
  ring

/-- Bound a 1-periodic holomorphic function bounded at infinity whose canonical `q`-coefficients
vanish below `n₀`. Summability at the positive reference height `c` is automatic. -/
lemma norm_le_qExpansion_of_coeff_vanish {F : ℍ → ℂ}
    (hper : Function.Periodic (F ∘ ofComplex) 1) (hhol : MDiff F)
    (hbdd : IsBoundedAtImInfty F) (n₀ : ℕ)
    (hvan : ∀ m < n₀, (qExpansion 1 F).coeff m = 0)
    {c : ℝ} (hc : 0 < c) {z : ℍ} (hz : c ≤ z.im) :
    ‖F z‖ ≤ (∑' m : ℕ, ‖(qExpansion 1 F).coeff m‖ * rexp (-(2 * π * c) * m)) *
      rexp (-(2 * π) * n₀ * (z.im - c)) := by
  have hterm (m : ℕ) : Function.Periodic.qParam 1 z ^ m = cexp (2 * π * Complex.I * m * z) := by
    rw [Function.Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [← (hasSum_qExpansion one_pos hper hhol hbdd z).tsum_eq]
  simp_rw [smul_eq_mul, hterm]
  exact Complex.norm_qseries_le_of_coeff_vanish n₀ hvan
    (summable_norm_qExpansion_mul_exp hper hhol hbdd hc) hz

end UpperHalfPlane
