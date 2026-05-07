module
public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import SpherePacking.MagicFunction.b.Schwartz.Basic


/-!
# Reductions for the `a'` and `b'` integrals

Rewrites the Schwartz radial profiles `MagicFunction.FourierEigenfunctions.a'`/`b'` to the
real-integral formulas `MagicFunction.a.RealIntegrals.a'`/`MagicFunction.b.RealIntegrals.b'`
when the argument is nonnegative (so the cutoff equals `1`).

## Main statements
* `MagicFunction.g.CohnElkies.a'_eq_realIntegrals_a'`
* `MagicFunction.g.CohnElkies.b'_eq_realIntegrals_b'`
-/

namespace MagicFunction.g.CohnElkies

/--
For `u ≥ 0`, the radial profile `a'` from `MagicFunction.FourierEigenfunctions` agrees with the
real-integral definition `MagicFunction.a.RealIntegrals.a'`.

The prime `'` is part of the standard notation for this radial profile (it is not a derivative).
-/
public lemma a'_eq_realIntegrals_a' {u : ℝ} (hu : 0 ≤ u) :
    (MagicFunction.FourierEigenfunctions.a' : ℝ → ℂ) u = MagicFunction.a.RealIntegrals.a' u := by
  simp [MagicFunction.FourierEigenfunctions.a', MagicFunction.a.RealIntegrals.a',
    MagicFunction.a.SchwartzIntegrals.I₁'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₂'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₃'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₄'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₅'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₆'_apply_of_nonneg, hu]

/--
For `u ≥ 0`, the radial profile `b'` from `MagicFunction.FourierEigenfunctions` agrees with the
real-integral definition `MagicFunction.b.RealIntegrals.b'`.

The prime `'` is part of the standard notation for this radial profile (it is not a derivative).
-/
public lemma b'_eq_realIntegrals_b' {u : ℝ} (hu : 0 ≤ u) :
    (MagicFunction.FourierEigenfunctions.b' : ℝ → ℂ) u = MagicFunction.b.RealIntegrals.b' u := by
  simp [MagicFunction.FourierEigenfunctions.b', MagicFunction.b.RealIntegrals.b',
    MagicFunction.b.SchwartzIntegrals.J₁'_apply_of_nonneg,
    MagicFunction.b.SchwartzIntegrals.J₂'_apply_of_nonneg,
    MagicFunction.b.SchwartzIntegrals.J₃'_apply_of_nonneg,
    MagicFunction.b.SchwartzIntegrals.J₄'_apply_of_nonneg,
    MagicFunction.b.SchwartzIntegrals.J₅'_apply_of_nonneg,
    MagicFunction.b.SchwartzIntegrals.J₆'_apply_of_nonneg, hu]

end MagicFunction.g.CohnElkies
