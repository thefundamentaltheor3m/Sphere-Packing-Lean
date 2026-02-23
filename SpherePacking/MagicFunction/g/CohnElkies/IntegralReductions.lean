module
public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import SpherePacking.MagicFunction.b.Schwartz.Basic


/-!
# Reductions for the `a'` and `b'` integrals

These lemmas rewrite the Schwartz radial profiles `MagicFunction.FourierEigenfunctions.a'` and
`MagicFunction.FourierEigenfunctions.b'` to the corresponding real-integral formulas
`MagicFunction.a.RealIntegrals.a'` and `MagicFunction.b.RealIntegrals.b'` when the argument is
nonnegative (so the cutoff equals `1`).

## Main statements
* `MagicFunction.g.CohnElkies.a'_eq_realIntegrals_a'`
* `MagicFunction.g.CohnElkies.b'_eq_realIntegrals_b'`
-/

namespace MagicFunction.g.CohnElkies

private lemma sum_I'_eq_sum_realIntegrals_I' {u : ℝ} (hu : 0 ≤ u) :
    MagicFunction.a.SchwartzIntegrals.I₁' u + MagicFunction.a.SchwartzIntegrals.I₂' u +
          MagicFunction.a.SchwartzIntegrals.I₃' u + MagicFunction.a.SchwartzIntegrals.I₄' u +
      MagicFunction.a.SchwartzIntegrals.I₅' u +
      MagicFunction.a.SchwartzIntegrals.I₆' u =
    MagicFunction.a.RealIntegrals.I₁' u + MagicFunction.a.RealIntegrals.I₂' u +
          MagicFunction.a.RealIntegrals.I₃' u + MagicFunction.a.RealIntegrals.I₄' u +
      MagicFunction.a.RealIntegrals.I₅' u +
      MagicFunction.a.RealIntegrals.I₆' u := by
  simp [MagicFunction.a.SchwartzIntegrals.I₁'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₂'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₃'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₄'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₅'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₆'_apply_of_nonneg, hu]

private lemma sum_J'_eq_sum_realIntegrals_J' {u : ℝ} (hu : 0 ≤ u) :
    MagicFunction.b.SchwartzIntegrals.J₁' u + MagicFunction.b.SchwartzIntegrals.J₂' u +
          MagicFunction.b.SchwartzIntegrals.J₃' u + MagicFunction.b.SchwartzIntegrals.J₄' u +
      MagicFunction.b.SchwartzIntegrals.J₅' u +
      MagicFunction.b.SchwartzIntegrals.J₆' u =
    MagicFunction.b.RealIntegrals.J₁' u + MagicFunction.b.RealIntegrals.J₂' u +
          MagicFunction.b.RealIntegrals.J₃' u + MagicFunction.b.RealIntegrals.J₄' u +
      MagicFunction.b.RealIntegrals.J₅' u +
      MagicFunction.b.RealIntegrals.J₆' u := by
  simp [MagicFunction.b.SchwartzIntegrals.J₁'_apply_of_nonneg,
    MagicFunction.b.SchwartzIntegrals.J₂'_apply_of_nonneg,
    MagicFunction.b.SchwartzIntegrals.J₃'_apply_of_nonneg,
    MagicFunction.b.SchwartzIntegrals.J₄'_apply_of_nonneg,
    MagicFunction.b.SchwartzIntegrals.J₅'_apply_of_nonneg,
    MagicFunction.b.SchwartzIntegrals.J₆'_apply_of_nonneg, hu]

/--
For `u ≥ 0`, the radial profile `a'` from `MagicFunction.FourierEigenfunctions` agrees with the
real-integral definition `MagicFunction.a.RealIntegrals.a'`.

The prime `'` is part of the standard notation for this radial profile (it is not a derivative).
-/
public lemma a'_eq_realIntegrals_a' {u : ℝ} (hu : 0 ≤ u) :
    (MagicFunction.FourierEigenfunctions.a' : ℝ → ℂ) u = MagicFunction.a.RealIntegrals.a' u := by
  simpa [MagicFunction.FourierEigenfunctions.a', MagicFunction.a.RealIntegrals.a'] using
    sum_I'_eq_sum_realIntegrals_I' (u := u) hu

/--
For `u ≥ 0`, the radial profile `b'` from `MagicFunction.FourierEigenfunctions` agrees with the
real-integral definition `MagicFunction.b.RealIntegrals.b'`.

The prime `'` is part of the standard notation for this radial profile (it is not a derivative).
-/
public lemma b'_eq_realIntegrals_b' {u : ℝ} (hu : 0 ≤ u) :
    (MagicFunction.FourierEigenfunctions.b' : ℝ → ℂ) u = MagicFunction.b.RealIntegrals.b' u := by
  simpa [MagicFunction.FourierEigenfunctions.b', MagicFunction.b.RealIntegrals.b'] using
    sum_J'_eq_sum_realIntegrals_J' (u := u) hu

end MagicFunction.g.CohnElkies
