module
public import Mathlib.Data.Complex.Basic

/-!
# Lemmas about `Complex.I`

These are intentionally kept in a small, stable helper module so other files can use them
without importing large modular-forms developments.
-/

open Complex

/-- Simplify `I * (I * x)` to `-x`. -/
@[grind =] public lemma I_mul_I_mul (x : ℂ) : I * (I * x) = -x := by
  simpa [mul_assoc, I_mul_I] using (mul_assoc I I x).symm
