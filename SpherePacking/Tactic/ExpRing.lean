/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The `exp_ring` tactic

`ring` treats `Real.exp x` and `Complex.exp x` as opaque atoms, so it cannot prove

```
C * rexp (-(π * (r + 2)) * t) = C * rexp (-2 * π * t) * rexp (-π * r * t)
```

even though this is "obviously" just algebra. Identities of this kind are everywhere in analysis
(Fourier and Laplace transforms, Gaussian integrals, `q`-expansions, generating functions, ...), and
the usual manual proof is some variation on

```
rw [mul_assoc, ← Complex.exp_add]; congr 1; ring_nf; rw [I_sq]; ring_nf
```

in which one has to steer the exponentials next to each other before `← exp_add` applies.

`exp_ring` proves such goals directly. It works in the *opposite* direction to the manual proof:
rather than merging exponentials (which depends on where they sit in a product), it splits every
exponential into exponentials of monomials, which then really are atoms for `ring`.

## Algorithm

1. `ring_nf` puts every exponent into the normal form `m₁ + m₂ + ⋯` of a sum of monomials.
2. `I ^ 2`, `I ^ 3` and `I ^ 4` are simplified and `ring_nf` is run again, so exponents that
   involve the imaginary unit are normalised too.
3. `exp_add`, `exp_sub`, `exp_neg` and `exp_zero` split `exp (m₁ + m₂ + ⋯)` into
   `exp m₁ * exp m₂ * ⋯`, and `exp (m * 2)` becomes `exp m ^ 2` (similarly for other numerals).
4. `field_simp` clears the inverses coming from `exp_neg` (it knows `exp _ ≠ 0`), and `ring1`
   closes the goal. If that fails `grind [Complex.I_sq]` is tried, which handles the remaining
   cases in which `I ^ 2 = -1` is needed outside an exponent.

`exp_ring_nf` performs steps 1–3 only and can be used at hypotheses.

## Limitations

* Non-integer rational coefficients are not split: `exp (x / 2)` stays an atom. So
  `exp (x / 2) ^ 2 = exp x` is out of scope, though `exp (x / 2) * exp y = exp (y + x / 2)` is not.
* Only `Real.exp` and `Complex.exp` are handled, and casts between them are not moved.
-/

public section

open Complex in
/-- `Complex.exp (x * 2) = Complex.exp x ^ 2`, and similarly for other numerals. This is the form
in which `ring_nf` leaves a monomial with a numeric coefficient. The statement uses `ofNat(n)` so
that `simp` can match it against numeric literals. -/
theorem Complex.exp_mul_ofNat (x : ℂ) (n : ℕ) [n.AtLeastTwo] :
    exp (x * ofNat(n)) = exp x ^ (ofNat(n) : ℕ) := by
  rw [mul_comm, ← Nat.cast_ofNat (R := ℂ), Complex.exp_nat_mul]

/-- `Real.exp (x * 2) = Real.exp x ^ 2`, and similarly for other numerals. This is the form in
which `ring_nf` leaves a monomial with a numeric coefficient. -/
theorem Real.exp_mul_ofNat (x : ℝ) (n : ℕ) [n.AtLeastTwo] :
    exp (x * ofNat(n)) = exp x ^ (ofNat(n) : ℕ) := by
  rw [mul_comm, ← Nat.cast_ofNat (R := ℝ), Real.exp_nat_mul]

end

public meta section

/-- `exp_ring_nf` normalises expressions built from ring operations and `Real.exp` /
`Complex.exp`: exponents are put into `ring_nf` normal form (with `I ^ 2 = -1` taken into account),
and then every exponential of a sum is split into a product of exponentials of monomials.

`exp_ring_nf at h` does the same at a hypothesis. See also `exp_ring`, which closes equalities. -/
syntax (name := expRingNF) "exp_ring_nf" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| exp_ring_nf $[$loc]?) => `(tactic| (
      try ring_nf $[$loc]?
      try simp only [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four] $[$loc]?
      try ring_nf $[$loc]?
      try simp only [Complex.exp_add, Complex.exp_sub, Complex.exp_neg, Complex.exp_zero,
        Complex.exp_mul_ofNat, Real.exp_add, Real.exp_sub, Real.exp_neg, Real.exp_zero,
        Real.exp_mul_ofNat] $[$loc]?
      try ring_nf $[$loc]?))

/-- `exp_ring` proves equalities in commutative rings and fields that involve `Real.exp` and
`Complex.exp`, treating `exp (a + b) = exp a * exp b` (and `I ^ 2 = -1` in `ℂ`) as part of the
algebra. For example:

```
example (C r t : ℝ) :
    C * rexp (-(π * (r + 2)) * t) = C * rexp (-2 * π * t) * rexp (-π * r * t) := by
  exp_ring

example (r t : ℂ) :
    cexp (π * I * r * (-1 + t + I)) = cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r) := by
  exp_ring
```

It is a terminal tactic: it fails if it does not close the goal. See `exp_ring_nf` for the
normalisation it is built on, and the module docstring of `SpherePacking.Tactic.ExpRing` for the
algorithm and its limitations. -/
syntax (name := expRing) "exp_ring" : tactic

macro_rules
  | `(tactic| exp_ring) => `(tactic| (
      exp_ring_nf
      try field_simp
      first
        | done
        | ring1
        | grind [Complex.I_sq]
        | fail "exp_ring failed to close the goal; \
            use `exp_ring_nf` to see the normal form it reached"))

end
