/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# A `grind` set for complex arithmetic

`grind` has a commutative-ring solver and a linear-arithmetic solver, and Mathlib already tells it
how to unfold membership in intervals (`Set.mem_Icc` and friends are tagged `@[grind =]`). What it
does not know out of the box is anything about `ℂ`: that `I ^ 2 = -1`, or how `re` and `im` interact
with arithmetic. This file supplies those facts as a **scoped** set of `grind` annotations, so that
after

```
open scoped ComplexGrind
```

plain `grind` proves goals such as

```
example (t : ℝ) : (I * t) ^ 2 = -(t : ℂ) ^ 2
example (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : 0 < (-1 + I * t).im
example (z c : ℂ) (hz : 0 < z.im) (hc : c.im = 0) : z + c ≠ 0
example (z : ℍ) : (z : ℂ) ≠ 0
```

These are exactly the side conditions that come up when working with paths in `ℂ` and with the
upper half-plane: positivity of an imaginary part, non-vanishing of a denominator, and ring
identities modulo `I ^ 2 = -1`. In this repository they were previously discharged by long
`simp only [mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add, ...]` calls or
by `ring_nf; rw [I_sq]; ring_nf`.

Because `grind` becomes a competent discharger for such goals, `fun_prop (disch := grind)` and
`simp (disch := grind)` become useful too. For example
`ContinuousOn (fun t : ℝ ↦ (-1 : ℂ) / (I * t)) (Ioi 0)` is proved by `fun_prop (disch := grind)`.

## Contents of the set

* `Complex.I_sq` and `Complex.I_ne_zero`, instantiated whenever `I` occurs in the goal. The first
  turns the ring solver into a solver for `ℂ` as `ℝ[I] / (I ^ 2 + 1)`.
* `re` and `im` of `+`, `-`, unary `-`, `*`, `I`, numerals and real coercions, as `@[grind =]`
  rewrite rules. Together with the linear-arithmetic solver this decides sign conditions on real
  and imaginary parts.
* `Complex.ofReal_eq_zero` and `Complex.ofReal_inj`.
* `UpperHalfPlane.coe_im_pos`, instantiated whenever a coercion `(z : ℂ)` of `z : ℍ` occurs.

## Why scoped?

Lean does not yet have user-defined `grind` attribute sets, so a scoped set of annotations in a
namespace is the closest substitute: it has to be opened explicitly, and it does not change the
behaviour of any `grind` call elsewhere. If these annotations were upstreamed they would simply
become attributes on the Mathlib lemmas.

Deliberately *not* included is `Complex.ext_iff`. It would make `grind` split every equation in `ℂ`
into real and imaginary parts, which is too expensive as a default.

## Caveats

* `grind` reads the whole local context. In a goal with many hypotheses about products and
  inverses it can lose itself in case splits on which denominators vanish, even when the goal on
  its own is easy. State the identity as a separate `have … := by grind` (or `clear` what is not
  needed) in that situation.
* There are no rules for `re` and `im` of `z⁻¹`, `z / w` or `z ^ n`. Clear denominators first, as in
  `field_simp; grind`.
-/

public section

namespace ComplexGrind

/-! ### The imaginary unit -/

scoped grind_pattern Complex.I_sq => Complex.I
scoped grind_pattern Complex.I_ne_zero => Complex.I

/-! ### Real and imaginary parts -/

attribute [scoped grind =]
  Complex.ofReal_re Complex.ofReal_im Complex.I_re Complex.I_im
  Complex.zero_re Complex.zero_im Complex.one_re Complex.one_im
  Complex.add_re Complex.add_im Complex.sub_re Complex.sub_im
  Complex.neg_re Complex.neg_im Complex.mul_re Complex.mul_im
  Complex.ofReal_eq_zero Complex.ofReal_inj

scoped grind_pattern Complex.re_ofNat => (OfNat.ofNat n : ℂ).re
scoped grind_pattern Complex.im_ofNat => (OfNat.ofNat n : ℂ).im

/-! The real and imaginary parts of `I` and of a real coercion are also asserted as soon as the
number itself occurs. This is what lets `grind` refute `(t : ℂ) + I = 0`: the ring solver rewrites
the hypothesis to `(t : ℂ) = -I`, and the two sides have different imaginary parts. -/

scoped grind_pattern Complex.I_re => Complex.I
scoped grind_pattern Complex.I_im => Complex.I
scoped grind_pattern Complex.ofReal_re => (r : ℂ)
scoped grind_pattern Complex.ofReal_im => (r : ℂ)

/-! ### The upper half-plane -/

scoped grind_pattern UpperHalfPlane.coe_im_pos => self.coe

end ComplexGrind
