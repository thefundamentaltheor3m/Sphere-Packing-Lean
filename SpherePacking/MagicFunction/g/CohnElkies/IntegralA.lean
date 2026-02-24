module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
import SpherePacking.MagicFunction.g.CohnElkies.ImagAxisReal
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.LaplaceRepresentation
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceB.LaplaceRepresentation

/-!
# Integral representation for `gRadial`

This file expresses the radial profile `gRadial` as a Laplace-type integral with kernel `A(t)`.

The proof combines the Laplace representations of `a'` and `b'` with the double-zero property.
This produces the factor `sin(π u / 2)^2` where `u` is the squared norm parameter.

## Main statements
* `MagicFunction.g.CohnElkies.gRadial_eq_integral_A`
-/

namespace MagicFunction.g.CohnElkies

open MeasureTheory Real Complex
open MagicFunction.FourierEigenfunctions

private lemma A_as_complex {t : ℝ} (ht : 0 < t) :
    (A t : ℂ) =
      (-(t ^ (2 : ℕ)) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) +
        (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * ψI' ((Complex.I : ℂ) * (t : ℂ)) := by
  apply Complex.ext <;> simp [A, sub_eq_add_neg, φ₀''_imag_axis_div_im t ht, ψI'_imag_axis_im t ht]

/-- Laplace-type integral formula for `gRadial` in terms of the kernel `A(t)` (for `u > 2`). -/
public theorem gRadial_eq_integral_A {u : ℝ} (hu : 2 < u) :
    gRadial u =
      (π / 2160 : ℂ) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ), (A t : ℂ) * Real.exp (-π * u * t)) := by
  -- Start from the Laplace-type formulas for `a'` and `b'`.
  have ha :=
    MagicFunction.g.CohnElkies.IntegralReps.aRadial_eq_laplace_phi0_main (u := u) hu
  have hb :=
    MagicFunction.g.CohnElkies.IntegralReps.bRadial_eq_laplace_psiI_main (u := u) hu
  -- Abbreviate the two integrals that appear.
  set IA : ℂ :=
    ∫ t in Set.Ioi (0 : ℝ),
      ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) * Real.exp (-π * u * t)
  set IB : ℂ :=
    ∫ t in Set.Ioi (0 : ℝ), ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)
  have ha' : a' u = (4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IA := by
    simpa [IA, mul_assoc] using ha
  have hb' : b' u = (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IB := by
    simpa [IB, mul_assoc] using hb
  -- Rewrite `gRadial u` using the definition and substitute `ha'`/`hb'`.
  have hg :
      gRadial u =
        ((↑π * Complex.I) / 8640 : ℂ) * a' u - (Complex.I / (240 * (↑π)) : ℂ) * b' u := by
    simp [gRadial, sub_eq_add_neg, SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul]
  -- Compute the scalar coefficients.
  have hcoefA :
      ((↑π * Complex.I) / 8640 : ℂ) * (4 * (Complex.I : ℂ)) = -(π / 2160 : ℂ) := by
    -- Pure arithmetic in `ℂ` using `I^2 = -1`.
    have : ((↑π * Complex.I) / 8640 : ℂ) * (4 * (Complex.I : ℂ)) = -(↑π / 2160 : ℂ) := by
      -- Reduce to `I * (I * x) = -x`.
      ring_nf
      simp
      ring
    simpa using this
  have hcoefB :
      (-(Complex.I / (240 * (↑π)) : ℂ)) * (-4 * (Complex.I : ℂ)) = -(1 / (60 * π) : ℂ) := by
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    -- Clear denominators in `ℂ`.
    field_simp [hπ]
    ring_nf
    simp
  -- Express the RHS integral in terms of `IA` and `IB`.
  have hA_integral :
      (∫ t in Set.Ioi (0 : ℝ), (A t : ℂ) * Real.exp (-π * u * t)) =
        -IA + (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * IB := by
    -- Rewrite `A t` pointwise using `A_as_complex`.
    have hset :
        (∫ t in Set.Ioi (0 : ℝ), (A t : ℂ) * Real.exp (-π * u * t)) =
          ∫ t in Set.Ioi (0 : ℝ),
            (((-(t ^ (2 : ℕ)) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) +
                (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * ψI' ((Complex.I : ℂ) * (t : ℂ))) *
              Real.exp (-π * u * t)) := by
      refine MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi ?_
      intro t ht
      simp [A_as_complex (t := t) ht]
    -- Now expand and recognize `IA` and `IB`.
    rw [hset]
    -- Use integrability of the Laplace kernels (available as lemmas in `IntegralReps`).
    have hIntA :
        IntegrableOn
            (fun t : ℝ =>
              ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
                Real.exp (-π * u * t))
            (Set.Ioi (0 : ℝ)) := by
      -- This is exactly `aLaplaceIntegrand`.
      simpa [MagicFunction.g.CohnElkies.IntegralReps.aLaplaceIntegrand, mul_assoc] using
        (MagicFunction.g.CohnElkies.IntegralReps.aLaplaceIntegral_convergent (u := u) hu)
    have hIntB :
        IntegrableOn
            (fun t : ℝ =>
              ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t))
            (Set.Ioi (0 : ℝ)) := by
      simpa [MagicFunction.g.CohnElkies.IntegralReps.bLaplaceIntegrand] using
        (MagicFunction.g.CohnElkies.IntegralReps.bLaplaceIntegral_convergent (u := u) hu)
    set c : ℂ := (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)
    -- Split the integral into the two pieces and identify `IA` and `IB`.
    have hsplit :
        (fun t : ℝ =>
            (((-(t ^ (2 : ℕ)) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) +
                c * ψI' ((Complex.I : ℂ) * (t : ℂ))) *
              Real.exp (-π * u * t))) =
          fun t : ℝ =>
            -(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
                Real.exp (-π * u * t)) +
              c * (ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)) := by
      funext t
      have hneg :
          (-(t ^ (2 : ℕ) : ℂ)) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) * Real.exp (-π * u * t) =
            -(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
                Real.exp (-π * u * t)) := by
        -- `(-a) * (b * c) = -(a * (b * c))`, then reassociate.
        simp [mul_assoc]
      calc
        (((-(t ^ (2 : ℕ)) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) +
                c * ψI' ((Complex.I : ℂ) * (t : ℂ))) *
              Real.exp (-π * u * t)) =
            (-(t ^ (2 : ℕ) : ℂ)) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) * Real.exp (-π * u * t) +
              c * ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t) := by
            simp [add_mul, mul_assoc]
        _ =
            -(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
                  Real.exp (-π * u * t)) +
              c * (ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)) := by
            simp [mul_assoc, c]
    rw [hsplit]
    -- Use `integral_add` on the restricted measure.
    have hIntA0 :
        Integrable
            (fun t : ℝ =>
              ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
                Real.exp (-π * u * t))
            ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
      simpa [IntegrableOn] using hIntA
    have hIntA'' : Integrable (fun t : ℝ =>
        -(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
            Real.exp (-π * u * t)))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
      exact hIntA0.neg
    have hIntB0 :
        Integrable
            (fun t : ℝ =>
              ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t))
            ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
      simpa [IntegrableOn] using hIntB
    have hIntB'' :
        Integrable
            (fun t : ℝ =>
              c * (ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)))
            ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
      exact hIntB0.const_mul c
    -- Rewrite the set integral as an integral over the restricted measure.
    change
        (∫ t : ℝ,
            -(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
                Real.exp (-π * u * t)) +
              c * (ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)) ∂
            ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) =
          -IA + c * IB
    -- Split the integral and simplify.
    rw [MeasureTheory.integral_add hIntA'' hIntB'']
    -- Identify the two integrals with `IA` and `IB`.
    simp [IA, IB, c, mul_assoc, MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]
  -- Pull out the common `sin^2` factor and use `hA_integral`.
  have hmain :
      ((↑π * Complex.I) / 8640 : ℂ) *
              ((4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IA) +
          (-(Complex.I / (240 * (↑π)) : ℂ)) *
              ((-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IB) =
        (π / 2160 : ℂ) *
          (Real.sin (π * u / 2)) ^ (2 : ℕ) *
            (-IA + (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * IB) := by
    -- Make the implicit coercions `ℝ → ℂ` explicit to avoid `simp` rewriting the sine factor.
    change
        ((↑π * Complex.I) / 8640 : ℂ) *
              ((4 * (Complex.I : ℂ)) *
                    ((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) * IA) +
            (-(Complex.I / (240 * (↑π)) : ℂ)) *
              ((-4 * (Complex.I : ℂ)) *
                    ((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) * IB) =
          (π / 2160 : ℂ) * ((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) *
            (-IA + (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * IB)
    -- The only nontrivial numeric identity is `(π/2160) * (-(36/π^2)) = -(1/(60*π))`.
    have h36 :
        (π / 2160 : ℂ) * (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) = (-(1 / (60 * π)) : ℂ) := by
      have h36R :
          (π / 2160 : ℝ) * (-(36 / (π ^ (2 : ℕ)) : ℝ)) = -(1 / (60 * π)) := by
        have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
        field_simp [hπ]
        norm_num
      exact_mod_cast h36R
    have hc :
        (-(1 / (60 * π)) : ℂ) =
          (π / 2160 : ℂ) * (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) := by
      simpa using h36.symm
    -- Pull out the `((↑π*I)/8640) * (4*I)` and `(I/(240*π)) * (4*I)` scalar products.
    have hA :
        ((↑π * Complex.I) / 8640 : ℂ) *
              ((4 * (Complex.I : ℂ)) * ((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) * IA) =
          (-(π / 2160 : ℂ)) *
            (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) * IA) := by
      calc
        ((↑π * Complex.I) / 8640 : ℂ) *
              ((4 * (Complex.I : ℂ)) * ((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) * IA)
            =
                (((↑π * Complex.I) / 8640 : ℂ) * (4 * (Complex.I : ℂ))) *
                  (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) * IA) := by
                -- Reassociate `a * (b * s * IA)` into `(a*b) * (s*IA)`.
                rw [← mul_assoc ((↑π * Complex.I) / 8640 : ℂ)
                    ((4 * (Complex.I : ℂ)) * ((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ)) IA]
                rw [← mul_assoc ((↑π * Complex.I) / 8640 : ℂ) (4 * (Complex.I : ℂ))
                    ((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ)]
                rw [mul_assoc (((↑π * Complex.I) / 8640 : ℂ) * (4 * (Complex.I : ℂ)))
                    ((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) IA]
        _ = (-(π / 2160 : ℂ)) * (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) * IA) := by
              simpa using congrArg (fun z : ℂ =>
                z * (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) * IA)) hcoefA
    have hB :
        (-(Complex.I / (240 * (↑π)) : ℂ)) *
              ((-4 * (Complex.I : ℂ)) * ((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) * IB) =
          (-(1 / (60 * π)) : ℂ) *
            (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) * IB) := by
      calc
        (-(Complex.I / (240 * (↑π)) : ℂ)) *
              ((-4 * (Complex.I : ℂ)) * ((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) * IB)
            =
                ((-(Complex.I / (240 * (↑π)) : ℂ)) * (-4 * (Complex.I : ℂ))) *
                  (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) * IB) := by
                rw [← mul_assoc (-(Complex.I / (240 * (↑π)) : ℂ))
                    ((-4 * (Complex.I : ℂ)) * ((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ)) IB]
                rw [← mul_assoc (-(Complex.I / (240 * (↑π)) : ℂ)) (-4 * (Complex.I : ℂ))
                    ((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ)]
                rw [mul_assoc ((-(Complex.I / (240 * (↑π)) : ℂ)) * (-4 * (Complex.I : ℂ)))
                    ((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) IB]
        _ = (-(1 / (60 * π)) : ℂ) * (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) * IB) := by
              simpa using congrArg (fun z : ℂ =>
                z * (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℂ) * IB)) hcoefB
    -- Substitute the coefficient computations and finish by ring arithmetic.
    rw [hA, hB, hc]
    ring
  -- Finish by rewriting the RHS using `hA_integral`.
  calc
    gRadial u
        =
          ((↑π * Complex.I) / 8640 : ℂ) * a' u + (-(Complex.I / (240 * (↑π)) : ℂ)) * b' u := by
          simpa [sub_eq_add_neg] using hg
    _ =
          ((↑π * Complex.I) / 8640 : ℂ) *
              ((4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IA) +
            (-(Complex.I / (240 * (↑π)) : ℂ)) *
              ((-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IB) := by
          simp [ha', hb', mul_assoc, mul_left_comm, mul_comm]
    _ =
          (π / 2160 : ℂ) *
            (Real.sin (π * u / 2)) ^ (2 : ℕ) *
              (-IA + (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * IB) := by
          simpa [mul_assoc] using hmain
    _ = (π / 2160 : ℂ) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ), (A t : ℂ) * Real.exp (-π * u * t)) := by
          -- Rewrite the RHS using the previously established identity.
          rw [← hA_integral]

end MagicFunction.g.CohnElkies
