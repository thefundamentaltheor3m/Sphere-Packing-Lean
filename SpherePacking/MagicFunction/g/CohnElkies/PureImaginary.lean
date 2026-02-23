module
public import SpherePacking.MagicFunction.g.Basic
import SpherePacking.MagicFunction.g.CohnElkies.ImagAxisReal
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Representation
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.AnotherIntegral
import SpherePacking.MagicFunction.a.SpecialValues
import SpherePacking.MagicFunction.b.SpecialValues


/-!
# Purely imaginary values of `a` and `b`

This file shows that Viazovska's eigenfunctions `a` and `b` are purely imaginary-valued.
These lemmas are used to deduce that the specific linear combination defining `g` is real-valued.

## Main statements
* `MagicFunction.g.CohnElkies.a_pureImag`
* `MagicFunction.g.CohnElkies.b_pureImag`
-/

namespace MagicFunction.g.CohnElkies

open scoped FourierTransform SchwartzMap

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open Complex Real MeasureTheory
open MagicFunction.FourierEigenfunctions

namespace PureImaginary

private lemma setIntegral_im_ofReal (f : ℝ → ℝ) :
    (∫ t in Set.Ioi (0 : ℝ), ((f t : ℝ) : ℂ)).im = 0 := by
  simpa using congrArg Complex.im
    (integral_ofReal (μ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) (𝕜 := ℂ) (f := f))

lemma a'_re_eq_zero_of_pos_ne_two {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) : (a' u).re = 0 := by
  have hEq := IntegralReps.aRadial_eq_another_integral_main (u := u) hu hu2
  set Iterm : ℂ :=
      ∫ t in Set.Ioi (0 : ℝ),
        ((((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                ((8640 / π : ℝ) : ℂ) * t -
                ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) *
            Real.exp (-π * u * t))
  set E : ℂ :=
      (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
        (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
        (18144 : ℂ) / (π ^ (3 : ℕ) * u) +
          Iterm
  have hEq' : a' u =
      (4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * E := by
    simpa [E, Iterm, IntegralReps.aAnotherIntegrand, mul_assoc] using hEq
  have hIterm : Iterm.im = 0 := by
    let innerR : ℝ → ℝ := fun t =>
      (t ^ (2 : ℕ)) * (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re -
        (36 / (π ^ (2 : ℕ)) : ℝ) * Real.exp (2 * π * t) +
        (8640 / π : ℝ) * t -
        (18144 / (π ^ (2 : ℕ)) : ℝ)
    have hcongr :
        Iterm = ∫ t in Set.Ioi (0 : ℝ), ((innerR t * Real.exp (-π * u * t) : ℝ) : ℂ) := by
      refine MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := ht
      have hφ :
          φ₀'' ((Complex.I : ℂ) / (t : ℂ)) =
            ((φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re : ℂ) := by
        apply Complex.ext <;> simp [φ₀''_imag_axis_div_im t ht0]
      have hbracket :
          (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                ((8640 / π : ℝ) : ℂ) * t -
                ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) =
            ((innerR t : ℝ) : ℂ) := by
        -- Rewrite each term as `Complex.ofReal` and combine using `ofReal_{add,sub,mul}`.
        set φre : ℝ := (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re
        have hφ' : φ₀'' ((Complex.I : ℂ) / (t : ℂ)) = (φre : ℂ) := by
          simpa [φre] using hφ
        let aR : ℝ := (t ^ (2 : ℕ)) * φre
        let bR : ℝ := (36 / (π ^ (2 : ℕ)) : ℝ) * Real.exp (2 * π * t)
        let cR : ℝ := (8640 / π : ℝ) * t
        let dR : ℝ := (18144 / (π ^ (2 : ℕ)) : ℝ)
        have ha : (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ))) = (aR : ℂ) := by
          rw [hφ']
          simp [aR, Complex.ofReal_mul]
        have hb : (((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t)) = (bR : ℂ) := by
          simp [bR, Complex.ofReal_mul]
        have hc : (((8640 / π : ℝ) : ℂ) * t) = (cR : ℂ) := by
          simp [cR, Complex.ofReal_mul]
        have hd : (((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) = (dR : ℂ) := by
          simp [dR]
        -- Now the bracket is `ofReal (aR - bR + cR - dR)`.
        have hcomb :
            (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                  ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                  ((8640 / π : ℝ) : ℂ) * t -
                  ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) =
                ((aR - bR + cR - dR : ℝ) : ℂ) := by
          -- Rewrite by `ha hb hc hd`, then collapse using `ofReal_add/ofReal_sub`.
          -- (We do this explicitly to avoid `simp` recursion issues.)
          have h1 : (aR : ℂ) - (bR : ℂ) = ((aR - bR : ℝ) : ℂ) := by
            simp [Complex.ofReal_sub]
          have h2 : ((aR - bR : ℝ) : ℂ) + (cR : ℂ) = ((aR - bR + cR : ℝ) : ℂ) := by
            simp [Complex.ofReal_add]
          have h3 :
              ((aR - bR + cR : ℝ) : ℂ) - (dR : ℂ) =
                ((aR - bR + cR - dR : ℝ) : ℂ) := by
            simp [sub_eq_add_neg, add_left_comm, add_comm]
          -- Put everything together.
          calc
            (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                    ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                    ((8640 / π : ℝ) : ℂ) * t -
                    ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) =
                (aR : ℂ) - (bR : ℂ) + (cR : ℂ) - (dR : ℂ) := by
                  rw [ha, hb, hc, hd]
            _ = ((aR - bR : ℝ) : ℂ) + (cR : ℂ) - (dR : ℂ) := by
                  rw [h1]
            _ = ((aR - bR + cR : ℝ) : ℂ) - (dR : ℂ) := by
                  simp [sub_eq_add_neg, add_assoc]
            _ = ((aR - bR + cR - dR : ℝ) : ℂ) := h3
        -- Finish by unfolding `innerR`.
        have hinner : aR - bR + cR - dR = innerR t := by
          simp [innerR, aR, bR, cR, dR, φre]
        -- Replace `innerR t` by the real expression and conclude.
        simpa [hinner] using hcomb
      have hmul :
          ((((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                  ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                  ((8640 / π : ℝ) : ℂ) * t -
                  ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) *
              Real.exp (-π * u * t)) =
            ((innerR t : ℝ) : ℂ) * Real.exp (-π * u * t) :=
        congrArg (fun z : ℂ => z * Real.exp (-π * u * t)) hbracket
      calc
        ((((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                ((8640 / π : ℝ) : ℂ) * t -
                ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) *
            Real.exp (-π * u * t)) =
            ((innerR t : ℝ) : ℂ) * Real.exp (-π * u * t) := by
              simpa using hmul
        _ = ((innerR t * Real.exp (-π * u * t) : ℝ) : ℂ) := by
              simp [Complex.ofReal_mul, mul_assoc]
    have hReal :
        (∫ t in Set.Ioi (0 : ℝ), ((innerR t * Real.exp (-π * u * t) : ℝ) : ℂ)).im = 0 := by
      simpa using
        (setIntegral_im_ofReal (f := fun t => innerR t * Real.exp (-π * u * t)))
    simpa [hcongr] using hReal
  have hpiIm : ((π : ℂ)).im = 0 := by simp
  have hpi3Im : ((π : ℂ) ^ (3 : ℕ)).im = 0 := by
    simpa using Complex.im_pow_eq_zero_of_im_eq_zero hpiIm 3
  have hfrac36 : ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2))).im = 0 := by
    have hden : ((π ^ (3 : ℕ) * (u - 2) : ℂ)).im = 0 := by
      rw [Complex.mul_im]
      simp [hpi3Im]
    simp [Complex.div_im, hden]
  have hfrac8640 : ((8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ))).im = 0 := by
    have hden : ((π ^ (3 : ℕ) * u ^ (2 : ℕ) : ℂ)).im = 0 := by
      have huIm : ((u : ℂ)).im = 0 := by simp
      have hu2Im : ((u : ℂ) ^ (2 : ℕ)).im = 0 := by
        simpa using Complex.im_pow_eq_zero_of_im_eq_zero huIm 2
      rw [Complex.mul_im]
      simp [hpi3Im, hu2Im]
    simp [Complex.div_im, hden]
  have hfrac18144 : ((18144 : ℂ) / (π ^ (3 : ℕ) * u)).im = 0 := by
    have hden : ((π ^ (3 : ℕ) * u : ℂ)).im = 0 := by
      rw [Complex.mul_im]
      simp [hpi3Im]
    simp [Complex.div_im, hden]
  have hEim : E.im = 0 := by
    simp [E, Complex.add_im, Complex.sub_im, hIterm, hfrac36, hfrac8640, hfrac18144]
  rw [hEq']
  have hsin :
      ((Real.sin (π * u / 2) : ℂ) ^ (2 : ℕ)) =
        (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
    simp [Complex.ofReal_pow]
  rw [hsin]
  have hsinIm : (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ).im = 0 := by
    exact Complex.ofReal_im ((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ)
  have hprodIm : ((((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * E).im = 0 := by
    rw [Complex.mul_im]
    rw [hEim, hsinIm]
    simp
  have : ((4 * (Complex.I : ℂ)) * ((((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * E)).re = 0 := by
    rw [Complex.mul_re]
    rw [hprodIm]
    simp
  simpa [mul_assoc] using this

lemma b'_re_eq_zero_of_pos_ne_two {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) : (b' u).re = 0 := by
  have hEq := IntegralReps.bRadial_eq_another_integral_main (u := u) hu hu2
  set Iterm : ℂ :=
      ∫ t in Set.Ioi (0 : ℝ),
        (ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) - Real.exp (2 * π * t)) *
          Real.exp (-π * u * t)
  set E : ℂ :=
      (144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + Iterm
  have hEq' : b' u =
      (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * E := by
    simpa [E, Iterm, IntegralReps.bAnotherIntegrand, mul_assoc] using hEq
  have hψI : ∀ t : ℝ, 0 < t → (ψI' ((Complex.I : ℂ) * (t : ℂ))).im = 0 :=
    fun t ht => ψI'_imag_axis_im t ht
  have hIterm : Iterm.im = 0 := by
    let innerR : ℝ → ℝ := fun t =>
      (ψI' ((Complex.I : ℂ) * (t : ℂ))).re - (144 : ℝ) - Real.exp (2 * π * t)
    have hcongr :
        Iterm = ∫ t in Set.Ioi (0 : ℝ), ((innerR t * Real.exp (-π * u * t) : ℝ) : ℂ) := by
      refine MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := ht
      have hψ :
          ψI' ((Complex.I : ℂ) * (t : ℂ)) =
            ((ψI' ((Complex.I : ℂ) * (t : ℂ))).re : ℂ) := by
        apply Complex.ext <;> simp [hψI t ht0]
      have hbracket :
          (ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) - Real.exp (2 * π * t)) =
            ((innerR t : ℝ) : ℂ) := by
        -- Everything is `ofReal` after replacing `ψI'` by its real part.
        dsimp [innerR]
        rw [hψ]
        -- Now both sides are casts from `ℝ`.
        have hsub1 :
            ((ψI' ((Complex.I : ℂ) * (t : ℂ))).re : ℂ) - (144 : ℂ) =
              (((ψI' ((Complex.I : ℂ) * (t : ℂ))).re - (144 : ℝ) : ℝ) : ℂ) := by
          simp
        have hsub2 :
            (((ψI' ((Complex.I : ℂ) * (t : ℂ))).re - (144 : ℝ) : ℝ) : ℂ) -
                Real.exp (2 * π * t) =
              ((((ψI' ((Complex.I : ℂ) * (t : ℂ))).re - (144 : ℝ)) -
                      Real.exp (2 * π * t) : ℝ) : ℂ) := by
          simp
        -- Assemble.
        calc
          ((ψI' ((Complex.I : ℂ) * (t : ℂ))).re : ℂ) - (144 : ℂ) -
                Real.exp (2 * π * t) =
              (((ψI' ((Complex.I : ℂ) * (t : ℂ))).re - (144 : ℝ) : ℝ) : ℂ) -
                Real.exp (2 * π * t) := by
                simp [sub_eq_add_neg, add_assoc]
          _ =
              ((((ψI' ((Complex.I : ℂ) * (t : ℂ))).re - (144 : ℝ)) -
                      Real.exp (2 * π * t) : ℝ) : ℂ) := hsub2
      calc
        ((ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) - Real.exp (2 * π * t)) *
              Real.exp (-π * u * t)) =
            ((innerR t : ℝ) : ℂ) * Real.exp (-π * u * t) := by
              simpa using congrArg (fun z : ℂ => z * Real.exp (-π * u * t)) hbracket
        _ = ((innerR t * Real.exp (-π * u * t) : ℝ) : ℂ) := by
              simp [Complex.ofReal_mul, mul_assoc]
    have hReal :
        (∫ t in Set.Ioi (0 : ℝ), ((innerR t * Real.exp (-π * u * t) : ℝ) : ℂ)).im = 0 := by
      simpa using
        (setIntegral_im_ofReal (f := fun t => innerR t * Real.exp (-π * u * t)))
    simpa [hcongr] using hReal
  have hfrac144 : ((144 : ℂ) / (π * u)).im = 0 := by
    have hden : ((π * u : ℂ)).im = 0 := by
      rw [Complex.mul_im]
      simp
    simp [Complex.div_im, hden]
  have hfrac1 : ((1 : ℂ) / (π * (u - 2))).im = 0 := by
    have hden : ((π * (u - 2) : ℂ)).im = 0 := by
      rw [Complex.mul_im]
      simp
    simp
  have hEim : E.im = 0 := by
    simp [E, Complex.add_im, hIterm, hfrac144]
  rw [hEq']
  have hsin :
      ((Real.sin (π * u / 2) : ℂ) ^ (2 : ℕ)) =
        (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
    simp [Complex.ofReal_pow]
  rw [hsin]
  have hsinIm : (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ).im = 0 := by
    exact Complex.ofReal_im ((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ)
  have hprodIm : ((((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * E).im = 0 := by
    rw [Complex.mul_im]
    rw [hEim, hsinIm]
    simp
  have :
      ((-4 * (Complex.I : ℂ)) * ((((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * E)).re = 0 := by
    rw [Complex.mul_re]
    rw [hprodIm]
    simp
  simpa [mul_assoc] using this

lemma a'_re_eq_zero_of_pos {u : ℝ} (hu : 0 < u) : (a' u).re = 0 := by
  by_cases hu2 : u = 2
  · -- Extend across the removable point using continuity.
    subst hu2
    have hcont : Continuous fun r : ℝ => (a' r).re :=
      Complex.continuous_re.comp (SchwartzMap.continuous a')
    have hclosed : IsClosed {r : ℝ | (a' r).re = 0} := isClosed_eq hcont continuous_const
    have hsubset : Set.Ioi (0 : ℝ) \ ({2} : Set ℝ) ⊆ {r : ℝ | (a' r).re = 0} := by
      intro r hr
      have hr0 : 0 < r := hr.1
      have hr2 : r ≠ 2 := by
        intro h
        have : r ∈ ({2} : Set ℝ) := by simp [h]
        exact hr.2 this
      exact a'_re_eq_zero_of_pos_ne_two (u := r) hr0 hr2
    have hclosure : closure (Set.Ioi (0 : ℝ) \ ({2} : Set ℝ)) ⊆ {r : ℝ | (a' r).re = 0} :=
      (IsClosed.closure_subset_iff hclosed).2 hsubset
    have hmem : (2 : ℝ) ∈ closure (Set.Ioi (0 : ℝ) \ ({2} : Set ℝ)) := by
      -- Metric characterization of closure at a point.
      rw [Metric.mem_closure_iff]
      intro ε hε
      refine ⟨2 + ε / 2, ?_, ?_⟩
      · have hpos : 0 < ε / 2 := by nlinarith
        refine ⟨?_, ?_⟩
        · have h2 : (0 : ℝ) < 2 := by norm_num
          exact add_pos h2 hpos
        intro h
        have hEq : (2 + ε / 2 : ℝ) = 2 := by simpa using h
        have hzero : ε / 2 = 0 := by
          have := congrArg (fun x : ℝ => x - 2) hEq
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
        exact (ne_of_gt hpos) hzero
      · -- `dist (2 + ε/2) 2 = ε/2 < ε`
        have hpos : 0 < ε / 2 := by nlinarith
        have hdist : dist 2 (2 + ε / 2) = |ε / 2| := by
          -- `dist 2 (2+ε/2) = |2-(2+ε/2)| = |-(ε/2)|`.
          rw [Real.dist_eq]
          simp [sub_eq_add_neg]
        rw [hdist]
        simpa [abs_of_pos hpos] using (by nlinarith : ε / 2 < ε)
    exact hclosure hmem
  · exact a'_re_eq_zero_of_pos_ne_two (u := u) hu hu2

lemma b'_re_eq_zero_of_pos {u : ℝ} (hu : 0 < u) : (b' u).re = 0 := by
  by_cases hu2 : u = 2
  · subst hu2
    have hcont : Continuous fun r : ℝ => (b' r).re :=
      Complex.continuous_re.comp (SchwartzMap.continuous b')
    have hclosed : IsClosed {r : ℝ | (b' r).re = 0} := isClosed_eq hcont continuous_const
    have hsubset : Set.Ioi (0 : ℝ) \ ({2} : Set ℝ) ⊆ {r : ℝ | (b' r).re = 0} := by
      intro r hr
      have hr0 : 0 < r := hr.1
      have hr2 : r ≠ 2 := by
        intro h
        have : r ∈ ({2} : Set ℝ) := by simp [h]
        exact hr.2 this
      exact b'_re_eq_zero_of_pos_ne_two (u := r) hr0 hr2
    have hclosure : closure (Set.Ioi (0 : ℝ) \ ({2} : Set ℝ)) ⊆ {r : ℝ | (b' r).re = 0} :=
      (IsClosed.closure_subset_iff hclosed).2 hsubset
    have hmem : (2 : ℝ) ∈ closure (Set.Ioi (0 : ℝ) \ ({2} : Set ℝ)) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      refine ⟨2 + ε / 2, ?_, ?_⟩
      · have hpos : 0 < ε / 2 := by nlinarith
        refine ⟨?_, ?_⟩
        · have h2 : (0 : ℝ) < 2 := by norm_num
          exact add_pos h2 hpos
        intro h
        have hEq : (2 + ε / 2 : ℝ) = 2 := by simpa using h
        have hzero : ε / 2 = 0 := by
          have := congrArg (fun x : ℝ => x - 2) hEq
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
        exact (ne_of_gt hpos) hzero
      · have hpos : 0 < ε / 2 := by nlinarith
        have hdist : dist 2 (2 + ε / 2) = |ε / 2| := by
          rw [Real.dist_eq]
          simp [sub_eq_add_neg]
        rw [hdist]
        simpa [abs_of_pos hpos] using (by nlinarith : ε / 2 < ε)
    exact hclosure hmem
  · exact b'_re_eq_zero_of_pos_ne_two (u := u) hu hu2

end PureImaginary

/-- The eigenfunction `a` is purely imaginary-valued (its real part vanishes). -/
public theorem a_pureImag : ∀ x : ℝ⁸, (a x).re = 0 := by
  intro x
  by_cases hx : x = 0
  · subst hx
    -- `a(0)` is a purely imaginary constant.
    simp [MagicFunction.a.SpecialValues.a_zero]
  · have hu : 0 < (‖x‖ ^ 2 : ℝ) := by
      simpa using pow_pos (norm_pos_iff.2 hx) 2
    simpa [MagicFunction.FourierEigenfunctions.a, schwartzMap_multidimensional_of_schwartzMap_real,
      SchwartzMap.compCLM_apply] using (PureImaginary.a'_re_eq_zero_of_pos (u := ‖x‖ ^ 2) hu)

/-- The eigenfunction `b` is purely imaginary-valued (its real part vanishes). -/
public theorem b_pureImag : ∀ x : ℝ⁸, (b x).re = 0 := by
  intro x
  by_cases hx : x = 0
  · subst hx
    -- `b(0)=0`.
    simp [MagicFunction.b.SpecialValues.b_zero]
  · have hu : 0 < (‖x‖ ^ 2 : ℝ) := by
      simpa using pow_pos (norm_pos_iff.2 hx) 2
    simpa [MagicFunction.FourierEigenfunctions.b, schwartzMap_multidimensional_of_schwartzMap_real,
      SchwartzMap.compCLM_apply] using (PureImaginary.b'_re_eq_zero_of_pos (u := ‖x‖ ^ 2) hu)

end MagicFunction.g.CohnElkies
