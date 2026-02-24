module

public import SpherePacking.Contour.PermJ12Contour
public import SpherePacking.Basic.Domains.WedgeSet
public import SpherePacking.Contour.MobiusInv.Segments
import SpherePacking.Contour.MobiusInv.WedgeSet
import SpherePacking.Contour.MobiusInv.LineMap
import SpherePacking.Contour.Segments
import SpherePacking.Contour.MobiusInv.ContourChange

/-!
# Contour identities for `mobiusInv` on `wedgeSet`

This file specializes the abstract contour deformation lemmas in
`SpherePacking.Contour.PermJ12Contour` to the concrete domain `SpherePacking.wedgeSet`
and map `SpherePacking.mobiusInv`.

It provides the shared "assembled contour identity" lemmas used in the `perm_J1/J2` and
`perm_I1/I2` developments, factoring out:
- the two Mobius segment contour-change lemmas; and
- the two wedge-set contour deformation steps (`h1`/`h2`).
-/

open MeasureTheory
open MagicFunction

namespace SpherePacking

noncomputable section

open SpherePacking.Contour

lemma perm_J12_contour_h1_mobiusInv_wedgeSet
    {Ψ₁' : ℝ → ℂ → ℂ}
    (closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet)
    (r : ℝ) :
    (∫ᶜ z in mobiusInv_segment_z₁, scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment (mobiusInv ((-1 : ℂ) + Complex.I)) ((1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁' r) z =
      ∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I), scalarOneForm (Ψ₁' r) z := by
  have h :
      PermJ12ContourH1Hyp mobiusInv wedgeSet := by
    refine
      { continuousOn_mobiusInv_segment_z₁ :=
          continuousOn_mobiusInv_segment_z₁
        mobiusInv_neg_one := by simp [mobiusInv]
        homotopy_mem_wedgeSet := ?_
        contDiffOn_homotopy := ?_ }
    · intro x y hx hy
      exact
        convex_wedgeSet.lineMap_mem (mobiusInv_lineMap_z₁_mem_wedgeSet (t := y) hy.1 hy.2)
          (lineMap_z₃line_mem_wedgeSet (t := y) hy.1) ⟨hx.1.le, hx.2.le⟩
    · refine contDiffOn_lineMap_mobiusInv_lineMap _ _ _ _ ?_
      rintro ⟨_x, y⟩ ⟨h0, h1⟩
      exact segment_z₁_ne_zero ⟨y, ⟨h0.2, h1.2⟩⟩
  have hArgs :
      PermJ12ContourH1Args mobiusInv Ψ₁' wedgeSet :=
    { closed_ω_wedgeSet := closed_ω_wedgeSet
      hyp := h }
  exact perm_J12_contour_h1 hArgs r

lemma perm_J12_contour_h2_mobiusInv_wedgeSet
    {Ψ₁' : ℝ → ℂ → ℂ}
    (closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet)
    (r : ℝ) :
    ∫ᶜ z in mobiusInv_segment_z₂, scalarOneForm (Ψ₁' r) z =
      (∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I, scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment (mobiusInv ((-1 : ℂ) + Complex.I)) ((1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁' r) z := by
  have h :
      PermJ12ContourH2Hyp mobiusInv wedgeSet := by
    refine
      { continuousOn_mobiusInv_segment_z₂ :=
          continuousOn_mobiusInv_segment_z₂
        mobiusInv_I := by simp [mobiusInv]
        homotopy_mem_wedgeSet := ?_
        contDiffOn_homotopy := ?_ }
    · intro x y hx hy
      exact
        convex_wedgeSet.lineMap_mem (mobiusInv_lineMap_z₂_mem_wedgeSet (t := y) hy.1 hy.2)
          (lineMap_z₄line_mem_wedgeSet (t := y) hy.1 hy.2) ⟨hx.1.le, hx.2.le⟩
    · refine contDiffOn_lineMap_mobiusInv_lineMap _ _ _ _ ?_
      rintro ⟨_x, y⟩ ⟨h0, h1⟩
      exact segment_z₂_ne_zero ⟨y, ⟨h0.2, h1.2⟩⟩
  have hArgs :
      PermJ12ContourH2Args mobiusInv Ψ₁' wedgeSet :=
    { closed_ω_wedgeSet := closed_ω_wedgeSet
      hyp := h }
  exact perm_J12_contour_h2 hArgs r

private lemma perm_12_contour_mobiusInv_wedgeSet_aux
    {Ψ₁_fourier Ψ₁' : ℝ → ℂ → ℂ}
    (s : ℂ)
    (closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet)
    (r : ℝ)
    (hseg1 :
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
            scalarOneForm (Ψ₁_fourier r) z) =
        s * ∫ᶜ z in mobiusInv_segment_z₁, scalarOneForm (Ψ₁' r) z)
    (hseg2 :
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Ψ₁_fourier r) z) =
        s * ∫ᶜ z in mobiusInv_segment_z₂, scalarOneForm (Ψ₁' r) z) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Ψ₁_fourier r) z =
      s *
        ((∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
              scalarOneForm (Ψ₁' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Ψ₁' r) z) := by
  let ω : ℂ → ℂ →L[ℂ] ℂ := scalarOneForm (Ψ₁' r)
  let γa :
      Path (mobiusInv (-1 : ℂ)) (mobiusInv ((-1 : ℂ) + Complex.I)) :=
    mobiusInv_segment_z₁
  let γb :
      Path (mobiusInv ((-1 : ℂ) + Complex.I)) (mobiusInv Complex.I) :=
    mobiusInv_segment_z₂
  let zmid : ℂ := mobiusInv ((-1 : ℂ) + Complex.I)
  let ztop : ℂ := (1 : ℂ) + Complex.I
  let δa : Path (1 : ℂ) ((1 : ℂ) + Complex.I) := Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I)
  let δb : Path ((1 : ℂ) + Complex.I) Complex.I := Path.segment ((1 : ℂ) + Complex.I) Complex.I
  let η : Path zmid ztop := Path.segment zmid ztop
  have h1 : (∫ᶜ z in γa, ω z) + ∫ᶜ z in η, ω z = ∫ᶜ z in δa, ω z := by
    have h :=
      perm_J12_contour_h1_mobiusInv_wedgeSet (Ψ₁' := Ψ₁') closed_ω_wedgeSet (r := r)
    simpa [ω, γa, δa, η, zmid, ztop] using h
  have h2 : ∫ᶜ z in γb, ω z = (∫ᶜ z in δb, ω z) + ∫ᶜ z in η, ω z := by
    have h :=
      perm_J12_contour_h2_mobiusInv_wedgeSet (Ψ₁' := Ψ₁') closed_ω_wedgeSet (r := r)
    simpa [ω, γb, δb, η, zmid, ztop] using h
  have hsum :
      (∫ᶜ z in γa, ω z) + ∫ᶜ z in γb, ω z =
        (∫ᶜ z in δa, ω z) + ∫ᶜ z in δb, ω z := by
    calc
      (∫ᶜ z in γa, ω z) + ∫ᶜ z in γb, ω z =
          ((∫ᶜ z in δa, ω z) - ∫ᶜ z in η, ω z) + ((∫ᶜ z in δb, ω z) + ∫ᶜ z in η, ω z) := by
            simp [(eq_sub_iff_add_eq).2 h1, h2]
      _ = (∫ᶜ z in δa, ω z) + ∫ᶜ z in δb, ω z := by
            abel
  calc
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I), scalarOneForm (Ψ₁_fourier r) z) +
          ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Ψ₁_fourier r) z =
        s * ∫ᶜ z in γa, ω z + s * ∫ᶜ z in γb, ω z := by
          simp [hseg1, hseg2, ω, γa, γb]
    _ = s * ((∫ᶜ z in γa, ω z) + ∫ᶜ z in γb, ω z) := by
          simp [mul_add]
    _ = s * ((∫ᶜ z in δa, ω z) + ∫ᶜ z in δb, ω z) := by
          exact congrArg (fun t : ℂ => s * t) hsum
      _ = s *
        ((∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
              scalarOneForm (Ψ₁' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Ψ₁' r) z) := by
          simp [ω, δa, δb]

/--
Assembled contour identity for the `perm_J12` argument, specialized to `mobiusInv` and `wedgeSet`.

This combines:
- the segment contour-change lemmas under `mobiusInv`, and
- the wedge-set contour deformations (`perm_J12_contour_h1`/`perm_J12_contour_h2`).
-/
public lemma perm_J12_contour_mobiusInv_wedgeSet
    {Ψ₁_fourier Ψ₁' : ℝ → ℂ → ℂ}
    (Ψ₁_fourier_eq_neg_deriv_mul :
      ∀ r : ℝ, ∀ z : ℂ, 0 < z.im →
        Ψ₁_fourier r z = -(deriv mobiusInv z) * Ψ₁' r (mobiusInv z))
    (closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet)
    (r : ℝ) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Ψ₁_fourier r) z =
      -((∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
            scalarOneForm (Ψ₁' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Ψ₁' r) z) := by
  have hseg1 :
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
            scalarOneForm (Ψ₁_fourier r) z) =
        (-1 : ℂ) * ∫ᶜ z in mobiusInv_segment_z₁,
          scalarOneForm (Ψ₁' r) z := by
    simpa [neg_one_mul] using
      (SpherePacking.MobiusInv.curveIntegral_segment_neg_inv (Ψ₁_fourier := Ψ₁_fourier) (Ψ₁' := Ψ₁')
        (-1 : ℂ) ((-1 : ℂ) + Complex.I)
        (Ψ₁_fourier_eq_neg_deriv_mul := Ψ₁_fourier_eq_neg_deriv_mul) (r := r))
  have hseg2 :
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Ψ₁_fourier r) z) =
        (-1 : ℂ) * ∫ᶜ z in mobiusInv_segment_z₂, scalarOneForm (Ψ₁' r) z := by
    simpa [neg_one_mul] using
      (SpherePacking.MobiusInv.curveIntegral_segment_neg_inv (Ψ₁_fourier := Ψ₁_fourier) (Ψ₁' := Ψ₁')
        ((-1 : ℂ) + Complex.I) Complex.I
        (Ψ₁_fourier_eq_neg_deriv_mul := Ψ₁_fourier_eq_neg_deriv_mul) (r := r))
  have hmain :=
    perm_12_contour_mobiusInv_wedgeSet_aux
      (Ψ₁_fourier := Ψ₁_fourier)
      (Ψ₁' := Ψ₁')
      (s := (-1 : ℂ))
      (hseg1 := hseg1)
      (hseg2 := hseg2)
      (closed_ω_wedgeSet := closed_ω_wedgeSet)
      (r := r)
  simpa using hmain

/--
Assembled contour identity for the `perm_I12` argument, specialized to `mobiusInv` and `wedgeSet`.
-/
public lemma perm_I12_contour_mobiusInv_wedgeSet
    {Ψ₁_fourier Ψ₁' : ℝ → ℂ → ℂ}
    (Ψ₁_fourier_eq_deriv_mul :
      ∀ r : ℝ, ∀ z : ℂ, 0 < z.im →
        Ψ₁_fourier r z = (deriv mobiusInv z) * Ψ₁' r (mobiusInv z))
    (closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet)
    (r : ℝ) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Ψ₁_fourier r) z =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
            scalarOneForm (Ψ₁' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Ψ₁' r) z := by
  have hseg1 :
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
            scalarOneForm (Ψ₁_fourier r) z) =
        (1 : ℂ) * ∫ᶜ z in mobiusInv_segment_z₁, scalarOneForm (Ψ₁' r) z := by
    simpa using
      (SpherePacking.MobiusInv.curveIntegral_segment_pos_inv (Ψ₁_fourier := Ψ₁_fourier) (Ψ₁' := Ψ₁')
        (-1 : ℂ) ((-1 : ℂ) + Complex.I)
        (Ψ₁_fourier_eq_deriv_mul := Ψ₁_fourier_eq_deriv_mul) (r := r))
  have hseg2 :
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Ψ₁_fourier r) z) =
        (1 : ℂ) * ∫ᶜ z in mobiusInv_segment_z₂, scalarOneForm (Ψ₁' r) z := by
    simpa using
      (SpherePacking.MobiusInv.curveIntegral_segment_pos_inv (Ψ₁_fourier := Ψ₁_fourier) (Ψ₁' := Ψ₁')
        ((-1 : ℂ) + Complex.I) Complex.I
        (Ψ₁_fourier_eq_deriv_mul := Ψ₁_fourier_eq_deriv_mul) (r := r))
  have hmain :=
    perm_12_contour_mobiusInv_wedgeSet_aux
      (Ψ₁_fourier := Ψ₁_fourier)
      (Ψ₁' := Ψ₁')
      (s := (1 : ℂ))
      (hseg1 := hseg1)
      (hseg2 := hseg2)
      (closed_ω_wedgeSet := closed_ω_wedgeSet)
      (r := r)
  simpa using hmain

end

end SpherePacking
