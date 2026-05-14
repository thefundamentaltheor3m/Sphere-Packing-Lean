module

public import SpherePacking.Contour.PermJ12Contour
public import SpherePacking.Basic.Domains.WedgeSet
public import SpherePacking.Contour.MobiusInv.Segments
import SpherePacking.Contour.Segments
import SpherePacking.Contour.MobiusInv.ContourChange
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Order.LatticeIntervals
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Contour identities for `mobiusInv` on `wedgeSet`. -/

open MeasureTheory
open MagicFunction

namespace SpherePacking

noncomputable section

open SpherePacking.Contour

private lemma mobiusInv_re_im (x y : ℝ) :
    (-( ((x : ℂ) + Complex.I * (y : ℂ)) )⁻¹ : ℂ).re = (-x) / (x ^ 2 + y ^ 2) ∧
      (-( ((x : ℂ) + Complex.I * (y : ℂ)) )⁻¹ : ℂ).im = y / (x ^ 2 + y ^ 2) := by
  constructor <;>
    simp [Complex.inv_re, Complex.inv_im, Complex.normSq, pow_two, neg_div]

/-- Along `-1 → -1 + I`, the Mobius inversion map lands in `wedgeSet`. -/
public lemma mobiusInv_lineMap_z₁_mem_wedgeSet
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    mobiusInv (AffineMap.lineMap (-1 : ℂ) ((-1 : ℂ) + Complex.I) t) ∈ wedgeSet := by
  rw [Contour.lineMap_z₁line]
  obtain ⟨hre, him⟩ := mobiusInv_re_im (-1) t
  rw [show mobiusInv (Contour.z₁line t) = -(↑(-1 : ℝ) + Complex.I * ↑t)⁻¹ from by
    simp [mobiusInv, Contour.z₁line]] at *
  refine wedgeSet_iff.mpr ⟨by rw [him]; positivity, ?_⟩
  rw [hre, him]; simp only [fieldLt]
  constructor <;> nlinarith only [ht0, ht1]

/-- Along `-1 + I → I`, the Mobius inversion map lands in `wedgeSet`. -/
public lemma mobiusInv_lineMap_z₂_mem_wedgeSet
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    mobiusInv (AffineMap.lineMap ((-1 : ℂ) + Complex.I) Complex.I t) ∈ wedgeSet := by
  rw [Contour.lineMap_z₂line]
  obtain ⟨hre, him⟩ := mobiusInv_re_im (t - 1) 1
  rw [show mobiusInv (Contour.z₂line t) = -(↑(t - 1) + Complex.I * ↑(1 : ℝ))⁻¹ from by
    simp [sub_eq_add_neg, add_comm, mobiusInv, Contour.z₂line], one_pow] at *
  refine wedgeSet_iff.mpr ⟨by rw [him]; positivity, ?_⟩
  rw [hre, him]; simp only [fieldLt]
  constructor <;> nlinarith only [ht0, ht1]

/-- `C^2` smoothness of the homotopy map
`(x,y) ↦ lineMap (mobiusInv (lineMap p0 p1 y)) (lineMap q0 q1 y) x`
on the unit square, assuming `lineMap p0 p1 y ≠ 0` throughout. -/
private lemma contDiffOn_lineMap_mobiusInv_lineMap (p0 p1 q0 q1 : ℂ)
    (hne : ∀ xy ∈ Set.Icc (0 : ℝ × ℝ) 1, (AffineMap.lineMap p0 p1 xy.2) ≠ 0) :
    ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ =>
        (AffineMap.lineMap (k := ℝ)
            (mobiusInv (AffineMap.lineMap p0 p1 xy.2))
            (AffineMap.lineMap q0 q1 xy.2)) xy.1)
      (Set.Icc (0 : ℝ × ℝ) 1) := by
  have hline (a b : ℂ) :
      ContDiffOn ℝ 2 (fun xy => AffineMap.lineMap a b xy.2) (Set.Icc (0 : ℝ × ℝ) 1) := by
    simpa [AffineMap.lineMap_apply_module] using (by
      fun_prop :
        ContDiffOn ℝ 2 (fun xy => (1 - xy.2) • a + xy.2 • b) (Set.Icc (0 : ℝ × ℝ) 1))
  have hA : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ => mobiusInv (AffineMap.lineMap p0 p1 xy.2))
      (Set.Icc (0 : ℝ × ℝ) 1) := by simpa [mobiusInv] using ((hline p0 p1).inv hne).neg
  simpa [AffineMap.lineMap_apply_module] using
    ((by fun_prop : ContDiffOn ℝ 2 (fun xy => (1 : ℝ) - xy.1) (Set.Icc (0 : ℝ × ℝ) 1)).smul hA).add
      ((by fun_prop : ContDiffOn ℝ 2 (fun xy => xy.1) (Set.Icc (0 : ℝ × ℝ) 1)).smul (hline q0 q1))

lemma perm_J12_contour_h1_mobiusInv_wedgeSet {Ψ₁' : ℝ → ℂ → ℂ}
    (closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet) (r : ℝ) :
    (∫ᶜ z in mobiusInv_segment_z₁, scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment (mobiusInv ((-1 : ℂ) + Complex.I)) ((1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁' r) z =
      ∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I), scalarOneForm (Ψ₁' r) z :=
  perm_J12_contour_h1 (mobiusInv := mobiusInv) (Ψ₁' := Ψ₁') (wedgeSet := wedgeSet)
    ⟨closed_ω_wedgeSet,
      { continuousOn_mobiusInv_segment_z₁ := continuousOn_mobiusInv_segment_z₁
        mobiusInv_neg_one := by simp [mobiusInv]
        homotopy_mem_wedgeSet := fun hx hy => convex_wedgeSet.lineMap_mem
          (mobiusInv_lineMap_z₁_mem_wedgeSet hy.1 hy.2)
          (lineMap_z₃line_mem_wedgeSet hy.1) ⟨hx.1.le, hx.2.le⟩
        contDiffOn_homotopy := by
          refine contDiffOn_lineMap_mobiusInv_lineMap (-1) (-1 + Complex.I) 1 (1 + Complex.I) ?_
          rintro ⟨_x, y⟩ ⟨h0, h1⟩
          exact segment_z₁_ne_zero ⟨y, ⟨h0.2, h1.2⟩⟩ }⟩ r

lemma perm_J12_contour_h2_mobiusInv_wedgeSet {Ψ₁' : ℝ → ℂ → ℂ}
    (closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet) (r : ℝ) :
    ∫ᶜ z in mobiusInv_segment_z₂, scalarOneForm (Ψ₁' r) z =
      (∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I, scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment (mobiusInv ((-1 : ℂ) + Complex.I)) ((1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁' r) z :=
  perm_J12_contour_h2 (mobiusInv := mobiusInv) (Ψ₁' := Ψ₁') (wedgeSet := wedgeSet)
    ⟨closed_ω_wedgeSet,
      { continuousOn_mobiusInv_segment_z₂ := continuousOn_mobiusInv_segment_z₂
        mobiusInv_I := by simp [mobiusInv]
        homotopy_mem_wedgeSet := fun hx hy => convex_wedgeSet.lineMap_mem
          (mobiusInv_lineMap_z₂_mem_wedgeSet hy.1 hy.2)
          (lineMap_z₄line_mem_wedgeSet hy.1 hy.2) ⟨hx.1.le, hx.2.le⟩
        contDiffOn_homotopy := by
          refine contDiffOn_lineMap_mobiusInv_lineMap
            (-1 + Complex.I) Complex.I (1 + Complex.I) Complex.I ?_
          rintro ⟨_x, y⟩ ⟨h0, h1⟩
          exact segment_z₂_ne_zero ⟨y, ⟨h0.2, h1.2⟩⟩ }⟩ r

private lemma perm_12_contour_mobiusInv_wedgeSet_aux
    {Ψ₁_fourier Ψ₁' : ℝ → ℂ → ℂ} (s : ℂ)
    (closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet) (r : ℝ)
    (hseg1 : (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁_fourier r) z) =
        s * ∫ᶜ z in mobiusInv_segment_z₁, scalarOneForm (Ψ₁' r) z)
    (hseg2 : (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Ψ₁_fourier r) z) =
        s * ∫ᶜ z in mobiusInv_segment_z₂, scalarOneForm (Ψ₁' r) z) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Ψ₁_fourier r) z =
      s * ((∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I), scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I, scalarOneForm (Ψ₁' r) z) := by
  have := perm_J12_contour_h1_mobiusInv_wedgeSet closed_ω_wedgeSet r
  have := perm_J12_contour_h2_mobiusInv_wedgeSet closed_ω_wedgeSet r
  grind only

/-- Assembled `perm_J12` contour identity for `mobiusInv` and `wedgeSet`. -/
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
  simpa using
    perm_12_contour_mobiusInv_wedgeSet_aux (s := (-1 : ℂ)) closed_ω_wedgeSet r
      (hseg1 := by
        simpa [neg_one_mul] using SpherePacking.MobiusInv.curveIntegral_segment_neg_inv
          (Ψ₁' := Ψ₁') (-1 : ℂ) ((-1 : ℂ) + Complex.I) Ψ₁_fourier_eq_neg_deriv_mul r)
      (hseg2 := by
        simpa [neg_one_mul] using SpherePacking.MobiusInv.curveIntegral_segment_neg_inv
          (Ψ₁' := Ψ₁') ((-1 : ℂ) + Complex.I) Complex.I Ψ₁_fourier_eq_neg_deriv_mul r)

/-- Assembled `perm_I12` contour identity for `mobiusInv` and `wedgeSet`. -/
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
  simpa using
    perm_12_contour_mobiusInv_wedgeSet_aux (s := (1 : ℂ)) closed_ω_wedgeSet r
      (hseg1 := by
        simpa using SpherePacking.MobiusInv.curveIntegral_segment_pos_inv (Ψ₁' := Ψ₁')
          (-1 : ℂ) ((-1 : ℂ) + Complex.I) Ψ₁_fourier_eq_deriv_mul r)
      (hseg2 := by
        simpa using SpherePacking.MobiusInv.curveIntegral_segment_pos_inv (Ψ₁' := Ψ₁')
          ((-1 : ℂ) + Complex.I) Complex.I Ψ₁_fourier_eq_deriv_mul r)

end

end SpherePacking
