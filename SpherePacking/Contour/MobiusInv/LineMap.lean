module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Order.LatticeIntervals

import Mathlib.Tactic.FunProp

public import SpherePacking.Contour.MobiusInv.Basic

/-!
# Smoothness of Mobius homotopies

This file proves a smoothness lemma for the affine homotopy map used in Poincare-lemma arguments.
We linearly interpolate between `mobiusInv (lineMap p0 p1 t)` and `lineMap q0 q1 t`,
assuming the inner segment avoids `0`.

This lemma is shared by the contour deformation developments.
-/

namespace SpherePacking

noncomputable section

/--
`C^2` smoothness of the homotopy map
`(x,y) ↦ lineMap (mobiusInv (lineMap p0 p1 y)) (lineMap q0 q1 y) x`
on the unit square, assuming `lineMap p0 p1 y ≠ 0` throughout.
-/
public lemma contDiffOn_lineMap_mobiusInv_lineMap (p0 p1 q0 q1 : ℂ)
    (hne : ∀ xy ∈ Set.Icc (0 : ℝ × ℝ) 1, (AffineMap.lineMap p0 p1 xy.2) ≠ 0) :
    ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ =>
        (AffineMap.lineMap (k := ℝ)
            (mobiusInv (AffineMap.lineMap p0 p1 xy.2))
            (AffineMap.lineMap q0 q1 xy.2)) xy.1)
      (Set.Icc (0 : ℝ × ℝ) 1) := by
  have hline (a b : ℂ) :
      ContDiffOn ℝ 2 (fun xy : ℝ × ℝ => AffineMap.lineMap a b xy.2) (Set.Icc (0 : ℝ × ℝ) 1) := by
    simpa [AffineMap.lineMap_apply_module] using (by
      fun_prop :
        ContDiffOn ℝ 2 (fun xy : ℝ × ℝ => ((1 : ℝ) - xy.2) • a + xy.2 • b) (Set.Icc (0 : ℝ × ℝ) 1))
  have hA :
      ContDiffOn ℝ 2
        (fun xy : ℝ × ℝ => mobiusInv (AffineMap.lineMap p0 p1 xy.2))
        (Set.Icc (0 : ℝ × ℝ) 1) :=
    by simpa [mobiusInv] using ((hline p0 p1).inv hne).neg
  simpa [AffineMap.lineMap_apply_module] using
    ((by fun_prop : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ => (1 : ℝ) - xy.1) (Set.Icc (0 : ℝ × ℝ) 1)).smul
        hA).add
      ((by fun_prop : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ => xy.1) (Set.Icc (0 : ℝ × ℝ) 1)).smul
        (hline q0 q1))

end

end SpherePacking
