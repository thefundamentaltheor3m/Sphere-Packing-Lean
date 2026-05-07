module

public import SpherePacking.MagicFunction.IntegralParametrisations

/-!
# Continuity of integral parametrisations

This file records continuity lemmas for the parametrisations `z₁`--`z₅` and their extensions
`z₁'`--`z₅'`.
-/

namespace MagicFunction.Parametrisations

noncomputable section

open scoped Topology
open Complex Real Set

private lemma continuous_coe_Icc_toComplex :
    Continuous (fun t : Icc (0 : ℝ) 1 => (t : ℂ)) :=
  Complex.continuous_ofReal.comp continuous_subtype_val

/-- The extension `z₁' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₁' : Continuous z₁' :=
  have h : Continuous z₁ := by
    simpa [z₁] using continuous_const.add (continuous_const.mul continuous_coe_Icc_toComplex)
  (h.Icc_extend' : Continuous (IccExtend (zero_le_one : (0 : ℝ) ≤ 1) z₁))

/-- The extension `z₂' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₂' : Continuous z₂' :=
  have h : Continuous z₂ := by
    simpa [z₂] using (continuous_const.add continuous_coe_Icc_toComplex).add continuous_const
  (h.Icc_extend' : Continuous (IccExtend (zero_le_one : (0 : ℝ) ≤ 1) z₂))

/-- The extension `z₃' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₃' : Continuous z₃' :=
  have h : Continuous z₃ := by
    simpa [z₃] using continuous_const.add (continuous_const.mul continuous_coe_Icc_toComplex)
  (h.Icc_extend' : Continuous (IccExtend (zero_le_one : (0 : ℝ) ≤ 1) z₃))

/-- The extension `z₄' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₄' : Continuous z₄' :=
  have h : Continuous z₄ := by
    simpa [z₄, sub_eq_add_neg, add_assoc] using
      (continuous_const.sub continuous_coe_Icc_toComplex).add continuous_const
  (h.Icc_extend' : Continuous (IccExtend (zero_le_one : (0 : ℝ) ≤ 1) z₄))

/-- The extension `z₅' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₅' : Continuous z₅' :=
  have h : Continuous z₅ := by simpa [z₅] using continuous_const.mul continuous_coe_Icc_toComplex
  (h.Icc_extend' : Continuous (IccExtend (zero_le_one : (0 : ℝ) ≤ 1) z₅))

end

end MagicFunction.Parametrisations
