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

/-- The parametrisation `z₁` is continuous on `Icc (0 : ℝ) 1`. -/
public lemma continuous_z₁ : Continuous z₁ := by
  simpa [z₁] using continuous_const.add (continuous_const.mul continuous_coe_Icc_toComplex)

/-- The extension `z₁' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₁' : Continuous z₁' := by
  change Continuous (IccExtend (zero_le_one : (0 : ℝ) ≤ 1) z₁)
  exact continuous_z₁.Icc_extend'

/-- The parametrisation `z₂` is continuous on `Icc (0 : ℝ) 1`. -/
public lemma continuous_z₂ : Continuous z₂ := by
  simpa [z₂] using (continuous_const.add continuous_coe_Icc_toComplex).add continuous_const

/-- The extension `z₂' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₂' : Continuous z₂' := by
  change Continuous (IccExtend (zero_le_one : (0 : ℝ) ≤ 1) z₂)
  exact continuous_z₂.Icc_extend'

/-- The parametrisation `z₃` is continuous on `Icc (0 : ℝ) 1`. -/
public lemma continuous_z₃ : Continuous z₃ := by
  simpa [z₃] using continuous_const.add (continuous_const.mul continuous_coe_Icc_toComplex)

/-- The extension `z₃' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₃' : Continuous z₃' := by
  change Continuous (IccExtend (zero_le_one : (0 : ℝ) ≤ 1) z₃)
  exact continuous_z₃.Icc_extend'

/-- The parametrisation `z₄` is continuous on `Icc (0 : ℝ) 1`. -/
public lemma continuous_z₄ : Continuous z₄ := by
  simpa [z₄, sub_eq_add_neg, add_assoc] using
    (continuous_const.sub continuous_coe_Icc_toComplex).add continuous_const

/-- The extension `z₄' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₄' : Continuous z₄' := by
  change Continuous (IccExtend (zero_le_one : (0 : ℝ) ≤ 1) z₄)
  exact continuous_z₄.Icc_extend'

/-- The parametrisation `z₅` is continuous on `Icc (0 : ℝ) 1`. -/
public lemma continuous_z₅ : Continuous z₅ := by
  simpa [z₅] using continuous_const.mul continuous_coe_Icc_toComplex

/-- The extension `z₅' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₅' : Continuous z₅' := by
  change Continuous (IccExtend (zero_le_one : (0 : ℝ) ≤ 1) z₅)
  exact continuous_z₅.Icc_extend'

end

end MagicFunction.Parametrisations
