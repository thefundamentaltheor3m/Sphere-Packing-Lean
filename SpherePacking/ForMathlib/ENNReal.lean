import Mathlib.Topology.Instances.ENNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/- Maybe put this in Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean -/

open ENNReal Filter Topology

protected theorem ENNReal.Tendsto.rpow {α : Type*} {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} {n : ℝ}
    (hm : Tendsto m f (𝓝 a)) : Tendsto (fun x => m x ^ n) f (𝓝 (a ^ n)) :=
  (ENNReal.continuous_rpow_const.tendsto a).comp hm
