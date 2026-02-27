import SpherePacking.Tactic.TendstoPoly
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

variable {f g k : ℝ → ℝ}

-- Constant function
example : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := by tendsto_poly

-- Single atom, identity
example (h : Tendsto f atTop (nhds 3)) :
    Tendsto (fun z => f z) atTop (nhds 3) := by tendsto_poly

-- Single atom, scalar multiply
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => 2 * f z) atTop (nhds 0) := by tendsto_poly

-- Two atoms, sum
example (h₁ : Tendsto f atTop (nhds 1)) (h₂ : Tendsto g atTop (nhds 2)) :
    Tendsto (fun z => f z + g z) atTop (nhds 3) := by tendsto_poly

-- Two atoms, polynomial
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1)) :
    Tendsto (fun z => f z ^ 2 + f z * g z + g z ^ 2) atTop (nhds 1) := by tendsto_poly

-- Three atoms, subtraction
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1))
    (h₃ : Tendsto k atTop (nhds 1)) :
    Tendsto (fun z => f z + g z - k z) atTop (nhds 0) := by tendsto_poly

-- Unused hypotheses in context don't interfere
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1))
    (h_unrelated : Tendsto f atBot (nhds 5)) :
    Tendsto (fun z => f z * g z) atTop (nhds 0) := by tendsto_poly
