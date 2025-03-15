import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.EMetricSpace.Paracompact

open TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical


lemma int_tendsto_nat {f : ℤ → ℂ} {x : ℂ} (hf : Tendsto f atTop (𝓝 x)) :
  Tendsto (fun n : ℕ => f n) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop] at *
  intro ε hε
  obtain ⟨N, hN⟩ := hf ε hε
  use N.natAbs
  intro n hn
  apply hN n ?_
  omega

lemma pnat_tendsto_nat (f : ℕ → ℂ) (x : ℂ) (hf : Tendsto (fun n : ℕ+ => f n) atTop (𝓝 x)) :
  Tendsto f atTop (𝓝 x) := by
  exact tendsto_comp_val_Ioi_atTop.mp hf

lemma nat_tendsto_pnat (f : ℕ → ℂ) (x : ℂ) (hf : Tendsto f atTop (𝓝 x)) :
  Tendsto (fun n : ℕ+ => f n) atTop (𝓝 x) := by
  exact tendsto_comp_val_Ioi_atTop.mpr hf

lemma rest (f g : ℕ → ℂ) (x : ℂ) (hf : Tendsto f atTop (𝓝 x)) (hfg : Tendsto (g - f) atTop (𝓝 0)) :
  Tendsto g atTop (𝓝 x) := by
  have := Tendsto.add hf hfg
  simp at this
  exact this


lemma aux47 (r : ℂ) (hr : ‖r‖ < 1) : Tendsto (fun n : ℕ => 1 - r^n) atTop (𝓝 1) := by
  rw [show (1 : ℂ) = 1 - 0 by ring]
  apply Filter.Tendsto.sub
  simp
  apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr
