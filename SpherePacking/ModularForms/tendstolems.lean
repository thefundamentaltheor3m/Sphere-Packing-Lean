import Mathlib.Analysis.CStarAlgebra.Classes

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
