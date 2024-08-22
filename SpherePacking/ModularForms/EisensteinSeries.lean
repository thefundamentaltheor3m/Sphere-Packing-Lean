import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ArithmeticFunction
import SpherePacking.ModularForms.QExpansion

open scoped Nat Real
open UpperHalfPlane hiding I
open Complex ModularForm ArithmeticFunction Filter Topology

local notation "G[" k ";" hk "]" => eisensteinSeries_MF (k := k) (N := 1) hk 0
local notation "G[" k "]" => eisensteinSeries_MF (N := 1) (show 3 ≤ k by decide) 0

variable {k : ℕ} (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ)

theorem eisensteinSeries_qexp :
    G[k;hk] z
      = 2 * ((-1) ^ (k / 2 + 1) * 2 ^ (2 * (k / 2) - 1) * π ^ k * bernoulli k / k !)
        + ∑' n : ℕ+, (2 * ((-2 * π * I) ^ k / (k - 1)!) * sigma (k - 1) n)
          * Complex.exp (2 * π * I * z * n) := by
  sorry

#check QExp.tendsto_nat_pos
lemma eisensteinSeries_tendsto_atImInfty : Tendsto G[4] atImInfty (𝓝 (π ^ 4 / 45)) := by
  change Tendsto (fun z ↦ G[4] z) _ _
  -- simp_rw [eisensteinSeries_qexp (k := 3) (by decide)]
  conv => enter [1, z]; rw [eisensteinSeries_qexp]
  convert Tendsto.const_add (c := (0 : ℂ)) _ ?_ using 1
  · norm_num [bernoulli, mul_one_div, Nat.factorial]
    ring_nf
  · have := QExp.tendsto_nat_pos _

example : G[4] 0 ≠ 0 := by
  sorry
