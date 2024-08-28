import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import SpherePacking.ModularForms.QExpansion

open scoped Nat Real
open UpperHalfPlane hiding I
open QExp Complex ModularForm ArithmeticFunction Filter Topology

local notation "G[" k ";" hk "]" => eisensteinSeries_MF (k := k) (N := 1) hk 0
local notation "G[" k "]" => eisensteinSeries_MF (N := 1) (show 3 ≤ k by decide) 0

variable {k : ℕ} (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ)

-- Proven in Chris' repo
theorem eisensteinSeries_qexp :
    G[k;hk] z = 2 * riemannZeta k + 2 * ((-2 * π * I) ^ k / (k - 1)!) * ∑' n : ℕ+, 𝕢 n z := by
  sorry

lemma eisensteinSeries_tendsto_atImInfty : Tendsto G[k;hk] atImInfty (𝓝 (2 * riemannZeta k)) := by
  change Tendsto (fun z ↦ G[k;hk] z) _ _
  conv => enter [1, z]; rw [eisensteinSeries_qexp]
  convert Tendsto.const_add (c := (0 : ℂ)) _ ?_ using 1
  · rw [add_zero]
  · conv => enter [3, 1]; rw [← mul_zero (2 * ((-2 * ↑π * I) ^ k / ↑(k - 1)!))]
    apply Tendsto.const_mul
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simp_rw [tsum_pnat, PNat.mk_coe]
    simp_rw [𝕢_eq_one_pow_nat]
    convert_to Tendsto (fun z : ℍ ↦ ‖∑' (n : ℕ), 𝕢 1 z ^ n - 1‖) atImInfty (𝓝 0)
    · -- Not sure why I can't simp_rw [this] above
      have (z : ℍ) := geom_series_succ _ (norm_𝕢_lt_one _ _ zero_lt_one z.prop)
      exact funext fun z ↦ congrArg (fun z ↦ ‖z‖) (this z)
    · apply squeeze_zero (g := fun z : ℍ ↦ ‖(1 - 𝕢 1 z)⁻¹ - 1‖) (by simp)
      · intro z
        rw [tsum_geometric_of_norm_lt_one]
        exact norm_𝕢_lt_one _ _ zero_lt_one z.prop
      · convert ((((𝕢_tendsto_atImInfty 1).const_sub 1).inv₀ ?_).sub_const 1).norm <;> norm_num

example : G[k;hk] ≠ 0 := by
  intro h
  have h₁ : Tendsto G[k;hk] atImInfty (𝓝 0) := by simpa [h] using tendsto_const_nhds
  have h₂ := @eisensteinSeries_tendsto_atImInfty k hk
  norm_num [← mul_div_assoc] at h₂
  have := tendsto_nhds_unique h₁ h₂
  rw [eq_comm] at this
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at this
  exact riemannZeta_ne_zero_of_one_lt_re (s := k) (by simp; linarith) this
