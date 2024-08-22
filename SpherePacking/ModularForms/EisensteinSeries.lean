import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import SpherePacking.ModularForms.QExpansion

open scoped Nat Real
open UpperHalfPlane hiding I
open Complex ModularForm ArithmeticFunction Filter Topology

local notation "G[" k ";" hk "]" => eisensteinSeries_MF (k := k) (N := 1) hk 0
local notation "G[" k "]" => eisensteinSeries_MF (N := 1) (show 3 ≤ k by decide) 0

variable {k : ℕ} (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ)

theorem eisensteinSeries_qexp :
    G[k;hk] z
      = 2 * riemannZeta k
        + 2 * ((-2 * π * I) ^ k / (k - 1)!) * ∑' n : ℕ+, Complex.exp (π * (2 * n) * z * I) := by
  sorry

example {n : ℤ} : Int.sqrt (n ^ 2) = |n| := by
  rw [sq, Int.sqrt_eq, Int.natCast_natAbs]

instance fin (n : ℤ) : Fintype { k // k ^ 2 = n } :=
  ⟨Finset.subtype _ {Int.sqrt n, - Int.sqrt n}, fun ⟨k, hk⟩ => by
    simp only [Finset.mem_subtype, Finset.mem_insert, Finset.mem_singleton]
    subst hk
    rw [sq, Int.sqrt_eq, Int.natCast_natAbs]
    exact eq_or_eq_neg_of_abs_eq rfl ⟩

example {n : ℤ} : Fintype.card { k // k ^ 2 = n } ≤ 2 := by
  rw [← Finset.card_univ, Finset.univ, Fintype.elems, fin, Finset.card_subtype]
  exact (Finset.card_filter_le _ _).trans Finset.card_le_two

lemma eisensteinSeries_tendsto_atImInfty : Tendsto G[k;hk] atImInfty (𝓝 (2 * riemannZeta k)) := by
  change Tendsto (fun z ↦ G[k;hk] z) _ _
  conv => enter [1, z]; rw [eisensteinSeries_qexp]
  convert Tendsto.const_add (c := (0 : ℂ)) _ ?_ using 1
  · rw [add_zero]
  · conv => enter [3, 1]; rw [← mul_zero (2 * ((-2 * ↑π * I) ^ k / ↑(k - 1)!))]
    apply Tendsto.const_mul
    have (n : ℕ+) : 2 * ((n : ℕ) : ℂ) = (2 * n : ℤ) := by norm_cast
    simp_rw [this]
    convert QExp.tendsto_nat_pos' (fun _ ↦ 1) (fun n : ℕ+ ↦ 2 * ((n : ℕ) : ℤ)) ?_ ?_ using 2 with z
    · simp_rw [one_mul]
    · simp
    · simp
      -- too lazy
      sorry

example : G[k;hk] ≠ 0 := by
  intro h
  have h₁ : Tendsto G[k;hk] atImInfty (𝓝 0) := by simpa [h] using tendsto_const_nhds
  have h₂ := @eisensteinSeries_tendsto_atImInfty k hk
  norm_num [← mul_div_assoc] at h₂
  have := tendsto_nhds_unique h₁ h₂
  rw [eq_comm] at this
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at this
  exact riemannZeta_ne_zero_of_one_lt_re (s := k) (by simp; linarith) this
