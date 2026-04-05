module
public import SpherePacking.ModularForms.Derivative
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Topology.Order.Compact
import SpherePacking.ForMathlib.ExpPiIMulMulI

@[expose] public section

/-!
# The Eisenstein combination `A_E`

This file studies the weight-6 combination `A_E = E₂ * E₄ - E₆` and records its Fourier
(`q`-expansion) formulas used later in the magic function argument.

## Main definitions
* `A_E`, `A_E_coeff`, `A_E_term`

## Main statements
* `E₂_mul_E₄_sub_E₆`
* `A_E_eq_tsum`
-/
section Ramanujan_Formula

open scoped Topology Real BigOperators Nat
open scoped ArithmeticFunction.sigma
open scoped MatrixGroups CongruenceSubgroup ModularForm

open ModularForm EisensteinSeries UpperHalfPlane Complex ModularFormClass

local notation "𝕢" => Function.Periodic.qParam

/-- The common combination `E₂ * E₄ - E₆`. -/
@[expose] public noncomputable def A_E : ℍ → ℂ := fun z => (E₂ z) * (E₄ z) - (E₆ z)

/-- Fourier coefficients for the shifted `ℕ`-Fourier expansion of `A_E`. -/
@[expose] public noncomputable def A_E_coeff (n : ℕ) : ℂ :=
  (720 : ℂ) * ((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ)

/-- Term `n` in the shifted `ℕ`-Fourier expansion of `A_E`. -/
@[expose] public noncomputable def A_E_term (z : ℍ) (n : ℕ) : ℂ :=
  A_E_coeff n * cexp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))

/-- The norm of `A_E_coeff n` expressed as a real number. -/
public lemma norm_A_E_coeff (n : ℕ) :
    ‖A_E_coeff n‖ = (720 : ℝ) * ((n + 1 : ℕ) : ℝ) * (σ 3 (n + 1) : ℝ) := by
  -- `simp` rewrites `((n+1 : ℕ) : ℂ)` as `(n : ℂ) + 1`, so package the corresponding norm lemma.
  have hn : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    simpa [Nat.cast_add, Nat.cast_one] using (Complex.norm_natCast (n + 1))
  simp [A_E_coeff, hn, Nat.cast_add, Nat.cast_one, mul_assoc, mul_comm]

private def E4Coeff : ℕ → ℂ := fun n => if n = 0 then 1 else (240 : ℂ) * (σ 3 n)

private noncomputable def E4qSeries : ℍ → ℂ :=
  fun w => ∑' n : ℕ, E4Coeff n * cexp (2 * Real.pi * Complex.I * n * w)

private lemma one_mem_strictPeriods :
    (1 : ℝ) ∈ ((Γ(1) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by simp

private lemma E4qSeries_hasSum
    (w : ℍ) :
    HasSum (fun n : ℕ => E4Coeff n * cexp (2 * Real.pi * Complex.I * n * w)) (E₄ w) := by
  have hsum :=
    ModularFormClass.hasSum_qExpansion (f := E₄) (h := (1 : ℝ)) (by positivity)
      one_mem_strictPeriods w
  refine HasSum.congr_fun hsum (fun n => ?_)
  have hcoeff : (ModularFormClass.qExpansion (1 : ℝ) E₄).coeff n = E4Coeff n := by
    simpa [E4Coeff] using congr_fun E4_q_exp n
  have hqpow : (𝕢 (1 : ℝ) w) ^ n = cexp (2 * Real.pi * Complex.I * n * w) := by
    simpa [Function.Periodic.qParam, mul_assoc, mul_left_comm, mul_comm] using
      (Complex.exp_nat_mul (2 * Real.pi * Complex.I * w) n).symm
  simp [hcoeff, hqpow, smul_eq_mul, mul_left_comm, mul_comm]

private lemma E4qSeries_eq : E4qSeries = E₄.toFun := by
  ext w
  simpa [E4qSeries] using (E4qSeries_hasSum w).tsum_eq

private lemma E4qSeries_derivBound :
    ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K),
        ‖E4Coeff n * (2 * Real.pi * Complex.I * n) *
            cexp (2 * Real.pi * Complex.I * n * k.1)‖ ≤ u n := by
  intro K hK hKc
  have him_cont : ContinuousOn (fun w : ℂ => w.im) K := Complex.continuous_im.continuousOn
  have him_pos : ∀ w ∈ K, (0 : ℝ) < w.im := fun w hw => hK hw
  obtain ⟨δ, hδ_pos, hδ_le⟩ :=
    IsCompact.exists_forall_le' (s := K) hKc him_cont (a := (0 : ℝ)) him_pos
  let r : ℝ := Real.exp (-2 * Real.pi * δ)
  have hr_lt_one : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, hδ_pos])
  have hr_nonneg : 0 ≤ r := by simpa [r] using (Real.exp_pos (-2 * Real.pi * δ)).le
  have hr_norm : ‖(r : ℝ)‖ < 1 := by simpa [Real.norm_of_nonneg hr_nonneg] using hr_lt_one
  let u : ℕ → ℝ := fun n => (480 * Real.pi) * (((n : ℝ) ^ 5 : ℝ) * r ^ n)
  have hu : Summable u := by
    have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5 hr_norm
    exact hs.mul_left (480 * Real.pi)
  refine ⟨u, hu, fun n k => ?_⟩
  by_cases hn0 : n = 0
  · subst hn0
    simp [E4Coeff, u]
  have hk_im : δ ≤ k.1.im := hδ_le k.1 k.2
  have hnorm_exp :
      ‖cexp (2 * Real.pi * Complex.I * (n : ℂ) * k.1)‖ ≤ r ^ n :=
    SpherePacking.ForMathlib.norm_cexp_two_pi_I_mul_nat_mul_le_pow_of_le_im n hk_im
  have hσ : (σ 3 n : ℝ) ≤ (n : ℝ) ^ 4 := by
    exact_mod_cast (sigma_bound 3 n)
  have hcoeff_norm : ‖E4Coeff n‖ ≤ (240 : ℝ) * (n : ℝ) ^ 4 := by
    have hc' : E4Coeff n = (240 : ℂ) * (σ 3 n : ℂ) := by simp [E4Coeff, hn0]
    simp_all
  have hnorm_2pin : ‖(2 * Real.pi * Complex.I * (n : ℂ) : ℂ)‖ = 2 * Real.pi * (n : ℝ) := by
    simp [Real.norm_of_nonneg Real.pi_pos.le, mul_left_comm, mul_comm]
  have hmul1 :
      ‖E4Coeff n‖ * ‖(2 * Real.pi * Complex.I * (n : ℂ) : ℂ)‖ ≤
        ((240 : ℝ) * (n : ℝ) ^ 4) * (2 * Real.pi * (n : ℝ)) := by
    exact mul_le_mul hcoeff_norm (le_of_eq hnorm_2pin) (norm_nonneg _) (by positivity)
  calc
    ‖E4Coeff n * (2 * Real.pi * Complex.I * n) * cexp (2 * Real.pi * Complex.I * n * k.1)‖ =
        (‖E4Coeff n‖ * ‖(2 * Real.pi * Complex.I * (n : ℂ) : ℂ)‖) *
          ‖cexp (2 * Real.pi * Complex.I * (n : ℂ) * k.1)‖ := by
          simp [mul_assoc]
    _ ≤ (((240 : ℝ) * (n : ℝ) ^ 4) * (2 * Real.pi * (n : ℝ))) *
          ‖cexp (2 * Real.pi * Complex.I * (n : ℂ) * k.1)‖ := by
          exact mul_le_mul_of_nonneg_right hmul1 (norm_nonneg _)
    _ ≤ (((240 : ℝ) * (n : ℝ) ^ 4) * (2 * Real.pi * (n : ℝ))) * (r ^ n) := by
          exact mul_le_mul_of_nonneg_left hnorm_exp (by positivity)
    _ = u n := by
          dsimp [u]
          ring_nf

/-- The Fourier expansion of `E₂ * E₄ - E₆` as an `ℕ+`-indexed series. -/
public theorem E₂_mul_E₄_sub_E₆ (z : ℍ) :
    (E₂ z) * (E₄ z) - (E₆ z) =
      720 * ∑' (n : ℕ+), n * (σ 3 n) * cexp (2 * Real.pi * Complex.I * n * z) := by
  have hDE4 :
      D E₄.toFun z = ∑' n : ℕ, (n : ℂ) * E4Coeff n * cexp (2 * Real.pi * Complex.I * n * z) := by
    -- Differentiate the `q`-expansion termwise, then identify it with `E₄`.
    have hD :
        D E4qSeries z =
          ∑' n : ℕ, (n : ℂ) * E4Coeff n * cexp (2 * Real.pi * Complex.I * n * z) := by
      simpa [E4qSeries] using D_qexp_tsum E4Coeff z (by
        intro K hK hKc
        simpa using E4qSeries_derivBound K hK hKc)
    simpa [E4qSeries_eq] using hD
  have hRam := congrArg (fun f : ℍ → ℂ => f z) ramanujan_E₄
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have hmain : (E₂ z) * (E₄ z) - (E₆ z) = (3 : ℂ) * D E₄.toFun z := by
    simp_all
  have htail :
      (∑' n : ℕ, (n : ℂ) * E4Coeff n * cexp (2 * Real.pi * Complex.I * n * z)) =
        (240 : ℂ) * ∑' (n : ℕ+), n * (σ 3 n) * cexp (2 * Real.pi * Complex.I * n * z) := by
    let f : ℕ → ℂ := fun n => (n : ℂ) * E4Coeff n * cexp (2 * Real.pi * Complex.I * n * z)
    have hf0 : f 0 = 0 := by simp [f, E4Coeff]
    have htsum : (∑' n : ℕ, f n) = ∑' n : ℕ+, f n := by
      simpa using (tsum_pNat (f := f) hf0).symm
    calc
      (∑' n : ℕ, (n : ℂ) * E4Coeff n * cexp (2 * Real.pi * Complex.I * n * z))
          = ∑' n : ℕ+, f n := by simpa [f] using htsum
      _ =
          (240 : ℂ) *
            ∑' n : ℕ+, n * (σ 3 n) * cexp (2 * Real.pi * Complex.I * n * z) := by
          simp [f, E4Coeff, tsum_mul_left, mul_assoc, mul_left_comm, mul_comm]
  grind only

/-- Rewrite `A_E` as an `ℕ`-indexed series with terms `A_E_term z n`. -/
public lemma A_E_eq_tsum (z : ℍ) : A_E z = ∑' n : ℕ, A_E_term z n := by
  -- Start from the `ℕ+`-Fourier expansion.
  have h :=
    (E₂_mul_E₄_sub_E₆ z : (E₂ z) * (E₄ z) - (E₆ z) =
      720 * ∑' (n : ℕ+), (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * Real.pi * Complex.I * (n : ℂ) * (z : ℂ)))
  -- Shift the `ℕ+`-series to an `ℕ`-series with exponent `n+1`.
  let f : ℕ → ℂ := fun n =>
    (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * Real.pi * Complex.I * (n : ℂ) * (z : ℂ))
  have hshift : (∑' n : ℕ+, f n) = ∑' n : ℕ, f (n + 1) := by
    simpa [f] using (tsum_pnat_eq_tsum_succ (f := f))
  -- Absorb the scalar `720` and rewrite coefficients.
  calc
    A_E z = (720 : ℂ) * ∑' n : ℕ+, f n := by
      simpa [A_E, f, mul_assoc, mul_left_comm, mul_comm] using h
    _ = (720 : ℂ) * ∑' n : ℕ, f (n + 1) := by simp [hshift]
    _ = ∑' n : ℕ, (720 : ℂ) * f (n + 1) := by simp [tsum_mul_left]
    _ = ∑' n : ℕ, A_E_term z n := by
      simp [A_E_term, A_E_coeff, f, mul_assoc, mul_left_comm, mul_comm]

end Ramanujan_Formula
