module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.Parametric
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.BPrimeExtension
public import SpherePacking.MagicFunction.g.CohnElkies.IntegralReductions
public import SpherePacking.MagicFunction.g.CohnElkies.IntegralReps.ACDomain
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.ContinuationCommon
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv


/-!
# Analytic continuation for `AnotherIntegral.B`

Assuming the "another integral" formula for `b'` holds for all real `u > 2`, this file extends the
equality to all real `0 < u` with `u ≠ 2` by comparing analytic functions on the punctured
right half-plane `ACDomain = {u : ℂ | 0 < Re u} \\ {2}` and applying an identity theorem.

## Main definition
* `bAnotherRHS`

## Main statement
* `bRadial_eq_another_integral_analytic_continuation_of_gt2`

## Domain for the identity theorem

We work on `ACDomain = {u : ℂ | 0 < Re u} \\ {2}`.
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Topology

open MeasureTheory Real Complex

open SpherePacking

open MagicFunction.FourierEigenfunctions

noncomputable section

/-!
## Analytic RHS function on `ℂ`
-/

def bAnotherRHS (u : ℂ) : ℂ :=
  (-4 * (Complex.I : ℂ)) *
    (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) *
      ((144 : ℂ) / ((π : ℂ) * u) + (1 : ℂ) / ((π : ℂ) * (u - 2)) + bAnotherIntegralC u)

lemma bAnotherRHS_analyticOnNhd :
    AnalyticOnNhd ℂ bAnotherRHS ACDomain := by
  have hb : ACDomain ⊆ rightHalfPlane := by
    intro u hu
    exact hu.1
  have hπ : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hu_ne0 : ∀ u ∈ ACDomain, u ≠ 0 := by
    intro u hu h0
    have hre : (0 : ℝ) < u.re := by
      simpa [rightHalfPlane] using hu.1
    have hne : u.re ≠ 0 := ne_of_gt hre
    exact hne (by simp [h0])
  have hsin_arg : AnalyticOnNhd ℂ (fun u : ℂ => (π : ℂ) * u / 2) ACDomain := by
    refine (analyticOnNhd_const.mul analyticOnNhd_id).div analyticOnNhd_const ?_
    intro _u _hu
    norm_num
  have hsin : AnalyticOnNhd ℂ (fun u : ℂ => Complex.sin ((π : ℂ) * u / 2)) ACDomain := by
    simpa [Function.comp] using
      (analyticOnNhd_sin (s := (Set.univ : Set ℂ))).comp hsin_arg (by intro _ _; simp)
  have hsin_sq :
      AnalyticOnNhd ℂ (fun u : ℂ => (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ)) ACDomain :=
    hsin.pow 2
  have hI : AnalyticOnNhd ℂ bAnotherIntegralC ACDomain :=
    (bAnotherIntegralC_analyticOnNhd).mono hb
  have hsub2 : AnalyticOnNhd ℂ (fun u : ℂ => u - 2) ACDomain :=
    analyticOnNhd_id.sub analyticOnNhd_const
  have hden1 : ∀ u ∈ ACDomain, (π : ℂ) * u ≠ 0 := by
    intro u hu
    exact mul_ne_zero hπ (hu_ne0 u hu)
  have hden2 : ∀ u ∈ ACDomain, (π : ℂ) * (u - 2) ≠ 0 := by
    intro u hu
    have hu_ne2 : u ≠ (2 : ℂ) := by
      simpa [Set.mem_singleton_iff] using hu.2
    have : u - 2 ≠ 0 := sub_ne_zero.2 hu_ne2
    exact mul_ne_zero hπ this
  have hterm1 :
      AnalyticOnNhd ℂ (fun u : ℂ => (144 : ℂ) / ((π : ℂ) * u)) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul analyticOnNhd_id) hden1
  have hterm2 :
      AnalyticOnNhd ℂ (fun u : ℂ => (1 : ℂ) / ((π : ℂ) * (u - 2))) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul hsub2) hden2
  have hinner :
      AnalyticOnNhd ℂ
        (fun u : ℂ =>
          (144 : ℂ) / ((π : ℂ) * u) + (1 : ℂ) / ((π : ℂ) * (u - 2)) + bAnotherIntegralC u)
        ACDomain := by
    simpa [add_assoc] using (hterm1.add hterm2).add hI
  have hconst : AnalyticOnNhd ℂ (fun _u : ℂ => (-4 * (Complex.I : ℂ))) ACDomain :=
    analyticOnNhd_const
  -- Avoid `simp` normalization issues; unfold and use the analytic-factorization directly.
  unfold bAnotherRHS
  exact (hconst.mul hsin_sq).mul hinner

lemma bAnotherRHS_ofReal (u : ℝ) :
    bAnotherRHS (u : ℂ) =
      (-4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) +
            ∫ t in Set.Ioi (0 : ℝ), bAnotherBase t * (Real.exp (-π * u * t) : ℂ)) := by
  simp [bAnotherRHS, bAnotherIntegralC_ofReal, sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
    mul_assoc]

/-!
## Analytic extension of `b'`
-/

lemma exists_b'_analytic_extension :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f ACDomain ∧
      (∀ u : ℝ, 0 < u → u ≠ 2 → f (u : ℂ) = b' u) := by
  refine ⟨bPrimeC, ?_, ?_⟩
  · have hb : ACDomain ⊆ rightHalfPlane := by
      intro u hu
      exact hu.1
    exact (bPrimeC_analyticOnNhd).mono hb
  · intro u hu _hu2
    have hb' : MagicFunction.b.RealIntegrals.b' u = b' u := by
      simpa using
        (MagicFunction.g.CohnElkies.b'_eq_realIntegrals_b' (u := u) (le_of_lt hu)).symm
    simpa [hb'] using (bPrimeC_ofReal u)

/-!
## Final wrapper theorem

This is the desired analytic continuation statement, packaged to take the `u > 2` identity as an
input (supplied by `SpherePacking/MagicFunction/g/CohnElkies/AnotherIntegral/B/Main.lean`).
-/

/--
Analytic-continuation step: extend the "another integral" identity for `b'` from `u > 2` to all
real `0 < u` with `u ≠ 2`.
-/
public theorem bRadial_eq_another_integral_analytic_continuation_of_gt2
    (h_gt2 :
      ∀ r : ℝ, 2 < r →
        b' r =
          (-4 * (Complex.I : ℂ)) *
            (Real.sin (π * r / 2)) ^ (2 : ℕ) *
              ((144 : ℂ) / (π * r) + (1 : ℂ) / (π * (r - 2)) +
                ∫ t in Set.Ioi (0 : ℝ),
                  bAnotherBase t * (Real.exp (-π * r * t) : ℂ)))
    {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    b' u =
      (-4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) +
            ∫ t in Set.Ioi (0 : ℝ),
              bAnotherBase t * (Real.exp (-π * u * t) : ℂ)) := by
  have h3_mem : (3 : ℂ) ∈ ACDomain := by
    simp [ACDomain, rightHalfPlane]
  rcases exists_b'_analytic_extension with ⟨f, hf_analytic, hf_ofReal⟩
  have hf_gt2 : ∀ r : ℝ, 2 < r → f (r : ℂ) = bAnotherRHS (r : ℂ) := by
    intro r hr
    have hr0 : 0 < r := lt_trans (by norm_num) hr
    have hr2 : r ≠ 2 := by linarith
    have hf_r : f (r : ℂ) = b' r := by simpa using hf_ofReal r hr0 hr2
    exact (hf_r.trans (h_gt2 r hr)).trans (bAnotherRHS_ofReal r).symm
  have hfreq : (∃ᶠ z in 𝓝[≠] (3 : ℂ), f z = bAnotherRHS z) :=
    frequently_eq_near_three hf_gt2
  have hEqOn : Set.EqOn f bAnotherRHS ACDomain :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf_analytic bAnotherRHS_analyticOnNhd
      ACDomain_isPreconnected h3_mem hfreq
  have hu_mem : (u : ℂ) ∈ ACDomain := by
    refine ⟨?_, ?_⟩
    · simpa [rightHalfPlane] using hu
    · have : (u : ℂ) ≠ (2 : ℂ) := by exact_mod_cast hu2
      simpa [ACDomain, Set.mem_singleton_iff] using this
  have hmain : f (u : ℂ) = bAnotherRHS (u : ℂ) := hEqOn hu_mem
  have hf_u : f (u : ℂ) = b' u := by
    simpa using hf_ofReal u hu hu2
  have : b' u = bAnotherRHS (u : ℂ) := by
    simpa [hf_u] using (hf_u.symm.trans hmain)
  simpa using this.trans (bAnotherRHS_ofReal u)

end

end MagicFunction.g.CohnElkies.IntegralReps
