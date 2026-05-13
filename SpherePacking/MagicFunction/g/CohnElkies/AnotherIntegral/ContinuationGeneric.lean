/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SpherePacking.Basic.Domains.RightHalfPlane
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

/-!
# Generic analytic continuation wrapper

Defines the right-half-plane domain `ACDomain = {u : ℂ | 0 < re u} \ {2}` used for analytic
continuation in the integral representations for Viazovska's magic function, and proves the
shared wrapper theorem `analytic_continuation_of_gt2` for analytic continuation on `ACDomain`,
used by the `a'` and `b'` continuation arguments.
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped Topology
open Real Complex Filter SpherePacking

/-- The analytic continuation domain `U = {u : ℂ | 0 < re u} \ {2}`. -/
@[expose] public def ACDomain : Set ℂ := rightHalfPlane \ {2}

/-- The analytic continuation domain `ACDomain` is preconnected. -/
public lemma ACDomain_isPreconnected : IsPreconnected ACDomain := by
  -- We use a homeomorphism `ℂ ≃ₜ {u : ℂ // 0 < u.re}` to reduce to connectedness of the
  -- complement of a singleton in `ℂ`.
  let z2 : {u : ℂ // 0 < u.re} := ⟨(2 : ℂ), by simp⟩
  let h₃ : (Set.Ioi (0 : ℝ) × ℝ) ≃ₜ {u : ℂ // 0 < u.re} :=
    { toEquiv :=
        { toFun := fun p =>
            ⟨(p.1 : ℝ) + p.2 * Complex.I, by
              have hp : (0 : ℝ) < (p.1 : ℝ) := p.1.2
              simpa using hp⟩
          invFun := fun z => (⟨z.1.re, z.2⟩, z.1.im)
          left_inv := by
            rintro ⟨x, y⟩
            ext <;> simp
          right_inv := by
            rintro ⟨z, hz⟩
            apply Subtype.ext
            simp [Complex.re_add_im] }
      continuous_toFun := by
        refine
            (show Continuous (fun p : Set.Ioi (0 : ℝ) × ℝ => (p.1 : ℝ) + p.2 * Complex.I) by
              fun_prop).subtype_mk fun p => by
            have hp : (0 : ℝ) < (p.1 : ℝ) := p.1.2
            simpa using hp
      continuous_invFun := by
        fun_prop }
  let h : ℂ ≃ₜ {u : ℂ // 0 < u.re} :=
    (Complex.equivRealProdCLM.toHomeomorph.trans
          ((Real.expOrderIso.toHomeomorph).prodCongr (Homeomorph.refl ℝ))).trans h₃
  have hpre : IsPreconnected ({z2}ᶜ : Set {u : ℂ // 0 < u.re}) := by
    have hconn : IsConnected ({h.symm z2}ᶜ : Set ℂ) :=
      isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) (h.symm z2)
    have himage :
        h '' ({h.symm z2}ᶜ : Set ℂ) = ({z2}ᶜ : Set {u : ℂ // 0 < u.re}) := by
      ext z
      refine ⟨?_, fun hz => ⟨h.symm z, by simpa, by simp⟩⟩
      rintro ⟨x, hx, rfl⟩
      have hx' : x ≠ h.symm z2 := by simpa using hx
      simpa using fun hz => hx' (by simpa using congrArg h.symm hz)
    simpa [himage] using hconn.isPreconnected.image h h.continuous.continuousOn
  have hval :
      ((Subtype.val : {u : ℂ // 0 < u.re} → ℂ) '' ({z2}ᶜ :
          Set {u : ℂ // 0 < u.re})) = ACDomain := by
    ext u
    refine ⟨?_, ?_⟩
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ≠ z2 := by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
      exact ⟨z.2, by simpa using fun hEq => hz' (Subtype.ext hEq)⟩
    · rintro hu
      have hu_re : 0 < u.re := by simpa [rightHalfPlane] using hu.1
      refine ⟨⟨u, hu_re⟩, ?_, rfl⟩
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using fun hEq =>
        (by simpa using hu.2 : u ≠ (2 : ℂ)) (congrArg Subtype.val hEq)
  simpa [hval] using
    hpre.image (Subtype.val : {u : ℂ // 0 < u.re} → ℂ) continuous_subtype_val.continuousOn

/-- Generic analytic continuation on `ACDomain = {Re u > 0} \ {2}`. -/
public theorem analytic_continuation_of_gt2
    {value : ℝ → ℂ} {rhsC : ℂ → ℂ} {rhsR : ℝ → ℂ}
    (h_extension : ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f ACDomain ∧
      ∀ u : ℝ, 0 < u → u ≠ 2 → f (u : ℂ) = value u)
    (h_rhs_analytic : AnalyticOnNhd ℂ rhsC ACDomain)
    (h_rhs_ofReal : ∀ u : ℝ, rhsC (u : ℂ) = rhsR u)
    (h_gt2 : ∀ r : ℝ, 2 < r → value r = rhsR r)
    {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    value u = rhsR u := by
  rcases h_extension with ⟨f, hf_analytic, hf_ofReal⟩
  have hf_gt2 : ∀ r : ℝ, 2 < r → f (r : ℂ) = rhsC (r : ℂ) := fun r hr =>
    (hf_ofReal r (lt_trans (by norm_num) hr) (by linarith)).trans
      ((h_gt2 r hr).trans (h_rhs_ofReal r).symm)
  have hFreq : (∃ᶠ z in 𝓝[≠] (3 : ℂ), f z = rhsC z) := Filter.frequently_iff.2 <| by
    intro U hU
    obtain ⟨V, hVnhds, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hU
    obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.1 hVnhds
    refine ⟨((3 + ε / 2 : ℝ) : ℂ), hVsub ⟨hball ?_, ?_⟩, by
      simpa using hf_gt2 (3 + ε / 2) (by nlinarith [hεpos])⟩
    · simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε / 2),
        abs_of_nonneg hεpos.le] using half_lt_self hεpos
    · simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (show ((3 + ε / 2 : ℝ) : ℂ) ≠ 3 by exact_mod_cast
          (by nlinarith [hεpos.ne'] : (3 + ε / 2 : ℝ) ≠ 3))
  have hEqOn : Set.EqOn f rhsC ACDomain :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf_analytic h_rhs_analytic
      ACDomain_isPreconnected (by simp [ACDomain, rightHalfPlane]) hFreq
  have hu_mem : (u : ℂ) ∈ ACDomain :=
    ⟨by simpa [rightHalfPlane] using hu,
      by simpa [ACDomain, Set.mem_singleton_iff] using (show (u : ℂ) ≠ 2 by exact_mod_cast hu2)⟩
  exact (hf_ofReal u hu hu2).symm.trans ((hEqOn hu_mem).trans (h_rhs_ofReal u))

/-- If `inner` is analytic on `ACDomain`, then so is
`u ↦ sign * (sin (π u / 2))^2 * inner u` for any constant `sign : ℂ`. -/
public lemma analyticOnNhd_sinSq_prefactor_mul
    (sign : ℂ) {inner : ℂ → ℂ} (hinner : AnalyticOnNhd ℂ inner ACDomain) :
    AnalyticOnNhd ℂ
      (fun u : ℂ => sign * (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) * inner u) ACDomain :=
  (analyticOnNhd_const.mul (by
    have hsin : AnalyticOnNhd ℂ (fun u : ℂ => Complex.sin ((π : ℂ) * u / 2)) ACDomain := by
      simpa [Function.comp] using ((by simpa using (analyticOnNhd_sin (s := (Set.univ : Set ℂ)))) :
          AnalyticOnNhd ℂ (fun z : ℂ => Complex.sin z) (Set.univ : Set ℂ)).comp
        (AnalyticOnNhd.div_const (analyticOnNhd_const.mul analyticOnNhd_id) :
          AnalyticOnNhd ℂ (fun u : ℂ => (π : ℂ) * u / 2) ACDomain) (by intro _ _; simp)
    exact hsin.pow 2)).mul hinner

end MagicFunction.g.CohnElkies.IntegralReps
