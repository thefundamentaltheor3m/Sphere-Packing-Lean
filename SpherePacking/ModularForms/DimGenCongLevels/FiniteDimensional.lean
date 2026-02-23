module
import Mathlib.RingTheory.Artinian.Module
public import SpherePacking.ModularForms.DimGenCongLevels.Basic
public import SpherePacking.ModularForms.DimGenCongLevels.Aux

/-!
# Injectivity of finite `q`-coefficients

This file proves an Artinian stabilization argument: for a finite-dimensional space of modular
forms, finitely many `q`-coefficients already determine the form.

## Main statement
* `exists_qCoeff_injective`
-/

namespace SpherePacking.ModularForms

open scoped MatrixGroups Topology BigOperators
open UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass Filter

noncomputable section

section Truncation

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ}

/-- The subspace of modular forms whose first `N` `q`-coefficients vanish. -/
def qKerBelow
    [DiscreteTopology Γ] [Γ.HasDetOne]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (N : ℕ) : Submodule ℂ (ModularForm Γ k) where
  carrier := { f | ∀ n < N, (qExpansion h f).coeff n = 0 }
  zero_mem' := by
    intro n hn
    simp [qExpansion_zero (h := h)]
  add_mem' := by
    intro f g hf hg n hn
    simp [qExpansion_add (Γ := Γ) (k := k) (h := h) f g hh hΓ, hf n hn, hg n hn]
  smul_mem' := by
    intro a f hf n hn
    simp [qExpansion_smul (Γ := Γ) (k := k) (h := h) a f hh hΓ, hf n hn]

lemma qKerBelow_antitone
    [DiscreteTopology Γ] [Γ.HasDetOne] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    Antitone (qKerBelow (Γ := Γ) (k := k) (h := h) hh hΓ) := by
  intro A B hAB f hf n hn
  exact hf n (lt_of_lt_of_le hn hAB)

lemma qKerBelow_iInf_eq_bot
    [DiscreteTopology Γ] [Γ.HasDetOne]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    (⨅ N : ℕ, qKerBelow (Γ := Γ) (k := k) (h := h) hh hΓ N) = ⊥ := by
  ext f
  constructor
  · intro hf
    have hf' : ∀ N : ℕ, f ∈ qKerBelow (Γ := Γ) (k := k) (h := h) hh hΓ N :=
      (Submodule.mem_iInf (p := fun N => qKerBelow (Γ := Γ) (k := k) (h := h) hh hΓ N)).1 hf
    refine (Submodule.mem_bot (R := ℂ) (x := f)).2 ?_
    apply (qExpansion_eq_zero_iff (Γ := Γ) (h := h) hh hΓ f).1
    ext n
    exact hf' (n + 1) n (Nat.lt_succ_self _)
  · intro hf
    subst hf
    simp

lemma exists_qKerBelow_eq_bot
    [DiscreteTopology Γ] [Γ.HasDetOne]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) [FiniteDimensional ℂ (ModularForm Γ k)] :
    ∃ N : ℕ, qKerBelow (Γ := Γ) (k := k) (h := h) hh hΓ N = ⊥ := by
  haveI : IsArtinian ℂ (ModularForm Γ k) := by infer_instance
  let f : ℕ →o (Submodule ℂ (ModularForm Γ k))ᵒᵈ :=
    { toFun := fun N => OrderDual.toDual (qKerBelow (Γ := Γ) (k := k) (h := h) hh hΓ N)
      monotone' := by
        intro A B hAB
        exact qKerBelow_antitone (Γ := Γ) (k := k) (h := h) hh hΓ hAB }
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes (R := ℂ) (M := ModularForm Γ k) f
  have hle : ∀ M : ℕ, qKerBelow (Γ := Γ) (k := k) (h := h) hh hΓ N ≤
      qKerBelow (Γ := Γ) (k := k) (h := h) hh hΓ M := by
    intro M
    by_cases hNM : N ≤ M
    · have : qKerBelow (Γ := Γ) (k := k) (h := h) hh hΓ N =
          qKerBelow (Γ := Γ) (k := k) (h := h) hh hΓ M := by
        simpa using congrArg OrderDual.ofDual (hN M hNM)
      simp [this]
    · exact qKerBelow_antitone (Γ := Γ) (k := k) (h := h) hh hΓ (Nat.le_of_not_ge hNM)
  have hiInf :
      (⨅ M : ℕ, qKerBelow (Γ := Γ) (k := k) (h := h) hh hΓ M) =
        qKerBelow (Γ := Γ) (k := k) (h := h) hh hΓ N := by
    exact le_antisymm (iInf_le _ N) (le_iInf hle)
  refine ⟨N, ?_⟩
  simpa [hiInf] using qKerBelow_iInf_eq_bot (Γ := Γ) (k := k) (h := h) hh hΓ

/-- There exists `N` such that the first `N` `q`-coefficients determine a modular form. -/
public lemma exists_qCoeff_injective
    [DiscreteTopology Γ] [Γ.HasDetOne]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) [FiniteDimensional ℂ (ModularForm Γ k)] :
    ∃ N : ℕ, Function.Injective
      (fun f : ModularForm Γ k => fun n : Fin N => (qExpansion h f).coeff n) := by
  obtain ⟨N, hN⟩ := exists_qKerBelow_eq_bot (Γ := Γ) (k := k) (h := h) hh hΓ
  refine ⟨N, ?_⟩
  intro f g hfg
  have hsub : f - g ∈ qKerBelow (Γ := Γ) (k := k) (h := h) hh hΓ N := by
    intro n hn
    have hcoeff : (qExpansion h f).coeff n = (qExpansion h g).coeff n := by
      simpa using congrArg (fun t => t ⟨n, hn⟩) hfg
    simpa [hcoeff] using
      congrArg (fun ps : PowerSeries ℂ => ps.coeff n) (qExpansion_sub (Γ := Γ) (h := h) hh hΓ f g)
  have : f - g = 0 := by simpa [hN] using hsub
  exact sub_eq_zero.mp this

end Truncation

end

end SpherePacking.ModularForms
