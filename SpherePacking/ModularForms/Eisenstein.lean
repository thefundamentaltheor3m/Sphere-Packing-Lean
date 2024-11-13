/-
The purpose of this file is to define the Eisenstein series we are interested in using more convenient notation.
-/

import Mathlib
-- import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open ArithmeticFunction

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R
noncomputable section Definitions

def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0



-- private lemma aux4 : (3 : ℤ) ≤ 4 := by norm_num
-- private lemma aux6 : (3 : ℤ) ≤ 6 := by norm_num

/- The Eisenstein Series E₂, E₄ and E₆ -/

def E₄ : ModularForm (CongruenceSubgroup.Gamma ↑1) 4 :=
  (1/2) • eisensteinSeries_MF (by norm_num) standardcongruencecondition /-they need  1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/
def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma ↑1) k :=
  (1/2) • eisensteinSeries_MF hk standardcongruencecondition /-they need  1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/
def E₆ : ModularForm (CongruenceSubgroup.Gamma ↑1) 6 :=
  (1/2) • eisensteinSeries_MF (by norm_num) standardcongruencecondition

def S0 : Set ℤ := {0}ᶜ

def G₂' : ℍ → ℂ := fun z => ∑' (m : ℤ), (∑' (n : ℤ), 1 / (m * z + n) ^ 2) --hmm is this right?

/--Maybe this is the definition we want as I cant see how to easily show the other outer sum is
absolutely convergent. -/
def G₂ : ℍ → ℂ := fun z =>  2 * riemannZeta 2 + limUnder (atTop)
    (fun k : ℕ+ => ∑ m in Finset.range k, 2 • (∑' (n : ℤ), 1 / ((m + 1 : ℂ) * z + n) ^ 2))

lemma G₂_eq1 (z : ℍ) : G₂ z = 2 * riemannZeta 2 +
  ∑' (m : ℕ+), ∑' (n : ℤ), 1 / ((m : ℂ) * z + n) ^ 2 := by
  rw [G₂]
  rw [Filter.Tendsto.limUnder_eq]
  simp
  rw [@NormedAddCommGroup.tendsto_atTop]
  --is this true?
  sorry

lemma fsb (b : ℕ) : Finset.Ico (-(b+1) : ℤ) (b+1) = Finset.Ico (-(b : ℤ)) (b) ∪
    {-((b+1) : ℤ), (b : ℤ)} :=  by
  ext n
  simp
  omega


lemma PS1 (z : ℍ) (m : ℤ) (hm : m ≠ 0) : limUnder atTop
  (fun N : ℕ => ∑ n in (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) = 0 := by
  apply Filter.Tendsto.limUnder_eq
  rw [@NormedAddCommGroup.tendsto_nhds_zero]
  intro ε hε
  simp only [  norm_eq_abs, eventually_atTop, ge_iff_le]
  use 0
  intro b hb
  have : ∑ n in (Finset.Ico (-(b : ℤ)) (b : ℤ)),
    (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1)) = (1 / ((m : ℂ) * z - b) -  1 / (m * z + b))  := by
    induction' b with b hB
    aesop
    simp only [Nat.cast_add, Nat.cast_one, Int.reduceNeg, one_div,
      Finset.sum_sub_distrib] at *
    rw [fsb]
    rw [Finset.sum_union]
    rw [Finset.sum_union]
    have := hB ?_



    all_goals{sorry}


  rw [this]
  simp [hε]
  sorry

lemma ada (f : ℤ → ℂ) (h : ∀ i, f i = 0) : ∑' n, f n = 0 := by
  convert tsum_zero
  aesop


lemma PS2 (z : ℍ) : ∑' m : S0, (limUnder atTop
  (fun N : ℕ => ∑ n in (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1)))) = 0 := by
    convert tsum_zero
    next m =>
    apply PS1
    apply m.2

lemma PS3 (z : ℍ) (n : ℤ) : limUnder atTop
  (fun N : ℕ => ∑ m in (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    ∑' m : ℕ+, (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) = -2 * π * Complex.I / z := by sorry

lemma G2_alt_eq (z : ℍ) : --this sum is now abs convergent. Idea is to subtract PS1 from the G₂ defn.
    G₂ z = ∑' m : ℤ, ∑' n : ℤ, 1 / (((m : ℂ)* z +n)^2 * (m * z + n +1))  := by
    rw [G₂]
    have :=  PS2 z

    sorry

/-This is proven in the modular forms repo. -/
lemma G2_summable_aux (n : ℤ) (z : ℍ) (k : ℤ) (hk : 2 ≤ k) :
    Summable fun d : ℤ => ((((n : ℂ) * z) + d) ^ k)⁻¹ := by sorry

/-Check that we didnt define the zero function! -/
lemma G2'_summable (z : ℍ) : Summable fun m : ℤ =>  (∑' (n : ℤ), 1 / ((m : ℂ) * z + n) ^ 2) := by
  --is this true??
  sorry


/-This is from the modforms repo, so no need to prove it. -/
theorem series_eql' (z : ℍ) :
    ↑π * Complex.I - 2 * ↑π * Complex.I * ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * z * n) =
      1 / z + ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) := sorry

/-This is from the modforms repo, so no need to prove it. -/
theorem q_exp_iden (k : ℕ) (hk : 2 ≤ k) (z : ℍ) :
    ∑' d : ℤ, 1 / ((z : ℂ) + d) ^ k =
      (-2 * ↑π * Complex.I) ^ k / (k - 1)! *
      ∑' n : ℕ+, n ^ ((k - 1) ) * Complex.exp (2 * ↑π * Complex.I * z * n) := sorry

def E₂ : ℍ → ℂ := (1 / (2 * riemannZeta 2)) •  G₂

/-This result is already proven in the modular forms repo and being PRed (slowly) into mathlib, so
we can use it freely here. -/
lemma E_k_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (E k hk) z = 1 +
        (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, sigma (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by sorry

/--This we should get from the modular forms repo stuff. Will port these things soon. -/
lemma E₂_eq (z : UpperHalfPlane) : E₂ z =
    1 - 24 * ∑' (n : ℕ+),
    ↑n * cexp (2 * π * Complex.I * n * z) / (1 - cexp (2 * π * Complex.I * n * z)) := sorry

/-This should follow from the mod forms repo stuff. Will port soon. -/
lemma G₂_eq (z : UpperHalfPlane) : G₂ z = (2 * riemannZeta 2) +
    8 * π ^ 2 * ∑' (n : ℕ+), (sigma 1 n) * cexp (2 * π * Complex.I * n * z) := sorry

/-This is the annoying exercise. -/
lemma G₂_transform (z : ℍ) (γ : SL(2, ℤ)) : (G₂ ∣[(2 : ℤ)] γ) z =
  G₂ z - (2 * π * Complex.I * γ 1 0) / (denom γ z) := sorry

/-Should be easy from the above.-/
lemma E₂_transform (z : ℍ) (γ : SL(2, ℤ)) : (E₂ ∣[(2 : ℤ)] ModularGroup.S) z =
  E₂ z + 6 / ( π * Complex.I * z) := sorry

lemma MultipliableDiscriminantProductExpansion : Multipliable (fun (z : UpperHalfPlane) =>
  cexp (2 * π * Complex.I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * Complex.I * n * z)) ^ 24) := sorry

/- The discriminant form -/
def Δ (z : UpperHalfPlane) :=  cexp (2 * π * Complex.I * z) * ∏' (n : ℕ+),
    (1 - cexp (2 * π * Complex.I * n * z)) ^ 24

/-This should be easy from the definition and the Mulitpliable bit. -/
lemma Δ_ne_zero (z : UpperHalfPlane) : Δ z ≠ 0 := by sorry

/- The eta function. Best to define it on all of ℂ since we want to take its logDeriv. -/
def η (z : ℂ) := cexp (π * Complex.I * z / 24) * ∏' (n : ℕ+),
    (1 - cexp (2 * π * Complex.I * n * z))

lemma eta_disc (z : ℍ) : (η ^ 24) z = Δ z := by sorry

lemma eta_logDeriv (z : ℍ) : logDeriv η z = (π * Complex.I / 12) * E₂ z := sorry

/- φ₀, φ₋₂ and φ₋₄, except we can't use - signs in subscripts for definitions... -/
def φ₀ (z : UpperHalfPlane) := (((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) / (Δ z)
def φ₂' (z : UpperHalfPlane) := (E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)
def φ₄' (z : UpperHalfPlane) := ((E₄ z) ^ 2) / (Δ z)
/- We extend these definitions to ℂ for convenience. -/
def φ₀'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₀ ⟨z, hz⟩ else 0
def φ₂'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₂' ⟨z, hz⟩ else 0
def φ₄'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₄' ⟨z, hz⟩ else 0

end Definitions

noncomputable section Holomorphicity

-- Try and get the desired holomorphicity results for φ₀, φ₂ and φ₄ in terms of the Eᵢ

end Holomorphicity

noncomputable section Integrability

-- Here, we show that

end Integrability

open Complex Real

noncomputable section  Product_Formula
/-This one is easy.-/
lemma Discriminant_T_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ := sorry

/-This is the hard one. -/
lemma Discriminant_S_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.S) = Δ := sorry
-- use E₂_transform

def Discriminant_SIF : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := Δ
  slash_action_eq' A := by sorry

open Manifold in
lemma Discriminant_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Δ := sorry

lemma Discriminant_zeroAtImInfty (γ : SL(2, ℤ)): IsZeroAtImInfty (Δ ∣[(12 : ℤ)] γ) := sorry

def CuspForm_div_Discriminant (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k) (z : ℍ) :
  ModularForm (CongruenceSubgroup.Gamma 1) (k - 12) where
    toFun := f  / Δ
    slash_action_eq' := sorry
    holo' := sorry --need to use the q-expansion to see that its still holo
    bdd_at_infty' := sorry


/-this is done in the modformdims repo, soon to be in mathlib.-/
lemma weigth_zero_rank_eq_one : Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) 0) = 1 :=
  by sorry

/-this is done in the modformdims repo, soon to be in mathlib.-/
lemma neg_weight_rank_zero (k : ℤ) (hk : k < 0) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = 0 := by sorry

def CuspForms_iso_Modforms (k : ℤ) : CuspForm (CongruenceSubgroup.Gamma 1) k ≃ₗ[ℂ]
    ModularForm (CongruenceSubgroup.Gamma 1) (k - 12) := sorry

theorem DiscriminantProductFormula (z : UpperHalfPlane) : Δ z = ((E₄ z) ^ 3 - (E₆ z) ^ 2) / 1728 := sorry
--enough to check its a cuspform, since if it is, then divining by Δ gives a modular form of weight 0.

lemma weight_two_empty (f : ModularForm (CongruenceSubgroup.Gamma 1) 2) : f = 0 := sorry
/- cant be a cuspform from the above, so let a be its constant term, then f^2 = a^2 E₄ and
f^3 = a^3 E₆, but now this would mean that Δ = 0 or a = 0, which is a contradiction. -/

lemma dim_modforms_eq_one_add_dim_cuspforms (k : ℤ) (hk : 2 < k):
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) =
    1 + Module.rank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) k) := sorry

lemma dim_modforms_lvl_one (k : ℤ) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = if 12 ∣ k - 2 then
    Nat.floor (k / 12) else Nat.floor (k / 12) + 1 := sorry

lemma dim_gen_cong_levels (k : ℤ) (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) :
    FiniteDimensional ℂ (ModularForm Γ k) := by sorry
--use the norm to turn it into a level one question.


end Product_Formula

#min_imports
