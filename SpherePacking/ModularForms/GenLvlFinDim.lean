
import SpherePacking.ModularForms.DimensionFormulas


open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
  Real MatrixGroups CongruenceSubgroup


lemma odd_wt_eq_zero (k : ℤ) (hk : Odd k) (Γ : Subgroup SL(2, ℤ)) (hI : -1 ∈ Γ) :
   Module.rank ℂ (ModularForm Γ k) = 0 := by
  rw [@rank_zero_iff_forall_zero]
  intro f
  ext z
  have h0 := SlashInvariantForm.slash_action_eqn_SL'' f hI z
  simp [denom] at h0
  simpa [Odd.neg_one_zpow hk, CharZero.eq_neg_self_iff] using h0


lemma ModularForm.dimension_level_one_FinDim (k : ℤ) :
    FiniteDimensional ℂ (ModularForm ((CongruenceSubgroup.Gamma 1)) k) := by
  by_cases hk : k < 0
  · exact Module.finite_of_rank_eq_zero (ModularForm.levelOne_neg_weight_rank_zero hk )
  · simp only [not_lt] at hk
    by_cases hk2 : Odd k
    · have := odd_wt_eq_zero k hk2 (CongruenceSubgroup.Gamma 1) (by
       simp [CongruenceSubgroup.Gamma_one_top])
      exact Module.finite_of_rank_eq_zero this
    · lift k to ℕ using hk
      simp at hk2
      by_cases hk3 : 3 ≤ (k : ℤ)
      · have hdim := ModularForm.dimension_level_one k  hk3 hk2
        apply  Module.finite_of_rank_eq_nat hdim
      · simp at hk3
        have : k = 0 ∨ k = 1 ∨ k = 2 := by
          omega
        rcases this with (rfl | rfl | rfl)
        · exact Module.finite_of_rank_eq_nat (ModularForm.levelOne_weight_zero_rank_one )
        · simp at hk2
        · exact Module.finite_of_rank_eq_nat (dim_weight_two )

lemma exists_coeff_ne_zero (k : ℤ) (n : ℕ) (hn : NeZero n)
    {f : ModularForm Γ(n) k} (hf : f ≠ 0) : ∃ m : ℕ, (qExpansion n f).coeff m ≠ 0 := by
    by_contra h
    simp at h
    have := qExpansion_injective n f
    grind

noncomputable def vOrd (k : ℤ) (n : ℕ) (hn : NeZero n)
    {f : ModularForm Γ(n) k} (hf : f ≠ 0) : ℕ := by
    exact Nat.find (exists_coeff_ne_zero k n hn hf)

abbrev cong_levl_map (k : ℤ) (Γ Γ' : Subgroup SL(2, ℤ)) (hGamma : Γ' ≤ Γ)
    (f : ModularForm Γ k) : (ModularForm Γ' k) where
      toFun := f.toFun
      slash_action_eq' := by
        have hS := f.slash_action_eq'
        intro γ hΓ
        apply hS γ (by apply Subgroup.map_mono hGamma; apply hΓ)
      holo' := by
        apply f.holo'
      bdd_at_cusps' {c} hc := by
        have hC : IsCusp c (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) := by
          obtain ⟨g, hg, hgp, hgc⟩ := hc
          refine ⟨g, Subgroup.map_mono hGamma hg, hgp, hgc⟩
        exact f.bdd_at_cusps' hC

lemma cong_levl_map_eq_coe (k : ℤ) (Γ Γ' : Subgroup SL(2, ℤ)) (hGamma : Γ' ≤ Γ)
    (f : ModularForm Γ k) :
    (cong_levl_map k Γ Γ' hGamma f : UpperHalfPlane → ℂ) = f := rfl

abbrev cong_levl_Lin_map (k : ℤ) (Γ Γ' : Subgroup SL(2, ℤ)) (hGamma : Γ' ≤ Γ) :
    (ModularForm Γ k) →ₗ[ℂ] (ModularForm Γ' k) where
  toFun := fun f ↦ cong_levl_map k Γ Γ' hGamma f
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro s f
    rfl

lemma cong_levl_Lin_map_eq_coe (k : ℤ) (Γ Γ' : Subgroup SL(2, ℤ)) (hGamma : Γ' ≤ Γ)
    (f : ModularForm Γ k) :
    (cong_levl_Lin_map k Γ Γ' hGamma f : UpperHalfPlane → ℂ) = f := rfl

lemma cong_levl_Lin_map_injective (k : ℤ) (Γ Γ' : Subgroup SL(2, ℤ)) (hGamma : Γ' ≤ Γ) :
    Function.Injective (cong_levl_Lin_map k Γ Γ' hGamma) := by
    intro f g hfg
    ext z
    have hfg' := congr_fun (cong_levl_Lin_map_eq_coe k Γ Γ' hGamma f) z
    have hfg'' := congr_fun (cong_levl_Lin_map_eq_coe k Γ Γ' hGamma g) z
    rw [← hfg' , ← hfg'' ]
    grind



local notation "ℍₒ" => upperHalfPlaneSet

lemma mod_form_eq_iff (k : ℤ) (Γ : Subgroup SL(2, ℤ))
    (f1 : ModularForm Γ k) :
    (f1 = 0) ↔ ∀ z ∈ ℍₒ, (f1 ∘ ofComplex) z = 0 := by
    constructor
    · intro h
      rw [h]
      simp
    intro h
    ext z
    have H := h z z.2
    convert H
    simp

lemma mod_form_mul_eq_zero_iff (k1 k2 : ℤ) (Γ : Subgroup SL(2, ℤ))
    (f1 : ModularForm Γ k1) (f2 : ModularForm Γ k2) :
    (f1.mul f2 = 0) ↔ (f1 = 0) ∨ (f2 = 0) := by
    constructor
    · intro h
      have H1 := f1.holo'
      simp at H1
      suffices (∀ z ∈ ℍₒ, (f1 ∘ ofComplex) z = 0) ∨ (∀ z ∈ ℍₒ, (f2 ∘ ofComplex) z = 0) by
        rw [mod_form_eq_iff k1 Γ f1, mod_form_eq_iff k2 Γ f2]
        exact this
      have hA := AnalyticOnNhd.eq_zero_or_eq_zero_of_smul_eq_zero (U := ℍₒ) (f := f1 ∘ ofComplex)
        (g := f2 ∘ ofComplex)
      apply hA
      · intro z hz
        rw [Complex.analyticAt_iff_eventually_differentiableAt, eventually_iff_exists_mem]
        refine ⟨ℍₒ, by refine IsOpen.mem_nhds UpperHalfPlane.isOpen_upperHalfPlaneSet hz, ?_⟩
        intro y hy
        have H1 := f1.holo' ⟨y, hy⟩
        rw [mdifferentiableAt_iff] at H1
        simpa using H1
      · intro z hz
        rw [Complex.analyticAt_iff_eventually_differentiableAt, eventually_iff_exists_mem]
        refine ⟨ℍₒ, by refine IsOpen.mem_nhds UpperHalfPlane.isOpen_upperHalfPlaneSet hz, ?_⟩
        intro y hy
        have H2 := f2.holo' ⟨y, hy⟩
        rw [mdifferentiableAt_iff] at H2
        simpa using H2
      · rw [mod_form_eq_iff ] at h
        simpa using h
      · refine IsConnected.isPreconnected ?_
        have : ContractibleSpace ℍₒ := by
          apply (convex_halfSpace_im_gt 0).contractibleSpace ⟨Complex.I, by simp⟩
        have h0 : PathConnectedSpace ℍₒ := by
          exact ContractibleSpace.instPathConnectedSpace
        refine IsPathConnected.isConnected ?_
        exact isPathConnected_iff_pathConnectedSpace.mpr h0
    intro h
    rcases h with (h1 | h2)
    · rw [h1]
      ext z
      simp
    · rw [h2]
      ext z
      simp

def mod_form_norm_map (k : ℤ) (Γ Γ' : Subgroup SL(2, ℤ)) (hΓ : Γ ≤ Γ') (hΓ2 : Γ.relIndex Γ' ≠ 0)
    (f : ModularForm Γ k) : ℍ → ℂ :=  sorry--fun z => ∏ (g : (Γ' ⧸ (Γ.subgroupOf Γ'))) , f z := by sorry


lemma dim_full_levels (k : ℤ) (n : ℕ) (hn : NeZero n) :
    FiniteDimensional ℂ (ModularForm Γ(n) k) := by

  sorry

lemma dim_cong_levels (k : ℤ) (Γ : Subgroup SL(2, ℤ))
      (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) : FiniteDimensional ℂ (ModularForm Γ k) := by
    obtain ⟨N, hN⟩ := hΓ
    have := dim_full_levels k N (by refine { out := hN.1 })
    apply (FiniteDimensional.of_injective (cong_levl_Lin_map k Γ Γ(N) hN.2)
      (cong_levl_Lin_map_injective k Γ (CongruenceSubgroup.Gamma N) hN.2))
