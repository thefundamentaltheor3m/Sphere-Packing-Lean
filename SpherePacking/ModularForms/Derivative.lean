import SpherePacking.ModularForms.Eisenstein

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap

open scoped ModularForm MatrixGroups Manifold

/-!
Definition of (Serre) derivative of modular forms.
Prove Ramanujan's formulas on derivatives of Eisenstein series.
-/

noncomputable def D (F : ℍ → ℂ) : ℍ → ℂ :=
  fun (z : ℍ) => (2 * π * I)⁻¹ * ((deriv (F ∘ ofComplex)) z)

/--
TODO: Remove this or move this to somewhere more appropriate.
-/
lemma MDifferentiableAt_DifferentiableAt {F : ℍ → ℂ} {z : ℍ}
  (h : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F z) :
  DifferentiableAt ℂ (F ∘ ofComplex) ↑z := by
  have h₁ : DifferentiableWithinAt ℂ (F ∘ ofComplex) Set.univ ↑z :=
    by simpa [writtenInExtChartAt, extChartAt, Set.range_id] using
      MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt h
  exact (differentiableWithinAt_univ.1 h₁)


/--
TODO: Move this to E2.lean.
-/
theorem E₂_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E₂ := sorry

/--
Basic properties of derivatives: linearity, Leibniz rule, etc.
-/
@[simp]
theorem D_add (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) :
    D (F + G) = D F + D G := by
  ext z
  have h : deriv ((F ∘ ofComplex) + (G ∘ ofComplex)) z
      = deriv (F ∘ ofComplex) z + deriv (G ∘ ofComplex) z := by
    refine deriv_add ?_ ?_
    exact MDifferentiableAt_DifferentiableAt (hF z)
    exact MDifferentiableAt_DifferentiableAt (hG z)
  calc
    D (F + G) z
    _ = (2 * π * I)⁻¹ * deriv ((F ∘ ofComplex) + (G ∘ ofComplex)) z := by rfl
    _ = (2 * π * I)⁻¹ * (deriv (F ∘ ofComplex) z + deriv (G ∘ ofComplex) z)
      := by rw [h]
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z
        + (2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z
      := by simp [mul_add]
    _ = D F z + D G z := by rfl

@[simp]
theorem D_sub (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    : D (F - G) = D F - D G := by
  ext z
  have h : deriv ((F ∘ ofComplex) - (G ∘ ofComplex)) z
      = deriv (F ∘ ofComplex) z - deriv (G ∘ ofComplex) z := by
    refine deriv_sub ?_ ?_
    exact MDifferentiableAt_DifferentiableAt (hF z)
    exact MDifferentiableAt_DifferentiableAt (hG z)
  calc
    D (F - G) z
    _ = (2 * π * I)⁻¹ * deriv ((F ∘ ofComplex) - (G ∘ ofComplex)) z := by rfl
    _ = (2 * π * I)⁻¹ * (deriv (F ∘ ofComplex) z - deriv (G ∘ ofComplex) z)
      := by rw [h]
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z
        - (2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z
      := by ring_nf
    _ = D F z - D G z := by rfl

@[simp]
theorem D_smul (c : ℂ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    : D (c • F) = c • D F := by
  ext z
  have h : deriv (c • (F ∘ ofComplex)) z = c • deriv (F ∘ ofComplex) z :=
    deriv_const_mul c (MDifferentiableAt_DifferentiableAt (hF z))
  calc
    D (c • F) z
    _ = (2 * π * I)⁻¹ * deriv (c • (F ∘ ofComplex)) z := by rfl
    _ = (2 * π * I)⁻¹ * (c * deriv (F ∘ ofComplex) z) := by rw [h, smul_eq_mul]
    _ = c * ((2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z) := by ring_nf
    _ = c * D F z := by rfl

@[simp]
theorem D_mul (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    : D (F * G) = F * D G + D F * G := by
  ext z
  have h : deriv ((F ∘ ofComplex) * (G ∘ ofComplex)) z =
      F z * deriv (G ∘ ofComplex) z + deriv (F ∘ ofComplex) z * G z:= by
    have hFz := MDifferentiableAt_DifferentiableAt (hF z)
    have hGz := MDifferentiableAt_DifferentiableAt (hG z)
    sorry -- something with deriv_mul or deriv_smul
  calc
    D (F * G) z
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex * G ∘ ofComplex) z := by rfl
    _ = (2 * π * I)⁻¹ * (F z * deriv (G ∘ ofComplex) z + deriv (F ∘ ofComplex) z * G z)
      := by rw [h]
    _ = F z * ((2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z) +
        (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z * G z
      := by ring_nf
    _ = F z * D G z + D F z * G z := by rfl

@[simp]
theorem D_sq (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F):
    D (F ^ 2) = 2 * F * D F := by
  calc
    D (F ^ 2) = D (F * F) := by rw [pow_two]
    _ = F * D F + D F * F := by rw [D_mul F F hF hF]
    _ = 2 * F * D F := by ring_nf

@[simp]
theorem D_cube (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F):
    D (F ^ 3) = 3 * F ^ 2 * D F := by
  have hF2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F ^ 2) := by rw [pow_two]; exact MDifferentiable.mul hF hF
  calc
    D (F ^ 3) = D (F * F ^ 2) := by ring_nf
    _ = F * D (F ^ 2) + D F * F ^ 2 := by rw [D_mul F (F ^ 2) hF hF2]
    _ = F * (2 * F * D F) + D F * F ^ 2 := by rw [D_sq F hF]
    _ = 3 * F^2 * D F := by ring_nf

@[simp]
theorem D_const (c : ℂ) (z : ℍ) : D (Function.const _ c) z = 0 := by
  have h : deriv (Function.const _ c ∘ ofComplex) z = 0 := by
    have h' : Function.const _ c ∘ ofComplex = Function.const _ c := by rfl
    rw [h']
    exact deriv_const _ c
  calc
    D (Function.const _ c) z
    _ = (2 * π * I)⁻¹ * deriv (Function.const _ c ∘ ofComplex) z := by rfl
    _ = (2 * π * I)⁻¹ * 0 := by rw [h]
    _ = 0 := by ring_nf


/--
Serre derivative of weight `k`.
-/
noncomputable def serre_D (k : ℂ) : (ℍ → ℂ) → (ℍ → ℂ) :=
  fun (F : ℍ → ℂ) => (fun z => D F z - k * 12⁻¹ * E₂ z * F z)

/--
Basic properties of Serre derivative: linearity, Leibniz rule, etc.
-/
theorem serre_D_add (k : ℤ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) : serre_D k (F + G) = serre_D k F + serre_D k G := by
  ext z
  simp only [serre_D, Pi.add_apply, D_add F G hF hG]
  ring_nf

theorem serre_D_smul (k : ℤ) (c : ℂ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (z : ℍ) :
    serre_D k (c • F) z = c * serre_D k F z := by
  simp only [serre_D, D_smul c F hF]
  simp
  ring_nf

theorem serre_D_mul (k₁ k₂ : ℤ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (z : ℍ) :
    serre_D (k₁ + k₂) (F * G) z = F z * serre_D k₁ G z + G z * serre_D k₂ F z := by
  simp only [serre_D, D_mul F G hF hG]
  simp
  ring_nf


/--
Serre derivative is equivariant under the slash action. More precisely, if `F` is invariant
under the slash action of weight `k`, then `serre_D k F` is invariant under the slash action
of weight `k + 2`.
-/
theorem serre_D_slash_equivariant (k : ℤ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    ∀ γ : SL(2, ℤ), serre_D k F ∣[k + 2] γ = serre_D k (F ∣[k] γ) := by sorry

theorem serre_D_slash_invariant (k : ℤ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (γ : SL(2, ℤ)) (h : F ∣[k] γ = F) :
    serre_D k F ∣[k + 2] γ = serre_D k F := by
  rw [serre_D_slash_equivariant, h]
  exact hF

/--
Serre derivative of Eisenstein series. Use `serre_D_slash_invariant` and compare constant terms.
Note that the dimensions of the spaces of modular forms are all 1.
-/
theorem ramanujan_E₂' : serre_D 1 E₂ = - 12⁻¹ * E₄.toFun := by sorry

theorem ramanujan_E₄' : serre_D 4 E₄.toFun = - 3⁻¹ * E₆.toFun := by sorry

theorem ramanujan_E₆' : serre_D 6 E₆.toFun = - 2⁻¹ * E₄.toFun * E₄.toFun := by sorry

@[simp]
theorem ramanujan_E₂ : D E₂ = 12⁻¹ * (E₂ * E₂ - E₄.toFun) := by
  ext z
  have h := ramanujan_E₂'
  unfold serre_D at h
  have h1 := congrFun h z
  field_simp
  field_simp at h1
  simpa [add_comm, sub_eq_iff_eq_add] using h1

@[simp]
theorem ramanujan_E₄ : D E₄.toFun = 3⁻¹ * (E₂ * E₄.toFun - E₆.toFun) := by
  ext z
  have h := ramanujan_E₄'
  unfold serre_D at h
  have h1 := congrFun h z
  field_simp
  field_simp at h1
  ring_nf
  ring_nf at h1
  have hc : (12 : ℂ) ≠ 0 := by norm_num
  apply (mul_right_inj' hc).mp
  ring_nf
  simpa [add_comm, sub_eq_iff_eq_add] using h1

@[simp]
theorem ramanujan_E₆ : D E₆.toFun = 2⁻¹ * (E₂ * E₆.toFun - E₄.toFun * E₄.toFun) := by
  ext z
  have h := ramanujan_E₆'
  unfold serre_D at h
  have h1 := congrFun h z
  field_simp
  field_simp at h1
  ring_nf
  ring_nf at h1
  have hc : (12 : ℂ) ≠ 0 := by norm_num
  apply (mul_right_inj' hc).mp
  ring_nf
  simpa [add_comm, sub_eq_iff_eq_add] using h1


/--
Prove modular linear differential equation satisfied by $F$.
-/
noncomputable def X₄₂ := 288⁻¹ * (E₄.toFun - E₂ * E₂)

noncomputable def Δ_fun := 1728⁻¹ * (E₄.toFun ^ 3 - E₆.toFun ^ 2)

noncomputable def F := (E₂ * E₄.toFun - E₆.toFun) ^ 2

theorem F_aux : D F = 5 * 6⁻¹ * E₂ ^ 3 * E₄.toFun ^ 2 - 5 * 2⁻¹ * E₂ ^ 2 * E₄.toFun * E₆.toFun
    + 5 * 6⁻¹ * E₂ * E₄.toFun ^ 3 + 5 * 3⁻¹ * E₂ * E₆.toFun ^ 2 - 5 * 6⁻¹ * E₄.toFun^2 * E₆.toFun := by
  rw [F, D_sq, D_sub, D_mul]
  ring_nf
  rw [ramanujan_E₂, ramanujan_E₄, ramanujan_E₆]
  ext z
  simp
  ring_nf

  -- Holomorphicity of the terms
  · exact E₂_holo'
  · exact E₄.holo'
  · exact MDifferentiable.mul E₂_holo' E₄.holo'
  · exact E₆.holo'
  have h24 := MDifferentiable.mul E₂_holo' E₄.holo'
  exact MDifferentiable.sub h24 E₆.holo'


/--
Modular linear differential equation satisfied by `F`.
TODO: Move this to a more appropriate place.
-/
theorem MLDE_F : serre_D 12 (serre_D 10 F) = 5 * 6⁻¹ * F + 172800 * Δ_fun * X₄₂ := by
  ext x
  rw [X₄₂, Δ_fun, serre_D, serre_D, F_aux]
  unfold serre_D
  rw [F_aux]
  sorry

example : D (E₄.toFun * E₄.toFun) = 2 * 3⁻¹ * E₄.toFun * (E₂ * E₄.toFun - E₆.toFun) :=
  by
  rw [D_mul E₄.toFun E₄.toFun]
  simp only [ramanujan_E₄]
  ring_nf
  exact E₄.holo'
  exact E₄.holo'
