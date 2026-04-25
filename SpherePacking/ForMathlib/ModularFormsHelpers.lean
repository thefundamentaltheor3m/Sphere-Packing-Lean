module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.NumberTheory.ModularForms.SlashActions


/-!
# Modular-form helpers (candidates for mathlib upstreaming)

Collected small lemmas about:
* `UpperHalfPlane.atImInfty` (filter of large imaginary part)
* `ModularGroup.S` action on `ℍ`
* Slash actions by `-1` / negated matrices in even weight
-/

@[expose] public section

open UpperHalfPlane ModularForm
open scoped MatrixGroups

/-! ### `atImInfty` -/

/-- Unfold `∀ᶠ z in UpperHalfPlane.atImInfty, p z` into an explicit bound on the imaginary part. -/
public lemma Filter.eventually_atImInfty {p : UpperHalfPlane → Prop} :
    (∀ᶠ x in UpperHalfPlane.atImInfty, p x) ↔
      ∃ A : ℝ, ∀ z : UpperHalfPlane, A ≤ z.im → p z :=
  UpperHalfPlane.atImInfty_mem (setOf p)

/-- The imaginary-part map `z ↦ z.im` tends to `∞` along the filter `UpperHalfPlane.atImInfty`. -/
public lemma Filter.tendsto_im_atImInfty :
    Tendsto (fun x : UpperHalfPlane ↦ x.im) UpperHalfPlane.atImInfty atTop := by
  simp [UpperHalfPlane.atImInfty, Filter.tendsto_iff_comap]

/-! ### `ModularGroup.S` action -/

/-- Coercion of the `S`-action on `ℍ`: `(S • z : ℂ) = -1 / z`. -/
public theorem ModularGroup.coe_S_smul (z : UpperHalfPlane) :
    (↑(S • z) : ℂ) = (-1 : ℂ) / (z : ℂ) := by
  simpa [div_eq_mul_inv] using congrArg UpperHalfPlane.coe (UpperHalfPlane.modular_S_smul (z := z))

/-- The `S` matrix squares to `-1` in `SL(2, ℤ)`. -/
@[simp] public theorem ModularGroup.modular_S_sq : S * S = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [S]

/-- Explicit matrix for `S * T` in `SL(2, ℤ)`. -/
@[simp] public theorem ModularGroup.S_mul_T :
    S * T = ⟨!![0, -1; 1, 1], by norm_num [Matrix.det_fin_two_of]⟩ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [S, T]

/-- Coercion of the `(S * T)`-action on `ℍ`: `((S * T) • z : ℂ) = -1 / (z + 1)`. -/
public theorem ModularGroup.coe_ST_smul (z : UpperHalfPlane) :
    (↑((S * T) • z) : ℂ) = (-1 : ℂ) / ((z : ℂ) + 1) := by
  simpa [ModularGroup.S_mul_T] using coe_specialLinearGroup_apply (g := S * T) (z := z)


/-! ### Slash actions by negated matrices in even weight -/

/-- Negating a matrix does not change the slash action for even weight (`SL(2, ℤ)` version). -/
@[simp] public theorem ModularForm.slash_neg' {k : ℤ} (g : SL(2, ℤ)) (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-g) = f ∣[k] g := by
  have : f ∣[k] (-1 : GL (Fin 2) ℝ) = f ∣[k] (1 : GL (Fin 2) ℝ) := by
    simp [slash_def, denom, hk.neg_one_zpow, Matrix.det_neg, σ]
  have hGL : ∀ g' : GL (Fin 2) ℝ, f ∣[k] (-g') = f ∣[k] g' := fun g' => by
    rw [← neg_one_mul, SlashAction.slash_mul, this, SlashAction.slash_one]
  simpa [SL_slash] using hGL (g : GL (Fin 2) ℝ)
