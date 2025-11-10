import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Real.CompleteField
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Tactic.Cases

import SpherePacking.ForMathlib.PoissonSummation.Zn_to_Euclidean

/-!
# Some Facts about Schwartz Functions

In this file, we prove some useful facts about Schwartz Functions. It is possible that some of them
apply to cases more general than just ℝ-vector spaces, but we do not worry about that here.

## Main Definitions
1. `linearEquiv_of_linearEquiv_domain` : Given a linear equivalence between finite-dimensional real
   vector spaces, composition with this equivalence gives a continuous linear equivalence
   between any two Schwartz spaces that have these equivalent spaces for a domain.
2. `SchwartzMap_one_of_SchwartzMap_two` : Given a Schwartz function in two variables, we can
   consider it as a Schwartz function in one variable by fixing a coordinate. The action of mapping
   the Schwartz function in two variables to the Schwartz function in one variable is continuous
   and linear.
-/

open SchwartzMap

open Real Complex BigOperators SchwartzMap Function PiLp
open LinearMap LinearEquiv ContinuousLinearEquiv ContinuousLinearMap

variable {E F H : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

-- In finite-dimensional spaces, any linear equivalence is a continuous linear equivalence.
noncomputable example (eq : E ≃ₗ[ℝ] H) : E ≃L[ℝ] H := eq.toContinuousLinearEquiv

namespace SchwartzMap

section Equivalence

/-- Given a linear equivalence between finite-dimensional real vector spaces, composition on the
left with this equivalence gives a continuous linear isomorphism between any two Schwartz spaces
that have these equivalent spaces for a domain. -/
noncomputable def linearEquiv_of_linearEquiv_domain (eq_l : E ≃ₗ[ℝ] H) : 𝓢(H, F) ≃L[ℝ] 𝓢(E, F) where
  toFun := compCLMOfContinuousLinearEquiv ℝ eq_l.toContinuousLinearEquiv
  invFun := compCLMOfContinuousLinearEquiv ℝ eq_l.symm.toContinuousLinearEquiv
  left_inv := by intro f; ext x; simp
  right_inv := by intro f; ext x; simp
  map_add' := (compCLMOfContinuousLinearEquiv ℝ eq_l.toContinuousLinearEquiv).map_add'
  map_smul' := (compCLMOfContinuousLinearEquiv ℝ eq_l.toContinuousLinearEquiv).map_smul'

end Equivalence

noncomputable section Inductive_Dimensions

/-!
In this section, we explore Schwartzness in the different variables of a multivariable Schwartz
function. The theory in this section would be necessary for an inductive proof of Poisson Summation
Formula over the canonical lattice `ℤ^n`, which is used to prove the result for other lattices.
-/

-- The key ingredient we use is the following.
-- #check SchwartzMap.compCLMOfAntilipschitz
-- We therefore construct a map from `Euc(1)` to `Euc(2)` that is antilipschitz and has temperate
-- growth. We inform our construction by the fact that the map we desire on the Schwartz spaces is
-- precisely given by composing with this map.

-- We begin by remarking that we can identify `Euc(1)` with `ℝ` continuously and linearly.
example : Euc(1) ≃L[ℝ] ℝ := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ

/-- The family of embeddings of `Euc(1)` into `Euc(2)` by fixing a coordinate, indexed by elements
of ℝ. The subscripts indicate it is an embedding of `Euc(1)` into `Euc(2)`. -/
def coordinateEmbedding₁₂ (x : ℝ) : Euc(1) → Euc(2) :=
  fun y => !₂[x, ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ (y)]

-- This was less trivial to prove than I thought... coordinates really are clunky!
/-- `coordinateEmbedding₁₂` is injective. -/
theorem coordinateEmbedding₁₂_injective (x : ℝ) : (coordinateEmbedding₁₂ x).Injective := by
  intro y₁ y₂ h
  simp only [coordinateEmbedding₁₂, coe_funUnique, eval, Fin.default_eq_zero, Fin.isValue] at h
  have : !₂[x, y₁ 0] 1 = !₂[x, y₂ 0] 1 := by rw [h]
  simp only [Fin.isValue] at this
  ext i
  rw [Fin.fin_one_eq_zero i]
  exact this

/-- `coordinateEmbedding₁₂` is smooth. -/
theorem coordinateEmbedding₁₂_smooth (x : ℝ) : ContDiff ℝ ⊤ (coordinateEmbedding₁₂ x) :=
by
  classical
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [coordinateEmbedding₁₂, Fin.isValue, Matrix.cons_val_zero]
      using (contDiff_const : ContDiff ℝ ⊤ (fun _ : Euc(1) => (x : ℝ)))
  · simpa [coordinateEmbedding₁₂, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        EuclideanSpace.proj, PiLp.proj]
      using ((EuclideanSpace.proj (ι := Fin 1) (𝕜 := ℝ) 0 : Euc(1) →L[ℝ] ℝ).contDiff)

-- We first show temperate growth.
-- #check Function.HasTemperateGrowth

-- We can use the following tool to show temperate growth.
-- #check Function.HasTemperateGrowth.of_fderiv

-- Note: We can probably do away with the `x` here as I doubt any of the proofs will need it.
/-- The Jacobian of `coordinateEmbedding₁₂ x` for all `x : ℝ`. -/
def coordinateEmbedding₁₂_fderiv (_ : ℝ) : Euc(1) →L[ℝ] Euc(2) :=
  -- Use the projection onto the unique coordinate and scale the fixed vector
  ContinuousLinearMap.smulRight
    (EuclideanSpace.proj (ι := Fin 1) (𝕜 := ℝ) 0 : Euc(1) →L[ℝ] ℝ)
    (!₂[(0 : ℝ), 1] : Euc(2))

/-- The Jacobian of `coordinateEmbedding₁₂ x` is the constant `!₂[0, 1]`. -/
theorem coordinateEmbedding₁₂_hasDerivAt (x : ℝ) (p : Euc(1)) :
    HasFDerivAt (𝕜 := ℝ) (coordinateEmbedding₁₂ x) (coordinateEmbedding₁₂_fderiv x) p := by
  classical
  have hlin :
      HasFDerivAt (fun y : Euc(1) => coordinateEmbedding₁₂_fderiv x y)
        (coordinateEmbedding₁₂_fderiv x) p :=
    ContinuousLinearMap.hasFDerivAt (coordinateEmbedding₁₂_fderiv x) (x := p)
  have hfd :
      HasFDerivAt
        (fun y : Euc(1) =>
          !₂[(x : ℝ), (0 : ℝ)] + coordinateEmbedding₁₂_fderiv x y)
        (coordinateEmbedding₁₂_fderiv x) p :=
    hlin.const_add (!₂[(x : ℝ), (0 : ℝ)] : Euc(2))
  have hpoint :
      (fun y : Euc(1) =>
          !₂[(x : ℝ), (0 : ℝ)] + coordinateEmbedding₁₂_fderiv x y)
        = coordinateEmbedding₁₂ x := by
    funext y
    ext i
    fin_cases i <;> simp [coordinateEmbedding₁₂, coordinateEmbedding₁₂_fderiv, Fin.isValue]
  exact hpoint ▸ hfd

-- We need to use the following to get an expression for the `fderiv` of `coordinateEmbedding₁₂ x`.
-- #check HasFDerivAt.fderiv

/-- The Jacobian of `coordinateEmbedding₁₂` has temperate growth. -/
theorem fderiv_coordinateEmbedding₁₂_hasTemperateGrowth (x : ℝ) :
    Function.HasTemperateGrowth (fderiv ℝ (coordinateEmbedding₁₂ x)) :=
by
  simpa [funext (fun p => by simpa using (coordinateEmbedding₁₂_hasDerivAt x p).fderiv)]
    using Function.HasTemperateGrowth.const (coordinateEmbedding₁₂_fderiv x)

example {a b : ℝ} : 0 ≤ a → 0 ≤ b → (a ≤ b ↔ a ^ 2 ≤ b ^ 2) := by
  exact fun a_1 a_2 ↦ Iff.symm (sq_le_sq₀ a_1 a_2)

/-- `coordinateEmbedding₁₂` has temperate growth. -/
theorem coordinateEmbedding₁₂_hasTemperateGrowth (x : ℝ) :
    (coordinateEmbedding₁₂ x).HasTemperateGrowth := by
  classical
  set c : Euc(2) := !₂[(x : ℝ), (0 : ℝ)]
  set L : Euc(1) →L[ℝ] Euc(2) := coordinateEmbedding₁₂_fderiv x
  set C : ℝ := ‖c‖ + ‖L‖
  refine Function.HasTemperateGrowth.of_fderiv
    (fderiv_coordinateEmbedding₁₂_hasTemperateGrowth x)
    ((coordinateEmbedding₁₂_smooth x).differentiable le_top) (k := 1) (C := C) ?_
  intro y
  have hpoint : coordinateEmbedding₁₂ x y = c + L y := by
    ext i
    fin_cases i <;> simp [coordinateEmbedding₁₂, coordinateEmbedding₁₂_fderiv, c, L, Fin.isValue]
  have hC_c : ‖c‖ ≤ C := le_add_of_nonneg_right (norm_nonneg _)
  have hC_L : ‖L‖ ≤ C := le_add_of_nonneg_left (norm_nonneg _)
  calc
    ‖coordinateEmbedding₁₂ x y‖
        = ‖c + L y‖ := by simp [hpoint]
    _ ≤ ‖c‖ + ‖L y‖ := norm_add_le _ _
    _ ≤ ‖c‖ + ‖L‖ * ‖y‖ := add_le_add_left (L.le_opNorm y) _
    _ ≤ C + C * ‖y‖ :=
          add_le_add hC_c (mul_le_mul_of_nonneg_right hC_L (norm_nonneg _))
    _ = C * (1 + ‖y‖) := by simp [C, mul_add]
    _ = C * (1 + ‖y‖) ^ (1 : ℕ) := by simp [pow_one]

-- Next, we show the antilipschitz condition. This is significantly easier.
-- #check AntilipschitzWith

/-- `coordinateEmbedding₁₂` is `AntilipschitzWith 1`. -/
theorem coordinateEmbedding₁₂_antiLipschitzWith (x : ℝ) :
    AntilipschitzWith 1 (coordinateEmbedding₁₂ x) := by
  intro a b
  simp only [ENNReal.coe_one, coordinateEmbedding₁₂, coe_funUnique, eval, Fin.default_eq_zero,
    Fin.isValue, one_mul, edist_dist]
  gcongr
  apply le_of_eq
  simp [dist_eq_sum]

/-- A Schwartz function in multiple variables is Schwartz in each variable. (2 variable case) -/
def SchwartzMap_one_of_SchwartzMap_two (x : ℝ) : 𝓢(Euc(2), ℂ) →L[ℝ] 𝓢(Euc(1), ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℝ
  (coordinateEmbedding₁₂_hasTemperateGrowth x)
    (coordinateEmbedding₁₂_antiLipschitzWith x)

end Inductive_Dimensions
end SchwartzMap
