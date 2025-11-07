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
theorem coordinateEmbedding₁₂_smooth (x : ℝ) : ContDiff ℝ ⊤ (coordinateEmbedding₁₂ x) := by
  -- The coordinate embedding is the sum of the two projections, which are both linear maps and hence continuously differentiable.
  have h_proj : ContDiff ℝ ⊤ (fun y : Euc(1) => !₂[x, ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ (y)]) := by
    -- The function !₂[x, y 0] is the sum of two continuously differentiable functions: the constant function x and the projection function y ↦ y 0.
    have h_sum : ContDiff ℝ ⊤ (fun y : Euc(1) => x) ∧ ContDiff ℝ ⊤ (fun y : Euc(1) => ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ y) := by
      exact ⟨ contDiff_const, ContinuousLinearEquiv.contDiff _ ⟩;
    aesop;
    -- The function !₂[x, y 0] can be written as the sum of the constant function x and the projection function y ↦ y 0.
    have h_sum : (fun y : Euc(1) => !₂[x, y 0]) = fun y : Euc(1) => x • ![1, 0] + y 0 • ![0, 1] := by
      -- To prove the equality of the two functions, we can show that they produce the same output for any input.
      funext y; simp [Pi.smul_apply, Pi.add_apply];
      ext i; fin_cases i <;> norm_num [ Algebra.smul_def ] ;
    exact h_sum.symm ▸ ContDiff.add ( ContDiff.smul contDiff_const contDiff_const ) ( ContDiff.smul right contDiff_const );
  -- Since the sum of two continuously differentiable functions is continuously differentiable, the coordinate embedding is continuously differentiable.
  convert h_proj using 1

def coordinateEmbedding₁₂_fderiv (x : ℝ) : Euc(1) →L[ℝ] Euc(2) where
  toFun := fun y => (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ y) • !₂[(0 : ℝ), 1]
  cont := by
    -- The function y ↦ y Inhabited.default • !₂[0, 1] is continuous because it is a product of continuous functions.
    apply Continuous.smul;
    · exact continuous_apply _;
    · -- The constant function !₂[0, 1] is continuous because it maps every element to the same value.
      apply continuous_const
  map_add' := by
    -- By definition of scalar multiplication in Euclidean space, we can expand both sides.
    simp [Pi.add_apply, add_smul]
  map_smul' := by
    -- By definition of scalar multiplication in Euclidean space, we can simplify the expression.
    simp [smul_smul]

/-- The Jacobian of `coordinateEmbedding₁₂ x` is the constant `!₂[0, 1]`. -/
theorem coordinateEmbedding₁₂_hasDerivAt (x : ℝ) (p : Euc(1)) :
    HasFDerivAt (𝕜 := ℝ) (coordinateEmbedding₁₂ x) (coordinateEmbedding₁₂_fderiv x) p := by
  -- The difference between the function and its linear approximation is zero, so the derivative exists and is equal to coordinateEmbedding₁₂_fderiv x.
  have h_diff_zero : ∀ y : Euc(1), coordinateEmbedding₁₂ x y - coordinateEmbedding₁₂ x p - coordinateEmbedding₁₂_fderiv x (y - p) = 0 := by
    intro y; ext i; fin_cases i <;> simp +decide [ SchwartzMap.coordinateEmbedding₁₂, SchwartzMap.coordinateEmbedding₁₂_fderiv ] ;
  rw [ hasFDerivAt_iff_tendsto ];
  aesop

theorem fderiv_coordinateEmbedding₁₂_hasTemperateGrowth (x : ℝ) :
    Function.HasTemperateGrowth (fderiv ℝ (coordinateEmbedding₁₂ x)) := by
  -- Since the derivative is a constant function, we can apply the theorem that states constant functions have temperate growth.
  have h_const : Function.HasTemperateGrowth (fun _ : Euc(1) => coordinateEmbedding₁₂_fderiv x) := by
    -- Apply the fact that constant functions have temperate growth.
    apply Function.HasTemperateGrowth.const;
  rw [ show fderiv ℝ ( SchwartzMap.coordinateEmbedding₁₂ x ) = _ from funext fun p => HasFDerivAt.fderiv ( coordinateEmbedding₁₂_hasDerivAt x p ) ] ; aesop

example {a b : ℝ} : 0 ≤ a → 0 ≤ b → (a ≤ b ↔ a ^ 2 ≤ b ^ 2) := by
  exact fun a_1 a_2 ↦ Iff.symm (sq_le_sq₀ a_1 a_2)

/-- `coordinateEmbedding₁₂` has temperate growth. -/
theorem coordinateEmbedding₁₂_hasTemperateGrowth (x : ℝ) :
    (coordinateEmbedding₁₂ x).HasTemperateGrowth := by
  -- Apply the theorem that states if the derivative of a function is temperate, then the function itself is temperate.
  have h_temperate : Function.HasTemperateGrowth (coordinateEmbedding₁₂ x) := by
    have h_deriv_temperate : Function.HasTemperateGrowth (fderiv ℝ (coordinateEmbedding₁₂ x)) := by
      exact fderiv_coordinateEmbedding₁₂_hasTemperateGrowth x
    -- Apply the theorem that states if the derivative of a function is temperate, then the function itself is temperate. Use `Function.HasTemperateGrowth.of_fderiv`.
    apply Function.HasTemperateGrowth.of_fderiv; assumption;
    -- The function `coordinateEmbedding₁₂ x` is differentiable because it is a linear map.
    have h_diff : Differentiable ℝ (coordinateEmbedding₁₂ x) := by
      exact fun y => (coordinateEmbedding₁₂_hasDerivAt x y).differentiableAt
    exact h_diff;
    case k => exact 1;
    simp [SchwartzMap.coordinateEmbedding₁₂];
    intro y; rw [ EuclideanSpace.norm_eq ] ; norm_num;
    case C => exact ( |x| + 1 );
    rw [ Real.sqrt_le_left ] <;> ring <;> norm_num [ EuclideanSpace.norm_eq ];
    · nlinarith [ abs_nonneg x, Real.sqrt_nonneg ( y 0 ^ 2 ), Real.mul_self_sqrt ( sq_nonneg ( y 0 ) ) ];
    · positivity;
  exact h_temperate

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
