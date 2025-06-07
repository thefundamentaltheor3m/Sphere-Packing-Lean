import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open SchwartzMap Function RCLike

section SchwartzMap_multidimensional_of_schwartzMap_real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma hasFDerivAt_norm_sq {x : F} :
  HasFDerivAt (fun x ↦ ‖x‖ ^ 2) (2 • ((innerSL ℝ) x)) x := (hasFDerivAt_id x).norm_sq

lemma differentiableAt_norm_sq {x : F} :
  DifferentiableAt ℝ (fun x ↦ ‖x‖ ^ 2) x := hasFDerivAt_norm_sq.differentiableAt

lemma differentiable_norm_sq :
  Differentiable ℝ (fun (x : F) ↦ ‖x‖ ^ 2) := fun _ => differentiableAt_norm_sq

lemma fderiv_norm_sq {x : F} :
  fderiv ℝ (fun x ↦ ‖x‖ ^ 2) x = 2 • ((innerSL ℝ) x) := hasFDerivAt_norm_sq.fderiv

lemma hasTemperateGrowth_norm_sq :
    HasTemperateGrowth (fun (x :F) ↦ ‖x‖ ^ 2) := by
  refine Function.HasTemperateGrowth.of_fderiv ?_ differentiable_norm_sq (k := 2) (C := 1) ?_
  · convert (2 • (innerSL ℝ)).hasTemperateGrowth
    ext
    simp [fderiv_norm_sq]
  · intro x
    rw [norm_pow, norm_norm, one_mul, sq_le_sq, abs_norm, abs_of_nonneg (by positivity)]
    linear_combination

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : 𝓢(ℝ, ℂ))

@[simps!]
noncomputable def schwartzMap_multidimensional_of_schwartzMap_real : 𝓢(F, ℂ) :=
    f.compCLM ℝ hasTemperateGrowth_norm_sq <| by
  use 1, 1
  intro _
  simp only [norm_pow, norm_norm]
  nlinarith

end SchwartzMap_multidimensional_of_schwartzMap_real

section SchwartzMap_multidimensional_of_schwartzLike_real

open Set

open scoped ContDiff

-- variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {g : ℝ → ℂ} (d : ℕ) (hContDiffOn : ContDiffOn ℝ ∞ g (Ici (0 : ℝ)))
  (hdecay : ∀ k n : ℕ, ∃ C : ℝ, ∀ x ∈ (Ici (0 : ℝ)), ‖x‖ ^ ((k : ℝ) / 2) *
    ‖iteratedFDerivWithin ℝ n g (Ici 0) x‖ ≤ C)

include hContDiffOn in
lemma ContDiffOn.comp_norm_sq_smooth :  -- More general version possible but for now unnecessary
    ContDiff ℝ ∞ (fun (x : EuclideanSpace ℝ (Fin d)) ↦ g (‖x‖ ^ 2)) :=
  hContDiffOn.comp_contDiff (contDiff_norm_sq ℝ) <| by simp

-- To match with `norm_iteratedFDerivWithin_comp_le`
local notation "f" => fun (x : EuclideanSpace ℝ (Fin d)) ↦ ‖x‖ ^ 2
local notation "s" => (⊤ : Set (EuclideanSpace ℝ (Fin d)))
local notation "t" => (Ici (0 : ℝ) : Set ℝ)

private lemma ht : UniqueDiffOn ℝ t := uniqueDiffOn_Ici 0
private lemma hs : UniqueDiffOn ℝ s := uniqueDiffOn_univ
private lemma hst : Set.MapsTo f s t := fun _ _ => by simp

private lemma hD (x : EuclideanSpace ℝ (Fin d)) (n : ℕ) : ∀ i : ℕ, 1 ≤ i → i ≤ n →
    ‖iteratedFDerivWithin ℝ i f s x‖ ≤ 2 ^ i := by
  have hnorm_eq (y : EuclideanSpace ℝ (Fin d)) : ‖y‖ ^ 2 = inner ℝ y y := by
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs, PiLp.inner_apply, inner_apply,
      conj_trivial]
    congr; ext; ring
  have hinner_eq_innerSL (a b : EuclideanSpace ℝ (Fin d)) : inner ℝ a b = innerSL ℝ a b := rfl
  intro i hi₁ hi₂
  rw [iteratedFDerivWithin_eq_iteratedFDeriv]
  · have h₁ : ContDiff ℝ ∞ (fun (x : EuclideanSpace ℝ (Fin d)) ↦ x) := contDiff_id
    simp only [hnorm_eq, hinner_eq_innerSL]
    have h₂ : ‖innerSL ℝ‖ ≤ 1 := norm_innerSL_le (E := EuclideanSpace ℝ (Fin d)) ℝ
    have h₃ : i ≤ ∞ := right_eq_inf.mp rfl
    have h₄ :=
      ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one (innerSL ℝ) h₁ h₁ x h₃ h₂
    apply h₄.trans
    have h₅ (j : ℕ) : ‖iteratedFDeriv ℝ j (fun (x : EuclideanSpace ℝ (Fin d)) ↦ x) x‖ = 1 := by
      -- Why is this not obvious?
      sorry
    simp only [h₅, mul_one]
    -- This isn't in the library?!
    sorry
  · exact uniqueDiffOn_univ
  · exact (contDiff_norm_sq ℝ).contDiffAt
  · trivial

private lemma h_pow (x : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    (‖x‖ ^ 2) ^ ((k : ℝ) / 2) = ‖x‖ ^ (k : ℝ) := by
  have h_pow_2 : ‖x‖ ^ 2 = ‖x‖ ^ (2 : ℝ) := by norm_cast
  rw [h_pow_2, ← Real.rpow_mul (by positivity)]
  field_simp

include hdecay in
private lemma hC (x : EuclideanSpace ℝ (Fin d)) (n k : ℕ) : ∃ C : ℝ, ∀ i ≤ n,
    (‖x‖ ^ k) * ‖iteratedFDerivWithin ℝ i g t (f x)‖ ≤ C := by
  -- I know that given some k, for all n, there is a Cₙ such that ‖deriv‖ ≤ Cₙ / (‖x‖ ^ (k / 2))
  -- Simply define C to be the max of all Cᵢ for 0 ≤ i ≤ n
  -- Copilot did the first few lines
  choose! C hC using hdecay k
  let Cmax := Finset.range (n + 1) |>.sup' (by simp) C
  use Cmax
  intro i hi
  specialize hC i (‖x‖ ^ 2)
  simp only [mem_Ici, norm_nonneg, pow_nonneg, norm_pow, norm_norm, forall_const, h_pow] at hC
  have hCi : C i ≤ Cmax := Finset.le_sup' C <| Finset.mem_range_succ_iff.mpr hi
  simp only
  have := hC.trans hCi
  norm_cast at this


noncomputable def schwartzMap_multidimensional_of_schwartzLike_real :
    𝓢(EuclideanSpace ℝ (Fin d), ℂ) where
  toFun := fun x ↦ g (f x)
  smooth' := hContDiffOn.comp_norm_sq_smooth d
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := hdecay k n
    use n.factorial * C * 2 ^ n
    intro x
    -- specialize hC (‖x‖ ^ 2)
    -- simp only [mem_Ici, norm_nonneg, pow_nonneg, norm_pow, norm_norm, forall_const] at hC
    -- rw [h_pow d x k, Real.rpow_natCast] at hC
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_univ]
    wlog hk_ne_zero : k ≠ 0
    · simp only [ne_eq, Decidable.not_not] at hk_ne_zero
      simp only [hk_ne_zero, pow_zero, one_mul] at hC ⊢

      sorry
    stop
    have hnorm_eq (y : EuclideanSpace ℝ (Fin d)) : ‖y‖ ^ 2 = inner ℝ y y := by
      simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs, PiLp.inner_apply, inner_apply,
        conj_trivial]
      congr; ext; ring
    have hrw : (fun (x : EuclideanSpace ℝ (Fin d)) ↦ g (‖x‖ ^ 2)) = (fun x ↦ g (inner ℝ x x)) := by
      ext x
      congr
      exact hnorm_eq x
    rw [hrw]
    have hbilin : ‖innerSL ℝ (E := EuclideanSpace ℝ (Fin d))‖ ≤ 1 := norm_innerSL_le ℝ
    have hinner_eq_innerSL (a b : EuclideanSpace ℝ (Fin d)) : inner ℝ a b = innerSL ℝ a b := rfl
    change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x ↦ g (innerSL ℝ x x)) x‖ ≤ ↑n.factorial * C * 2 ^ n

      sorry
    -- wlog hne_zero : x ≠ 0
    -- · simp only [ne_eq, Decidable.not_not] at hne_zero
    --   rw [hne_zero, norm_zero, zero_pow, zero_mul]
    --   sorry
    stop

    -- norm_iteratedFDeriv_comp_le hcontdiff (contDiff_norm_sq ℝ) (n := n) ?_ x ?_ ?_

    -- stop
    -- use C
    induction' n with n hn
    · simp only [norm_iteratedFDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero,
        mul_one]
      intro x
      simp only [mem_Ici, Real.norm_eq_abs, norm_iteratedFDeriv_zero] at hC

      specialize hC (‖x‖ ^ 2) (by positivity)
      simp only [abs_pow, abs_norm] at hC
      have h₁ : (‖x‖ ^ 2) ^ k = ‖x‖ ^ (2 * k) := by rw [pow_mul, pow_two]
      rw [h₁] at hC
      have h₂ : ‖x‖ ^ k ≤ ‖x‖ ^ (2 * k) := by
        -- gcongr
        sorry
      sorry
    · intro x
      simp only [← norm_fderiv_iteratedFDeriv] at hC ⊢
      sorry

-- example (n : ℕ) (x : F) : ‖iteratedFDeriv ℝ n (fun (v : F) ↦ ‖v‖^2) x‖ < 2 ^ n := by
--   sorry

example (n d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (h : ContDiffOn ℝ n g ⊤) :
    iteratedFDeriv ℝ n g x = iteratedFDerivWithin ℝ n g (⊤ : Set (EuclideanSpace ℝ (Fin d))) x :=
  Eq.symm (iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_univ (h x trivial) trivial)

#check ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one

end SchwartzMap_multidimensional_of_schwartzLike_real

section Scratch

namespace Scratch

-- Below is copy pasted from mathlib. Using it for scratch.

open scoped Nat NNReal ContDiff

/-- Composition with a function on the right is a continuous linear map on Schwartz space
provided that the function is temperate and growths polynomially near infinity. -/
def SchwartzMap.compCLM (𝕜 : Type) {D : Type} {E : Type} {F : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [RCLike 𝕜] [NormedAddCommGroup D]
  [NormedSpace ℝ D] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] {g : D → E} (hg : Function.HasTemperateGrowth g)
  (hg_upper : ∃ k C, ∀ (x : D), ‖x‖ ≤ C * (1 + ‖g x‖) ^ k) : 𝓢(E, F) →L[𝕜] 𝓢(D, F)
 := by
  refine mkCLM (fun f x => f (g x))
    (fun _ _ _ => by simp only [add_left_inj, Pi.add_apply, eq_self_iff_true]) (fun _ _ _ => rfl)
    (fun f => f.smooth'.comp hg.1) ?_
  rintro ⟨k, n⟩
  rcases hg.norm_iteratedFDeriv_le_uniform_aux n with ⟨l, C, hC, hgrowth⟩
  rcases hg_upper with ⟨kg, Cg, hg_upper'⟩
  have hCg : 1 ≤ 1 + Cg := by
    refine le_add_of_nonneg_right ?_
    specialize hg_upper' 0
    rw [norm_zero] at hg_upper'
    exact nonneg_of_mul_nonneg_left hg_upper' (by positivity)
  let k' := kg * (k + l * n)
  use Finset.Iic (k', n), (1 + Cg) ^ (k + l * n) * ((C + 1) ^ n * n ! * 2 ^ k'), by positivity
  intro f x
  let seminorm_f := ((Finset.Iic (k', n)).sup (schwartzSeminormFamily 𝕜 _ _)) f
  have hg_upper'' : (1 + ‖x‖) ^ (k + l * n) ≤ (1 + Cg) ^ (k + l * n) * (1 + ‖g x‖) ^ k' := by
    rw [pow_mul, ← mul_pow]
    gcongr
    rw [add_mul]
    refine add_le_add ?_ (hg_upper' x)
    nth_rw 1 [← one_mul (1 : ℝ)]
    gcongr
    apply one_le_pow₀
    simp only [le_add_iff_nonneg_right, norm_nonneg]
  have hbound (i) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i f (g x)‖ ≤ 2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k' := by
    have hpos : 0 < (1 + ‖g x‖) ^ k' := by positivity
    rw [le_div_iff₀' hpos]
    change i ≤ (k', n).snd at hi
    exact one_add_le_sup_seminorm_apply le_rfl hi _ _
  have hgrowth' (N : ℕ) (hN₁ : 1 ≤ N) (hN₂ : N ≤ n) :
      ‖iteratedFDeriv ℝ N g x‖ ≤ ((C + 1) * (1 + ‖x‖) ^ l) ^ N := by
    refine (hgrowth N hN₂ x).trans ?_
    rw [mul_pow]
    have hN₁' := (lt_of_lt_of_le zero_lt_one hN₁).ne'
    gcongr
    · exact le_trans (by simp [hC]) (le_self_pow₀ (by simp [hC]) hN₁')
    · refine le_self_pow₀ (one_le_pow₀ ?_) hN₁'
      simp only [le_add_iff_nonneg_right, norm_nonneg]
  have := norm_iteratedFDeriv_comp_le f.smooth' hg.1 (mod_cast le_top) x hbound hgrowth'
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (by simp only [zero_le_one, le_add_iff_nonneg_left]) _
  refine le_trans (mul_le_mul hxk this (by positivity) (by positivity)) ?_
  have rearrange :
    (1 + ‖x‖) ^ k *
        (n ! * (2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k') * ((C + 1) * (1 + ‖x‖) ^ l) ^ n) =
      (1 + ‖x‖) ^ (k + l * n) / (1 + ‖g x‖) ^ k' *
        ((C + 1) ^ n * n ! * 2 ^ k' * seminorm_f) := by
    rw [mul_pow, pow_add, ← pow_mul]
    ring
  rw [rearrange]
  have hgxk' : 0 < (1 + ‖g x‖) ^ k' := by positivity
  rw [← div_le_iff₀ hgxk'] at hg_upper''
  have hpos : (0 : ℝ) ≤ (C + 1) ^ n * n ! * 2 ^ k' * seminorm_f := by
    have : 0 ≤ seminorm_f := apply_nonneg _ _
    positivity
  refine le_trans (mul_le_mul_of_nonneg_right hg_upper'' hpos) ?_
  rw [← mul_assoc]
