/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import Mathlib

-- TODO: run #min_imports once file completed
import Mathlib.Analysis.Distribution.SchwartzSpace

open scoped Nat NNReal ContDiff

variable {𝕜 𝕜' D E F G V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

section TemperateGrowthOn

def Function.HasTemperateGrowthOn (f : E → F) (S : Set E) : Prop :=
  ContDiffOn ℝ ∞ f S ∧
  ∀ n : ℕ, ∃ (k : ℕ) (C : ℝ), ∀ x ∈ S, ‖iteratedFDeriv ℝ n f x‖ ≤ C * (1 + ‖x‖) ^ k

theorem Function.HasTemperateGrowthOn.norm_iteratedFDeriv_le_uniform_aux {f : E → F} {S : Set E}
    (hf_temperate : f.HasTemperateGrowthOn S) (n : ℕ) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ N ≤ n, ∀ x ∈ S, ‖iteratedFDeriv ℝ N f x‖ ≤ C * (1 + ‖x‖) ^ k := by
  choose k C hf using hf_temperate.2
  use (Finset.range (n + 1)).sup k
  let C' := max (0 : ℝ) ((Finset.range (n + 1)).sup' (by simp) C)
  have hC' : 0 ≤ C' := le_max_left _ _
  use C', hC'
  intro N hN x hx
  rw [← Finset.mem_range_succ_iff] at hN
  grw [hf]
  gcongr
  · simp only [C', Finset.le_sup'_iff, le_max_iff]
    right
    exact ⟨N, hN, le_rfl⟩
  · simp
  · exact Finset.le_sup hN
  · exact hx

end TemperateGrowthOn

section Even

/-! Let's try proving smoothness here. First, a famous result of Whitney: https://projecteuclid.org/journals/duke-mathematical-journal/volume-10/issue-1/Differentiable-even-functions/10.1215/S0012-7094-43-01015-4.full -/

open Function Real
open Filter

variable {f : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ f) (heven : f.Even)

example (x : ℝ) : √(x ^ 2) = |x| := sqrt_sq_eq_abs x

include heven in
lemma Function.Even.comp_abs : f = f ∘ abs := by
  ext x; by_cases hx : x ≥ 0
  · congr; exact (abs_of_nonneg hx).symm
  · rw [ge_iff_le, not_le] at hx
    rw [comp_apply, abs_of_neg hx]
    exact (heven x).symm

include heven in
lemma Function.Even.comp_abs_apply (x : ℝ) : f x = f |x| := by
  conv_lhs => rw [heven.comp_abs]
  rw [comp_apply]

include heven in
lemma Function.Even.HasDeriv_at_zero : deriv f (0 : ℝ) = 0 := by
  wlog hdiff : DifferentiableAt ℝ f 0
  · rw [← differentiableWithinAt_univ] at hdiff
    rw [deriv, fderiv, fderivWithin]
    simp [hdiff]
  -- simp
  suffices deriv f 0 = -deriv f 0 by linarith
  -- apply HasDerivAt.deriv
  -- rw [hasDerivAt_iff_tendsto_slope_zero]
  -- have hHasDerivAt : HasDerivAt f (deriv f 0) 0 := hdiff.hasDerivAt
  have hrw {t : ℝ} : f (-t) - f 0 = f t - f 0 := by rw [heven]
  have hlim₁ : Tendsto (fun t ↦ t⁻¹ • (f (0 + t) - f 0)) (nhdsWithin 0 {0}ᶜ) (nhds (deriv f 0)) :=
    hasDerivAt_iff_tendsto_slope_zero.mp hdiff.hasDerivAt
  simp only [zero_add, smul_eq_mul] at hlim₁
  have hlim₂ : Tendsto (fun t ↦ -((t)⁻¹ * (f t - f 0))) (nhdsWithin 0 {0}ᶜ) (nhds (-deriv f 0)) :=
    hlim₁.neg
  -- do tendsto comp or something - use fact that x ↦ -x tends to 0 as you go to 0 or smth
  sorry

/-
*****************  New Aristotle Proofs ***********************
-/

/-
If $\phi$ is a smooth compactly supported bump function, then for any $k < n$, the $k$-th derivative of $x^n \phi(u x)$ tends to 0 uniformly as $u \to \infty$.
-/
set_option linter.style.longLine false in
lemma smooth_bump_scaling_bound (ϕ : ℝ → ℝ) (hϕ : ContDiff ℝ ∞ ϕ) (hsupp : HasCompactSupport ϕ)
    (n k : ℕ) (hk : k < n) :
    ∀ ε > 0, ∃ R, ∀ u ≥ R, ∀ x, |iteratedDeriv k (fun x => x^n * ϕ (u * x)) x| ≤ ε := by
      intro ε ε_pos
      have fwd_1 := le_of_lt hk  -- todo: remove
      -- Using the Leibniz rule, we can express the $k$-th derivative of $x^n \phi(u x)$ as a sum of terms involving derivatives of $x^n$ and $\phi(u x)$.
      have h_leibniz : ∀ u x, iteratedDeriv k (fun x => x ^ n * (ϕ (u * x))) x = ∑ j ∈ Finset.range (k + 1), Nat.choose k j * (Nat.descFactorial n (k - j)) * x ^ (n - (k - j)) * u ^ j * (iteratedDeriv j ϕ) (u * x) := by
        have h_leibniz : ∀ u x, iteratedDeriv k (fun x => x ^ n * (ϕ (u * x))) x = ∑ j ∈ Finset.range (k + 1), Nat.choose k j * iteratedDeriv (k - j) (fun x => x ^ n) x * iteratedDeriv j (fun x => ϕ (u * x)) x := by
          intro u x;
          -- Apply the Leibniz rule for the $k$-th derivative of a product.
          have h_leibniz : ∀ (f g : ℝ → ℝ), ContDiff ℝ ∞ f → ContDiff ℝ ∞ g → ∀ k : ℕ, iteratedDeriv k (fun x => f x * g x) = fun x => ∑ j ∈ Finset.range (k + 1), Nat.choose k j * iteratedDeriv (k - j) f x * iteratedDeriv j g x := by
            intro f g hf hg k; induction' k with k ih generalizing f g <;> simp_all +decide [ iteratedDeriv_succ ] ;
            -- Apply the product rule to each term in the sum.
            have h_prod_rule : ∀ x, deriv (fun x => ∑ j ∈ Finset.range (k + 1), Nat.choose k j * iteratedDeriv (k - j) f x * iteratedDeriv j g x) x =
              ∑ j ∈ Finset.range (k + 1), Nat.choose k j * deriv (fun x => iteratedDeriv (k - j) f x) x * iteratedDeriv j g x +
              ∑ j ∈ Finset.range (k + 1), Nat.choose k j * iteratedDeriv (k - j) f x * deriv (fun x => iteratedDeriv j g x) x := by
                -- Apply the linearity of the derivative and the product rule to each term in the sum.
                intros x
                have h_deriv_term : ∀ j ∈ Finset.range (k + 1), deriv (fun x => (Nat.choose k j) * iteratedDeriv (k - j) f x * iteratedDeriv j g x) x =
                  (Nat.choose k j) * deriv (fun x => iteratedDeriv (k - j) f x) x * iteratedDeriv j g x +
                  (Nat.choose k j) * iteratedDeriv (k - j) f x * deriv (fun x => iteratedDeriv j g x) x := by
                    -- Apply the product rule to each term in the sum using the fact that the iterated derivatives of $f$ and $g$ are differentiable.
                    intros j hj
                    have h_diff : DifferentiableAt ℝ (fun x => iteratedDeriv (k - j) f x) x ∧ DifferentiableAt ℝ (fun x => iteratedDeriv j g x) x := by
                      constructor;
                      · apply_rules [ ContDiff.differentiable_iteratedDeriv, hf ];
                        exact compareOfLessAndEq_eq_lt.mp rfl
                      · apply_rules [ ContDiff.differentiable_iteratedDeriv, hg ];
                        exact compareOfLessAndEq_eq_lt.mp rfl
                    norm_num [ h_diff.1, h_diff.2, mul_assoc ];
                    ring;
                -- Apply the linearity of the derivative to the sum.
                have h_deriv_sum : deriv (fun x => ∑ j ∈ Finset.range (k + 1), (Nat.choose k j) * iteratedDeriv (k - j) f x * iteratedDeriv j g x) x = ∑ j ∈ Finset.range (k + 1), deriv (fun x => (Nat.choose k j) * iteratedDeriv (k - j) f x * iteratedDeriv j g x) x := by
                  -- Since each term in the sum is differentiable, we can apply the linearity of the derivative.
                  have h_diff : ∀ j ∈ Finset.range (k + 1), DifferentiableAt ℝ (fun x => (Nat.choose k j) * iteratedDeriv (k - j) f x * iteratedDeriv j g x) x := by
                    intro j hj; apply_rules [ DifferentiableAt.mul, DifferentiableAt.pow, differentiableAt_id, differentiableAt_const ] ;
                    · apply_rules [ ContDiff.differentiable_iteratedDeriv, hf ];
                      exact compareOfLessAndEq_eq_lt.mp rfl
                    · apply_rules [ ContDiff.differentiable_iteratedDeriv, hf, hg ];
                      exact compareOfLessAndEq_eq_lt.mp rfl
                  exact deriv_fun_sum h_diff
                rw [ h_deriv_sum, ← Finset.sum_add_distrib, Finset.sum_congr rfl h_deriv_term ];
            -- Apply the induction hypothesis to rewrite the derivatives of the iterated derivatives.
            have h_ind : ∀ x, ∑ j ∈ Finset.range (k + 1), Nat.choose k j * deriv (fun x => iteratedDeriv (k - j) f x) x * iteratedDeriv j g x +
                           ∑ j ∈ Finset.range (k + 1), Nat.choose k j * iteratedDeriv (k - j) f x * deriv (fun x => iteratedDeriv j g x) x =
                           ∑ j ∈ Finset.range (k + 1), Nat.choose k j * iteratedDeriv (k + 1 - j) f x * iteratedDeriv j g x +
                           ∑ j ∈ Finset.range (k + 1), Nat.choose k j * iteratedDeriv (k - j) f x * iteratedDeriv (j + 1) g x := by
                             intro x; congr! 2; rw [ Nat.sub_add_comm ( Nat.le_of_lt_succ <| Finset.mem_range.mp <| by assumption ) ] ; simp +decide [ iteratedDeriv_succ ] ; ring;
                             rw [ add_comm, iteratedDeriv_succ ];
            ext x; rw [ h_prod_rule, h_ind ] ; rw [ Finset.sum_range_succ' ] ;
            simp +decide only [Nat.reduceSubDiff, Nat.choose_zero_right, Nat.cast_one, tsub_zero,
              one_mul, iteratedDeriv_zero] ;
            ring;
            rw [ show 2 + k = 1 + k + 1 by ring, Finset.sum_range_succ' ] ;
            simp +decide only [add_comm, Finset.sum_range_succ, Nat.choose_self, Nat.cast_one,
              tsub_self, iteratedDeriv_zero, one_mul, add_left_comm, add_assoc, Nat.reduceSubDiff,
              Nat.choose_zero_right, tsub_zero, add_right_inj] ;
            ring;
            rw [ ← Finset.sum_add_distrib ] ;
            apply Finset.sum_congr
            · rfl
            · intro i hi
              rw [ Nat.add_comm 1 k, Nat.add_comm 1 i ] ; rw [ Nat.choose_succ_succ ]
              ring
              norm_num [ Nat.choose_succ_succ, add_comm 1 i ] ; ring;
          exact congr_fun ( h_leibniz _ _ ( contDiff_id.pow _ ) ( hϕ.comp ( contDiff_const.mul contDiff_id ) ) _ ) _;
        intro u x; rw [ h_leibniz u x ] ;
        apply Finset.sum_congr
        · rfl
        intro j hj
        simp only [iteratedDeriv_eq_iterate, iter_deriv_pow', mul_comm, mul_left_comm,
            mul_assoc];
        -- By definition of iterated derivative, we know that
        have h_iter_deriv : ∀ j : ℕ, deriv^[j] (fun x => ϕ (u * x)) = fun x => u ^ j * deriv^[j] ϕ (u * x) := by
          intro j; induction j <;> simp_all +decide [ Function.iterate_succ_apply', pow_succ', mul_assoc, mul_comm u ] ;
          ext x; erw [ deriv_comp ] <;> norm_num [ mul_comm u ] ; ring;
          apply_rules [ ContDiff.differentiable ];
          apply_rules [ ContDiff.iterate_deriv ];
          decide +revert;
        simp +decide only [h_iter_deriv, mul_left_comm, Nat.descFactorial_eq_prod_range,
          Nat.cast_prod, mul_eq_mul_left_iff, mul_eq_mul_right_iff, Nat.cast_eq_zero,
          pow_eq_zero_iff', ne_eq];
        exact Or.inl <| Or.inl <| Or.inl <| Or.inl <| Finset.prod_congr rfl fun i hi => by rw [ Nat.cast_sub <| by linarith [ Finset.mem_range.mp hj, Finset.mem_range.mp hi, Nat.sub_le k j ] ] ;
      -- Since $\phi$ has compact support, there exists $M > 0$ such that $\phi^{(j)}(x) = 0$ for $|x| > M$.
      obtain ⟨M, hM⟩ : ∃ M > 0, ∀ x, abs x > M → ∀ j ≤ k, iteratedDeriv j ϕ x = 0 := by
        -- Since $\phi$ has compact support, there exists $M > 0$ such that $\phi(x) = 0$ for $|x| > M$.
        obtain ⟨M, hM⟩ : ∃ M > 0, ∀ x, abs x > M → ϕ x = 0 := by
          have := hsupp.isCompact.isBounded.exists_pos_norm_le;
          simp_all only [gt_iff_lt, norm_eq_abs]
          obtain ⟨w, h⟩ := this
          obtain ⟨left, right⟩ := h
          exact ⟨ w, left, fun x hx => Classical.not_not.1 fun hx' => hx.not_ge <| right x <| subset_closure <| by aesop ⟩;
        use M
        constructor
        · exact hM.1
        · intro x hx j hj
          induction' j with j ih generalizing x
          · simp_all only [gt_iff_lt, zero_le, iteratedDeriv_zero]
          · simp_all only [gt_iff_lt, iteratedDeriv_succ]
            exact HasDerivAt.deriv ( HasDerivAt.congr_of_eventuallyEq ( hasDerivAt_const _ _ ) ( Filter.eventuallyEq_of_mem ( IsOpen.mem_nhds ( isOpen_lt     continuous_const continuous_abs ) hx ) fun y hy => ih y hy ( by linarith ) ) );
      -- For $|u x| \leq M$, we have $|x^{n-k+j} u^j| \leq (M/u)^{n-k+j} u^j = M^{n-k+j} u^{-(n-k)}$.
      have h_bound : ∀ u ≥ 1, ∀ x, abs (u * x) ≤ M → ∀ j ≤ k, abs (x ^ (n - (k - j)) * u ^ j) ≤ M ^ (n - (k - j)) * u ^ (-(n - k) : ℤ) := by
        intros u hu x hx j hj
        have h_abs : abs (x ^ (n - (k - j)) * u ^ j) ≤ (M / u) ^ (n - (k - j)) * u ^ j := by
          rw [ abs_mul, abs_pow, abs_of_nonneg ( by positivity : 0 ≤ u ^ j ) ];
          exact mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( abs_nonneg x ) ( by rw [ le_div_iff₀ ( by positivity ) ] ; cases abs_cases x <;> cases abs_cases ( u * x ) <;> nlinarith ) _ ) ( by positivity );
        convert h_abs using 1 ; norm_cast ; norm_num ; ring;
        rw [ tsub_tsub_assoc fwd_1 hj ] ;
        rw [ mul_assoc ]
        congr
        rw [mul_comm, inv_pow, inv_pow]
        rw [← inv_pow_sub_of_lt u (Nat.lt_add_of_pos_left (Nat.zero_lt_sub_of_lt hk)), ←inv_pow]
        exact congrArg (HPow.hPow u⁻¹) (Nat.add_sub_self_right (n - k) j).symm

      -- Since $\phi^{(j)}$ is bounded (since it is smooth and compactly supported), say by $B_j$, we can bound each term in the sum.
      obtain ⟨B, hB⟩ : ∃ B > 0, ∀ j ≤ k, ∀ x, abs (iteratedDeriv j ϕ x) ≤ B := by
        -- Since $\phi$ is smooth and compactly supported, its derivatives are also compactly supported.
        have h_deriv_compact_support : ∀ j ≤ k, HasCompactSupport (iteratedDeriv j ϕ) := by
          intro j hj;
          rw [ hasCompactSupport_iff_eventuallyEq ] at *;
          simp_all +decide only [EventuallyEq, Pi.zero_apply, coclosedCompact_eq_cocompact,
            cocompact_eq_atBot_atTop, eventually_sup, eventually_atBot, eventually_atTop, ge_iff_le,
            gt_iff_lt, abs_mul, abs_pow, neg_sub];
          exact ⟨ ⟨ -M - 1, fun x hx => hM.2 x ( by cases abs_cases x <;> linarith ) j hj ⟩, ⟨ M + 1, fun x hx => hM.2 x ( by cases abs_cases x <;> linarith ) j hj ⟩ ⟩;
        -- Since $\phi^{(j)}$ is compactly supported, it is bounded.
        have h_deriv_bounded : ∀ j ≤ k, ∃ B > 0, ∀ x, abs (iteratedDeriv j ϕ x) ≤ B := by
          intro j hj; specialize h_deriv_compact_support j hj;
          have := h_deriv_compact_support.exists_bound_of_continuous ( show Continuous ( iteratedDeriv j ϕ ) from ?_ ) ;
          simp_all only [gt_iff_lt, ge_iff_le, abs_mul, abs_pow, neg_sub, Real.norm_eq_abs]
          obtain ⟨w, h⟩ := this
          · exact ⟨ Max.max w 1, by positivity, fun x => le_trans ( h x ) ( le_max_left _ _ ) ⟩;
          · apply_rules [ ContDiff.continuous_iteratedDeriv, hϕ ];
            -- Since $j$ is a natural number, we have $j \leq \infty$.
            norm_cast;
            norm_num;
        choose! B hB₁ hB₂ using h_deriv_bounded;
        exact ⟨ ∑ j ∈ Finset.range ( k + 1 ), B j, Finset.sum_pos ( fun j hj => hB₁ j ( Finset.mem_range_succ_iff.mp hj ) ) ( by norm_num ), fun j hj x => le_trans ( hB₂ j hj x ) ( Finset.single_le_sum ( fun j _ => le_of_lt ( hB₁ j ( Finset.mem_range_succ_iff.mp ‹_› ) ) ) ( Finset.mem_range_succ_iff.mpr hj ) ) ⟩;
      -- Using the bounds from h_bound and hB, we can bound the sum.
      have h_sum_bound : ∀ u ≥ 1, ∀ x, abs (iteratedDeriv k (fun x => x ^ n * (ϕ (u * x))) x) ≤ ∑ j ∈ Finset.range (k + 1), Nat.choose k j * Nat.descFactorial n (k - j) * M ^ (n - (k - j)) * u ^ (-(n - k) : ℤ) * B := by
        intros u hu x
        rw [h_leibniz u x];
        -- refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) _;
        apply le_trans ( Finset.abs_sum_le_sum_abs _ _ ) _;
        -- Apply the bounds from h_bound and hB to each term in the sum.
        have h_term_bound : ∀ j ≤ k, abs (Nat.choose k j * Nat.descFactorial n (k - j) * x ^ (n - (k - j)) * u ^ j * iteratedDeriv j ϕ (u * x)) ≤ Nat.choose k j * Nat.descFactorial n (k - j) * M ^ (n - (k - j)) * u ^ (-(n - k) : ℤ) * B := by
          intro j hj
          by_cases h_abs : abs (u * x) ≤ M;
          · simp_all +decide only [gt_iff_lt, mul_assoc, ge_iff_le, abs_mul, abs_pow, neg_sub,
              Nat.abs_cast];
            exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( by nlinarith [ h_bound u hu x h_abs j hj, hB.2 j hj ( u * x ), show 0 ≤ |x| ^ ( n - ( k - j ) ) * |u| ^ j by positivity, show 0 ≤ M ^ ( n - ( k - j ) ) * u ^ ( ( k : ℤ ) - n ) by exact mul_nonneg ( pow_nonneg hM.1.le _ ) ( by positivity ) ] ) ( Nat.cast_nonneg _ ) ) ( Nat.cast_nonneg _ );
          · obtain left := hM.1
            simp_all only [gt_iff_lt, ge_iff_le, abs_mul, abs_pow, neg_sub, not_le, mul_zero, abs_zero,mul_nonneg_iff_of_pos_right]
            positivity;
        exact Finset.sum_le_sum fun i hi => h_term_bound i <| Finset.mem_range_succ_iff.mp hi;
      -- Since $u^{-(n-k)}$ tends to $0$ as $u \to \infty$, we can choose $R$ large enough such that the sum is less than $\epsilon$.
      have h_lim : Filter.Tendsto (fun u : ℝ => ∑ j ∈ Finset.range (k + 1), Nat.choose k j * Nat.descFactorial n (k - j) * M ^ (n - (k - j)) * u ^ (-(n - k) : ℤ) * B) Filter.atTop (nhds 0) := by
        norm_num [ ← Finset.sum_mul _ _ _ ];
        exact le_trans ( Filter.Tendsto.mul ( Filter.Tendsto.mul tendsto_const_nhds <| tendsto_zpow_atTop_zero <| by linarith ) tendsto_const_nhds ) <| by norm_num;
      exact Filter.eventually_atTop.mp ( h_lim.eventually ( ge_mem_nhds ε_pos ) ) |> fun ⟨ R, hR ⟩ ↦ ⟨ Max.max R 1, fun u hu x ↦ le_trans ( h_sum_bound u ( le_trans ( le_max_right _ _ ) hu ) x ) ( hR u ( le_trans ( le_max_left _ _ ) hu ) ) ⟩

/-
For any $n, c, \epsilon$, there exists a smooth compactly supported function whose $n$-th derivative at 0 is $c$ (and others 0) and whose derivatives of order less than $n$ are bounded by $\epsilon$.
-/
set_option linter.style.longLine false in
lemma exists_smooth_term_with_bound (n : ℕ) (c : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (∀ k, iteratedDeriv k f 0 = if k = n then c else 0) ∧
    (∀ k < n, ∀ x, |iteratedDeriv k f x| ≤ ε) := by
      -- Let's choose a smooth bump function $\phi$ such that $\phi(x) = 1$ for $|x| \leq 1$ and $\phi(x) = 0$ for $|x| \geq 2$.
      obtain ⟨ϕ, hϕ⟩ : ∃ ϕ : ℝ → ℝ, ContDiff ℝ ∞ ϕ ∧ HasCompactSupport ϕ ∧ (∀ x, |x| ≤ 1 → ϕ x = 1) ∧ (∀ x, |x| ≥ 2 → ϕ x = 0) := by
        -- Apply the existence of smooth bump functions.
        obtain ⟨ϕ, hϕ⟩ : ∃ ϕ : ℝ → ℝ, ContDiff ℝ ∞ ϕ ∧ (∀ x, |x| ≤ 1 → ϕ x = 1) ∧ (∀ x, |x| ≥ 2 → ϕ x = 0) := by
          have := @exists_smooth_zero_one_of_isClosed;
          specialize this ( modelWithCornersSelf ℝ ℝ ) ( show IsClosed ( { x : ℝ | |x| ≥ 2 } ) from isClosed_le continuous_const <| continuous_abs ) ( show IsClosed ( { x : ℝ | |x| ≤ 1 } ) from isClosed_le continuous_abs continuous_const ) ( by exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ hx₁.out, hx₂.out ] );
          bound;
          exact ⟨ w, w.contMDiff.contDiff, fun x hx => left_1 hx, fun x hx => left hx ⟩;
        use ϕ;
        rw [ hasCompactSupport_iff_eventuallyEq ];
        simp_all only [ge_iff_le, EventuallyEq, Pi.zero_apply, coclosedCompact_eq_cocompact,
          cocompact_eq_atBot_atTop, eventually_sup, eventually_atBot, eventually_atTop,
          implies_true, and_self, and_true, true_and];
        exact ⟨ ⟨ -2, fun x hx => hϕ.2.2 x <| by cases abs_cases x <;> linarith ⟩, ⟨ 2, fun x hx => hϕ.2.2 x <| by cases abs_cases x <;> linarith ⟩ ⟩;
      -- Define the function $f_u(x) = \frac{c}{n!} x^n \phi(u x)$ for some large $u$.
      obtain ⟨u, hu⟩ : ∃ u : ℝ, 0 < u ∧ (∀ k < n, ∀ x, |iteratedDeriv k (fun x => (c / n.factorial) * x^n * ϕ (u * x)) x| ≤ ε) := by
        have h_smooth_bump_scaling_bound : ∀ k < n, ∃ R, ∀ u ≥ R, ∀ x, |iteratedDeriv k (fun x => (c / n.factorial) * x^n * ϕ (u * x)) x| ≤ ε := by
          intro k hk
          have h_bound : ∀ u : ℝ, ∀ x : ℝ, iteratedDeriv k (fun x => (c / Nat.factorial n) * x^n * ϕ (u * x)) x = (c / Nat.factorial n) * iteratedDeriv k (fun x => x^n * ϕ (u * x)) x := by
            intro u x
            simp only [mul_assoc, iteratedDeriv_eq_iterate]
            induction' k with k ih generalizing x <;> simp_all [ Function.iterate_succ_apply', mul_comm u ];
            rw [ Filter.EventuallyEq.deriv_eq ( Filter.eventuallyEq_of_mem ( Metric.ball_mem_nhds _ zero_lt_one ) fun y hy => ih ( Nat.lt_of_succ_lt hk ) y ) ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm ];
          have := smooth_bump_scaling_bound ϕ hϕ.1 hϕ.2.1 n k hk;
          obtain ⟨ R, hR ⟩ := this ( ε / ( |c / ( n ! : ℝ )| + 1 ) ) ( by positivity ) ; exact ⟨ R, fun u hu x => by rw [ h_bound u x ] ; exact abs_le.mpr ⟨ by cases abs_cases ( c / ( n ! : ℝ ) ) <;> nlinarith [ abs_le.mp ( hR u hu x ), mul_div_cancel₀ ε ( by positivity : ( |c / ( n ! : ℝ )| + 1 ) ≠ 0 ) ], by cases abs_cases ( c / ( n ! : ℝ ) ) <;> nlinarith [ abs_le.mp ( hR u hu x ), mul_div_cancel₀ ε ( by positivity : ( |c / ( n ! : ℝ )| + 1 ) ≠ 0 ) ] ⟩ ⟩ ;
        choose! R hR using h_smooth_bump_scaling_bound;
        exact ⟨ Max.max ( ∑ k ∈ Finset.range n, |R k| + 1 ) 1, by positivity, fun k hk x => hR k hk _ ( le_trans ( le_abs_self _ ) ( le_trans ( Finset.single_le_sum ( fun a _ => abs_nonneg ( R a ) ) ( Finset.mem_range.mpr hk ) ) ( by linarith [ le_max_left ( ∑ k ∈ Finset.range n, |R k| + 1 ) 1, le_max_right ( ∑ k ∈ Finset.range n, |R k| + 1 ) 1 ] ) ) ) x ⟩;
      -- refine' ⟨ _, _, _, _, hu.2 ⟩;
      use fun x ↦ c / ↑n ! * x ^ n * ϕ (u * x)
      constructor
      · exact ContDiff.mul ( ContDiff.mul contDiff_const ( contDiff_id.pow n ) ) ( hϕ.1.comp ( contDiff_const.mul contDiff_id ) );
      constructor
      · rw [ hasCompactSupport_iff_eventuallyEq ] at *;
        simp_all only [EventuallyEq, Pi.zero_apply, coclosedCompact_eq_cocompact,
          cocompact_eq_atBot_atTop, eventually_sup, eventually_atBot, eventually_atTop, ge_iff_le,
          mul_eq_zero, div_eq_zero_iff, Nat.cast_eq_zero, pow_eq_zero_iff', ne_eq];
        exact ⟨ by obtain ⟨ a, ha ⟩ := hϕ.2.1.1; exact ⟨ a / u, fun x hx => Or.inr <| ha _ <| by nlinarith [ mul_div_cancel₀ a hu.1.ne' ] ⟩, by obtain ⟨ a, ha ⟩ := hϕ.2.1.2; exact ⟨ a / u, fun x hx => Or.inr <| ha _ <| by nlinarith [ mul_div_cancel₀ a hu.1.ne' ] ⟩ ⟩;
      constructor
      · intro k
        -- By definition of $f$, we know that its $k$-th derivative at 0 is given by the $k$-th derivative of $\frac{c}{n!} x^n \phi(u x)$ at 0.
        have h_deriv : iteratedDeriv k (fun x => (c / n.factorial) * x^n * ϕ (u * x)) 0 = (c / n.factorial) * iteratedDeriv k (fun x => x^n * ϕ (u * x)) 0 := by
          simp only [mul_assoc, iteratedDeriv_eq_iterate];
          -- The derivative of a constant times a function is the constant times the derivative of the function.
          have h_const_deriv : ∀ k : ℕ, deriv^[k] (fun x => c / (n ! : ℝ) * (x ^ n * ϕ (u * x))) = fun x => c / (n ! : ℝ) * deriv^[k] (fun x => x ^ n * ϕ (u * x)) x := by
            intro k; induction k <;> simp_all +decide [ Function.iterate_succ_apply', mul_assoc ] ;
          exact congr_fun ( h_const_deriv k ) 0;
        -- By definition of $f$, we know that its $k$-th derivative at 0 is given by the $k$-th derivative of $x^n \phi(u x)$ at 0.
        have h_deriv : iteratedDeriv k (fun x => x^n * ϕ (u * x)) 0 = iteratedDeriv k (fun x => x^n) 0 := by
          have h_deriv : ∀ x, |x| ≤ 1 / u → x^n * ϕ (u * x) = x^n := by
            intro x hx; rw [ hϕ.2.2.1 ( u * x ) ( by rw [ abs_mul, abs_of_nonneg hu.1.le ] ; exact le_trans ( mul_le_mul_of_nonneg_left hx hu.1.le ) ( by norm_num [ hu.1.ne' ] ) ) ] ; ring;
          rw [ Filter.EventuallyEq.iteratedDeriv_eq ];
          filter_upwards [ Metric.ball_mem_nhds 0 ( inv_pos.mpr hu.1 ) ] with x hx using h_deriv x ( by simpa [ abs_mul, abs_inv, abs_of_pos hu.1 ] using hx.out.le );
        bound;
        · simp_all only [ge_iff_le, iteratedDeriv_eq_iterate, iter_deriv_pow', tsub_self, pow_zero,
            mul_one];
          rw [ div_mul_eq_mul_div, div_eq_iff ( by positivity ) ];
          exact congrArg _ ( Nat.recOn k ( by norm_num ) fun n ih => by rw [ Finset.prod_range_succ' ] ; simp +decide [ Nat.factorial_succ, ih, mul_comm ] );
        · simp_all only [iteratedDeriv_eq_iterate, iter_deriv_pow', ge_iff_le, mul_eq_zero,
            div_eq_zero_iff, Nat.cast_eq_zero, pow_eq_zero_iff', ne_eq, true_and];
          cases lt_or_gt_of_ne h <;> first | exact Or.inr <| Or.inl <| Finset.prod_eq_zero ( Finset.mem_range.mpr ‹_› ) <| sub_self _ | exact Or.inr <| Or.inr <| Nat.sub_ne_zero_of_lt ‹_›
      exact hu.2

/-
The n-th derivative of x^m * f(x) at 0 is 0 if n < m.
-/
set_option linter.style.longLine false in
lemma iteratedDeriv_mul_pow_eq_zero_of_lt {n m : ℕ} (h : n < m) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv n (fun x => x ^ m * f x) 0 = 0 := by
      rw [ iteratedDeriv_eq_iterate ];
      -- By induction on $n$, we can show that the $n$-th derivative of $x^m f(x)$ is $x^{m-n} g_n(x)$ for some smooth function $g_n(x)$.
      have h_ind : ∀ n ≤ m, ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ deriv^[n] (fun x => x ^ m * f x) = fun x => x ^ (m - n) * g x := by
        -- We proceed by induction on $n$.
        intro n hn
        induction' n with n ih;
        · exact ⟨ f, hf, rfl ⟩;
        · obtain ⟨ g, hg₁, hg₂ ⟩ := ih ( Nat.le_of_succ_le hn ) ; rw [ Function.iterate_succ_apply' ] ; aesop;
          -- The derivative of $x^{m-n} g(x)$ is $(m-n)x^{m-n-1} g(x) + x^{m-n} g'(x)$.
          use fun x => (m - n) * g x + x * deriv g x;
          -- The sum of continuously differentiable functions is continuously differentiable.
          have h_cont_diff : ContDiff ℝ ∞ (fun x => (m - n) * g x + x * deriv g x) := by
            apply_rules [ ContDiff.add, ContDiff.mul, contDiff_const, contDiff_id ];
            apply_rules [ ContDiff.fderiv_apply, hg₁ ];
            -- The function g is continuously differentiable up to infinity by hypothesis.
            apply ContDiff.comp hg₁ (contDiff_snd);
            · exact contDiff_id;
            · exact contDiff_const;
            · norm_num;
          aesop
          ext x; norm_num [ hg₁.contDiffAt.differentiableAt ] ; ring;
          rw [ Nat.cast_sub ( by linarith ) ] ; rw [ show m - n = m - ( 1 + n ) + 1 by omega ] ; ring;
          grind;
      rcases h_ind n h.le with ⟨g, hg⟩
      simp_all only [ne_eq, tsub_pos_iff_lt, ne_of_gt, not_false_eq_true, zero_pow, zero_mul]

set_option linter.style.longLine false in
lemma deriv_bound {f : ℝ → ℝ} {c x u y : ℝ} (hf : ContDiff ℝ 1 f) (hc : c ∈ Set.Ioo (min (u * x) (u * (x + y))) (max (u * x) (u * (x + y))))
                              (hu₁ : 0 < u) (hu₂ : u ≤ 1) (hy : |y| < 1) :
      |deriv f c| ≤ sSup (Set.image (fun t => |deriv f t|) (Set.Icc (-1 - |x|) (1 + |x|))) := by
    apply le_csSup (IsCompact.bddAbove <| isCompact_Icc.image <| continuous_abs.comp <| hf.continuous_deriv le_rfl) _
    have hmem : c ∈ Set.Icc (-1 - |x|) (1 + |x|) := by
      constructor <;>
        cases max_cases (u * x) (u * (x + y)) <;>
        cases min_cases (u * x) (u * (x + y)) <;>
        cases abs_cases x <;>
        cases abs_cases y <;>
        nlinarith [hc.1, hc.2]
    exact ⟨c, hmem, rfl⟩

/-
The derivative of the integral of P(t) * f(t * x) is the integral of t * P(t) * f'(t * x).
-/
set_option linter.style.longLine false in
lemma hasDerivAt_integral_poly_mul_comp (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (P : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun x => ∫ t in (0 : ℝ)..1, P.eval t * f (t * x)) (∫ t in (0 : ℝ)..1, t * P.eval t * deriv f (t * x)) x := by
      -- Apply the Leibniz rule for differentiation under the integral sign.
      have h_leibniz : HasDerivAt (fun x => ∫ t in (0 : ℝ)..1, P.eval t * f (t * x)) (∫ t in (0 : ℝ)..1, P.eval t * deriv f (t * x) * t) x := by
        rw [ hasDerivAt_iff_tendsto_slope_zero ];
        -- Apply the dominated convergence theorem to interchange the limit and the integral.
        have h_dominate : Filter.Tendsto (fun t => ∫ u in (0 : ℝ)..1, P.eval u * (f (u * (x + t)) - f (u * x)) / t) (nhdsWithin 0 {0}ᶜ) (nhds (∫ u in (0 : ℝ)..1, P.eval u * deriv f (u * x) * u)) := by
          apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _
          use fun u => ‖P.eval u‖ * ( SupSet.sSup ( Set.image ( fun t => ‖deriv f t‖ ) ( Set.Icc ( -1 - |x| ) ( 1 + |x| ) ) ) ) * |u|;
          · exact Filter.Eventually.of_forall fun n => Continuous.aestronglyMeasurable ( by exact Continuous.div_const ( by exact Continuous.mul ( P.continuous ) ( by exact Continuous.sub ( hf.continuous.comp ( by continuity ) ) ( hf.continuous.comp ( by continuity ) ) ) ) _ );
          · rw [ eventually_nhdsWithin_iff, Metric.eventually_nhds_iff ]
            refine ⟨ 1, zero_lt_one, ?_⟩
            apply fun y hy hy' => Filter.Eventually.of_forall fun u hu => _
            intro y hy hy' u hu
            simp_all only [dist_zero_right, norm_eq_abs, Set.mem_compl_iff, Set.mem_singleton_iff, zero_le_one,
              Set.uIoc_of_le, Set.mem_Ioc, norm_div, norm_mul]
            obtain ⟨left, right⟩ := hu
            -- Apply the mean value theorem to the interval $[u * x, u * (x + y)]$.
            obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo (min (u * x) (u * (x + y))) (max (u * x) (u * (x + y))), deriv f c = (f (u * (x + y)) - f (u * x)) / (u * y) := by
              have hne : u * x ≠ u * (x + y) := by
                intro h
                have : u * y = 0 := by
                  have := congrArg (fun t => t - u * x) h
                  -- (u*x - u*x) = (u*(x+y) - u*x) = u*y
                  simpa [mul_add] using this
                have : y = 0 := by
                  rcases mul_eq_zero.mp this with hu | hy0
                  · exfalso ; exact (ne_of_gt left hu).elim
                  · exact hy0
                exact hy' this
              have hcont : Continuous f := (hf.differentiable le_rfl).continuous
              by_cases hle : u * x ≤ u * (x + y)
              · have hlt : u * x < u * (x + y) := lt_of_le_of_ne hle hne
                rcases exists_deriv_eq_slope (f := f) hlt hcont.continuousOn (hf.differentiable le_rfl).differentiableOn with
                  ⟨c, hc, hderiv⟩
                refine ⟨c, ?_, ?_⟩
                · simpa [min_eq_left hle, max_eq_right hle] using hc
                · have hsub : u * (x + y) - u * x = u * y := by ring
                  simpa [min_eq_left hle, max_eq_right hle, hsub] using hderiv
              · have hlt : u * (x + y) < u * x := lt_of_le_of_ne (le_of_not_ge hle) hne.symm
                rcases exists_deriv_eq_slope (f := f) hlt hcont.continuousOn (hf.differentiable le_rfl).differentiableOn with
                  ⟨c, hc, hderiv⟩
                refine ⟨c, ?_, ?_⟩
                · have hle' : u * (x + y) ≤ u * x := le_of_lt hlt
                  simpa [min_eq_right hle', max_eq_left hle'] using hc
                · have hsub : u * x - u * (x + y) = -(u * y) := by ring
                  have hsub' : u * x - u * (x + y) = - (u * y) := hsub
                  -- flip both numerator and denominator
                  have : (f (u * x) - f (u * (x + y))) / (u * x - u * (x + y))
                        = (f (u * (x + y)) - f (u * x)) / (u * y) := by
                    calc
                      (f (u * x) - f (u * (x + y))) / (u * x - u * (x + y))
                          = (f (u * x) - f (u * (x + y))) / (-(u * y)) := by simp [hsub']
                      _   = -((f (u * x) - f (u * (x + y))) / (u * y)) := by simp [div_neg]
                      _   = (f (u * (x + y)) - f (u * x)) / (u * y) := by ring
                  have hle' : u * (x + y) ≤ u * x := le_of_lt hlt
                  simpa [min_eq_right hle', max_eq_left hle', this] using hderiv
            -- Since $|c| \leq 1 + |x|$, we have $|deriv f c| \leq \sup_{t \in [-1 - |x|, 1 + |x|]} |deriv f t|$.
            let h_deriv_bound := deriv_bound hf hc.1 left right hy
            simp_all only [abs_pos, ne_eq,not_false_eq_true, div_le_iff₀, ge_iff_le]
            rw [ hc.2, abs_div, abs_mul, div_le_iff₀ ( mul_pos ( abs_pos.mpr left.ne' ) ( abs_pos.mpr hy' ) ) ] at h_deriv_bound
            nlinarith [ abs_nonneg ( P.eval u ) ]
          · exact Continuous.intervalIntegrable ( by exact Continuous.mul ( Continuous.mul ( P.continuous.norm ) continuous_const ) continuous_abs ) _ _;
          · apply Filter.Eventually.of_forall
            intro t ht
            have h_deriv : HasDerivAt (fun n => f (t * (x + n))) (deriv f (t * x) * t) 0 := by
              convert HasDerivAt.comp 0 ( hf.differentiable le_rfl _ |> DifferentiableAt.hasDerivAt ) ( HasDerivAt.const_mul t ( hasDerivAt_id 0 |> HasDerivAt.const_add x ) ) using 1 ; norm_num;
            simpa only [mul_comm, div_eq_mul_inv, mul_left_comm, zero_add, add_zero, smul_eq_mul,
              mul_assoc] using h_deriv.tendsto_slope_zero.const_mul (P.eval t);
        convert h_dominate using 2;
        norm_num [ div_eq_inv_mul, mul_sub ];
        rw [ intervalIntegral.integral_sub ( by exact Continuous.intervalIntegrable ( by exact Continuous.mul continuous_const <| by exact Continuous.mul ( P.continuous.comp continuous_id' ) <| hf.continuous.comp <| by continuity ) _ _ ) ( by exact Continuous.intervalIntegrable ( by exact Continuous.mul continuous_const <| by exact Continuous.mul ( P.continuous.comp continuous_id' ) <| hf.continuous.comp <| by continuity ) _ _ ) ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm ];
        simp only [← intervalIntegral.integral_const_mul, mul_left_comm];
      simpa only [ mul_assoc, mul_comm, mul_left_comm ] using h_leibniz

/-
The integral of P(t) * f(t * x) is smooth if f is smooth.
-/
lemma contDiff_integral_poly_mul_comp (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (P : Polynomial ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, P.eval t * f (t * x)) := by
      -- By induction on $n$, we can show that the function is $C^n$ for all $n$.
      have h_ind : ∀ n : ℕ, ContDiff ℝ n (fun x => ∫ t in (0 : ℝ)..1, P.eval t * f (t * x)) := by
        intro n;
        induction' n with n ih generalizing f P;
        · simp +zetaDelta at *;
          -- The integral of a continuous function is continuous, so the function x ↦ ∫ t in (0 : ℝ)..1, P.eval t * f (t * x) is continuous.
          have h_cont : Continuous (fun x => ∫ t in (0 : ℝ)..1, P.eval t * f (t * x)) := by
            have h_integrand_cont : Continuous (fun (p : ℝ × ℝ) => P.eval p.2 * f (p.2 * p.1)) := by
              exact Continuous.mul ( P.continuous.comp continuous_snd ) ( hf.continuous.comp ( continuous_snd.mul continuous_fst ) )
            fun_prop;
          exact h_cont;
        · -- By the induction hypothesis, the derivative of the integral is C^n.
          have h_deriv : ContDiff ℝ n (fun x => ∫ t in (0 : ℝ)..1, t * P.eval t * deriv f (t * x)) := by
            convert ih ( deriv f ) ( by
              exact ContDiff.deriv' hf ) ( Polynomial.X * P ) using 1;
            norm_num;
          have h_eq_deriv : ∀ x, HasDerivAt (fun x => ∫ t in (0 : ℝ)..1, P.eval t * f (t * x)) (∫ t in (0 : ℝ)..1, t * P.eval t * deriv f (t * x)) x := by
            apply_rules [ hasDerivAt_integral_poly_mul_comp ];
            -- Since $f$ is $C^\infty$, it is also $C^1$.
            apply hf.of_le; norm_num;
          simp +zetaDelta at *;
          rw [ contDiff_succ_iff_deriv ];
          exact ⟨ fun x => ( h_eq_deriv x |> HasDerivAt.differentiableAt ), by aesop, by rw [ show deriv _ = _ from funext fun x => HasDerivAt.deriv ( h_eq_deriv x ) ] ; exact h_deriv ⟩;
      exact contDiff_iff_contDiffAt.mpr fun x => contDiffAt_infty.mpr fun n => h_ind n |> ContDiff.contDiffAt




set_option linter.style.longLine false in
theorem smooth_realization_jet : ∀ a : ℕ → ℝ, ∃ f : ℝ → ℝ, (ContDiff ℝ ∞ f) ∧ ∀ k : ℕ, iteratedDeriv k f 0 = a k := by
  -- Apply the lemma exists_smooth_term_with_bound to each term in the sequence a.
  have h_seq : ∀ n : ℕ, ∀ a_n : ℝ, ∃ f_n : ℝ → ℝ, ContDiff ℝ ∞ f_n ∧ HasCompactSupport f_n ∧ (∀ k, iteratedDeriv k f_n 0 = if k = n then a_n else 0) ∧ (∀ k < n, ∀ x, |iteratedDeriv k f_n x| ≤ (1 / 2) ^ (n + 1)) := by
    aesop;
    convert exists_smooth_term_with_bound n a_n ( ( 2 ^ ( n + 1 ) ) ⁻¹ ) ( by positivity ) using 1;
  -- Define the function $f$ as the sum of the functions $f_n$ from $h_seq$.
  have h_sum : ∀ a : ℕ → ℝ, ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ ∀ k, iteratedDeriv k f 0 = a k := by
    intro a
    have h_seq : ∀ n, ∃ f_n : ℝ → ℝ, ContDiff ℝ ∞ f_n ∧ HasCompactSupport f_n ∧ (∀ k, iteratedDeriv k f_n 0 = if k = n then a n else 0) ∧ (∀ k < n, ∀ x, |iteratedDeriv k f_n x| ≤ (1 / 2) ^ (n + 1)) := by
      exact fun n => h_seq n ( a n )
    choose f hf1 hf2 hf3 hf4 using h_seq;
    -- Apply the lemma `smooth_bump_scaling_bound` to each `f_n` to get bounds on their derivatives.
    have h_bounds : ∀ k, ∃ M : ℕ → ℝ, (∀ n, 0 ≤ M n) ∧ Summable M ∧ ∀ n, ∀ x, |iteratedDeriv k (f n) x| ≤ M n := by
      intro k;
      use fun n => if n ≤ k then ( SupSet.sSup ( Set.image ( fun x => |iteratedDeriv k ( f n ) x| ) ( Set.univ ) ) ) else ( 1 / 2 ) ^ ( n + 1 );
      aesop;
      · apply_rules [ Real.sSup_nonneg ] ; aesop;
      · rw [ ← summable_nat_add_iff ( k + 1 ) ];
        ring_nf;
        norm_num +zetaDelta at *;
        exact Summable.mul_right _ ( Summable.mul_right _ ( summable_geometric_two ) );
      · apply le_csSup;
        · have h_compact_support : HasCompactSupport (iteratedDeriv k (f n)) := by
            -- Since $f_n$ is smooth and compactly supported, its derivatives are also compactly supported.
            have h_compact_support : ∀ k, HasCompactSupport (iteratedDeriv k (f n)) := by
              intro k
              have h_support : ∀ x, x ∉ tsupport (f n) → iteratedDeriv k (f n) x = 0 := by
                induction' k with k ih generalizing x <;> simp_all +decide [ iteratedDeriv_succ ];
                · exact fun x hx => Classical.not_not.1 fun hx' => hx <| subset_closure hx';
                · intro x hx;
                  exact HasDerivAt.deriv ( HasDerivAt.congr_of_eventuallyEq ( hasDerivAt_const _ _ ) ( Filter.eventuallyEq_of_mem ( IsOpen.mem_nhds ( isOpen_compl_iff.mpr <| isClosed_tsupport _ ) hx ) fun y hy => ih y hy ) )
              rw [ hasCompactSupport_iff_eventuallyEq ];
              simp_all +decide [ Filter.EventuallyEq, Filter.eventually_inf_principal ];
              have h_compact_support : IsCompact (tsupport (f n)) := by
                exact hf2 n;
              exact ⟨ ⟨ -1 - ( SupSet.sSup ( Set.image ( fun x => |x| ) ( tsupport ( f n ) ) ) ), fun x hx => h_support x <| by rintro H; linarith [ abs_le.mp ( show |x| ≤ SupSet.sSup ( Set.image ( fun x => |x| ) ( tsupport ( f n ) ) ) from le_csSup ( by exact IsCompact.bddAbove <| h_compact_support.image <| continuous_abs ) <| Set.mem_image_of_mem _ H ) ] ⟩, ⟨ 1 + ( SupSet.sSup ( Set.image ( fun x => |x| ) ( tsupport ( f n ) ) ) ), fun x hx => h_support x <| by rintro H; linarith [ abs_le.mp ( show |x| ≤ SupSet.sSup ( Set.image ( fun x => |x| ) ( tsupport ( f n ) ) ) from le_csSup ( by exact IsCompact.bddAbove <| h_compact_support.image <| continuous_abs ) <| Set.mem_image_of_mem _ H ) ] ⟩ ⟩;
            exact h_compact_support k;
          have := h_compact_support.exists_bound_of_continuous ( show Continuous ( iteratedDeriv k ( f n ) ) from ?_ );
          · exact ⟨ this.choose, Set.forall_mem_range.mpr fun x => this.choose_spec x ⟩;
          · apply_rules [ ContDiff.continuous_iteratedDeriv, hf1 ];
            -- Since $k$ is a natural number, it is less than or equal to infinity.
            norm_cast;
            norm_num;
        · exact Set.mem_range_self x;
    choose M hM1 hM2 hM3 using h_bounds;
    -- Define the function $f$ as the sum of the functions $f_n$ from $h_seq$ and show that it is smooth.
    have h_smooth : ContDiff ℝ ∞ (fun x => ∑' n, f n x) := by
      refine' contDiff_tsum _ _ _;
      use fun k n => M k n;
      · assumption;
      · aesop;
      · simp_all +decide [ iteratedFDeriv_eq_equiv_comp ];
    -- Show that the k-th derivative of the sum is the sum of the k-th derivatives.
    have h_deriv_sum : ∀ k, iteratedDeriv k (fun x => ∑' n, f n x) = fun x => ∑' n, iteratedDeriv k (f n) x := by
      intro k;
      induction' k with k ih;
      · norm_num;
      · ext x;
        rw [ iteratedDeriv_succ, ih ];
        rw [ deriv_tsum ];
        congr! 1;
        exact funext fun n => by rw [ iteratedDeriv_succ ] ;
        exact hM2 ( k + 1 );
        any_goals exact x;
        · intro n;
          apply_rules [ ContDiff.differentiable_iteratedDeriv, hf1 ];
          exact compareOfLessAndEq_eq_lt.mp rfl;
        · intro n y; specialize hM3 ( k + 1 ) n y; simp_all +decide [ iteratedDeriv_succ ] ;
        · -- Since the series of M k n is summable and |iteratedDeriv k (f n) x| ≤ M k n for all n, the series of the k-th derivatives is absolutely summable.
          have h_abs_summable : Summable (fun n => |iteratedDeriv k (f n) x|) := by
            exact Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => hM3 k n x ) ( hM2 k );
          exact h_abs_summable.of_abs;
    use fun x => ∑' n, f n x;
    aesop;
    rw [ tsum_eq_single k ] <;> aesop;
  assumption

set_option linter.style.longLine false
lemma iteratedDeriv_comp_sq (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    iteratedDeriv (2 * k) (fun x => g (x ^ 2)) 0 = ((Nat.factorial (2 * k) : ℝ) / (Nat.factorial k : ℝ)) * iteratedDeriv k g 0 := by
  -- By definition of $g$, we know that its Taylor expansion at 0 is given by the Taylor series of $g$.
  have h_taylor : ∀ x, g x = ∑ n ∈ Finset.range (k + 1), deriv^[n] g 0 / n ! * x ^ n + x ^ (k + 1) * ∫ t in (0 : ℝ)..1, (1 - t) ^ k / k ! * deriv^[k + 1] g (t * x) := by
    -- Apply the Taylor series expansion theorem to g at 0.
    have h_taylor : ∀ x, g x = ∑ n ∈ Finset.range (k + 1), deriv^[n] g 0 / n ! * x ^ n + ∫ t in (0 : ℝ)..x, (x - t) ^ k / k ! * deriv^[k + 1] g t := by
      induction' k with k ih;
      · intro x
        simp_all only [zero_add, Finset.range_one, Finset.sum_singleton, iterate_zero, id_eq, Nat.factorial_zero,
          Nat.cast_one, div_one, pow_zero, mul_one, ne_eq, one_ne_zero, not_false_eq_true, div_self, iterate_one,
          one_mul]
        rw [ intervalIntegral.integral_deriv_eq_sub ] <;> norm_num [ hg.contDiffAt.differentiableAt ];
        -- Since $g$ is infinitely differentiable, its derivative $g'$ is continuous.
        have h_cont_diff : Continuous (deriv g) := by
          simpa using hg.continuous_deriv;
        exact h_cont_diff.intervalIntegrable _ _;
      · -- Apply the integration by parts formula to the integral.
        have h_parts : ∀ a b x, ∫ t in a..b, (x - t) ^ (k + 1) / (Nat.factorial (k + 1)) * deriv^[k + 2] g t = (x - b) ^ (k + 1) / (Nat.factorial (k + 1)) * deriv^[k + 1] g b - (x - a) ^ (k + 1) / (Nat.factorial (k + 1)) * deriv^[k + 1] g a + ∫ t in a..b, (x - t) ^ k / (Nat.factorial k) * deriv^[k + 1] g t := by
          intro a b x;
          rw [ intervalIntegral.integral_mul_deriv_eq_deriv_mul ];
          rotate_left;
          -- The derivative of $(x - t)^{k+1} / (k+1)!$ with respect to $t$ is $-(x - t)^k / k!$.
          have h_deriv : ∀ t, HasDerivAt (fun t => (x - t) ^ (k + 1) / (Nat.factorial (k + 1))) (-(x - t) ^ k / (Nat.factorial k)) t := by
            -- Apply the chain rule to compute the derivative.
            intro t
            have h_chain : HasDerivAt (fun t => (x - t) ^ (k + 1)) (-(k + 1) * (x - t) ^ k) t := by
              -- Apply the chain rule to compute the derivative: the derivative of $(x - t)^{k+1}$ with respect to $t$ is $-(k+1)(x - t)^k$.
              have h_chain : HasDerivAt (fun t => (x - t)) (-1) t := by
                exact hasDerivAt_id t |> HasDerivAt.const_sub x;
              convert h_chain.pow ( k + 1 ) using 1 ; norm_num ; ring;
            convert h_chain.div_const ( ( k + 1 ) ! : ℝ ) using 1 ; push_cast [ Nat.factorial_succ ] ; ring;
            -- Combine and simplify the fractions
            field_simp
            ring;
          exact fun x a ↦ h_deriv x;
          rotate_left;
          exact Continuous.intervalIntegrable ( by exact Continuous.div_const ( by exact Continuous.neg ( by exact Continuous.pow ( continuous_const.sub continuous_id' ) _ ) ) _ ) _ _;
          rotate_left;
          use fun t => deriv^[k + 1] g t;
          · norm_num [ neg_div, neg_mul ];
          · have h_deriv : ∀ n : ℕ, ContDiff ℝ ∞ (deriv^[n] g) := by
              fun_prop;
            intro x hx; have := h_deriv ( k + 1 ) ; have := this.differentiable;
            simp_all only [iterate_succ, comp_apply, WithTop.one_le_coe, le_top, forall_const]
            convert this.differentiableAt.hasDerivAt using 1;
            erw [ Function.iterate_succ_apply' ];
          · have h_cont_diff : ∀ n, ContDiff ℝ ∞ (deriv^[n] g) := by
              fun_prop;
            exact ( h_cont_diff _ |> ContDiff.continuous |> Continuous.intervalIntegrable ) _ _;
        intro x; rw [ h_parts ] ; simp +decide [ Finset.sum_range_succ, ih ] ; ring;
    intro x; specialize h_taylor x; by_cases hx : x = 0 <;> simp_all +decide [ div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm ] ;
    -- Perform the substitution $u = \frac{t}{x}$ to transform the integral.
    have h_subst : ∫ t in (0 : ℝ)..x, (x - t) ^ k * ((k ! : ℝ)⁻¹ * deriv^[k] (deriv g) t) = ∫ u in (0 : ℝ)..1, (x - x * u) ^ k * ((k ! : ℝ)⁻¹ * deriv^[k] (deriv g) (x * u)) * x := by
      simp only [mul_comm x, intervalIntegral.integral_mul_const, ne_eq, hx, not_false_eq_true,
        intervalIntegral.integral_comp_mul_right
            (fun u => (x - u) ^ k * ((k ! : ℝ)⁻¹ * deriv^[k] (deriv g) u)),
        zero_mul, one_mul, smul_eq_mul];
      rw [ inv_mul_eq_div, div_mul_cancel₀ _ hx ];
    rw [ h_subst ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, ← intervalIntegral.integral_const_mul ] ; ring
    exact intervalIntegral.integral_congr fun u hu => by rw [ show x - x * u = x * ( 1 - u ) by ring ] ; rw [ mul_pow ] ; ring
  -- The remainder term's 2k-th derivative is zero because it's multiplied by x^(2(k+1)), which is a higher power than 2k.
  have h_remainder : iteratedDeriv (2 * k) (fun x => x ^ (2 * (k + 1)) * ∫ t in (0 : ℝ)..1, (1 - t) ^ k / k ! * deriv^[k + 1] g (t * x ^ 2)) 0 = 0 := by
    apply iteratedDeriv_mul_pow_eq_zero_of_lt;
    · linarith;
    · have h_cont_diff : ∀ k : ℕ, ContDiff ℝ ∞ (deriv^[k] g) := by
        fun_prop;
      have := h_cont_diff ( k + 1 );
      have := contDiff_integral_poly_mul_comp ( deriv^[k + 1] g ) this;
      convert this ( Polynomial.C ( 1 / ( k ! : ℝ ) ) * ( 1 - Polynomial.X ) ^ k ) |> ContDiff.comp <| contDiff_id.pow 2 using 2 ; norm_num;
      exact intervalIntegral.integral_congr fun _ _ => by ring;
  -- The polynomial part's 2k-th derivative is given by the binomial theorem.
  have h_poly : iteratedDeriv (2 * k) (fun x => ∑ n ∈ Finset.range (k + 1), deriv^[n] g 0 / n ! * x ^ (2 * n)) 0 = (2 * k)! / k ! * deriv^[k] g 0 := by
    -- The 2k-th derivative of a sum is the sum of the 2k-th derivatives.
    have h_poly_deriv : iteratedDeriv (2 * k) (fun x => ∑ n ∈ Finset.range (k + 1), deriv^[n] g 0 / n ! * x ^ (2 * n)) 0 = ∑ n ∈ Finset.range (k + 1), deriv^[n] g 0 / n ! * iteratedDeriv (2 * k) (fun x => x ^ (2 * n)) 0 := by
      have h_poly_deriv : ∀ m : ℕ, iteratedDeriv m (fun x => ∑ n ∈ Finset.range (k + 1), deriv^[n] g 0 / n ! * x ^ (2 * n)) = fun x => ∑ n ∈ Finset.range (k + 1), deriv^[n] g 0 / n ! * iteratedDeriv m (fun x => x ^ (2 * n)) x := by
        intro m; induction' m with m ih <;> simp +decide [ *, iteratedDeriv_succ ] ;
        -- The derivative of a sum is the sum of the derivatives, and the derivative of a constant times a function is the constant times the derivative of the function.
        funext x; exact (by
        -- The derivative of a sum is the sum of the derivatives, and the derivative of a constant times a function is the constant times the derivative of the function.
        have h_deriv_sum : deriv (fun x => ∑ n ∈ Finset.range (k + 1), deriv^[n] g 0 / n ! * iteratedDeriv m (fun x => x ^ (2 * n)) x) x = ∑ n ∈ Finset.range (k + 1), deriv (fun x => deriv^[n] g 0 / n ! * iteratedDeriv m (fun x => x ^ (2 * n)) x) x := by
          -- The derivative of a sum is the sum of the derivatives, as long as the functions are differentiable.
          have h_deriv_sum : ∀ n ∈ Finset.range (k + 1), DifferentiableAt ℝ (fun x => deriv^[n] g 0 / (n ! : ℝ) * iteratedDeriv m (fun x => x ^ (2 * n)) x) x := by
            intro n hn; norm_num [ iteratedDeriv_eq_iterate ] ;
          exact deriv_fun_sum h_deriv_sum;
        exact h_deriv_sum.trans ( Finset.sum_congr rfl fun _ _ => by norm_num ));
      exact congr_fun ( h_poly_deriv ( 2 * k ) ) 0;
    rw [ h_poly_deriv, Finset.sum_eq_single k ] <;> norm_num [ Nat.factorial_ne_zero, iteratedDeriv_eq_iterate ]
    ring_nf
    simp_all only [iterate_succ, comp_apply, mul_eq_mul_left_iff, mul_eq_zero, inv_eq_zero, Nat.cast_eq_zero]
    · -- The product $\prod_{x=0}^{2k-1} (k*2 - x)$ is equal to $(2k)!$ because it's the product of the first $2k$ natural numbers in reverse order.
      left; exact (by
      have h_prod : ∀ m : ℕ, ∏ x ∈ Finset.range m, (m - x : ℝ) = Nat.factorial m := by
        intro m;
        induction m
        · simp_all only [Finset.range_zero, CharP.cast_eq_zero, zero_sub, Finset.prod_empty,
            Nat.factorial_zero, Nat.cast_one]
        · simp_all only [Nat.cast_add, Nat.cast_one, Finset.prod_range_succ',
            add_sub_add_right_eq_sub, CharP.cast_eq_zero, sub_zero, Nat.factorial_succ, Nat.cast_mul]
          ring
      exact_mod_cast h_prod ( k * 2 ));
    · intro n hn hn'; right; left; rw [ Finset.prod_eq_zero_iff ] ; norm_num [ Nat.sub_eq_zero_of_le ( show n ≤ k from Nat.le_of_lt_succ hn ) ] ;
      exact ⟨ 2 * n, by contrapose! hn'; linarith, by push_cast; ring ⟩;
  -- By combining the results from the polynomial part and the remainder term, we conclude the proof.
  have h_final : iteratedDeriv (2 * k) (fun x => g (x ^ 2)) 0 = iteratedDeriv (2 * k) (fun x => ∑ n ∈ Finset.range (k + 1), deriv^[n] g 0 / n ! * x ^ (2 * n)) 0 + iteratedDeriv (2 * k) (fun x => x ^ (2 * (k + 1)) * ∫ t in (0 : ℝ)..1, (1 - t) ^ k / k ! * deriv^[k + 1] g (t * x ^ 2)) 0 := by
    rw [ ← iteratedDeriv_add ] ; congr ; ext x ; rw [ h_taylor ] ; ring;
    · norm_num [ add_comm ];
    · exact ContDiffAt.sum fun _ _ => ContDiffAt.mul ( contDiffAt_const ) ( contDiffAt_id.pow _ );
    · apply ContDiffAt.mul (contDiffAt_id.pow _) _;
      have h_int_smooth : ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, (1 - t) ^ k / k ! * deriv^[k + 1] g (t * x ^ 2)) := by
        have h_int_smooth : ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, (1 - t) ^ k / k ! * deriv^[k + 1] g (t * x)) := by
          have h_cont_diff : ContDiff ℝ ∞ (fun x => deriv^[k + 1] g x) := by
            fun_prop
          have h_int_smooth : ∀ (P : Polynomial ℝ), ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, P.eval t * deriv^[k + 1] g (t * x)) := by
            exact fun P ↦ contDiff_integral_poly_mul_comp (deriv^[k + 1] g) h_cont_diff P;
          convert h_int_smooth ( Polynomial.C ( 1 / ( k ! : ℝ ) ) * ( 1 - Polynomial.X ) ^ k ) using 2 ; norm_num ; ring;
          ac_rfl;
        exact h_int_smooth.comp ( contDiff_id.pow 2 );
      -- Since ContDiff ℝ ∞ implies ContDiffAt ℝ (2k) for any k, we can conclude that the integral function is ContDiffAt ℝ (2k) at 0.
      apply h_int_smooth.contDiffAt.of_le; norm_num;
      exact right_eq_inf.mp rfl;
  rw [h_final, h_poly, h_remainder]
  simp only [add_zero, mul_eq_mul_left_iff, div_eq_zero_iff, Nat.cast_eq_zero];
  exact Or.inl <| by rw [ iteratedDeriv_eq_iterate ] ;

set_option linter.style.longLine false in
lemma iteratedDeriv_odd_eq_zero_of_even (f : ℝ → ℝ) (heven : Function.Even f) (k : ℕ) :
    iteratedDeriv (2 * k + 1) f 0 = 0 := by
      -- By definition of even functions, we know that their derivatives at zero are zero for odd orders.
      have h_odd_deriv : ∀ k : ℕ, deriv^[k] (fun x => f (-x)) = fun x => (-1)^k * deriv^[k] f (-x) := by
        -- We proceed by induction on $k$.
        intro k
        induction' k with k ih;
        · norm_num;
        · ext x; rw [ Function.iterate_succ_apply', ih, Function.iterate_succ_apply' ] ; norm_num [ pow_succ' ] ;
          rw [ show deriv ( fun x => deriv^[k] f ( -x ) ) x = -deriv ( deriv^[k] f ) ( -x ) from ?_ ];
          · ring;
          · exact deriv_comp_neg (deriv^[k] f) x;
      -- Since $f$ is even, we have $f(-x) = f(x)$. Taking the $k$-th derivative of both sides, we get $(deriv^[k] f) (-x) = (-1)^k * (deriv^[k] f) x$.
      have h_even_deriv : ∀ k : ℕ, deriv^[k] f (-0) = (-1)^k * deriv^[k] f 0 := by
        intro k; specialize h_odd_deriv k; replace h_odd_deriv := congr_fun h_odd_deriv 0; aesop;
        rw [ ← h_odd_deriv, show ( fun x => f ( -x ) ) = f from funext fun x => heven x ];
      -- Applying the result from h_even_deriv with k = 2k+1, we get that the (2k+1)-th derivative of f at 0 is equal to (-1)^(2k+1) times itself.
      have h_odd_deriv_zero : deriv^[2 * k + 1] f 0 = (-1)^(2 * k + 1) * deriv^[2 * k + 1] f 0 := by
        grind +ring;
      norm_num [ iteratedDeriv_eq_iterate ] at * ; linarith

/-
For any even smooth function f, there exists a smooth function g such that f(x) - g(x^2) is flat at 0.
-/
set_option linter.style.longLine false in
lemma exists_smooth_even_approx (f : ℝ → ℝ) (heven : Function.Even f) (hsmooth : ContDiff ℝ ∞ f) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ ∀ k, iteratedDeriv k (fun x => f x - g (x ^ 2)) 0 = 0 := by
      -- Define the function $g$ using the provided theorem and the coefficients $a_k$.
      obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ ∀ k : ℕ, iteratedDeriv k g 0 = (iteratedDeriv (2 * k) f 0) / ((Nat.factorial (2 * k) : ℝ) / (Nat.factorial k : ℝ)) := by
        have := smooth_realization_jet; aesop;
      -- By definition of $g$, we know that its iterated derivatives at 0 match those of $f$.
      have h_deriv : ∀ k : ℕ, iteratedDeriv (2 * k) (fun x => f x - g (x ^ 2)) 0 = 0 := by
        -- By definition of $g$, we know that its iterated derivatives at 0 match those of $f$. Therefore, the difference $f(x) - g(x^2)$ has all derivatives zero at 0.
        intros k
        have h_diff : iteratedDeriv (2 * k) (fun x => f x - g (x ^ 2)) 0 = iteratedDeriv (2 * k) f 0 - iteratedDeriv (2 * k) (fun x => g (x ^ 2)) 0 := by
          -- Apply the linearity of the iterated derivative.
          have h_linearity : ∀ n : ℕ, iteratedDeriv n (fun x => f x - g (x ^ 2)) = fun x => iteratedDeriv n f x - iteratedDeriv n (fun x => g (x ^ 2)) x := by
            intro n; induction n <;> simp_all +decide [ iteratedDeriv_succ ] ;
            -- Apply the linearity of the derivative to the difference of the two functions.
            apply funext; intro x; exact deriv_sub (by
            apply_rules [ ContDiff.differentiable_iteratedDeriv, hsmooth ];
            exact compareOfLessAndEq_eq_lt.mp rfl) (by
            apply_rules [ ContDiff.differentiable_iteratedDeriv, hg.1.comp ];
            · exact contDiff_id.pow 2;
            · exact compareOfLessAndEq_eq_lt.mp rfl);
          exact congr_fun ( h_linearity _ ) _;
        -- Apply the lemma iteratedDeriv_comp_sq with the smooth function g and the natural number k.
        have h_comp : iteratedDeriv (2 * k) (fun x => g (x ^ 2)) 0 = ((Nat.factorial (2 * k) : ℝ) / (Nat.factorial k : ℝ)) * iteratedDeriv k g 0 := by
          have h_smooth : ContDiff ℝ ∞ g := hg.1
          exact iteratedDeriv_comp_sq g h_smooth k;
        aesop;
        rw [ mul_div_cancel₀ _ ( by positivity ), sub_self ];
      -- Since $f$ is even, its odd-order derivatives at $0$ are zero. Therefore, for any odd $k$, we have $\text{iteratedDeriv } k (f - g(x^2)) 0 = 0$.
      have h_odd_deriv : ∀ k : ℕ, iteratedDeriv (2 * k + 1) (fun x => f x - g (x ^ 2)) 0 = 0 := by
        -- Since $h(x) = f(x) - g(x^2)$ is even, its odd-order derivatives at $0$ are zero.
        have h_even : Function.Even (fun x => f x - g (x ^ 2)) := by
          exact fun x => by simp +decide [ heven x ] ;
        -- Apply the lemma that states the odd-order derivatives of an even function at 0 are zero.
        intros k
        apply iteratedDeriv_odd_eq_zero_of_even;
        · exact h_even;
      exact ⟨ g, hg.1, fun k => by rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> solve_by_elim ⟩


set_option linter.style.longLine false in
lemma deriv_integral_of_smooth (F : ℝ → ℝ → ℝ) (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2)) (x : ℝ) :
    HasDerivAt (fun x => ∫ t in (0 : ℝ)..1, F t x) (∫ t in (0 : ℝ)..1, deriv (fun y => F t y) x) x := by
      -- Applying the Leibniz rule to differentiate the integral.
      have h_leibniz : HasDerivAt (fun x => ∫ t in (0 : ℝ)..1, F t x) (∫ t in (0 : ℝ)..1, deriv (fun y => F t y) x) x := by
        have : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun x => F t x) (deriv (fun y => F t y) x) x := by
          -- Since $F$ is smooth, for any fixed $t$, the function $F(t, x)$ is smooth in $x$, hence differentiable at $x$.
          have h_diff : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiff ℝ ∞ (fun x => F t x) := by
            exact fun t ht => hF.comp ( contDiff_const.prodMk contDiff_id );
          exact fun t ht => DifferentiableAt.hasDerivAt ( h_diff t ht |> ContDiff.contDiffAt |> ContDiffAt.differentiableAt <| by norm_num )
        -- Apply the Leibniz rule for differentiation under the integral sign.
        have h_leibniz : HasDerivAt (fun x => ∫ t in (0 : ℝ)..1, F t x) (∫ t in (0 : ℝ)..1, deriv (fun y => F t y) x) x := by
          have h_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2) := by
            exact hF.continuous
          have h_cont_deriv : Continuous (fun p : ℝ × ℝ => deriv (fun y => F p.1 y) p.2) := by
            have h_cont_deriv : ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun y => F p.1 y) p.2) := by
              apply_rules [ ContDiff.fderiv_apply ];
              fun_prop;
              · exact contDiff_snd;
              · exact contDiff_const;
              · norm_num;
            exact h_cont_deriv.continuous
          -- By the dominated convergence theorem, we can interchange the limit and the integral.
          have h_dominated : Filter.Tendsto (fun h => ∫ t in (0 : ℝ)..1, (F t (x + h) - F t x) / h) (nhdsWithin 0 {0}ᶜ) (nhds (∫ t in (0 : ℝ)..1, deriv (fun y => F t y) x)) := by
            -- By the dominated convergence theorem, we can interchange the limit and the integral since the integrand is bounded.
            have h_dominated : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ h : ℝ, abs h ≤ 1 → abs ((F t (x + h) - F t x) / h) ≤ (sSup (Set.image (fun p : ℝ × ℝ => abs (deriv (fun y => F p.1 y) p.2)) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (x - 1) (x + 1)))) := by
              -- By the mean value theorem, there exists some $c \in (x, x + h)$ such that $\frac{F(t, x + h) - F(t, x)}{h} = \frac{\partial F}{\partial y}(t, c)$.
              have h_mean_value : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ h : ℝ, h ≠ 0 → abs h ≤ 1 → ∃ c ∈ Set.Icc (min x (x + h)) (max x (x + h)), (F t (x + h) - F t x) / h = deriv (fun y => F t y) c := by
                -- Apply the Mean Value Theorem to the function $F(t, y)$ with respect to $y$.
                intros t ht h h_ne h_abs
                have h_cont_diff : ContinuousOn (fun y => F t y) (Set.Icc (min x (x + h)) (max x (x + h))) ∧ DifferentiableOn ℝ (fun y => F t y) (Set.Ioo (min x (x + h)) (max x (x + h))) := by
                  constructor
                  · exact h_cont.comp_continuousOn ( continuousOn_const.prodMk continuousOn_id );
                  · -- Since $F$ is smooth, the partial derivative with respect to $y$ exists and is continuous, hence $F(t, y)$ is differentiable on any interval.
                    have h_diff : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiff ℝ ∞ (fun y => F t y) := by
                      exact fun t ht => hF.comp ( contDiff_const.prodMk contDiff_id );
                    exact ( h_diff t ht |> ContDiff.differentiable <| by norm_num ) |> Differentiable.differentiableOn;
                cases max_cases x ( x + h ) <;> cases min_cases x ( x + h ) <;> simp_all +decide;
                · have := exists_deriv_eq_slope ( f := fun y => F t y ) ( show x + h < x by linarith );
                  exact this h_cont_diff.1 h_cont_diff.2 |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, ⟨ by linarith [ hc₁.1 ], by linarith [ hc₁.2 ] ⟩, by rw [ hc₂ ] ; rw [ div_eq_div_iff ] <;> linarith ⟩;
                · have := exists_deriv_eq_slope ( f := fun y => F t y ) ( show x < x + h by linarith )
                  simp_all only [Set.mem_Ioo, add_sub_cancel_left, forall_const]
                  obtain ⟨w, left_2, right_2⟩ := this
                  exact ⟨ w, ⟨ by linarith, by linarith ⟩, right_2.symm ⟩;
              intro t ht h hh; by_cases hh' : h = 0
              · subst hh'
                simp_all only [Set.mem_Icc, hasDerivAt_deriv_iff, and_imp, ne_eq, inf_le_iff, le_sup_iff, abs_zero,
                  zero_le_one, add_zero, sub_self, div_zero, Set.Icc_prod_Icc]
                apply_rules [ Real.sSup_nonneg ]
                intro x₁ a
                simp_all only [Set.mem_image, Set.mem_Icc, Prod.exists, Prod.mk_le_mk, tsub_le_iff_right]
                obtain ⟨a, b, h⟩ := a
                rw [← h.2]
                exact abs_nonneg _
              · simp_all only [Set.mem_Icc, hasDerivAt_deriv_iff, and_imp, ne_eq, inf_le_iff, le_sup_iff,
                  Set.Icc_prod_Icc]
                obtain ⟨left, right⟩ := ht
                obtain ⟨ c, hc₁, hc₂ ⟩ := h_mean_value t left right h hh' hh ; rw [ hc₂ ]
                apply le_csSup _ _ <;> norm_num;
                · exact IsCompact.bddAbove ( isCompact_Icc.image ( h_cont_deriv.abs ) );
                · exact ⟨ t, c, ⟨ ⟨ left, by cases hc₁.1 <;> cases hc₁.2 <;> linarith [ abs_le.mp hh ] ⟩, right, by cases hc₁.1 <;> cases hc₁.2 <;> linarith [ abs_le.mp hh ] ⟩, rfl ⟩;
            apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _
            · exact fun t => SupSet.sSup ( Set.image ( fun p : ℝ × ℝ => |deriv ( fun y => F p.1 y ) p.2| ) ( Set.Icc 0 1 ×ˢ Set.Icc ( x - 1 ) ( x + 1 ) ) );
            · exact Filter.Eventually.of_forall fun n => Continuous.aestronglyMeasurable ( by exact Continuous.div_const ( by exact Continuous.sub ( h_cont.comp ( continuous_id.prodMk continuous_const ) ) ( h_cont.comp ( continuous_id.prodMk continuous_const ) ) ) _ );
            · rw [ eventually_nhdsWithin_iff ];
              filter_upwards [ Metric.ball_mem_nhds _ zero_lt_one ] with h hh hh' using Filter.eventually_of_mem ( MeasureTheory.ae_of_all _ fun t ht => h_dominated t ( by constructor <;> cases Set.mem_uIoc.mp ht <;> linarith ) h <| by simpa using hh.out.le ) fun t ht => ht;
            · norm_num;
            · simp_all only [Set.mem_Icc, hasDerivAt_deriv_iff, and_imp, Set.Icc_prod_Icc, zero_le_one, Set.uIoc_of_le, Set.mem_Ioc]
              filter_upwards [ ] with t ht₁ ht₂ using by simpa [ div_eq_inv_mul ] using this t ht₁.le ht₂ |> DifferentiableAt.hasDerivAt |> HasDerivAt.tendsto_slope_zero;
          rw [ hasDerivAt_iff_tendsto_slope_zero ];
          convert h_dominated using 2 ; norm_num [ div_eq_inv_mul ];
          rw [ intervalIntegral.integral_sub ] <;> norm_num;
          · exact Continuous.intervalIntegrable ( by exact h_cont.comp ( continuous_id.prodMk continuous_const ) ) _ _;
          · exact Continuous.intervalIntegrable ( by exact h_cont.comp ( continuous_id.prodMk continuous_const ) ) _ _;
        apply h_leibniz.congr_of_eventuallyEq
        filter_upwards
        intro a
        simp_all only [Set.mem_Icc, hasDerivAt_deriv_iff, and_imp]
      exact h_leibniz


/-
The integral of a smooth function F(t, x) with respect to t over [0, 1] is a smooth function of x.
-/
set_option linter.style.longLine false in
lemma contDiff_parametric_integral (F : ℝ → ℝ → ℝ) (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2)) :
    ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, F t x) := by
      refine' contDiff_infty.2 _;
      -- Apply the fact that the integral of a smooth function is smooth using the theorem `contDiff_integral_of_contDiff`.
      have h_int_smooth : ∀ n : ℕ, ContDiff ℝ n (fun x => ∫ t in (0 : ℝ)..1, F t x) := by
        intro n
        have h_cont_diff : ContDiff ℝ n (fun p : ℝ × ℝ => F p.1 p.2) := by
          -- Since $F$ is continuously differentiable up to order infinity, it is also continuously differentiable up to any finite order $n$.
          apply hF.of_le;
          exact ENat.LEInfty.out
        induction' n with n ih generalizing F <;> aesop;
        · fun_prop;
        · -- The derivative of the integral with respect to x is the integral of the partial derivative of F with respect to x.
          have h_deriv : ∀ x, HasDerivAt (fun x => ∫ t in (0 : ℝ)..1, F t x) (∫ t in (0 : ℝ)..1, deriv (fun y => F t y) x) x := by
            exact fun x ↦ deriv_integral_of_smooth F hF x;;
          -- Since the derivative of the integral function is the integral of the partial derivative of F, and the partial derivative of F is ContDiff ℝ n, the derivative of the integral function is ContDiff ℝ n.
          have h_deriv_cont_diff : ContDiff ℝ n (fun x => ∫ t in (0 : ℝ)..1, deriv (fun y => F t y) x) := by
            apply ih;
            · -- Since $F$ is $C^\infty$, its partial derivative with respect to $y$ is also $C^\infty$.
              have h_partial_deriv : ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun y => F p.1 y) p.2) := by
                have h_partial : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2) := hF
                apply_rules [ ContDiff.fderiv_apply ];
                -- The function (x, y) ↦ F x y is just the same as F, so we can use h_partial directly.
                apply h_partial.comp (contDiff_fst.fst.prodMk contDiff_snd);
                · exact contDiff_snd;
                · exact contDiff_const;
                · norm_num;
              exact h_partial_deriv;
            · apply_rules [ ContDiff.fderiv_apply ];
              any_goals exact le_rfl;
              · fun_prop;
              · exact contDiff_snd;
              · exact contDiff_const;
          rw [ contDiff_succ_iff_deriv ];
          exact ⟨ fun x => ( h_deriv x |> HasDerivAt.differentiableAt ), by aesop, by rw [ show deriv _ = _ from funext fun x => HasDerivAt.deriv ( h_deriv x ) ] ; exact h_deriv_cont_diff ⟩;
      assumption

set_option linter.style.longLine false in
lemma exists_smooth_flat_factor (f : ℝ → ℝ) (hsmooth : ContDiff ℝ ∞ f)
                          (hflat : ∀ k, iteratedDeriv k f 0 = 0) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ (∀ k, iteratedDeriv k g 0 = 0) ∧ ∀ x, f x = x * g x := by
      by_contra h_not;
      -- Since $f$ is flat at $0$, we can write $f(x) = x * g(x)$ for some smooth function $g$.
      obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ (∀ x, f x = x * g x) := by
        -- Let $g(x) = \int_0^1 f'(tx) dt$.
        set g : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..1, deriv f (t * x);
        -- By definition of $g$, we know that $f(x) = x * g(x)$ for all $x$.
        have hfg : ∀ x, f x = x * g x := by
          norm_num +zetaDelta at *;
          intro x; rw [ intervalIntegral.integral_deriv_eq_sub ];
          · specialize hflat 0 ; aesop;
          · exact fun t ht => hsmooth.contDiffAt.differentiableAt ( by norm_num );
          · -- Since $f$ is smooth, its derivative $f'$ is continuous, and hence integrable on any closed interval.
            have h_cont_deriv : Continuous (deriv f) := by
              -- Since $f$ is smooth, its derivative $f'$ is continuous by definition of smoothness.
              apply hsmooth.continuous_deriv; norm_num;
            exact h_cont_deriv.intervalIntegrable _ _;
        refine' ⟨ g, _, hfg ⟩;
        apply_rules [ contDiff_parametric_integral ];
        apply_rules [ ContDiff.fderiv_apply, hsmooth.comp ];
        · exact contDiff_snd;
        · exact contDiff_fst.mul contDiff_snd;
        · exact contDiff_const;
        · norm_num;
      refine' h_not ⟨ g, hg.1, _, hg.2 ⟩;
      -- By definition of $g$, we know that $f(x) = x * g(x)$, so we can write $f^{(k)}(x)$ as $x * g^{(k)}(x) + k * g^{(k-1)}(x)$.
      have h_deriv : ∀ k, deriv^[k] f = fun x => x * deriv^[k] g x + k * deriv^[k-1] g x := by
        intro k;
        induction k <;> aesop;
        erw [ Function.iterate_succ_apply', a ];
        ext x; erw [ deriv_add ] <;> norm_num [ left.contDiffAt.differentiableAt ];
        · erw [ deriv_mul ] <;> norm_num;
          · erw [ Function.iterate_succ_apply' ] ; ring;
            cases n <;> norm_num [ Function.iterate_succ_apply' ] ; ring;
          · have h_diff : ∀ n, ContDiff ℝ ∞ (deriv^[n] g) := by
              exact fun n ↦ ContDiff.iterate_deriv n left;
            exact ( h_diff n |> ContDiff.differentiable <| by norm_num ) x;
        · refine' DifferentiableAt.mul differentiableAt_id _;
          apply_rules [ ContDiff.differentiable ];
          apply_rules [ ContDiff.iterate_deriv ];
          norm_num;
        · refine' DifferentiableAt.const_mul _ _;
          apply_rules [ ContDiff.differentiable ];
          apply_rules [ ContDiff.iterate_deriv ];
          norm_num;
      intro k; specialize hflat ( k + 1 ) ; simp_all +decide [ iteratedDeriv_eq_iterate ] ;
      exact hflat.resolve_left <| by positivity;

-- set_option trace.profiler true in
set_option linter.style.longLine false in
set_option maxHeartbeats 400000 in
lemma contDiff_comp_sqrt_of_flat (f : ℝ → ℝ) (hsmooth : ContDiff ℝ ∞ f)
                                (hflat : ∀ k, iteratedDeriv k f 0 = 0) :
    ContDiff ℝ ∞ (fun x => f (Real.sqrt x)) := by
      -- Let's choose any $n \geq 0$.
      have h_cont_diff : ∀ n : ℕ, ContDiff ℝ n (fun x => f (Real.sqrt x)) := by
        -- We prove `ContDiff ℝ n` for all `n` by induction.
        intro n
        induction' n with n ih generalizing f;
        · exact contDiff_zero.2 <| hsmooth.continuous.comp <| Real.continuous_sqrt;
        · simp +zetaDelta at *;
          -- By `exists_smooth_flat_factor` applied to `f'`, there exists smooth flat `g` such that `f'(x) = x g(x)`.
          obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ (∀ k, iteratedDeriv k g 0 = 0) ∧ ∀ x, deriv f x = x * g x := by
            have := exists_smooth_flat_factor ( deriv f ) ?_ ?_;
            · exact this;
            · exact ContDiff.deriv' hsmooth
            · intro k
              convert hflat ( k + 1 ) using 1;
              rw [ iteratedDeriv_succ' ];
          -- We claim the derivative of $f(\sqrt{x})$ is $\frac{1}{2} g(\sqrt{x})$.
          have h_deriv : ∀ x, HasDerivAt (fun x => f (Real.sqrt x)) (if x = 0 then 0 else (1 / 2) * g (Real.sqrt x)) x := by
            intro x; split_ifs <;> simp_all +decide [ Real.sqrt_eq_rpow ] ;
            · -- By definition of $f$, we know that $f(\sqrt{h}) = \int_0^{\sqrt{h}} f'(t) dt = \int_0^{\sqrt{h}} t g(t) dt$.
              have h_int : ∀ h ≥ 0, f (Real.sqrt h) = ∫ t in (0 : ℝ)..Real.sqrt h, t * g t := by
                -- By the Fundamental Theorem of Calculus, we have $f(\sqrt{h}) - f(0) = \int_0^{\sqrt{h}} f'(t) dt$.
                have h_ftc : ∀ h ≥ 0, f (Real.sqrt h) - f 0 = ∫ t in (0 : ℝ)..Real.sqrt h, deriv f t := by
                  intro h hh; rw [ intervalIntegral.integral_deriv_eq_sub ] ;
                  intro x_1 a
                  simp_all only [ge_iff_le, sqrt_nonneg, Set.uIcc_of_le, Set.mem_Icc]
                  · exact hsmooth.contDiffAt.differentiableAt ( by norm_num );
                  · exact Continuous.intervalIntegrable ( by rw [ show deriv f = _ from funext hg.2.2 ] ; exact Continuous.mul continuous_id hg.1.continuous ) _ _;
                simp_all +decide only [ge_iff_le, sub_eq_iff_eq_add, add_eq_left];
                exact fun h hh => by simpa using hflat 0;
              -- By definition of $f$, we know that $f(\sqrt{h}) = h \int_0^1 u g(u\sqrt{h}) du$.
              have h_int_simplified : ∀ h ≥ 0, f (Real.sqrt h) = h * ∫ u in (0 : ℝ)..1, u * g (u * Real.sqrt h) := by
                intro h hh; rw [ h_int h hh ] ; by_cases hh' : Real.sqrt h = 0 <;> simp_all +decide [ mul_comm ] ;
                have h_int_simplified : ∀ a b : ℝ, 0 ≤ a → a ≤ b → ∫ t in a..b, t * g t = (∫ u in (a / Real.sqrt h).. (b / Real.sqrt h), (u * Real.sqrt h) * g (u * Real.sqrt h)) * Real.sqrt h := by
                  intros a b ha hb; rw [ mul_comm ] ; simp +decide [ div_eq_inv_mul] ;
                  convert intervalIntegral.integral_comp_div _ _ using 3 <;> ring <;> norm_num [ hh', hh ];
                rw [ h_int_simplified _ _ le_rfl ( Real.sqrt_nonneg _ ) ] ; norm_num [ hh, hh', mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] ; ring;
                norm_num [ mul_assoc, mul_left_comm, ← intervalIntegral.integral_const_mul, hh ];
                -- exact intervalIntegral.integral_congr fun x _ => by ring_nf; norm_num [ hh ] ; ring;
                apply intervalIntegral.integral_congr
                intro x hx
                simp_all only [le_refl, sqrt_nonneg, zero_div, zero_le_one, Set.uIcc_of_le, Set.mem_Icc]
                rw [← mul_assoc √h, mul_self_sqrt hh] ; ring_nf
              -- We need to show that the limit of the difference quotient as $h$ approaches $0$ is $0$.
              have h_limit : Filter.Tendsto (fun h => (∫ u in (0 : ℝ)..1, u * g (u * Real.sqrt h)) / 1) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
                -- Since $g$ is continuous at $0$, we have $\lim_{h \to 0} g(u \sqrt{h}) = g(0)$ for all $u \in [0, 1]$.
                have h_cont_g : ∀ u ∈ Set.Icc (0 : ℝ) 1, Filter.Tendsto (fun h => g (u * Real.sqrt h)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (g 0)) := by
                  exact fun u hu => tendsto_nhdsWithin_of_tendsto_nhds ( hg.1.continuous.continuousAt.tendsto.comp <| Continuous.tendsto' ( by continuity ) _ _ <| by aesop );
                -- By the Dominated Convergence Theorem, we can interchange the limit and the integral.
                have h_dominated : Filter.Tendsto (fun h => ∫ u in (0 : ℝ)..1, u * g (u * Real.sqrt h)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ u in (0 : ℝ)..1, u * g 0)) := by
                  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
                  use fun u => |u| * ( SupSet.sSup ( Set.image ( fun x => |g x| ) ( Set.Icc ( -1 ) 1 ) ) );
                  · exact Filter.Eventually.of_forall fun x => Continuous.aestronglyMeasurable ( by exact Continuous.mul continuous_id <| hg.1.continuous.comp <| by continuity );
                  · rw [ eventually_nhdsWithin_iff ] ;
                    rename_i h
                    subst h
                    simp_all only [ge_iff_le, Set.mem_Icc, and_imp, Set.mem_Ioi, zero_le_one, Set.uIoc_of_le,
                      Set.mem_Ioc, norm_mul, norm_eq_abs]
                    obtain ⟨left, right⟩ := hg
                    obtain ⟨left_1, right⟩ := right
                    filter_upwards [ gt_mem_nhds zero_lt_one ] with x hx₁ hx₂ using Filter.Eventually.of_forall fun y hy₁ hy₂ => mul_le_mul_of_nonneg_left ( le_csSup ( IsCompact.bddAbove ( isCompact_Icc.image ( show Continuous fun x => |g x| from continuous_abs.comp left.continuous ) ) ) <| Set.mem_image_of_mem _ <| by constructor <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt hx₂.le ] ) <| abs_nonneg _;
                  · exact Continuous.intervalIntegrable ( by continuity ) _ _;
                  · filter_upwards [ ] with x hx using Filter.Tendsto.mul tendsto_const_nhds ( h_cont_g x <| by constructor <;> cases Set.mem_uIoc.mp hx <;> linarith );
                have := hg.2.1 0;
                rename_i h
                subst h
                simp_all only [ge_iff_le, Set.mem_Icc, and_imp, intervalIntegral.integral_mul_const, integral_id,
                  one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, one_div, div_one]
                obtain ⟨left, right⟩ := hg
                obtain ⟨left_1, right⟩ := right
                specialize left_1 0; aesop;
              rw [ hasDerivAt_iff_tendsto_slope_zero ] ;
              rename_i h
              subst h
              simp_all only [ge_iff_le, div_one, zero_add, ne_eq, inv_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
                zero_rpow, smul_eq_mul]
              obtain ⟨left, right⟩ := hg
              obtain ⟨left_1, right⟩ := right
              rw [ Metric.tendsto_nhdsWithin_nhds ] at * ;
              intro ε a
              simp_all only [gt_iff_lt, Set.mem_Ioi, dist_zero_right, norm_eq_abs, Set.mem_compl_iff,
                Set.mem_singleton_iff, norm_mul, norm_inv]
              obtain ⟨ δ, hδ₁, hδ₂ ⟩ := h_limit ε a; use δ, hδ₁; intro x hx₁ hx₂; cases lt_or_gt_of_ne hx₁ <;> simp_all +decide [ Real.sqrt_eq_rpow ] ;
              · norm_num [ Real.rpow_def_of_neg ‹_› ] at * ;
                simp_all only [one_div]
                norm_num [ show 1 / 2 * Real.pi = Real.pi / 2 by ring, Real.exp_mul, Real.exp_log_eq_abs, hx₁ ] at * ; aesop;
              · rw [ inv_mul_eq_div, div_lt_iff₀ ] <;> have := h_int_simplified x ( by positivity ) <;> have := h_int_simplified 0 ( by positivity ) <;>
                simp_all only [ne_eq, inv_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, zero_rpow,
                  intervalIntegral.integral_same, abs_pos]
                expose_names
                rw [ ← h_int x h.le ] ; exact abs_lt.mpr ⟨ by cases abs_cases x <;> nlinarith [ abs_lt.mp ( hδ₂ h ( by simpa [ abs_of_pos h ] using hx₂ ) ) ], by cases abs_cases x <;> nlinarith [ abs_lt.mp ( hδ₂ h ( by simpa [ abs_of_pos h ] using hx₂ ) ) ] ⟩ ;
            · convert HasDerivAt.comp x ( hsmooth.contDiffAt.differentiableAt ( by norm_num ) |>
                DifferentiableAt.hasDerivAt ) ( HasDerivAt.rpow_const ( hasDerivAt_id x ) _ ) using 1 <;>
                simp_all only [id_eq, ne_eq, not_false_eq_true, true_or];
              by_cases hx : x < 0 <;> norm_num [ Real.rpow_def_of_neg, hx ] ; ring_nf;
              · norm_num [ mul_div ];
                simpa using hg.2.1 0;
              · expose_names
                rw [ Real.rpow_neg ( by linarith ) ] ; ring_nf;
                norm_num [ mul_comm, h, ne_of_gt ( Real.rpow_pos_of_pos ( lt_of_le_of_ne ( le_of_not_gt hx ) ( Ne.symm h ) ) _ ) ];
                rw [ mul_right_comm, mul_inv_cancel₀ ( ne_of_gt ( Real.rpow_pos_of_pos ( lt_of_le_of_ne ( le_of_not_gt hx ) ( Ne.symm h ) ) _ ) ), one_mul ];
          rw [ contDiff_succ_iff_deriv ];
          -- The derivative function is ContDiff ℝ n because it's a composition of smooth functions.
          have h_deriv_cont_diff : ContDiff ℝ n (fun x => (1 / 2) * g (Real.sqrt x)) := by
            exact ContDiff.mul contDiff_const ( ih g hg.1 hg.2.1 );
          simp_all only [one_div, WithTop.natCast_ne_top, analyticOn_univ, IsEmpty.forall_iff, true_and]
          obtain ⟨left, right⟩ := hg
          obtain ⟨left_1, right⟩ := right
          apply And.intro
          · exact fun x => ( h_deriv x |> HasDerivAt.differentiableAt );
          · convert h_deriv_cont_diff using 1;
            ext x; specialize h_deriv x; have := h_deriv.deriv;
            simp_all only [ite_eq_right_iff, sqrt_zero, zero_eq_mul, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
            intro a
            subst a
            simp_all only [↓reduceIte]
            simpa using left_1 0;
      exact contDiff_infty.mpr h_cont_diff

include hsmooth heven in
theorem Function.Even.eq_smooth_comp_sq_of_smooth : ∃ g : ℝ → ℝ, f = g ∘ (fun x => x ^ 2) ∧
    ContDiff ℝ ∞ g := by
  -- Apply `exists_smooth_even_approx` to get g₁.
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : ℝ → ℝ, ContDiff ℝ ∞ g₁ ∧ ∀ k, iteratedDeriv k
          (fun x => f x - g₁ (x ^ 2)) 0 = 0 := by
    exact exists_smooth_even_approx f heven hsmooth;
  -- Define $g₂(x) = h(\sqrt{x})$ where $h(x) = f(x) - g₁(x^2)$.
  set h : ℝ → ℝ := fun x => f x - g₁ (x ^ 2)
  have hg₂ : ContDiff ℝ ∞ (fun x => h (Real.sqrt x)) := by
    apply contDiff_comp_sqrt_of_flat;
    · exact hsmooth.sub ( hg₁.1.comp ( contDiff_id.pow 2 ) );
    · exact hg₁.2;
  use fun x => g₁ x + h ( Real.sqrt x );
  simp_all only [h]
  obtain ⟨left, right⟩ := hg₁
  apply And.intro
  · ext x
    rw [ comp, Real.sqrt_sq_eq_abs, abs_eq_max_neg, max_def ]
    simp_all only [le_neg_self_iff, ite_pow, even_two, Even.neg_pow, ite_self, add_sub_cancel]
    split
    next h_1 => exact Eq.symm (ext_cauchy (congrArg cauchy (heven x)))
    next h_1 => simp_all only [not_le]
  · exact ContDiff.add left hg₂;

end Even

namespace SchwartzMap

variable (𝕜)
variable [RCLike 𝕜]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

example (x : E) : x ∈ (⊤ : Set E) := trivial

def comp (f : 𝓢(E, F)) {g : D → E} {S : Set D} (hS : UniqueDiffOn ℝ S)
  (hf : ∀ x ∈ Sᶜ, ∀ n : ℕ, iteratedFDeriv ℝ n f (g x) = 0) (hg : g.HasTemperateGrowthOn S)
  (hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k) : 𝓢(D, F) where
  toFun := f ∘ g
  smooth' := by
    refine (f.smooth _).comp ?_

    sorry
  decay' := by
    suffices ∀ n : ℕ × ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ x ∈ S,
        ‖x‖ ^ n.fst * ‖iteratedFDeriv ℝ n.snd (f ∘ g) x‖ ≤
        C * s.sup (schwartzSeminormFamily 𝕜 E F) f by
      -- sorry
      intro k n
      rcases this ⟨k, n⟩ with ⟨s, C, _, h⟩
      use C * (s.sup (schwartzSeminormFamily 𝕜 E F)) f
      intro x
      if hx : x ∈ S then
      · exact h x hx
      else
      · specialize hf x hx n
        -- This simplifies greatly when Sᶜ = {0}, but I want to do it in general
        sorry
    -- stop
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
    intro x hx
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
    have hbound' (i) (hi : i ≤ n) :
        ‖iteratedFDerivWithin ℝ i f ⊤ (g x)‖ ≤ 2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k' := by
      -- This must be trivial, surely...
      sorry
    have hgrowth' (N : ℕ) (hN₁ : 1 ≤ N) (hN₂ : N ≤ n) :
        ‖iteratedFDerivWithin ℝ N g S x‖ ≤ ((C + 1) * (1 + ‖x‖) ^ l) ^ N := by
      stop
      refine (hgrowth N hN₂ x).trans ?_
      rw [mul_pow]
      have hN₁' := (lt_of_lt_of_le zero_lt_one hN₁).ne'
      gcongr
      · exact le_trans (by simp) (le_self_pow₀ (by simp [hC]) hN₁')
      · refine le_self_pow₀ (one_le_pow₀ ?_) hN₁'
        simp only [le_add_iff_nonneg_right, norm_nonneg]
    have hbound_aux_1 : UniqueDiffOn ℝ (⊤ : Set E) := by sorry
    have hbound_aux_2 : Set.MapsTo g S (⊤ : Set E) := fun _ _ ↦ trivial
    -- stop -- Proof I'm trying to generalise
    have := norm_iteratedFDerivWithin_comp_le (f.smooth ⊤).contDiffOn hg.1 (mod_cast le_top)
      hbound_aux_1 hS hbound_aux_2 hx hbound' hgrowth'
    have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (by simp only [zero_le_one, le_add_iff_nonneg_left]) _
    stop
    -- I think the cases on whether x ∈ S or not should be done way earlier.
    -- Also maybe S should just be the complement of zero... for convenience, if
    -- nothing else...
    grw [hxk, this]
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
    grw [hg_upper'', ← mul_assoc]
    -- End of proof
    stop
    sorry
    stop
    -- Proof I tried before I realised I had to do suffices hbound
    have := norm_iteratedFDerivWithin_comp_le (f.smooth ⊤).contDiffOn hg.1 (mod_cast le_top) (by sorry) hS (by sorry) trivial hbound hgrowth'
    have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (by simp only [zero_le_one, le_add_iff_nonneg_left]) _
    grw [hxk, this]
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
    grw [hg_upper'', ← mul_assoc]

    sorry

def compCLM_original {g : D → E} (hg : g.HasTemperateGrowth)
    (hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k) : 𝓢(E, F) →L[𝕜] 𝓢(D, F) := by
  refine mkCLM (fun f => f ∘ g) (fun _ _ _ => by simp) (fun _ _ _ => rfl)
    (fun f => (f.smooth ⊤).comp hg.1) ?_
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
    · exact le_trans (by simp) (le_self_pow₀ (by simp [hC]) hN₁')
    · refine le_self_pow₀ (one_le_pow₀ ?_) hN₁'
      simp only [le_add_iff_nonneg_right, norm_nonneg]
  have := norm_iteratedFDeriv_comp_le (f.smooth ⊤) hg.1 (mod_cast le_top) x hbound hgrowth'
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (by simp only [zero_le_one, le_add_iff_nonneg_left]) _
  grw [hxk, this]
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
  grw [hg_upper'', ← mul_assoc]

end SchwartzMap
