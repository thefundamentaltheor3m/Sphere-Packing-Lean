/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.NormNum

/-!
# `fin_vec_simp` tactic

Evaluates goals about `Fin`-indexed vector/matrix literals (`![...]`, `!![...]`): matrix
products, `vecMul`/`mulVec`, `dotProduct`, entrywise equalities, and `∀ i : Fin n` /
`∑ i : Fin n` over literals. It bundles the standard unfolding lemmas (`Matrix.mul_apply`,
`Fin.sum_univ_succ`, `Fin.forall_fin_succ`, the `Matrix.cons_val` and
`vecMul_cons`/`dotProduct_cons` recursion families, ...) into one `norm_num +decide`
call, so entries are evaluated over any commutative ring with numeric literals — in
particular over `ℝ`/`ℂ`/abstract fields where `decide` is unavailable — and is immune to
renamings of `Fin.sum_univ_eight`-style lemmas. For *fully literal* `ℚ`/`ℤ` goals
(e.g. `E8Inverse ℚ * E8Matrix ℚ = 1`) `decide +kernel` can still be the better choice:
`fin_vec_simp` handles such 8×8 products in isolation, but the proof terms grow large.

* `fin_vec_simp [foo]` adds extra simp lemmas (e.g. local matrix definitions to unfold);
* `fin_vec_simp at h ⊢` works at hypotheses.
-/

@[expose] public section

/-- `fin_vec_simp` evaluates `Fin`-indexed vector/matrix literal goals: matrix products,
`vecMul`/`mulVec`/`dotProduct` against `![...]`/`!![...]` literals, entrywise equalities
(via `funext_iff`/`Matrix.ext_iff` + `Fin.forall_fin_succ`), and `∑ i : Fin n` sums.
Extra simp lemmas (e.g. matrix definitions to unfold) may be passed in brackets. -/
syntax (name := finVecSimpTac) "fin_vec_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")?
  (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| fin_vec_simp $[$loc:location]?) =>
    `(tactic| norm_num +decide [← Matrix.ext_iff, funext_iff, Fin.forall_fin_succ,
        Fin.forall_fin_one, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.mul_apply,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons, Matrix.one_apply,
        Matrix.of_apply, Matrix.map_apply, Matrix.transpose_apply, Fin.succ_ne_zero,
        Fin.succ_inj, Matrix.cons_vecMul, Matrix.vecMul_cons, Matrix.empty_vecMul,
        Matrix.vecMul_empty, Matrix.cons_mulVec, Matrix.mulVec_cons, Matrix.empty_mulVec,
        Matrix.mulVec_empty, Matrix.cons_dotProduct, Matrix.dotProduct_cons,
        Matrix.dotProduct_of_isEmpty, Matrix.smul_cons, Matrix.smul_empty, Matrix.vecHead,
        Matrix.vecTail, Function.comp_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul] $[$loc:location]?)
  | `(tactic| fin_vec_simp [$ls,*] $[$loc:location]?) =>
    `(tactic| norm_num +decide [← Matrix.ext_iff, funext_iff, Fin.forall_fin_succ,
        Fin.forall_fin_one, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.mul_apply,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons, Matrix.one_apply,
        Matrix.of_apply, Matrix.map_apply, Matrix.transpose_apply, Fin.succ_ne_zero,
        Fin.succ_inj, Matrix.cons_vecMul, Matrix.vecMul_cons, Matrix.empty_vecMul,
        Matrix.vecMul_empty, Matrix.cons_mulVec, Matrix.mulVec_cons, Matrix.empty_mulVec,
        Matrix.mulVec_empty, Matrix.cons_dotProduct, Matrix.dotProduct_cons,
        Matrix.dotProduct_of_isEmpty, Matrix.smul_cons, Matrix.smul_empty, Matrix.vecHead,
        Matrix.vecTail, Function.comp_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul, $ls,*] $[$loc:location]?)
