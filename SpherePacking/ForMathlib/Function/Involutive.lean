/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Logic.Function.Basic

@[expose] public section

namespace Function.Involutive

lemma apply_apply {α : Type*} {f : α → α} (hf : Involutive f) {x : α} :
  f (f x) = x := by rw [← f.comp_apply, hf.comp_self, id_eq]

-- Consider mimicking `StarModule.decomposeProdAdjoint` and other such `StarModule` designs to get
-- Symmetric + Antisymmetric decomposition lemmas for involutive maps on additive commutative
-- groups, vector spaces, etc.

/-
section AddCommGroup

variable {G : Type*} [AddCommGroup G] {f : G →+ G}

def Symmetric (hf : Involutive f) (x : G) : Prop := f x = x

def Antisymmetric (hf : Involutive f) (x : G) : Prop := f x = -x

#check fixedPoints

lemma map_add_apply (hf : Involutive f) (x : G) : f (x + f x) = x + f x := by
  rw [map_add, hf.apply_apply, add_comm]

lemma map_sub_apply (hf : Involutive f) (x : G) : f (x - f x) = -(x - f x) := by
  rw [sub_eq_add_neg, map_add, map_neg, hf.apply_apply]
  abel

lemma decomposition (hf : Involutive f) (x : G) : 2 • x = (x + f x) + (x - f x) := by abel

end AddCommGroup
-/

end Function.Involutive
