/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib

@[expose] public section

namespace Function

variable {E F K : Type*} (r : E → K)

def InvariantUnder (f : E → F) : Prop := ∀ {x y : E}, r x = r y → f x = f y



end Function
