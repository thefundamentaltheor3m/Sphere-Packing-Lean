/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import SpherePacking.MagicFunction.a.Schwartz

/-!
# Special Values of `a`

This file records special values of the function `a`.
-/

@[expose] public section

open SchwartzMap Real Complex MagicFunction.FourierEigenfunctions

namespace MagicFunction.a.SpecialValues

section Zero

theorem a_zero : a 0 = -8640 * I / π := by sorry

end Zero
end MagicFunction.a.SpecialValues
