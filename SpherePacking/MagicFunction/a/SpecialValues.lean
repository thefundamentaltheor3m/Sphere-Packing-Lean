/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import Architect
import SpherePacking.MagicFunction.a.Schwartz

open SchwartzMap Real Complex MagicFunction.FourierEigenfunctions

namespace MagicFunction.a.SpecialValues

section Zero

@[blueprint
  "prop:a0"
  (statement := /--
  We have $a(0) = -\frac{i}{8640}$.
  % \begin{equation}
  % a(0)=\frac{-i\,8640}{\pi}\qquad
  % a(\sqrt{2})=0\qquad
  % a^\prime(\sqrt{2})=\frac{i\,72\sqrt{2}}{\pi}.
  % \end{equation}
  -/)
  (proof := /-- These identities follow immediately from the previous proposition. -/)
  (proofUses := ["prop:a-another-integral"])
  (latexEnv := "proposition")]
theorem a_zero : a 0 = -8640 * I / π := by sorry

end Zero
end MagicFunction.a.SpecialValues
