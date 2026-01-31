/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import Architect
import SpherePacking.MagicFunction.b.Schwartz

open SchwartzMap Real Complex MagicFunction.FourierEigenfunctions

namespace MagicFunction.b.SpecialValues

section Zero

@[blueprint
  "prop:b0"
  (statement := /--
  We have $b(0) = 0$.
  % \begin{equation}\label{eqn: b values}
  % b(0)=0\qquad
  % % b(\sqrt{2})=0\qquad
  % % b^\prime(\sqrt{2})=\frac{i}{2\sqrt{2}\,\pi}.
  % \end{equation}
  -/)
  (proof := /--
  These identities follow immediately from the previous proposition. % Mentioning this here because
  % this should not be -ed (yet).
  -/)
  (proofUses := ["prop:b-another-integral"])
  (latexEnv := "proposition")]
theorem b_zero : b 0 = 0 := by sorry

end Zero

end SpecialValues

end b

end MagicFunction
