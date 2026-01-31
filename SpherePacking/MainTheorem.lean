import Architect
import SpherePacking.Basic.E8

open SpherePacking E8

@[blueprint
  "MainTheorem"
  (statement := /-- $\Delta_8 = \Delta_{E_8}$. -/)
  (proof := /--
  By definition, $\Delta_{E_8} \leq \Delta_8$, while \cref{corollary:upper-bound-E8} shows $\Delta_8
  = \sup_{\mathrm{packing} \, \mathcal{P}} \leq \Delta_{E_8}$, and the result follows.
  -/)
  (proofUses := ["corollary:upper-bound-E8"])
  (latexEnv := "corollary")]
theorem SpherePacking.MainTheorem : SpherePackingConstant 8 = E8Packing.density :=
  sorry
