import SpherePacking.ModularForms.Derivative

/-!
# Boundedness of E₄ Derivatives

Boundedness results for derivatives of E₄, to be extended with Ramanujan's identities
in future work.

## Main results

* `D_E₄_isBoundedAtImInfty` : D(E₄) is bounded at infinity
* `serre_D_E₄_isBoundedAtImInfty` : serre_D 4 E₄ is bounded at infinity
-/

open UpperHalfPlane hiding I
open Real Complex Filter ModularForm

open scoped ModularForm Topology Manifold

noncomputable section

/-- D E₄ is bounded at infinity.

Follows from `D_isBoundedAtImInfty_of_bounded` since E₄ is holomorphic and bounded at infinity. -/
lemma D_E₄_isBoundedAtImInfty : IsBoundedAtImInfty (D E₄.toFun) :=
  D_isBoundedAtImInfty_of_bounded E₄.holo' (ModularFormClass.bdd_at_infty E₄)

/-- serre_D 4 E₄ is bounded at infinity. -/
lemma serre_D_E₄_isBoundedAtImInfty : IsBoundedAtImInfty (serre_D 4 E₄.toFun) :=
  serre_D_isBoundedAtImInfty 4 E₄.holo' (ModularFormClass.bdd_at_infty E₄)

end
