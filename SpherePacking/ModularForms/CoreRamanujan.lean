import SpherePacking.ModularForms.Derivative

/-!
# Boundedness of Eisenstein Series Derivatives

Boundedness results for derivatives of Eisenstein series, to be extended with
Ramanujan's identities in future work.

## Main results

* `serre_D_isBoundedAtImInfty` : serre_D k f is bounded for bounded holomorphic f
* `D_E₄_isBoundedAtImInfty` : D(E₄) is bounded at infinity
* `serre_D_E₄_isBoundedAtImInfty` : serre_D 4 E₄ is bounded at infinity
-/

open UpperHalfPlane hiding I
open Real Complex Filter ModularForm

open scoped ModularForm Topology Manifold

noncomputable section

/-- The Serre derivative of a bounded holomorphic function is bounded at infinity.

serre_D k f = D f - (k/12)·E₂·f. Both terms are bounded:
- D f is bounded by `D_isBoundedAtImInfty_of_bounded`
- (k/12)·E₂·f is bounded since E₂ and f are bounded -/
theorem serre_D_isBoundedAtImInfty {f : ℍ → ℂ} (k : ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) : IsBoundedAtImInfty (serre_D k f) := by
  unfold serre_D
  have hD : IsBoundedAtImInfty (D f) := D_isBoundedAtImInfty_of_bounded hf hbdd
  have hE₂f : IsBoundedAtImInfty (fun z => k * 12⁻¹ * E₂ z * f z) := by
    have hconst : IsBoundedAtImInfty (fun _ : ℍ => k * 12⁻¹) :=
      Filter.const_boundedAtFilter _ _
    convert hconst.mul (E₂_isBoundedAtImInfty.mul hbdd) using 1
    ext z
    simp only [Pi.mul_apply]
    ring
  exact hD.sub hE₂f

/-- D E₄ is bounded at infinity.

Follows from `D_isBoundedAtImInfty_of_bounded` since E₄ is holomorphic and bounded at infinity. -/
lemma D_E₄_isBoundedAtImInfty : IsBoundedAtImInfty (D E₄.toFun) :=
  D_isBoundedAtImInfty_of_bounded E₄.holo' (ModularFormClass.bdd_at_infty E₄)

/-- serre_D 4 E₄ is bounded at infinity. -/
lemma serre_D_E₄_isBoundedAtImInfty : IsBoundedAtImInfty (serre_D 4 E₄.toFun) :=
  serre_D_isBoundedAtImInfty 4 E₄.holo' (ModularFormClass.bdd_at_infty E₄)

end
