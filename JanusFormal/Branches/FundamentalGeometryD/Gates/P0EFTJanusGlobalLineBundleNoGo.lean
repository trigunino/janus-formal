import Mathlib

namespace JanusFormal
namespace P0EFTJanusGlobalLineBundleNoGo

set_option autoImplicit false

/-- The minimal mapping-torus cellular model has no degree-two integral cell. -/
abbrev DegreeTwoIntegralCochain := Fin 0 → ℤ

/-- Every degree-two integral cellular cochain is zero. -/
theorem every_degree_two_integral_cochain_vanishes
    (c : DegreeTwoIntegralCochain) :
    c = 0 := by
  funext i
  exact Fin.elim0 i

/-- A cellular first-Chern representative is therefore trivial. -/
theorem every_cellular_first_chern_class_vanishes
    (c1 : DegreeTwoIntegralCochain) :
    c1 = 0 :=
  every_degree_two_integral_cochain_vanishes c1

/--
After comparison with singular cohomology and the classification of complex
line bundles by `H^2(-;Z)`, this yields a second no-go: the full twisted-Hopf
four-manifold cannot carry a topologically nontrivial ordinary complex line
bundle.  The nontrivial monopole bundle must live on the throat, use twisted
coefficients, or arise as a boundary/transgression object.
-/
structure GlobalLineBundleNoGoStatus where
  cellularH2IntegralVanishes : Prop
  cellularToSingularH2IsomorphismDerived : Prop
  complexLineBundlesClassifiedByH2 : Prop
  allGlobalComplexLineBundlesTopologicallyTrivial : Prop
  throatRestrictionCanBeNontrivial : Prop
  twistedO2AlternativeAvailable : Prop


def globalLineBundleNoGoClosed
    (s : GlobalLineBundleNoGoStatus) : Prop :=
  s.cellularH2IntegralVanishes /\
  s.cellularToSingularH2IsomorphismDerived /\
  s.complexLineBundlesClassifiedByH2 /\
  s.allGlobalComplexLineBundlesTopologicallyTrivial /\
  s.throatRestrictionCanBeNontrivial /\
  s.twistedO2AlternativeAvailable

end P0EFTJanusGlobalLineBundleNoGo
end JanusFormal
