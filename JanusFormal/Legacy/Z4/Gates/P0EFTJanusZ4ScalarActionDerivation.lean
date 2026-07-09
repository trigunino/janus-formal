import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4BackgroundActionDerivation
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4ScalarConservationIdentity

namespace JanusFormal
namespace P0EFTJanusZ4ScalarActionDerivation

set_option autoImplicit false

structure ScalarActionDerivation where
  newtonianGaugeProjectionDeclared : Prop
  poissonCoefficientDerived : Prop
  momentumCoefficientDerived : Prop
  slipCoefficientDerived : Prop
  continuityEulerFromWardCurrent : Prop
  scalarBianchiResidualVanishes : Prop
  noFictitiousCrossMetricForce : Prop

def scalarActionDerivedReady (s : ScalarActionDerivation) : Prop :=
  s.newtonianGaugeProjectionDeclared /\
  s.poissonCoefficientDerived /\
  s.momentumCoefficientDerived /\
  s.slipCoefficientDerived /\
  s.continuityEulerFromWardCurrent /\
  s.scalarBianchiResidualVanishes /\
  s.noFictitiousCrossMetricForce

theorem scalar_action_derivation_gives_slip_coefficient
    (s : ScalarActionDerivation)
    (h : scalarActionDerivedReady s) :
    s.slipCoefficientDerived := by
  exact h.right.right.right.left

theorem scalar_action_derivation_forbids_cross_metric_force
    (s : ScalarActionDerivation)
    (h : scalarActionDerivedReady s) :
    s.noFictitiousCrossMetricForce := by
  exact h.right.right.right.right.right.right

end P0EFTJanusZ4ScalarActionDerivation
end JanusFormal
