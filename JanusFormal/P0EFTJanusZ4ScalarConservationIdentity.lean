import JanusFormal.P0EFTJanusZ4ScalarClosure

namespace JanusFormal
namespace P0EFTJanusZ4ScalarConservationIdentity

set_option autoImplicit false

structure ScalarConservationIdentity where
  masterDensityPerturbationUsed : Prop
  masterVelocityDivergenceUsed : Prop
  continuityResidualClosed : Prop
  eulerResidualClosed : Prop
  projectedMetricSourceUsed : Prop
  noFictitiousCrossMetricForce : Prop
  coefficientsFromFullAction : Prop

def scalarConservationIdentityReady (s : ScalarConservationIdentity) : Prop :=
  s.masterDensityPerturbationUsed /\
  s.masterVelocityDivergenceUsed /\
  s.continuityResidualClosed /\
  s.eulerResidualClosed /\
  s.projectedMetricSourceUsed /\
  s.noFictitiousCrossMetricForce

def scalarConservationPhysicalReady (s : ScalarConservationIdentity) : Prop :=
  scalarConservationIdentityReady s /\
  s.coefficientsFromFullAction

theorem scalar_conservation_forbids_fictitious_cross_force
    (s : ScalarConservationIdentity)
    (h : scalarConservationIdentityReady s) :
    s.noFictitiousCrossMetricForce := by
  exact h.right.right.right.right.right

theorem scalar_conservation_does_not_replace_full_action
    (s : ScalarConservationIdentity)
    (_h : scalarConservationIdentityReady s)
    (hMissing : Not s.coefficientsFromFullAction) :
    Not (scalarConservationPhysicalReady s) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4ScalarConservationIdentity
end JanusFormal
