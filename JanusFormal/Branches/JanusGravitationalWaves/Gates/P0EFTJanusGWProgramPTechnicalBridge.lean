import JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWStabilityCausalityGate
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedMinkowskiInteractionOpenDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalRootFrontierControl4D

namespace JanusFormal
namespace P0EFTJanusGWProgramPTechnicalBridge

set_option autoImplicit false

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusIntegratedMinkowskiInteractionOpenDomain4D
open P0EFTJanusGlobalDiagonalRootFrontierControl4D

/-- The selected global diagonal root has controlled closed-minus frontier,
and its zero-spectrum faces are exactly identified. This is the global root
input for the next tensor analysis, not yet its physical Hessian. -/
def global_diagonal_root_frontier_is_controlled :=
  global_diagonal_root_frontier_control_closure

/-- Program P now supplies an actual integrated Candidate-A interaction on a
measured PT base, invariant under the full measured PT exchange. -/
theorem candidate_a_interaction_functional_is_pt_invariant
    {X : Type*} [MeasurableSpace X] (base : MeasuredPTBase X)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : PTMetricField X) :
    integratedCandidateAFunctional base.measure interactionScale coefficients
        (measuredPTMetricFieldExchange base field) =
      integratedCandidateAFunctional base.measure interactionScale
        coefficients field :=
  integratedCandidateAFunctional_measuredPTExchange
    base interactionScale coefficients field

structure GWBridgeBoundary where
  integratedLocalInteractionClosed : Prop
  measuredPTInvarianceClosed : Prop
  globalDiagonalRootFrontierClosed : Prop
  fullCovariantSecondVariationOpen : Prop
  physicalFLRWBackgroundOpen : Prop
  visibleMatterCouplingOpen : Prop

end P0EFTJanusGWProgramPTechnicalBridge
end JanusFormal
