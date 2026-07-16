import JanusFormal.Branches.JanusPTPhaseTransition.Gates.P0EFTJanusPT03ScaleNoGo
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedMinkowskiInteractionOpenDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCandidateAFunctionalVariation4D

namespace JanusFormal
namespace P0EFTJanusPTProgramPTechnicalBridge

set_option autoImplicit false

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusIntegratedMinkowskiInteractionOpenDomain4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D

/-- On the smooth global D8 metric curve, P identifies the actual derivative
of the integrated Candidate-A action under its explicit domination contract. -/
def candidate_a_global_action_has_first_variation :=
  candidateAActionCurve_hasDerivAt

/-- Candidate A now supplies a genuine integrated PT-invariant interaction
functional on the local root domain. It is not yet the renormalized scalar
order-parameter potential used by PT01-PT03. -/
theorem candidate_a_integrated_interaction_is_pt_even
    {X : Type*} [MeasurableSpace X] (base : MeasuredPTBase X)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : PTMetricField X) :
    integratedCandidateAFunctional base.measure interactionScale coefficients
        (measuredPTMetricFieldExchange base field) =
      integratedCandidateAFunctional base.measure interactionScale
        coefficients field :=
  integratedCandidateAFunctional_measuredPTExchange
    base interactionScale coefficients field

structure PTBridgeBoundary where
  integratedPTInvariantInteractionClosed : Prop
  localMetricOrderParameterCandidateAvailable : Prop
  globalActionFirstVariationClosed : Prop
  renormalizedEffectivePotentialOpen : Prop
  physicalTemperatureLawOpen : Prop
  absoluteNormalizationOpen : Prop

end P0EFTJanusPTProgramPTechnicalBridge
end JanusFormal
