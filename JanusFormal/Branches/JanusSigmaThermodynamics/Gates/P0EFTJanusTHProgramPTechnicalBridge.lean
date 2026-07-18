import JanusFormal.Branches.JanusSigmaThermodynamics.Gates.P0EFTJanusTH05QuantumEntropyBridge
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedMinkowskiInteractionOpenDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusInducedFieldVariation4D

namespace JanusFormal
namespace P0EFTJanusTHProgramPTechnicalBridge

set_option autoImplicit false

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusIntegratedMinkowskiInteractionOpenDomain4D
open P0EFTJanusMappingTorusInducedFieldVariation4D

/-- Gauge, ghost, auxiliary and LL-only directions have exactly zero response
in the induced metric/matter package. This isolates the sectors that may feed
future physical balance currents. -/
def non_metric_matter_induced_response_is_zero :=
  induced_cross_response_zero

/-- The integrated Candidate-A metric first variation is invariant under the
measured PT exchange. This is a geometric variational input, not yet an energy
or entropy current. -/
theorem candidate_a_first_variation_is_pt_invariant
    {X : Type*} [MeasurableSpace X] (base : MeasuredPTBase X)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : PTMetricField X) (variation : MetricPairFieldVariation X) :
    integratedCandidateAFirstVariation base.measure interactionScale
        coefficients (measuredPTMetricFieldExchange base field)
        (measuredPTMetricVariationExchange base variation) =
      integratedCandidateAFirstVariation base.measure interactionScale
        coefficients field variation :=
  integratedCandidateAFirstVariation_measuredPTExchange
    base interactionScale coefficients field variation

structure THBridgeBoundary where
  measuredPTBaseClosed : Prop
  interactionVariationPTInvariant : Prop
  inducedSectorVariationChainClosed : Prop
  nonMetricMatterCrossResponseClosed : Prop
  physicalEnergyCurrentsOpen : Prop
  transportCoefficientsOpen : Prop
  quantumStateLawOpen : Prop

end P0EFTJanusTHProgramPTechnicalBridge
end JanusFormal
