import JanusFormal.Branches.JanusPTPhaseTransition.Gates.P0EFTJanusPT03ScaleNoGo
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedMinkowskiInteractionOpenDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatNuclearTraceSecondDerivative
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarScalarRemainderEnergyIdentity4D

namespace JanusFormal
namespace P0EFTJanusPTProgramPTechnicalBridge

set_option autoImplicit false

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusIntegratedMinkowskiInteractionOpenDomain4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D

/-- The regular holonomic scalar action on a general Lorentz metric has its
actual line derivative on the compact effective D8 quotient. It provides a
covariant order-parameter carrier, not a renormalized thermal potential. -/
def general_scalar_action_has_first_variation :=
  generalHolonomicScalarAction_line_hasDerivAt

/-- The same regular scalar functional has an exact line expansion with its
quadratic remainder. This exposes a controlled curvature carrier without
identifying it with a renormalized finite-temperature potential. -/
def general_scalar_action_has_quadratic_line_expansion :=
  generalHolonomicScalarAction_line_expansion

/-- The circle nuclear heat trace has a nonnegative second derivative at
positive heat time, providing a convex spectral contribution. It is not by
itself the renormalized Janus order-parameter potential. -/
def circle_heat_trace_second_variation_is_nonnegative :=
  P0EFTJanusCircleHeatNuclearTraceSecondDerivative.circleHeatNuclearTraceRealSecondDerivative_nonnegative

/-- The scalar remainder data produce an exact energy identity and its
coercive estimate. This controls the analytic remainder without selecting a
thermal vacuum or a critical temperature. -/
def scalar_remainder_energy_identity_certificate :=
  P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData.ScalarRemainderEnergyIdentityData.certificate

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
  generalLorentzScalarVariationClosed : Prop
  scalarQuadraticRemainderClosed : Prop
  spectralHeatTraceConvexityClosed : Prop
  scalarRemainderEnergyIdentityClosed : Prop
  renormalizedEffectivePotentialOpen : Prop
  physicalTemperatureLawOpen : Prop
  absoluteNormalizationOpen : Prop

end P0EFTJanusPTProgramPTechnicalBridge
end JanusFormal
