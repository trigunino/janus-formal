import JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWStabilityCausalityGate
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedMinkowskiInteractionOpenDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalRootFrontierControl4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothPTFieldAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzTensorPTSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusScalarStressCovarianceExchangeCertificate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPBoundaryTangentGreenStokes4D

namespace JanusFormal
namespace P0EFTJanusGWProgramPTechnicalBridge

set_option autoImplicit false

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusIntegratedMinkowskiInteractionOpenDomain4D
open P0EFTJanusGlobalDiagonalRootFrontierControl4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D

/-- The genuine smooth symmetric covariant two-tensor pullback is globally
defined on D8 and involutive, with the analytic regularity obligation closed. -/
def smooth_general_tensor_pt_pullback_is_involutive :=
  P0EFTJanusMappingTorusGeneralLorentzTensorPTSmoothness4D.smoothPTTensorPullback_involutive

/-- P supplies an unconditional certificate combining scalar-stress covariance
with two-sector exchange. It fixes the source transformation law, not the
visible-matter content or waveform normalization. -/
theorem scalar_stress_covariance_exchange_certificate_exists
    (period : Real) (hPeriod : period ≠ 0) :
    Nonempty
      (P0EFTJanusScalarStressCovarianceExchangeCertificate4D.ScalarStressCovarianceExchangeCertificate4D
        period hPeriod) :=
  P0EFTJanusScalarStressCovarianceExchangeCertificate4D.scalarStressCovarianceExchange_unconditional
    period hPeriod

/-- Euler components of physical Program-P boundary tangents satisfy the
metric Green--Stokes identity and have zero cutoff divergence under the stated
scalar Euler hypotheses. This is the on-shell scalar boundary sector, not the
spin-2 wave equation. -/
def boundary_tangent_scalar_metric_green_stokes :=
  P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPBoundaryTangentGreenStokes4D.programPBoundaryTangents_metricGreenStokes_certificate

/-- The smooth two-sector coefficient fields now carry an exact involutive PT
exchange on the effective D8 quotient. This supplies the global symmetry
carrier for perturbations, not their covariant spin-2 Hessian. -/
def smooth_tensor_sector_exchange_is_involutive :=
  sectorExchange_involutive

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
  smoothPTSectorExchangeClosed : Prop
  smoothGeneralTensorPTActionClosed : Prop
  scalarStressCovarianceExchangeClosed : Prop
  boundaryTangentScalarGreenStokesClosed : Prop
  fullCovariantSecondVariationOpen : Prop
  physicalFLRWBackgroundOpen : Prop
  visibleMatterCouplingOpen : Prop

end P0EFTJanusGWProgramPTechnicalBridge
end JanusFormal
