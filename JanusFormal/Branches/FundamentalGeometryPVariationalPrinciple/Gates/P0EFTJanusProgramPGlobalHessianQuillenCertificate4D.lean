import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianQuillenFamilyBridge4D

/-!
# Conditional global Quillen certificate

This file packages the exact output of the family bridge: a nonzero global
zeta determinant, a nowhere-vanishing section of the clutched determinant
line, parallelism for the Quillen connection, vanishing metric first variation
and endpoint clutching.

The certificate is conditional only on the family zeta continuation and its
connection/coefficient identification stored in the bridge data.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianQuillenCertificate4D

set_option autoImplicit false
set_option maxHeartbeats 10600000
set_option synthInstance.maxHeartbeats 5300000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace ComplexConjugate
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDeterminantLineFamily
open P0EFTJanusCircleQuillenMetricFlatConnection
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyBoundaryProjection4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalAgreement4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalCoerciveShift4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianConcreteAgreementClosure4D
open P0EFTJanusProgramPGlobalHessianZetaDeterminant4D
open P0EFTJanusProgramPGlobalHessianQuillenFamilyBridge4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Complete conditional Quillen output. -/
structure GlobalCandidateAHessianQuillenCertificate4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
      period hPeriod configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family))
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateAConcretePhysicalExtension period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family extensions))
    (fold : Fold)
    (bridge : GlobalCandidateAHessianQuillenFamilyBridgeData4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift fold) : Prop where
  basepointDeterminant_nonzero :
    globalCandidateAHessianZetaDeterminant bridge.basepointDeterminant ≠ 0
  section_nonzero : ∀ twist : CircleTwist,
    globalCandidateAHessianQuillenFamilySection bridge twist ≠ 0
  connection_parallel : ∀ parameter,
    circleQuillenConnectionAt fold
        (relativeZetaDeterminantCoordinate bridge.zetaFamily parameter)
        (relativeZetaDeterminantCoordinateDerivative bridge.zetaFamily
          parameter) = 0
  metricFirstVariation_zero : ∀ parameter,
    circleQuillenCoordinateMetricFirstVariation fold parameter
        (relativeZetaDeterminantCoordinate bridge.zetaFamily parameter)
        (relativeZetaDeterminantCoordinateDerivative bridge.zetaFamily
          parameter)
        (relativeZetaDeterminantCoordinate bridge.zetaFamily parameter)
        (relativeZetaDeterminantCoordinateDerivative bridge.zetaFamily
          parameter) = 0
  endpoint_clutching :
    circleLargeGaugeDeterminantTransition fold
        (globalCandidateAHessianQuillenFamilySection bridge unitCircleTwist) =
      globalCandidateAHessianQuillenFamilySection bridge periodicTwist

/-- Construction of the full conditional certificate. -/
def globalCandidateAHessianQuillenCertificate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {extensions : GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
      period hPeriod configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)}
    {shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateAConcretePhysicalExtension period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family extensions)}
    {fold : Fold}
    (bridge : GlobalCandidateAHessianQuillenFamilyBridgeData4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift fold) :
    GlobalCandidateAHessianQuillenCertificate4D period hPeriod configuration
      data analysis einsteinScale hBoundaryTransverse family extensions shift
        fold bridge where
  basepointDeterminant_nonzero :=
    globalCandidateAHessianZetaDeterminant_ne_zero
      bridge.basepointDeterminant
  section_nonzero :=
    globalCandidateAHessianQuillenFamilySection_ne_zero bridge
  connection_parallel := bridge.connectionBridge.circle_parallel
  metricFirstVariation_zero :=
    bridge.connectionBridge.metricFirstVariation_zero
  endpoint_clutching :=
    globalCandidateAHessianQuillenFamilySection_clutching bridge

/-- Terminal conditional Quillen gate. -/
theorem global_candidateA_hessian_quillen_certificate_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {extensions : GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
      period hPeriod configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)}
    {shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateAConcretePhysicalExtension period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family extensions)}
    {fold : Fold}
    (bridge : GlobalCandidateAHessianQuillenFamilyBridgeData4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift fold) :
    GlobalCandidateAHessianQuillenCertificate4D period hPeriod configuration
      data analysis einsteinScale hBoundaryTransverse family extensions shift
        fold bridge :=
  globalCandidateAHessianQuillenCertificate bridge

end
end P0EFTJanusProgramPGlobalHessianQuillenCertificate4D
end JanusFormal
