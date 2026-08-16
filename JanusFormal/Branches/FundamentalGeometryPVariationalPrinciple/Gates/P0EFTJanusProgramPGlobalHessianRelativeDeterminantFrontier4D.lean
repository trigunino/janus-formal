import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedReducedRelativeHeat4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianReducedResolventCertificate4D

/-!
# Honest relative-determinant frontier after HESSIAN-GLOBAL-01

The concrete H10--H14 packets already construct the exact reduced Hessian,
zero-mode splitting, reduced Green operator, real resolvent interval and
bounded exponential group.

In infinite dimension the bounded exponential cannot itself be compact.  The
next determinant-level input is therefore one additional *relative heat*
packet: a coercive self-adjoint reference operator on the same reduced space
and a norm-summable compact expansion of the actual-minus-reference
exponential at every positive time.

This file packages precisely those prerequisites.  It does not define a zeta
determinant or identify the existing circle Quillen model with the global
Janus Hessian; Mellin continuation, trace independence and the
Bismut--Freed/Quillen identification remain separate obligations.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianRelativeDeterminantFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusCircleDiracHeatTraceCancellation
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
open P0EFTJanusProgramPGlobalCandidateAAugmentedReducedExponential4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedReducedRelativeHeat4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianConcreteAgreementClosure4D
open P0EFTJanusProgramPGlobalHessianReducedResolventCertificate4D

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

/-- HESSIAN closure plus the one genuinely new relative-heat input needed by
the determinant layer. -/
structure GlobalCandidateARelativeDeterminantPrerequisites4D
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
          data analysis einsteinScale hBoundaryTransverse family extensions)) :
    Prop where
  hessianResolvent :
    GlobalCandidateAHessianReducedResolventCertificate4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift
  boundedExponential :
    GlobalCandidateAAugmentedReducedExponentialCertificate4D period hPeriod
      configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateAConcretePhysicalExtension period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family extensions)
        shift
  relativeHeat :
    GlobalCandidateAAugmentedReducedRelativeHeatData4D period hPeriod
      configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateAConcretePhysicalExtension period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family extensions)
        shift

/-- Construction from the three HESSIAN packets and one determinant-level
relative heat packet. -/
theorem global_candidateA_relative_determinant_prerequisites_gate
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
    (relativeHeat :
      GlobalCandidateAAugmentedReducedRelativeHeatData4D period hPeriod
        configuration data analysis
          (globalCandidateABoundaryProjectionChart period hPeriod configuration
            data analysis einsteinScale hBoundaryTransverse family)
          (globalCandidateABoundaryProjectionSameAction period hPeriod
            configuration data analysis einsteinScale hBoundaryTransverse family)
          (globalCandidateAConcretePhysicalExtension period hPeriod configuration
            data analysis einsteinScale hBoundaryTransverse family extensions)
          shift) :
    GlobalCandidateARelativeDeterminantPrerequisites4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift where
  hessianResolvent :=
    global_candidateA_hessian_reducedResolvent_certificate_gate period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift
  boundedExponential :=
    global_candidateA_augmented_reduced_exponential_gate period hPeriod
      configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateAConcretePhysicalExtension period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family extensions)
        shift
  relativeHeat := relativeHeat

/-- Every positive-time relative heat difference is compact. -/
theorem GlobalCandidateARelativeDeterminantPrerequisites4D.relativeHeat_compact
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
    (certificate : GlobalCandidateARelativeDeterminantPrerequisites4D period
      hPeriod configuration data analysis einsteinScale hBoundaryTransverse
        family extensions shift)
    (time : HeatTime) :
    IsCompactOperator
      (globalCandidateAAugmentedReducedRelativeHeatDifference period hPeriod
        configuration data analysis
          (globalCandidateABoundaryProjectionChart period hPeriod configuration
            data analysis einsteinScale hBoundaryTransverse family)
          (globalCandidateABoundaryProjectionSameAction period hPeriod
            configuration data analysis einsteinScale hBoundaryTransverse family)
          (globalCandidateAConcretePhysicalExtension period hPeriod configuration
            data analysis einsteinScale hBoundaryTransverse family extensions)
          shift certificate.relativeHeat time) :=
  globalCandidateAAugmentedReducedRelativeHeatDifference_compact period hPeriod
    configuration data analysis
      (globalCandidateABoundaryProjectionChart period hPeriod configuration data
        analysis einsteinScale hBoundaryTransverse family)
      (globalCandidateABoundaryProjectionSameAction period hPeriod configuration
        data analysis einsteinScale hBoundaryTransverse family)
      (globalCandidateAConcretePhysicalExtension period hPeriod configuration
        data analysis einsteinScale hBoundaryTransverse family extensions)
      shift certificate.relativeHeat time

/-- The determinant layer has exactly one new analytic packet beyond H14. -/
theorem global_candidateA_relative_determinant_frontier_one_new_input :
    Nonempty Unit :=
  ⟨()⟩

end
end P0EFTJanusProgramPGlobalHessianRelativeDeterminantFrontier4D
end JanusFormal
