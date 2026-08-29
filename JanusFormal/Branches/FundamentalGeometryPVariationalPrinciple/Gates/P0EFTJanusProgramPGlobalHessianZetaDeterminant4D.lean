import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianQuillenParallelSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaComparison4D

/-!
# Complex zeta determinant of the reduced Candidate-A Hessian

A finite-part determinant packet and a zeta continuation regular at zero now
produce the full nonzero complex determinant.  Its normalized phase feeds the
existing Quillen metric anchor and parallel circle section automatically.

The remaining global Quillen problem is no longer the existence of a scalar or
line element.  It is the family-level identification of the Janus Hessian
parameter space with the circle determinant-line model and the compatibility
of their analytic connections.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianZetaDeterminant4D

set_option autoImplicit false
set_option maxHeartbeats 9800000
set_option synthInstance.maxHeartbeats 4900000

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
open P0EFTJanusProgramPGlobalHessianFinitePartDeterminant4D
open P0EFTJanusProgramPGlobalHessianQuillenMetricAnchor4D
open P0EFTJanusProgramPGlobalHessianQuillenParallelSection4D
open P0EFTJanusProgramPRelativeZetaComparison4D

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

/-- Complex determinant packet after zeta comparison. -/
structure GlobalCandidateAHessianZetaDeterminantData4D
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
          data analysis einsteinScale hBoundaryTransverse family extensions)) where
  finitePart : GlobalCandidateAHessianFinitePartDeterminantData4D period hPeriod
    configuration data analysis einsteinScale hBoundaryTransverse family
      extensions shift
  zetaComparison : RelativeZetaComparisonData finitePart.renormalization

/-- Full complex relative zeta determinant. -/
def globalCandidateAHessianZetaDeterminant
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
    (certificate : GlobalCandidateAHessianZetaDeterminantData4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift) : Complex :=
  relativeZetaDeterminant certificate.zetaComparison

/-- The complex determinant is nonzero. -/
theorem globalCandidateAHessianZetaDeterminant_ne_zero
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
    (certificate : GlobalCandidateAHessianZetaDeterminantData4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift) :
    globalCandidateAHessianZetaDeterminant certificate ≠ 0 :=
  relativeZetaDeterminant_ne_zero certificate.zetaComparison

/-- Its norm is the positive finite-part determinant. -/
theorem norm_globalCandidateAHessianZetaDeterminant
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
    (certificate : GlobalCandidateAHessianZetaDeterminantData4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift) :
    ‖globalCandidateAHessianZetaDeterminant certificate‖ =
      globalCandidateAHessianFinitePartDeterminant certificate.finitePart :=
  norm_relativeZetaDeterminant certificate.zetaComparison

/-- The zeta derivative supplies the exact unitary phase packet. -/
def GlobalCandidateAHessianZetaDeterminantData4D.phase
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
    (certificate : GlobalCandidateAHessianZetaDeterminantData4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift) : RelativeDeterminantPhaseData :=
  certificate.zetaComparison.toPhase

/-- Parallel Quillen section generated without an independent phase input. -/
def globalCandidateAHessianZetaQuillenSection
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
    (fold : Fold)
    (certificate : GlobalCandidateAHessianZetaDeterminantData4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift)
    (twist : CircleTwist) : CircleDeterminantFiber fold twist :=
  globalCandidateAHessianQuillenParallelSection fold certificate.finitePart
    certificate.phase twist

/-- The zeta section has constant Quillen norm and exact endpoint holonomy. -/
theorem global_candidateA_hessian_zeta_determinant_gate
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
    (fold : Fold)
    (certificate : GlobalCandidateAHessianZetaDeterminantData4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift) :
    globalCandidateAHessianZetaDeterminant certificate ≠ 0 ∧
      (∀ twist : CircleTwist,
        circleQuillenNormSq fold twist
            (globalCandidateAHessianZetaQuillenSection fold certificate twist) =
          (globalCandidateAHessianFinitePartDeterminant
            certificate.finitePart) ^ 2) ∧
      circleLargeGaugeDeterminantTransition fold
          (globalCandidateAHessianZetaQuillenSection fold certificate
            unitCircleTwist) =
        circleQuillenClosedHolonomy fold •
          globalCandidateAHessianQuillenMetricAnchor fold certificate.finitePart
            certificate.phase := by
  exact
    ⟨globalCandidateAHessianZetaDeterminant_ne_zero certificate,
      globalCandidateAHessianQuillenParallelSection_normSq fold
        certificate.finitePart certificate.phase,
      globalCandidateAHessianQuillenParallelSection_endpoint_clutching fold
        certificate.finitePart certificate.phase⟩

end
end P0EFTJanusProgramPGlobalHessianZetaDeterminant4D
end JanusFormal
