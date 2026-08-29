import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianFinitePartDeterminant4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeDeterminantPhase4D
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusCircleQuillenMetricFlatConnection

/-!
# Metric anchor from the reduced Candidate-A determinant to the Quillen line

The finite-part heat construction gives a positive determinant magnitude and a
unitary phase gives a nonzero complex determinant.  At the periodic basepoint
of the existing circle determinant line, the Fourier frame turns that scalar
into an actual line element.  Its Quillen norm square is exactly the square of
the global determinant magnitude.

This is a basepoint metric anchor only.  It does not identify the full global
Hessian family with the circle family, nor does it prove connection or
holonomy compatibility along parameter space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianQuillenMetricAnchor4D

set_option autoImplicit false
set_option maxHeartbeats 9200000
set_option synthInstance.maxHeartbeats 4600000

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
open P0EFTJanusProgramPRelativeDeterminantPhase4D

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

/-- Complex determinant scalar obtained from the concrete finite-part packet. -/
def globalCandidateAHessianComplexDeterminant
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
    (determinant : GlobalCandidateAHessianFinitePartDeterminantData4D period
      hPeriod configuration data analysis einsteinScale hBoundaryTransverse
        family extensions shift)
    (phase : RelativeDeterminantPhaseData) : Complex :=
  relativeHeatComplexDeterminant determinant.renormalization phase

/-- Actual determinant-line element at the periodic basepoint. -/
def globalCandidateAHessianQuillenMetricAnchor
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
    (determinant : GlobalCandidateAHessianFinitePartDeterminantData4D period
      hPeriod configuration data analysis einsteinScale hBoundaryTransverse
        family extensions shift)
    (phase : RelativeDeterminantPhaseData) :
    CircleDeterminantFiber fold periodicTwist :=
  circleDeterminantFrameEquiv fold periodicTwist
    (globalCandidateAHessianComplexDeterminant determinant phase)

/-- Fourier coordinate of the anchor is the global complex determinant. -/
@[simp]
theorem globalCandidateAHessianQuillenMetricAnchor_coordinate
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
    (determinant : GlobalCandidateAHessianFinitePartDeterminantData4D period
      hPeriod configuration data analysis einsteinScale hBoundaryTransverse
        family extensions shift)
    (phase : RelativeDeterminantPhaseData) :
    circleDeterminantCoordinate fold periodicTwist
        (globalCandidateAHessianQuillenMetricAnchor fold determinant phase) =
      globalCandidateAHessianComplexDeterminant determinant phase := by
  simp [globalCandidateAHessianQuillenMetricAnchor,
    circleDeterminantCoordinate]

/-- The periodic Quillen norm square is exactly the square of the positive
global determinant magnitude. -/
theorem globalCandidateAHessianQuillenMetricAnchor_normSq
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
    (determinant : GlobalCandidateAHessianFinitePartDeterminantData4D period
      hPeriod configuration data analysis einsteinScale hBoundaryTransverse
        family extensions shift)
    (phase : RelativeDeterminantPhaseData) :
    circleQuillenNormSq fold periodicTwist
        (globalCandidateAHessianQuillenMetricAnchor fold determinant phase) =
      (globalCandidateAHessianFinitePartDeterminant determinant) ^ 2 := by
  rw [circleQuillenNormSq, circleQuillenMetricWeight_zero,
    one_mul, globalCandidateAHessianQuillenMetricAnchor_coordinate]
  exact normSq_relativeHeatComplexDeterminant determinant.renormalization phase

/-- The anchor is nonzero. -/
theorem globalCandidateAHessianQuillenMetricAnchor_ne_zero
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
    (determinant : GlobalCandidateAHessianFinitePartDeterminantData4D period
      hPeriod configuration data analysis einsteinScale hBoundaryTransverse
        family extensions shift)
    (phase : RelativeDeterminantPhaseData) :
    globalCandidateAHessianQuillenMetricAnchor fold determinant phase ≠ 0 := by
  intro hZero
  have hCoordinate := congrArg
    (circleDeterminantCoordinate fold periodicTwist) hZero
  rw [globalCandidateAHessianQuillenMetricAnchor_coordinate] at hCoordinate
  simp [circleDeterminantCoordinate] at hCoordinate
  exact relativeHeatComplexDeterminant_ne_zero determinant.renormalization phase
    hCoordinate

/-- Public basepoint Quillen-metric anchor. -/
theorem global_candidateA_hessian_quillen_metric_anchor_gate
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
    (determinant : GlobalCandidateAHessianFinitePartDeterminantData4D period
      hPeriod configuration data analysis einsteinScale hBoundaryTransverse
        family extensions shift)
    (phase : RelativeDeterminantPhaseData) :
    globalCandidateAHessianQuillenMetricAnchor fold determinant phase ≠ 0 ∧
      circleQuillenNormSq fold periodicTwist
          (globalCandidateAHessianQuillenMetricAnchor fold determinant phase) =
        (globalCandidateAHessianFinitePartDeterminant determinant) ^ 2 :=
  ⟨globalCandidateAHessianQuillenMetricAnchor_ne_zero fold determinant phase,
    globalCandidateAHessianQuillenMetricAnchor_normSq fold determinant phase⟩

end
end P0EFTJanusProgramPGlobalHessianQuillenMetricAnchor4D
end JanusFormal
