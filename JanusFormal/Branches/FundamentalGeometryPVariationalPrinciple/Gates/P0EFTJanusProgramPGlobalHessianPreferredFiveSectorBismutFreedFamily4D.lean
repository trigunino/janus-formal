import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorIntrinsicQuillenClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementBismutFreedFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeBismutFreedCircleTraceBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointUniformGapFamilyResolvent4D

/-!
# Preferred Candidate-A Bismut--Freed family after H14

The intrinsic Quillen closure currently carries a differentiable scalar Mellin
family.  This file supplies its missing operator origin.

A family of genuine augmented Candidate-A Hessians is equipped with a unitary
trivialization of the varying actual-kernel complements.  The transported
reduced family has a uniform gap, a differentiable Green family and intrinsic
nuclear logarithmic derivatives.  Its relative trace is required to equal the
zeta connection coefficient already used by the intrinsic Quillen atlas.

At parameter zero the full family is the concrete Candidate-A Hessian of the
preferred H14 closure.  Thus the Green, resolvent, determinant connection,
circle clutching and phase holonomy all belong to one operator family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D

set_option autoImplicit false
set_option maxHeartbeats 19000000
set_option synthInstance.maxHeartbeats 9500000

noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusCircleQuillenMetricFlatConnection
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalSmallness4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorIntrinsicQuillenAtlas4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorIntrinsicQuillenClosure4D
open P0EFTJanusProgramPRelativeBismutFreedCircleTraceBridge4D
open P0EFTJanusProgramPRelativeBismutFreedTraceConnection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeZetaFinitePartFamily4D
open P0EFTJanusProgramPSelfAdjointKernelComplementBismutFreedFamily4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointUniformGapFamilyResolvent4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

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

variable {measure : Measure (EffectiveQuotient period hPeriod)}

def GlobalHessianPreferredFiveSectorBismutFreedHilbert4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) candidateAHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
        configuration data analysis) := by
  unfold GlobalHessianPreferredFiveSectorBismutFreedHilbert4D
  exact P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
        configuration data analysis) := by
  unfold GlobalHessianPreferredFiveSectorBismutFreedHilbert4D
  exact P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
        configuration data analysis) := by
  unfold GlobalHessianPreferredFiveSectorBismutFreedHilbert4D
  exact P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
        configuration data analysis) := by
  unfold GlobalHessianPreferredFiveSectorBismutFreedHilbert4D
  exact P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
        configuration data analysis) := by
  unfold GlobalHessianPreferredFiveSectorBismutFreedHilbert4D
  exact P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

private abbrev CanonicalChart
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :=
  globalCandidateAActualKernelChart period hPeriod configuration data analysis
    einsteinScale hTransverse family

private abbrev CanonicalSameAction
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :=
  globalCandidateAActualKernelSameAction period hPeriod configuration data
    analysis einsteinScale hTransverse family

private abbrev CanonicalPhysical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))) :=
  globalCandidateACanonicalSixPhysicalExtension_of_chartBound period hPeriod
    configuration data analysis einsteinScale hTransverse family chartBound

private abbrev CanonicalOperator
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))) :=
  globalCandidateAActualKernelOperator period hPeriod configuration data analysis
    (CanonicalChart period hPeriod einsteinScale hTransverse family)
    (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
    (CanonicalPhysical period hPeriod einsteinScale hTransverse family chartBound)

/-- Candidate-A intrinsic Quillen atlas with its actual/reference operator
family and intrinsic Bismut--Freed trace formula. -/
structure GlobalHessianPreferredFiveSectorBismutFreedFamily4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family)))
    (Metric Abelian Matter Longitudinal Boundary : Type*)
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (ZeroMode : Type) [Fintype ZeroMode] [DecidableEq ZeroMode]
    (fold : Fold) (Index : Type*) where
  quillen : GlobalHessianPreferredFiveSectorIntrinsicQuillenAtlas4D period
    hPeriod configuration data analysis einsteinScale hTransverse family
      chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index
  actualOperator : Real →
    GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
        configuration data analysis →L[Real]
      GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
        configuration data analysis
  actual_zero : actualOperator 0 =
    CanonicalOperator period hPeriod einsteinScale hTransverse family chartBound
  referenceOperator : Real →
    SelfAdjointKernelComplement (actualOperator 0) →L[Real]
      SelfAdjointKernelComplement (actualOperator 0)
  familyIndex : SelfAdjointKernelComplementBismutFreedFamilyData.{0, 0}
    actualOperator referenceOperator
  zetaFamily_eq :
    familyIndex.zetaFamily = quillen.intrinsicFamily.mellinFamily
  coefficient_eq_circle : ∀ parameter,
    familyIndex.toBismutFreed.operatorTrace.bismutFreedCoefficient parameter =
      (circleQuillenConnectionCoefficient fold : Complex)

namespace GlobalHessianPreferredFiveSectorBismutFreedFamily4D

/-- Intrinsic trace/circle bridge generated from the Candidate-A family. -/
def toCircleTraceBridge
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}
    (input : GlobalHessianPreferredFiveSectorBismutFreedFamily4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    RelativeBismutFreedCircleTraceBridgeData
      input.familyIndex.actualGap.fixedOperator input.referenceOperator fold where
  bismutFreed := input.familyIndex.toBismutFreed
  coefficient_eq_circle := input.coefficient_eq_circle
  endpoint_clutching := by
    have hEndpoint := input.quillen.circleBridge.endpoint_clutching
    rw [← input.zetaFamily_eq] at hEndpoint
    exact hEndpoint

/-- Base reduced family is the genuine Candidate-A actual-kernel operator. -/
theorem fixedOperator_zero_eq_actual
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}
    (input : GlobalHessianPreferredFiveSectorBismutFreedFamily4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    input.familyIndex.actualGap.fixedOperator 0 =
      selfAdjointKernelComplementOperator
        (input.actualOperator 0)
        (input.familyIndex.actual_selfAdjoint 0) :=
  input.familyIndex.fixedOperator_zero

/-- Uniform absence of zero crossings in the transported reduced family. -/
theorem noCrossing
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}
    (input : GlobalHessianPreferredFiveSectorBismutFreedFamily4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    UniformGapFamilyNoCrossingCertificate
      input.familyIndex.actualDifferentiable.analytic :=
  uniformGapFamily_noCrossing input.familyIndex.actualDifferentiable.analytic

/-- Terminal family-index output. -/
structure GlobalHessianPreferredFiveSectorBismutFreedFamilyOutput4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}
    (input : GlobalHessianPreferredFiveSectorBismutFreedFamily4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) where
  intrinsicQuillen :
    GlobalHessianPreferredFiveSectorIntrinsicQuillenClosureCertificate4D
      (period := period) (hPeriod := hPeriod) input.quillen
  baseReducedOperator :
    input.familyIndex.actualGap.fixedOperator 0 =
      selfAdjointKernelComplementOperator
        (input.actualOperator 0)
        (input.familyIndex.actual_selfAdjoint 0)
  familyIndex :
    (∀ parameter,
      input.familyIndex.zetaFamily.finitePartFamily.logDerivative parameter =
        input.familyIndex.relativeTrace.trace parameter) ∧
    (∀ parameter,
      input.familyIndex.toBismutFreed.connectionAt parameter
          (relativeHeatMellinZetaFamilyDeterminant
            input.familyIndex.zetaFamily parameter)
          (relativeZetaDeterminantCoordinateDerivative
            input.familyIndex.zetaFamily.toZetaFamily parameter) = 0)
  noCrossing : UniformGapFamilyNoCrossingCertificate
    input.familyIndex.actualDifferentiable.analytic
  uniformResolvent : ∀ parameter spectralParameter,
    ∀ hSpectral : |spectralParameter| <
      input.familyIndex.actualDifferentiable.analytic.gap,
      ‖uniformGapFamilyResolvent
          input.familyIndex.actualDifferentiable.analytic parameter
          spectralParameter hSpectral‖ ≤
        (input.familyIndex.actualDifferentiable.analytic.gap -
          |spectralParameter|)⁻¹
  relativeTraceCircle : ∀ parameter,
    input.familyIndex.relativeTrace.trace parameter =
      -circleQuillenConnectionCoefficient fold
  phaseHolonomy :
    circleQuillenClosedHolonomy fold =
      relativeZetaFinitePartPhase
          input.familyIndex.zetaFamily.toFinitePartComparison 0 /
        relativeZetaFinitePartPhase
          input.familyIndex.zetaFamily.toFinitePartComparison 1

/-- Assemble the Candidate-A family-index output. -/
def close
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}
    (input : GlobalHessianPreferredFiveSectorBismutFreedFamily4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    GlobalHessianPreferredFiveSectorBismutFreedFamilyOutput4D
      (period := period) (hPeriod := hPeriod) input where
  intrinsicQuillen :=
    globalHessianPreferredFiveSectorIntrinsicQuillenClosureCertificate
      (period := period) (hPeriod := hPeriod) input.quillen
  baseReducedOperator := input.fixedOperator_zero_eq_actual period hPeriod
  familyIndex :=
    ⟨input.familyIndex.finitePart_logDerivative_eq_relativeTrace,
      input.familyIndex.determinant_parallel⟩
  noCrossing := input.noCrossing
  uniformResolvent :=
    uniformGapFamilyResolvent_opNorm_le
      input.familyIndex.actualDifferentiable.analytic
  relativeTraceCircle := input.toCircleTraceBridge.relativeTrace_eq_neg_circleCoefficient
  phaseHolonomy := input.toCircleTraceBridge.closedHolonomy_eq_phase_ratio

/-- Public preferred Candidate-A family-index checkpoint. -/
def global_hessian_preferred_five_sector_bismut_freed_family_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}
    (input : GlobalHessianPreferredFiveSectorBismutFreedFamily4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    GlobalHessianPreferredFiveSectorBismutFreedFamilyOutput4D
      (period := period) (hPeriod := hPeriod) input :=
  input.close

end GlobalHessianPreferredFiveSectorBismutFreedFamily4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
end JanusFormal
