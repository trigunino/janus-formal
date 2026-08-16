import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalExtensionNorm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActionTranslationStablePhysicalForm4D

/-!
# Explicit smallness constant for the canonical seven physical blocks

The canonical H11 extension is generated from one dense-core product estimate.
Its completed operator norm is therefore bounded by the same scalar constant.
This file instantiates that fact for the H10 Robin plus six genuine local
Candidate-A Hessians built from one core-to-chart estimate.

The perturbative Noether packet can now compare an explicit computable H11
constant with the principal Gårding constant; it no longer asks for the norm of
the completed form as an independent theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalSmallness4D

set_option autoImplicit false
set_option maxHeartbeats 11800000
set_option synthInstance.maxHeartbeats 5900000

noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateBound4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalExtensionNorm4D
open P0EFTJanusProgramPGlobalCandidateAActionTranslationStablePhysicalForm4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixDenseCoreFrontier4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

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

private abbrev CanonicalSmallnessHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) canonicalSmallNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (CanonicalSmallnessHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) canonicalSmallInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (CanonicalSmallnessHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) canonicalSmallNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (CanonicalSmallnessHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) canonicalSmallModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (CanonicalSmallnessHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) canonicalSmallCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (CanonicalSmallnessHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)

/-- Exact seven-block core bound underlying the canonical chart-bound H11
extension. -/
def globalCandidateACanonicalSevenPhysicalCoreBound_of_chartBound
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family))) :=
  globalCandidateASevenPhysicalCoreBound_of_sixAggregate period hPeriod
    configuration data analysis
      (globalCandidateAActualKernelChart period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAActualKernelSameAction period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      einsteinScale
      (globalCandidateACanonicalSixTerminalBound period hPeriod configuration
        data analysis einsteinScale hTransverse family
          ((globalCandidateAH10ProjectionCoreData_of_chartBound period hPeriod
            configuration data analysis einsteinScale hTransverse family
              chartBound).toDenseCoreAgreement period hPeriod hTransverse)
          chartBound)

/-- Explicit scalar bound for the completed canonical seven-block form. -/
def globalCandidateACanonicalSevenPhysicalConstant
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family))) : Real :=
  (globalCandidateACanonicalSevenPhysicalCoreBound_of_chartBound period hPeriod
    configuration data analysis einsteinScale hTransverse family chartBound
    ).constant

/-- The completed canonical H11 form is controlled by the explicit dense-core
constant. -/
theorem globalCandidateACanonicalSixPhysicalExtension_form_opNorm_le
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family))) :
    ‖(globalCandidateACanonicalSixPhysicalExtension_of_chartBound period hPeriod
        configuration data analysis einsteinScale hTransverse family chartBound
        ).form‖ ≤
      globalCandidateACanonicalSevenPhysicalConstant period hPeriod
        configuration data analysis einsteinScale hTransverse family
          chartBound := by
  change
    ‖(globalCandidateASevenPhysicalCommonDomainExtension_of_bound period hPeriod
        configuration data analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family)
          (globalCandidateACanonicalSevenPhysicalCoreBound_of_chartBound period
            hPeriod configuration data analysis einsteinScale hTransverse family
              chartBound)).form‖ ≤ _
  exact globalCandidateASevenPhysicalExtension_form_opNorm_le period hPeriod
    configuration data analysis
      (globalCandidateAActualKernelChart period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAActualKernelSameAction period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateACanonicalSevenPhysicalCoreBound_of_chartBound period
        hPeriod configuration data analysis einsteinScale hTransverse family
          chartBound)

/-- Action symmetries and principal Gårding with an explicit dense-core H11
smallness test. -/
structure GlobalCandidateAActionTranslationCanonicalSmallnessData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family)))
    (ZeroMode : Type*) [Fintype ZeroMode] : Prop where
  translations : GlobalCandidateAActionTranslationSymmetryModes4D period hPeriod
    configuration data analysis
      (globalCandidateAActualKernelChart period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAActualKernelSameAction period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period hPeriod
        configuration data analysis einsteinScale hTransverse family chartBound)
      ZeroMode
  nonzero : ∀ mode, translations.vector mode ≠ 0
  orthogonal : Pairwise fun first second =>
    ⟪translations.vector first, translations.vector second, Real⟫ = 0
  referenceConstant : Real
  canonical_constant_small :
    globalCandidateACanonicalSevenPhysicalConstant period hPeriod configuration
      data analysis einsteinScale hTransverse family chartBound <
        referenceConstant
  defectConstant : Real
  defectConstant_nonneg : 0 ≤ defectConstant
  reference_garding : ∀ current :
      CanonicalSmallnessHilbert period hPeriod configuration data analysis,
    referenceConstant * ‖current‖ ^ 2 ≤
      ⟪current,
        globalCandidateACanonicalStableReferenceOperator period hPeriod
          configuration data analysis current, Real⟫ +
        defectConstant *
          ∑ mode : ZeroMode,
            ⟪current, translations.vector mode, Real⟫ ^ 2
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- Convert the explicit scalar comparison to the stable physical-form packet. -/
def GlobalCandidateAActionTranslationCanonicalSmallnessData4D.toStable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family))}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAActionTranslationCanonicalSmallnessData4D period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound ZeroMode) :
    GlobalCandidateAActionTranslationStablePhysicalFormData4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
          hPeriod configuration data analysis einsteinScale hTransverse family
            chartBound)
        ZeroMode where
  translations := input.translations
  nonzero := input.nonzero
  orthogonal := input.orthogonal
  referenceConstant := input.referenceConstant
  physical_form_small := lt_of_le_of_lt
    (globalCandidateACanonicalSixPhysicalExtension_form_opNorm_le period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound)
    input.canonical_constant_small
  defectConstant := input.defectConstant
  defectConstant_nonneg := input.defectConstant_nonneg
  reference_garding := input.reference_garding
  ll_stationary := input.ll_stationary

/-- Public explicit-smallness checkpoint. -/
theorem global_candidateA_canonical_physical_smallness_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family))}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAActionTranslationCanonicalSmallnessData4D period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound ZeroMode) :
    ‖(globalCandidateACanonicalSixPhysicalExtension_of_chartBound period hPeriod
        configuration data analysis einsteinScale hTransverse family chartBound
        ).form‖ < input.referenceConstant :=
  (input.toStable period hPeriod).physical_form_small

end
end P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalSmallness4D
end JanusFormal
