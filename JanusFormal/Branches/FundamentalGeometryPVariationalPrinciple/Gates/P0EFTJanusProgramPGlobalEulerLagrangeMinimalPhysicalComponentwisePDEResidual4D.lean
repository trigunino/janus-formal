import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

/-!
# Componentwise separating PDE residuals for the minimal system

The seven corrected bulk equations and primitive SpinC equation receive eight
independent residual representations.  This exposes the exact construction
obligation for each future tensorial differential operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentwisePDEResidual4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalWeakEightSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalAtlasRetraction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)
private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

local instance globalMinimalPhysicalBulkTangentAddCommGroup :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModule :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

/-- Eight named separating representations, one for each true minimal field
sector. -/
structure GlobalCandidateAMinimalPhysicalComponentwisePDEDataAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) where
  metric : SeparatingPDEResidualRepresentation
    (globalCandidateAMinimalPhysicalMetricEulerCovectorAt period hPeriod
      configuration data analysis chartData point)
  gauge : SeparatingPDEResidualRepresentation
    (globalCandidateAMinimalPhysicalGaugeEulerCovectorAt period hPeriod
      configuration data analysis chartData point)
  normal : SeparatingPDEResidualRepresentation
    (globalCandidateAMinimalPhysicalNormalEulerCovectorAt period hPeriod
      configuration data analysis chartData point)
  diffeomorphismGhost : SeparatingPDEResidualRepresentation
    (globalCandidateAMinimalPhysicalDiffeomorphismGhostEulerCovectorAt
      period hPeriod configuration data analysis chartData point)
  llAuxMetric : SeparatingPDEResidualRepresentation
    (globalCandidateAMinimalPhysicalLLAuxMetricEulerCovectorAt period hPeriod
      configuration data analysis chartData point)
  llMeasure : SeparatingPDEResidualRepresentation
    (globalCandidateAMinimalPhysicalLLMeasureEulerCovectorAt period hPeriod
      configuration data analysis chartData point)
  llField : SeparatingPDEResidualRepresentation
    (globalCandidateAMinimalPhysicalLLFieldEulerCovectorAt period hPeriod
      configuration data analysis chartData point)
  spinC : SeparatingPDEResidualRepresentation
    (globalCandidateAMinimalPhysicalSpinCMatterEulerCovectorAt period hPeriod
      configuration data analysis chartData point)

/-- The eight named strong residual equations. -/
def GlobalCandidateAMinimalPhysicalComponentwiseStrongPDESystemAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model)
    (pdeData : GlobalCandidateAMinimalPhysicalComponentwisePDEDataAt period
      hPeriod configuration data analysis chartData point) : Prop :=
  (pdeData.metric.residual = pdeData.metric.zeroResidual ∧
    pdeData.gauge.residual = pdeData.gauge.zeroResidual ∧
    pdeData.normal.residual = pdeData.normal.zeroResidual ∧
    pdeData.diffeomorphismGhost.residual =
      pdeData.diffeomorphismGhost.zeroResidual ∧
    pdeData.llAuxMetric.residual = pdeData.llAuxMetric.zeroResidual ∧
    pdeData.llMeasure.residual = pdeData.llMeasure.zeroResidual ∧
    pdeData.llField.residual = pdeData.llField.zeroResidual) ∧
  pdeData.spinC.residual = pdeData.spinC.zeroResidual

/-- Local Euler vanishing is exactly the eight named strong residual
equations. -/
theorem globalCandidateAMinimalPhysicalEuler_eq_zero_iff_componentwiseStrongPDE
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model)
    (pdeData : GlobalCandidateAMinimalPhysicalComponentwisePDEDataAt period
      hPeriod configuration data analysis chartData point) :
    globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData) point = 0 ↔
      GlobalCandidateAMinimalPhysicalComponentwiseStrongPDESystemAt period
        hPeriod configuration data analysis chartData point pdeData := by
  rw [globalCandidateAMinimalPhysicalEuler_eq_zero_iff_eightSectors period
    hPeriod configuration data analysis chartData point]
  unfold GlobalCandidateAMinimalPhysicalEightSectorEulerSystemAt
  unfold GlobalCandidateAMinimalPhysicalComponentwiseStrongPDESystemAt
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff pdeData.metric]
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff pdeData.gauge]
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff pdeData.normal]
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff
    pdeData.diffeomorphismGhost]
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff
    pdeData.llAuxMetric]
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff
    pdeData.llMeasure]
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff pdeData.llField]
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff pdeData.spinC]

/-- The exact weak nine-block equations are equivalent to all eight named
strong residual equations at every admissible point. -/
theorem globalCandidateAMinimalPhysicalWeakEightSectorSystem_iff_componentwiseStrongPDE
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model)
    (hPoint : point ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).family.domain)
    (pdeData : GlobalCandidateAMinimalPhysicalComponentwisePDEDataAt period
      hPeriod configuration data analysis chartData point) :
    GlobalCandidateAMinimalPhysicalWeakEightSectorSystemAt period hPeriod
        configuration data analysis chartData point ↔
      GlobalCandidateAMinimalPhysicalComponentwiseStrongPDESystemAt period
        hPeriod configuration data analysis chartData point pdeData :=
  (globalCandidateAMinimalPhysicalEuler_eq_zero_iff_weakEightSectorSystem
    period hPeriod configuration data analysis chartData point hPoint).symm.trans
      (globalCandidateAMinimalPhysicalEuler_eq_zero_iff_componentwiseStrongPDE
        period hPeriod configuration data analysis chartData point pdeData)

/-- Retractive-atlas criticality at the covered base is equivalent to all
eight named strong residual equations. -/
theorem globalCandidateAMinimalPhysicalRetractiveAtlas_isEulerCritical_iff_componentwiseStrongPDE
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (retraction : LocalChartCoordinateRetraction period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData))
    (pdeData : GlobalCandidateAMinimalPhysicalComponentwisePDEDataAt period
      hPeriod configuration data analysis chartData
        (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
          configuration data analysis chartData).basePoint) :
    (globalCandidateAMinimalPhysicalVariationalAtlas_of_retraction period
        hPeriod configuration data analysis chartData retraction).IsEulerCritical
          period hPeriod configuration.physical ↔
      GlobalCandidateAMinimalPhysicalComponentwiseStrongPDESystemAt period
        hPeriod configuration data analysis chartData
          (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
            configuration data analysis chartData).basePoint pdeData := by
  rw [globalCandidateAMinimalPhysicalRetractiveAtlas_isEulerCritical_iff
    period hPeriod configuration data analysis chartData retraction]
  exact globalCandidateAMinimalPhysicalEuler_eq_zero_iff_componentwiseStrongPDE
    period hPeriod configuration data analysis chartData
      (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
        configuration data analysis chartData).basePoint pdeData

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentwisePDEResidual4D
end JanusFormal
