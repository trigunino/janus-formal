import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D

/-!
# Eight-sector Euler equations as nine-block derivatives

The seven corrected bulk coordinates and primitive SpinC matter are transported
to the minimal chart.  Their Euler evaluations are the exact sums of the nine
assembled action-block derivatives at every admissible chart point.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D

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
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D

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

local instance globalMinimalPhysicalTangentAddCommGroup
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

local instance globalMinimalPhysicalTangentModule
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

/-- Direction in the minimal chart determined by all seven corrected bulk
coordinates and zero primitive matter. -/
def globalCandidateAMinimalPhysicalSevenBulkChartDirection
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod →ₗ[Real]
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model :=
  (globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
      configuration data analysis chartData).toLinearMap.comp
    ((globalMinimalPhysicalTangentSectorEquiv period hPeriod
        configuration.physical).symm.toLinearMap.comp
      ((productFirstInclusion
          (GlobalMinimalPhysicalBulkTangent period hPeriod)
          (Sector → D9PrimitiveSpinCSmoothSection
            period hPeriod .positiveQuarter)).comp
        (globalMinimalPhysicalSevenBulkEquiv period hPeriod).symm.toLinearMap))

/-- Pure primitive SpinC direction in the minimal chart. -/
def globalCandidateAMinimalPhysicalSpinCMatterChartDirection
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    (Sector → D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter) →ₗ[Real]
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model :=
  (globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
      configuration data analysis chartData).toLinearMap.comp
    ((globalMinimalPhysicalTangentSectorEquiv period hPeriod
        configuration.physical).symm.toLinearMap.comp
      (productSecondInclusion
        (GlobalMinimalPhysicalBulkTangent period hPeriod)
        (Sector → D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter)))

/-- Directional nine-block formula for every admissible local chart. -/
theorem globalCandidateALocalEulerLagrangeOperator_apply_eq_blockSum
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain)
    (direction : chart.Model) :
    globalCandidateALocalEulerLagrangeOperator period hPeriod chart point direction =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain)
          measure)
        point direction := by
  let blocks := globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain) measure
  have hC2 : FullCoupledC2At blocks point :=
    fullCoupledC2WithinAt_toAt
      (chart.blocksC2Within point hPoint) chart.isOpen_domain hPoint
  unfold globalCandidateALocalEulerLagrangeOperator
    globalCandidateALocalActionPullback
  rw [fullCoupledAction_gradient_apply_eq_blockSum blocks point hC2]

/-- The seven-coordinate bulk Euler evaluation is the exact nine-block
derivative sum on its transported chart direction. -/
theorem globalCandidateAMinimalPhysicalSevenBulkEuler_apply_eq_blockSum
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
    (variation : GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod) :
    globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point variation =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData).family.toActionFamily
              period hPeriod 0
              (globalCandidateAMinimalPhysicalLocalVariationalChart period
                hPeriod configuration data analysis chartData).zero_mem_domain)
          measure)
        point
        (globalCandidateAMinimalPhysicalSevenBulkChartDirection period hPeriod
          configuration data analysis chartData variation) := by
  change globalCandidateALocalEulerLagrangeOperator period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData) point
      (globalCandidateAMinimalPhysicalSevenBulkChartDirection period hPeriod
        configuration data analysis chartData variation) = _
  exact globalCandidateALocalEulerLagrangeOperator_apply_eq_blockSum
    period hPeriod _ point hPoint _

/-- Every linear pure-component restriction of the seven bulk coordinates
inherits the same exact nine-block formula. -/
theorem globalCandidateAMinimalPhysicalSevenBulkEuler_restrict_apply_eq_blockSum
    {Component : Type*} [AddCommGroup Component] [Module Real Component]
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
    (inclusion : Component →ₗ[Real]
      GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod)
    (variation : Component) :
    ((globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point).comp inclusion) variation =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData).family.toActionFamily
              period hPeriod 0
              (globalCandidateAMinimalPhysicalLocalVariationalChart period
                hPeriod configuration data analysis chartData).zero_mem_domain)
          measure)
        point
        (globalCandidateAMinimalPhysicalSevenBulkChartDirection period hPeriod
          configuration data analysis chartData (inclusion variation)) :=
  globalCandidateAMinimalPhysicalSevenBulkEuler_apply_eq_blockSum period hPeriod
    configuration data analysis chartData point hPoint (inclusion variation)

/-- The primitive SpinC Euler evaluation is the exact nine-block derivative
sum on its pure transported chart direction. -/
theorem globalCandidateAMinimalPhysicalSpinCMatterEuler_apply_eq_blockSum
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
    (variation : Sector → D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter) :
    globalCandidateAMinimalPhysicalSpinCMatterEulerCovectorAt period hPeriod
        configuration data analysis chartData point variation =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData).family.toActionFamily
              period hPeriod 0
              (globalCandidateAMinimalPhysicalLocalVariationalChart period
                hPeriod configuration data analysis chartData).zero_mem_domain)
          measure)
        point
        (globalCandidateAMinimalPhysicalSpinCMatterChartDirection period hPeriod
          configuration data analysis chartData variation) := by
  change globalCandidateALocalEulerLagrangeOperator period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData) point
      (globalCandidateAMinimalPhysicalSpinCMatterChartDirection period hPeriod
        configuration data analysis chartData variation) = _
  exact globalCandidateALocalEulerLagrangeOperator_apply_eq_blockSum
    period hPeriod _ point hPoint _

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D
end JanusFormal
