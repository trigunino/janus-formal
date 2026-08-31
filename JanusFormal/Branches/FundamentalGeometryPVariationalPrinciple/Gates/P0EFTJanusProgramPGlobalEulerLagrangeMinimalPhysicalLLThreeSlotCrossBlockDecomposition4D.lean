import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalLLGraphRieszResidualBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D

/-!
# Three-slot LL cross-block decomposition in the minimal physical chart

Each pure LL direction receives an exact contribution from the authentic
complete LL action block.  The difference from the corresponding component of
the full nine-block Euler covector is retained as a named cross-block term.
No slotwise separation or cross-block vanishing is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalLLThreeSlotCrossBlockDecomposition4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLQuadraticChartBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeLLGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalLLGraphRieszResidualBridge4D

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

variable
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

/-! ## Pure LL directions -/

def globalCandidateAMinimalPhysicalLLAuxMetricChartDirection :
    GlobalMinimalPhysicalLLAuxMetricTest period hPeriod →ₗ[Real]
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model :=
  (globalCandidateAMinimalPhysicalSevenBulkChartDirection period hPeriod
    configuration data analysis chartData).comp
      (globalMinimalPhysicalLLAuxMetricTestInclusion period hPeriod)

def globalCandidateAMinimalPhysicalLLMeasureChartDirection :
    GlobalMinimalPhysicalLLMeasureTest period hPeriod →ₗ[Real]
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model :=
  (globalCandidateAMinimalPhysicalSevenBulkChartDirection period hPeriod
    configuration data analysis chartData).comp
      (globalMinimalPhysicalLLMeasureTestInclusion period hPeriod)

def globalCandidateAMinimalPhysicalLLFieldChartDirection :
    GlobalMinimalPhysicalLLFieldTest period hPeriod →ₗ[Real]
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model :=
  (globalCandidateAMinimalPhysicalSevenBulkChartDirection period hPeriod
    configuration data analysis chartData).comp
      (globalMinimalPhysicalLLFieldTestInclusion period hPeriod)

/-! ## Authentic LL-block contributions and cross-block remainders -/

def globalCandidateAMinimalPhysicalLLAuxMetricBlockEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    GlobalMinimalPhysicalLLAuxMetricTest period hPeriod →ₗ[Real] Real :=
  (globalCandidateAMinimalPhysicalLLBlockEulerCovectorAt period hPeriod
    configuration data analysis chartData point).toLinearMap.comp
      (globalCandidateAMinimalPhysicalLLAuxMetricChartDirection period hPeriod
        configuration data analysis chartData)

def globalCandidateAMinimalPhysicalLLMeasureBlockEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    GlobalMinimalPhysicalLLMeasureTest period hPeriod →ₗ[Real] Real :=
  (globalCandidateAMinimalPhysicalLLBlockEulerCovectorAt period hPeriod
    configuration data analysis chartData point).toLinearMap.comp
      (globalCandidateAMinimalPhysicalLLMeasureChartDirection period hPeriod
        configuration data analysis chartData)

def globalCandidateAMinimalPhysicalLLFieldBlockEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    GlobalMinimalPhysicalLLFieldTest period hPeriod →ₗ[Real] Real :=
  (globalCandidateAMinimalPhysicalLLBlockEulerCovectorAt period hPeriod
    configuration data analysis chartData point).toLinearMap.comp
      (globalCandidateAMinimalPhysicalLLFieldChartDirection period hPeriod
        configuration data analysis chartData)

def globalCandidateAMinimalPhysicalLLAuxMetricCrossBlockEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    GlobalMinimalPhysicalLLAuxMetricTest period hPeriod →ₗ[Real] Real :=
  globalCandidateAMinimalPhysicalLLAuxMetricEulerCovectorAt period hPeriod
      configuration data analysis chartData point -
    globalCandidateAMinimalPhysicalLLAuxMetricBlockEulerCovectorAt period
      hPeriod configuration data analysis chartData point

def globalCandidateAMinimalPhysicalLLMeasureCrossBlockEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    GlobalMinimalPhysicalLLMeasureTest period hPeriod →ₗ[Real] Real :=
  globalCandidateAMinimalPhysicalLLMeasureEulerCovectorAt period hPeriod
      configuration data analysis chartData point -
    globalCandidateAMinimalPhysicalLLMeasureBlockEulerCovectorAt period hPeriod
      configuration data analysis chartData point

def globalCandidateAMinimalPhysicalLLFieldCrossBlockEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    GlobalMinimalPhysicalLLFieldTest period hPeriod →ₗ[Real] Real :=
  globalCandidateAMinimalPhysicalLLFieldEulerCovectorAt period hPeriod
      configuration data analysis chartData point -
    globalCandidateAMinimalPhysicalLLFieldBlockEulerCovectorAt period hPeriod
      configuration data analysis chartData point

theorem globalCandidateAMinimalPhysicalLLAuxMetricEulerCovector_decomposition
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalLLAuxMetricEulerCovectorAt period hPeriod
        configuration data analysis chartData point =
      globalCandidateAMinimalPhysicalLLAuxMetricBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point +
        globalCandidateAMinimalPhysicalLLAuxMetricCrossBlockEulerCovectorAt
          period hPeriod configuration data analysis chartData point := by
  unfold globalCandidateAMinimalPhysicalLLAuxMetricCrossBlockEulerCovectorAt
  abel

theorem globalCandidateAMinimalPhysicalLLMeasureEulerCovector_decomposition
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalLLMeasureEulerCovectorAt period hPeriod
        configuration data analysis chartData point =
      globalCandidateAMinimalPhysicalLLMeasureBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point +
        globalCandidateAMinimalPhysicalLLMeasureCrossBlockEulerCovectorAt
          period hPeriod configuration data analysis chartData point := by
  unfold globalCandidateAMinimalPhysicalLLMeasureCrossBlockEulerCovectorAt
  abel

theorem globalCandidateAMinimalPhysicalLLFieldEulerCovector_decomposition
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalLLFieldEulerCovectorAt period hPeriod
        configuration data analysis chartData point =
      globalCandidateAMinimalPhysicalLLFieldBlockEulerCovectorAt period hPeriod
          configuration data analysis chartData point +
        globalCandidateAMinimalPhysicalLLFieldCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point := by
  unfold globalCandidateAMinimalPhysicalLLFieldCrossBlockEulerCovectorAt
  abel

/-! ## Exact slotwise Riesz formulas -/

theorem globalCandidateAMinimalPhysicalLLAuxMetricEuler_eq_rieszResidualPairing
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model)
    (variation : GlobalMinimalPhysicalLLAuxMetricTest period hPeriod) :
    globalCandidateAMinimalPhysicalLLAuxMetricEulerCovectorAt period hPeriod
        configuration data analysis chartData point variation =
      globalCandidateAMinimalPhysicalLLBlockRieszResidualPairing period hPeriod
          configuration data analysis chartData
          (globalCandidateAFullLLGraphRieszResidual period hPeriod data analysis
            ((globalCandidateAMinimalPhysicalQuadraticChartBridge period
              hPeriod configuration data analysis chartData).llProjection
                point))
          (globalCandidateAMinimalPhysicalLLAuxMetricChartDirection period
            hPeriod configuration data analysis chartData variation) +
        globalCandidateAMinimalPhysicalLLAuxMetricCrossBlockEulerCovectorAt
          period hPeriod configuration data analysis chartData point
            variation := by
  rw [LinearMap.congr_fun
    (globalCandidateAMinimalPhysicalLLAuxMetricEulerCovector_decomposition
      period hPeriod configuration data analysis chartData point) variation]
  change
    globalCandidateAMinimalPhysicalLLBlockEulerCovectorAt period hPeriod
          configuration data analysis chartData point
          (globalCandidateAMinimalPhysicalLLAuxMetricChartDirection period
            hPeriod configuration data analysis chartData variation) + _ = _
  rw [globalCandidateAMinimalPhysicalLLBlockEuler_eq_rieszResidualPairing]

theorem globalCandidateAMinimalPhysicalLLMeasureEuler_eq_rieszResidualPairing
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model)
    (variation : GlobalMinimalPhysicalLLMeasureTest period hPeriod) :
    globalCandidateAMinimalPhysicalLLMeasureEulerCovectorAt period hPeriod
        configuration data analysis chartData point variation =
      globalCandidateAMinimalPhysicalLLBlockRieszResidualPairing period hPeriod
          configuration data analysis chartData
          (globalCandidateAFullLLGraphRieszResidual period hPeriod data analysis
            ((globalCandidateAMinimalPhysicalQuadraticChartBridge period
              hPeriod configuration data analysis chartData).llProjection
                point))
          (globalCandidateAMinimalPhysicalLLMeasureChartDirection period
            hPeriod configuration data analysis chartData variation) +
        globalCandidateAMinimalPhysicalLLMeasureCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point variation := by
  rw [LinearMap.congr_fun
    (globalCandidateAMinimalPhysicalLLMeasureEulerCovector_decomposition period
      hPeriod configuration data analysis chartData point) variation]
  change
    globalCandidateAMinimalPhysicalLLBlockEulerCovectorAt period hPeriod
          configuration data analysis chartData point
          (globalCandidateAMinimalPhysicalLLMeasureChartDirection period hPeriod
            configuration data analysis chartData variation) + _ = _
  rw [globalCandidateAMinimalPhysicalLLBlockEuler_eq_rieszResidualPairing]

theorem globalCandidateAMinimalPhysicalLLFieldEuler_eq_rieszResidualPairing
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model)
    (variation : GlobalMinimalPhysicalLLFieldTest period hPeriod) :
    globalCandidateAMinimalPhysicalLLFieldEulerCovectorAt period hPeriod
        configuration data analysis chartData point variation =
      globalCandidateAMinimalPhysicalLLBlockRieszResidualPairing period hPeriod
          configuration data analysis chartData
          (globalCandidateAFullLLGraphRieszResidual period hPeriod data analysis
            ((globalCandidateAMinimalPhysicalQuadraticChartBridge period
              hPeriod configuration data analysis chartData).llProjection
                point))
          (globalCandidateAMinimalPhysicalLLFieldChartDirection period hPeriod
            configuration data analysis chartData variation) +
        globalCandidateAMinimalPhysicalLLFieldCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point variation := by
  rw [LinearMap.congr_fun
    (globalCandidateAMinimalPhysicalLLFieldEulerCovector_decomposition period
      hPeriod configuration data analysis chartData point) variation]
  change
    globalCandidateAMinimalPhysicalLLBlockEulerCovectorAt period hPeriod
          configuration data analysis chartData point
          (globalCandidateAMinimalPhysicalLLFieldChartDirection period hPeriod
            configuration data analysis chartData variation) + _ = _
  rw [globalCandidateAMinimalPhysicalLLBlockEuler_eq_rieszResidualPairing]

/-! ## Exact cross-block obstruction -/

theorem globalCandidateAMinimalPhysicalLLAuxMetricEuler_eq_block_iff_crossBlock_zero
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalLLAuxMetricEulerCovectorAt period hPeriod
          configuration data analysis chartData point =
        globalCandidateAMinimalPhysicalLLAuxMetricBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point ↔
      globalCandidateAMinimalPhysicalLLAuxMetricCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point = 0 := by
  unfold globalCandidateAMinimalPhysicalLLAuxMetricCrossBlockEulerCovectorAt
  constructor
  · intro hEqual
    simp [hEqual]
  · intro hZero
    exact sub_eq_zero.mp hZero

theorem globalCandidateAMinimalPhysicalLLMeasureEuler_eq_block_iff_crossBlock_zero
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalLLMeasureEulerCovectorAt period hPeriod
          configuration data analysis chartData point =
        globalCandidateAMinimalPhysicalLLMeasureBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point ↔
      globalCandidateAMinimalPhysicalLLMeasureCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point = 0 := by
  unfold globalCandidateAMinimalPhysicalLLMeasureCrossBlockEulerCovectorAt
  constructor
  · intro hEqual
    simp [hEqual]
  · intro hZero
    exact sub_eq_zero.mp hZero

theorem globalCandidateAMinimalPhysicalLLFieldEuler_eq_block_iff_crossBlock_zero
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalLLFieldEulerCovectorAt period hPeriod
          configuration data analysis chartData point =
        globalCandidateAMinimalPhysicalLLFieldBlockEulerCovectorAt period hPeriod
          configuration data analysis chartData point ↔
      globalCandidateAMinimalPhysicalLLFieldCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData point = 0 := by
  unfold globalCandidateAMinimalPhysicalLLFieldCrossBlockEulerCovectorAt
  constructor
  · intro hEqual
    simp [hEqual]
  · intro hZero
    exact sub_eq_zero.mp hZero

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalLLThreeSlotCrossBlockDecomposition4D
end JanusFormal
