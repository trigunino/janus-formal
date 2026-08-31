import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSpinCMatterGraphResidualBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeLLGraphRieszResidual4D

/-!
# Complete LL-block Riesz residual in the minimal physical chart

The exact LL action identity pulls the complete three-slot LL graph form and
its Riesz residual back to every minimal physical chart.  Smooth LL core
directions already occur in the typed diagonal core; their dense image makes
the pulled residual separating.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalLLGraphRieszResidualBridge4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLQuadraticChartBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalEulerLagrangeLLGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

/-- The actual LL member of the nine-block Candidate-A action in the minimal
chart. -/
def globalCandidateAMinimalPhysicalLLBlockAction :
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model → Real :=
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  (globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod (0 : chart.Model)
      chart.zero_mem_domain) measure).ll

/-- The chart LL block is exactly the constant spectator plus the complete
three-slot LL graph action. -/
theorem globalCandidateAMinimalPhysicalLLBlockAction_eq_graph :
    globalCandidateAMinimalPhysicalLLBlockAction period hPeriod
        configuration data analysis chartData =
      fun state =>
        (globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
          configuration data analysis chartData).llConstant +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          ((globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
            configuration data analysis chartData).llProjection state) := by
  exact
    (globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
      configuration data analysis chartData).llAction_eq

/-- Frechet Euler covector of the LL block alone. -/
noncomputable def globalCandidateAMinimalPhysicalLLBlockEulerCovectorAt
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model →L[Real] Real :=
  fderiv Real
    (globalCandidateAMinimalPhysicalLLBlockAction period hPeriod
      configuration data analysis chartData) point

/-- The LL-block Euler covector is the pullback of the complete graph form at
every chart point. -/
theorem globalCandidateAMinimalPhysicalLLBlockEulerCovector_eq_graph
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalLLBlockEulerCovectorAt period hPeriod
        configuration data analysis chartData point =
      (globalCandidateAFullLLGraphForm period hPeriod data analysis
        ((globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
          configuration data analysis chartData).llProjection point)).comp
      (globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
          configuration data analysis chartData).llProjection := by
  unfold globalCandidateAMinimalPhysicalLLBlockEulerCovectorAt
  rw [globalCandidateAMinimalPhysicalLLBlockAction_eq_graph period hPeriod
    configuration data analysis chartData]
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  let bridge := globalCandidateAMinimalPhysicalQuadraticChartBridge period
    hPeriod configuration data analysis chartData
  have hGraph := globalCandidateAFullLLGraphAction_hasFDerivAt period hPeriod
    data analysis (bridge.llProjection point)
  have hComp := @HasFDerivAt.comp Real inferInstance chart.Model
    inferInstance inferInstance
    (GlobalFullLLGraphHilbert period hPeriod data analysis)
    (GlobalFullLLGraphHilbert period hPeriod data analysis).normedAddCommGroup
    (@globalFullLLC2GraphNormedSpace period hPeriod configuration.physical
      couplings NonNullFace NullFace inferInstance inferInstance data analysis)
    Real inferInstance inferInstance
    (fun state => bridge.llProjection state) bridge.llProjection point
    (globalCandidateAFullLLGraphAction period hPeriod data analysis)
    (globalCandidateAFullLLGraphForm period hPeriod data analysis
      (bridge.llProjection point)) hGraph bridge.llProjection.hasFDerivAt
  exact
    (hComp.const_add bridge.llConstant).fderiv

/-- Pair a complete LL Riesz residual with a chart direction through the
canonical LL projection. -/
def globalCandidateAMinimalPhysicalLLBlockRieszResidualPairing
    (residual : GlobalFullLLGraphHilbert period hPeriod data analysis)
    (direction : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) : Real :=
  globalCandidateAFullLLGraphRieszResidualPairing period hPeriod data analysis
    residual
      ((globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
        configuration data analysis chartData).llProjection direction)

/-- The complete LL Riesz residual represents the exact LL-block Euler
covector after pullback to the minimal chart. -/
theorem globalCandidateAMinimalPhysicalLLBlockEuler_eq_rieszResidualPairing
    (point direction :
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalLLBlockEulerCovectorAt period hPeriod
        configuration data analysis chartData point direction =
      globalCandidateAMinimalPhysicalLLBlockRieszResidualPairing period
        hPeriod configuration data analysis chartData
          (globalCandidateAFullLLGraphRieszResidual period hPeriod data
            analysis
              ((globalCandidateAMinimalPhysicalQuadraticChartBridge period
                hPeriod configuration data analysis chartData).llProjection
                  point)) direction := by
  rw [globalCandidateAMinimalPhysicalLLBlockEulerCovector_eq_graph period
    hPeriod configuration data analysis chartData point]
  exact globalCandidateAFullLLGraphForm_eq_rieszResidualPairing period hPeriod
    data analysis
      ((globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
        configuration data analysis chartData).llProjection point)
      ((globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
        configuration data analysis chartData).llProjection direction)

/-- Typed diagonal-core LL directions have dense image and therefore
separate every complete LL graph residual. -/
theorem globalCandidateAMinimalPhysicalLLBlockRieszResidualPairing_separates
    (residual : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    (∀ direction :
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).Model,
      globalCandidateAMinimalPhysicalLLBlockRieszResidualPairing period
        hPeriod configuration data analysis chartData residual direction = 0) ↔
      residual = 0 := by
  constructor
  · intro hPairing
    apply (globalCandidateAFullLLGraphRieszResidualPairing_separates period
      hPeriod data analysis residual).mp
    intro test
    unfold globalCandidateAFullLLGraphRieszResidualPairing
    refine DenseRange.induction_on
      (globalCandidateAFullLLSmoothEmbedding_denseRange period hPeriod data
        analysis) test
      (isClosed_eq
        (@innerSL Real (GlobalFullLLGraphHilbert period hPeriod data analysis)
          inferInstance _
          (@globalFullLLGraphInnerProductSpace period hPeriod
            configuration.physical couplings NonNullFace NullFace inferInstance
            inferInstance data analysis) residual).continuous
        continuous_const) ?_
    intro smooth
    let core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
        analysis :=
      (0, (0, (0, smooth)))
    let bridge := globalCandidateAMinimalPhysicalQuadraticChartBridge period
      hPeriod configuration data analysis chartData
    let direction := bridge.chartBridge.tangentAnalysis
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis core)
    have hCore := hPairing direction
    have hProjection :
        bridge.llProjection direction =
          globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
            smooth := by
      simpa [direction] using bridge.llProjection_core core
    change globalCandidateAFullLLGraphRieszResidualPairing period hPeriod data
      analysis residual (bridge.llProjection direction) = 0 at hCore
    rw [hProjection] at hCore
    simpa only [globalCandidateAFullLLGraphRieszResidualPairing] using hCore
  · rintro rfl direction
    unfold globalCandidateAMinimalPhysicalLLBlockRieszResidualPairing
    unfold globalCandidateAFullLLGraphRieszResidualPairing
    exact @inner_zero_left Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) inferInstance _
      (@globalFullLLGraphInnerProductSpace period hPeriod
        configuration.physical couplings NonNullFace NullFace inferInstance
        inferInstance data analysis) _

/-- Concrete separating representation of the LL block on the minimal chart.
Its residual is the genuine complete three-slot graph Riesz output. -/
def globalCandidateAMinimalPhysicalLLBlockRieszResidualRepresentation
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    SeparatingPDEResidualRepresentation
      (globalCandidateAMinimalPhysicalLLBlockEulerCovectorAt period hPeriod
        configuration data analysis chartData point).toLinearMap where
  Residual := GlobalFullLLGraphHilbert period hPeriod data analysis
  zeroResidual := 0
  residual := globalCandidateAFullLLGraphRieszResidual period hPeriod data
    analysis
      ((globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
        configuration data analysis chartData).llProjection point)
  pairing := globalCandidateAMinimalPhysicalLLBlockRieszResidualPairing period
    hPeriod configuration data analysis chartData
  represents :=
    globalCandidateAMinimalPhysicalLLBlockEuler_eq_rieszResidualPairing period
      hPeriod configuration data analysis chartData point
  separates :=
    globalCandidateAMinimalPhysicalLLBlockRieszResidualPairing_separates period
      hPeriod configuration data analysis chartData _

/-- LL-block stationarity is exactly vanishing of the pulled complete graph
Riesz residual. -/
theorem globalCandidateAMinimalPhysicalLLBlockEuler_eq_zero_iff_rieszResidual
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalLLBlockEulerCovectorAt period hPeriod
        configuration data analysis chartData point = 0 ↔
      globalCandidateAFullLLGraphRieszResidual period hPeriod data analysis
          ((globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
            configuration data analysis chartData).llProjection point) = 0 := by
  let representation :=
    globalCandidateAMinimalPhysicalLLBlockRieszResidualRepresentation period
      hPeriod configuration data analysis chartData point
  constructor
  · intro hEuler
    apply (separatingPDEResidualRepresentation_covector_eq_zero_iff
      representation).mp
    exact congrArg ContinuousLinearMap.toLinearMap hEuler
  · intro hResidual
    apply ContinuousLinearMap.ext
    intro direction
    have hCovector :=
      (separatingPDEResidualRepresentation_covector_eq_zero_iff
        representation).mpr hResidual
    exact LinearMap.congr_fun hCovector direction

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalLLGraphRieszResidualBridge4D
end JanusFormal
