import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreHilbertChartEquivalence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertBlockSum4D

/-!
# Minimal physical Hilbert closure from the dense smooth core

The three remaining analytic inputs for the selected physical chart are
packaged once.  They canonically produce the common-Hilbert equivalence and
therefore the nonlinear residual atlas, its exact nine-block formula,
criticality criterion, and smooth-core Hessian identity.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalDenseCoreHilbertClosure4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D
open P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAtlasResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertLinearization4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertResidualAtlas4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertPhysicalAtlasBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalCanonicalAlgebraicResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertPDEResidualBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertBlockSum4D
open P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreHilbertChartEquivalence4D

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

section Construction

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

local instance constructionCommonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance constructionCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance constructionCommonModule : Module Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkModule period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance constructionCommonCompleteSpace : CompleteSpace
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkCompleteSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- Exactly the three analytic obligations needed to close the common-Hilbert
chart for the selected minimal physical chart. -/
structure ProgramPGlobalMinimalPhysicalDenseCoreHilbertClosureData4D where
  chartComplete : CompleteSpace
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model
  norm_compatibility :
    ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
        analysis,
      ‖globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
          analysis
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData)
          (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
            configuration data analysis chartData) core‖ =
        ‖globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
          configuration data analysis core‖
  dense_range : DenseRange
    (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
      analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData))

/-- The common-Hilbert chart is no longer an independent input once the three
dense-core obligations are available. -/
def globalCandidateAMinimalPhysicalCommonHilbertChartOfDenseCoreClosure
    (closure : ProgramPGlobalMinimalPhysicalDenseCoreHilbertClosureData4D
      period hPeriod configuration data analysis chartData) :
    ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period hPeriod
      configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData) := by
  letI := closure.chartComplete
  exact globalCandidateACommonHilbertChartOfDenseCoreIsometry period hPeriod
    configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData)
      closure.norm_compatibility closure.dense_range

end Construction

section Consequences

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
    (closure : ProgramPGlobalMinimalPhysicalDenseCoreHilbertClosureData4D
      period hPeriod configuration data analysis chartData)

local instance consequenceCommonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedNormedAddCommGroup period hPeriod configuration data analysis

local instance consequenceCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedNormedSpace period hPeriod configuration data analysis

local instance consequenceCommonModule : Module Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedModule period hPeriod configuration data analysis

/-- Canonical singleton nonlinear residual atlas obtained from the dense-core
closure data, with no separately supplied Hilbert equivalence. -/
def globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlasOfDenseCoreClosure :
    GlobalCandidateANonlinearHilbertResidualAtlas period hPeriod
      (measure := measure) configuration data analysis :=
  globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period hPeriod
    configuration data analysis chartData
      (globalCandidateAMinimalPhysicalCommonHilbertChartOfDenseCoreClosure
        period hPeriod configuration data analysis chartData closure)

/-- Dense-core closure identifies Hilbert criticality with the canonical
eight-sector algebraic residual at every represented state. -/
theorem globalCandidateAMinimalPhysicalHilbertCritical_iff_canonicalAlgebraicResidual_of_denseCoreClosure
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlasOfDenseCoreClosure
      period hPeriod configuration data analysis chartData closure).IsEulerCritical
        period hPeriod state ↔
      GlobalCandidateAMinimalPhysicalCanonicalAlgebraicResidualSystemAt
        period hPeriod configuration data analysis chartData
          (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
            configuration data analysis chartData
              (globalCandidateAMinimalPhysicalCommonHilbertChartOfDenseCoreClosure
                period hPeriod configuration data analysis chartData closure)
              state) := by
  exact globalCandidateAMinimalPhysicalHilbertCritical_iff_canonicalAlgebraicResidual
    period hPeriod configuration data analysis chartData
      (globalCandidateAMinimalPhysicalCommonHilbertChartOfDenseCoreClosure
        period hPeriod configuration data analysis chartData closure) state

/-- The resulting residual pairing is exactly the derivative sum of the nine
true action blocks. -/
theorem globalCandidateAMinimalPhysicalHilbertResidual_pairing_eq_blockSum_of_denseCoreClosure
    (state test : CommonAugmentedHilbert period hPeriod configuration data
      analysis)
    (hState : state ∈
      (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlasOfDenseCoreClosure
        period hPeriod configuration data analysis chartData closure).carrier) :
    inner Real
        ((globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlasOfDenseCoreClosure
          period hPeriod configuration data analysis chartData closure).residual
            period hPeriod state) test =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData).family.toActionFamily
              period hPeriod 0
                (globalCandidateAMinimalPhysicalLocalVariationalChart period
                  hPeriod configuration data analysis chartData).zero_mem_domain)
          measure)
        (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
          configuration data analysis chartData
            (globalCandidateAMinimalPhysicalCommonHilbertChartOfDenseCoreClosure
              period hPeriod configuration data analysis chartData closure)
            state)
        (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
          configuration data analysis chartData
            (globalCandidateAMinimalPhysicalCommonHilbertChartOfDenseCoreClosure
              period hPeriod configuration data analysis chartData closure)
            test) := by
  exact globalCandidateAMinimalPhysicalHilbertResidual_pairing_eq_blockSum
    period hPeriod configuration data analysis chartData
      (globalCandidateAMinimalPhysicalCommonHilbertChartOfDenseCoreClosure
        period hPeriod configuration data analysis chartData closure)
      state test hState

/-- The nonlinear residual linearization obtained from the same closure is the
genuine covariant Hessian on the dense smooth core. -/
theorem globalCandidateAMinimalPhysicalNonlinearHilbertHessian_smooth_eq_covariant_of_denseCoreClosure
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis) :
    globalCandidateANonlinearHilbertHessian period hPeriod configuration data
        analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData).chartBridge.basePoint
        (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
          configuration data analysis chartData
            (globalCandidateAMinimalPhysicalCommonHilbertChartOfDenseCoreClosure
              period hPeriod configuration data analysis chartData closure)) 0
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis first)
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalCovariantHessianOnCore period
        hPeriod configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData).chartBridge first second := by
  exact globalCandidateAMinimalPhysicalNonlinearHilbertHessian_smooth_eq_covariant
    period hPeriod configuration data analysis chartData
      (globalCandidateAMinimalPhysicalCommonHilbertChartOfDenseCoreClosure
        period hPeriod configuration data analysis chartData closure)
      first second

end Consequences

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalDenseCoreHilbertClosure4D
end JanusFormal
