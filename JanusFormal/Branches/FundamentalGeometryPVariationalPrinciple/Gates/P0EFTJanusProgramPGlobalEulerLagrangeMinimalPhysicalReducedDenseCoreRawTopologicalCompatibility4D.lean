import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreTopologicalClosure4D

/-!
# Raw-core form of the reduced topological norm compatibility

The two uniform norm bounds needed by the topological dense-core closure are
equivalent to their versions on raw smooth representatives.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreRawTopologicalCompatibility4D

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
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreTopologicalClosure4D

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

local instance reducedRawTopologicalCommonNormedAddCommGroup :
    NormedAddCommGroup
      (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance reducedRawTopologicalCommonInnerProductSpace :
    InnerProductSpace Real
      (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkInnerProductSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance reducedRawTopologicalCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (reducedRawTopologicalCommonInnerProductSpace period hPeriod configuration
    data analysis).toNormedSpace

local instance reducedRawTopologicalCommonModule : Module Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (reducedRawTopologicalCommonNormedSpace period hPeriod configuration data
    analysis).toModule

local instance reducedRawTopologicalCommonCompleteSpace : CompleteSpace
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkCompleteSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- The two uniform comparison bounds on the physical quotient smooth core. -/
def GlobalCandidateAMinimalPhysicalReducedCoreTopologicalCompatibility : Prop :=
  (∃ constant : Real,
    ∀ core : GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
        configuration data analysis,
      ‖globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
          configuration data analysis chartData core‖ ≤
        constant *
          ‖globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
            period hPeriod configuration data analysis core‖) ∧
  (∃ constant : Real,
    ∀ core : GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
        configuration data analysis,
      ‖globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis core‖ ≤
        constant *
          ‖globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
            configuration data analysis chartData core‖)

/-- The same two bounds before quotienting the raw smooth core. -/
def GlobalCandidateAMinimalPhysicalReducedRawCoreTopologicalCompatibility :
    Prop :=
  (∃ constant : Real,
    ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
        analysis,
      ‖globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
          analysis
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData)
          (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
            configuration data analysis chartData) core‖ ≤
        constant *
          ‖globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period
            hPeriod configuration data analysis core‖) ∧
  (∃ constant : Real,
    ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
        analysis,
      ‖globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period hPeriod
          configuration data analysis core‖ ≤
        constant *
          ‖globalCandidateACanonicalSixCoreToChart period hPeriod configuration
            data analysis
            (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
              configuration data analysis chartData)
            (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period
              hPeriod configuration data analysis chartData) core‖)

/-- Quotient and raw representatives carry exactly the same two norm-bound
obligations. -/
theorem globalCandidateAMinimalPhysicalReducedCoreTopologicalCompatibility_iff_rawCore :
    GlobalCandidateAMinimalPhysicalReducedCoreTopologicalCompatibility period
        hPeriod configuration data analysis chartData ↔
      GlobalCandidateAMinimalPhysicalReducedRawCoreTopologicalCompatibility
        period hPeriod configuration data analysis chartData := by
  constructor
  · rintro ⟨⟨forwardConstant, hForward⟩, ⟨inverseConstant, hInverse⟩⟩
    constructor
    · refine ⟨forwardConstant, ?_⟩
      intro core
      simpa only [globalCandidateAMinimalPhysicalReducedCoreToChart_mk,
        globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk]
        using hForward (Submodule.Quotient.mk core)
    · refine ⟨inverseConstant, ?_⟩
      intro core
      simpa only [globalCandidateAMinimalPhysicalReducedCoreToChart_mk,
        globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk]
        using hInverse (Submodule.Quotient.mk core)
  · rintro ⟨⟨forwardConstant, hForward⟩, ⟨inverseConstant, hInverse⟩⟩
    constructor
    · refine ⟨forwardConstant, ?_⟩
      intro core
      obtain ⟨representative, rfl⟩ := Submodule.Quotient.mk_surjective
        (globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
          configuration data analysis) core
      simpa only [globalCandidateAMinimalPhysicalReducedCoreToChart_mk,
        globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk]
        using hForward representative
    · refine ⟨inverseConstant, ?_⟩
      intro core
      obtain ⟨representative, rfl⟩ := Submodule.Quotient.mk_surjective
        (globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
          configuration data analysis) core
      simpa only [globalCandidateAMinimalPhysicalReducedCoreToChart_mk,
        globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk]
        using hInverse representative

/-- Raw comparison bounds, chart completeness, and quotient density assemble
the topological dense-core closure certificate. -/
def globalCandidateAMinimalPhysicalReducedDenseCoreTopologicalClosure_of_rawCoreBounds
    (chartComplete : CompleteSpace
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model)
    (denseRange : DenseRange
      (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
        configuration data analysis chartData))
    (rawCompatibility :
      GlobalCandidateAMinimalPhysicalReducedRawCoreTopologicalCompatibility
        period hPeriod configuration data analysis chartData) :
    ProgramPGlobalMinimalPhysicalReducedDenseCoreTopologicalClosureData4D period
      hPeriod configuration data analysis chartData := by
  have compatibility :=
    (globalCandidateAMinimalPhysicalReducedCoreTopologicalCompatibility_iff_rawCore
      period hPeriod configuration data analysis chartData).mpr rawCompatibility
  exact
    { chartComplete := chartComplete
      forward_bound := compatibility.1
      inverse_bound := compatibility.2
      dense_range := denseRange }

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreRawTopologicalCompatibility4D
end JanusFormal
