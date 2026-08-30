import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertPhysicalAtlasBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeVariationalAtlasHilbertResidualBridge4D

/-!
# Canonical Hilbert realization of the minimal physical singleton atlas

The minimal retractive physical atlas and its Hilbert chart equivalence satisfy
the generic multi-chart realization contract without further transition or
compatibility hypotheses.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalVariationalAtlasHilbertRealization4D

set_option autoImplicit false
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
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D
open P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalAtlas4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalAtlasRetraction4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAtlasResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertResidualAtlas4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertPhysicalAtlasBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeVariationalAtlasHilbertResidualBridge4D

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

section

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
    (hilbertChart : ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period
      hPeriod configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData))
    (retraction : LocalChartCoordinateRetraction period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData))

local instance realizationCommonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedNormedAddCommGroup period hPeriod configuration data analysis

local instance realizationCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedNormedSpace period hPeriod configuration data analysis

local instance realizationCommonModule : Module Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedModule period hPeriod configuration data analysis

/-- The minimal physical singleton atlas satisfies the generic compatible
Hilbert-realization contract canonically. -/
def globalCandidateAMinimalPhysicalVariationalAtlasHilbertRealization :
    GlobalCandidateAVariationalAtlasHilbertRealization period hPeriod
      configuration data analysis
      (globalCandidateAMinimalPhysicalVariationalAtlas_of_retraction period
        hPeriod configuration data analysis chartData retraction) := by
  let physicalAtlas :=
    globalCandidateAMinimalPhysicalVariationalAtlas_of_retraction period hPeriod
      configuration data analysis chartData retraction
  refine
    { basePoint := fun _ ↦
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData).chartBridge.basePoint
      chartEquiv := fun _ ↦ hilbertChart.toChart
      carrier :=
        (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
          hPeriod configuration data analysis chartData hilbertChart).carrier
      referenceIndex := ()
      point_mem := ?_
      same_configuration := ?_
      represented_mem := ?_
      derivative_compatible := ?_ }
  · intro state hState index
    cases index
    exact globalCandidateAMinimalPhysicalHilbertChartPoint_mem_domain period
      hPeriod configuration data analysis chartData hilbertChart state hState
  · intro state hState first second
    cases first
    cases second
    rfl
  · intro state hState
    exact
      globalCandidateAMinimalPhysicalConfigurationOfHilbertState_mem_atlas
        period hPeriod configuration data analysis chartData hilbertChart
          retraction state hState
  · intro state hState first second
    cases first
    cases second
    rfl

/-- Residual atlas obtained through the generic physical-atlas constructor. -/
def globalCandidateAMinimalPhysicalResidualAtlasViaVariationalAtlas :
    GlobalCandidateANonlinearHilbertResidualAtlas period hPeriod
      (measure := measure) configuration data analysis :=
  (globalCandidateAMinimalPhysicalVariationalAtlasHilbertRealization period
    hPeriod configuration data analysis chartData hilbertChart retraction).toNonlinearHilbertResidualAtlas
      period hPeriod

/-- The generic construction keeps exactly the original Hilbert carrier. -/
theorem globalCandidateAMinimalPhysicalResidualAtlasViaVariationalAtlas_carrier :
    (globalCandidateAMinimalPhysicalResidualAtlasViaVariationalAtlas period
      hPeriod configuration data analysis chartData hilbertChart
        retraction).carrier =
      (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).carrier :=
  rfl

/-- The generic and direct constructions define the same nonlinear action. -/
theorem globalCandidateAMinimalPhysicalResidualAtlasViaVariationalAtlas_action :
    (globalCandidateAMinimalPhysicalResidualAtlasViaVariationalAtlas period
        hPeriod configuration data analysis chartData hilbertChart
          retraction).action period hPeriod =
      (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).action
          period hPeriod :=
  rfl

/-- The generic and direct constructions define the same strong residual. -/
theorem globalCandidateAMinimalPhysicalResidualAtlasViaVariationalAtlas_residual :
    (globalCandidateAMinimalPhysicalResidualAtlasViaVariationalAtlas period
        hPeriod configuration data analysis chartData hilbertChart
          retraction).residual period hPeriod =
      (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).residual
          period hPeriod :=
  rfl

/-- Hence their criticality predicates coincide at every Hilbert state. -/
theorem globalCandidateAMinimalPhysicalResidualAtlasViaVariationalAtlas_critical
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    (globalCandidateAMinimalPhysicalResidualAtlasViaVariationalAtlas period
        hPeriod configuration data analysis chartData hilbertChart
          retraction).IsEulerCritical period hPeriod state ↔
      (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).IsEulerCritical
          period hPeriod state :=
  Iff.rfl

end


end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalVariationalAtlasHilbertRealization4D
end JanusFormal
