import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertBlockSum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D

/-!
# Hilbert residual pairings with component PDE residuals

The inverse Hilbert chart realizes each pure physical chart test.  Pairing the
nonlinear Hilbert residual with that inverse image is therefore exactly the
corresponding supplied PDE residual pairing, for every bulk component and for
primitive SpinC matter.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertComponentPDEPairing4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAtlasResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentwisePDEResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertResidualAtlas4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertPhysicalAtlasBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertBlockSum4D

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
  Submodule.addCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModule :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

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

local instance denseCoreCommonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedNormedAddCommGroup period hPeriod configuration data analysis

local instance denseCoreCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedNormedSpace period hPeriod configuration data analysis

/-- Every supplied separating bulk-component residual is an exact coordinate
pairing of the nonlinear Hilbert residual. -/
theorem globalCandidateAMinimalPhysicalHilbertResidual_pairing_eq_componentResidual
    {Component : Type*} [AddCommGroup Component] [Module Real Component]
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : state ∈
      (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).carrier)
    (componentCovector : Component →ₗ[Real] Real)
    (inclusion : Component →ₗ[Real]
      GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod)
    (hRestriction : componentCovector =
      (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData
          (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
            configuration data analysis chartData hilbertChart state)).comp
        inclusion)
    (representation : SeparatingPDEResidualRepresentation componentCovector)
    (variation : Component) :
    inner Real
        ((globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
          hPeriod configuration data analysis chartData hilbertChart).residual
            period hPeriod state)
        (hilbertChart.toChart.symm
          (globalCandidateAMinimalPhysicalSevenBulkChartDirection period hPeriod
            configuration data analysis chartData (inclusion variation))) =
      representation.pairing representation.residual variation := by
  rw [globalCandidateAMinimalPhysicalHilbertResidual_pairing_symm_eq_blockSum
    period hPeriod configuration data analysis chartData hilbertChart state
      hState
      (globalCandidateAMinimalPhysicalSevenBulkChartDirection period hPeriod
        configuration data analysis chartData (inclusion variation))]
  exact
    globalCandidateAMinimalPhysicalComponentBlockSum_eq_residualPairing period
      hPeriod configuration data analysis chartData
        (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
          configuration data analysis chartData hilbertChart state)
        (globalCandidateAMinimalPhysicalHilbertChartPoint_mem_domain period
          hPeriod configuration data analysis chartData hilbertChart state
            hState)
        componentCovector inclusion hRestriction representation variation

/-- The primitive SpinC residual is the remaining exact Hilbert residual
coordinate pairing. -/
theorem globalCandidateAMinimalPhysicalHilbertResidual_pairing_eq_spinCResidual
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : state ∈
      (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).carrier)
    (pdeData : GlobalCandidateAMinimalPhysicalComponentwisePDEDataAt period
      hPeriod configuration data analysis chartData
        (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
          configuration data analysis chartData hilbertChart state))
    (variation : Sector → D9PrimitiveSpinCSmoothSection period hPeriod
      .positiveQuarter) :
    inner Real
        ((globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
          hPeriod configuration data analysis chartData hilbertChart).residual
            period hPeriod state)
        (hilbertChart.toChart.symm
          (globalCandidateAMinimalPhysicalSpinCMatterChartDirection period
            hPeriod configuration data analysis chartData variation)) =
      pdeData.spinC.pairing pdeData.spinC.residual variation := by
  rw [globalCandidateAMinimalPhysicalHilbertResidual_pairing_symm_eq_blockSum
    period hPeriod configuration data analysis chartData hilbertChart state
      hState
      (globalCandidateAMinimalPhysicalSpinCMatterChartDirection period hPeriod
        configuration data analysis chartData variation)]
  exact globalCandidateAMinimalPhysicalSpinCBlockSum_eq_residualPairing period
    hPeriod configuration data analysis chartData
      (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
        configuration data analysis chartData hilbertChart state)
      (globalCandidateAMinimalPhysicalHilbertChartPoint_mem_domain period
        hPeriod configuration data analysis chartData hilbertChart state hState)
      pdeData variation

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertComponentPDEPairing4D
end JanusFormal
