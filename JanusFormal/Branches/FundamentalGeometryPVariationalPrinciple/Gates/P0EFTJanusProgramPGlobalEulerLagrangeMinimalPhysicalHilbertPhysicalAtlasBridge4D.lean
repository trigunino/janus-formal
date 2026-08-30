import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertResidualAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalAtlasRetraction4D

/-!
# Bridge from the Hilbert residual carrier to the physical variational atlas

For the minimal physical chart, every admissible state of the nonlinear
Hilbert residual atlas represents a configuration in the retractive physical
atlas.  Because the Hilbert chart realization is an equivalence, its strong
residual vanishes exactly when the chart Euler one-form vanishes.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertPhysicalAtlasBridge4D

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
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D
open P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalAtlas4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalAtlasRetraction4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAtlasResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertResidualAtlas4D

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

private theorem continuousLinearMap_comp_equiv_eq_zero_iff
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (equiv : E ≃L[Real] F) (functional : F →L[Real] Real) :
    functional.comp equiv.toContinuousLinearMap = 0 ↔ functional = 0 := by
  constructor
  · intro hComp
    apply ContinuousLinearMap.ext
    intro value
    have hValue := DFunLike.congr_fun hComp (equiv.symm value)
    simpa using hValue
  · intro hFunctional
    rw [hFunctional]
    rfl

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

local instance denseCoreCommonModule : Module Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedModule period hPeriod configuration data analysis

/-- The minimal chart point represented by a common-Hilbert state. -/
def globalCandidateAMinimalPhysicalHilbertChartPoint
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model :=
  globalCandidateANonlinearHilbertChartPoint period hPeriod configuration data
    analysis
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData)
    (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
      configuration data analysis chartData).chartBridge.basePoint
    (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
      configuration data analysis chartData hilbertChart) state

/-- Membership in the Hilbert residual carrier is precisely admissibility of
the represented minimal-chart point. -/
theorem globalCandidateAMinimalPhysicalHilbertChartPoint_mem_domain
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : state ∈
      (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).carrier) :
    globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
        configuration data analysis chartData hilbertChart state ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).family.domain := by
  exact hState

/-- The physical configuration represented by an admissible Hilbert state. -/
def globalCandidateAMinimalPhysicalConfigurationOfHilbertState
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : state ∈
      (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).carrier) :
    GlobalFieldConfiguration period hPeriod :=
  localChartConfigurationAt period hPeriod
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData)
    ⟨globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
        configuration data analysis chartData hilbertChart state,
      globalCandidateAMinimalPhysicalHilbertChartPoint_mem_domain period hPeriod
        configuration data analysis chartData hilbertChart state hState⟩

/-- The strong Hilbert residual vanishes exactly when the genuine local Euler
one-form vanishes at the represented chart point. -/
theorem globalCandidateAMinimalPhysicalHilbertCritical_iff_localEuler
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).IsEulerCritical
          period hPeriod state ↔
      globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
          configuration data analysis chartData hilbertChart state) = 0 := by
  rw [GlobalCandidateANonlinearHilbertResidualAtlas.IsEulerCritical]
  change
    globalCandidateANonlinearHilbertRieszResidual period hPeriod configuration
        data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData).chartBridge.basePoint
        (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
          configuration data analysis chartData hilbertChart) state = 0 ↔ _
  rw [← globalCandidateANonlinearHilbertEulerCovector_eq_zero_iff_rieszResidual
    period hPeriod configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData).chartBridge.basePoint
      (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
        configuration data analysis chartData hilbertChart) state]
  change
    (globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
          configuration data analysis chartData hilbertChart state)).comp
        (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
          configuration data analysis chartData hilbertChart) = 0 ↔ _
  constructor
  · intro hComp
    apply ContinuousLinearMap.ext
    intro value
    have hValue := DFunLike.congr_fun hComp (hilbertChart.toChart.symm value)
    simpa [globalCandidateAMinimalPhysicalHilbertChartRealization] using hValue
  · intro hEuler
    rw [hEuler]
    rfl

/-- Every admissible Hilbert state represents a configuration covered by the
retractive physical atlas. -/
theorem globalCandidateAMinimalPhysicalConfigurationOfHilbertState_mem_atlas
    (retraction : LocalChartCoordinateRetraction period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData))
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : state ∈
      (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).carrier) :
    globalCandidateAMinimalPhysicalConfigurationOfHilbertState period hPeriod
        configuration data analysis chartData hilbertChart state hState ∈
      (globalCandidateAMinimalPhysicalVariationalAtlas_of_retraction period
        hPeriod configuration data analysis chartData retraction).carrier := by
  let point :
      { point :
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData).Model //
        point ∈
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData).family.domain } :=
    ⟨globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
        configuration data analysis chartData hilbertChart state,
      globalCandidateAMinimalPhysicalHilbertChartPoint_mem_domain period hPeriod
        configuration data analysis chartData hilbertChart state hState⟩
  change
    globalCandidateAMinimalPhysicalConfigurationOfHilbertState period hPeriod
        configuration data analysis chartData hilbertChart state hState ∈
      Set.range (localChartConfigurationAt period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData))
  exact ⟨point, rfl⟩

/-- On the represented physical configuration, Hilbert criticality and
chart-independent physical-atlas criticality are the same equation. -/
theorem globalCandidateAMinimalPhysicalHilbertCritical_iff_physicalAtlas
    (retraction : LocalChartCoordinateRetraction period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData))
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : state ∈
      (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).carrier) :
    (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).IsEulerCritical
          period hPeriod state ↔
      (globalCandidateAMinimalPhysicalVariationalAtlas_of_retraction period
        hPeriod configuration data analysis chartData retraction).IsEulerCritical
          period hPeriod
          (globalCandidateAMinimalPhysicalConfigurationOfHilbertState period
            hPeriod configuration data analysis chartData hilbertChart state
              hState) := by
  let physicalAtlas :=
    globalCandidateAMinimalPhysicalVariationalAtlas_of_retraction period hPeriod
      configuration data analysis chartData retraction
  let point := globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
    configuration data analysis chartData hilbertChart state
  have hPoint : point ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).family.domain :=
    globalCandidateAMinimalPhysicalHilbertChartPoint_mem_domain period hPeriod
      configuration data analysis chartData hilbertChart state hState
  have hPhysical :
      physicalAtlas.IsEulerCritical period hPeriod
          (globalCandidateAMinimalPhysicalConfigurationOfHilbertState period
            hPeriod configuration data analysis chartData hilbertChart state
              hState) ↔
        globalCandidateALocalEulerLagrangeOperator period hPeriod
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData) point = 0 := by
    apply physicalAtlas.isEulerCritical_iff period hPeriod
      (globalCandidateAMinimalPhysicalConfigurationOfHilbertState period hPeriod
        configuration data analysis chartData hilbertChart state hState)
      () point hPoint
    rfl
  exact
    (globalCandidateAMinimalPhysicalHilbertCritical_iff_localEuler period
      hPeriod configuration data analysis chartData hilbertChart state).trans
      hPhysical.symm

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertPhysicalAtlasBridge4D
end JanusFormal
