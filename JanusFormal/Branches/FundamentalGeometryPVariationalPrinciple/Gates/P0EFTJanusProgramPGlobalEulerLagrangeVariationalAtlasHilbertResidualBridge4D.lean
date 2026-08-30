import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAtlasResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D

/-!
# Residual atlas constructed from a physical variational atlas

A physical atlas already determines every nonlinear chart transition whenever
two admissible chart points represent the same configuration.  Thus a family
of compatible Hilbert chart equivalences needs no second collection of
pairwise transition witnesses.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeVariationalAtlasHilbertResidualBridge4D

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
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAtlasResidual4D

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

local instance atlasCommonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedNormedAddCommGroup period hPeriod configuration data analysis

local instance atlasCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedNormedSpace period hPeriod configuration data analysis

local instance atlasCommonModule : Module Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedModule period hPeriod configuration data analysis

/-- Point of a physical atlas chart represented by a Hilbert state. -/
def globalCandidateAVariationalAtlasHilbertPoint
    (physicalAtlas : GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure)
    (basePoint : (index : physicalAtlas.Index) →
      (physicalAtlas.chart index).Model)
    (chartEquiv : (index : physicalAtlas.Index) →
      CommonAugmentedHilbert period hPeriod configuration data analysis
        ≃L[Real] (physicalAtlas.chart index).Model)
    (index : physicalAtlas.Index)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    (physicalAtlas.chart index).Model :=
  globalCandidateANonlinearHilbertChartPoint period hPeriod configuration data
    analysis (physicalAtlas.chart index) (basePoint index)
      (chartEquiv index).toContinuousLinearMap state

/-- Compatible Hilbert realizations over a physical variational atlas.  The
physical atlas itself supplies every transition appearing in the final
residual atlas. -/
structure GlobalCandidateAVariationalAtlasHilbertRealization
    (physicalAtlas : GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure) where
  basePoint : (index : physicalAtlas.Index) →
    (physicalAtlas.chart index).Model
  chartEquiv : (index : physicalAtlas.Index) →
    CommonAugmentedHilbert period hPeriod configuration data analysis
      ≃L[Real] (physicalAtlas.chart index).Model
  carrier : Set
    (CommonAugmentedHilbert period hPeriod configuration data analysis)
  referenceIndex : physicalAtlas.Index
  point_mem : ∀ (state : CommonAugmentedHilbert period hPeriod configuration
      data analysis), state ∈ carrier → ∀ index : physicalAtlas.Index,
    globalCandidateAVariationalAtlasHilbertPoint period hPeriod configuration
        data analysis physicalAtlas basePoint chartEquiv index state ∈
      (physicalAtlas.chart index).family.domain
  same_configuration : ∀ (state : CommonAugmentedHilbert period hPeriod
      configuration data analysis) (hState : state ∈ carrier)
      (first second : physicalAtlas.Index),
    ((physicalAtlas.chart first).family.datumAt
      (globalCandidateAVariationalAtlasHilbertPoint period hPeriod
        configuration data analysis physicalAtlas basePoint chartEquiv first
          state)
      (point_mem state hState first)).1 =
    ((physicalAtlas.chart second).family.datumAt
      (globalCandidateAVariationalAtlasHilbertPoint period hPeriod
        configuration data analysis physicalAtlas basePoint chartEquiv second
          state)
      (point_mem state hState second)).1
  represented_mem : ∀ (state : CommonAugmentedHilbert period hPeriod
      configuration data analysis) (hState : state ∈ carrier),
    ((physicalAtlas.chart referenceIndex).family.datumAt
      (globalCandidateAVariationalAtlasHilbertPoint period hPeriod
        configuration data analysis physicalAtlas basePoint chartEquiv
          referenceIndex state)
      (point_mem state hState referenceIndex)).1 ∈ physicalAtlas.carrier
  derivative_compatible : ∀
      (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
      (hState : state ∈ carrier) (first second : physicalAtlas.Index),
    ((physicalAtlas.transition first second
      (globalCandidateAVariationalAtlasHilbertPoint period hPeriod
        configuration data analysis physicalAtlas basePoint chartEquiv first
          state)
      (globalCandidateAVariationalAtlasHilbertPoint period hPeriod
        configuration data analysis physicalAtlas basePoint chartEquiv second
          state)
      (point_mem state hState first) (point_mem state hState second)
      (same_configuration state hState first second)).derivative.toContinuousLinearMap.comp
        (chartEquiv first).toContinuousLinearMap) =
      (chartEquiv second).toContinuousLinearMap

namespace GlobalCandidateAVariationalAtlasHilbertRealization

variable
    {physicalAtlas : GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure}
    (realization : GlobalCandidateAVariationalAtlasHilbertRealization period
      hPeriod configuration data analysis physicalAtlas)

/-- The residual atlas obtained without supplying any new transition
witnesses. -/
def toNonlinearHilbertResidualAtlas :
    GlobalCandidateANonlinearHilbertResidualAtlas period hPeriod
      (measure := measure) configuration data analysis where
  Index := physicalAtlas.Index
  chart := physicalAtlas.chart
  basePoint := realization.basePoint
  chartRealization := fun index ↦
    (realization.chartEquiv index).toContinuousLinearMap
  carrier := realization.carrier
  referenceIndex := realization.referenceIndex
  transition := by
    intro state hState first second
    exact physicalAtlas.transition first second
      (globalCandidateAVariationalAtlasHilbertPoint period hPeriod
        configuration data analysis physicalAtlas realization.basePoint
          realization.chartEquiv first state)
      (globalCandidateAVariationalAtlasHilbertPoint period hPeriod
        configuration data analysis physicalAtlas realization.basePoint
          realization.chartEquiv second state)
      (realization.point_mem state hState first)
      (realization.point_mem state hState second)
      (realization.same_configuration state hState first second)
  derivative_compatible := realization.derivative_compatible

/-- Physical configuration represented by an admissible Hilbert state in the
reference chart. -/
def representedConfiguration
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : state ∈ realization.carrier) :
    GlobalFieldConfiguration period hPeriod :=
  ((physicalAtlas.chart realization.referenceIndex).family.datumAt
    (globalCandidateAVariationalAtlasHilbertPoint period hPeriod configuration
      data analysis physicalAtlas realization.basePoint realization.chartEquiv
        realization.referenceIndex state)
    (realization.point_mem state hState realization.referenceIndex)).1

/-- The represented configuration lies in the physical atlas carrier. -/
theorem representedConfiguration_mem
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : state ∈ realization.carrier) :
    realization.representedConfiguration period hPeriod configuration data
      analysis state hState ∈
      physicalAtlas.carrier :=
  realization.represented_mem state hState

/-- Every Hilbert chart point represents the same descended physical
configuration. -/
theorem chart_represents
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : state ∈ realization.carrier)
    (index : physicalAtlas.Index) :
    physicalAtlas.Represents period hPeriod
      (realization.representedConfiguration period hPeriod configuration data
        analysis state hState) index
      (globalCandidateAVariationalAtlasHilbertPoint period hPeriod
        configuration data analysis physicalAtlas realization.basePoint
          realization.chartEquiv index state)
      (realization.point_mem state hState index) := by
  exact realization.same_configuration state hState index
    realization.referenceIndex

/-- The descended strong residual equation is exactly physical-atlas
criticality of the represented configuration. -/
theorem isEulerCritical_iff_physicalAtlas
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : state ∈ realization.carrier) :
    (realization.toNonlinearHilbertResidualAtlas period hPeriod).IsEulerCritical
        period hPeriod state ↔
      physicalAtlas.IsEulerCritical period hPeriod
        (realization.representedConfiguration period hPeriod configuration data
          analysis state hState) := by
  let index := realization.referenceIndex
  let point := globalCandidateAVariationalAtlasHilbertPoint period hPeriod
    configuration data analysis physicalAtlas realization.basePoint
      realization.chartEquiv index state
  let euler := globalCandidateALocalEulerLagrangeOperator period hPeriod
    (physicalAtlas.chart index) point
  have hResidual :
      (realization.toNonlinearHilbertResidualAtlas period hPeriod).IsEulerCritical
          period hPeriod state ↔ euler = 0 := by
    rw [GlobalCandidateANonlinearHilbertResidualAtlas.IsEulerCritical]
    change
      globalCandidateANonlinearHilbertRieszResidual period hPeriod configuration
          data analysis (physicalAtlas.chart index)
          (realization.basePoint index)
          (realization.chartEquiv index).toContinuousLinearMap state = 0 ↔ _
    rw [← globalCandidateANonlinearHilbertEulerCovector_eq_zero_iff_rieszResidual
      period hPeriod configuration data analysis (physicalAtlas.chart index)
        (realization.basePoint index)
        (realization.chartEquiv index).toContinuousLinearMap state]
    change
      euler.comp (realization.chartEquiv index).toContinuousLinearMap = 0 ↔
        euler = 0
    constructor
    · intro hComp
      apply ContinuousLinearMap.ext
      intro value
      have hValue := DFunLike.congr_fun hComp
        ((realization.chartEquiv index).symm value)
      change euler ((realization.chartEquiv index)
        ((realization.chartEquiv index).symm value)) = 0 at hValue
      simpa using hValue
    · intro hEuler
      rw [hEuler]
      rfl
  have hPhysical :
      physicalAtlas.IsEulerCritical period hPeriod
          (realization.representedConfiguration period hPeriod configuration data
            analysis state hState) ↔
        euler = 0 := by
    apply physicalAtlas.isEulerCritical_iff period hPeriod
      (realization.representedConfiguration period hPeriod configuration data
        analysis state hState) index
      point (realization.point_mem state hState index)
    exact realization.chart_represents period hPeriod configuration data
      analysis state hState index
  exact hResidual.trans hPhysical.symm

end GlobalCandidateAVariationalAtlasHilbertRealization

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeVariationalAtlasHilbertResidualBridge4D
end JanusFormal
