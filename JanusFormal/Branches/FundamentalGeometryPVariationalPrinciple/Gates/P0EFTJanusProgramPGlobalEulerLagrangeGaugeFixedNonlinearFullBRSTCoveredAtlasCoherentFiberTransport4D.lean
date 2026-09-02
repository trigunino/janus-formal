import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianL2ResidualRegularity4D

/-!
# Coherent bounded transports on a covered full-BRST atlas

Every covering member already has a bounded frame from the selected member.
Normalizing transports through that common frame constructs identity, inverse
and cocycle laws without adding coherence assumptions.  These are transports
of the linear chart fibres; no inverse nonlinear chart germ is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoveredAtlasCoherentFiberTransport4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTProjectionCompatibleCoveredAtlas4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section CoherentTransport

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}

private abbrev FullChart (chartData :
    ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    (measure := measure) configuration data analysis chartData

private abbrev TransportChartNormedAddCommGroup
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedAddCommGroup
      (FullChart period hPeriod (configuration := configuration) (data := data)
        (analysis := analysis) chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedAddCommGroupCalculus
    period hPeriod (measure := measure) configuration data analysis chartData

private abbrev TransportChartNormedSpace
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedSpace Real
      (FullChart period hPeriod (configuration := configuration) (data := data)
        (analysis := analysis) chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedSpaceCalculus
    period hPeriod (measure := measure) configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 11000) transportChartNormedAddCommGroup
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedAddCommGroup
      (FullChart period hPeriod (configuration := configuration) (data := data)
        (analysis := analysis) chartData) :=
  TransportChartNormedAddCommGroup period hPeriod
    (configuration := configuration) (data := data) (analysis := analysis)
    chartData

@[implicit_reducible]
local instance (priority := 11000) transportChartNormedSpace
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    NormedSpace Real
      (FullChart period hPeriod (configuration := configuration) (data := data)
        (analysis := analysis) chartData) :=
  TransportChartNormedSpace period hPeriod
    (configuration := configuration) (data := data) (analysis := analysis)
    chartData

variable
    (atlas :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleCoveredAtlas
        period hPeriod (measure := measure) configuration data analysis)

/-- Atlas members which contain a fixed covered state. -/
abbrev CoveringIndexAt (state : atlas.carrier) :=
  {index : atlas.Index //
    atlas.chartState period hPeriod state.1 index ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis (atlas.chartData index)}

/-- Bounded frame from the selected chart fibre to one covering fibre. -/
noncomputable def selectedFrame (state : atlas.carrier)
    (index : CoveringIndexAt period hPeriod atlas state) :
    FullChart period hPeriod (configuration := configuration) (data := data)
        (analysis := analysis)
        (atlas.chartData (atlas.selectedIndex period hPeriod state)) ≃L[Real]
      FullChart period hPeriod (configuration := configuration) (data := data)
        (analysis := analysis)
        (atlas.chartData index.1) :=
  (atlas.selectedTransition period hPeriod state index.1 index.2).transport

/-- Canonically normalized bounded transport between two covering fibres. -/
noncomputable def coherentTransport (state : atlas.carrier)
    (first second : CoveringIndexAt period hPeriod atlas state) :
    FullChart period hPeriod (configuration := configuration) (data := data)
        (analysis := analysis)
        (atlas.chartData first.1) ≃L[Real]
      FullChart period hPeriod (configuration := configuration) (data := data)
        (analysis := analysis)
        (atlas.chartData second.1) :=
  (selectedFrame period hPeriod atlas state first).symm.trans
    (selectedFrame period hPeriod atlas state second)

@[simp]
theorem coherentTransport_self (state : atlas.carrier)
    (index : CoveringIndexAt period hPeriod atlas state) :
    coherentTransport period hPeriod atlas state index index =
      ContinuousLinearEquiv.refl Real
        (FullChart period hPeriod (configuration := configuration) (data := data)
          (analysis := analysis)
          (atlas.chartData index.1)) := by
  apply ContinuousLinearEquiv.ext
  funext direction
  simp [coherentTransport]

@[simp]
theorem coherentTransport_symm (state : atlas.carrier)
    (first second : CoveringIndexAt period hPeriod atlas state) :
    (coherentTransport period hPeriod atlas state first second).symm =
      coherentTransport period hPeriod atlas state second first := by
  apply ContinuousLinearEquiv.ext
  funext direction
  simp [coherentTransport]

theorem coherentTransport_trans (state : atlas.carrier)
    (first second third : CoveringIndexAt period hPeriod atlas state) :
    (coherentTransport period hPeriod atlas state first second).trans
        (coherentTransport period hPeriod atlas state second third) =
      coherentTransport period hPeriod atlas state first third := by
  apply ContinuousLinearEquiv.ext
  funext direction
  simp [coherentTransport]

/-- The exact Euler covectors form a compatible section for the normalized
transport cocycle. -/
theorem eulerOperator_coherentTransport (state : atlas.carrier)
    (first second : CoveringIndexAt period hPeriod atlas state) :
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis (atlas.chartData first.1)
          (atlas.chartState period hPeriod state.1 first.1) =
      (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis (atlas.chartData second.1)
          (atlas.chartState period hPeriod state.1 second.1)).comp
        (coherentTransport period hPeriod atlas state first
          second).toContinuousLinearMap := by
  let firstFrame := selectedFrame period hPeriod atlas state first
  let secondFrame := selectedFrame period hPeriod atlas state second
  have hFirst :=
    atlas.eulerOperator_eq_chart_comp_transport period hPeriod state first.1
      first.2
  have hSecond :=
    atlas.eulerOperator_eq_chart_comp_transport period hPeriod state second.1
      second.2
  apply ContinuousLinearMap.ext
  intro direction
  let sourceDirection := firstFrame.symm direction
  have hFirstAt := congrArg (fun covector => covector sourceDirection) hFirst
  have hSecondAt := congrArg (fun covector => covector sourceDirection) hSecond
  change
    atlas.eulerOperator period hPeriod state sourceDirection =
      globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis (atlas.chartData first.1)
          (atlas.chartState period hPeriod state.1 first.1)
            (firstFrame sourceDirection) at hFirstAt
  change
    atlas.eulerOperator period hPeriod state sourceDirection =
      globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis (atlas.chartData second.1)
          (atlas.chartState period hPeriod state.1 second.1)
            (secondFrame sourceDirection) at hSecondAt
  rw [show firstFrame sourceDirection = direction by
    exact firstFrame.apply_symm_apply direction] at hFirstAt
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis (atlas.chartData first.1)
          (atlas.chartState period hPeriod state.1 first.1) direction =
      globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis (atlas.chartData second.1)
          (atlas.chartState period hPeriod state.1 second.1)
            (secondFrame (firstFrame.symm direction))
  exact hFirstAt.symm.trans hSecondAt

/-- Criticality is constant on the coherent fibre groupoid. -/
theorem eulerOperator_eq_zero_iff_coherentTransport (state : atlas.carrier)
    (first second : CoveringIndexAt period hPeriod atlas state) :
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis (atlas.chartData first.1)
            (atlas.chartState period hPeriod state.1 first.1) = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis (atlas.chartData second.1)
            (atlas.chartState period hPeriod state.1 second.1) = 0 := by
  rw [← atlas.isEulerCritical_iff_chart_eulerOperator_eq_zero period hPeriod
    state first.1 first.2]
  exact atlas.isEulerCritical_iff_chart_eulerOperator_eq_zero period hPeriod
    state second.1 second.2

/-- Gate 274: the covered full-BRST fibres carry a constructed bounded
identity/inverse/cocycle transport, and the exact Euler covectors descend as
a compatible section. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_covered_atlas_coherent_fiber_transport_gate
    (state : atlas.carrier)
    (first second third : CoveringIndexAt period hPeriod atlas state) :
    coherentTransport period hPeriod atlas state first first =
        ContinuousLinearEquiv.refl Real
          (FullChart period hPeriod (configuration := configuration) (data := data)
            (analysis := analysis)
            (atlas.chartData first.1)) ∧
      (coherentTransport period hPeriod atlas state first second).symm =
        coherentTransport period hPeriod atlas state second first ∧
      (coherentTransport period hPeriod atlas state first second).trans
          (coherentTransport period hPeriod atlas state second third) =
        coherentTransport period hPeriod atlas state first third ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis (atlas.chartData first.1)
            (atlas.chartState period hPeriod state.1 first.1) =
        (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis (atlas.chartData second.1)
            (atlas.chartState period hPeriod state.1 second.1)).comp
          (coherentTransport period hPeriod atlas state first
            second).toContinuousLinearMap ∧
      (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
            configuration data analysis (atlas.chartData first.1)
              (atlas.chartState period hPeriod state.1 first.1) = 0 ↔
        globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
            configuration data analysis (atlas.chartData second.1)
              (atlas.chartState period hPeriod state.1 second.1) = 0) :=
  ⟨coherentTransport_self period hPeriod atlas state first,
    coherentTransport_symm period hPeriod atlas state first second,
    coherentTransport_trans period hPeriod atlas state first second third,
    eulerOperator_coherentTransport period hPeriod atlas state first second,
    eulerOperator_eq_zero_iff_coherentTransport period hPeriod atlas state first
      second⟩

end CoherentTransport
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoveredAtlasCoherentFiberTransport4D
end JanusFormal
