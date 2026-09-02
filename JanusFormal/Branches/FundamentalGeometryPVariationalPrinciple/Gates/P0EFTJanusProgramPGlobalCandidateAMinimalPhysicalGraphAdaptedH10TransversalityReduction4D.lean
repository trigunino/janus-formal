import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphAdaptedH10ChartDataReduction4D

/-!
# Automatic H10 transversality for the graph-adapted minimal chart

Admissibility of the bounded H10 boundary projection at the origin already
forces the background throat metric to have no tangential radical.  Thus the
graph-adapted family constructs chart data without a separate transversality
hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphAdaptedH10TransversalityReduction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000
noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphAdaptedChartDataReduction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphAdaptedH10ChartDataReduction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

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

/-- Membership of the H10 boundary projection at zero forces the background
throat metric to have no tangential radical. -/
theorem globalCandidateAMinimalPhysicalGraphAdaptedH10_hasNoTangentialRadical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    (family : ProgramPGlobalMinimalPhysicalGraphAdaptedH10LocalActionData4D
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale) :
    HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric := by
  letI := globalMinimalPhysicalCanonicalGraphNormedAddCommGroup period hPeriod
    configuration data analysis
  letI := globalMinimalPhysicalCanonicalGraphNormedSpace period hPeriod
    configuration data analysis
  have hZero :
      (0 : CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric × Real) ∈
        candidateANormalBoundaryGHYDomain period hPeriod
          data.plusGravity.metric := by
    simpa using
      (family.boundaryProjection_mem
        (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
          configuration.physical)
        family.zero_mem_domain)
  have hGraph :
      NormalGraphNonNullAt period hPeriod data.plusGravity.metric.metric
        (0 : SmoothNormalDisplacement period hPeriod) 0 := by
    refine normalGraphNonNullAt_of_candidate_GHY_mem period hPeriod
      data.plusGravity.metric
      (0 : SmoothSymmetricCovariantTwoTensor period hPeriod)
      data.plusGravity.metric.metric ?_ 0 0 ?_
    · simp
    · change
        ((smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric)
          (0 : SmoothSymmetricCovariantTwoTensor period hPeriod ×
            SmoothNormalDisplacement period hPeriod), 0) ∈
          candidateANormalBoundaryGHYDomain period hPeriod
            data.plusGravity.metric
      rw [map_zero]
      exact hZero
  apply
    (throatTrace_nondegenerate_iff_no_tangential_radical period hPeriod
      data.plusGravity.metric.metric).1
  intro point
  change Function.Injective
    (generalLorentzMetricThroatTraceValue period hPeriod
      data.plusGravity.metric.metric point)
  simpa only [normalGraphInducedMetricValue_zero] using hGraph point

/-- Canonical graph-adapted H10 chart data with transversality inferred from
the supplied local family. -/
def globalCandidateAMinimalPhysicalGraphAdaptedH10ChartData_of_family
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (family : ProgramPGlobalMinimalPhysicalGraphAdaptedH10LocalActionData4D
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale) :
    ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis :=
  globalCandidateAMinimalPhysicalGraphAdaptedH10ChartData period hPeriod
    configuration data analysis einsteinScale
      (globalCandidateAMinimalPhysicalGraphAdaptedH10_hasNoTangentialRadical
        period hPeriod family) family

/-- Gate 321: the graph-adapted H10 local family constructs chart data without
an independently supplied transversality hypothesis. -/
theorem global_candidateA_minimal_physical_graph_adapted_h10_transversality_reduction_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (family : ProgramPGlobalMinimalPhysicalGraphAdaptedH10LocalActionData4D
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale) :
    Nonempty (ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :=
  global_candidateA_minimal_physical_graph_adapted_h10_chartData_reduction_gate
    period hPeriod configuration data analysis einsteinScale
      (globalCandidateAMinimalPhysicalGraphAdaptedH10_hasNoTangentialRadical
        period hPeriod family) family

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphAdaptedH10TransversalityReduction4D
end JanusFormal
