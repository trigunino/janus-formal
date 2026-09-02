import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLExtraGraphAdaptedNorm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphAdaptedH10TransversalityReduction4D

/-! # H10 chart data from an algebraic boundary projection -/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalAlgebraicBoundaryH10ChartDataReduction4D

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
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphAdaptedChartDataReduction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLExtraGraphAdaptedNorm4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryH10Closure4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

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

private abbrev Model
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical

private abbrev BoundaryTarget
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace) :=
  CandidateANormalBoundaryFunctionalCore period hPeriod
    data.plusGravity.metric × Real

private local instance boundaryCoreNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace) :
    NormedAddCommGroup (CandidateANormalBoundaryFunctionalCore period hPeriod
      data.plusGravity.metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod
    data.plusGravity.metric

private local instance boundaryCoreNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace) :
    NormedSpace Real (CandidateANormalBoundaryFunctionalCore period hPeriod
      data.plusGravity.metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod
    data.plusGravity.metric

/-- Remaining local data when the boundary projection is merely algebraic. -/
structure ProgramPGlobalMinimalPhysicalAlgebraicBoundaryH10LocalActionData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real) where
  boundaryProjection : Model period hPeriod configuration →ₗ[Real]
    BoundaryTarget period hPeriod configuration data
  domain : Set (Model period hPeriod configuration)
  isOpen_domain :
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
      hPeriod configuration data analysis
        (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
        boundaryProjection
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
      configuration data analysis
        (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
        boundaryProjection
    IsOpen domain
  zero_mem_domain : (0 : Model period hPeriod configuration) ∈ domain
  datumAt : ∀ point : Model period hPeriod configuration, point ∈ domain →
    GlobalCandidateALocalActionDatum period hPeriod couplings NonNullFace NullFace
  datumAt_zero_configuration :
    (datumAt 0 zero_mem_domain).1 = configuration.physical
  sixPhysicalBlocksC2Within :
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
      hPeriod configuration data analysis
        (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
        boundaryProjection
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
      configuration data analysis
        (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
        boundaryProjection
    ∀ point (_hPoint : point ∈ domain),
      let family : GlobalCandidateALocalActionFamily period hPeriod
          (Model period hPeriod configuration) couplings NonNullFace NullFace :=
        { domain := domain, datumAt := datumAt }
      GlobalCandidateASixPhysicalC2WithinAt
        (globalCandidateAActionBlocks period hPeriod
          (family.toActionFamily period hPeriod 0 zero_mem_domain) measure)
        domain point
  boundaryProjection_mem : ∀ point, point ∈ domain →
    boundaryProjection point ∈
      candidateANormalBoundaryGHYDomain period hPeriod data.plusGravity.metric
  robinAction_eq :
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
      hPeriod configuration data analysis
        (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
        boundaryProjection
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
      configuration data analysis
        (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
        boundaryProjection
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (Model period hPeriod configuration) couplings NonNullFace NullFace :=
      { domain := domain, datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).robin =
      fun state => candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation
        period hPeriod einsteinScale data.plusGravity.metric
          (boundaryProjection state)
  matterConstant : Real
  llConstant : Real
  matterAction_eq :
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
      hPeriod configuration data analysis
        (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
        boundaryProjection
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
      configuration data analysis
        (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
        boundaryProjection
    let realization := globalMinimalPhysicalCanonicalMatterGraphRealization
      period hPeriod
    let bounds := globalMinimalPhysicalMatterLLExtraGraphAdaptedBounds period
      hPeriod configuration data analysis realization boundaryProjection
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (Model period hPeriod configuration) couplings NonNullFace NullFace :=
      { domain := domain, datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).matter =
      fun state => matterConstant +
        programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared
          (globalMinimalPhysicalMatterGraphCLM period hPeriod configuration data
            analysis realization bounds state)
  llAction_eq :
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
      hPeriod configuration data analysis
        (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
        boundaryProjection
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
      configuration data analysis
        (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
        boundaryProjection
    let realization := globalMinimalPhysicalCanonicalMatterGraphRealization
      period hPeriod
    let bounds := globalMinimalPhysicalMatterLLExtraGraphAdaptedBounds period
      hPeriod configuration data analysis realization boundaryProjection
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (Model period hPeriod configuration) couplings NonNullFace NullFace :=
      { domain := domain, datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).ll =
      fun state => llConstant +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          (globalMinimalPhysicalLLGraphCLM period hPeriod configuration data
            analysis realization bounds state)

/-- Insert the extra-graph norm and turn the algebraic boundary map into a CLM. -/
def ProgramPGlobalMinimalPhysicalAlgebraicBoundaryH10LocalActionData4D.toH10Reduced
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    (family : ProgramPGlobalMinimalPhysicalAlgebraicBoundaryH10LocalActionData4D
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale) :
    ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D period
      hPeriod (measure := measure) configuration data analysis
        (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
        einsteinScale where
  normedAddCommGroup :=
    globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period hPeriod
      configuration data analysis
        (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
        family.boundaryProjection
  normedSpace := globalMinimalPhysicalMatterLLExtraGraphNormedSpace period
    hPeriod configuration data analysis
      (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
      family.boundaryProjection
  toAddCommGroup_eq := rfl
  toSMul_eq := rfl
  bounds := globalMinimalPhysicalMatterLLExtraGraphAdaptedBounds period hPeriod
    configuration data analysis
      (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
      family.boundaryProjection
  domain := family.domain
  isOpen_domain := family.isOpen_domain
  zero_mem_domain := family.zero_mem_domain
  datumAt := family.datumAt
  datumAt_zero_configuration := family.datumAt_zero_configuration
  sixPhysicalBlocksC2Within := family.sixPhysicalBlocksC2Within
  boundaryProjection := globalMinimalPhysicalMatterLLExtraGraphExtraCLM period
    hPeriod configuration data analysis
      (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
      family.boundaryProjection
  boundaryProjection_mem := family.boundaryProjection_mem
  robinAction_eq := family.robinAction_eq
  matterConstant := family.matterConstant
  llConstant := family.llConstant
  matterAction_eq := family.matterAction_eq
  llAction_eq := family.llAction_eq

private theorem hasNoTangentialRadical_of_h10Reduced
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D period
      hPeriod couplings.matterMassSquared}
    {einsteinScale : Real}
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod (measure := measure) configuration data analysis realization
        einsteinScale) :
    HasNoTangentialRadical period hPeriod data.plusGravity.metric.metric := by
  letI := family.normedAddCommGroup
  letI := family.normedSpace
  have hZero : (0 : BoundaryTarget period hPeriod configuration data) ∈
      candidateANormalBoundaryGHYDomain period hPeriod
        data.plusGravity.metric := by
    simpa using family.boundaryProjection_mem 0 family.zero_mem_domain
  have hGraph : NormalGraphNonNullAt period hPeriod
      data.plusGravity.metric.metric (0 : SmoothNormalDisplacement period hPeriod)
        0 := by
    refine normalGraphNonNullAt_of_candidate_GHY_mem period hPeriod
      data.plusGravity.metric
      (0 : SmoothSymmetricCovariantTwoTensor period hPeriod)
      data.plusGravity.metric.metric (by simp) 0 0 ?_
    change ((smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
      data.plusGravity.metric)
        (0 : SmoothSymmetricCovariantTwoTensor period hPeriod ×
          SmoothNormalDisplacement period hPeriod), 0) ∈
      candidateANormalBoundaryGHYDomain period hPeriod data.plusGravity.metric
    rw [map_zero]
    exact hZero
  apply (throatTrace_nondegenerate_iff_no_tangential_radical period hPeriod
    data.plusGravity.metric.metric).1
  intro point
  change Function.Injective (generalLorentzMetricThroatTraceValue period hPeriod
    data.plusGravity.metric.metric point)
  simpa only [normalGraphInducedMetricValue_zero] using hGraph point

/-- Chart data with continuity and transversality inferred from the packet. -/
def globalCandidateAMinimalPhysicalAlgebraicBoundaryH10ChartData
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (family : ProgramPGlobalMinimalPhysicalAlgebraicBoundaryH10LocalActionData4D
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale) :
    ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis := by
  let reduced := family.toH10Reduced period hPeriod
  exact globalCandidateAMinimalPhysicalActionChartData_of_reducedFamily period
    hPeriod configuration data analysis
      (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
      ((reduced.toPhysicalC2 period hPeriod
        (hasNoTangentialRadical_of_h10Reduced period hPeriod reduced)).toReduced
          period hPeriod)

/-- Gate 322: an algebraic H10 boundary projection suffices. -/
theorem global_candidateA_minimal_physical_algebraic_boundary_h10_chartData_reduction_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (family : ProgramPGlobalMinimalPhysicalAlgebraicBoundaryH10LocalActionData4D
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale) :
    Nonempty (ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :=
  ⟨globalCandidateAMinimalPhysicalAlgebraicBoundaryH10ChartData period hPeriod
    configuration data analysis einsteinScale family⟩

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalAlgebraicBoundaryH10ChartDataReduction4D
end JanusFormal
