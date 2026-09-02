import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalAlgebraicBoundaryH10ChartDataReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalNormalBoundaryAlgebraicProjection4D

/-!
# H10 chart data from the canonical sector normal-boundary projection

The algebraic boundary map is no longer supplied wholesale.  A Program-P
sector and a real linear parameter map determine it from the existing metric
and normal slots of the minimal physical tangent.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalNormalBoundaryH10ChartDataReduction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000
noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalAlgebraicBoundaryH10ChartDataReduction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalNormalBoundaryAlgebraicProjection4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
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

/-- Remaining local data after fixing the algebraic boundary map to the
metric-normal projection of one sector and an explicit real parameter map. -/
structure ProgramPGlobalMinimalPhysicalNormalBoundaryH10LocalActionData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real) where
  sector : Sector
  parameterMap : Model period hPeriod configuration →ₗ[Real] Real
  domain : Set (Model period hPeriod configuration)
  isOpen_domain :
    let boundaryProjection :=
      globalMinimalPhysicalNormalBoundaryProductLinearMap period hPeriod
        data.plusGravity.metric configuration.physical sector parameterMap
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
    let boundaryProjection :=
      globalMinimalPhysicalNormalBoundaryProductLinearMap period hPeriod
        data.plusGravity.metric configuration.physical sector parameterMap
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
    globalMinimalPhysicalNormalBoundaryProductLinearMap period hPeriod
        data.plusGravity.metric configuration.physical sector parameterMap point ∈
      candidateANormalBoundaryGHYDomain period hPeriod data.plusGravity.metric
  robinAction_eq :
    let boundaryProjection :=
      globalMinimalPhysicalNormalBoundaryProductLinearMap period hPeriod
        data.plusGravity.metric configuration.physical sector parameterMap
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
    let boundaryProjection :=
      globalMinimalPhysicalNormalBoundaryProductLinearMap period hPeriod
        data.plusGravity.metric configuration.physical sector parameterMap
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
    let boundaryProjection :=
      globalMinimalPhysicalNormalBoundaryProductLinearMap period hPeriod
        data.plusGravity.metric configuration.physical sector parameterMap
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

/-- Insert the canonical sector boundary map into the algebraic H10 packet. -/
def ProgramPGlobalMinimalPhysicalNormalBoundaryH10LocalActionData4D.toAlgebraicBoundaryH10
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    (family : ProgramPGlobalMinimalPhysicalNormalBoundaryH10LocalActionData4D
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale) :
    ProgramPGlobalMinimalPhysicalAlgebraicBoundaryH10LocalActionData4D period
      hPeriod (measure := measure) configuration data analysis einsteinScale where
  boundaryProjection :=
    globalMinimalPhysicalNormalBoundaryProductLinearMap period hPeriod
      data.plusGravity.metric configuration.physical family.sector
        family.parameterMap
  domain := family.domain
  isOpen_domain := family.isOpen_domain
  zero_mem_domain := family.zero_mem_domain
  datumAt := family.datumAt
  datumAt_zero_configuration := family.datumAt_zero_configuration
  sixPhysicalBlocksC2Within := family.sixPhysicalBlocksC2Within
  boundaryProjection_mem := family.boundaryProjection_mem
  robinAction_eq := family.robinAction_eq
  matterConstant := family.matterConstant
  llConstant := family.llConstant
  matterAction_eq := family.matterAction_eq
  llAction_eq := family.llAction_eq

/-- Chart data with the H10 boundary projection fixed by one sector and one
real linear parameter map. -/
def globalCandidateAMinimalPhysicalNormalBoundaryH10ChartData
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (family : ProgramPGlobalMinimalPhysicalNormalBoundaryH10LocalActionData4D
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale) :
    ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis :=
  globalCandidateAMinimalPhysicalAlgebraicBoundaryH10ChartData period hPeriod
    configuration data analysis einsteinScale
      (family.toAlgebraicBoundaryH10 period hPeriod)

/-- Gate 324: sector selection and a real parameter map determine the full
algebraic H10 boundary projection needed for minimal-physical chart data. -/
theorem global_candidateA_minimal_physical_normal_boundary_h10_chartData_reduction_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (family : ProgramPGlobalMinimalPhysicalNormalBoundaryH10LocalActionData4D
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale) :
    Nonempty (ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :=
  global_candidateA_minimal_physical_algebraic_boundary_h10_chartData_reduction_gate
    period hPeriod configuration data analysis einsteinScale
      (family.toAlgebraicBoundaryH10 period hPeriod)

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalNormalBoundaryH10ChartDataReduction4D
end JanusFormal
