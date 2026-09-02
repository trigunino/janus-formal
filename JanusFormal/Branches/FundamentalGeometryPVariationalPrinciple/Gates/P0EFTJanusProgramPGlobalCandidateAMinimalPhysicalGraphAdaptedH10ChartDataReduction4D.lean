import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphAdaptedChartDataReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D

/-!
# Graph-adapted H10 reduction of minimal physical chart data

The canonical SpinC realization, norm and graph bounds remove the remaining
analytic carrier choices from the H10-reduced local-family packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphAdaptedH10ChartDataReduction4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphAdaptedChartDataReduction4D
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

/-- Exact remaining H10 local-family data after fixing the canonical graph
realization, norm and projection bounds. -/
structure ProgramPGlobalMinimalPhysicalGraphAdaptedH10LocalActionData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real) where
  domain : Set (Model period hPeriod configuration)
  isOpen_domain :
    letI := globalMinimalPhysicalCanonicalGraphNormedAddCommGroup period hPeriod
      configuration data analysis
    letI := globalMinimalPhysicalCanonicalGraphNormedSpace period hPeriod
      configuration data analysis
    IsOpen domain
  zero_mem_domain : (0 : Model period hPeriod configuration) ∈ domain
  datumAt : ∀ point : Model period hPeriod configuration, point ∈ domain →
    GlobalCandidateALocalActionDatum period hPeriod couplings
      NonNullFace NullFace
  datumAt_zero_configuration :
    (datumAt 0 zero_mem_domain).1 = configuration.physical
  sixPhysicalBlocksC2Within :
    letI := globalMinimalPhysicalCanonicalGraphNormedAddCommGroup period hPeriod
      configuration data analysis
    letI := globalMinimalPhysicalCanonicalGraphNormedSpace period hPeriod
      configuration data analysis
    ∀ point (_hPoint : point ∈ domain),
      let family : GlobalCandidateALocalActionFamily period hPeriod
          (Model period hPeriod configuration) couplings NonNullFace NullFace :=
        { domain := domain, datumAt := datumAt }
      GlobalCandidateASixPhysicalC2WithinAt
        (globalCandidateAActionBlocks period hPeriod
          (family.toActionFamily period hPeriod 0 zero_mem_domain) measure)
        domain point
  boundaryProjection :
    letI := globalMinimalPhysicalCanonicalGraphNormedAddCommGroup period hPeriod
      configuration data analysis
    letI := globalMinimalPhysicalCanonicalGraphNormedSpace period hPeriod
      configuration data analysis
    Model period hPeriod configuration →L[Real]
      Prod (CandidateANormalBoundaryFunctionalCore period hPeriod
        data.plusGravity.metric) Real
  boundaryProjection_mem : ∀ point, point ∈ domain →
    boundaryProjection point ∈
      candidateANormalBoundaryGHYDomain period hPeriod data.plusGravity.metric
  robinAction_eq :
    letI := globalMinimalPhysicalCanonicalGraphNormedAddCommGroup period hPeriod
      configuration data analysis
    letI := globalMinimalPhysicalCanonicalGraphNormedSpace period hPeriod
      configuration data analysis
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
    letI := globalMinimalPhysicalCanonicalGraphNormedAddCommGroup period hPeriod
      configuration data analysis
    letI := globalMinimalPhysicalCanonicalGraphNormedSpace period hPeriod
      configuration data analysis
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (Model period hPeriod configuration) couplings NonNullFace NullFace :=
      { domain := domain, datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).matter =
      fun state => matterConstant +
        programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared
          (globalMinimalPhysicalMatterGraphCLM period hPeriod configuration data
            analysis (globalMinimalPhysicalCanonicalMatterGraphRealization
              period hPeriod)
              (globalMinimalPhysicalCanonicalGraphBounds period hPeriod
                configuration data analysis) state)
  llAction_eq :
    letI := globalMinimalPhysicalCanonicalGraphNormedAddCommGroup period hPeriod
      configuration data analysis
    letI := globalMinimalPhysicalCanonicalGraphNormedSpace period hPeriod
      configuration data analysis
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (Model period hPeriod configuration) couplings NonNullFace NullFace :=
      { domain := domain, datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).ll =
      fun state => llConstant +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          (globalMinimalPhysicalLLGraphCLM period hPeriod configuration data
            analysis (globalMinimalPhysicalCanonicalMatterGraphRealization
              period hPeriod)
              (globalMinimalPhysicalCanonicalGraphBounds period hPeriod
                configuration data analysis) state)

/-- Restore the existing H10-reduced packet using only canonical choices. -/
def ProgramPGlobalMinimalPhysicalGraphAdaptedH10LocalActionData4D.toH10Reduced
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
    ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D period
      hPeriod (measure := measure) configuration data analysis
        (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
        einsteinScale where
  normedAddCommGroup := globalMinimalPhysicalCanonicalGraphNormedAddCommGroup
    period hPeriod configuration data analysis
  normedSpace := globalMinimalPhysicalCanonicalGraphNormedSpace period hPeriod
    configuration data analysis
  toAddCommGroup_eq := rfl
  toSMul_eq := rfl
  bounds := globalMinimalPhysicalCanonicalGraphBounds period hPeriod
    configuration data analysis
  domain := family.domain
  isOpen_domain := family.isOpen_domain
  zero_mem_domain := family.zero_mem_domain
  datumAt := family.datumAt
  datumAt_zero_configuration := family.datumAt_zero_configuration
  sixPhysicalBlocksC2Within := family.sixPhysicalBlocksC2Within
  boundaryProjection := family.boundaryProjection
  boundaryProjection_mem := family.boundaryProjection_mem
  robinAction_eq := family.robinAction_eq
  matterConstant := family.matterConstant
  llConstant := family.llConstant
  matterAction_eq := family.matterAction_eq
  llAction_eq := family.llAction_eq

/-- Construct chart data once the H10 transverse hypothesis is supplied. -/
def globalCandidateAMinimalPhysicalGraphAdaptedH10ChartData
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalGraphAdaptedH10LocalActionData4D
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale) :
    ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis :=
  globalCandidateAMinimalPhysicalActionChartData_of_reducedFamily period
    hPeriod configuration data analysis
      (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
      (((family.toH10Reduced period hPeriod).toPhysicalC2 period hPeriod
        hTransverse).toReduced period hPeriod)

/-- Gate 319: canonical graph choices reduce H10 chart construction to the
remaining local geometric family and transversality. -/
theorem global_candidateA_minimal_physical_graph_adapted_h10_chartData_reduction_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalGraphAdaptedH10LocalActionData4D
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale) :
    Nonempty (ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :=
  ⟨globalCandidateAMinimalPhysicalGraphAdaptedH10ChartData period hPeriod
    configuration data analysis einsteinScale hTransverse family⟩

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphAdaptedH10ChartDataReduction4D
end JanusFormal
