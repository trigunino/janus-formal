import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLGraphAdaptedNorm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyPhysicalC2Reduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCDiracGreenClosure4D

/-!
# Graph-adapted reduction of the minimal physical chart-data frontier

The primitive SpinC graph realization is unconditional, and the graph-adapted
norm supplies the compatible norm and both matter/LL bounds.  This file inserts
those constructions into the existing physical-`C²` local-family route.

The remaining input is exactly geometric: an actual local `datumAt` family,
`C²` regularity of its seven physical blocks, and the two exact same-action
identities.  Such input constructs the genuine minimal physical `chartData`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphAdaptedChartDataReduction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyPhysicalC2Reduction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLGraphAdaptedNorm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCDiracGreenClosure4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private abbrev GraphAdaptedModel
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical

/-- The unconditional primitive SpinC graph realization selected by the
geometric Green identity. -/
def globalMinimalPhysicalCanonicalMatterGraphRealization
    {couplings : GlobalCandidateAActionCouplings} :
    ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D period hPeriod
      couplings.matterMassSquared :=
  programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen period
    hPeriod couplings.matterMassSquared

/-- Canonical specialization of the graph-adapted additive norm. -/
@[reducible] def globalMinimalPhysicalCanonicalGraphNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup (GraphAdaptedModel period hPeriod configuration) :=
  globalMinimalPhysicalMatterLLGraphNormedAddCommGroup period hPeriod
    configuration data analysis
      (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)

/-- Canonical specialization of the graph-adapted real normed-space
structure. -/
@[reducible] def globalMinimalPhysicalCanonicalGraphNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    letI : NormedAddCommGroup
        (GraphAdaptedModel period hPeriod configuration) :=
      globalMinimalPhysicalCanonicalGraphNormedAddCommGroup period hPeriod
        configuration data analysis
    NormedSpace Real (GraphAdaptedModel period hPeriod configuration) :=
  globalMinimalPhysicalMatterLLGraphNormedSpace period hPeriod configuration
    data analysis
      (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)

/-- Both canonical graph projections have bound one in the selected norm. -/
def globalMinimalPhysicalCanonicalGraphBounds
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    letI : NormedAddCommGroup
        (GraphAdaptedModel period hPeriod configuration) :=
      globalMinimalPhysicalCanonicalGraphNormedAddCommGroup period hPeriod
        configuration data analysis
    letI : NormedSpace Real
        (GraphAdaptedModel period hPeriod configuration) :=
      globalMinimalPhysicalCanonicalGraphNormedSpace period hPeriod
        configuration data analysis
    GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod configuration data
      analysis
        (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod) :=
  globalMinimalPhysicalMatterLLGraphAdaptedBounds period hPeriod configuration
    data analysis
      (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)

/-- Exact remaining local geometric input after inserting the unconditional
SpinC realization and the graph-adapted norm. -/
structure ProgramPGlobalMinimalPhysicalGraphAdaptedLocalActionData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) where
  domain : Set (GraphAdaptedModel period hPeriod configuration)
  isOpen_domain :
    letI : NormedAddCommGroup
        (GraphAdaptedModel period hPeriod configuration) :=
      globalMinimalPhysicalCanonicalGraphNormedAddCommGroup period hPeriod
        configuration data analysis
    IsOpen domain
  zero_mem_domain :
    (0 : GraphAdaptedModel period hPeriod configuration) ∈ domain
  datumAt : ∀ point : GraphAdaptedModel period hPeriod configuration,
    point ∈ domain →
      GlobalCandidateALocalActionDatum period hPeriod couplings
        NonNullFace NullFace
  datumAt_zero_configuration :
    (datumAt 0 zero_mem_domain).1 = configuration.physical
  physicalBlocksC2Within :
    letI : NormedAddCommGroup
        (GraphAdaptedModel period hPeriod configuration) :=
      globalMinimalPhysicalCanonicalGraphNormedAddCommGroup period hPeriod
        configuration data analysis
    letI : NormedSpace Real
        (GraphAdaptedModel period hPeriod configuration) :=
      globalMinimalPhysicalCanonicalGraphNormedSpace period hPeriod
        configuration data analysis
    ∀ point (hPoint : point ∈ domain),
      let family : GlobalCandidateALocalActionFamily period hPeriod
          (GraphAdaptedModel period hPeriod configuration) couplings
          NonNullFace NullFace :=
        { domain := domain
          datumAt := datumAt }
      GlobalCandidateASevenPhysicalC2WithinAt
        (globalCandidateAActionBlocks period hPeriod
          (family.toActionFamily period hPeriod 0 zero_mem_domain) measure)
        domain point
  matterConstant : Real
  llConstant : Real
  matterAction_eq :
    letI : NormedAddCommGroup
        (GraphAdaptedModel period hPeriod configuration) :=
      globalMinimalPhysicalCanonicalGraphNormedAddCommGroup period hPeriod
        configuration data analysis
    letI : NormedSpace Real
        (GraphAdaptedModel period hPeriod configuration) :=
      globalMinimalPhysicalCanonicalGraphNormedSpace period hPeriod
        configuration data analysis
    let realization :=
      globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod
    let bounds :=
      globalMinimalPhysicalCanonicalGraphBounds period hPeriod configuration
        data analysis
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (GraphAdaptedModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).matter =
      fun state => matterConstant +
        programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared
          (globalMinimalPhysicalMatterGraphCLM period hPeriod configuration data
            analysis realization bounds state)
  llAction_eq :
    letI : NormedAddCommGroup
        (GraphAdaptedModel period hPeriod configuration) :=
      globalMinimalPhysicalCanonicalGraphNormedAddCommGroup period hPeriod
        configuration data analysis
    letI : NormedSpace Real
        (GraphAdaptedModel period hPeriod configuration) :=
      globalMinimalPhysicalCanonicalGraphNormedSpace period hPeriod
        configuration data analysis
    let realization :=
      globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod
    let bounds :=
      globalMinimalPhysicalCanonicalGraphBounds period hPeriod configuration
        data analysis
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (GraphAdaptedModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).ll =
      fun state => llConstant +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          (globalMinimalPhysicalLLGraphCLM period hPeriod configuration data
            analysis realization bounds state)

/-- Insert the unconditional analytic choices into the existing physical-`C²`
family packet. -/
def ProgramPGlobalMinimalPhysicalGraphAdaptedLocalActionData4D.toPhysicalC2
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (family : ProgramPGlobalMinimalPhysicalGraphAdaptedLocalActionData4D
      period hPeriod (measure := measure) configuration data analysis) :
    ProgramPGlobalMinimalPhysicalLocalActionFamilyPhysicalC2Data4D period
      hPeriod (measure := measure) configuration data analysis
        (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod) where
  normedAddCommGroup :=
    globalMinimalPhysicalCanonicalGraphNormedAddCommGroup period hPeriod
      configuration data analysis
  normedSpace :=
    globalMinimalPhysicalCanonicalGraphNormedSpace period hPeriod configuration
      data analysis
  toAddCommGroup_eq := rfl
  toSMul_eq := rfl
  bounds := globalMinimalPhysicalCanonicalGraphBounds period hPeriod
    configuration data analysis
  domain := family.domain
  isOpen_domain := family.isOpen_domain
  zero_mem_domain := family.zero_mem_domain
  datumAt := family.datumAt
  datumAt_zero_configuration := family.datumAt_zero_configuration
  physicalBlocksC2Within := family.physicalBlocksC2Within
  matterConstant := family.matterConstant
  llConstant := family.llConstant
  matterAction_eq := family.matterAction_eq
  llAction_eq := family.llAction_eq

/-- The exact remaining geometric input constructs a genuine minimal physical
chart-data object. -/
def globalCandidateAMinimalPhysicalGraphAdaptedChartData
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (family : ProgramPGlobalMinimalPhysicalGraphAdaptedLocalActionData4D
      period hPeriod (measure := measure) configuration data analysis) :
    ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis :=
  globalCandidateAMinimalPhysicalActionChartData_of_reducedFamily period
    hPeriod configuration data analysis
      (globalMinimalPhysicalCanonicalMatterGraphRealization period hPeriod)
      ((family.toPhysicalC2 period hPeriod).toReduced period hPeriod)

/-- Gate marker: norms, graph bounds and SpinC realization are no longer
inputs to chart-data construction. -/
theorem global_candidateA_minimal_physical_graph_adapted_chartData_reduction_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (family : ProgramPGlobalMinimalPhysicalGraphAdaptedLocalActionData4D
      period hPeriod (measure := measure) configuration data analysis) :
    Nonempty
      (ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
        (measure := measure) configuration data analysis) :=
  ⟨globalCandidateAMinimalPhysicalGraphAdaptedChartData period hPeriod
    configuration data analysis family⟩

end

end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphAdaptedChartDataReduction4D
end JanusFormal
