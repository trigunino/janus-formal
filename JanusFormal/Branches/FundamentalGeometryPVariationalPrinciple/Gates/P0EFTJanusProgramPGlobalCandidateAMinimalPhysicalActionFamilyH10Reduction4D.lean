import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryH10Closure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyPhysicalC2Reduction4D

/-!
# Consume H10 inside the minimal physical Candidate-A family

After the terminal mobile-boundary closure, Robin/GHY regularity must not
remain a seventh independent `C²` hypothesis in H13.  This file attaches the
actual minimal physical chart to the completed metric-normal parameter by one
bounded linear projection.  Exact equality of the local Robin block with the
completed two-sheet GHY pullback and preservation of the genuine GHY domain
then derive its `C²` regularity from H10.

The reduced local-family input therefore keeps only six independent physical
regularity statements: interaction, the two Einstein--Hilbert blocks, the two
Maxwell blocks, and finite/null-BV.  Matter and LL are supplied by their closed
quadratic graph actions; Robin is supplied by H10.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

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
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyPhysicalC2Reduction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryH10Closure4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
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

private abbrev ReducedFamilyModel
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical

/-- Exactly the physical blocks still requiring independent local regularity
after matter, LL and Robin have been assigned to their canonical analytic
realisations. -/
structure GlobalCandidateASixPhysicalC2WithinAt
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (blocks : FullCoupledActionBlocks Model)
    (domain : Set Model) (point : Model) : Prop where
  candidateA : ContDiffWithinAt Real 2 blocks.candidateA domain point
  einsteinHilbertPlus :
    ContDiffWithinAt Real 2 blocks.einsteinHilbertPlus domain point
  einsteinHilbertMinus :
    ContDiffWithinAt Real 2 blocks.einsteinHilbertMinus domain point
  maxwellPlus : ContDiffWithinAt Real 2 blocks.maxwellPlus domain point
  maxwellMinus : ContDiffWithinAt Real 2 blocks.maxwellMinus domain point
  finiteBV : ContDiffWithinAt Real 2 blocks.finiteBV domain point

/-- Minimal local-family packet after consuming H10.  `boundaryProjection`
contains no second boundary field: it is the chart coordinate of the existing
metric and normal variations in the completed H10 core. -/
structure ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (einsteinScale : Real) where
  normedAddCommGroup : NormedAddCommGroup
    (ReducedFamilyModel period hPeriod configuration)
  normedSpace : NormedSpace Real
    (ReducedFamilyModel period hPeriod configuration)
  bounds : @GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod
    couplings NonNullFace NullFace _ _ configuration data analysis realization
      normedAddCommGroup normedSpace
  domain : Set (ReducedFamilyModel period hPeriod configuration)
  isOpen_domain : IsOpen domain
  zero_mem_domain : (0 : ReducedFamilyModel period hPeriod configuration) ∈
    domain
  datumAt : ∀ point : ReducedFamilyModel period hPeriod configuration,
    point ∈ domain →
      GlobalCandidateALocalActionDatum period hPeriod couplings
        NonNullFace NullFace
  datumAt_zero_configuration :
    (datumAt 0 zero_mem_domain).1 = configuration.physical
  sixPhysicalBlocksC2Within : ∀ point (hPoint : point ∈ domain),
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (ReducedFamilyModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    GlobalCandidateASixPhysicalC2WithinAt
      (globalCandidateAActionBlocks period hPeriod
        (family.toActionFamily period hPeriod 0 zero_mem_domain) measure)
      domain point
  boundaryProjection :
    ReducedFamilyModel period hPeriod configuration →L[Real]
      Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real
  boundaryProjection_mem : ∀ point, point ∈ domain →
    boundaryProjection point ∈
      candidateANormalBoundaryGHYDomain period hPeriod data.plusGravity.metric
  robinAction_eq :
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (ReducedFamilyModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).robin =
      fun state =>
        candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
          einsteinScale data.plusGravity.metric (boundaryProjection state)
  matterConstant : Real
  llConstant : Real
  matterAction_eq :
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (ReducedFamilyModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).matter =
      fun state => matterConstant +
        programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared
          (@globalMinimalPhysicalMatterGraphCLM period hPeriod couplings
            NonNullFace NullFace _ _ configuration data analysis realization
            normedAddCommGroup normedSpace bounds state)
  llAction_eq :
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (ReducedFamilyModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).ll =
      fun state => llConstant +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          (@globalMinimalPhysicalLLGraphCLM period hPeriod couplings
            NonNullFace NullFace _ _ configuration data analysis realization
            normedAddCommGroup normedSpace bounds state)

/-- H10 supplies `C²` regularity of the Robin block after pullback by the
bounded chart projection. -/
private theorem h10RobinPullback_contDiffWithinAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis realization einsteinScale)
    (point : ReducedFamilyModel period hPeriod configuration) :
    ContDiffWithinAt Real 2
      (fun state =>
        candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
          einsteinScale data.plusGravity.metric
            (family.boundaryProjection state))
      family.domain point := by
  have hOn : ContDiffOn Real 2
      (fun state =>
        candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
          einsteinScale data.plusGravity.metric
            (family.boundaryProjection state))
      family.domain :=
    (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffOn_two
      period hPeriod einsteinScale data.plusGravity.metric hTransverse).comp
      family.boundaryProjection.contDiff.contDiffOn
      family.boundaryProjection_mem
  exact hOn.contDiffWithinAt

/-- Reconstruct the seven-physical-block packet.  Robin is discharged by H10;
no independent Robin regularity field is retained. -/
def ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D.toPhysicalC2
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared}
    {einsteinScale : Real}
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis realization einsteinScale) :
    ProgramPGlobalMinimalPhysicalLocalActionFamilyPhysicalC2Data4D period
      hPeriod configuration data analysis realization where
  normedAddCommGroup := family.normedAddCommGroup
  normedSpace := family.normedSpace
  bounds := family.bounds
  domain := family.domain
  isOpen_domain := family.isOpen_domain
  zero_mem_domain := family.zero_mem_domain
  datumAt := family.datumAt
  datumAt_zero_configuration := family.datumAt_zero_configuration
  physicalBlocksC2Within := by
    intro point hPoint
    let localFamily : GlobalCandidateALocalActionFamily period hPeriod
        (ReducedFamilyModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := family.domain
        datumAt := family.datumAt }
    let blocks := globalCandidateAActionBlocks period hPeriod
      (localFamily.toActionFamily period hPeriod 0 family.zero_mem_domain)
      measure
    have hSix : GlobalCandidateASixPhysicalC2WithinAt blocks family.domain
        point := by
      simpa [localFamily, blocks] using
        family.sixPhysicalBlocksC2Within point hPoint
    have hRobin : ContDiffWithinAt Real 2 blocks.robin family.domain point := by
      rw [show blocks.robin = fun state =>
          candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period
            hPeriod einsteinScale data.plusGravity.metric
              (family.boundaryProjection state) by
        simpa [localFamily, blocks] using family.robinAction_eq]
      exact h10RobinPullback_contDiffWithinAt period hPeriod configuration data
        analysis realization einsteinScale hTransverse family point
    exact
      { candidateA := hSix.candidateA
        robin := hRobin
        einsteinHilbertPlus := hSix.einsteinHilbertPlus
        einsteinHilbertMinus := hSix.einsteinHilbertMinus
        maxwellPlus := hSix.maxwellPlus
        maxwellMinus := hSix.maxwellMinus
        finiteBV := hSix.finiteBV }
  matterConstant := family.matterConstant
  llConstant := family.llConstant
  matterAction_eq := family.matterAction_eq
  llAction_eq := family.llAction_eq

/-- H13 from six local physical regularity statements, the H10 pullback and
the two already closed graph actions. -/
theorem global_candidateA_h13_minimalPhysical_h10ReducedFamily_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis realization einsteinScale) :=
  global_candidateA_h13_minimalPhysical_physicalC2Family_gate period hPeriod
    configuration data analysis realization
      (family.toPhysicalC2 period hPeriod hTransverse)

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
end JanusFormal
