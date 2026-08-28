import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryRobinC2Transfer4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyPhysicalC2Reduction4D

/-!
# Candidate-A local family with the Robin block supplied by H10

The seven-physical-block family still accepted an independent `C²` proof for
its Robin component.  After H10 this is redundant: the completed normal-boundary
action is already `C²` and agrees with the historical/mobile Robin action on a
common open domain.

This module removes that duplicate input.  The local-family packet now stores
only the six non-Robin physical regularity statements.  The seventh statement
is reconstructed from the H10 same-action transfer before invoking the existing
H13 constructor.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10RobinReduction4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000

noncomputable section

open Filter Set Topology MeasureTheory
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
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChartConstructor4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyPhysicalC2Reduction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryRobinC2Transfer4D
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

/-- The six physical summands whose `C²` regularity is not supplied by H10. -/
structure GlobalCandidateASixNonRobinPhysicalC2WithinAt
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

/-- Local Candidate-A family data in which the Robin block is represented by
the completed H10 action and its same-action comparison. -/
structure ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared) where
  [normedAddCommGroup : NormedAddCommGroup
    (ReducedFamilyModel period hPeriod configuration)]
  [normedSpace : NormedSpace Real
    (ReducedFamilyModel period hPeriod configuration)]
  toAddCommGroup_eq : normedAddCommGroup.toAddCommGroup =
    Submodule.addCommGroup (ReducedFamilyModel period hPeriod configuration)
  toSMul_eq : normedSpace.toModule.toSMul =
    Submodule.smul (ReducedFamilyModel period hPeriod configuration)
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
  nonRobinBlocksC2Within : ∀ point (hPoint : point ∈ domain),
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (ReducedFamilyModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    GlobalCandidateASixNonRobinPhysicalC2WithinAt
      (globalCandidateAActionBlocks period hPeriod
        (family.toActionFamily period hPeriod 0 zero_mem_domain) measure)
      domain point
  completedRobinAction :
    ReducedFamilyModel period hPeriod configuration → Real
  completedRobin_contDiffWithin_two :
    ContDiffOn Real 2 completedRobinAction domain
  completedRobin_sameAction :
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (ReducedFamilyModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    let blocks := globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure
    Set.EqOn completedRobinAction blocks.robin domain
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

/-- Reconstruct the seven-block packet by transferring `C²` from the completed
H10 action to the actual Robin action. -/
def ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D.toPhysicalC2
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D
      period hPeriod (measure := measure) configuration data analysis realization) :
    ProgramPGlobalMinimalPhysicalLocalActionFamilyPhysicalC2Data4D
      period hPeriod (measure := measure) configuration data analysis realization where
  normedAddCommGroup := family.normedAddCommGroup
  normedSpace := family.normedSpace
  toAddCommGroup_eq := family.toAddCommGroup_eq
  toSMul_eq := family.toSMul_eq
  bounds := family.bounds
  domain := family.domain
  isOpen_domain := family.isOpen_domain
  zero_mem_domain := family.zero_mem_domain
  datumAt := family.datumAt
  datumAt_zero_configuration := family.datumAt_zero_configuration
  physicalBlocksC2Within := by
    letI : NormedAddCommGroup
        (ReducedFamilyModel period hPeriod configuration) :=
      family.normedAddCommGroup
    letI : NormedSpace Real
        (ReducedFamilyModel period hPeriod configuration) :=
      family.normedSpace
    intro point hPoint
    let localFamily : GlobalCandidateALocalActionFamily period hPeriod
        (ReducedFamilyModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := family.domain
        datumAt := family.datumAt }
    let blocks := globalCandidateAActionBlocks period hPeriod
      (localFamily.toActionFamily period hPeriod 0 family.zero_mem_domain)
      measure
    have hSix :
        GlobalCandidateASixNonRobinPhysicalC2WithinAt blocks family.domain
          point := by
      simpa [localFamily, blocks] using
        family.nonRobinBlocksC2Within point hPoint
    have hSameAction : Set.EqOn family.completedRobinAction blocks.robin
        family.domain := by
      simpa [localFamily, blocks] using family.completedRobin_sameAction
    let transfer : NormalBoundaryRobinC2TransferData
        family.completedRobinAction blocks.robin :=
      { domain := family.domain
        isOpen_domain := family.isOpen_domain
        completed_contDiffWithin_two :=
          family.completedRobin_contDiffWithin_two
        sameAction := hSameAction }
    have hRobin :
        ContDiffWithinAt Real 2 blocks.robin family.domain point :=
      transfer.historical_contDiffWithinAt_two hPoint
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

/-- Reconstruct the original reduced H13 packet. -/
def ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D.toReduced
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D
      period hPeriod (measure := measure) configuration data analysis realization) :
    ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D
      period hPeriod (measure := measure) configuration data analysis realization :=
  (family.toPhysicalC2 period hPeriod (measure := measure)).toReduced
    period hPeriod

/-- H13 from six local `C²` proofs plus the H10 same-action Robin transfer. -/
def global_candidateA_h13_minimalPhysical_h10RobinFamily_gate
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D
      period hPeriod (measure := measure) configuration data analysis realization) :=
  global_candidateA_h13_minimalPhysical_reducedFamily_gate period hPeriod
    configuration data analysis realization
      (family.toReduced period hPeriod (measure := measure))

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10RobinReduction4D
end JanusFormal
