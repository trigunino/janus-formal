import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10RobinReduction4D

/-!
# Adapters into the H10-supplied local-family packet

Existing chartwise Candidate-A modules often already expose the older
nine-block `FullCoupledC2WithinAt` certificate.  This module extracts the six
non-Robin physical fields and permits those families to use the new H10 Robin
route without duplicating any chart or action data.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10RobinAdapters4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10RobinReduction4D

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

/-- Forget the matter, Robin and LL fields of the older nine-block regularity
certificate. -/
def GlobalCandidateASixNonRobinPhysicalC2WithinAt.ofFullCoupled
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    {blocks : FullCoupledActionBlocks Model}
    {domain : Set Model} {point : Model}
    (full : FullCoupledC2WithinAt blocks domain point) :
    GlobalCandidateASixNonRobinPhysicalC2WithinAt blocks domain point where
  candidateA := full.candidateA
  einsteinHilbertPlus := full.einsteinHilbertPlus
  einsteinHilbertMinus := full.einsteinHilbertMinus
  maxwellPlus := full.maxwellPlus
  maxwellMinus := full.maxwellMinus
  finiteBV := full.finiteBV

/-- Convert an older reduced family to the H10-supplied packet once the
completed Robin action and its action-level equality are provided. -/
def programPGlobalMinimalPhysicalLocalActionFamilyH10Robin_of_reduced
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D
      period hPeriod configuration data analysis realization)
    (completedRobinAction :
      GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical →
        Real)
    (completedRobin_contDiffWithin_two :
      ContDiffWithin Real 2 completedRobinAction family.domain)
    (completedRobin_sameAction :
      let localFamily : GlobalCandidateALocalActionFamily period hPeriod
          (GlobalMinimalPhysicalFieldTangent period hPeriod
            configuration.physical)
          couplings NonNullFace NullFace :=
        { domain := family.domain
          datumAt := family.datumAt }
      let blocks := globalCandidateAActionBlocks period hPeriod
        (localFamily.toActionFamily period hPeriod 0 family.zero_mem_domain)
        measure
      Set.EqOn completedRobinAction blocks.robin family.domain) :
    ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D period hPeriod
      configuration data analysis realization where
  normedAddCommGroup := family.normedAddCommGroup
  normedSpace := family.normedSpace
  bounds := family.bounds
  domain := family.domain
  isOpen_domain := family.isOpen_domain
  zero_mem_domain := family.zero_mem_domain
  datumAt := family.datumAt
  datumAt_zero_configuration := family.datumAt_zero_configuration
  nonRobinBlocksC2Within := by
    intro point hPoint
    exact GlobalCandidateASixNonRobinPhysicalC2WithinAt.ofFullCoupled
      (family.blocksC2Within point hPoint)
  completedRobinAction := completedRobinAction
  completedRobin_contDiffWithin_two := completedRobin_contDiffWithin_two
  completedRobin_sameAction := completedRobin_sameAction
  matterConstant := family.matterConstant
  llConstant := family.llConstant
  matterAction_eq := family.matterAction_eq
  llAction_eq := family.llAction_eq

/-- The adapter round-trip preserves the original reduced family fields. -/
theorem programPGlobalMinimalPhysicalLocalActionFamilyH10Robin_of_reduced_toReduced
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D
      period hPeriod configuration data analysis realization)
    (completedRobinAction :
      GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical →
        Real)
    (completedRobin_contDiffWithin_two :
      ContDiffWithin Real 2 completedRobinAction family.domain)
    (completedRobin_sameAction :
      let localFamily : GlobalCandidateALocalActionFamily period hPeriod
          (GlobalMinimalPhysicalFieldTangent period hPeriod
            configuration.physical)
          couplings NonNullFace NullFace :=
        { domain := family.domain
          datumAt := family.datumAt }
      let blocks := globalCandidateAActionBlocks period hPeriod
        (localFamily.toActionFamily period hPeriod 0 family.zero_mem_domain)
        measure
      Set.EqOn completedRobinAction blocks.robin family.domain) :
    (programPGlobalMinimalPhysicalLocalActionFamilyH10Robin_of_reduced period
      hPeriod configuration data analysis realization family
      completedRobinAction completedRobin_contDiffWithin_two
      completedRobin_sameAction).toReduced period hPeriod = family := by
  cases family
  rfl

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10RobinAdapters4D
end JanusFormal
