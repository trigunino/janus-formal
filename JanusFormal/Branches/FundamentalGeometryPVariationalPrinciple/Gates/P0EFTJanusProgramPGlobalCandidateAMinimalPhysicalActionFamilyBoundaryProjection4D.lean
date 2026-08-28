import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10RobinReduction4D

/-!
# Concrete H10 Robin family from the boundary projection

The generic H10-Robin family packet accepts an arbitrary same-action germ.
For the actual Candidate-A chart this germ is already determined by one bounded
linear map from the minimal physical tangent to the completed metric-normal H10
parameter space.

This file converts the more concrete boundary-projection packet to the generic
H10-Robin packet.  The open germ is the chart domain itself, the completed
Robin action is the genuine two-sheet H10 action pulled back by the projection,
and the equality with the local Robin block is the stored exact action
identity.  Robin `C²` regularity is derived from the H10 domain theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyBoundaryProjection4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000

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
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10RobinReduction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionGermCalculus4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
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

private abbrev BoundaryProjectionModel
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical

/-- H10 regularity after pullback by the actual bounded metric-normal chart
projection. -/
private theorem boundaryProjectedRobin_contDiffWithinAt
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
      period hPeriod (measure := measure) configuration data analysis realization
        einsteinScale)
    (point : BoundaryProjectionModel period hPeriod configuration)
    (hPoint : point ∈ family.domain) :
    letI : NormedAddCommGroup
        (BoundaryProjectionModel period hPeriod configuration) :=
      family.normedAddCommGroup
    letI : NormedSpace Real
        (BoundaryProjectionModel period hPeriod configuration) :=
      family.normedSpace
    ContDiffWithinAt Real 2
      (fun state =>
        candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
          einsteinScale data.plusGravity.metric
            (family.boundaryProjection state))
      family.domain point := by
  letI : NormedAddCommGroup
      (BoundaryProjectionModel period hPeriod configuration) :=
    family.normedAddCommGroup
  letI : NormedSpace Real
      (BoundaryProjectionModel period hPeriod configuration) :=
    family.normedSpace
  let localFamily : GlobalCandidateALocalActionFamily period hPeriod
      (BoundaryProjectionModel period hPeriod configuration) couplings
      NonNullFace NullFace :=
    { domain := family.domain
      datumAt := family.datumAt }
  let blocks := globalCandidateAActionBlocks period hPeriod
    (localFamily.toActionFamily period hPeriod 0 family.zero_mem_domain) measure
  let physical := family.toPhysicalC2 period hPeriod hTransverse
  letI := physical.normedAddCommGroup
  letI := physical.normedSpace
  have hRobin : ContDiffWithinAt Real 2 blocks.robin family.domain point :=
    (physical.physicalBlocksC2Within point hPoint).robin
  rw [show (fun state =>
      candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale data.plusGravity.metric (family.boundaryProjection state)) =
      blocks.robin by
    simpa [localFamily, blocks] using family.robinAction_eq.symm]
  exact hRobin

/-- The concrete boundary-projection packet determines the generic H10 Robin
same-action family without an additional germ witness. -/
def ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D.toH10Robin
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod (measure := measure) configuration data analysis realization
        einsteinScale)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric) :
    ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D period hPeriod
      (measure := measure) configuration data analysis realization where
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
  nonRobinBlocksC2Within := by
    letI : NormedAddCommGroup
        (BoundaryProjectionModel period hPeriod configuration) :=
      family.normedAddCommGroup
    letI : NormedSpace Real
        (BoundaryProjectionModel period hPeriod configuration) :=
      family.normedSpace
    intro point hPoint
    have hSix := family.sixPhysicalBlocksC2Within point hPoint
    exact
      { candidateA := hSix.candidateA
        einsteinHilbertPlus := hSix.einsteinHilbertPlus
        einsteinHilbertMinus := hSix.einsteinHilbertMinus
        maxwellPlus := hSix.maxwellPlus
        maxwellMinus := hSix.maxwellMinus
        finiteBV := hSix.finiteBV }
  completedRobinAction := fun state =>
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
      einsteinScale data.plusGravity.metric (family.boundaryProjection state)
  completedRobin_contDiffWithin_two := by
    intro point hPoint
    exact boundaryProjectedRobin_contDiffWithinAt period hPeriod configuration
      data analysis realization einsteinScale hTransverse family point hPoint
  completedRobin_sameAction := by
    dsimp only
    intro state hState
    have hEquality := congrFun family.robinAction_eq state
    simpa using hEquality.symm
  matterConstant := family.matterConstant
  llConstant := family.llConstant
  matterAction_eq := family.matterAction_eq
  llAction_eq := family.llAction_eq

/-- H13 directly from the actual bounded boundary projection and the six
independent local regularity statements. -/
def global_candidateA_h13_minimalPhysical_boundaryProjection_gate
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
      period hPeriod (measure := measure) configuration data analysis realization
        einsteinScale) :=
  global_candidateA_h13_minimalPhysical_h10RobinFamily_gate period hPeriod
    (measure := measure) configuration data analysis realization
      (ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D.toH10Robin
        period hPeriod (measure := measure) family hTransverse)

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyBoundaryProjection4D
end JanusFormal
