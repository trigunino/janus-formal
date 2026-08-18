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
      period hPeriod configuration data analysis realization einsteinScale)
    (point : BoundaryProjectionModel period hPeriod configuration) :
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
      period hPeriod configuration data analysis realization einsteinScale)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric) :
    ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D period hPeriod
      configuration data analysis realization where
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
  sixPhysicalBlocksC2Within := family.sixPhysicalBlocksC2Within
  completedRobinAction := fun state =>
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
      einsteinScale data.plusGravity.metric (family.boundaryProjection state)
  completedRobinAction_contDiffWithin := by
    intro point
    exact boundaryProjectedRobin_contDiffWithinAt period hPeriod configuration
      data analysis realization einsteinScale hTransverse family point
  robinAction := by
    let localFamily : GlobalCandidateALocalActionFamily period hPeriod
        (BoundaryProjectionModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := family.domain
        datumAt := family.datumAt }
    exact (globalCandidateAActionBlocks period hPeriod
      (localFamily.toActionFamily period hPeriod 0 family.zero_mem_domain)
        measure).robin
  sameAction := by
    let localFamily : GlobalCandidateALocalActionFamily period hPeriod
        (BoundaryProjectionModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := family.domain
        datumAt := family.datumAt }
    refine
      { domain := family.domain
        isOpen_domain := family.isOpen_domain
        base_mem_domain := family.zero_mem_domain
        eqOn_domain := ?_ }
    intro state hState
    have hEquality := congrFun family.robinAction_eq state
    simpa [localFamily] using hEquality.symm
  matterConstant := family.matterConstant
  llConstant := family.llConstant
  matterAction_eq := family.matterAction_eq
  llAction_eq := family.llAction_eq

/-- H13 directly from the actual bounded boundary projection and the six
independent local regularity statements. -/
theorem global_candidateA_h13_minimalPhysical_boundaryProjection_gate
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
  global_candidateA_h13_minimalPhysical_h10RobinFamily_gate period hPeriod
    configuration data analysis realization
      (family.toH10Robin period hPeriod hTransverse)

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyBoundaryProjection4D
end JanusFormal
