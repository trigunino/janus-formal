import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D

/-!
# H11 from H10 Robin and one aggregate non-Robin extension

After H10, the Robin block is already a continuous symmetric bilinear form: it
is the genuine second Fréchet derivative of the completed two-sheet GHY
action, pulled back by the physical boundary projection.

The six remaining physical blocks need not be prolonged separately.  Their
sum is the only combination entering the augmented Hessian.  This file accepts
one continuous symmetric extension of that sum, with exact dense-core
agreement, and adds it to the canonical H10 Robin form.

Thus H11 is reduced to one non-Robin extension rather than six unrelated
forms or seven numerical bounds.  The resulting form is still tied exactly to
the true seven-block local Hessian on the existing smooth core.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateExtension4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

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

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

private abbrev PhysicalCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev CommonHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  CommonAugmentedHilbert period hPeriod configuration data analysis

local instance aggregateBoundaryCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod metric

local instance aggregateBoundaryCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance aggregateBoundaryCoreCompleteSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreCompleteSpace period hPeriod metric

/-- H11 data after aggregating the six non-Robin physical blocks.  Both core
forms are exact forms on the true diagonal core; the reconstruction field says
their sum is precisely the H13 seven-block Hessian. -/
structure GlobalCandidateASixPhysicalAggregateContinuousExtension4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (einsteinScale : Real) where
  robinProjection : CommonHilbert period hPeriod configuration data analysis →L[Real]
    Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod
        data.plusGravity.metric) Real
  robinCoreForm : PhysicalCore period hPeriod analysis →ₗ[Real]
    PhysicalCore period hPeriod analysis →ₗ[Real] Real
  robin_core_agreement : ∀ first second : PhysicalCore period hPeriod analysis,
    robinCoreForm first second =
      globalCandidateAH10RobinCommonDomainForm period hPeriod configuration data
        analysis einsteinScale robinProjection
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis first)
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis second)
  nonRobinForm : CommonHilbert period hPeriod configuration data analysis →L[Real]
    CommonHilbert period hPeriod configuration data analysis →L[Real] Real
  nonRobinCoreForm : PhysicalCore period hPeriod analysis →ₗ[Real]
    PhysicalCore period hPeriod analysis →ₗ[Real] Real
  nonRobin_core_agreement : ∀ first second : PhysicalCore period hPeriod analysis,
    nonRobinCoreForm first second =
      nonRobinForm
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis first)
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis second)
  nonRobin_symmetric : ∀ first second,
    nonRobinForm first second = nonRobinForm second first
  reconstruct : ∀ first second : PhysicalCore period hPeriod analysis,
    globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration data
        analysis chart sameAction first second =
      robinCoreForm first second + nonRobinCoreForm first second

/-- Sum of the canonical H10 Robin Hessian and the single aggregate non-Robin
extension. -/
def globalCandidateASevenPhysicalCommonDomainExtension_of_sixAggregate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (extension : GlobalCandidateASixPhysicalAggregateContinuousExtension4D
      period hPeriod configuration data analysis chart sameAction einsteinScale) :
    GlobalCandidateASevenPhysicalCommonDomainExtension4D period hPeriod
      configuration data analysis chart sameAction where
  form :=
    globalCandidateAH10RobinCommonDomainForm period hPeriod configuration data
        analysis einsteinScale extension.robinProjection +
      extension.nonRobinForm
  symmetric := by
    intro first second
    simp only [ContinuousLinearMap.add_apply]
    rw [globalCandidateAH10RobinCommonDomainForm_symmetric period hPeriod
        configuration data analysis einsteinScale hTransverse
        extension.robinProjection first second,
      extension.nonRobin_symmetric first second]
  smooth_agreement := by
    intro first second
    simp only [ContinuousLinearMap.add_apply]
    change
      globalCandidateAH10RobinCommonDomainForm period hPeriod configuration data
          analysis einsteinScale extension.robinProjection
          (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
            configuration data analysis first)
          (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
            configuration data analysis second) +
        extension.nonRobinForm
          (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
            configuration data analysis first)
          (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
            configuration data analysis second) = _
    rw [← extension.robin_core_agreement first second,
      ← extension.nonRobin_core_agreement first second,
      ← extension.reconstruct first second]
    rfl

/-- H11 from one non-Robin continuous extension plus the already closed H10
Robin Hessian. -/
theorem global_candidateA_h11_common_domain_gate_of_sixAggregate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (extension : GlobalCandidateASixPhysicalAggregateContinuousExtension4D
      period hPeriod configuration data analysis chart sameAction einsteinScale) :
    GlobalCandidateACommonAugmentedAnalyticDomainCertificate4D period hPeriod
      configuration data analysis chart sameAction
        (globalCandidateASevenPhysicalCommonDomainExtension_of_sixAggregate period
          hPeriod configuration data analysis chart sameAction einsteinScale
            hTransverse extension) :=
  global_candidateA_h11_common_augmented_domain_gate period hPeriod
    configuration data analysis chart sameAction
      (globalCandidateASevenPhysicalCommonDomainExtension_of_sixAggregate period
        hPeriod configuration data analysis chart sameAction einsteinScale
          hTransverse extension)

end
end P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateExtension4D
end JanusFormal
