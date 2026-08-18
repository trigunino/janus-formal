import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalCoreEmbedding4D

/-!
# H11 from six continuous physical extensions and the H10 Robin Hessian

The earlier H11 reductions asked either for one aggregate product estimate or
for seven separate estimates. Once H10 is closed, the Robin block has a
canonical continuous bilinear realization already: the genuine second
Fréchet derivative of the completed two-sheet GHY action. A bounded linear
projection from the common Hilbert space to the completed metric-normal chart
pulls that Hessian back to the unchanged D10-free common domain.

This file therefore leaves only six continuous extensions to construct:
Candidate-A interaction, Einstein--Hilbert on both sheets, Maxwell on both
sheets, and finite/null-BV. Exact dense-core agreement reconstructs the true
seven-block local Hessian, so no arbitrary bounded perturbation can be inserted.
No second Hilbert completion and no replacement boundary action is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
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

local instance h11BoundaryCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod metric

local instance h11BoundaryCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance h11BoundaryCoreCompleteSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreCompleteSpace period hPeriod metric

/-- The six physical blocks not already represented by the H10 Robin Hessian. -/
inductive GlobalCandidateANonRobinPhysicalBlock
  | candidateA
  | einsteinHilbertPlus
  | einsteinHilbertMinus
  | maxwellPlus
  | maxwellMinus
  | finiteBV
  deriving DecidableEq, Fintype

/-- Pullback of the genuine H10 second Fréchet derivative to the unchanged
common Hilbert space. -/
def globalCandidateAH10RobinCommonDomainForm
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (projection : CommonHilbert period hPeriod configuration data analysis →L[Real]
      Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real) :
    CommonHilbert period hPeriod configuration data analysis →L[Real]
      CommonHilbert period hPeriod configuration data analysis →L[Real] Real :=
  (candidateANormalBoundaryTwoSheetGHYActionHessian period hPeriod
    einsteinScale data.plusGravity.metric).bilinearComp projection projection

/-- Symmetry of the Robin extension is inherited from H10, not supplied as a
new field of the H11 packet. -/
theorem globalCandidateAH10RobinCommonDomainForm_symmetric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (projection : CommonHilbert period hPeriod configuration data analysis →L[Real]
      Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real)
    (first second : CommonHilbert period hPeriod configuration data analysis) :
    globalCandidateAH10RobinCommonDomainForm period hPeriod configuration data
        analysis einsteinScale projection first second =
      globalCandidateAH10RobinCommonDomainForm period hPeriod configuration data
        analysis einsteinScale projection second first := by
  exact candidateANormalBoundaryTwoSheetGHYActionHessian_symmetric period hPeriod
    einsteinScale data.plusGravity.metric hTransverse
      (projection first) (projection second)

/-- H11 input after consuming H10. Only six genuinely new continuous block
extensions remain. The `reconstruct` equality is on the actual dense core and
includes the H10 Robin form, so the sum is definitionally tied to the local
Candidate-A Hessian retained by H13. -/
structure GlobalCandidateASixPhysicalContinuousExtensions4D
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
  form : GlobalCandidateANonRobinPhysicalBlock →
    CommonHilbert period hPeriod configuration data analysis →L[Real]
      CommonHilbert period hPeriod configuration data analysis →L[Real] Real
  coreForm : GlobalCandidateANonRobinPhysicalBlock →
    PhysicalCore period hPeriod analysis →ₗ[Real]
      PhysicalCore period hPeriod analysis →ₗ[Real] Real
  core_agreement : ∀ block first second,
    coreForm block first second =
      form block
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis first)
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis second)
  symmetric : ∀ block first second,
    form block first second = form block second first
  reconstruct : ∀ first second : PhysicalCore period hPeriod analysis,
    globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration data
        analysis chart sameAction first second =
      robinCoreForm first second +
        ∑ block : GlobalCandidateANonRobinPhysicalBlock,
          coreForm block first second

/-- Sum the canonical H10 Robin form with the six supplied continuous physical
forms. -/
def globalCandidateASevenPhysicalCommonDomainExtension_of_sixContinuous
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
    (extensions : GlobalCandidateASixPhysicalContinuousExtensions4D period
      hPeriod configuration data analysis chart sameAction einsteinScale) :
    GlobalCandidateASevenPhysicalCommonDomainExtension4D period hPeriod
      configuration data analysis chart sameAction where
  form :=
    globalCandidateAH10RobinCommonDomainForm period hPeriod configuration data
        analysis einsteinScale extensions.robinProjection +
      ∑ block : GlobalCandidateANonRobinPhysicalBlock, extensions.form block
  symmetric := by
    intro first second
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply]
    rw [globalCandidateAH10RobinCommonDomainForm_symmetric period hPeriod
      configuration data analysis einsteinScale hTransverse
        extensions.robinProjection first second]
    congr 1
    apply Finset.sum_congr rfl
    intro block _
    exact extensions.symmetric block first second
  smooth_agreement := by
    intro first second
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply]
    change
      globalCandidateAH10RobinCommonDomainForm period hPeriod configuration data
          analysis einsteinScale extensions.robinProjection
          (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
            configuration data analysis first)
          (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
            configuration data analysis second) +
        (∑ block : GlobalCandidateANonRobinPhysicalBlock,
          extensions.form block
            (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
              configuration data analysis first)
            (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
              configuration data analysis second)) = _
    rw [← extensions.robin_core_agreement first second]
    have hSum :
        (∑ block : GlobalCandidateANonRobinPhysicalBlock,
          extensions.form block
            (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
              configuration data analysis first)
            (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
              configuration data analysis second)) =
        ∑ block : GlobalCandidateANonRobinPhysicalBlock,
          extensions.coreForm block first second := by
      apply Finset.sum_congr rfl
      intro block _
      exact (extensions.core_agreement block first second).symm
    rw [hSum, ← extensions.reconstruct first second]
    exact globalCandidateASevenPhysicalCoreLinearForm_apply period hPeriod
      configuration data analysis chart sameAction first second

/-- H11 on the unique common Hilbert space from six continuous extensions;
Robin is entirely supplied by H10. -/
theorem global_candidateA_h11_common_augmented_domain_gate_of_sixContinuous
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
    (extensions : GlobalCandidateASixPhysicalContinuousExtensions4D period
      hPeriod configuration data analysis chart sameAction einsteinScale) :
    GlobalCandidateACommonAugmentedAnalyticDomainCertificate4D period hPeriod
      configuration data analysis chart sameAction
        (globalCandidateASevenPhysicalCommonDomainExtension_of_sixContinuous
          period hPeriod configuration data analysis chart sameAction
            einsteinScale hTransverse extensions) :=
  global_candidateA_h11_common_augmented_domain_gate period hPeriod
    configuration data analysis chart sameAction
      (globalCandidateASevenPhysicalCommonDomainExtension_of_sixContinuous
        period hPeriod configuration data analysis chart sameAction
          einsteinScale hTransverse extensions)

end
end P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D
end JanusFormal
