import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D

/-!
# H10 completed boundary projection from the existing local family

The H10-reduced Candidate-A family already stores the genuine bounded local
boundary projection and the exact Robin action identity.  The minimal physical
chart uses that same tangent model and its chart analysis map is the identity.
Therefore these fields must not be supplied again by the terminal H11 packet.

This file retains only a bounded projection on the common Hilbert completion
and its agreement with the existing family projection on the typed smooth
core.  It reconstructs the action-level projection packet consumed by the
canonical-six frontier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAH10CompletedBoundaryProjection4D

set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option synthInstance.maxHeartbeats 3100000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D

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

private abbrev PhysicalCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

/-- Only the genuinely completed H10 projection remains. The local projection,
its value at the base point and the scalar Robin identity are all fields of the
existing H10-reduced family. -/
structure GlobalCandidateAH10CompletedBoundaryProjectionData4D
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) where
  completedProjection :
    GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
        analysis →L[Real]
      Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real
  smoothCoreAgreement : ∀ core : PhysicalCore period hPeriod analysis,
    completedProjection
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis core) =
      family.boundaryProjection
        (globalCandidateACanonicalSixCoreToChart period hPeriod configuration
          data analysis
            (globalCandidateAActualKernelChart period hPeriod configuration data
              analysis einsteinScale hTransverse family)
            (globalCandidateAActualKernelSameAction period hPeriod configuration
              data analysis einsteinScale hTransverse family)
            core)

/-- Reconstruct the previous action-level H10 projection packet. -/
def GlobalCandidateAH10CompletedBoundaryProjectionData4D.toProjectionCoreData
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    (projection : GlobalCandidateAH10CompletedBoundaryProjectionData4D period
      hPeriod configuration data analysis einsteinScale hTransverse family) :
    GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod configuration
      data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        einsteinScale where
  localProjection := family.boundaryProjection
  completedProjection := projection.completedProjection
  localProjection_base_zero := by
    simpa using family.boundaryProjection.map_zero
  robinAction_eq := by
    simpa [globalCandidateACanonicalSixLocalBlocks] using family.robinAction_eq
  smoothCoreProjectionAgreement := projection.smoothCoreAgreement

/-- Public adapter checkpoint. -/
theorem global_candidateA_h10_completed_boundary_projection_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    (projection : GlobalCandidateAH10CompletedBoundaryProjectionData4D period
      hPeriod configuration data analysis einsteinScale hTransverse family) :
    GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod configuration
      data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        einsteinScale :=
  projection.toProjectionCoreData period hPeriod

end
end P0EFTJanusProgramPGlobalCandidateAH10CompletedBoundaryProjection4D
end JanusFormal
