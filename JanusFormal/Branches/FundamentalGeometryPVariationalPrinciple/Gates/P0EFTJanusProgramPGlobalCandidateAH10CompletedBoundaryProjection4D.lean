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
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChartConstructor4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyPhysicalC2Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianH10ContinuousClosure4D
open P0EFTJanusProgramPGlobalHessianMaximalDomainBoundedClosure4D

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
      period hPeriod (measure := measure) configuration data analysis
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
        (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure) configuration
          data analysis
            (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
              analysis einsteinScale hTransverse family)
            (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration
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
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    (projection : GlobalCandidateAH10CompletedBoundaryProjectionData4D period
      hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family) :
    GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod (measure := measure) configuration
      data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        einsteinScale := by
  let chart := globalCandidateAActualKernelChart period hPeriod
    (measure := measure) configuration data analysis einsteinScale hTransverse
      family
  letI := family.normedAddCommGroup
  letI := family.normedSpace
  have hZero :
      family.normedAddCommGroup.toAddCommGroup.toZero =
        (Submodule.addCommGroup
          (ReducedFamilyModel period hPeriod configuration)).toZero :=
    congrArg
      (fun group : AddCommGroup
          (ReducedFamilyModel period hPeriod configuration) => group.toZero)
      family.toAddCommGroup_eq
  let projectionMap := family.boundaryProjection
  let adaptedLinear :
      @LinearMap Real Real _ _ (RingHom.id Real)
        (ReducedFamilyModel period hPeriod configuration)
        (Prod
          (CandidateANormalBoundaryFunctionalCore period hPeriod
            data.plusGravity.metric) Real)
        family.normedAddCommGroup.toAddCommGroup.toAddCommMonoid inferInstance
        family.normedSpace.toModule inferInstance :=
    @LinearMap.mk Real Real _ _ (RingHom.id Real)
      (ReducedFamilyModel period hPeriod configuration)
      (Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real)
      family.normedAddCommGroup.toAddCommGroup.toAddCommMonoid inferInstance
      family.normedSpace.toModule inferInstance
      (@AddHom.mk
        (ReducedFamilyModel period hPeriod configuration)
        (Prod
          (CandidateANormalBoundaryFunctionalCore period hPeriod
            data.plusGravity.metric) Real)
        family.normedAddCommGroup.toAddCommGroup.toAddCommMonoid.toAdd
        inferInstance
        (fun direction => projectionMap direction)
        (by
          intro first second
          change projectionMap
              (@Add.add _
                family.normedAddCommGroup.toAddCommGroup.toAddCommMonoid.toAdd
                first second) =
            projectionMap first + projectionMap second
          rw [family.toAddCommGroup_eq]
          exact projectionMap.map_add first second))
      (by
        intro scalar direction
        change projectionMap
            (@SMul.smul Real _ family.normedSpace.toModule.toSMul scalar
              direction) =
          (RingHom.id Real) scalar • projectionMap direction
        rw [family.toSMul_eq]
        have hMap := projectionMap.map_smul scalar direction
        change projectionMap
            (@SMul.smul Real _
              (Submodule.smul
                (ReducedFamilyModel period hPeriod configuration))
              scalar direction) =
          scalar • projectionMap direction at hMap
        simpa only [RingHom.id_apply] using hMap)
  let adapted :
      @ContinuousLinearMap Real Real _ _ (RingHom.id Real)
        (ReducedFamilyModel period hPeriod configuration)
        family.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        family.normedAddCommGroup.toAddCommGroup.toAddCommMonoid
        (Prod
          (CandidateANormalBoundaryFunctionalCore period hPeriod
            data.plusGravity.metric) Real)
        inferInstance inferInstance family.normedSpace.toModule inferInstance :=
    @ContinuousLinearMap.mk Real Real _ _ (RingHom.id Real)
      (ReducedFamilyModel period hPeriod configuration)
      family.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      family.normedAddCommGroup.toAddCommGroup.toAddCommMonoid
      (Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real)
      inferInstance inferInstance family.normedSpace.toModule inferInstance
      adaptedLinear
      (by
        change Continuous (fun direction => projectionMap direction)
        exact projectionMap.cont)
  let localFamily : GlobalCandidateALocalActionFamily period hPeriod
      (ReducedFamilyModel period hPeriod configuration) couplings NonNullFace
        NullFace :=
    { domain := family.domain
      datumAt := family.datumAt }
  let localBlocks := globalCandidateAActionBlocks period hPeriod
    (localFamily.toActionFamily period hPeriod
      (0 : ReducedFamilyModel period hPeriod configuration)
      family.zero_mem_domain) measure
  have hBlocks :
      globalCandidateACanonicalSixLocalBlocks period hPeriod chart =
        localBlocks := by
    unfold globalCandidateACanonicalSixLocalBlocks
    congr 1
    simp only [chart, globalCandidateAActualKernelChart,
      globalCandidateAH10ContinuousChart,
      globalCandidateAH10ContinuousReducedFamily, diracGreenClosureChart,
      maximalDomainClosureChart, maximalDomainClosureChartData,
      globalCandidateAMinimalPhysicalActionChartData_of_reducedFamily,
      globalCandidateAMinimalPhysicalActionChartData_of_family,
      ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D.toFull,
      ProgramPGlobalMinimalPhysicalLocalActionFamilyPhysicalC2Data4D.toReduced,
      ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D.toPhysicalC2,
      globalCandidateAMinimalPhysicalLocalVariationalChart,
      globalCandidateAMinimalPhysicalLocalActionFamily, localFamily]
    congr
  have hRobinBlocks := congrArg (fun blocks => blocks.robin) hBlocks
  exact {
    localProjection := adapted
    completedProjection := projection.completedProjection
    localProjection_base_zero := by
      change projectionMap 0 = 0
      exact projectionMap.map_zero
    robinAction_eq :=
      calc
        (globalCandidateACanonicalSixLocalBlocks period hPeriod chart).robin =
            localBlocks.robin := by
          exact hRobinBlocks
        _ = fun state =>
            candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period
              hPeriod einsteinScale data.plusGravity.metric (adapted state) := by
          simpa [localBlocks, localFamily, adapted, adaptedLinear,
            projectionMap] using family.robinAction_eq
    smoothCoreProjectionAgreement := projection.smoothCoreAgreement
  }

/-- Public adapter checkpoint. -/
def global_candidateA_h10_completed_boundary_projection_gate
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
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    (projection : GlobalCandidateAH10CompletedBoundaryProjectionData4D period
      hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family) :
    GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod (measure := measure) configuration
      data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        einsteinScale :=
  projection.toProjectionCoreData period hPeriod (measure := measure)

end
end P0EFTJanusProgramPGlobalCandidateAH10CompletedBoundaryProjection4D
end JanusFormal
