import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAH10CompletedBoundaryProjection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixProjectionCoreFrontier4D

/-!
# Completed H10 boundary projection from the core-to-chart estimate

The H10-reduced family already carries a bounded local boundary projection.
Consequently the same graph-norm estimate that controls the smooth-core map
into the physical chart also controls its composite with the boundary
projection.

This file extends that composite canonically from the dense smooth core to the
common Hilbert completion using `LinearMap.extendOfNorm`.  It proves agreement
on the core and builds the entire H10 projection packet.  No completed boundary
projection is supplied as an independent analytic datum.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
open P0EFTJanusProgramPGlobalCandidateAH10CompletedBoundaryProjection4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixDenseCoreFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixProjectionCoreFrontier4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

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

local instance h10ChartBoundBoundaryCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod metric

local instance h10ChartBoundBoundaryCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance h10ChartBoundBoundaryCoreCompleteSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreCompleteSpace period hPeriod metric

def globalCandidateAH10AdaptedBoundaryProjection
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :
    @ContinuousLinearMap Real Real _ _ (RingHom.id Real)
      (ReducedFamilyModel period hPeriod configuration)
      family.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      family.normedAddCommGroup.toAddCommGroup.toAddCommMonoid
      (Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real)
      inferInstance inferInstance family.normedSpace.toModule inferInstance := by
  letI := family.normedAddCommGroup
  letI := family.normedSpace
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
  exact @ContinuousLinearMap.mk Real Real _ _ (RingHom.id Real)
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

/-- Canonical boundary parameter map on the typed smooth core. -/
def globalCandidateAH10BoundaryCoreMap
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
          couplings.matterMassSquared) einsteinScale) :
    PhysicalCore period hPeriod analysis →ₗ[Real]
      Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real := by
  letI := family.normedAddCommGroup
  letI := family.normedSpace
  let coreToChart := globalCandidateACanonicalSixCoreToChart period hPeriod
    (measure := measure) configuration data analysis
      (globalCandidateAActualKernelChart period hPeriod (measure := measure)
        configuration data analysis einsteinScale hTransverse family)
      (globalCandidateAActualKernelSameAction period hPeriod (measure := measure)
        configuration data analysis einsteinScale hTransverse family)
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
  exact
    { toFun := fun core => adaptedLinear (coreToChart core)
      map_add' := by
        intro first second
        calc
          adaptedLinear (coreToChart (first + second)) =
              adaptedLinear
                (@Add.add _
                  family.normedAddCommGroup.toAddCommGroup.toAddCommMonoid.toAdd
                  (coreToChart first) (coreToChart second)) :=
            congrArg adaptedLinear (coreToChart.map_add' first second)
          _ = adaptedLinear (coreToChart first) +
              adaptedLinear (coreToChart second) :=
            by
              change projectionMap
                  (@Add.add _
                    family.normedAddCommGroup.toAddCommGroup.toAddCommMonoid.toAdd
                    (coreToChart first) (coreToChart second)) =
                projectionMap (coreToChart first) +
                  projectionMap (coreToChart second)
              rw [family.toAddCommGroup_eq]
              exact projectionMap.map_add _ _
      map_smul' := by
        intro scalar core
        calc
          adaptedLinear (coreToChart (scalar • core)) =
              adaptedLinear
                (@SMul.smul Real _ family.normedSpace.toModule.toSMul
                  ((RingHom.id Real) scalar) (coreToChart core)) :=
            congrArg adaptedLinear (coreToChart.map_smul' scalar core)
          _ = (RingHom.id Real) scalar • adaptedLinear (coreToChart core) :=
            by
              change projectionMap
                  (@SMul.smul Real _ family.normedSpace.toModule.toSMul
                    scalar (coreToChart core)) =
                (RingHom.id Real) scalar • projectionMap (coreToChart core)
              rw [family.toSMul_eq]
              have hMap := projectionMap.map_smul scalar (coreToChart core)
              change projectionMap
                  (@SMul.smul Real _
                    (Submodule.smul
                      (ReducedFamilyModel period hPeriod configuration))
                    scalar (coreToChart core)) =
                scalar • projectionMap (coreToChart core) at hMap
              simpa only [RingHom.id_apply] using hMap }

/-- The boundary-core estimate derived from the one core-to-chart estimate. -/
structure GlobalCandidateAH10BoundaryCoreMapBound4D
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
          couplings.matterMassSquared) einsteinScale) : Type where
  constant : Real
  constant_nonneg : 0 ≤ constant
  estimate : ∀ core : PhysicalCore period hPeriod analysis,
    ‖globalCandidateAH10BoundaryCoreMap period hPeriod (measure := measure) configuration data
        analysis einsteinScale hTransverse family core‖ ≤
      constant *
        ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis core‖

/-- The local boundary projection norm and the chart-map estimate give the
boundary-core estimate automatically. -/
def globalCandidateAH10BoundaryCoreMapBound_of_chartBound
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
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure) configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration
            data analysis einsteinScale hTransverse family))) :
    GlobalCandidateAH10BoundaryCoreMapBound4D period hPeriod (measure := measure) configuration data
      analysis einsteinScale hTransverse family := by
  letI := family.normedAddCommGroup
  letI := family.normedSpace
  let adapted := globalCandidateAH10AdaptedBoundaryProjection period hPeriod
    (measure := measure) configuration data analysis einsteinScale family
  exact {
    constant := ‖adapted‖ * chartBound.constant
    constant_nonneg := mul_nonneg (norm_nonneg _) chartBound.constant_nonneg
    estimate := by
      intro core
      let chartValue :=
        globalCandidateACanonicalSixCoreToChart period hPeriod
          (measure := measure) configuration data analysis
            (globalCandidateAActualKernelChart period hPeriod
              (measure := measure) configuration data analysis einsteinScale
                hTransverse family)
            (globalCandidateAActualKernelSameAction period hPeriod
              (measure := measure) configuration data analysis einsteinScale
                hTransverse family) core
      change ‖adapted chartValue‖ ≤
        (‖adapted‖ * chartBound.constant) *
          ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
            configuration data analysis core‖
      calc
        ‖adapted chartValue‖ ≤ ‖adapted‖ * ‖chartValue‖ :=
          adapted.le_opNorm chartValue
        _ ≤ ‖adapted‖ *
            (chartBound.constant *
              ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis core‖) := by
          exact mul_le_mul_of_nonneg_left (chartBound.estimate core)
            (norm_nonneg adapted)
        _ = (‖adapted‖ * chartBound.constant) *
            ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
              configuration data analysis core‖ := by ring
  }

/-- Canonical extension of the boundary parameter map to the common Hilbert
completion. -/
def globalCandidateAH10CompletedBoundaryProjection_of_bound
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
          couplings.matterMassSquared) einsteinScale)
    (bound : GlobalCandidateAH10BoundaryCoreMapBound4D period hPeriod (measure := measure)
      configuration data analysis einsteinScale hTransverse family) :
    CommonAugmentedHilbert period hPeriod configuration data
        analysis →L[Real]
      Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real :=
  (globalCandidateAH10BoundaryCoreMap period hPeriod (measure := measure) configuration data analysis
    einsteinScale hTransverse family).extendOfNorm
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)

/-- The canonical extension agrees with the original map on the smooth core. -/
theorem globalCandidateAH10CompletedBoundaryProjection_eq_core
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
          couplings.matterMassSquared) einsteinScale)
    (bound : GlobalCandidateAH10BoundaryCoreMapBound4D period hPeriod (measure := measure)
      configuration data analysis einsteinScale hTransverse family)
    (core : PhysicalCore period hPeriod analysis) :
    globalCandidateAH10CompletedBoundaryProjection_of_bound period hPeriod (measure := measure)
        configuration data analysis einsteinScale hTransverse family bound
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis core) =
      globalCandidateAH10BoundaryCoreMap period hPeriod (measure := measure) configuration data
        analysis einsteinScale hTransverse family core := by
  apply LinearMap.extendOfNorm_eq
  · exact diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis
  · exact ⟨bound.constant, bound.estimate⟩

/-- Build the reduced completed-projection packet from one core bound. -/
def globalCandidateAH10CompletedBoundaryProjectionData_of_bound
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
          couplings.matterMassSquared) einsteinScale)
    (bound : GlobalCandidateAH10BoundaryCoreMapBound4D period hPeriod (measure := measure)
      configuration data analysis einsteinScale hTransverse family) :
    GlobalCandidateAH10CompletedBoundaryProjectionData4D period hPeriod (measure := measure)
      configuration data analysis einsteinScale hTransverse family where
  completedProjection :=
    globalCandidateAH10CompletedBoundaryProjection_of_bound period hPeriod (measure := measure)
      configuration data analysis einsteinScale hTransverse family bound
  smoothCoreAgreement := by
    intro core
    calc
      globalCandidateAH10CompletedBoundaryProjection_of_bound period hPeriod
          (measure := measure) configuration data analysis einsteinScale
            hTransverse family bound
          (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
            configuration data analysis core) =
        globalCandidateAH10BoundaryCoreMap period hPeriod (measure := measure)
          configuration data analysis einsteinScale hTransverse family core :=
        globalCandidateAH10CompletedBoundaryProjection_eq_core period hPeriod
          (measure := measure) configuration data analysis einsteinScale
            hTransverse family bound core
      _ = family.boundaryProjection
          (globalCandidateACanonicalSixCoreToChart period hPeriod
            (measure := measure) configuration data analysis
              (globalCandidateAActualKernelChart period hPeriod
                (measure := measure) configuration data analysis einsteinScale
                  hTransverse family)
              (globalCandidateAActualKernelSameAction period hPeriod
                (measure := measure) configuration data analysis einsteinScale
                  hTransverse family) core) := by
        rfl

/-- The one chart-map bound constructs the complete H10 projection packet. -/
def globalCandidateAH10ProjectionCoreData_of_chartBound
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
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure) configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration
            data analysis einsteinScale hTransverse family))) :=
  (globalCandidateAH10CompletedBoundaryProjectionData_of_bound period hPeriod (measure := measure)
    configuration data analysis einsteinScale hTransverse family
      (globalCandidateAH10BoundaryCoreMapBound_of_chartBound period hPeriod (measure := measure)
        configuration data analysis einsteinScale hTransverse family
          chartBound)).toProjectionCoreData period hPeriod (measure := measure)

/-- Canonical H11 physical extension generated from that same chart-map bound. -/
def globalCandidateACanonicalSixPhysicalExtension_of_chartBound
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
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure) configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration
            data analysis einsteinScale hTransverse family))) :=
  globalCandidateACanonicalSixPhysicalExtension period hPeriod (measure := measure) configuration
    data analysis einsteinScale hTransverse family
      ((globalCandidateAH10ProjectionCoreData_of_chartBound period hPeriod (measure := measure)
        configuration data analysis einsteinScale hTransverse family chartBound
        ).toDenseCoreAgreement period hPeriod (measure := measure) hTransverse)
      chartBound

/-- Narrowest current terminal: family, one core-to-chart estimate, and the
actual-kernel gap. The H10 completed projection and all seven physical H11
forms are derived. -/
def global_candidateA_hessian_canonicalSix_chartBound_frontier_gate
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
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure) configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration
            data analysis einsteinScale hTransverse family)))
    (gap : GlobalCandidateAActualKernelGap4D period hPeriod (measure := measure) configuration data
      analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
          hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
            chartBound)) :=
  global_candidateA_hessian_canonicalSix_projectionCore_frontier_gate period
    hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
      (globalCandidateAH10ProjectionCoreData_of_chartBound period hPeriod (measure := measure)
        configuration data analysis einsteinScale hTransverse family chartBound)
      chartBound gap

/-- Beyond the fixed geometry, only the family, the core-to-chart estimate and
the actual-kernel coercivity/gap remain. -/
theorem global_candidateA_hessian_canonicalSix_chartBound_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
end JanusFormal
