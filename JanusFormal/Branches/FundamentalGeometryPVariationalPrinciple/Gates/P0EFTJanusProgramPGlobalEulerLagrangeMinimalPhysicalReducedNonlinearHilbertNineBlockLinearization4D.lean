import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertLinearization4D

/-!
# Exact nine-block form of the reduced nonlinear linearization

The local Hessian is decomposed into the six canonical physical Hessians,
the Robin Hessian, the primitive-matter Hessian and the full-LL Hessian.  The
same genuine nine-block operator is then pulled to the reduced Hilbert space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertNineBlockLinearization4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPCanonicalSixPhysicalChartHessian4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertLinearization4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period
      hPeriod configuration data analysis chartData)

/-- Sum of the nine genuine second Frechet derivatives selected by the local
action chart. -/
noncomputable def globalCandidateALocalNineBlockHessianSum
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model →L[Real]
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model →L[Real] Real :=
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  let blocks := globalCandidateACanonicalSixLocalBlocks period hPeriod chart
  (canonicalSixPhysicalHessianSum blocks point +
      fderiv Real (actionGradient blocks.robin) point) +
    (globalCandidateAH13LocalMatterHessian period hPeriod chart point +
      globalCandidateAH13LocalLLHessian period hPeriod chart point)

/-- The local Hessian is exactly the nine-block Hessian sum. -/
theorem globalCandidateALocalHessian_eq_nineBlockSum
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model)
    (hPoint : point ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).family.domain) :
    globalCandidateALocalHessian period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData) point =
      globalCandidateALocalNineBlockHessianSum period hPeriod configuration
        data analysis chartData point := by
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  let blocks := globalCandidateACanonicalSixLocalBlocks period hPeriod chart
  have hC2 : FullCoupledC2At blocks point :=
    fullCoupledC2WithinAt_toAt (chart.blocksC2Within point hPoint)
      chart.isOpen_domain hPoint
  have hPhysical :
      globalCandidateALocalPhysicalHessian period hPeriod chart point =
        canonicalSixPhysicalHessianSum blocks point +
          fderiv Real (actionGradient blocks.robin) point := by
    change fderiv Real (actionGradient (fullCoupledPhysicalAction blocks)) point = _
    exact fullCoupledPhysicalHessian_eq_six_add_robin blocks point hC2
  rw [globalCandidateALocalHessian_eq_physical_add_matterLL period hPeriod
    chart point hPoint, hPhysical,
    globalCandidateAH13LocalMatterLLHessian_split period hPeriod chart point
      hPoint]
  rfl

/-- The nine-block Hessian pulled through the reduced chart in both slots. -/
noncomputable def globalCandidateAMinimalPhysicalReducedNineBlockHessian
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
        data analysis →L[Real]
      GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
        data analysis →L[Real] Real :=
  ((ContinuousLinearMap.compL Real
      (GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis)
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model Real).flip
          (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
            hPeriod configuration data analysis chartData reducedChart)).comp
    ((globalCandidateALocalNineBlockHessianSum period hPeriod configuration data
      analysis chartData
      (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis chartData reducedChart state)).comp
      (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
        hPeriod configuration data analysis chartData reducedChart))

theorem globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian_eq_nineBlock
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain) :
    globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian period hPeriod
        configuration data analysis chartData reducedChart state =
      globalCandidateAMinimalPhysicalReducedNineBlockHessian period hPeriod
        configuration data analysis chartData reducedChart state := by
  unfold globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian
    globalCandidateAMinimalPhysicalReducedNineBlockHessian
  rw [globalCandidateALocalHessian_eq_nineBlockSum period hPeriod configuration
    data analysis chartData _ hState]

theorem globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization_pairing_eq_nineBlock
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain)
    (first second : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization
          period hPeriod configuration data analysis chartData reducedChart state
            first) second =
      globalCandidateAMinimalPhysicalReducedNineBlockHessian period hPeriod
        configuration data analysis chartData reducedChart state first second := by
  rw [globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization_pairing]
  rw [globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian_eq_nineBlock
    period hPeriod configuration data analysis chartData reducedChart state hState]

/-- On the raw smooth core at the base state, the strong linearization pairs as
the exact nine-block Hessian evaluated on the canonical chart directions. -/
theorem globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization_smooth_pairing_eq_nineBlock
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization
          period hPeriod configuration data analysis chartData reducedChart 0
          (globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period hPeriod
            configuration data analysis first))
        (globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period hPeriod
          configuration data analysis second) =
      globalCandidateALocalNineBlockHessianSum period hPeriod configuration data
        analysis chartData
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData).chartBridge.basePoint
        (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
          analysis
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData)
          (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
            configuration data analysis chartData) first)
        (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
          analysis
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData)
          (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
            configuration data analysis chartData) second) := by
  rw [globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization_pairing]
  rw [globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian_pairing]
  simp only [globalCandidateAMinimalPhysicalReducedHilbertChartPoint, map_zero,
    add_zero]
  rw [globalCandidateALocalHessian_eq_nineBlockSum period hPeriod configuration
    data analysis chartData _
    (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
      configuration data analysis chartData).chartBridge.basePoint_mem]
  rw [globalCandidateAMinimalPhysicalReducedHilbertChartRealization_smooth,
    globalCandidateAMinimalPhysicalReducedHilbertChartRealization_smooth]

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertNineBlockLinearization4D
end JanusFormal
