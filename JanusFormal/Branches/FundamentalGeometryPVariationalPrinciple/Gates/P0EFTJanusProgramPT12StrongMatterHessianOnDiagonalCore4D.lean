import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSecondFrechetLinearPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphCoreCompatibility4D

/-! The translated strong matter action has the same second jet as the
homogeneous H13 graph action on the diagonal finite core. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongMatterHessianOnDiagonalCore4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphCoreCompatibility4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMatterC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPSecondFrechetLinearPullback4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D

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

private theorem translated_matter_graph_second_fderiv
    (massSquared : Real)
    (base : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared) :
    fderiv Real
        (actionGradient (fun state =>
          programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
            (base + state))) 0 =
      programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared := by
  let form := programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
  have hGradient : ∀ state,
      actionGradient (fun current =>
        programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
          (base + current)) state = form (base + state) := by
    intro state
    have hInput : HasFDerivAt (fun current => base + current)
        (ContinuousLinearMap.id Real _) state :=
      (hasFDerivAt_id state).const_add base
    have hAction :=
      (programPPrimitiveSpinCMatterGraphAction_hasFDerivAt period hPeriod
        massSquared (base + state)).comp state hInput
    change fderiv Real (fun current =>
      programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
        (base + current)) state = _
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      hAction.fderiv
  have hFunction :
      (fun state => actionGradient (fun current =>
        programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
          (base + current)) state) =
      (fun state => form base + form state) := by
    funext state
    rw [hGradient, map_add]
  change fderiv Real (fun state => actionGradient (fun current =>
    programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
      (base + current)) state) 0 = _
  rw [hFunction]
  rw [fderiv_const_add]
  exact ContinuousLinearMap.fderiv
    (𝕜 := Real)
    (E := ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared)
    (F := ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared
      →L[Real] Real) form

/-- The concrete strong chart and the H13 graph block have the same matter
Hessian on both slots of the full diagonal smooth core. -/
theorem strong_matter_hessian_on_diagonal_core_eq_graph
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis) :
    globalCandidateAH13LocalMatterHessian period hPeriod
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure) 0
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis first)
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis second) =
      diagonalExtendedBulkH13MatterGraphHessianOnCore period hPeriod
        configuration data analysis first second := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let chart :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure
  let blocks :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration.physical couplings data plusBase minusBase
        hBase measure
  let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongMatterCLM
    period hPeriod configuration data analysis realization plusBase minusBase
  let base := realization.toGraph configuration.physical.spinCMatter
  let translated := fun state : ProgramPPrimitiveSpinCMatterGraphDomain period
      hPeriod couplings.matterMassSquared =>
    programPPrimitiveSpinCMatterGraphAction period hPeriod
      couplings.matterMassSquared (base + state)
  have hOpen :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase
  have hZero : (0 : chart.Model) ∈ chart.family.domain := chart.zero_mem_domain
  have hActionEq : ∀ state ∈ chart.family.domain,
      blocks.matter state = translated (projection state) := by
    intro state hState
    have h :=
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_matter_eq
        period hPeriod configuration data realization plusBase minusBase hBase
          measure state hState
    simpa [blocks, translated, base, projection,
      regularGeneralMetricC2PairedMinimalPhysicalMatterGraphInput,
      globalMinimalPhysicalPairedMetricGaugeLLStrongMatterCLM_apply] using h
  have hGradientEventually :
      actionGradient blocks.matter =ᶠ[𝓝 (0 : chart.Model)]
        actionGradient (fun state => translated (projection state)) := by
    filter_upwards [hOpen.mem_nhds hZero] with state hState
    have hLocal : blocks.matter =ᶠ[𝓝 state]
        (fun current => translated (projection current)) := by
      filter_upwards [hOpen.mem_nhds hState] with current hCurrent
      exact hActionEq current hCurrent
    exact hLocal.fderiv_eq
  have hSecond :
      fderiv Real (actionGradient blocks.matter)
        (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
          configuration.physical) =
        fderiv Real (actionGradient (fun state =>
          translated (projection state))) 0 :=
    hGradientEventually.fderiv_eq
  have hTranslatedC2 : ContDiffAt Real 2 translated (projection 0) := by
    exact ((programPPrimitiveSpinCMatterGraphAction_contDiff_two period hPeriod
      couplings.matterMassSquared).comp
        (contDiff_const.add contDiff_id)).contDiffAt
  have hPullback := secondFrechet_linearPullback translated projection 0
    hTranslatedC2
  have hTranslatedHessian :
      fderiv Real (actionGradient translated) (projection 0) =
        programPPrimitiveSpinCMatterGraphForm period hPeriod
          couplings.matterMassSquared := by
    simpa [translated] using
      translated_matter_graph_second_fderiv period hPeriod
        couplings.matterMassSquared base
  have hCore (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis) :
      projection (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period
        hPeriod configuration data analysis core) =
        programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
          couplings.matterMassSquared core.2.2.1 := by
    calc
      projection (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period
          hPeriod configuration data analysis core) =
        realization.toGraph
          ((diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis core).1.2) := rfl
      _ = realization.toGraph
            (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              core.2.2.1) := by
        rw [diagonalExtendedBulkMinimalPhysicalTangent_matter period hPeriod
          configuration data analysis core]
      _ = _ := realization.finite_compatibility core.2.2.1
  change fderiv Real (actionGradient blocks.matter) 0
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis first)
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis second) = _
  rw [hSecond, hPullback, hTranslatedHessian]
  change programPPrimitiveSpinCMatterGraphForm period hPeriod
    couplings.matterMassSquared
      (projection (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period
        hPeriod configuration data analysis first))
      (projection (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period
        hPeriod configuration data analysis second)) = _
  rw [hCore first, hCore second]
  rfl

end
end P0EFTJanusProgramPT12StrongMatterHessianOnDiagonalCore4D
end JanusFormal
