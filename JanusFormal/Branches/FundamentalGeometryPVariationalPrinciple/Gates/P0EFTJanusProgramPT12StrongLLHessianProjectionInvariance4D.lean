import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongLLAtOriginSecondJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSecondFrechetLinearPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphCoreCompatibility4D

/-! The nonlinear strong LL Hessian only sees the three LL coefficients. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongLLHessianProjectionInvariance4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphCoreCompatibility4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D
open P0EFTJanusProgramPSecondFrechetLinearPullback4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- The strong LL Hessian factors through the continuous three-slot first-jet
projection, so changing any of the other physical slots leaves it unchanged. -/
theorem strongLLAction_second_fderiv_projection_invariant
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
    (first second first' second' : GlobalMinimalPhysicalFieldTangent period
      hPeriod configuration.physical)
    (hFirst : globalMinimalPhysicalLLSmoothCoefficientLinearMap period hPeriod
        configuration.physical first =
      globalMinimalPhysicalLLSmoothCoefficientLinearMap period hPeriod
        configuration.physical first')
    (hSecond : globalMinimalPhysicalLLSmoothCoefficientLinearMap period hPeriod
        configuration.physical second =
      globalMinimalPhysicalLLSmoothCoefficientLinearMap period hPeriod
        configuration.physical second') :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    fderiv Real (fun state => fderiv Real
        (regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
          configuration.physical) state)
      (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical) first second =
    fderiv Real (fun state => fderiv Real
        (regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
          configuration.physical) state)
      (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical) first' second' := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
    (canonicalDivergenceFreeLLFrame period hPeriod)
  let frame := canonicalDivergenceFreeLLFrame period hPeriod
  letI : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  let projection := globalMinimalPhysicalPairedLLC0FirstJetCLM period hPeriod
    configuration data analysis realization plusBase minusBase frame
  let basePacket := smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame
    (configuration.physical.coefficientFields.llAuxMetric,
      (configuration.physical.coefficientFields.llMeasure,
        configuration.physical.coefficientFields.llField))
  let translated := fun packet => regularGeneralMetricC0LLPTAction period hPeriod
    frame (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (basePacket + packet)
  have hAction : regularGeneralMetricC2PairedMinimalPhysicalLLAction period
      hPeriod configuration.physical = fun state => translated (projection state) := by
    funext state
    unfold regularGeneralMetricC2PairedMinimalPhysicalLLAction translated
    rw [regularGeneralMetricC2PairedMinimalPhysicalLLPacketInput_eq_affine]
    rfl
  have hTranslatedC2 : ContDiffAt Real 2 translated (projection 0) := by
    exact ((regularGeneralMetricC0LLPTAction_contDiff period hPeriod frame
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).comp
        (contDiff_const.add contDiff_id)).contDiffAt.of_le
          (show (2 : ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hPullback := secondFrechet_linearPullback translated projection 0
    hTranslatedC2
  have hFirstProjection : projection first = projection first' := by
    change smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame
      (globalMinimalPhysicalLLSmoothCoefficientLinearMap period hPeriod
        configuration.physical first) =
      smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame
        (globalMinimalPhysicalLLSmoothCoefficientLinearMap period hPeriod
          configuration.physical first')
    rw [hFirst]
  have hSecondProjection : projection second = projection second' := by
    change smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame
      (globalMinimalPhysicalLLSmoothCoefficientLinearMap period hPeriod
        configuration.physical second) =
      smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame
        (globalMinimalPhysicalLLSmoothCoefficientLinearMap period hPeriod
          configuration.physical second')
    rw [hSecond]
  change (fderiv Real
      (fun state => fderiv Real
        (regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
          configuration.physical) state) 0) first second = _
  rw [hAction]
  change (fderiv Real
      (actionGradient (fun state => translated (projection state))) 0)
      first second =
    (fderiv Real
      (actionGradient (fun state => translated (projection state))) 0)
      first' second'
  rw [hPullback]
  change (fderiv Real (fun state => fderiv Real translated state)
      (projection 0)) (projection first) (projection second) =
    (fderiv Real (fun state => fderiv Real translated state)
      (projection 0)) (projection first') (projection second')
  rw [hFirstProjection, hSecondProjection]

/-- A corrected diagonal core direction and its pure LL part have identical
three-slot LL coefficients. -/
theorem diagonalCore_LL_coefficients_eq_pure
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalMinimalPhysicalLLSmoothCoefficientLinearMap period hPeriod
        configuration.physical
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis core) =
      globalMinimalPhysicalLLSmoothCoefficientLinearMap period hPeriod
        configuration.physical
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
          hPeriod configuration.physical
          (core.2.2.2.1.1, (core.2.2.2.1.2, core.2.2.2.2.toTest))) := by
  have hFull := diagonalExtendedBulkMinimalPhysicalTangent_fullLL period hPeriod
    configuration data analysis core
  have hCore := congrArg
    (fun ll : GlobalFullLLSmooth period hPeriod analysis =>
      (ll.1.1, (ll.1.2, ll.2.toTest))) hFull
  change globalMinimalPhysicalLLSmoothCoefficientLinearMap period hPeriod
      configuration.physical
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis core) = _
  rw [show globalMinimalPhysicalLLSmoothCoefficientLinearMap period hPeriod
      configuration.physical
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis core) =
        (core.2.2.2.1.1, (core.2.2.2.1.2, core.2.2.2.2.toTest)) from hCore]
  simp [globalMinimalPhysicalLLSmoothCoefficientLinearMap,
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection,
    regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkDirection,
    globalMinimalPhysicalSevenBulkEquiv,
    globalMinimalPhysicalTangentSectorEquiv,
    P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D.productFirstInclusion,
    GlobalPhysicalFieldTangent.completeVariation]

/-- All seven non-LL directions in a diagonal smooth core disappear from the
second jet of the authentic strong LL action. -/
theorem strongLLAction_second_fderiv_diagonalCore_eq_pureLL
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
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    fderiv Real (fun state => fderiv Real
        (regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
          configuration.physical) state)
      (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical)
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis first)
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis second) =
    fderiv Real (fun state => fderiv Real
        (regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
          configuration.physical) state)
      (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical)
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical
        (first.2.2.2.1.1, (first.2.2.2.1.2, first.2.2.2.2.toTest)))
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical
        (second.2.2.2.1.1, (second.2.2.2.1.2, second.2.2.2.2.toTest))) := by
  exact strongLLAction_second_fderiv_projection_invariant period hPeriod
    configuration data analysis realization plusBase minusBase _ _ _ _
    (diagonalCore_LL_coefficients_eq_pure period hPeriod configuration data
      analysis first)
    (diagonalCore_LL_coefficients_eq_pure period hPeriod configuration data
      analysis second)

/-- At the chart center, the actual local LL block has the H13 graph Hessian
on every pair of corrected diagonal smooth core directions. -/
theorem strong_LL_hessian_on_diagonal_core_eq_graph
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
    globalCandidateAH13LocalLLHessian period hPeriod
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure) 0
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis first)
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis second) =
      diagonalExtendedBulkH13LLGraphHessianOnCore period hPeriod configuration
        data analysis first second := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let chart := regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure
  let blocks := regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
    period hPeriod configuration.physical couplings data plusBase minusBase hBase
      measure
  let action := regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
    configuration.physical
  have hOpen := regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
    period hPeriod configuration data analysis realization plusBase minusBase
  have hZero : (0 : chart.Model) ∈ chart.family.domain := chart.zero_mem_domain
  have hActionEq : ∀ state ∈ chart.family.domain,
      blocks.ll state = action state := by
    intro state hState
    exact regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_ll_eq
      period hPeriod configuration.physical data plusBase minusBase hBase
        measure state hState
  have hGradientEventually :
      actionGradient blocks.ll =ᶠ[𝓝 (0 : chart.Model)] actionGradient action := by
    filter_upwards [hOpen.mem_nhds hZero] with state hState
    have hLocal : blocks.ll =ᶠ[𝓝 state] action := by
      filter_upwards [hOpen.mem_nhds hState] with current hCurrent
      exact hActionEq current hCurrent
    exact hLocal.fderiv_eq
  have hSecond : fderiv Real (actionGradient blocks.ll)
      (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical) =
      fderiv Real (actionGradient action) 0 :=
    hGradientEventually.fderiv_eq
  change fderiv Real (actionGradient blocks.ll) 0
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis first)
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis second) = _
  rw [hSecond]
  calc
    _ = fderiv Real (actionGradient action) 0
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
          hPeriod configuration.physical
          (first.2.2.2.1.1, (first.2.2.2.1.2, first.2.2.2.2.toTest)))
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
          hPeriod configuration.physical
          (second.2.2.2.1.1, (second.2.2.2.1.2,
            second.2.2.2.2.toTest))) :=
      strongLLAction_second_fderiv_diagonalCore_eq_pureLL period hPeriod
        configuration data analysis realization plusBase minusBase first second
    _ = _ := by
      exact P0EFTJanusProgramPT12StrongLLAtOriginSecondJet4D.strongLLAction_second_fderiv_eq_graph_on_smooth
        period hPeriod configuration data analysis realization plusBase
          minusBase first.2.2.2 second.2.2.2

end
end P0EFTJanusProgramPT12StrongLLHessianProjectionInvariance4D
end JanusFormal
