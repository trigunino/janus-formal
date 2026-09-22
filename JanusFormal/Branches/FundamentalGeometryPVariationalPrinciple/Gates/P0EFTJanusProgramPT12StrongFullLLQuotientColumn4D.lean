import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongCompletedMatterLLPhysicalRieszCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLQuotientFriedrichsSmoothPairing4D

/-! The full LL column of the actual augmented Riesz pairs exactly with
its quotient Friedrichs realization against every actual smooth test. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongFullLLQuotientColumn4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCTotalEuler4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12StrongLLPhysicalMixedHessianZero4D
open P0EFTJanusProgramPT12StrongMatterLLSameActionBridge4D
open P0EFTJanusProgramPT12StrongPhysicalSecondJet4D
open P0EFTJanusProgramPT12StrongToH11PhysicalSecondJet4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2AbelianInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterCompleteSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLCompleteSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
  P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D.programPPrimitiveSpinCMatterHilbertRealInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)

set_option backward.isDefEq.respectTransparency false
open P0EFTJanusProgramPT12StrongCompletedMatterLLPhysicalRieszZero4D
open P0EFTJanusProgramPT12LLQuotientFriedrichsRealization4D
open P0EFTJanusProgramPT12LLQuotientFriedrichsSmoothPairing4D
open P0EFTJanusProgramPT12LLFullJacobiHilbertQuotient4D

/-- All three smooth LL slots, inserted with the other sectors zero. -/
def fullLLCore : GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis :=
  (programPT12StrongMatterFullLLSmoothSliceCore period hPeriod configuration analysis).comp
    (LinearMap.inr Real _ _)

theorem fullLLCore_graph_pairing (direction : GlobalFullLLSmooth period hPeriod analysis)
    (test : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration data analysis
      (fullLLCore period hPeriod configuration analysis direction) test =
      globalCandidateAFullLLSameActionHessian period hPeriod data direction test.2.2.2 := by
  simp [diagonalExtendedBulkGraphHessianOnCore, diagonalExtendedBulkHessian_apply,
    fullLLCore, programPT12StrongMatterFullLLSmoothSliceCore,
    globalCandidateAFullLLGraphForm_apply, globalCandidateAFullLLContinuousHessian_smooth]

variable [IsFiniteMeasure measure]
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
  period hPeriod plusBase minusBase)
variable (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
  period hPeriod configuration.physical plusBase minusBase hBase)

abbrev strongChart := regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
  period hPeriod configuration data analysis realization plusBase minusBase hBase measure
abbrev strongBridge := strongMatterLLSameActionBridge period hPeriod configuration data analysis
  realization plusBase minusBase hBase hCenter measure

variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
  period hPeriod configuration data analysis
  (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
  (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter))

abbrev strongAugmentedRiesz := globalCandidateACommonAugmentedRieszOperator
  period hPeriod configuration data analysis
  (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
  (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter) physical

/-- All H11 contributions disappear from this full LL column, for arbitrary tests. -/
theorem strong_fullLL_augmented_pairing (direction : GlobalFullLLSmooth period hPeriod analysis)
    (test : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    let embed := diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) couplings.matterMassSquared data analysis
    inner Real
      (strongAugmentedRiesz (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter
        physical (embed (fullLLCore period hPeriod configuration analysis direction)))
      (embed test) = globalCandidateAFullLLSameActionHessian period hPeriod data direction test.2.2.2 := by
  dsimp only
  rw [globalCandidateACommonAugmentedRieszOperator_pairing,
    globalCandidateACommonAugmentedHessian_smooth_eq_gaugeFixed,
    diagonalExtendedBulkH13GaugeFixed_eq_graph_add_sevenPhysical, fullLLCore_graph_pairing,
    ← physical.smooth_agreement, ← globalCandidateASevenPhysicalCommonRieszOperator_pairing]
  have hPhysical := strongPhysicalRiesz_matterFullLLSmoothSlice_zero period hPeriod
    configuration data analysis realization plusBase minusBase hBase hCenter physical (0, direction)
  change globalCandidateASevenPhysicalCommonRieszOperator period hPeriod configuration data analysis
    (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
    (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter)
    physical (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) couplings.matterMassSquared data analysis
      (fullLLCore period hPeriod configuration analysis direction)) = 0 at hPhysical
  rw [hPhysical, inner_zero_left, add_zero]

theorem strong_fullLL_augmented_pairing_eq_quotient
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (direction : GlobalFullLLSmooth period hPeriod analysis)
    (test : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    let embed := diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) couplings.matterMassSquared data analysis
    inner Real
      (strongAugmentedRiesz (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter
        physical (embed (fullLLCore period hPeriod configuration analysis direction)))
      (embed test) =
      inner Real (quotientLLFriedrichs period hPeriod analysis
        (quotientLLFriedrichsSmoothDomainElement period hPeriod analysis direction))
        (fullLLReducedHilbertCore period hPeriod analysis test.2.2.2) := by
  exact (strong_fullLL_augmented_pairing period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical direction test).trans
      (quotientLLFriedrichs_smooth_sameAction_pairing period hPeriod analysis data hZero direction test.2.2.2).symm

end
end
end P0EFTJanusProgramPT12StrongFullLLQuotientColumn4D
end JanusFormal
