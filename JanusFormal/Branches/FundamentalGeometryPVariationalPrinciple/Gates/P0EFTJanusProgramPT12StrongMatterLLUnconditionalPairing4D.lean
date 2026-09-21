import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongCompletedMatterLLPhysicalRieszZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PreferredActualZeroMatterLLSevenPhysicalRieszDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongCompletedMatterLLPhysicalRieszCore4D

/-! The strong seven-block Riesz operator vanishes on the completed
matter--full-LL tail, hence on the Friedrichs value-adjoint transport. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongMatterLLUnconditionalPairing4D

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

open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsSmoothCore4D
open P0EFTJanusProgramPGlobalGaugeFixedMatterLLSmoothSlice4D
open P0EFTJanusProgramPT12MinimalPhysicalMatterLLReducedSliceToChart4D
open P0EFTJanusProgramPT12PreferredActualZeroMatterLLFriedrichsDecomposition4D
open P0EFTJanusProgramPT12PreferredActualZeroMatterLLSevenPhysicalRieszDecomposition4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12StrongCompletedMatterLLPhysicalRieszZero4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

variable [IsFiniteMeasure measure]
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
  period hPeriod plusBase minusBase)
variable (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
  period hPeriod configuration.physical plusBase minusBase hBase)

variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
  period hPeriod configuration data analysis (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart period hPeriod configuration data analysis realization plusBase minusBase hBase measure) (strongMatterLLSameActionBridge period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter measure))
variable {iota : Type*} [DecidableEq iota]



/-- The existing value transport retains no strong physical perturbation. -/
theorem strong_friedrichsPhysicalPerturbation_eq_zero :
    programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
      (configuration := configuration) (data := data) (analysis := analysis)
      (chart := (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart period hPeriod configuration data analysis realization plusBase minusBase hBase measure)) (sameAction := (strongMatterLLSameActionBridge period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter measure)) (physical := physical)
      (iota := iota) period hPeriod = 0 := by
  unfold programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
  rw [strong_programPT12FriedrichsMatterLLPhysicalRieszOperator_eq_zero
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase hCenter physical]
  ext state
  change (programPT12GaugeFixedLLFriedrichsMatterLLReadout
    (configuration := configuration) (iota := iota) period hPeriod
      analysis).adjoint 0 = 0
  exact map_zero _

/-- The actual augmented pairing has no remaining physical-form hypothesis
on the reduced matter--LL core. -/
theorem strong_actualMatterLL_pairing_eq_friedrichs
    (covector : iota → TangentVector3)
    (first second : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    let embed := diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis
    let core := programPT12MinimalPhysicalMatterLLReducedSliceCore period
      hPeriod configuration analysis
    inner Real
      (globalCandidateACommonAugmentedRieszOperator period hPeriod
        configuration data analysis (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart period hPeriod configuration data analysis realization plusBase minusBase hBase measure) (strongMatterLLSameActionBridge period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter measure) physical (embed (core first)))
      (embed (core second)) =
    inner Real
      (programPGlobalGaugeFixedLLFriedrichsHessianOperator period hPeriod
        covector couplings.matterMassSquared analysis
        (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
          covector couplings.matterMassSquared analysis
          (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
            (iota := iota) analysis first)))
      (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
        covector couplings.matterMassSquared analysis
        (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
          (iota := iota) analysis second) :
        ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod
          iota analysis) := by
  dsimp only
  rw [globalCandidateACommonAugmentedRieszOperator_pairing,
    globalCandidateACommonAugmentedHessian_smooth_eq_gaugeFixed,
    diagonalExtendedBulkH13GaugeFixed_eq_graph_add_sevenPhysical,
    programPT12MinimalPhysicalMatterLLReducedSlice_graphHessian_eq_friedrichsPairing
      period hPeriod configuration data analysis covector first second]
  rw [← physical.smooth_agreement,
    ← globalCandidateASevenPhysicalCommonRieszOperator_pairing]
  have hZero := strongPhysicalRiesz_matterLLReducedSlice_zero period hPeriod
    configuration data analysis realization plusBase minusBase hBase hCenter
      physical first
  change globalCandidateASevenPhysicalCommonRieszOperator period hPeriod
    configuration data analysis (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart period hPeriod configuration data analysis realization plusBase minusBase hBase measure) (strongMatterLLSameActionBridge period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter measure) physical _ = 0 at hZero
  rw [hZero, inner_zero_left, add_zero]

/-- Exact pairing with the physical zero fibre, without a transport-form
match or an ambient intertwiner assumption. -/
theorem strong_actualMatterLL_pairing_eq_physicalZero
    (covector : iota → TangentVector3)
    (first second : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    let embed := diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis
    let core := programPT12MinimalPhysicalMatterLLReducedSliceCore period
      hPeriod configuration analysis
    let firstDomain := programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap
      period hPeriod covector couplings.matterMassSquared analysis
      (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
        (iota := iota) analysis first)
    let secondDomain := programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap
      period hPeriod covector couplings.matterMassSquared analysis
      (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
        (iota := iota) analysis second)
    inner Real
      (globalCandidateACommonAugmentedRieszOperator period hPeriod
        configuration data analysis (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart period hPeriod configuration data analysis realization plusBase minusBase hBase measure) (strongMatterLLSameActionBridge period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter measure) physical (embed (core first)))
      (embed (core second)) =
    inner Real
      (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
        (configuration := configuration) (data := data) (analysis := analysis)
        (chart := (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart period hPeriod configuration data analysis realization plusBase minusBase hBase measure)) (sameAction := (strongMatterLLSameActionBridge period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter measure)) (physical := physical)
        period hPeriod covector 0 firstDomain)
      (secondDomain : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis) := by
  dsimp only
  rw [programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_pairing,
    ← programPT12GaugeFixedLLFriedrichsPhysicalPerturbation_pairing,
    strong_friedrichsPhysicalPerturbation_eq_zero period hPeriod configuration
      data analysis realization plusBase minusBase hBase hCenter physical]
  simp only [zero_apply, inner_zero_left, add_zero]
  rw [programPT12GaugeFixedLLFriedrichsD11Operator_zero_matterLLSlice_pairing]
  exact strong_actualMatterLL_pairing_eq_friedrichs period hPeriod
    configuration data analysis realization plusBase minusBase hBase hCenter
      physical covector first second

end
end
end P0EFTJanusProgramPT12StrongMatterLLUnconditionalPairing4D
end JanusFormal
