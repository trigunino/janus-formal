import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongCompletedMatterLLPhysicalRieszCore4D

/-! The strong seven-block Riesz operator vanishes on the completed
matter--full-LL tail, hence on the Friedrichs value-adjoint transport. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongCompletedMatterLLPhysicalRieszZero4D

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

private abbrev ActualDiffeomorphism :=
  GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)

private abbrev ActualAbelian :=
  GlobalPairedAbelianOffShellGraphHilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)

private abbrev ActualMatter :=
  ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod
    couplings.matterMassSquared

private abbrev ActualLL :=
  GlobalFullLLGraphHilbert period hPeriod data analysis

private theorem completedMatterLLInclusion_inner
    (tail : ProgramPT12StrongCompletedMatterLL period hPeriod configuration
      data analysis)
    (actual : CommonAugmentedHilbert period hPeriod configuration data
      analysis) :
    inner Real
        (programPT12StrongCompletedMatterLLInclusion
          (configuration := configuration) (data := data)
            (analysis := analysis) period hPeriod tail) actual =
      inner Real tail
        (programPT12StrongCompletedMatterLLProjection
          (configuration := configuration) (data := data)
            (analysis := analysis) period hPeriod actual) := by
  change
    inner Real
        (0 : ActualDiffeomorphism period hPeriod configuration data)
        (WithLp.fst actual) +
      (inner Real (0 : ActualAbelian period hPeriod configuration data)
          (WithLp.fst (WithLp.snd actual)) +
        inner Real tail (WithLp.snd (WithLp.snd actual))) =
      inner Real tail (WithLp.snd (WithLp.snd actual))
  simp [inner_zero_left]
  exact inner_zero_left _

/-- The value readout after restricting to the completed matter--full-LL
tail. -/
def programPT12StrongCompletedMatterLLReadout :
    ProgramPT12StrongCompletedMatterLL period hPeriod configuration data
        analysis →L[Real]
      ProgramPT12GaugeFixedLLFriedrichsMatterLLHilbert period hPeriod
        analysis :=
  (WithLp.prodContinuousLinearEquiv 2 Real
      ProgramPPrimitiveSpinCMatterHilbert
      (CanonicalLLL2 period hPeriod analysis)).symm.toContinuousLinearMap.comp
    (((programPPrimitiveSpinCMatterGraphFstRealCLM period hPeriod
        couplings.matterMassSquared).comp
      ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod
          couplings.matterMassSquared).toContinuousLinearMap.comp
        (WithLp.fstL 2 Real
          (ActualMatter (couplings := couplings) period hPeriod)
          (ActualLL period hPeriod configuration data analysis)))).prod
      ((canonicalLLH1ToFluxL2 period hPeriod analysis).comp
        ((globalCandidateAFullLLFieldProjection period hPeriod data
          analysis).comp
          (WithLp.sndL 2 Real
            (ActualMatter (couplings := couplings) period hPeriod)
            (ActualLL period hPeriod configuration data analysis)))))

private theorem actualReadout_eq_completed_comp_projection :
    programPT12ActualToFriedrichsMatterLLReadout
        (configuration := configuration) (data := data) (analysis := analysis)
        period hPeriod =
      (programPT12StrongCompletedMatterLLReadout
        (configuration := configuration) (data := data) period hPeriod
          analysis).comp
        (programPT12StrongCompletedMatterLLProjection
          (configuration := configuration) (data := data) (analysis := analysis)
            period hPeriod) := by
  ext state
  rfl

/-- The adjoint value transport lands in the completed matter--full-LL tail. -/
theorem programPT12FriedrichsMatterLLToActualTransport_eq_completedInclusion
    (source : ProgramPT12GaugeFixedLLFriedrichsMatterLLHilbert period hPeriod
      analysis) :
    programPT12FriedrichsMatterLLToActualTransport
        (configuration := configuration) (data := data) (analysis := analysis)
        period hPeriod source =
      programPT12StrongCompletedMatterLLInclusion
        (configuration := configuration) (data := data) (analysis := analysis)
        period hPeriod
        ((programPT12StrongCompletedMatterLLReadout
          (configuration := configuration) (data := data) period hPeriod
            analysis).adjoint source) := by
  apply ext_inner_right Real
  intro actual
  calc
    inner Real
        (programPT12FriedrichsMatterLLToActualTransport
          (configuration := configuration) (data := data)
            (analysis := analysis) period hPeriod source) actual =
      inner Real source
        (programPT12ActualToFriedrichsMatterLLReadout
          (configuration := configuration) (data := data)
            (analysis := analysis) period hPeriod actual) :=
      programPT12FriedrichsMatterLLToActualTransport_pairing period hPeriod
        configuration data analysis source actual
    _ = inner Real source
        (programPT12StrongCompletedMatterLLReadout
          (configuration := configuration) (data := data) period hPeriod
            analysis
          (programPT12StrongCompletedMatterLLProjection
            (configuration := configuration) (data := data)
              (analysis := analysis) period hPeriod actual)) := by
      rw [actualReadout_eq_completed_comp_projection period hPeriod
        configuration data analysis]
      rfl
    _ = inner Real
        ((programPT12StrongCompletedMatterLLReadout
          (configuration := configuration) (data := data) period hPeriod
            analysis).adjoint source)
        (programPT12StrongCompletedMatterLLProjection
          (configuration := configuration) (data := data)
            (analysis := analysis) period hPeriod actual) := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      rfl
    _ = inner Real
        (programPT12StrongCompletedMatterLLInclusion
          (configuration := configuration) (data := data)
            (analysis := analysis) period hPeriod
          ((programPT12StrongCompletedMatterLLReadout
            (configuration := configuration) (data := data) period hPeriod
              analysis).adjoint source)) actual := by
      exact (completedMatterLLInclusion_inner period hPeriod configuration data
        analysis _ actual).symm

/-- The concrete strong-chart physical Riesz operator kills the adjoint
matter--LL value transport. -/
theorem strongPhysicalRiesz_friedrichsMatterLLTransport_zero
    [IsFiniteMeasure measure]
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
      period hPeriod configuration.physical plusBase minusBase hBase)
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure)
      (strongMatterLLSameActionBridge period hPeriod configuration data analysis
        realization plusBase minusBase hBase hCenter measure))
    (source : ProgramPT12GaugeFixedLLFriedrichsMatterLLHilbert period hPeriod
      analysis) :
    globalCandidateASevenPhysicalCommonRieszOperator period hPeriod
        configuration data analysis
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure)
        (strongMatterLLSameActionBridge period hPeriod configuration data
          analysis realization plusBase minusBase hBase hCenter measure)
        physical
        (programPT12FriedrichsMatterLLToActualTransport
          (configuration := configuration) (data := data)
            (analysis := analysis) period hPeriod source) = 0 := by
  rw [programPT12FriedrichsMatterLLToActualTransport_eq_completedInclusion
    period hPeriod configuration data analysis source]
  exact strongPhysicalRiesz_completedMatterLL_zero period hPeriod
    configuration data analysis realization plusBase minusBase hBase hCenter
      physical _

/-- Consequently the pulled matter--LL physical Riesz operator is identically
zero for the concrete strong chart. -/
theorem strong_programPT12FriedrichsMatterLLPhysicalRieszOperator_eq_zero
    [IsFiniteMeasure measure]
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
      period hPeriod configuration.physical plusBase minusBase hBase)
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure)
      (strongMatterLLSameActionBridge period hPeriod configuration data analysis
        realization plusBase minusBase hBase hCenter measure)) :
    programPT12FriedrichsMatterLLPhysicalRieszOperator
        (configuration := configuration) (data := data) (analysis := analysis)
        (chart :=
          regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
            period hPeriod configuration data analysis realization plusBase
              minusBase hBase measure)
        (sameAction := strongMatterLLSameActionBridge period hPeriod
          configuration data analysis realization plusBase minusBase hBase
            hCenter measure)
        (physical := physical) period hPeriod = 0 := by
  apply ContinuousLinearMap.ext
  intro source
  change programPT12ActualToFriedrichsMatterLLReadout
      (configuration := configuration) (data := data) (analysis := analysis)
      period hPeriod
      (globalCandidateASevenPhysicalCommonRieszOperator period hPeriod
        configuration data analysis
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure)
        (strongMatterLLSameActionBridge period hPeriod configuration data
          analysis realization plusBase minusBase hBase hCenter measure)
        physical
        (programPT12FriedrichsMatterLLToActualTransport
          (configuration := configuration) (data := data)
            (analysis := analysis) period hPeriod source)) = 0
  rw [strongPhysicalRiesz_friedrichsMatterLLTransport_zero period hPeriod
    configuration data analysis realization plusBase minusBase hBase hCenter
      physical source]
  exact ContinuousLinearMap.map_zero _

end

end
end P0EFTJanusProgramPT12StrongCompletedMatterLLPhysicalRieszZero4D
end JanusFormal
