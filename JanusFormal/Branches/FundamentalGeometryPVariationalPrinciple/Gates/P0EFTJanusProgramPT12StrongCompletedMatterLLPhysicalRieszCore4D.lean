import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongPhysicalSecondJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D

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
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusCompleteVariationModuleCore4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusIndependentFieldVariationLinearSpace4D
open P0EFTJanusProgramPCommonLLActionVariation4D
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
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
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

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

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

/-- Completed actual matter--full-LL tail. -/
abbrev ProgramPT12StrongCompletedMatterLL :=
  WithLp 2
    (ActualMatter (couplings := couplings) period hPeriod ×
      ActualLL period hPeriod configuration data analysis)

private abbrev ActualAbelianMatterLLTail :=
  WithLp 2
    (ActualAbelian period hPeriod configuration data ×
      ProgramPT12StrongCompletedMatterLL period hPeriod configuration data
        analysis)

/-- Isometric coordinate insertion of the completed matter--full-LL tail. -/
def programPT12StrongCompletedMatterLLInclusion :
    ProgramPT12StrongCompletedMatterLL period hPeriod configuration data
        analysis →L[Real]
      CommonAugmentedHilbert period hPeriod configuration data analysis :=
  (WithLp.prodContinuousLinearEquiv 2 Real
      (ActualDiffeomorphism period hPeriod configuration data)
      (ActualAbelianMatterLLTail period hPeriod configuration data analysis)
      ).symm.toContinuousLinearMap.comp
    ((0 : ProgramPT12StrongCompletedMatterLL period hPeriod configuration data
        analysis →L[Real]
      ActualDiffeomorphism period hPeriod configuration data).prod
      ((WithLp.prodContinuousLinearEquiv 2 Real
          (ActualAbelian period hPeriod configuration data)
          (ProgramPT12StrongCompletedMatterLL period hPeriod configuration
            data analysis)).symm.toContinuousLinearMap.comp
        ((0 : ProgramPT12StrongCompletedMatterLL period hPeriod configuration
            data analysis →L[Real]
          ActualAbelian period hPeriod configuration data).prod
          (ContinuousLinearMap.id Real
            (ProgramPT12StrongCompletedMatterLL period hPeriod configuration
              data analysis)))))

/-- Coordinate projection back to the completed matter--full-LL tail. -/
def programPT12StrongCompletedMatterLLProjection :
    CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
      ProgramPT12StrongCompletedMatterLL period hPeriod configuration data
        analysis :=
  (WithLp.sndL 2 Real
      (ActualAbelian period hPeriod configuration data)
      (ProgramPT12StrongCompletedMatterLL period hPeriod configuration data
        analysis)).comp
    (WithLp.sndL 2 Real
      (ActualDiffeomorphism period hPeriod configuration data)
      (ActualAbelianMatterLLTail period hPeriod configuration data analysis))

/-- Finite matter coefficients paired with all three smooth LL slots. -/
abbrev ProgramPT12StrongMatterFullLLSmoothSlice :=
  ProgramPPrimitiveSpinCMatterFiniteCoefficients ×
    GlobalFullLLSmooth period hPeriod analysis

/-- Pure matter--full-LL insertion into the diagonal smooth core. -/
def programPT12StrongMatterFullLLSmoothSliceCore :
    ProgramPT12StrongMatterFullLLSmoothSlice period hPeriod configuration
        analysis →ₗ[Real]
      GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis where
  toFun direction := (0, (0, (direction.1, direction.2)))
  map_add' first second := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · apply Prod.ext <;> simp
  map_smul' scalar direction := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · apply Prod.ext <;> simp

/-- Finite matter graph vectors in the genuine L2 product model. -/
private def matterFiniteL2Embedding :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
      ActualMatter (couplings := couplings) period hPeriod :=
  (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod
      couplings.matterMassSquared).symm.toLinearMap.comp
    (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
      couplings.matterMassSquared)

private theorem matterFiniteL2Embedding_denseRange :
    DenseRange
      (matterFiniteL2Embedding (couplings := couplings) period hPeriod) := by
  have hBack :=
    ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod
      couplings.matterMassSquared).symm.surjective.denseRange).comp
      (programPPrimitiveSpinCMatterGraphFiniteLinearMap_denseRange period
        hPeriod couplings.matterMassSquared)
      (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod
        couplings.matterMassSquared).symm.continuous
  simpa [matterFiniteL2Embedding,
    programPPrimitiveSpinCMatterGraphFiniteRealLinearMap,
    Function.comp_def] using hBack

/-- Dense smooth parametrization of the completed matter--full-LL tail. -/
def programPT12StrongMatterFullLLSmoothToCompleted :
    ProgramPT12StrongMatterFullLLSmoothSlice period hPeriod configuration
        analysis →ₗ[Real]
      ProgramPT12StrongCompletedMatterLL period hPeriod configuration data
        analysis :=
  (WithLp.prodContinuousLinearEquiv 2 Real
      (ActualMatter (couplings := couplings) period hPeriod)
      (ActualLL period hPeriod configuration data analysis)
      ).symm.toLinearMap.comp
    (LinearMap.prodMap
      (matterFiniteL2Embedding (couplings := couplings) period hPeriod)
      (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis))

theorem programPT12StrongMatterFullLLSmoothToCompleted_denseRange :
    DenseRange
      (programPT12StrongMatterFullLLSmoothToCompleted
        (configuration := configuration) (data := data) period hPeriod
          analysis) := by
  have hProduct :=
    (matterFiniteL2Embedding_denseRange (couplings := couplings) period
      hPeriod).prodMap
      (globalCandidateAFullLLSmoothEmbedding_denseRange period hPeriod data
        analysis)
  have hBack :=
    ((WithLp.prodContinuousLinearEquiv 2 Real
      (ActualMatter (couplings := couplings) period hPeriod)
      (ActualLL period hPeriod configuration data analysis)
      ).symm.surjective.denseRange).comp hProduct
      (WithLp.prodContinuousLinearEquiv 2 Real
        (ActualMatter (couplings := couplings) period hPeriod)
        (ActualLL period hPeriod configuration data analysis)
        ).symm.continuous
  change DenseRange (fun direction => WithLp.toLp 2
    (Prod.map
      (matterFiniteL2Embedding (couplings := couplings) period hPeriod)
      (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis)
      direction))
  exact hBack

private theorem completedInclusion_smooth_eq_core
    (direction : ProgramPT12StrongMatterFullLLSmoothSlice period hPeriod
      configuration analysis) :
    programPT12StrongCompletedMatterLLInclusion
        (configuration := configuration) (data := data) (analysis := analysis)
        period hPeriod
        (programPT12StrongMatterFullLLSmoothToCompleted
          (configuration := configuration) (data := data) period hPeriod
            analysis direction) =
      diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        (programPT12StrongMatterFullLLSmoothSliceCore period hPeriod
          configuration analysis direction) := by
  unfold programPT12StrongCompletedMatterLLInclusion
    programPT12StrongMatterFullLLSmoothToCompleted
    matterFiniteL2Embedding
    programPT12StrongMatterFullLLSmoothSliceCore
    diagonalExtendedBulkL2SmoothEmbedding
    diagonalExtendedBulkL2Equiv
    diagonalExtendedBulkSmoothEmbedding
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (0 : ActualDiffeomorphism period hPeriod configuration data) =
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period
        hPeriod (globalCandidateAMetricBySector period hPeriod data)) 0
    exact (map_zero _).symm
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change (0 : ActualAbelian period hPeriod configuration data) =
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)) 0
      exact (map_zero _).symm
    · apply WithLp.ofLp_injective 2
      apply Prod.ext <;> rfl

private theorem strongPureMatter_minimal_eq_strongMatter
    (matter : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis (0, (0, (matter, 0))) =
      regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
          period hPeriod configuration.physical
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            matter) := by
  apply Subtype.ext
  simp [diagonalExtendedBulkMinimalPhysicalTangentLinearMap,
    diagonalExtendedBulkGaugeFixedTangentLinearMap,
    extendedMatterGaugeFixedTangentLinearMap,
    extendedLLGaugeFixedTangentLinearMap,
    extendedMatterMinimalTangentLinearMap,
    extendedLLMinimalTangentLinearMap,
    globalGaugeFixedPhysicalTangentPhysicalProjectionLinearMap,
    globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap,
    globalCandidateABulkMatterPhysicalTangentLinearMap,
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection,
    globalMinimalPhysicalTangentSectorEquiv,
    productSecondInclusion,
    programPPrimitiveSpinCMatterSmoothFiniteSynthesisRealLinearMap,
    programPPrimitiveSpinCMatterSmoothFiniteSynthesisLinearMap]

private theorem strongPureFullLL_minimal_eq_strongLL
    (ll : GlobalFullLLSmooth period hPeriod analysis) :
    diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis (0, (0, (0, ll))) =
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical
        (ll.1.1, (ll.1.2, ll.2.toTest)) := by
  apply Subtype.ext
  simp [diagonalExtendedBulkMinimalPhysicalTangentLinearMap,
    diagonalExtendedBulkGaugeFixedTangentLinearMap,
    extendedMatterGaugeFixedTangentLinearMap,
    extendedLLGaugeFixedTangentLinearMap,
    extendedMatterMinimalTangentLinearMap,
    extendedLLMinimalTangentLinearMap,
    globalGaugeFixedPhysicalTangentPhysicalProjectionLinearMap,
    globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap,
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection,
    regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkDirection,
    globalMinimalPhysicalTangentSectorEquiv,
    globalMinimalPhysicalSevenBulkEquiv,
    productFirstInclusion,
    fullLLSmoothPhysicalTangentLinearMap,
    fullLLSmoothGeneralMetricLinearMap,
    fullLLSmoothMatterFreeLinearMap,
    fullLLSmoothCompleteLinearMap,
    fullLLSmoothIndependentLinearMap,
    independentCompleteVariationLinearMap,
    independentCompleteVariation,
    zeroSmoothDiagonalMetricVariation]
  constructor
  · apply SmoothDiagonalMetricVariation.ext <;> rfl
  constructor
  · funext sector
    rfl
  constructor
  · funext sector
    apply ContMDiffSection.coe_injective
    rfl
  · funext sector
    apply SmoothSymmetricCovariantTwoTensor.ext
    rfl

private theorem strongMatterFullLLSlice_minimal_eq_strong
    (direction : ProgramPT12StrongMatterFullLLSmoothSlice period hPeriod
      configuration analysis) :
    diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis
        (programPT12StrongMatterFullLLSmoothSliceCore period hPeriod
          configuration analysis direction) =
      regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
          period hPeriod configuration.physical
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            direction.1) +
        regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
          hPeriod configuration.physical
          (direction.2.1.1, (direction.2.1.2, direction.2.2.toTest)) := by
  have hCore :
      programPT12StrongMatterFullLLSmoothSliceCore period hPeriod
          configuration analysis direction =
        (0, (0, (direction.1, 0))) + (0, (0, (0, direction.2))) := by
    ext <;> simp [programPT12StrongMatterFullLLSmoothSliceCore]
  rw [hCore, map_add,
    strongPureMatter_minimal_eq_strongMatter period hPeriod configuration data
      analysis direction.1,
    strongPureFullLL_minimal_eq_strongLL period hPeriod configuration data
      analysis direction.2]

/-- All seven physical blocks annihilate every smooth matter--full-LL vector
on the centered strong chart. -/
theorem strongPhysicalRiesz_matterFullLLSmoothSlice_zero
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
    (direction : ProgramPT12StrongMatterFullLLSmoothSlice period hPeriod
      configuration analysis) :
    globalCandidateASevenPhysicalCommonRieszOperator period hPeriod
        configuration data analysis
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure)
        (strongMatterLLSameActionBridge period hPeriod configuration data
          analysis realization plusBase minusBase hBase hCenter measure)
        physical
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis
          (programPT12StrongMatterFullLLSmoothSliceCore period hPeriod
            configuration analysis direction)) = 0 := by
  apply physicalRiesz_core_zero_of_hessian_column_zero period hPeriod
    configuration data analysis
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure)
    (strongMatterLLSameActionBridge period hPeriod configuration data analysis
      realization plusBase minusBase hBase hCenter measure)
    physical
    (programPT12StrongMatterFullLLSmoothSliceCore period hPeriod configuration
      analysis direction)
  intro test
  rw [(strongPhysicalSecondJet period hPeriod configuration data analysis
    realization plusBase minusBase hBase hCenter measure).physical_second_jet]
  rw [strongMatterFullLLSlice_minimal_eq_strong period hPeriod configuration
    data analysis direction]
  exact strong_matter_LL_physical_mixed_hessian_zero period hPeriod
    configuration data analysis realization plusBase minusBase hBase measure
    0
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis test)
    (zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration.physical plusBase minusBase hBase)
    (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
      direction.1)
    (direction.2.1.1, (direction.2.1.2, direction.2.2.toTest))

/-- Continuity extends the smooth cancellation to the entire completed
matter--full-LL tail. -/
theorem strongPhysicalRiesz_completedMatterLL_zero
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
    (state : ProgramPT12StrongCompletedMatterLL period hPeriod configuration
      data analysis) :
    globalCandidateASevenPhysicalCommonRieszOperator period hPeriod
        configuration data analysis
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure)
        (strongMatterLLSameActionBridge period hPeriod configuration data
          analysis realization plusBase minusBase hBase hCenter measure)
        physical
        (programPT12StrongCompletedMatterLLInclusion
          (configuration := configuration) (data := data) (analysis := analysis)
            period hPeriod state) = 0 := by
  let riesz := globalCandidateASevenPhysicalCommonRieszOperator period
    hPeriod configuration data analysis
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure)
    (strongMatterLLSameActionBridge period hPeriod configuration data analysis
      realization plusBase minusBase hBase hCenter measure)
    physical
  let inclusion := programPT12StrongCompletedMatterLLInclusion
    (configuration := configuration) (data := data) (analysis := analysis)
      period hPeriod
  have hAll : (fun value => riesz (inclusion value)) =
      (fun _ => (0 : CommonAugmentedHilbert period hPeriod configuration data
        analysis)) := by
    apply (programPT12StrongMatterFullLLSmoothToCompleted_denseRange
      (configuration := configuration) (data := data) period hPeriod
        analysis).equalizer
    · exact riesz.continuous.comp inclusion.continuous
    · exact continuous_const
    · funext direction
      change riesz
          (inclusion
            (programPT12StrongMatterFullLLSmoothToCompleted
              (configuration := configuration) (data := data) period hPeriod
                analysis direction)) = 0
      rw [completedInclusion_smooth_eq_core period hPeriod configuration data
        analysis direction]
      exact strongPhysicalRiesz_matterFullLLSmoothSlice_zero period hPeriod
        configuration data analysis realization plusBase minusBase hBase
          hCenter physical direction
  exact congrFun hAll state


end

end
end P0EFTJanusProgramPT12StrongCompletedMatterLLPhysicalRieszZero4D
end JanusFormal
