import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientAbelianColumn4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianBRSTNegativePhysicalColumn4D

/-! The reduced Abelian column realizes the original smooth BRST and H11 actions. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12JointQuotientAbelianSmoothPairing4D
set_option autoImplicit false
set_option maxRecDepth 4000
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

open P0EFTJanusProgramPT12StrongFullLLQuotientColumn4D
open P0EFTJanusProgramPGlobalLLAuxMeasureGraphRiesz4D
open P0EFTJanusProgramPT12LLFullJacobiZeroFluxKernel4D
open P0EFTJanusProgramPT12DiagonalGhostHilbertQuotient4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D

open P0EFTJanusProgramPT12StrongGhostLLNullSpace4D
open P0EFTJanusProgramPT12ClosedNullQuotient4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D

open P0EFTJanusProgramPT12StrongGhostLLHilbertQuotient4D
open P0EFTJanusProgramPT12JointQuotientAbelianFactor4D
open P0EFTJanusProgramPT12SignedBRSTAugmentedPairing4D
open P0EFTJanusProgramPT12AbelianSignedBRSTRealization4D
open P0EFTJanusProgramPT12DiffeomorphismSignedBRSTRealization4D
open P0EFTJanusProgramPT12JointQuotientAbelianColumn4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPT12AbelianBRSTNegativeDirection4D
open P0EFTJanusProgramPT12AbelianBRSTNegativePhysicalColumn4D

local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.canonicalLorentzVolumeFinite period hPeriod

def abelianCore : GlobalPairedAbelianBRSTState period hPeriod →ₗ[Real]
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis :=
  (LinearMap.inr Real _ _).comp (LinearMap.inl Real _ _)

theorem actualAbelianInclusion_smooth (vector : GlobalPairedAbelianBRSTState period hPeriod) :
    actualAbelianInclusion period hPeriod configuration data analysis
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) vector) =
    diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) couplings.matterMassSquared data analysis
      (abelianCore period hPeriod configuration analysis vector) := by
  change WithLp.toLp 2 (0, WithLp.toLp 2 (_, 0)) =
    WithLp.toLp 2
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) 0,
      WithLp.toLp 2 (_, WithLp.toLp 2
        ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod couplings.matterMassSquared).symm
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod couplings.matterMassSquared 0),
        globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis 0)))
  simp only [map_zero]
  rfl

theorem quotientAbelianInclusion_smooth (vector : GlobalPairedAbelianBRSTState period hPeriod) :
    quotientAbelianInclusion period hPeriod configuration data analysis
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) vector) =
    jointGhostLLCoreMap period hPeriod configuration data analysis
      (abelianCore period hPeriod configuration analysis vector) :=
  congrArg (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
    (actualAbelianInclusion_smooth period hPeriod configuration data analysis vector)
variable [IsFiniteMeasure measure]
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
  period hPeriod plusBase minusBase)
variable (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
  period hPeriod configuration.physical plusBase minusBase hBase)

variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
  period hPeriod configuration data analysis
  (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
  (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter))

variable (hZero : (data.boundary.llFields period hPeriod).llField = 0)

variable (hMetric : globalCandidateAMetricBySector period hPeriod data .plus =
  globalCandidateAMetricBySector period hPeriod data .minus)
variable (hWeights : candidateAPlusEinsteinKineticWeight couplings + candidateAMinusEinsteinKineticWeight couplings = 0)



include hZero hMetric hWeights in
/-- The physical term is exactly H11, with arbitrary smooth tests in every sector. -/
theorem quotientAbelianPhysicalColumn_smooth_pairing
    (vector : GlobalPairedAbelianBRSTState period hPeriod)
    (test : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    inner Real (quotientAbelianPhysicalColumn period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) vector))
      (jointGhostLLCoreMap period hPeriod configuration data analysis test) =
    diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod configuration data analysis
      (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
      (strongBridge (measure := measure) period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter).chartBridge
      (abelianCore period hPeriod configuration analysis vector) test := by
  have h := quotientAbelianPhysicalColumn_pairing period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical hZero hMetric hWeights
    (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) vector)
    (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) couplings.matterMassSquared data analysis test)
  rw [actualAbelianInclusion_smooth] at h
  exact h.trans (physical.smooth_agreement _ _)

theorem quotientAbelian_smooth_pairing
    (vector : GlobalPairedAbelianBRSTState period hPeriod)
    (test : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    inner Real
      (jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter
        physical hZero hMetric hWeights (jointGhostLLCoreMap period hPeriod configuration data analysis
          (abelianCore period hPeriod configuration analysis vector)))
      (jointGhostLLCoreMap period hPeriod configuration data analysis test) =
    globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) vector test.2.1
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
    diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod configuration data analysis
      (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
      (strongBridge (measure := measure) period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter).chartBridge
      (abelianCore period hPeriod configuration analysis vector) test := by
  have h := quotientAbelian_augmented_pairing period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical hZero hMetric hWeights
    (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) vector)
    (jointGhostLLCoreMap period hPeriod configuration data analysis test)
  rw [quotientAbelianInclusion_smooth] at h
  exact h.trans (congrArg₂ (· + ·)
    (pairedAbelianSignedRiesz_smooth_pairing period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) vector test.2.1)
    (quotientAbelianPhysicalColumn_smooth_pairing period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero hMetric hWeights vector test))

/-- Removing the ghost and LL null directions leaves the negative B square intact. -/
theorem quotientAbelian_B_pairing_self (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    let state := jointGhostLLCoreMap period hPeriod configuration data analysis
      (pureAbelianNakanishiLautrupCore period hPeriod configuration analysis field)
    inner Real (jointGhostLLRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero hMetric hWeights state) state =
      -‖globalPairedGaugeLieL2LinearMap period hPeriod field‖ ^ 2 := by
  exact (jointGhostLLRiesz_pairing period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical hZero hMetric hWeights _ _).trans
      (pureAbelianNakanishiLautrupCore_augmented_pairing_self period hPeriod configuration data analysis
        (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
        (strongBridge (measure := measure) period hPeriod configuration data analysis realization
          plusBase minusBase hBase hCenter) physical field)

theorem quotientAbelian_B_pairing_self_neg
    (field : GlobalPairedGaugeLieSmooth period hPeriod) (hField : field ≠ 0) :
    let state := jointGhostLLCoreMap period hPeriod configuration data analysis
      (pureAbelianNakanishiLautrupCore period hPeriod configuration analysis field)
    inner Real (jointGhostLLRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero hMetric hWeights state) state < 0 := by
  dsimp only
  rw [quotientAbelian_B_pairing_self]
  have hValue : globalPairedGaugeLieL2LinearMap period hPeriod field ≠ 0 := by
    intro hZeroField
    apply hField
    apply globalPairedGaugeLieL2LinearMap_injective period hPeriod
    simpa only [map_zero] using hZeroField
  exact neg_neg_of_pos (sq_pos_of_pos ((norm_pos_iff).2 hValue))

end
end
end P0EFTJanusProgramPT12JointQuotientAbelianSmoothPairing4D
end JanusFormal
