import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateACoupledBRSTSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianMixedMinimal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CoupledBRSTCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianMixedSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateACoupledBRST4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateACoupledBRSTMinimal4D
set_option autoImplicit false

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
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

open P0EFTJanusProgramPT12JointQuotientAbelianColumn4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D

open P0EFTJanusProgramPT12JointQuotientAbelianSmoothPairing4D
open P0EFTJanusProgramPT12AbelianLorenzGraphShear4D
open P0EFTJanusProgramPT12AbelianBRSTNegativePhysicalColumn4D
open P0EFTJanusProgramPT12JointQuotientPhysicalRiesz4D

open P0EFTJanusProgramPT12AbelianGhostSmoothRotation4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D

open P0EFTJanusProgramPT12CandidateAAbelianMixedOperator4D
open P0EFTJanusProgramPT12CandidateAAbelianMixedPotential4D
open P0EFTJanusProgramPT12AbelianPotentialGraphInclusion4D
open P0EFTJanusProgramPT12AbelianGhostRotationPhysical4D

open P0EFTJanusProgramPT12CandidateAAbelianMixedPhysical4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

local instance (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :=
  globalPairedAbelianLorenzGraphCompleteSpace period hPeriod metric

open P0EFTJanusProgramPT12JointQuotientDiffeomorphismFactor4D
open P0EFTJanusProgramPT12ReducedDiffeomorphismSignedRiesz4D
open P0EFTJanusProgramPT12CoupledBRSTOperator4D

attribute [local instance]
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismCompleteSpace

open P0EFTJanusProgramPT12CandidateACoupledBRST4D
open P0EFTJanusProgramPT12CandidateAAbelianMixedPairing4D
open P0EFTJanusProgramPT12JointQuotientDiffeomorphismColumn4D

open P0EFTJanusProgramPT12CandidateAAbelianMixedSmooth4D

open P0EFTJanusProgramPT12CandidateACoupledBRSTSmooth4D
open P0EFTJanusProgramPT12CandidateAAbelianMixedMinimal4D
open P0EFTJanusProgramPT12CoupledBRSTCore4D
open P0EFTJanusProgramPT12ProductCore4D
open P0EFTJanusProgramPT12ProductSelfAdjoint4D

/-- The simultaneous smooth range is the product of the two genuine field ranges. -/
theorem candidateACoupledBRSTSmooth_range :
    (candidateACoupledBRSTSmooth period hPeriod configuration data).range =
      productCore
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)).range
        (candidateAAbelianMixedSmoothLinearMap period hPeriod data).range := by
  ext x
  constructor
  · rintro ⟨pair, rfl⟩
    exact ⟨⟨pair.1, rfl⟩, ⟨pair.2, rfl⟩⟩
  · rintro ⟨⟨d, hd⟩, ⟨a, ha⟩⟩
    refine ⟨(d, a), ?_⟩
    apply WithLp.ofLp_injective 2
    exact Prod.ext hd ha

/-- The diffeomorphism factor is still on its existing graph Hilbert space. -/
theorem candidateADiffeomorphismSignedRiesz_hasCore :
    ((diagonalDiffeomorphismSignedRiesz period hPeriod couplings
      (globalCandidateAMetricBySector period hPeriod data)).toPMap ⊤).HasCore
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)).range :=
  bounded_range_hasCore _
    (bounded_toPMap_selfAdjoint _ (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (actualDiffeomorphismSignedRiesz_isSelfAdjoint period hPeriod configuration data))).isClosed _
    (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_denseRange period hPeriod _)

/-- Minimal coupled BRST closure, with all off-diagonal H11 blocks retained. -/
def candidateACoupledBRSTMinimal : CandidateACoupledBRSTHilbert period hPeriod configuration data →ₗ.[Real]
    CandidateACoupledBRSTHilbert period hPeriod configuration data :=
  coupledBRSTOperator
    (diagonalDiffeomorphismSignedRiesz period hPeriod couplings (globalCandidateAMetricBySector period hPeriod data))
    (candidateAAbelianMixedMinimal period hPeriod data)
    (actualDiffeomorphismInclusion period hPeriod configuration data analysis).toContinuousLinearMap
    (candidateAAbelianMixedPhysicalLift period hPeriod configuration data analysis)
    (strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)

theorem candidateACoupledBRSTMinimal_isClosed :
    (candidateACoupledBRSTMinimal period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).IsClosed :=
  coupledBRSTOperator_isClosed _ _ _ _ _
    (bounded_toPMap_selfAdjoint _ (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (actualDiffeomorphismSignedRiesz_isSelfAdjoint period hPeriod configuration data))).isClosed
    (candidateAAbelianMixedMinimal_isClosed period hPeriod data)

theorem candidateACoupledBRSTMinimal_hasCore :
    (candidateACoupledBRSTMinimal period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).HasCore
      (candidateACoupledBRSTSmooth period hPeriod configuration data).range := by
  rw [candidateACoupledBRSTSmooth_range]
  exact coupledBRSTOperator_hasCore _ _ _ _ _
    (bounded_toPMap_selfAdjoint _ (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (actualDiffeomorphismSignedRiesz_isSelfAdjoint period hPeriod configuration data))).isClosed
    (candidateAAbelianMixedMinimal_isClosed period hPeriod data) _ _
    (candidateADiffeomorphismSignedRiesz_hasCore period hPeriod configuration data)
    (candidateAAbelianMixedMinimal_hasCore period hPeriod data)

/-- Computed closure of the actual coupled restriction; no maximal-domain identification is assumed. -/
theorem candidateACoupledBRST_smoothClosure_eq_minimal :
    ((candidateACoupledBRSTOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).domRestrict
      (candidateACoupledBRSTSmooth period hPeriod configuration data).range).closure =
    candidateACoupledBRSTMinimal period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical := by
  rw [candidateACoupledBRSTSmooth_range]
  unfold candidateACoupledBRSTOperator
  rw [coupledBRSTOperator_restriction_closure _ _ _ _ _
    (bounded_toPMap_selfAdjoint _ (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (actualDiffeomorphismSignedRiesz_isSelfAdjoint period hPeriod configuration data))).isClosed
    (candidateAAbelianMixedOperator_selfAdjoint period hPeriod data).isClosed.isClosable _ _
    (candidateADiffeomorphismSignedRiesz_hasCore period hPeriod configuration data),
    candidateAAbelianMixed_smoothClosure_eq_minimal]
  rfl

end
end
end P0EFTJanusProgramPT12CandidateACoupledBRSTMinimal4D
end JanusFormal
