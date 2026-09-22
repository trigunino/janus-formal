import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianMixedAugmented4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientDiffeomorphismColumn4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CoupledBRSTOperator4D

/-! Joint actual diffeomorphism and mixed abelian BRST, with the full physical coupling. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateACoupledBRST4D
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

abbrev CandidateACoupledBRSTHilbert := WithLp 2
  (ActualDiffeomorphismHilbert period hPeriod configuration data × CandidateAAbelianMixedHilbert period hPeriod data)

def candidateACoupledBRSTOperator : CandidateACoupledBRSTHilbert period hPeriod configuration data →ₗ.[Real]
    CandidateACoupledBRSTHilbert period hPeriod configuration data :=
  coupledBRSTOperator
    (diagonalDiffeomorphismSignedRiesz period hPeriod couplings (globalCandidateAMetricBySector period hPeriod data))
    (candidateAAbelianMixedOperator period hPeriod data)
    (actualDiffeomorphismInclusion period hPeriod configuration data analysis).toContinuousLinearMap
    (candidateAAbelianMixedPhysicalLift period hPeriod configuration data analysis)
    (strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)

theorem candidateACoupledBRSTOperator_selfAdjoint : IsSelfAdjoint
    (candidateACoupledBRSTOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) :=
  coupledBRSTOperator_selfAdjoint _ _ _ _ _
    (actualDiffeomorphismSignedRiesz_isSelfAdjoint period hPeriod configuration data)
    (candidateAAbelianMixedOperator_selfAdjoint period hPeriod data)
    (strongPhysicalRiesz_isSelfAdjoint period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)

theorem candidateACoupledBRSTOperator_domain_iff
    (x : CandidateACoupledBRSTHilbert period hPeriod configuration data) :
    x ∈ (candidateACoupledBRSTOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).domain ↔
      x.snd ∈ (candidateAAbelianMixedOperator period hPeriod data).domain :=
  coupledBRSTOperator_domain_iff _ _ _ _ _ x

def candidateACoupledBRSTPhysicalLift : CandidateACoupledBRSTHilbert period hPeriod configuration data →L[Real]
    CommonAugmentedHilbert period hPeriod configuration data analysis :=
  coupledPhysicalLift (actualDiffeomorphismInclusion period hPeriod configuration data analysis).toContinuousLinearMap
    (candidateAAbelianMixedPhysicalLift period hPeriod configuration data analysis)

/-- All output sectors of H11 are retained separately from the internal coupled operator. -/
def candidateACoupledBRSTPhysicalColumn : CandidateACoupledBRSTHilbert period hPeriod configuration data →L[Real]
    CommonAugmentedHilbert period hPeriod configuration data analysis :=
  (strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical).comp
    (candidateACoupledBRSTPhysicalLift period hPeriod configuration data analysis)

def candidateACoupledBRSTState (d : ActualDiffeomorphismHilbert period hPeriod configuration data)
    (a : GlobalPairedAbelianBRSTState period hPeriod) : CandidateACoupledBRSTHilbert period hPeriod configuration data :=
  WithLp.toLp 2 (d, candidateAAbelianMixedSmooth period hPeriod data a)

def candidateACoupledBRSTOriginal (d : ActualDiffeomorphismHilbert period hPeriod configuration data)
    (a : GlobalPairedAbelianBRSTState period hPeriod) : CommonAugmentedHilbert period hPeriod configuration data analysis :=
  actualDiffeomorphismInclusion period hPeriod configuration data analysis d +
    actualAbelianInclusion period hPeriod configuration data analysis
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (globalCandidateAMetricBySector period hPeriod data) a)

theorem candidateACoupledBRSTState_mem (d : ActualDiffeomorphismHilbert period hPeriod configuration data)
    (a : GlobalPairedAbelianBRSTState period hPeriod) :
    candidateACoupledBRSTState period hPeriod configuration data d a ∈
      (candidateACoupledBRSTOperator period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical).domain := by
  rw [candidateACoupledBRSTOperator_domain_iff]
  exact candidateAAbelianMixedSmooth_mem period hPeriod data a

theorem candidateACoupledBRSTPhysicalColumn_state
    (d : ActualDiffeomorphismHilbert period hPeriod configuration data)
    (a : GlobalPairedAbelianBRSTState period hPeriod) :
    candidateACoupledBRSTPhysicalColumn period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical (candidateACoupledBRSTState period hPeriod configuration data d a) =
    strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical (candidateACoupledBRSTOriginal period hPeriod configuration data analysis d a) := by
  change strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical
    (actualDiffeomorphismInclusion period hPeriod configuration data analysis d +
      candidateAAbelianMixedPhysicalLift period hPeriod configuration data analysis
        (candidateAAbelianMixedSmooth period hPeriod data a)) = _
  rw [candidateACoupledBRSTOriginal, map_add, map_add]
  congr 1
  exact candidateAAbelianMixedPhysicalColumn_smooth period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical a

end
end
end P0EFTJanusProgramPT12CandidateACoupledBRST4D
end JanusFormal
