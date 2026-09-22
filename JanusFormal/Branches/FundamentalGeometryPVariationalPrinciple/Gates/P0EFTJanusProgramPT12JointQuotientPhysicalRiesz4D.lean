import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientAbelianColumn4D

/-! The full seven-block physical Riesz descends independently through the joint null quotient. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12JointQuotientPhysicalRiesz4D
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

theorem actualGhost_physicalRiesz_zero (pair : SharedGhostPair period hPeriod) :
    strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (actualGhostEmbedding period hPeriod configuration data analysis pair) = 0 := by
  apply physicalRiesz_core_zero_of_hessian_column_zero period hPeriod configuration data analysis
    (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
    (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter)
    physical (ghostPairCoreMap period hPeriod configuration analysis pair)
  intro test
  unfold diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore
  have hTangent := diagonalExtendedBulkMinimalPhysicalTangent_pureDiffeomorphismNonminimal_eq_zero
    period hPeriod configuration data analysis (diagonalGhostPairState period hPeriod pair).nonminimal
  change diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
    (ghostPairCoreMap period hPeriod configuration analysis pair) = 0 at hTangent
  rw [hTangent]
  simp

/-- This physical cancellation needs no zero-flux or Einstein-weight cancellation hypothesis. -/
theorem jointNull_le_physicalRiesz_kernel :
    jointGhostLLNullSpace period hPeriod configuration data analysis ≤
      (strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical).ker := by
  apply Submodule.topologicalClosure_minimal
  · apply sup_le
    · apply Submodule.topologicalClosure_minimal
      · rintro vector ⟨aux, rfl⟩
        exact strongPhysicalRiesz_matterFullLLSmoothSlice_zero period hPeriod configuration data analysis
          realization plusBase minusBase hBase hCenter physical (0, (aux, 0))
      · exact ContinuousLinearMap.isClosed_ker _
    · apply Submodule.topologicalClosure_minimal
      · rintro vector ⟨pair, rfl⟩
        exact actualGhost_physicalRiesz_zero period hPeriod configuration data analysis realization
          plusBase minusBase hBase hCenter physical pair
      · exact ContinuousLinearMap.isClosed_ker _
  · exact ContinuousLinearMap.isClosed_ker _

theorem strongPhysicalRiesz_isSelfAdjoint : IsSelfAdjoint
    (strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro first second
  calc
    _ = physical.form first second := globalCandidateASevenPhysicalCommonRieszOperator_pairing
      period hPeriod configuration data analysis
      (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
      (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter)
      physical first second
    _ = physical.form second first := physical.symmetric first second
    _ = inner Real (strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical second) first :=
      (globalCandidateASevenPhysicalCommonRieszOperator_pairing period hPeriod configuration data analysis
        (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
        (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter)
        physical second first).symm
    _ = _ := real_inner_comm _ _

def quotientPhysicalRiesz : JointGhostLLQuotient period hPeriod configuration data analysis →L[Real]
    JointGhostLLQuotient period hPeriod configuration data analysis :=
  closedNullQuotientOperator
    (strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)
    (jointGhostLLNullSpace period hPeriod configuration data analysis)
    (jointNull_le_physicalRiesz_kernel period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)

@[simp] theorem quotientPhysicalRiesz_mk
    (vector : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    quotientPhysicalRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical
      ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ vector) =
    (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
      (strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical vector) := rfl

theorem quotientPhysicalRiesz_isSelfAdjoint : IsSelfAdjoint
    (quotientPhysicalRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical) :=
  closedNullQuotientOperator_isSelfAdjoint _
    (strongPhysicalRiesz_isSelfAdjoint period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) _ _

theorem quotientPhysicalRiesz_pairing
    (first second : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    inner Real
      (quotientPhysicalRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical
        ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ first))
      ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ second) =
    physical.form first second :=
  (closedNullQuotientOperator_pairing _
    (strongPhysicalRiesz_isSelfAdjoint period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) _ _ first second).trans
    (globalCandidateASevenPhysicalCommonRieszOperator_pairing period hPeriod configuration data analysis
      (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
      (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter)
      physical first second)

theorem quotientPhysicalRiesz_smooth_pairing
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    inner Real
      (quotientPhysicalRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical
        (jointGhostLLCoreMap period hPeriod configuration data analysis first))
      (jointGhostLLCoreMap period hPeriod configuration data analysis second) =
    diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod configuration data analysis
      (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
      (strongBridge (measure := measure) period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter).chartBridge first second :=
  (quotientPhysicalRiesz_pairing period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical _ _).trans (physical.smooth_agreement first second)

end
end
end P0EFTJanusProgramPT12JointQuotientPhysicalRiesz4D
end JanusFormal
