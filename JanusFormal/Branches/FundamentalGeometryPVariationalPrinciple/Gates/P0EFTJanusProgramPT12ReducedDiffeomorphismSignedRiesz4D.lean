import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientDiffeomorphismFactor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismSignedBRSTRealization4D

/-! The actual signed diagonal BRST operator on its closed shared ghost quotient. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12ReducedDiffeomorphismSignedRiesz4D
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

attribute [local instance]
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismCompleteSpace

open P0EFTJanusProgramPT12JointQuotientDiffeomorphismFactor4D
open P0EFTJanusProgramPT12DiffeomorphismSignedBRSTRealization4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D

variable (hMetric : globalCandidateAMetricBySector period hPeriod data .plus =
  globalCandidateAMetricBySector period hPeriod data .minus)
variable (hWeights : candidateAPlusEinsteinKineticWeight couplings + candidateAMinusEinsteinKineticWeight couplings = 0)

include hMetric hWeights in
theorem diffeomorphismGhost_signedRiesz_zero (pair : SharedGhostPair period hPeriod) :
    diagonalDiffeomorphismSignedRiesz period hPeriod couplings
      (globalCandidateAMetricBySector period hPeriod data)
      (diffeomorphismGhostEmbedding period hPeriod configuration data pair) = 0 := by
  let state := diffeomorphismGhostEmbedding period hPeriod configuration data pair
  have hRow : (globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod couplings
      (globalCandidateAMetricBySector period hPeriod data) state : _ → Real) = fun _ => 0 := by
    apply (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_denseRange period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)).equalizer
      (globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod couplings
        (globalCandidateAMetricBySector period hPeriod data) state).continuous continuous_const
    funext test
    change globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod couplings
      (globalCandidateAMetricBySector period hPeriod data)
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) (diagonalGhostPairState period hPeriod pair))
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) test) = 0
    rw [globalCandidateADiagonalDiffeomorphismOffShellHessian_apply]
    simp only [globalCandidateADiagonalDiffeomorphismOffShellPlusProjection_smooth,
      globalCandidateADiagonalDiffeomorphismOffShellMinusProjection_smooth]
    simp [globalDiffeomorphismOffShellHessian_apply,
      globalCandidateADiagonalDiffeomorphismSectorStateLinearMap,
      diagonalGhostPairState, hMetric, ← add_mul, hWeights]
  apply ext_inner_right Real
  intro test
  rw [inner_zero_left]
  exact (diagonalDiffeomorphismSignedRiesz_pairing period hPeriod couplings
    (globalCandidateAMetricBySector period hPeriod data) state test).trans (congrFun hRow test)

include hMetric hWeights in
theorem diffeomorphismGhostNull_le_signedRiesz_kernel :
    diffeomorphismGhostNullSpace period hPeriod configuration data ≤
      (diagonalDiffeomorphismSignedRiesz period hPeriod couplings
        (globalCandidateAMetricBySector period hPeriod data)).ker := by
  apply Submodule.topologicalClosure_minimal
  · rintro vector ⟨pair, rfl⟩
    exact diffeomorphismGhost_signedRiesz_zero period hPeriod configuration data hMetric hWeights pair
  · exact ContinuousLinearMap.isClosed_ker _

theorem actualDiffeomorphismSignedRiesz_isSelfAdjoint : IsSelfAdjoint
    (diagonalDiffeomorphismSignedRiesz period hPeriod couplings
      (globalCandidateAMetricBySector period hPeriod data)) := by
  rw [diagonalDiffeomorphismSignedRiesz_eq_actual]
  exact LinearMap.IsSymmetric.isSelfAdjoint
    (globalCandidateADiagonalDiffeomorphismOffShellRieszOperator_symmetric period hPeriod couplings
      (globalCandidateAMetricBySector period hPeriod data))

def reducedDiffeomorphismSignedRiesz : ReducedDiffeomorphismHilbert period hPeriod configuration data →L[Real]
    ReducedDiffeomorphismHilbert period hPeriod configuration data :=
  closedNullQuotientOperator
    (diagonalDiffeomorphismSignedRiesz period hPeriod couplings (globalCandidateAMetricBySector period hPeriod data))
    (diffeomorphismGhostNullSpace period hPeriod configuration data)
    (diffeomorphismGhostNull_le_signedRiesz_kernel period hPeriod configuration data hMetric hWeights)

@[simp] theorem reducedDiffeomorphismSignedRiesz_mk
    (vector : ActualDiffeomorphismHilbert period hPeriod configuration data) :
    reducedDiffeomorphismSignedRiesz period hPeriod configuration data hMetric hWeights
      ((diffeomorphismGhostNullSpace period hPeriod configuration data).mkQ vector) =
    (diffeomorphismGhostNullSpace period hPeriod configuration data).mkQ
      (diagonalDiffeomorphismSignedRiesz period hPeriod couplings
        (globalCandidateAMetricBySector period hPeriod data) vector) := rfl

theorem reducedDiffeomorphismSignedRiesz_isSelfAdjoint : IsSelfAdjoint
    (reducedDiffeomorphismSignedRiesz period hPeriod configuration data hMetric hWeights) :=
  closedNullQuotientOperator_isSelfAdjoint _
    (actualDiffeomorphismSignedRiesz_isSelfAdjoint period hPeriod configuration data) _ _

theorem reducedDiffeomorphismSignedRiesz_pairing
    (first second : ActualDiffeomorphismHilbert period hPeriod configuration data) :
    inner Real (reducedDiffeomorphismSignedRiesz period hPeriod configuration data hMetric hWeights
      ((diffeomorphismGhostNullSpace period hPeriod configuration data).mkQ first))
      ((diffeomorphismGhostNullSpace period hPeriod configuration data).mkQ second) =
    inner Real (diagonalDiffeomorphismSignedRiesz period hPeriod couplings
      (globalCandidateAMetricBySector period hPeriod data) first) second :=
  closedNullQuotientOperator_pairing _
    (actualDiffeomorphismSignedRiesz_isSelfAdjoint period hPeriod configuration data) _ _ first second

theorem reducedDiffeomorphismSignedRiesz_kernel :
    (reducedDiffeomorphismSignedRiesz period hPeriod configuration data hMetric hWeights).ker =
      (diagonalDiffeomorphismSignedRiesz period hPeriod couplings
        (globalCandidateAMetricBySector period hPeriod data)).ker.map
        (diffeomorphismGhostNullSpace period hPeriod configuration data).mkQ :=
  closedNullQuotientOperator_kernel _
    (actualDiffeomorphismSignedRiesz_isSelfAdjoint period hPeriod configuration data) _ _

end
end
end P0EFTJanusProgramPT12ReducedDiffeomorphismSignedRiesz4D
end JanusFormal
