import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientMatterLLFactor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientPhysicalRiesz4D

/-! The actual bounded matter--LL graph Riesz on its auxiliary/measure quotient. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12ReducedMatterLLGraphRiesz4D
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

open P0EFTJanusProgramPT12JointQuotientMatterLLFactor4D
open P0EFTJanusProgramPT12JointQuotientPhysicalRiesz4D
open P0EFTJanusProgramPT12JointQuotientAbelianColumn4D

private def actualGraphRiesz : CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
    CommonAugmentedHilbert period hPeriod configuration data analysis := by
  unfold CommonAugmentedHilbert
  exact diagonalExtendedBulkL2RieszOperator period hPeriod
    (globalCandidateAMetricBySector period hPeriod data) couplings.matterMassSquared data analysis

/-- Compression of the existing graph Riesz; it is independent of the physical extension. -/
def actualMatterLLGraphRiesz : ActualMatterLLHilbert period hPeriod configuration data analysis →L[Real]
    ActualMatterLLHilbert period hPeriod configuration data analysis :=
  (actualMatterLLReadout period hPeriod configuration data analysis).comp
    ((actualGraphRiesz period hPeriod configuration data analysis).comp
      (actualMatterLLInclusion period hPeriod configuration data analysis).toContinuousLinearMap)

private theorem compression_pairing
    (first second : ActualMatterLLHilbert period hPeriod configuration data analysis) :
    inner Real (actualMatterLLGraphRiesz period hPeriod configuration data analysis first) second =
    inner Real (actualGraphRiesz period hPeriod configuration data analysis
      (actualMatterLLInclusion period hPeriod configuration data analysis first))
      (actualMatterLLInclusion period hPeriod configuration data analysis second) := by
  calc
    _ = inner Real second (actualMatterLLReadout period hPeriod configuration data analysis
      (actualGraphRiesz period hPeriod configuration data analysis
        (actualMatterLLInclusion period hPeriod configuration data analysis first))) := real_inner_comm _ _
    _ = inner Real (actualMatterLLInclusion period hPeriod configuration data analysis second)
      (actualGraphRiesz period hPeriod configuration data analysis
        (actualMatterLLInclusion period hPeriod configuration data analysis first)) :=
      (actualMatterLLInclusion_inner period hPeriod configuration data analysis second _).symm
    _ = _ := real_inner_comm _ _

private theorem graphRiesz_matterLL_pairing
    (first : ActualMatterLLHilbert period hPeriod configuration data analysis)
    (test : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    inner Real (actualGraphRiesz period hPeriod configuration data analysis
      (actualMatterLLInclusion period hPeriod configuration data analysis first)) test =
    programPPrimitiveSpinCMatterGraphForm period hPeriod couplings.matterMassSquared
      (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod couplings.matterMassSquared first.fst)
      (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod couplings.matterMassSquared test.snd.snd.fst) +
    globalCandidateAFullLLGraphForm period hPeriod data analysis first.snd test.snd.snd.snd := by
  have h := diagonalExtendedBulkL2RieszOperator_pairing period hPeriod
    (globalCandidateAMetricBySector period hPeriod data) couplings.matterMassSquared data analysis
    (actualMatterLLInclusion period hPeriod configuration data analysis first) test
  rw [diagonalExtendedBulkL2Hessian_apply, diagonalExtendedBulkHessian_apply] at h
  change inner Real (actualGraphRiesz period hPeriod configuration data analysis
      (actualMatterLLInclusion period hPeriod configuration data analysis first)) test =
    globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod couplings
      (globalCandidateAMetricBySector period hPeriod data) 0 test.fst +
    globalPairedAbelianOffShellHessian period hPeriod (globalCandidateAMetricBySector period hPeriod data) 0 test.snd.fst +
    programPPrimitiveSpinCMatterGraphForm period hPeriod couplings.matterMassSquared
      (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod couplings.matterMassSquared first.fst)
      (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod couplings.matterMassSquared test.snd.snd.fst) +
    globalCandidateAFullLLGraphForm period hPeriod data analysis first.snd test.snd.snd.snd at h
  simp only [map_zero, zero_apply, zero_add] at h
  exact h

theorem actualMatterLLGraphRiesz_pairing
    (first second : ActualMatterLLHilbert period hPeriod configuration data analysis) :
    inner Real (actualMatterLLGraphRiesz period hPeriod configuration data analysis first) second =
    programPPrimitiveSpinCMatterGraphForm period hPeriod couplings.matterMassSquared
      (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod couplings.matterMassSquared first.fst)
      (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod couplings.matterMassSquared second.fst) +
    globalCandidateAFullLLGraphForm period hPeriod data analysis first.snd second.snd :=
  (compression_pairing period hPeriod configuration data analysis first second).trans
    (graphRiesz_matterLL_pairing period hPeriod configuration data analysis first _)

theorem actualMatterLLGraphRiesz_isSelfAdjoint : IsSelfAdjoint
    (actualMatterLLGraphRiesz period hPeriod configuration data analysis) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro first second
  calc
    _ = inner Real (actualGraphRiesz period hPeriod configuration data analysis
      (actualMatterLLInclusion period hPeriod configuration data analysis first))
      (actualMatterLLInclusion period hPeriod configuration data analysis second) :=
      compression_pairing period hPeriod configuration data analysis first second
    _ = inner Real (actualMatterLLInclusion period hPeriod configuration data analysis first)
      (actualGraphRiesz period hPeriod configuration data analysis
        (actualMatterLLInclusion period hPeriod configuration data analysis second)) :=
      (diagonalExtendedBulkL2RieszOperator_isSelfAdjoint period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) couplings.matterMassSquared data analysis).isSymmetric _ _
    _ = _ := actualMatterLLInclusion_inner period hPeriod configuration data analysis first _

private theorem graphRiesz_matterLL_column
    (vector : ActualMatterLLHilbert period hPeriod configuration data analysis) :
    actualGraphRiesz period hPeriod configuration data analysis
      (actualMatterLLInclusion period hPeriod configuration data analysis vector) =
    actualMatterLLInclusion period hPeriod configuration data analysis
      (actualMatterLLGraphRiesz period hPeriod configuration data analysis vector) := by
  apply ext_inner_right Real
  intro test
  exact (graphRiesz_matterLL_pairing period hPeriod configuration data analysis vector test).trans
    ((actualMatterLLGraphRiesz_pairing period hPeriod configuration data analysis vector
      (actualMatterLLReadout period hPeriod configuration data analysis test)).symm.trans
      (actualMatterLLInclusion_inner period hPeriod configuration data analysis _ test).symm)
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



theorem actualMatterLL_augmented_column
    (vector : ActualMatterLLHilbert period hPeriod configuration data analysis) :
    strongAugmentedRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (actualMatterLLInclusion period hPeriod configuration data analysis vector) =
    actualMatterLLInclusion period hPeriod configuration data analysis
      (actualMatterLLGraphRiesz period hPeriod configuration data analysis vector) := by
  change actualGraphRiesz period hPeriod configuration data analysis
      (actualMatterLLInclusion period hPeriod configuration data analysis vector) +
    strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (actualMatterLLInclusion period hPeriod configuration data analysis vector) = _
  have hZeroPhysical : strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (actualMatterLLInclusion period hPeriod configuration data analysis vector) = 0 :=
    strongPhysicalRiesz_completedMatterLL_zero period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical vector
  rw [hZeroPhysical, add_zero]
  exact graphRiesz_matterLL_column period hPeriod configuration data analysis vector

include realization plusBase minusBase hBase hCenter physical hZero in
theorem matterLLAuxNull_le_graphRiesz_kernel :
    matterLLAuxNullSpace period hPeriod configuration data analysis ≤
      (actualMatterLLGraphRiesz period hPeriod configuration data analysis).ker := by
  apply Submodule.topologicalClosure_minimal
  · rintro vector ⟨aux, rfl⟩
    have h := actualAuxLL_riesz_zero period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero aux
    rw [← actualMatterLLInclusion_aux, actualMatterLL_augmented_column] at h
    apply (actualMatterLLInclusion period hPeriod configuration data analysis).injective
    exact h.trans (map_zero _).symm
  · exact ContinuousLinearMap.isClosed_ker _

def reducedMatterLLGraphRiesz : ReducedMatterLLHilbert period hPeriod configuration data analysis →L[Real]
    ReducedMatterLLHilbert period hPeriod configuration data analysis :=
  closedNullQuotientOperator (actualMatterLLGraphRiesz period hPeriod configuration data analysis)
    (matterLLAuxNullSpace period hPeriod configuration data analysis)
    (matterLLAuxNull_le_graphRiesz_kernel period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero)

theorem reducedMatterLLGraphRiesz_isSelfAdjoint : IsSelfAdjoint
    (reducedMatterLLGraphRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero) :=
  closedNullQuotientOperator_isSelfAdjoint _
    (actualMatterLLGraphRiesz_isSelfAdjoint period hPeriod configuration data analysis) _ _

theorem reducedMatterLLGraphRiesz_pairing
    (first second : ActualMatterLLHilbert period hPeriod configuration data analysis) :
    inner Real (reducedMatterLLGraphRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero
      ((matterLLAuxNullSpace period hPeriod configuration data analysis).mkQ first))
      ((matterLLAuxNullSpace period hPeriod configuration data analysis).mkQ second) =
    inner Real (actualMatterLLGraphRiesz period hPeriod configuration data analysis first) second :=
  closedNullQuotientOperator_pairing _
    (actualMatterLLGraphRiesz_isSelfAdjoint period hPeriod configuration data analysis) _ _ first second

theorem quotientMatterLL_augmented_column
    (vector : ReducedMatterLLHilbert period hPeriod configuration data analysis) :
    jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter
      physical hZero hMetric hWeights (quotientMatterLLInclusion period hPeriod configuration data analysis vector) =
    quotientMatterLLInclusion period hPeriod configuration data analysis
      (reducedMatterLLGraphRiesz period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical hZero vector) := by
  obtain ⟨vector, rfl⟩ := (matterLLAuxNullSpace period hPeriod configuration data analysis).mkQ_surjective vector
  exact congrArg (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
    (actualMatterLL_augmented_column period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical vector)

theorem quotientPhysicalRiesz_matterLL_zero
    (vector : ReducedMatterLLHilbert period hPeriod configuration data analysis) :
    quotientPhysicalRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical
      (quotientMatterLLInclusion period hPeriod configuration data analysis vector) = 0 := by
  obtain ⟨vector, rfl⟩ := (matterLLAuxNullSpace period hPeriod configuration data analysis).mkQ_surjective vector
  change (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
    (strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (actualMatterLLInclusion period hPeriod configuration data analysis vector)) = 0
  have h : strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (actualMatterLLInclusion period hPeriod configuration data analysis vector) = 0 :=
    strongPhysicalRiesz_completedMatterLL_zero period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical vector
  rw [h, map_zero]

end
end
end P0EFTJanusProgramPT12ReducedMatterLLGraphRiesz4D
end JanusFormal
