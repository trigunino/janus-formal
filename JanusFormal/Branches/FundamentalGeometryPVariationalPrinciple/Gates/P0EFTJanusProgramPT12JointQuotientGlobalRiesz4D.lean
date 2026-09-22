import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ThreeBlockHilbertAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientSectorDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ReducedMatterLLGraphRiesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientDiffeomorphismColumn4D

/-! Global actual reduced Riesz: three concrete diagonal blocks plus the same descended H11 operator. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12JointQuotientGlobalRiesz4D
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

variable (hZero : (data.boundary.llFields period hPeriod).llField = 0)

variable (hMetric : globalCandidateAMetricBySector period hPeriod data .plus =
  globalCandidateAMetricBySector period hPeriod data .minus)
variable (hWeights : candidateAPlusEinsteinKineticWeight couplings + candidateAMinusEinsteinKineticWeight couplings = 0)



open P0EFTJanusProgramPT12JointQuotientDiffeomorphismFactor4D
open P0EFTJanusProgramPT12ReducedDiffeomorphismSignedRiesz4D
open P0EFTJanusProgramPT12JointQuotientPhysicalRiesz4D
open P0EFTJanusProgramPT12JointQuotientAbelianColumn4D

attribute [local instance]
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismCompleteSpace

open P0EFTJanusProgramPT12JointQuotientMatterLLFactor4D
open P0EFTJanusProgramPT12ReducedMatterLLGraphRiesz4D
open P0EFTJanusProgramPT12JointQuotientSectorDecomposition4D
open P0EFTJanusProgramPT12JointQuotientDiffeomorphismColumn4D

open P0EFTJanusProgramPT12ThreeBlockHilbertAssembly4D

def reducedBlockRiesz : JointGhostLLQuotient period hPeriod configuration data analysis →L[Real]
    JointGhostLLQuotient period hPeriod configuration data analysis :=
  threeBlockOperator
    (quotientDiffeomorphismInclusion period hPeriod configuration data analysis).toContinuousLinearMap
    (quotientAbelianInclusion period hPeriod configuration data analysis).toContinuousLinearMap
    (quotientMatterLLInclusion period hPeriod configuration data analysis).toContinuousLinearMap
    (quotientDiffeomorphismReadout period hPeriod configuration data analysis)
    (quotientAbelianReadout period hPeriod configuration data analysis)
    (quotientMatterLLReadout period hPeriod configuration data analysis)
    (reducedDiffeomorphismSignedRiesz period hPeriod configuration data hMetric hWeights)
    (pairedAbelianSignedRiesz period hPeriod (globalCandidateAMetricBySector period hPeriod data))
    (reducedMatterLLGraphRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero)

/-- Equality on the whole reduced Hilbert space, not only on individual source columns. -/
theorem jointQuotientRiesz_eq_blocks_add_physical :
    jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical hZero hMetric hWeights = reducedBlockRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical hZero hMetric hWeights + quotientPhysicalRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical := by
  apply threeBlock_sum_eq (jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical hZero hMetric hWeights) (quotientPhysicalRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)
    (quotientDiffeomorphismInclusion period hPeriod configuration data analysis).toContinuousLinearMap
    (quotientAbelianInclusion period hPeriod configuration data analysis).toContinuousLinearMap
    (quotientMatterLLInclusion period hPeriod configuration data analysis).toContinuousLinearMap
    (quotientDiffeomorphismReadout period hPeriod configuration data analysis)
    (quotientAbelianReadout period hPeriod configuration data analysis)
    (quotientMatterLLReadout period hPeriod configuration data analysis)
    (reducedDiffeomorphismSignedRiesz period hPeriod configuration data hMetric hWeights)
    (pairedAbelianSignedRiesz period hPeriod (globalCandidateAMetricBySector period hPeriod data))
    (reducedMatterLLGraphRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero)
  · exact jointQuotient_reconstruct period hPeriod configuration data analysis
  · exact quotientDiffeomorphism_augmented_column period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero hMetric hWeights
  · intro vector
    have h := quotientAbelian_augmented_column period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero hMetric hWeights vector
    rw [quotientAbelianPhysicalColumn_eq_quotientPhysicalRiesz] at h
    exact h
  · exact quotientMatterLL_augmented_column period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero hMetric hWeights
  · exact quotientPhysicalRiesz_matterLL_zero period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical

theorem reducedBlockRiesz_isSelfAdjoint : IsSelfAdjoint (reducedBlockRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical hZero hMetric hWeights) := by
  have h : reducedBlockRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical hZero hMetric hWeights = jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical hZero hMetric hWeights - quotientPhysicalRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical := by
    apply eq_sub_iff_add_eq.mpr
    exact (jointQuotientRiesz_eq_blocks_add_physical period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero hMetric hWeights).symm
  rw [h]
  exact selfAdjoint_sub (jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical hZero hMetric hWeights) (quotientPhysicalRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)
    (jointGhostLLRiesz_isSelfAdjoint period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero hMetric hWeights)
    (quotientPhysicalRiesz_isSelfAdjoint period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)

/-- Exact global pairing of the three actual blocks and H11 on arbitrary reduced vectors. -/
theorem jointQuotientRiesz_pairing_decomposition
    (first second : JointGhostLLQuotient period hPeriod configuration data analysis) :
    inner Real ((jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical hZero hMetric hWeights) first) second =
    inner Real (reducedDiffeomorphismSignedRiesz period hPeriod configuration data hMetric hWeights
      (quotientDiffeomorphismReadout period hPeriod configuration data analysis first))
      (quotientDiffeomorphismReadout period hPeriod configuration data analysis second) +
    inner Real (pairedAbelianSignedRiesz period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      (quotientAbelianReadout period hPeriod configuration data analysis first))
      (quotientAbelianReadout period hPeriod configuration data analysis second) +
    inner Real (reducedMatterLLGraphRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero
      (quotientMatterLLReadout period hPeriod configuration data analysis first))
      (quotientMatterLLReadout period hPeriod configuration data analysis second) +
    inner Real ((quotientPhysicalRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical) first) second :=
  threeBlock_pairing (jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical hZero hMetric hWeights) (quotientPhysicalRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)
    (quotientDiffeomorphismInclusion period hPeriod configuration data analysis).toContinuousLinearMap
    (quotientAbelianInclusion period hPeriod configuration data analysis).toContinuousLinearMap
    (quotientMatterLLInclusion period hPeriod configuration data analysis).toContinuousLinearMap
    (quotientDiffeomorphismReadout period hPeriod configuration data analysis)
    (quotientAbelianReadout period hPeriod configuration data analysis)
    (quotientMatterLLReadout period hPeriod configuration data analysis)
    (reducedDiffeomorphismSignedRiesz period hPeriod configuration data hMetric hWeights)
    (pairedAbelianSignedRiesz period hPeriod (globalCandidateAMetricBySector period hPeriod data))
    (reducedMatterLLGraphRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero)
    (jointQuotientRiesz_eq_blocks_add_physical period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero hMetric hWeights)
    (quotientDiffeomorphismInclusion_inner period hPeriod configuration data analysis)
    (quotientAbelianInclusion_inner period hPeriod configuration data analysis)
    (quotientMatterLLInclusion_inner period hPeriod configuration data analysis) first second

/-- H11 depends only on the two BRST coordinates on the centered strong chart. -/
theorem quotientPhysicalRiesz_eq_on_BRST
    (vector : JointGhostLLQuotient period hPeriod configuration data analysis) :
    (quotientPhysicalRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical) vector =
    (quotientPhysicalRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)
      (quotientDiffeomorphismInclusion period hPeriod configuration data analysis
        (quotientDiffeomorphismReadout period hPeriod configuration data analysis vector) +
      quotientAbelianInclusion period hPeriod configuration data analysis
        (quotientAbelianReadout period hPeriod configuration data analysis vector)) := by
  have h := congrArg (quotientPhysicalRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)
    (jointQuotient_reconstruct period hPeriod configuration data analysis vector)
  rw [map_add, quotientPhysicalRiesz_matterLL_zero, add_zero] at h
  exact h.symm

end
end
end P0EFTJanusProgramPT12JointQuotientGlobalRiesz4D
end JanusFormal
