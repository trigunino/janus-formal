import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientAbelianFactor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SignedBRSTAugmentedPairing4D

/-! Exact signed Abelian column of the joint reduced operator, with its full H11 image. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12JointQuotientAbelianColumn4D
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



abbrev strongPhysicalRiesz := globalCandidateASevenPhysicalCommonRieszOperator
  period hPeriod configuration data analysis
  (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
  (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter)
  physical

/-- An arbitrary completed test sees the signed Abelian action and every H11 column. -/
theorem actualAbelian_augmented_pairing
    (vector : ActualAbelianHilbert period hPeriod configuration data)
    (test : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    inner Real (strongAugmentedRiesz (measure := measure) period hPeriod configuration data analysis
      realization plusBase minusBase hBase hCenter physical
      (actualAbelianInclusion period hPeriod configuration data analysis vector)) test =
    inner Real (pairedAbelianSignedRiesz period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) vector)
      (actualAbelianReadout period hPeriod configuration data analysis test) +
    physical.form (actualAbelianInclusion period hPeriod configuration data analysis vector) test := by
  have h := actualAugmented_pairing_eq_signedBRST_matterLL_physical period hPeriod
    configuration data analysis
    (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
    (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter)
    physical (actualAbelianInclusion period hPeriod configuration data analysis vector) test
  change inner Real (strongAugmentedRiesz (measure := measure) period hPeriod configuration data analysis
    realization plusBase minusBase hBase hCenter physical
    (actualAbelianInclusion period hPeriod configuration data analysis vector)) test =
      inner Real (diagonalDiffeomorphismSignedRiesz period hPeriod couplings
        (globalCandidateAMetricBySector period hPeriod data) 0) test.fst +
      inner Real (pairedAbelianSignedRiesz period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) vector) test.snd.fst +
      programPPrimitiveSpinCMatterGraphForm period hPeriod couplings.matterMassSquared
        (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod couplings.matterMassSquared 0)
        (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod couplings.matterMassSquared test.snd.snd.fst) +
      globalCandidateAFullLLGraphForm period hPeriod data analysis 0 test.snd.snd.snd +
      physical.form (actualAbelianInclusion period hPeriod configuration data analysis vector) test at h
  simp only [map_zero, inner_zero_left, zero_add, add_zero, zero_apply] at h
  exact h

/-- Vector equality retains H11 components in all sectors, including off-diagonal ones. -/
theorem actualAbelian_augmented_column
    (vector : ActualAbelianHilbert period hPeriod configuration data) :
    strongAugmentedRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (actualAbelianInclusion period hPeriod configuration data analysis vector) =
    actualAbelianInclusion period hPeriod configuration data analysis
      (pairedAbelianSignedRiesz period hPeriod (globalCandidateAMetricBySector period hPeriod data) vector) +
    strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (actualAbelianInclusion period hPeriod configuration data analysis vector) := by
  apply ext_inner_right Real
  intro test
  rw [inner_add_left, actualAbelianInclusion_inner]
  exact (actualAbelian_augmented_pairing period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical vector test).trans
      (congrArg (fun value => _ + value)
        (globalCandidateASevenPhysicalCommonRieszOperator_pairing period hPeriod configuration data analysis
          (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
          (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter)
          physical (actualAbelianInclusion period hPeriod configuration data analysis vector) test).symm)

/-- The entire physical column, mapped into the common reduced Hilbert space. -/
def quotientAbelianPhysicalColumn : ActualAbelianHilbert period hPeriod configuration data →L[Real]
    JointGhostLLQuotient period hPeriod configuration data analysis :=
  (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQL.comp
    ((strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).comp
        (actualAbelianInclusion period hPeriod configuration data analysis).toContinuousLinearMap)

theorem quotientAbelian_augmented_column
    (vector : ActualAbelianHilbert period hPeriod configuration data) :
    jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter
      physical hZero hMetric hWeights (quotientAbelianInclusion period hPeriod configuration data analysis vector) =
    quotientAbelianInclusion period hPeriod configuration data analysis
      (pairedAbelianSignedRiesz period hPeriod (globalCandidateAMetricBySector period hPeriod data) vector) +
    quotientAbelianPhysicalColumn period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical vector := by
  change (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
    (strongAugmentedRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (actualAbelianInclusion period hPeriod configuration data analysis vector)) = _
  rw [actualAbelian_augmented_column, map_add]
  rfl

/-- Exact pairing against every reduced test, with the physical column still explicit. -/
theorem quotientAbelian_augmented_pairing
    (vector : ActualAbelianHilbert period hPeriod configuration data)
    (test : JointGhostLLQuotient period hPeriod configuration data analysis) :
    inner Real
      (jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter
        physical hZero hMetric hWeights
        (quotientAbelianInclusion period hPeriod configuration data analysis vector)) test =
    inner Real (pairedAbelianSignedRiesz period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) vector)
      (quotientAbelianReadout period hPeriod configuration data analysis test) +
    inner Real (quotientAbelianPhysicalColumn period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical vector) test := by
  rw [quotientAbelian_augmented_column, inner_add_left, quotientAbelianInclusion_inner]

include hZero hMetric hWeights in
/-- Quotienting does not alter the physical action on any completed test. -/
theorem quotientAbelianPhysicalColumn_pairing
    (vector : ActualAbelianHilbert period hPeriod configuration data)
    (test : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    inner Real (quotientAbelianPhysicalColumn period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical vector)
      ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ test) =
    physical.form (actualAbelianInclusion period hPeriod configuration data analysis vector) test := by
  have hReduced := (jointGhostLLRiesz_pairing period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical hZero hMetric hWeights
    (actualAbelianInclusion period hPeriod configuration data analysis vector) test).trans
      (actualAbelian_augmented_pairing period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical vector test)
  have hColumn := quotientAbelian_augmented_pairing period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical hZero hMetric hWeights vector
    ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ test)
  change _ = inner Real (pairedAbelianSignedRiesz period hPeriod
    (globalCandidateAMetricBySector period hPeriod data) vector)
    (actualAbelianReadout period hPeriod configuration data analysis test) + _ at hColumn
  exact add_left_cancel (hColumn.symm.trans hReduced)

end
end
end P0EFTJanusProgramPT12JointQuotientAbelianColumn4D
end JanusFormal
