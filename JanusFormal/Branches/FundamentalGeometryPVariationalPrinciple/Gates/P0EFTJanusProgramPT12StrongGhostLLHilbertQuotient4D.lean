import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongGhostLLNullSpace4D

/-! A single actual Hilbert quotient for the closed ghost/antighost and
LL auxiliary/measure null directions, retaining the full augmented pairing. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongGhostLLHilbertQuotient4D

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

abbrev JointGhostLLQuotient := CommonAugmentedHilbert period hPeriod configuration data analysis ⧸
  jointGhostLLNullSpace period hPeriod configuration data analysis

def jointGhostLLCoreMap : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis →ₗ[Real]
    JointGhostLLQuotient period hPeriod configuration data analysis :=
  (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ.comp
    (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) couplings.matterMassSquared data analysis)

theorem jointGhostLLCoreMap_denseRange : DenseRange (jointGhostLLCoreMap period hPeriod configuration data analysis) :=
  (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ_surjective.denseRange.comp
    (diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) couplings.matterMassSquared data analysis)
    (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQL.continuous

theorem jointGhostLLCoreMap_auxLL_zero (aux : GlobalLLAuxMeasureSmooth period hPeriod) :
    jointGhostLLCoreMap period hPeriod configuration data analysis
      (auxLLCore period hPeriod configuration analysis aux) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply Submodule.le_topologicalClosure
  exact (show closedAuxLLSubspace period hPeriod configuration data analysis ≤
    closedAuxLLSubspace period hPeriod configuration data analysis ⊔
      closedGhostSubspace period hPeriod configuration data analysis from le_sup_left)
        (Submodule.le_topologicalClosure _ ⟨aux, rfl⟩)

theorem jointGhostLLCoreMap_ghostPair_zero (pair : SharedGhostPair period hPeriod) :
    jointGhostLLCoreMap period hPeriod configuration data analysis
      (ghostPairCoreMap period hPeriod configuration analysis pair) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply Submodule.le_topologicalClosure
  exact (show closedGhostSubspace period hPeriod configuration data analysis ≤
    closedAuxLLSubspace period hPeriod configuration data analysis ⊔
      closedGhostSubspace period hPeriod configuration data analysis from le_sup_right)
        (Submodule.le_topologicalClosure _ ⟨pair, rfl⟩)

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


def jointGhostLLRiesz : JointGhostLLQuotient period hPeriod configuration data analysis →L[Real]
    JointGhostLLQuotient period hPeriod configuration data analysis :=
  closedNullQuotientOperator
    (strongAugmentedRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)
    (jointGhostLLNullSpace period hPeriod configuration data analysis)
    (jointGhostLLNullSpace_le_kernel period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero hMetric hWeights)

private theorem strongRiesz_selfAdjoint : IsSelfAdjoint
    (strongAugmentedRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) :=
  globalCandidateACommonAugmentedRieszOperator_isSelfAdjoint period hPeriod configuration data analysis
    (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
    (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter)
    physical

theorem jointGhostLLRiesz_mk (vector : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter
      physical hZero hMetric hWeights ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ vector) =
      (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
        (strongAugmentedRiesz (measure := measure) period hPeriod configuration data analysis realization
          plusBase minusBase hBase hCenter physical vector) := rfl

theorem jointGhostLLRiesz_isSelfAdjoint : IsSelfAdjoint
    (jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter
      physical hZero hMetric hWeights) :=
  closedNullQuotientOperator_isSelfAdjoint _
    (strongRiesz_selfAdjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical) _ _

theorem jointGhostLLRiesz_pairing (first second : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    inner Real
      (jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter
        physical hZero hMetric hWeights ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ first))
      ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ second) =
      inner Real (strongAugmentedRiesz (measure := measure) period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical first) second :=
  closedNullQuotientOperator_pairing _
    (strongRiesz_selfAdjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical) _ _ first second

theorem jointGhostLLRiesz_kernel :
    (jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter
      physical hZero hMetric hWeights).ker =
      (strongAugmentedRiesz (measure := measure) period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical).ker.map
          (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ :=
  closedNullQuotientOperator_kernel _
    (strongRiesz_selfAdjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical) _ _

/-- The entire augmented smooth pairing survives the simultaneous reduction. -/
theorem jointGhostLLRiesz_smooth_pairing
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    inner Real
      (jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter
        physical hZero hMetric hWeights (jointGhostLLCoreMap period hPeriod configuration data analysis first))
      (jointGhostLLCoreMap period hPeriod configuration data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period hPeriod configuration data analysis
        (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
        (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter).chartBridge
        first second := by
  have hPair := jointGhostLLRiesz_pairing period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical hZero hMetric hWeights
    (diagonalExtendedBulkL2SmoothEmbedding period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis first)
    (diagonalExtendedBulkL2SmoothEmbedding period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis second)
  refine hPair.trans ?_
  exact (globalCandidateACommonAugmentedRieszOperator_pairing period hPeriod configuration data analysis
    (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
    (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter)
    physical _ _).trans
      (globalCandidateACommonAugmentedHessian_smooth_eq_gaugeFixed period hPeriod configuration data analysis
        (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
        (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter)
        physical first second)

/-- The LL column still agrees with quotient Friedrichs after removing both null sectors. -/
theorem jointGhostLLRiesz_fullLL_column
    (direction : GlobalFullLLSmooth period hPeriod analysis)
    (test : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    inner Real
      (jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter
        physical hZero hMetric hWeights (jointGhostLLCoreMap period hPeriod configuration data analysis
          (fullLLCore period hPeriod configuration analysis direction)))
      (jointGhostLLCoreMap period hPeriod configuration data analysis test) =
      inner Real (quotientLLFriedrichs period hPeriod analysis
        (quotientLLFriedrichsSmoothDomainElement period hPeriod analysis direction))
        (fullLLReducedHilbertCore period hPeriod analysis test.2.2.2) :=
  (jointGhostLLRiesz_pairing period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter
    physical hZero hMetric hWeights _ _).trans
      (strong_fullLL_augmented_pairing_eq_quotient period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical hZero direction test)

end
end
end P0EFTJanusProgramPT12StrongGhostLLHilbertQuotient4D
end JanusFormal
