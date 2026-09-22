import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientDiffeomorphismColumn4D

/-! Dense actual diffeomorphism core, with the original BRST and full H11 pairings after reduction. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12JointQuotientDiffeomorphismSmoothPairing4D
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
open P0EFTJanusProgramPT12ReducedDiffeomorphismSignedRiesz4D
open P0EFTJanusProgramPT12DiffeomorphismSignedBRSTRealization4D
open P0EFTJanusProgramPT12JointQuotientPhysicalRiesz4D
open P0EFTJanusProgramPT12JointQuotientDiffeomorphismColumn4D

def diffeomorphismCore : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis := LinearMap.inl Real _ _

def reducedDiffeomorphismCoreMap : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
    ReducedDiffeomorphismHilbert period hPeriod configuration data :=
  (diffeomorphismGhostNullSpace period hPeriod configuration data).mkQ.comp
    (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data))

theorem reducedDiffeomorphismCoreMap_denseRange : DenseRange
    (reducedDiffeomorphismCoreMap period hPeriod configuration data) :=
  (diffeomorphismGhostNullSpace period hPeriod configuration data).mkQ_surjective.denseRange.comp
    (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_denseRange period hPeriod
      (globalCandidateAMetricBySector period hPeriod data))
    (diffeomorphismGhostNullSpace period hPeriod configuration data).mkQL.continuous

theorem reducedDiffeomorphismCoreMap_ghost_zero (pair : SharedGhostPair period hPeriod) :
    reducedDiffeomorphismCoreMap period hPeriod configuration data (diagonalGhostPairState period hPeriod pair) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.le_topologicalClosure _ ⟨pair, rfl⟩

theorem actualDiffeomorphismInclusion_smooth (vector : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    actualDiffeomorphismInclusion period hPeriod configuration data analysis
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) vector) =
    diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) couplings.matterMassSquared data analysis
      (diffeomorphismCore period hPeriod configuration analysis vector) := by
  change WithLp.toLp 2 (_, 0) = WithLp.toLp 2 (_, WithLp.toLp 2
    (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) 0,
      WithLp.toLp 2
        ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod couplings.matterMassSquared).symm
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod couplings.matterMassSquared 0),
        globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis 0)))
  simp only [map_zero]
  rfl

theorem quotientDiffeomorphismInclusion_smooth (vector : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    quotientDiffeomorphismInclusion period hPeriod configuration data analysis
      (reducedDiffeomorphismCoreMap period hPeriod configuration data vector) =
    jointGhostLLCoreMap period hPeriod configuration data analysis
      (diffeomorphismCore period hPeriod configuration analysis vector) :=
  congrArg (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
    (actualDiffeomorphismInclusion_smooth period hPeriod configuration data analysis vector)
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



/-- Exact actual BRST action and H11 on a reduced diffeomorphism source, against every global smooth test. -/
theorem quotientDiffeomorphism_smooth_pairing
    (vector : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod)
    (test : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    inner Real
      (jointGhostLLRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter
        physical hZero hMetric hWeights (jointGhostLLCoreMap period hPeriod configuration data analysis
          (diffeomorphismCore period hPeriod configuration analysis vector)))
      (jointGhostLLCoreMap period hPeriod configuration data analysis test) =
    globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTPolarizationAction period hPeriod couplings
      (globalCandidateAMetricBySector period hPeriod data) vector test.1 +
    diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod configuration data analysis
      (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
      (strongBridge (measure := measure) period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter).chartBridge
      (diffeomorphismCore period hPeriod configuration analysis vector) test := by
  have h := quotientDiffeomorphism_augmented_pairing period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical hZero hMetric hWeights
    (reducedDiffeomorphismCoreMap period hPeriod configuration data vector)
    (jointGhostLLCoreMap period hPeriod configuration data analysis test)
  rw [quotientDiffeomorphismInclusion_smooth] at h
  exact h.trans (congrArg₂ (· + ·)
    ((reducedDiffeomorphismSignedRiesz_pairing period hPeriod configuration data hMetric hWeights
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) vector)
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) test.1)).trans
      (diagonalDiffeomorphismSignedRiesz_smooth_pairing period hPeriod couplings
        (globalCandidateAMetricBySector period hPeriod data) vector test.1))
    (quotientPhysicalRiesz_smooth_pairing period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (diffeomorphismCore period hPeriod configuration analysis vector) test))

end
end
end P0EFTJanusProgramPT12JointQuotientDiffeomorphismSmoothPairing4D
end JanusFormal
