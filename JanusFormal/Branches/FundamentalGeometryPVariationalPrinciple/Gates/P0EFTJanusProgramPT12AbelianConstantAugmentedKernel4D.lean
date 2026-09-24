import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianMixedAugmented4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianConstantKernel4D

/-! Constant gauge modes survive the complete abelian H11 column. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianConstantAugmentedKernel4D
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

open P0EFTJanusProgramPT12CandidateAAbelianMixedH114D
open P0EFTJanusProgramPT12BoundedSelfAdjointPerturbation4D
open P0EFTJanusProgramPT12CandidateAAbelianMixedPairing4D

open P0EFTJanusProgramPT12CandidateAAbelianMixedAugmented4D
open P0EFTJanusProgramPT12CandidateAAbelianConstantKernel4D
open P0EFTJanusProgramPT12ProductClosedOperator4D
open P0EFTJanusProgramPT12BRSTSaddleProduct4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D

def constantGhostMixed : (Sector → GaugeLieAlgebra) →ₗ[Real]
    CandidateAAbelianMixedHilbert period hPeriod data where
  toFun value := WithLp.toLp 2 (0, constantGhostBRST period hPeriod value)
  map_add' _ _ := by apply WithLp.ofLp_injective 2; exact Prod.ext (zero_add _).symm (map_add _ _ _)
  map_smul' _ _ := by apply WithLp.ofLp_injective 2; exact Prod.ext (smul_zero _).symm (map_smul _ _ _)

theorem constantGhostMixed_injective : Function.Injective (constantGhostMixed period hPeriod configuration data) := by
  intro first second h
  exact constantGhostBRST_injective period hPeriod (congrArg WithLp.snd h)

theorem constantGhostMixed_graph (value : Sector → GaugeLieAlgebra) :
    (constantGhostMixed period hPeriod configuration data value, 0) ∈
      (candidateAAbelianMixedOperator period hPeriod data).graph :=
  (productOperator_mem_graph_iff _ _ _ _).mpr
    ⟨Submodule.zero_mem _, constantGhostBRST_graph period hPeriod data value⟩

/-- Vanishing in the full common output Hilbert space, not just the abelian diagonal block. -/
theorem constantGhostMixed_physicalColumn_zero (value : Sector → GaugeLieAlgebra) :
    candidateAAbelianMixedPhysicalColumn period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical (constantGhostMixed period hPeriod configuration data value) = 0 := by
  change strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical
      (actualAbelianInclusion period hPeriod configuration data analysis
        (abelianPotentialGraphInclusion period hPeriod (globalCandidateAMetricBySector period hPeriod data) 0)) = 0
  simp only [map_zero]

theorem constantGhostMixed_H11_zero (value : Sector → GaugeLieAlgebra) :
    candidateAAbelianMixedH11 period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical (constantGhostMixed period hPeriod configuration data value) = 0 := by
  change (candidateAAbelianMixedPhysicalLift period hPeriod configuration data analysis).adjoint
    (candidateAAbelianMixedPhysicalColumn period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical (constantGhostMixed period hPeriod configuration data value)) = 0
  rw [constantGhostMixed_physicalColumn_zero, map_zero]

theorem constantGhostMixed_augmented_graph (value : Sector → GaugeLieAlgebra) :
    (constantGhostMixed period hPeriod configuration data value, 0) ∈
      (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical).graph := by
  rw [candidateAAbelianMixedAugmentedOperator, boundedPerturbation_mem_graph_iff,
    constantGhostMixed_H11_zero, sub_zero]
  exact constantGhostMixed_graph period hPeriod configuration data value

def constantGhostMixedAugmentedKernel : (Sector → GaugeLieAlgebra) →ₗ[Real]
    LinearMap.ker (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).toFun where
  toFun value := ⟨⟨constantGhostMixed period hPeriod configuration data value,
    LinearPMap.mem_domain_of_mem_graph (constantGhostMixed_augmented_graph period hPeriod configuration data analysis
      realization plusBase minusBase hBase hCenter physical value)⟩, by
    exact LinearPMap.mem_graph_snd_inj _ (LinearPMap.mem_graph _ _)
      (constantGhostMixed_augmented_graph period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical value) rfl⟩
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; exact map_smul _ _ _

theorem constantGhostMixedAugmentedKernel_injective : Function.Injective
    (constantGhostMixedAugmentedKernel period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) := by
  intro first second h
  apply constantGhostMixed_injective period hPeriod configuration data
  exact congrArg (fun state => state.val.val) h

theorem constantGhostMixedAugmentedKernel_range_finrank :
    Module.finrank Real (constantGhostMixedAugmentedKernel period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).range = 4 := by
  rw [LinearMap.finrank_range_of_inj (constantGhostMixedAugmentedKernel_injective period hPeriod configuration
    data analysis realization plusBase minusBase hBase hCenter physical)]
  rw [← LinearMap.finrank_range_of_inj (constantGhostBRSTKernel_injective period hPeriod data)]
  exact constantGhostBRSTKernel_range_finrank period hPeriod data

def constantPairMixed : ((Sector → GaugeLieAlgebra) × (Sector → GaugeLieAlgebra)) →ₗ[Real]
    CandidateAAbelianMixedHilbert period hPeriod data where
  toFun value := WithLp.toLp 2 (0, constantPairBRST period hPeriod data value)
  map_add' _ _ := by apply WithLp.ofLp_injective 2; exact Prod.ext (zero_add _).symm (map_add _ _ _)
  map_smul' _ _ := by apply WithLp.ofLp_injective 2; exact Prod.ext (smul_zero _).symm (map_smul _ _ _)

theorem constantPairMixed_injective : Function.Injective (constantPairMixed period hPeriod configuration data) := by
  intro first second h
  exact constantPairBRST_injective period hPeriod data (congrArg WithLp.snd h)

theorem constantPairMixed_physicalColumn_zero
    (value : (Sector → GaugeLieAlgebra) × (Sector → GaugeLieAlgebra)) :
    candidateAAbelianMixedPhysicalColumn period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical (constantPairMixed period hPeriod configuration data value) = 0 :=
  candidateAAbelianMixedPhysicalColumn_pureGhost_zero period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical _

theorem constantPairMixed_augmented_graph
    (value : (Sector → GaugeLieAlgebra) × (Sector → GaugeLieAlgebra)) :
    (constantPairMixed period hPeriod configuration data value, 0) ∈
      (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical).graph := by
  rw [candidateAAbelianMixedAugmentedOperator_eq_product]
  exact (productOperator_mem_graph_iff _ _ _ _).mpr
    ⟨Submodule.zero_mem _, constantPairBRST_graph period hPeriod data value⟩

theorem constantPairMixed_range_finrank :
    Module.finrank Real (constantPairMixed period hPeriod configuration data).range = 8 := by
  rw [LinearMap.finrank_range_of_inj (constantPairMixed_injective period hPeriod configuration data)]
  rw [← LinearMap.finrank_range_of_inj (constantPairBRSTKernel_injective period hPeriod data)]
  exact constantPairBRSTKernel_range_finrank period hPeriod data

end
end
end P0EFTJanusProgramPT12AbelianConstantAugmentedKernel4D
end JanusFormal
