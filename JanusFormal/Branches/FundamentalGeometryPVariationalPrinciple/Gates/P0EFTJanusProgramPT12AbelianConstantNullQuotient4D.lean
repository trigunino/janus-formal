import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianConstantAugmentedKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NullQuotientObservation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullPMapSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NullQuotientFredholm4D

/-! Remove exactly the four constructed constant ghost modes, retaining H11 and all other outputs. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianConstantNullQuotient4D
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

open P0EFTJanusProgramPT12AbelianConstantAugmentedKernel4D
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
open P0EFTJanusProgramPT12ClosedNullPMapSelfAdjoint4D

def abelianConstantNullSpace : Submodule Real (CandidateAAbelianMixedHilbert period hPeriod data) :=
  (constantGhostMixed period hPeriod configuration data).range

instance abelianConstantNullSpace_finite : FiniteDimensional Real
    (abelianConstantNullSpace period hPeriod configuration data) :=
  inferInstanceAs (FiniteDimensional Real (constantGhostMixed period hPeriod configuration data).range)

instance abelianConstantNullSpace_closed : IsClosed
    (abelianConstantNullSpace period hPeriod configuration data : Set (CandidateAAbelianMixedHilbert period hPeriod data)) :=
  Submodule.closed_of_finiteDimensional _

theorem abelianConstantNullSpace_finrank :
    Module.finrank Real (abelianConstantNullSpace period hPeriod configuration data) = 4 := by
  change Module.finrank Real (constantGhostMixed period hPeriod configuration data).range = 4
  rw [LinearMap.finrank_range_of_inj (constantGhostMixed_injective period hPeriod configuration data)]
  rw [← LinearMap.finrank_range_of_inj (constantGhostBRSTKernel_injective period hPeriod data)]
  exact constantGhostBRSTKernel_range_finrank period hPeriod data

theorem abelianConstantNullSpace_graph : ∀ vector ∈ abelianConstantNullSpace period hPeriod configuration data,
    (vector, (0 : CandidateAAbelianMixedHilbert period hPeriod data)) ∈
      (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical).graph := by
  rintro _ ⟨value, rfl⟩
  exact constantGhostMixed_augmented_graph period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical value

local instance constantQuotientComplete : CompleteSpace
    (CandidateAAbelianMixedHilbert period hPeriod data ⧸ abelianConstantNullSpace period hPeriod configuration data) :=
  inferInstance

local instance constantQuotientInner : InnerProductSpace Real
    (CandidateAAbelianMixedHilbert period hPeriod data ⧸ abelianConstantNullSpace period hPeriod configuration data) :=
  inferInstance

def abelianConstantReducedOperator :
    (CandidateAAbelianMixedHilbert period hPeriod data ⧸ abelianConstantNullSpace period hPeriod configuration data) →ₗ.[Real]
    (CandidateAAbelianMixedHilbert period hPeriod data ⧸ abelianConstantNullSpace period hPeriod configuration data) :=
  quotientPMap (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical) (abelianConstantNullSpace period hPeriod configuration data)

theorem abelianConstantReducedOperator_selfAdjoint : IsSelfAdjoint
    (abelianConstantReducedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) :=
  quotientPMap_selfAdjoint _ _
    (candidateAAbelianMixedAugmentedOperator_selfAdjoint period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)
    (abelianConstantNullSpace_graph period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)

private theorem augmented_symmetric :
    (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).IsFormalAdjoint
    (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) := by
  have hSelf := candidateAAbelianMixedAugmentedOperator_selfAdjoint period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical
  have h := LinearPMap.adjoint_isFormalAdjoint hSelf.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp hSelf] at h

theorem abelianConstantReducedOperator_domain :
    (abelianConstantReducedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).domain =
    (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).domain.map
      (abelianConstantNullSpace period hPeriod configuration data).mkQ :=
  quotientPMap_domain _ _
    (augmented_symmetric period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)
    (abelianConstantNullSpace_graph period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)

theorem abelianConstantReducedOperator_pairing
    (vector : (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).domain)
    (test : CandidateAAbelianMixedHilbert period hPeriod data)
    (hDomain : (abelianConstantNullSpace period hPeriod configuration data).mkQ vector.val ∈
      (abelianConstantReducedOperator period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical).domain) :
    inner Real ((abelianConstantReducedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)
        ⟨(abelianConstantNullSpace period hPeriod configuration data).mkQ vector.val, hDomain⟩)
      ((abelianConstantNullSpace period hPeriod configuration data).mkQ test) =
    inner Real ((candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) vector) test :=
  quotientPMap_pairing _ _
    (augmented_symmetric period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)
    (abelianConstantNullSpace_graph period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)
    vector test hDomain

/- The finite null quotient preserves all Fredholm obligations. The two genuine
analytic requirements remain on the actual augmented operator. -/
theorem abelianConstantReducedOperator_fredholm_iff :
    let original := candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
    let reduced := abelianConstantReducedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
    (IsClosed (LinearMap.range reduced.toFun : Set
        (CandidateAAbelianMixedHilbert period hPeriod data ⧸ abelianConstantNullSpace period hPeriod configuration data)) ∧
      FiniteDimensional Real (LinearMap.ker reduced.toFun) ∧
      FiniteDimensional Real ((CandidateAAbelianMixedHilbert period hPeriod data ⧸
        abelianConstantNullSpace period hPeriod configuration data) ⧸ LinearMap.range reduced.toFun)) ↔
    (IsClosed (LinearMap.range original.toFun : Set (CandidateAAbelianMixedHilbert period hPeriod data)) ∧
      FiniteDimensional Real (LinearMap.ker original.toFun)) := by
  have hSelf := candidateAAbelianMixedAugmentedOperator_selfAdjoint period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical
  exact (P0EFTJanusProgramPT12NullQuotientFredholm4D.quotientPMap_fredholm_iff _ hSelf _
    (abelianConstantNullSpace_graph period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)).trans
    (P0EFTJanusProgramPT12NullQuotientFredholm4D.selfAdjoint_fredholm_iff _ hSelf)

/-- Remove the eight constructed ghost/weighted-antighost modes. -/
def abelianConstantPairNullSpace : Submodule Real (CandidateAAbelianMixedHilbert period hPeriod data) :=
  (constantPairMixed period hPeriod configuration data).range

instance abelianConstantPairNullSpace_finite : FiniteDimensional Real
    (abelianConstantPairNullSpace period hPeriod configuration data) :=
  inferInstanceAs (FiniteDimensional Real (constantPairMixed period hPeriod configuration data).range)

instance abelianConstantPairNullSpace_closed : IsClosed
    (abelianConstantPairNullSpace period hPeriod configuration data : Set (CandidateAAbelianMixedHilbert period hPeriod data)) :=
  Submodule.closed_of_finiteDimensional _

theorem abelianConstantPairNullSpace_finrank :
    Module.finrank Real (abelianConstantPairNullSpace period hPeriod configuration data) = 8 := by
  change Module.finrank Real (constantPairMixed period hPeriod configuration data).range = 8
  rw [LinearMap.finrank_range_of_inj (constantPairMixed_injective period hPeriod configuration data)]
  rw [← LinearMap.finrank_range_of_inj (constantPairBRSTKernel_injective period hPeriod data)]
  exact constantPairBRSTKernel_range_finrank period hPeriod data

theorem abelianConstantPairNullSpace_graph : ∀ vector ∈ abelianConstantPairNullSpace period hPeriod configuration data,
    (vector, (0 : CandidateAAbelianMixedHilbert period hPeriod data)) ∈
      (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical).graph := by
  rintro _ ⟨value, rfl⟩
  exact constantPairMixed_augmented_graph period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical value

local instance constantPairQuotientComplete : CompleteSpace
    (CandidateAAbelianMixedHilbert period hPeriod data ⧸ abelianConstantPairNullSpace period hPeriod configuration data) :=
  inferInstance

local instance constantPairQuotientInner : InnerProductSpace Real
    (CandidateAAbelianMixedHilbert period hPeriod data ⧸ abelianConstantPairNullSpace period hPeriod configuration data) :=
  inferInstance

def abelianConstantPairReducedOperator :
    (CandidateAAbelianMixedHilbert period hPeriod data ⧸ abelianConstantPairNullSpace period hPeriod configuration data) →ₗ.[Real]
    (CandidateAAbelianMixedHilbert period hPeriod data ⧸ abelianConstantPairNullSpace period hPeriod configuration data) :=
  quotientPMap (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical) (abelianConstantPairNullSpace period hPeriod configuration data)

theorem abelianConstantPairReducedOperator_selfAdjoint : IsSelfAdjoint
    (abelianConstantPairReducedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) :=
  quotientPMap_selfAdjoint _ _
    (candidateAAbelianMixedAugmentedOperator_selfAdjoint period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)
    (abelianConstantPairNullSpace_graph period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)

theorem abelianConstantPairReducedOperator_domain :
    (abelianConstantPairReducedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).domain =
    (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).domain.map
      (abelianConstantPairNullSpace period hPeriod configuration data).mkQ :=
  quotientPMap_domain _ _
    (augmented_symmetric period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)
    (abelianConstantPairNullSpace_graph period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)

theorem abelianConstantPairReducedOperator_pairing
    (vector : (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).domain)
    (test : CandidateAAbelianMixedHilbert period hPeriod data)
    (hDomain : (abelianConstantPairNullSpace period hPeriod configuration data).mkQ vector.val ∈
      (abelianConstantPairReducedOperator period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical).domain) :
    inner Real ((abelianConstantPairReducedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)
        ⟨(abelianConstantPairNullSpace period hPeriod configuration data).mkQ vector.val, hDomain⟩)
      ((abelianConstantPairNullSpace period hPeriod configuration data).mkQ test) =
    inner Real ((candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) vector) test :=
  quotientPMap_pairing _ _
    (augmented_symmetric period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)
    (abelianConstantPairNullSpace_graph period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)
    vector test hDomain

/- The finite null quotient preserves all Fredholm obligations. The two genuine
analytic requirements remain on the actual augmented operator. -/
theorem abelianConstantPairReducedOperator_fredholm_iff :
    let original := candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
    let reduced := abelianConstantPairReducedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
    (IsClosed (LinearMap.range reduced.toFun : Set
        (CandidateAAbelianMixedHilbert period hPeriod data ⧸ abelianConstantPairNullSpace period hPeriod configuration data)) ∧
      FiniteDimensional Real (LinearMap.ker reduced.toFun) ∧
      FiniteDimensional Real ((CandidateAAbelianMixedHilbert period hPeriod data ⧸
        abelianConstantPairNullSpace period hPeriod configuration data) ⧸ LinearMap.range reduced.toFun)) ↔
    (IsClosed (LinearMap.range original.toFun : Set (CandidateAAbelianMixedHilbert period hPeriod data)) ∧
      FiniteDimensional Real (LinearMap.ker original.toFun)) := by
  have hSelf := candidateAAbelianMixedAugmentedOperator_selfAdjoint period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical
  exact (P0EFTJanusProgramPT12NullQuotientFredholm4D.quotientPMap_fredholm_iff _ hSelf _
    (abelianConstantPairNullSpace_graph period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)).trans
    (P0EFTJanusProgramPT12NullQuotientFredholm4D.selfAdjoint_fredholm_iff _ hSelf)

/-- One finite-observation estimate on the actual reduced domain implies all Fredholm obligations. -/
theorem abelianConstantPairReducedOperator_fredholm_of_estimate
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F]
    (observation : (CandidateAAbelianMixedHilbert period hPeriod data ⧸
      abelianConstantPairNullSpace period hPeriod configuration data) →L[Real] F)
    (C : NNReal)
    (hEstimate : ∀ u : (abelianConstantPairReducedOperator period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical).domain,
      ‖u.val‖ ≤ C *
        (‖abelianConstantPairReducedOperator period hPeriod configuration data analysis realization
          plusBase minusBase hBase hCenter physical u‖ + ‖observation u.val‖)) :
    let reduced := abelianConstantPairReducedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
    IsClosed (LinearMap.range reduced.toFun : Set
        (CandidateAAbelianMixedHilbert period hPeriod data ⧸ abelianConstantPairNullSpace period hPeriod configuration data)) ∧
      FiniteDimensional Real (LinearMap.ker reduced.toFun) ∧
      FiniteDimensional Real ((CandidateAAbelianMixedHilbert period hPeriod data ⧸
        abelianConstantPairNullSpace period hPeriod configuration data) ⧸ LinearMap.range reduced.toFun) :=
  P0EFTJanusProgramPT12FiniteObservationEstimate4D.selfAdjoint_fredholm_of_finite_observation _
    (abelianConstantPairReducedOperator_selfAdjoint period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) observation C hEstimate

/-- Canonical observation valued in the actual eight-dimensional null space. -/
def abelianConstantPairObservation : CandidateAAbelianMixedHilbert period hPeriod data →L[Real]
    abelianConstantPairNullSpace period hPeriod configuration data :=
  (abelianConstantPairNullSpace period hPeriod configuration data).orthogonalProjectionOnto

theorem abelianConstantPairObservation_norm_le (u : CandidateAAbelianMixedHilbert period hPeriod data) :
    ‖abelianConstantPairObservation period hPeriod configuration data u‖ ≤ ‖u‖ :=
  (abelianConstantPairNullSpace period hPeriod configuration data).norm_orthogonalProjectionOnto_apply_le u

theorem abelianConstantPairObservation_norm_of_mem
    (u : abelianConstantPairNullSpace period hPeriod configuration data) :
    ‖abelianConstantPairObservation period hPeriod configuration data u.val‖ = ‖u.val‖ :=
  (abelianConstantPairNullSpace period hPeriod configuration data).norm_orthogonalProjectionOnto_apply u.property

theorem abelianConstantPairObservation_norm_decomposition
    (u : CandidateAAbelianMixedHilbert period hPeriod data) :
    ‖u‖ ^ 2 = ‖(abelianConstantPairNullSpace period hPeriod configuration data).mkQ u‖ ^ 2 +
      ‖abelianConstantPairObservation period hPeriod configuration data u‖ ^ 2 :=
  P0EFTJanusProgramPT12NullQuotientObservation4D.norm_sq_eq_quotient_add_observation _ u

/-- The full actual output has no component in the observed null modes. -/
theorem abelianConstantPairObservation_output_zero
    (u : (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).domain) :
    abelianConstantPairObservation period hPeriod configuration data
      (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical u) = 0 :=
  (abelianConstantPairNullSpace period hPeriod configuration data).orthogonalProjectionOnto_eq_zero_iff.mpr
    (output_mem_orthogonal _ _
      (augmented_symmetric period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)
      (abelianConstantPairNullSpace_graph period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical) u)

/-- Append finite observations of any remaining null modes; the eight known modes are already covered. -/
def abelianLiftedObservation {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (observation : (CandidateAAbelianMixedHilbert period hPeriod data ⧸
      abelianConstantPairNullSpace period hPeriod configuration data) →L[Real] F) :
    CandidateAAbelianMixedHilbert period hPeriod data →L[Real]
      (abelianConstantPairNullSpace period hPeriod configuration data) × F :=
  P0EFTJanusProgramPT12NullQuotientObservation4D.liftedObservation _ observation

theorem abelianLiftedObservation_dimension {F : Type*}
    [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F] :
    Module.finrank Real ((abelianConstantPairNullSpace period hPeriod configuration data) × F) =
      8 + Module.finrank Real F := by
  rw [Module.finrank_prod, abelianConstantPairNullSpace_finrank]

theorem abelianConstantPairReduced_estimate_lifts
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (observation : (CandidateAAbelianMixedHilbert period hPeriod data ⧸
      abelianConstantPairNullSpace period hPeriod configuration data) →L[Real] F) (C : NNReal)
    (hEstimate : ∀ u : (abelianConstantPairReducedOperator period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical).domain,
      ‖u.val‖ ≤ C *
        (‖abelianConstantPairReducedOperator period hPeriod configuration data analysis realization
          plusBase minusBase hBase hCenter physical u‖ + ‖observation u.val‖))
    (u : (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).domain) :
    ‖u.val‖ ≤ (C + 1 : NNReal) *
      (‖candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
          plusBase minusBase hBase hCenter physical u‖ +
        ‖abelianLiftedObservation period hPeriod configuration data observation u.val‖) :=
  P0EFTJanusProgramPT12NullQuotientObservation4D.quotient_estimate_lifts _ _
    (augmented_symmetric period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)
    (abelianConstantPairNullSpace_graph period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) observation C hEstimate u

end
end
end P0EFTJanusProgramPT12AbelianConstantNullQuotient4D
end JanusFormal
