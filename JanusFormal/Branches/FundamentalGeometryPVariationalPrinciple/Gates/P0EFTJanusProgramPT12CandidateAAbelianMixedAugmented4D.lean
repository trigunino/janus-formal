import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianMixedH114D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BoundedSelfAdjointPerturbation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianMixedPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianMixedPhysical4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianMixedPotential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianGhostRotationPhysical4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianGhostSmoothRotation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianLorenzShearPhysical4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProductFirstPerturbation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProductFredholm4D

/-! All H11 output sectors are retained by the continuous mixed abelian column. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAAbelianMixedAugmented4D
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

/-- The actual abelian BRST block including its H11 contribution. -/
def candidateAAbelianMixedAugmentedOperator : CandidateAAbelianMixedHilbert period hPeriod data →ₗ.[Real]
    CandidateAAbelianMixedHilbert period hPeriod data :=
  boundedPerturbation (candidateAAbelianMixedOperator period hPeriod data)
    (candidateAAbelianMixedH11 period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)

theorem candidateAAbelianMixedAugmentedOperator_selfAdjoint : IsSelfAdjoint
    (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) :=
  boundedPerturbation_selfAdjoint _ _ (candidateAAbelianMixedOperator_selfAdjoint period hPeriod data)
    (candidateAAbelianMixedH11_selfAdjoint period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)

/-- H11 imposes no additional domain condition on the ghosts. -/
theorem candidateAAbelianMixedAugmentedOperator_domain :
    (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).domain =
    (candidateAAbelianMixedOperator period hPeriod data).domain := rfl

theorem candidateAAbelianMixedAugmentedOperator_smooth_pairing
    (first second : GlobalPairedAbelianBRSTState period hPeriod) :
    inner Real (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      ⟨candidateAAbelianMixedSmooth period hPeriod data first,
        candidateAAbelianMixedSmooth_mem period hPeriod data first⟩)
      (candidateAAbelianMixedSmooth period hPeriod data second) =
    globalPairedAbelianOffShellHessian period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (globalCandidateAMetricBySector period hPeriod data) first)
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (globalCandidateAMetricBySector period hPeriod data) second) +
    physical.form
      (actualAbelianInclusion period hPeriod configuration data analysis
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (globalCandidateAMetricBySector period hPeriod data) first))
      (actualAbelianInclusion period hPeriod configuration data analysis
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (globalCandidateAMetricBySector period hPeriod data) second)) := by
  change inner Real
    (candidateAAbelianMixedH11 period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical (candidateAAbelianMixedSmooth period hPeriod data first) +
     candidateAAbelianMixedOperator period hPeriod data
      ⟨candidateAAbelianMixedSmooth period hPeriod data first,
        candidateAAbelianMixedSmooth_mem period hPeriod data first⟩)
    (candidateAAbelianMixedSmooth period hPeriod data second) = _
  rw [inner_add_left, candidateAAbelianMixedH11_smooth_pairing,
    candidateAAbelianMixedOperator_smooth_hessian, add_comm]

/-- Exact agreement with the original augmented Riesz pairing on smooth abelian states. -/
theorem candidateAAbelianMixedAugmentedOperator_smooth_actual
    (first second : GlobalPairedAbelianBRSTState period hPeriod) :
    inner Real (candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      ⟨candidateAAbelianMixedSmooth period hPeriod data first,
        candidateAAbelianMixedSmooth_mem period hPeriod data first⟩)
      (candidateAAbelianMixedSmooth period hPeriod data second) =
    inner Real (strongAugmentedRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (actualAbelianInclusion period hPeriod configuration data analysis
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (globalCandidateAMetricBySector period hPeriod data) first)))
      (actualAbelianInclusion period hPeriod configuration data analysis
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (globalCandidateAMetricBySector period hPeriod data) second)) := by
  rw [candidateAAbelianMixedAugmentedOperator_smooth_pairing, actualAbelian_augmented_pairing]
  congr 1
  exact (pairedAbelianSignedRiesz_pairing period hPeriod
    (globalCandidateAMetricBySector period hPeriod data) _ _).symm

open P0EFTJanusProgramPT12ProductFirstPerturbation4D
open P0EFTJanusProgramPT12ProductClosedOperator4D
open P0EFTJanusProgramPT12ProductSelfAdjoint4D
open P0EFTJanusProgramPT12BRSTSaddleProduct4D
open P0EFTJanusProgramPT12CandidateAAbelianGhostSelfAdjoint4D

theorem candidateAAbelianMixedPhysicalLift_pureGhost_zero
    (ghost : CandidateAAbelianGhostL2 period hPeriod) :
    candidateAAbelianMixedPhysicalLift period hPeriod configuration data analysis (WithLp.toLp 2 (0, ghost)) = 0 := by
  change actualAbelianInclusion period hPeriod configuration data analysis
    (abelianPotentialGraphInclusion period hPeriod (globalCandidateAMetricBySector period hPeriod data) 0) = 0
  simp only [map_zero]

theorem candidateAAbelianMixedPhysicalColumn_pureGhost_zero
    (ghost : CandidateAAbelianGhostL2 period hPeriod) :
    candidateAAbelianMixedPhysicalColumn period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical (WithLp.toLp 2 (0, ghost)) = 0 := by
  change strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical
    (candidateAAbelianMixedPhysicalLift period hPeriod configuration data analysis (WithLp.toLp 2 (0, ghost))) = 0
  rw [candidateAAbelianMixedPhysicalLift_pureGhost_zero, map_zero]

/-- Every completed ghost vector has zero H11 column, not merely the constant modes. -/
theorem candidateAAbelianMixedH11_pureGhost_zero
    (ghost : CandidateAAbelianGhostL2 period hPeriod) :
    candidateAAbelianMixedH11 period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical (WithLp.toLp 2 (0, ghost)) = 0 := by
  change (candidateAAbelianMixedPhysicalLift period hPeriod configuration data analysis).adjoint
    (candidateAAbelianMixedPhysicalColumn period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (WithLp.toLp 2 (0, ghost))) = 0
  rw [candidateAAbelianMixedPhysicalColumn_pureGhost_zero, map_zero]

abbrev CandidateAAbelianPotentialBHilbert := WithLp 2
  (GlobalPairedAbelianLorenzGraphHilbert period hPeriod (globalCandidateAMetricBySector period hPeriod data) ×
    GlobalPairedGaugeLieL2 period hPeriod)

/-- The potential--B saddle, including its complete internal H11 perturbation. -/
def candidateAAbelianPotentialBHessian :
    CandidateAAbelianPotentialBHilbert period hPeriod configuration data →ₗ.[Real]
      CandidateAAbelianPotentialBHilbert period hPeriod configuration data :=
  boundedPerturbation
    ((nonminimalSaddle (globalPairedAbelianLorenzFeatureProjection period hPeriod
      (globalCandidateAMetricBySector period hPeriod data))).toPMap ⊤)
    (firstCompression (candidateAAbelianMixedH11 period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical))

theorem candidateAAbelianPotentialBHessian_domain :
    (candidateAAbelianPotentialBHessian period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical).domain = ⊤ := rfl

theorem candidateAAbelianPotentialBHessian_selfAdjoint : IsSelfAdjoint
    (candidateAAbelianPotentialBHessian period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) :=
  boundedPerturbation_selfAdjoint _ _
    (bounded_toPMap_selfAdjoint _ (nonminimalSaddle_symmetric _))
    (firstCompression_selfAdjoint _ (candidateAAbelianMixedH11_selfAdjoint period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical))

/-- Exact operator equality on the full domains: H11 leaves the actual FP/FP-adjoint block unchanged. -/
theorem candidateAAbelianMixedAugmentedOperator_eq_product :
    candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical =
    productOperator (candidateAAbelianPotentialBHessian period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) (candidateAAbelianGhostOperator period hPeriod data) :=
  product_firstPerturbation _
    (candidateAAbelianMixedH11_selfAdjoint period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)
    (candidateAAbelianMixedH11_pureGhost_zero period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) _ _

/-- The real abelian Fredholm problem separates into its two actual factors. -/
theorem candidateAAbelianMixedAugmentedOperator_fredholm_iff_factors :
    let full := candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
    let potentialB := candidateAAbelianPotentialBHessian period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
    let ghost := candidateAAbelianGhostOperator period hPeriod data
    (IsClosed (LinearMap.range full.toFun : Set (CandidateAAbelianMixedHilbert period hPeriod data)) ∧
      FiniteDimensional Real (LinearMap.ker full.toFun) ∧
      FiniteDimensional Real (CandidateAAbelianMixedHilbert period hPeriod data ⧸ LinearMap.range full.toFun)) ↔
    ((IsClosed (LinearMap.range potentialB.toFun : Set (CandidateAAbelianPotentialBHilbert period hPeriod configuration data)) ∧
      FiniteDimensional Real (LinearMap.ker potentialB.toFun)) ∧
     (IsClosed (LinearMap.range ghost.toFun : Set (CandidateAAbelianGhostL2 period hPeriod)) ∧
      FiniteDimensional Real (LinearMap.ker ghost.toFun))) := by
  dsimp only
  rw [candidateAAbelianMixedAugmentedOperator_eq_product]
  exact P0EFTJanusProgramPT12ProductFredholm4D.productOperator_fredholm_iff _ _
    (candidateAAbelianPotentialBHessian_selfAdjoint period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical)
    (candidateAAbelianGhostOperator_selfAdjoint period hPeriod data)

/-- The full abelian conditions use a single FP range and both actual FP kernels. -/
theorem candidateAAbelianMixedAugmentedOperator_fredholm_iff_fp_conditions :
    let full := candidateAAbelianMixedAugmentedOperator period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
    let potentialB := candidateAAbelianPotentialBHessian period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
    let fp := P0EFTJanusProgramPT12CandidateAFPCanonicalClosed4D.candidateAFPCanonicalMinimal period hPeriod data
    (IsClosed (LinearMap.range full.toFun : Set (CandidateAAbelianMixedHilbert period hPeriod data)) ∧
      FiniteDimensional Real (LinearMap.ker full.toFun) ∧
      FiniteDimensional Real (CandidateAAbelianMixedHilbert period hPeriod data ⧸ LinearMap.range full.toFun)) ↔
    ((IsClosed (LinearMap.range potentialB.toFun : Set (CandidateAAbelianPotentialBHilbert period hPeriod configuration data)) ∧
      FiniteDimensional Real (LinearMap.ker potentialB.toFun)) ∧
     (IsClosed (LinearMap.range fp.toFun : Set (GlobalPairedGaugeLieL2 period hPeriod)) ∧
      FiniteDimensional Real (LinearMap.ker fp.toFun) ∧
      FiniteDimensional Real (LinearMap.ker fp.adjoint.toFun))) := by
  dsimp only
  have hFactors := candidateAAbelianMixedAugmentedOperator_fredholm_iff_factors
    period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical
  have hGhost := candidateAAbelianGhostOperator_fredholm_iff period hPeriod data
  dsimp only at hFactors hGhost
  rw [hFactors,
    ← P0EFTJanusProgramPT12NullQuotientFredholm4D.selfAdjoint_fredholm_iff _
      (candidateAAbelianGhostOperator_selfAdjoint period hPeriod data),
    hGhost]

end
end
end P0EFTJanusProgramPT12CandidateAAbelianMixedAugmented4D
end JanusFormal
