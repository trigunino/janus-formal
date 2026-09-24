import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InteractionHessianCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ContinuousTensorCovectorL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InteractionHessianLocality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InteractionGradientLocality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongInteractionHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12C2RootPointwiseLocality4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12NativeInteractionHessianL24D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance 1900]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedAddCommGroup
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

open P0EFTJanusProgramPT12ProjectedGradientDerivative4D
open P0EFTJanusProgramPT12PairedMaxwellCenterC24D
open P0EFTJanusProgramPT12PairedMaxwellHessianPullback4D
open P0EFTJanusProgramPT12MaxwellNativeMixedHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellDerivative4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D

local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

variable {couplings : GlobalCandidateAActionCouplings}
  {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
  (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
  (data : GlobalCandidateAActionData period hPeriod configuration.physical couplings NonNullFace NullFace)
  (analysis : GlobalAnalysisData period hPeriod configuration.physical)
  (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D period hPeriod couplings.matterMassSquared)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertKernelSaturation4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPT12JointQuotientDiffeomorphismSmoothPairing4D
open P0EFTJanusProgramPT12JointQuotientAbelianSmoothPairing4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPT12MaxwellPhysicalCoreProjection4D
open P0EFTJanusProgramPT12StrongMaxwellActionHessian4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D

open P0EFTJanusProgramPT12PhysicalGaugeHessianReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeReducedCoupledResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellWeakFirstVariation4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D

open P0EFTJanusProgramPT12StrongPhysicalGaugeGradient4D
open P0EFTJanusProgramPT12StrongMaxwellBRSTMixedHessian4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D

open P0EFTJanusProgramPT12PhysicalMetricHessianReduction4D
open P0EFTJanusProgramPT12StrongEinsteinBRSTHessian4D
open P0EFTJanusProgramPT12StrongMaxwellBRSTMetricHessian4D

open P0EFTJanusProgramPT12StrongPhysicalBRSTMetricHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongInteractionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D

open P0EFTJanusProgramPT12C2RootPointwiseLocality4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootInverseCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2InverseVelocityPointwise4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D

private abbrev RelativeCore := RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase

open P0EFTJanusProgramPT12InteractionHessianCoefficients4D
open P0EFTJanusProgramPT12ContinuousTensorCovectorL24D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusProgramPGeneralMetricC2IntegratedVolume4D
open P0EFTJanusProgramPT12VectorHessianPullback4D
open scoped BigOperators InnerProductSpace

abbrev InteractionMatrixL2 := PiLp 2 fun _ : InteractionMatrixIndex => CanonicalPhysicalBulkL2 period hPeriod

def interactionTestValue (test : RelativeCore period hPeriod plusBase minusBase)
    (index : InteractionMatrixIndex) : C(EffectiveQuotient period hPeriod, Real) :=
  canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
    (if index.1 then test.2.1 index.2.1 index.2.2 else test.2.2 index.2.1 index.2.2)

theorem interactionTestValue_apply (test : RelativeCore period hPeriod plusBase minusBase)
    (index : InteractionMatrixIndex) (point : EffectiveQuotient period hPeriod) :
    interactionTestValue period hPeriod plusBase minusBase test index point =
      interactionMatrixValues period hPeriod plusBase minusBase point test index := by
  rcases index with ⟨sector, row, column⟩
  cases sector <;> rfl

def interactionTestL2 (test : RelativeCore period hPeriod plusBase minusBase) : InteractionMatrixL2 period hPeriod :=
  WithLp.toLp 2 fun index => continuousToCanonicalPhysicalBulkL2 period hPeriod
    (interactionTestValue period hPeriod plusBase minusBase test index)

def nativeInteractionHessianL2 (core first : RelativeCore period hPeriod plusBase minusBase) :
    InteractionMatrixL2 period hPeriod :=
  WithLp.toLp 2 fun index => continuousToCanonicalPhysicalBulkL2 period hPeriod
    (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (interactionDensityHessianCoefficient period hPeriod plusBase minusBase core first index (couplings := couplings)))

theorem nativeInteractionHessianL2_density_pairing
    (core first test : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase) :
    inner Real (nativeInteractionHessianL2 period hPeriod plusBase minusBase core first (couplings := couplings))
      (interactionTestL2 period hPeriod plusBase minusBase test) =
    ∫ point, canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (fderiv Real (fderiv Real (regularGeneralMetricC2PairedInteractionC2Density period hPeriod plusBase minusBase
        couplings.interactionScale couplings.interactionCoefficients)) core first test) point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [PiLp.inner_apply]
  change (∑ index : InteractionMatrixIndex, inner Real
    (continuousToCanonicalPhysicalBulkL2 period hPeriod
      (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (interactionDensityHessianCoefficient period hPeriod plusBase minusBase core first index (couplings := couplings))))
    (continuousToCanonicalPhysicalBulkL2 period hPeriod
      (interactionTestValue period hPeriod plusBase minusBase test index))) = _
  simp_rw [canonicalContinuousScalarL2_inner]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with point
    rw [interactionDensityHessian_valueAt_eq_sum period hPeriod plusBase minusBase core first test point hCore]
    apply Finset.sum_congr rfl
    intro index _
    rw [interactionTestValue_apply, mul_comm]
  · intro index _
    exact ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (interactionDensityHessianCoefficient period hPeriod plusBase minusBase core first index (couplings := couplings))).continuous.mul
      (interactionTestValue period hPeriod plusBase minusBase test index).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

theorem nativeInteractionHessianL2_pairing
    (core first test : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase) :
    fderiv Real (fderiv Real (regularGeneralMetricC2PairedInteractionC2Action period hPeriod plusBase minusBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings.interactionScale couplings.interactionCoefficients))
      core first test =
    inner Real (nativeInteractionHessianL2 period hPeriod plusBase minusBase core first (couplings := couplings))
      (interactionTestL2 period hPeriod plusBase minusBase test) := by
  have hC2 := (regularGeneralMetricC2PairedInteractionC2Density_contDiffOn period hPeriod plusBase minusBase
    couplings.interactionScale couplings.interactionCoefficients).contDiffAt
      ((regularGeneralMetricC2PairedLorentzMatrixDomain_isOpen period hPeriod plusBase minusBase).mem_nhds hCore)
  change fderiv Real (fderiv Real ((canonicalPhysicalC2ScalarIntegralCLM period hPeriod
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) ∘
    (regularGeneralMetricC2PairedInteractionC2Density period hPeriod plusBase minusBase
      couplings.interactionScale couplings.interactionCoefficients))) core first test = _
  rw [linearPostHessian _ _ core first test hC2, canonicalPhysicalC2ScalarIntegralCLM_apply]
  exact (nativeInteractionHessianL2_density_pairing period hPeriod plusBase minusBase core first test hCore).symm

theorem nativeInteractionHessianL2_bound
    (core first test : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase) :
    ‖fderiv Real (fderiv Real (regularGeneralMetricC2PairedInteractionC2Action period hPeriod plusBase minusBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings.interactionScale couplings.interactionCoefficients))
      core first test‖ ≤
    ‖nativeInteractionHessianL2 period hPeriod plusBase minusBase core first (couplings := couplings)‖ *
      ‖interactionTestL2 period hPeriod plusBase minusBase test‖ := by
  rw [nativeInteractionHessianL2_pairing period hPeriod plusBase minusBase core first test hCore]
  exact norm_inner_le_norm _ _

end
end P0EFTJanusProgramPT12NativeInteractionHessianL24D
end JanusFormal
