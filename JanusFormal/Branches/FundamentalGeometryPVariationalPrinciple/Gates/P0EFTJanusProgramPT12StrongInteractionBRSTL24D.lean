import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InteractionBRSTMatrixReadout4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeInteractionHessianL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RelativeMatrixL2Readout4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InteractionHessianCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ContinuousTensorCovectorL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InteractionHessianLocality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InteractionGradientLocality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongInteractionHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12C2RootPointwiseLocality4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongInteractionBRSTL24D

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

open P0EFTJanusProgramPT12NativeInteractionHessianL24D
open P0EFTJanusProgramPT12RelativeMatrixL2Readout4D
open P0EFTJanusProgramPT12NativeMaxwellSpatialSmooth4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D

variable (normalization : SmoothGeneralLorentzMetric period hPeriod)

open P0EFTJanusProgramPT12InteractionBRSTMatrixReadout4D
open P0EFTJanusProgramPT12StrongInteractionHessianPullback4D

def strongInteractionBRSTNativeDirection
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    RelativeCore period hPeriod plusBase minusBase := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  exact globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod configuration data analysis realization plusBase minusBase
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
      (diffeomorphismCore period hPeriod configuration analysis field))

/-- The true interaction Hessian column as a continuous covector on BRST L2. -/
def strongInteractionBRSTHessianCovector
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    DiffeomorphismL2 period hPeriod normalization →L[Real] Real :=
  (innerSL Real (nativeInteractionHessianL2 period hPeriod plusBase minusBase 0
    (strongInteractionBRSTNativeDirection period hPeriod configuration data analysis realization plusBase minusBase field)
      (couplings := couplings))).comp (interactionBRSTMatrixReadout period hPeriod plusBase normalization)

variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible period hPeriod plusBase minusBase)
  (field test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod)

theorem strongInteractionBRSTHessian_eq_covector :
    strongInteractionBRSTHessian period hPeriod configuration data analysis realization plusBase minusBase hBase field test =
    strongInteractionBRSTHessianCovector period hPeriod configuration data analysis realization plusBase minusBase normalization field
      (diffeomorphismL2Smooth period hPeriod normalization test) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  have hZero := zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
    period hPeriod configuration.physical plusBase minusBase hBase
  have hNativeZero := (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
    period hPeriod configuration.physical plusBase minusBase 0).1 hZero
  change (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod configuration data analysis realization plusBase minusBase) 0 ∈
    regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase at hNativeZero
  rw [map_zero] at hNativeZero
  calc
    _ = nativePairedInteractionHessian period hPeriod plusBase minusBase (couplings := couplings)
        (strongInteractionBRSTNativeDirection period hPeriod configuration data analysis realization plusBase minusBase field)
        (strongInteractionBRSTNativeDirection period hPeriod configuration data analysis realization plusBase minusBase test) :=
      strongInteractionActionHessian_eq_native period hPeriod configuration data analysis realization plusBase minusBase hBase _ _
    _ = inner Real (nativeInteractionHessianL2 period hPeriod plusBase minusBase 0
        (strongInteractionBRSTNativeDirection period hPeriod configuration data analysis realization plusBase minusBase field) (couplings := couplings))
        (interactionTestL2 period hPeriod plusBase minusBase
          (strongInteractionBRSTNativeDirection period hPeriod configuration data analysis realization plusBase minusBase test)) :=
      nativeInteractionHessianL2_pairing period hPeriod plusBase minusBase 0 _ _ hNativeZero
    _ = _ := by
      unfold strongInteractionBRSTNativeDirection
      rw [strongInteractionTestL2_eq_readout period hPeriod configuration data analysis realization plusBase minusBase normalization test]
      rfl

theorem strongInteractionBRSTHessian_metric_bound :
    ‖strongInteractionBRSTHessian period hPeriod configuration data analysis realization plusBase minusBase hBase field test‖ ≤
    ‖strongInteractionBRSTHessianCovector period hPeriod configuration data analysis realization plusBase minusBase normalization field‖ *
      ‖diffeomorphismMetricSmooth period hPeriod normalization test‖ := by
  rw [strongInteractionBRSTHessian_eq_covector]
  have hReadout : interactionBRSTMatrixReadout period hPeriod plusBase normalization
      (diffeomorphismL2Smooth period hPeriod normalization test) =
      interactionBRSTMatrixReadout period hPeriod plusBase normalization
        (diffeomorphismL2Smooth period hPeriod normalization (diffeomorphismMetricTransfer period hPeriod normalization test)) := by
    apply PiLp.ext
    intro index
    simp only [interactionBRSTMatrixReadout_smooth, diffeomorphismMetricTransfer_metric]
  have hCovector : strongInteractionBRSTHessianCovector period hPeriod configuration data analysis realization plusBase minusBase normalization field
      (diffeomorphismL2Smooth period hPeriod normalization test) =
      strongInteractionBRSTHessianCovector period hPeriod configuration data analysis realization plusBase minusBase normalization field
        (diffeomorphismL2Smooth period hPeriod normalization (diffeomorphismMetricTransfer period hPeriod normalization test)) :=
    congrArg (innerSL Real (nativeInteractionHessianL2 period hPeriod plusBase minusBase 0
      (strongInteractionBRSTNativeDirection period hPeriod configuration data analysis realization plusBase minusBase field) (couplings := couplings))) hReadout
  rw [hCovector]
  change _ ≤ _ * ‖(diffeomorphismMetricSmooth period hPeriod normalization test).val‖
  rw [diffeomorphismMetricSmooth_original]
  exact ContinuousLinearMap.le_opNorm _ _

end
end P0EFTJanusProgramPT12StrongInteractionBRSTL24D
end JanusFormal
