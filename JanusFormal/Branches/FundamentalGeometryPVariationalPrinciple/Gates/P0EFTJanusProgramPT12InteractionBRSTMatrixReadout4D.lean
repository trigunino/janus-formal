import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeInteractionHessianL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RelativeMatrixL2Readout4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InteractionHessianCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ContinuousTensorCovectorL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InteractionHessianLocality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InteractionGradientLocality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongInteractionHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12C2RootPointwiseLocality4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12InteractionBRSTMatrixReadout4D

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
open P0EFTJanusProgramPT12PairedInducedMaxwellL24D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D

variable (normalization : SmoothGeneralLorentzMetric period hPeriod)

def interactionBRSTMatrixReadout : DiffeomorphismL2 period hPeriod normalization →L[Real] InteractionMatrixL2 period hPeriod :=
  (PiLp.continuousLinearEquiv 2 Real (fun _ : InteractionMatrixIndex => CanonicalPhysicalBulkL2 period hPeriod)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun index =>
      if index.1 then
        (relativeMatrixComponentL2 period hPeriod plusBase index.2.1 index.2.2).comp
          (diffeomorphismTensorReadout period hPeriod normalization .plus)
      else
        (relativeMatrixComponentL2 period hPeriod plusBase index.2.1 index.2.2).comp
          ((diffeomorphismTensorReadout period hPeriod normalization .minus) -
            (diffeomorphismTensorReadout period hPeriod normalization .plus)))

theorem interactionBRSTMatrixReadout_smooth
    (test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (index : InteractionMatrixIndex) :
    interactionBRSTMatrixReadout period hPeriod plusBase normalization
      (diffeomorphismL2Smooth period hPeriod normalization test) index =
    if index.1 then smoothToCanonicalPhysicalBulkL2 period hPeriod
      (nativeRelativeMatrixField period hPeriod plusBase (test.metricPerturbation .plus) index.2.1 index.2.2)
    else smoothToCanonicalPhysicalBulkL2 period hPeriod
      (nativeRelativeMatrixField period hPeriod plusBase (test.metricPerturbation .minus) index.2.1 index.2.2) -
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (nativeRelativeMatrixField period hPeriod plusBase (test.metricPerturbation .plus) index.2.1 index.2.2) := by
  rcases index with ⟨sector, row, column⟩
  cases sector <;>
    simp only [interactionBRSTMatrixReadout, Bool.false_eq_true, ↓reduceIte, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.pi_apply, ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply,
      WithLp.ofLp_toLp, sub_apply, map_sub, diffeomorphismTensorReadout_smooth, relativeMatrixComponentL2_smooth]

private theorem variationEntryL2
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) (row column : Fin 4) :
    continuousToCanonicalPhysicalBulkL2 period hPeriod
      (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (regularGeneralMetricC2VariationMatrix period hPeriod plusBase tensor row column)) =
    smoothToCanonicalPhysicalBulkL2 period hPeriod (nativeRelativeMatrixField period hPeriod plusBase tensor row column) := by
  change continuousToCanonicalPhysicalBulkL2 period hPeriod
    (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (nativeRelativeMatrixField period hPeriod plusBase tensor row column))) = _
  rw [canonicalPhysicalScalarC2JetCoreToContinuous_smooth, continuousToCanonicalPhysicalBulkL2_agrees_on_smooth]

theorem strongInteractionTestL2_eq_readout
    (test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    interactionTestL2 period hPeriod plusBase minusBase
      (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod configuration data analysis realization plusBase minusBase
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
          (diffeomorphismCore period hPeriod configuration analysis test))) =
    interactionBRSTMatrixReadout period hPeriod plusBase normalization (diffeomorphismL2Smooth period hPeriod normalization test) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  apply PiLp.ext
  intro index
  rw [interactionBRSTMatrixReadout_smooth]
  let direction := diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
    (diffeomorphismCore period hPeriod configuration analysis test)
  have hMetric (sector) : direction.1.completeVariation.fullMetricPerturbation sector = test.metricPerturbation sector := by
    dsimp only [direction]
    rw [diagonalExtendedBulkMinimalPhysicalTangent_metric]
    rfl
  rcases index with ⟨sector, row, column⟩
  cases sector
  · change continuousToCanonicalPhysicalBulkL2 period hPeriod
      (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        ((regularGeneralMetricC2VariationMatrix period hPeriod plusBase (direction.1.completeVariation.fullMetricPerturbation .minus) row column) -
          (regularGeneralMetricC2VariationMatrix period hPeriod plusBase (direction.1.completeVariation.fullMetricPerturbation .plus) row column))) = _
    rw [hMetric, hMetric, map_sub, map_sub, variationEntryL2, variationEntryL2]
    rfl
  · change continuousToCanonicalPhysicalBulkL2 period hPeriod
      (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (regularGeneralMetricC2VariationMatrix period hPeriod plusBase (direction.1.completeVariation.fullMetricPerturbation .plus) row column)) = _
    rw [hMetric, variationEntryL2]
    rfl

end
end P0EFTJanusProgramPT12InteractionBRSTMatrixReadout4D
end JanusFormal
