import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InteractionGradientLocality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongInteractionHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12C2RootPointwiseLocality4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12InteractionHessianLocality4D

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

private theorem c2FiniteMatrixValueAt_neg
    (matrix : C2FiniteMatrix period hPeriod 4)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4 (-matrix) point =
      -c2FiniteMatrixValueAt period hPeriod 4 matrix point := rfl

open P0EFTJanusProgramPT12InteractionGradientLocality4D
open P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotentialDerivative4D

private theorem evaluatedHessian_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (field : E → F) (linear : F →L[Real] Real) (base first test : E)
    (hC2 : ContDiffAt Real 2 field base)
    (hNear : (fun current => linear (fderiv Real field current test)) =ᶠ[𝓝 base]
      (fun _ => (0 : Real))) :
    linear (fderiv Real (fderiv Real field) base first test) = 0 := by
  have hSecond := (hC2.fderiv_right
    (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hDerivative := linear.hasFDerivAt.comp base
    (hSecond.hasFDerivAt.clm_apply (hasFDerivAt_const test base))
  have hZero : fderiv Real (fun current => linear (fderiv Real field current test)) base = 0 := by
    rw [hNear.fderiv_eq, fderiv_const_apply]
  have h := congrArg (fun derivative : E →L[Real] Real => derivative first)
    (hDerivative.fderiv.symm.trans hZero)
  simpa only [ContinuousLinearMap.comp_apply, add_apply, zero_apply, map_zero,
    zero_add, ContinuousLinearMap.flip_apply] using h

/-- The actual density Hessian has no dependence on spatial derivatives of its test. -/
theorem interactionDensityHessian_valueAt_zero
    (core first test : RelativeCore period hPeriod plusBase minusBase)
    (point : EffectiveQuotient period hPeriod)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (hPlus : c2FiniteMatrixValueAt period hPeriod 4 test.2.1 point = 0)
    (hCross : c2FiniteMatrixValueAt period hPeriod 4 test.2.2 point = 0) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (fderiv Real (fderiv Real (regularGeneralMetricC2PairedInteractionC2Density
        period hPeriod plusBase minusBase couplings.interactionScale couplings.interactionCoefficients))
        core first test) point = 0 := by
  let density := regularGeneralMetricC2PairedInteractionC2Density
    period hPeriod plusBase minusBase couplings.interactionScale couplings.interactionCoefficients
  have hOpen := regularGeneralMetricC2PairedLorentzMatrixDomain_isOpen period hPeriod plusBase minusBase
  have hC2 : ContDiffAt Real 2 density core :=
    (regularGeneralMetricC2PairedInteractionC2Density_contDiffOn period hPeriod plusBase minusBase
      couplings.interactionScale couplings.interactionCoefficients).contDiffAt (hOpen.mem_nhds hCore)
  apply evaluatedHessian_zero density (c2ScalarValueAtCLM period hPeriod point) core first test hC2
  filter_upwards [hOpen.mem_nhds hCore] with current hCurrent
  have hDerivative := regularGeneralMetricC2PairedInteractionC2Density_hasFDerivAt
    period hPeriod plusBase minusBase couplings.interactionScale couplings.interactionCoefficients current hCurrent
  change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (fderiv Real density current test) point = 0
  rw [hDerivative.fderiv]
  exact interactionDensityDerivative_valueAt_zero period hPeriod plusBase minusBase current test point
    hCurrent hPlus hCross

end
end P0EFTJanusProgramPT12InteractionHessianLocality4D
end JanusFormal
