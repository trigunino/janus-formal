import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedMaxwellHessianPullback4D

namespace JanusFormal
namespace P0EFTJanusProgramPT12PairedMaxwellCenterC24D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D
open P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D
open P0EFTJanusFixedVolumeMaxwellStressResidual4D
open P0EFTJanusMetricInducedSmoothGaugeVelocity4D
open P0EFTJanusGaugeCoefficientMaxwellIntrinsicFirstVariation4D
open P0EFTJanusMetricInducedMaxwellResidual4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
@[reducible] local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
@[reducible] local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

open scoped InnerProductSpace
open P0EFTJanusProgramPT12RegularTensorCovectorL24D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusStrongMaxwellMetricResidual4D

variable (metric : RegularGeneralLorentzMetric period hPeriod)
  (potential : SmoothAbelianGaugePotential period hPeriod)

open P0EFTJanusProgramPT12MaxwellStressCoefficients4D
open P0EFTJanusProgramPT12InducedMaxwellMetricL24D

open P0EFTJanusProgramPT12FullMaxwellMetricL24D
open P0EFTJanusProgramPT12MaxwellCoefficientQuadratic4D
open P0EFTJanusProgramPT12QuadraticParameterDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D

open P0EFTJanusProgramPT12MixedPartialHessian4D
open P0EFTJanusProgramPT12MaxwellMixedMetricL24D

open P0EFTJanusProgramPT12AffineHessianPullback4D
open P0EFTJanusProgramPT12MaxwellNativeMixedHessian4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D

attribute [local instance 1900]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedAddCommGroup
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace

variable (configuration : GlobalFieldConfiguration period hPeriod)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

open P0EFTJanusProgramPT12PairedMaxwellHessianPullback4D

attribute [local irreducible] nativeMobileMaxwellAction
  regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction
  regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction
  pairedMaxwellPlusProjection pairedMaxwellMinusProjection
  canonicalPhysicalScalarC2JetCoreSubmodule
  P0EFTJanusProgramPGeneralMetricC2OpenDomain4D.generalMetricRelativeC2CoreSubmodule

theorem pairedPlusScaledMaxwellAction_contDiffAt_zero (scale : Real) :
    ContDiffAt Real 2 (fun core => scale * regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction
      period hPeriod configuration plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) core) 0 := by
  let coefficients := smoothGaugeCoefficientC2CoreLinearMap period hPeriod configuration.coefficientFields.gauge.1
  let projection := pairedMaxwellPlusProjection period hPeriod plusBase minusBase
  have hInput : ContDiffAt Real 2 (fun core => (0, coefficients) + projection core) 0 :=
    contDiffAt_const.add projection.contDiff.contDiffAt
  have hNative : ContDiffAt Real 2 (nativeMobileMaxwellAction period hPeriod plusBase)
      ((0, coefficients) + projection 0) := by
    simpa only [map_zero, add_zero] using
      nativeMobileMaxwellAction_contDiffAt period hPeriod plusBase coefficients
  have hComp := (contDiffAt_const (c := scale)).mul (hNative.comp 0 hInput)
  have hEq : (fun core => scale * regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction
      period hPeriod configuration plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) core) =
      (fun core => scale * nativeMobileMaxwellAction period hPeriod plusBase ((0, coefficients) + projection core)) := by
    funext core
    exact congrArg (fun value => scale * value)
      (pairedPlusMaxwellAction_eq_affine period hPeriod configuration plusBase minusBase core)
  exact (congrArg (fun action : RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase → Real =>
    ContDiffAt Real 2 action 0) hEq).mpr hComp
theorem pairedMinusScaledMaxwellAction_contDiffAt_zero (scale : Real) :
    ContDiffAt Real 2 (fun core => scale * regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction
      period hPeriod configuration plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) core) 0 := by
  let coefficients := smoothGaugeCoefficientC2CoreLinearMap period hPeriod configuration.coefficientFields.gauge.2
  let projection := pairedMaxwellMinusProjection period hPeriod plusBase minusBase
  have hInput : ContDiffAt Real 2 (fun core => (0, coefficients) + projection core) 0 :=
    contDiffAt_const.add projection.contDiff.contDiffAt
  have hNative : ContDiffAt Real 2 (nativeMobileMaxwellAction period hPeriod minusBase)
      ((0, coefficients) + projection 0) := by
    simpa only [map_zero, add_zero] using
      nativeMobileMaxwellAction_contDiffAt period hPeriod minusBase coefficients
  have hComp := (contDiffAt_const (c := scale)).mul (hNative.comp 0 hInput)
  have hEq : (fun core => scale * regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction
      period hPeriod configuration plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) core) =
      (fun core => scale * nativeMobileMaxwellAction period hPeriod minusBase ((0, coefficients) + projection core)) := by
    funext core
    exact congrArg (fun value => scale * value)
      (pairedMinusMaxwellAction_eq_affine period hPeriod configuration plusBase minusBase core)
  exact (congrArg (fun action : RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase → Real =>
    ContDiffAt Real 2 action 0) hEq).mpr hComp

end
end P0EFTJanusProgramPT12PairedMaxwellCenterC24D
end JanusFormal
