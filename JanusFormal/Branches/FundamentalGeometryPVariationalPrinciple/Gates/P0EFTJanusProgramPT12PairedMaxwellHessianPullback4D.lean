import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AffineHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellNativeMixedHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMaxwellCenterFirstVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MixedPartialHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellMixedMetricL24D
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FullMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellCoefficientQuadratic4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12QuadraticParameterDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellStressCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InducedMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorCovectorL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStrongMaxwellMetricResidual4D

/-! Exact native Hessian pullbacks for the actual paired Maxwell action blocks. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12PairedMaxwellHessianPullback4D

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

/-- Joint plus projection before translation by the physical gauge background. -/
def pairedMaxwellPlusProjection :
    RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase →L[Real]
      RegularGeneralMetricC2Core period hPeriod plusBase × RegularGeneralMetricC2GaugeCoefficientCore period hPeriod :=
  ((ContinuousLinearMap.fst Real _ _).comp
    ((ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.fst Real _ _))).prod
    ((ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.snd Real _ _))

def pairedMaxwellMinusProjection :
    RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase →L[Real]
      RegularGeneralMetricC2Core period hPeriod minusBase × RegularGeneralMetricC2GaugeCoefficientCore period hPeriod :=
  ((ContinuousLinearMap.snd Real _ _).comp
    ((ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.fst Real _ _))).prod
    ((ContinuousLinearMap.snd Real _ _).comp (ContinuousLinearMap.snd Real _ _))

theorem pairedMaxwellPlusProjection_apply
    (core : RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase) :
    pairedMaxwellPlusProjection period hPeriod plusBase minusBase core = (core.1.1.1, core.2.1) := rfl

theorem pairedMaxwellMinusProjection_apply
    (core : RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase) :
    pairedMaxwellMinusProjection period hPeriod plusBase minusBase core = (core.1.1.2, core.2.2) := rfl

/-- Reconstructed physical background gives exactly the stored completed coefficients. -/
theorem maxwellSmoothGaugeC2_reconstructed
    (base : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    maxwellSmoothGaugeC2 period hPeriod base
      (regularFrameGaugePotentialFromCoefficients period hPeriod base coefficients) =
      smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients := by
  unfold maxwellSmoothGaugeC2
  change smoothGaugeCoefficientC2CoreLinearMap period hPeriod
    (gaugePotentialFrameCoefficients period hPeriod base
      (regularFrameGaugePotentialFromCoefficients period hPeriod base coefficients)) = _
  rw [gaugePotentialFrameCoefficients_reconstructed]

attribute [local irreducible] nativeMobileMaxwellAction nativeMobileMaxwellHessian
  regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction
  regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction

theorem pairedPlusMaxwellAction_eq_affine
    (core : RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase) :
    regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction period hPeriod configuration
      plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) core =
    nativeMobileMaxwellAction period hPeriod plusBase
      ((0, smoothGaugeCoefficientC2CoreLinearMap period hPeriod configuration.coefficientFields.gauge.1) +
        pairedMaxwellPlusProjection period hPeriod plusBase minusBase core) := by
  unfold nativeMobileMaxwellAction regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction
  simp only [pairedMaxwellPlusProjection_apply, Prod.mk_add_mk, zero_add]
  rfl

theorem pairedMinusMaxwellAction_eq_affine
    (core : RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase) :
    regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction period hPeriod configuration
      plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) core =
    nativeMobileMaxwellAction period hPeriod minusBase
      ((0, smoothGaugeCoefficientC2CoreLinearMap period hPeriod configuration.coefficientFields.gauge.2) +
        pairedMaxwellMinusProjection period hPeriod plusBase minusBase core) := by
  unfold nativeMobileMaxwellAction regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction
  simp only [pairedMaxwellMinusProjection_apply, Prod.mk_add_mk, zero_add]
  rfl
attribute [local irreducible] canonicalPhysicalScalarC2JetCoreSubmodule
  P0EFTJanusProgramPGeneralMetricC2OpenDomain4D.generalMetricRelativeC2CoreSubmodule
  pairedMaxwellPlusProjection pairedMaxwellMinusProjection maxwellSmoothGaugeC2

theorem pairedPlusMaxwellHessian_eq_native (scale : Real)
    (first second : RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase) :
    fderiv Real (fderiv Real (fun core => scale * regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction
      period hPeriod configuration plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) core))
      0 first second =
    scale * nativeMobileMaxwellHessian period hPeriod plusBase
      (regularFrameGaugePotentialFromCoefficients period hPeriod plusBase configuration.coefficientFields.gauge.1)
      (pairedMaxwellPlusProjection period hPeriod plusBase minusBase first)
      (pairedMaxwellPlusProjection period hPeriod plusBase minusBase second) := by
  let coefficients := smoothGaugeCoefficientC2CoreLinearMap period hPeriod configuration.coefficientFields.gauge.1
  have hEq : (fun core => scale * regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction
      period hPeriod configuration plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) core) =
      (fun core => scale * nativeMobileMaxwellAction period hPeriod plusBase
        ((0, coefficients) + pairedMaxwellPlusProjection period hPeriod plusBase minusBase core)) := by
    funext core
    exact congrArg (fun value => scale * value) (pairedPlusMaxwellAction_eq_affine period hPeriod configuration plusBase minusBase core)
  refine (congrArg (fun action : RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase → Real =>
    fderiv Real (fderiv Real action) 0 first second) hEq).trans ?_
  have hPull := scaledAffineHessian (nativeMobileMaxwellAction period hPeriod plusBase)
    (0, coefficients) (pairedMaxwellPlusProjection period hPeriod plusBase minusBase) scale
    (nativeMobileMaxwellAction_contDiffAt period hPeriod plusBase coefficients) first second
  refine hPull.trans ?_
  unfold nativeMobileMaxwellHessian
  rw [maxwellSmoothGaugeC2_reconstructed]

theorem pairedMinusMaxwellHessian_eq_native (scale : Real)
    (first second : RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase) :
    fderiv Real (fderiv Real (fun core => scale * regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction
      period hPeriod configuration plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) core))
      0 first second =
    scale * nativeMobileMaxwellHessian period hPeriod minusBase
      (regularFrameGaugePotentialFromCoefficients period hPeriod minusBase configuration.coefficientFields.gauge.2)
      (pairedMaxwellMinusProjection period hPeriod plusBase minusBase first)
      (pairedMaxwellMinusProjection period hPeriod plusBase minusBase second) := by
  let coefficients := smoothGaugeCoefficientC2CoreLinearMap period hPeriod configuration.coefficientFields.gauge.2
  have hEq : (fun core => scale * regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction
      period hPeriod configuration plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) core) =
      (fun core => scale * nativeMobileMaxwellAction period hPeriod minusBase
        ((0, coefficients) + pairedMaxwellMinusProjection period hPeriod plusBase minusBase core)) := by
    funext core
    exact congrArg (fun value => scale * value) (pairedMinusMaxwellAction_eq_affine period hPeriod configuration plusBase minusBase core)
  refine (congrArg (fun action : RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase → Real =>
    fderiv Real (fderiv Real action) 0 first second) hEq).trans ?_
  have hPull := scaledAffineHessian (nativeMobileMaxwellAction period hPeriod minusBase)
    (0, coefficients) (pairedMaxwellMinusProjection period hPeriod plusBase minusBase) scale
    (nativeMobileMaxwellAction_contDiffAt period hPeriod minusBase coefficients) first second
  refine hPull.trans ?_
  unfold nativeMobileMaxwellHessian
  rw [maxwellSmoothGaugeC2_reconstructed]

end
end P0EFTJanusProgramPT12PairedMaxwellHessianPullback4D
end JanusFormal
