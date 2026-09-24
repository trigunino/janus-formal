import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeCurvatureJetHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CurvatureJetDifferentials4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InverseMetricHessianPointwise4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MetricJetAcceleration4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeCurvatureJetBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NonlinearHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CurvatureJetSymbol4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AffineHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMetricInvariantEinsteinVolumeCorrection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedEinsteinHilbertL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAllActionDerivatives4D

/-! Explicit acceleration of the complete native curvature jet. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12NativeCurvatureJetAcceleration4D

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothSymmetricEinsteinTensor4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongInteractionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
open P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAllActionDerivatives4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
attribute [local instance 1900]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedAddCommGroup
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace

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
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPT12AffineHessianPullback4D

open P0EFTJanusProgramPT12CurvatureJetSymbol4D

open P0EFTJanusProgramPT12NativeCurvatureJetBridge4D
open P0EFTJanusProgramPT12NonlinearHessianPullback4D

open P0EFTJanusProgramPT12NativeCurvatureJetHessian4D
open P0EFTJanusProgramPT12CurvatureJetDifferentials4D
open P0EFTJanusProgramPT12VectorHessianPullback4D
open P0EFTJanusProgramPT12InverseMetricHessianPointwise4D
open P0EFTJanusProgramPT12MetricJetAcceleration4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityPointwise4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D

private theorem evaluation_hessian_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (field : RegularGeneralMetricC2Core period hPeriod metric → C(EffectiveQuotient period hPeriod, Real))
    (first second : RegularGeneralMetricC2Core period hPeriod metric) (point : EffectiveQuotient period hPeriod)
    (hC2 : ContDiffAt Real 2 field 0)
    (hZero : fderiv Real (fderiv Real field) 0 first second = 0) :
    fderiv Real (fderiv Real (fun variation => field variation point)) 0 first second = 0 := by
  let evaluation : C(EffectiveQuotient period hPeriod, Real) →L[Real] Real := ContinuousMap.evalCLM Real point
  change fderiv Real (fderiv Real (evaluation ∘ field)) 0 first second = 0
  rw [linearPostHessian evaluation field 0 first second hC2, hZero, map_zero]

def nativeCurvatureJetAcceleration (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : RegularGeneralMetricC2Core period hPeriod metric) (point : EffectiveQuotient period hPeriod) : CurvatureJet :=
  let firstAt := regularGeneralMetricC2RelativeMatrixAt period hPeriod metric first point
  let secondAt := regularGeneralMetricC2RelativeMatrixAt period hPeriod metric second point
  (0, fun row column => ((secondAt * firstAt + firstAt * secondAt) *
    regularFrameMetricInverseMatrixMap period hPeriod metric point) row column, 0, 0)

theorem nativeCurvatureJet_hessian_explicit (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : RegularGeneralMetricC2Core period hPeriod metric) (point : EffectiveQuotient period hPeriod) :
    fderiv Real (fderiv Real (fun variation => nativeCurvatureJet period hPeriod metric variation point))
      0 first second = nativeCurvatureJetAcceleration period hPeriod metric first second point := by
  rw [curvatureJet_hessian _ 0 first second
    ((nativeCurvatureJet_contDiffAt_zero period hPeriod metric point).of_le (by decide))]
  apply Prod.ext
  · funext row column
    exact evaluation_hessian_zero period hPeriod metric _ first second point
      ((regularGeneralMetricC0MetricCoefficient_contDiff period hPeriod metric row column).contDiffAt.of_le (by decide))
      (nativeMetricCoefficient_hessian_zero period hPeriod metric first second row column)
  apply Prod.ext
  · funext row column
    exact nativeInverseCoefficient_hessian_pointwise period hPeriod metric first second point row column
  apply Prod.ext
  · funext direction row column
    exact evaluation_hessian_zero period hPeriod metric _ first second point
      ((regularGeneralMetricC0MetricFirstDerivative_contDiff period hPeriod metric direction row column).contDiffAt.of_le (by decide))
      (nativeMetricFirstJet_hessian_zero period hPeriod metric first second direction row column)
  · funext outer inner row column
    exact evaluation_hessian_zero period hPeriod metric _ first second point
      ((regularGeneralMetricC0MetricSecondDerivative_contDiff period hPeriod metric outer inner row column).contDiffAt.of_le (by decide))
      (nativeMetricSecondJet_hessian_zero period hPeriod metric first second outer inner row column)

def smoothCurvatureJetAcceleration (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) (point : EffectiveQuotient period hPeriod) : CurvatureJet :=
  let inverse := regularFrameMetricInverseMatrixMap period hPeriod metric point
  let firstAt := regularFrameCovariantVariationMatrixAt period hPeriod metric first point
  let secondAt := regularFrameCovariantVariationMatrixAt period hPeriod metric second point
  (0, fun row column => (((inverse * secondAt) * (inverse * firstAt) +
    (inverse * firstAt) * (inverse * secondAt)) * inverse) row column, 0, 0)

theorem nativeCurvatureJet_hessian_smooth (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) (point : EffectiveQuotient period hPeriod) :
    fderiv Real (fderiv Real (fun variation => nativeCurvatureJet period hPeriod metric variation point)) 0
      (regularGeneralMetricC2SmoothDirection period hPeriod metric first)
      (regularGeneralMetricC2SmoothDirection period hPeriod metric second) =
      smoothCurvatureJetAcceleration period hPeriod metric first second point := by
  rw [nativeCurvatureJet_hessian_explicit]
  simp only [nativeCurvatureJetAcceleration, regularGeneralMetricC2RelativeMatrixAt_smooth,
    smoothCurvatureJetAcceleration]

end
end P0EFTJanusProgramPT12NativeCurvatureJetAcceleration4D
end JanusFormal
