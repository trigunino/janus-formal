import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeCurvatureJetVelocity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeCurvatureJetAcceleration4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MetricJetLinearization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12EinsteinJetHessianIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothMetricParameterJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2InverseVelocityPointwise4D
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

/-! Concrete coefficients of the native Einstein Hessian in the test metric jet. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12NativeEinsteinJetCoefficients4D

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

open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMetricParameterJet4D
open P0EFTJanusProgramPRegularGeneralMetricC2InverseVelocityPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D

open P0EFTJanusProgramPT12NativeCurvatureJetVelocity4D
open P0EFTJanusProgramPT12NativeCurvatureJetAcceleration4D
open P0EFTJanusProgramPT12MetricJetCovector4D
open P0EFTJanusProgramPT12MetricJetLinearization4D
open P0EFTJanusProgramPT12EinsteinJetHessianIntegral4D
open P0EFTJanusProgramPT12NativeEinsteinHilbertHessian4D

variable (metric : RegularGeneralLorentzMetric period hPeriod)

def smoothMetricVariationJet (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : MetricVariationJet :=
  (regularFrameCovariantVariationMatrixAt period hPeriod metric tensor point,
   fun direction row column => regularFrameSmoothCovariantVariationFirstDerivative
     period hPeriod metric tensor direction row column point,
   fun outer inner row column => regularFrameSmoothCovariantVariationSecondDerivative
     period hPeriod metric tensor outer inner row column point)

theorem metricJetVelocity_smooth (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    metricJetVelocity (regularFrameMetricInverseMatrixMap period hPeriod metric point)
      (smoothMetricVariationJet period hPeriod metric tensor point) =
      smoothCurvatureJetVelocity period hPeriod metric tensor point := rfl

theorem metricJetAcceleration_smooth (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    metricJetAcceleration (regularFrameMetricInverseMatrixMap period hPeriod metric point)
      (smoothMetricVariationJet period hPeriod metric first point)
      (smoothMetricVariationJet period hPeriod metric second point) =
      smoothCurvatureJetAcceleration period hPeriod metric first second point := rfl

variable (couplings : EinsteinHilbertCouplings)

def nativeEinsteinJetCovector (first : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : MetricVariationJet →L[Real] Real :=
  metricJetHessianCovector (regularFrameMetricInverseMatrixMap period hPeriod metric point)
    (fderiv Real (jetEinsteinDensity period hPeriod metric couplings point)
      (nativeCurvatureJet period hPeriod metric 0 point))
    (fderiv Real (fderiv Real (jetEinsteinDensity period hPeriod metric couplings point))
      (nativeCurvatureJet period hPeriod metric 0 point))
    (smoothMetricVariationJet period hPeriod metric first point)

theorem nativeEinsteinJetHessianDensity_eq_covector
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) (point : EffectiveQuotient period hPeriod) :
    nativeEinsteinJetHessianDensity period hPeriod metric couplings
      (regularGeneralMetricC2SmoothDirection period hPeriod metric first)
      (regularGeneralMetricC2SmoothDirection period hPeriod metric second) point =
      nativeEinsteinJetCovector period hPeriod metric couplings first point
        (smoothMetricVariationJet period hPeriod metric second point) := by
  unfold nativeEinsteinJetHessianDensity nativeEinsteinJetCovector
  rw [metricJetHessianCovector_apply, metricJetVelocity_smooth, metricJetVelocity_smooth,
    metricJetAcceleration_smooth, nativeCurvatureJet_fderiv_smooth, nativeCurvatureJet_fderiv_smooth,
    nativeCurvatureJet_hessian_smooth]

def nativeEinsteinJetValueCoefficient (first : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) (row column : Fin 4) : Real :=
  nativeEinsteinJetCovector period hPeriod metric couplings first point (valueBasis row column)

def nativeEinsteinJetFirstCoefficient (first : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) (direction row column : Fin 4) : Real :=
  nativeEinsteinJetCovector period hPeriod metric couplings first point (firstBasis direction row column)

def nativeEinsteinJetSecondCoefficient (first : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) (outer inner row column : Fin 4) : Real :=
  nativeEinsteinJetCovector period hPeriod metric couplings first point (secondBasis outer inner row column)

def nativeEinsteinJetCoefficientDensity (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  (∑ row, ∑ column, nativeEinsteinJetValueCoefficient period hPeriod metric couplings first point row column *
    second.tensor point (metric.frame row point) (metric.frame column point)) +
  (∑ direction, ∑ row, ∑ column, nativeEinsteinJetFirstCoefficient period hPeriod metric couplings first point direction row column *
    regularFrameSmoothCovariantVariationFirstDerivative period hPeriod metric second direction row column point) +
  (∑ outer, ∑ inner, ∑ row, ∑ column, nativeEinsteinJetSecondCoefficient period hPeriod metric couplings first point outer inner row column *
    regularFrameSmoothCovariantVariationSecondDerivative period hPeriod metric second outer inner row column point)

theorem nativeEinsteinJetHessianDensity_eq_coefficients
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) (point : EffectiveQuotient period hPeriod) :
    nativeEinsteinJetHessianDensity period hPeriod metric couplings
      (regularGeneralMetricC2SmoothDirection period hPeriod metric first)
      (regularGeneralMetricC2SmoothDirection period hPeriod metric second) point =
      nativeEinsteinJetCoefficientDensity period hPeriod metric couplings first second point := by
  rw [nativeEinsteinJetHessianDensity_eq_covector]
  exact metricJetCovector_apply _ _

theorem nativeEinsteinHilbertHessian_eq_coefficientsIntegral
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    nativeEinsteinHilbertHessian period hPeriod metric couplings
      (regularGeneralMetricC2SmoothDirection period hPeriod metric first)
      (regularGeneralMetricC2SmoothDirection period hPeriod metric second) =
      ∫ point, nativeEinsteinJetCoefficientDensity period hPeriod metric couplings first second point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [nativeEinsteinHilbertHessian_eq_jetIntegral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    nativeEinsteinJetHessianDensity_eq_coefficients period hPeriod metric couplings first second point

end
end P0EFTJanusProgramPT12NativeEinsteinJetCoefficients4D
end JanusFormal
