import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeEinsteinJetCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12EinsteinSymbolJointSmooth4D
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

/-! Spatial smoothness of the actual inputs to the finite Einstein symbol. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12NativeJetSpatialSmooth4D

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

open P0EFTJanusProgramPT12NativeEinsteinJetCoefficients4D
open P0EFTJanusProgramPT12EinsteinSymbolJointSmooth4D
open P0EFTJanusMappingTorusH1GraphTrace4D

variable (metric : RegularGeneralLorentzMetric period hPeriod)

theorem nativeFrameBracket_contMDiff :
    ContMDiff coverModelWithCorners 𝓘(Real, MetricFirstJet) ∞ (nativeFrameBracket period hPeriod metric) := by
  apply contMDiff_pi_space.mpr; intro first
  apply contMDiff_pi_space.mpr; intro second
  apply contMDiff_pi_space.mpr; intro upper
  exact (regularFrameStructureCoefficient period hPeriod metric first second upper).contMDiff_toFun

theorem nativeFrameBracketDerivative_contMDiff :
    ContMDiff coverModelWithCorners 𝓘(Real, MetricSecondJet) ∞ (nativeFrameBracketDerivative period hPeriod metric) := by
  apply contMDiff_pi_space.mpr; intro direction
  apply contMDiff_pi_space.mpr; intro first
  apply contMDiff_pi_space.mpr; intro second
  apply contMDiff_pi_space.mpr; intro upper
  exact (frameDerivativeComponentField period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    (regularFrameStructureCoefficient period hPeriod metric first second upper) direction).contMDiff_toFun

theorem nativeInverseCoefficients_contMDiff :
    ContMDiff coverModelWithCorners 𝓘(Real, MetricMatrix) ∞
      (fun point row column => regularFrameMetricInverseMatrix period hPeriod metric row column point) := by
  apply contMDiff_pi_space.mpr; intro row
  apply contMDiff_pi_space.mpr; intro column
  exact (regularFrameMetricInverseMatrix period hPeriod metric row column).contMDiff_toFun

theorem nativeCurvatureJet_zero_contMDiff :
    ContMDiff coverModelWithCorners 𝓘(Real, CurvatureJet) ∞
      (fun point => nativeCurvatureJet period hPeriod metric 0 point) := by
  unfold nativeCurvatureJet
  simp only [regularGeneralMetricC0MetricCoefficient_zero_apply,
    regularGeneralMetricC0InverseMetricCoefficient_zero_apply,
    regularGeneralMetricC0MetricFirstDerivative_zero_apply,
    regularGeneralMetricC0MetricSecondDerivative_zero_apply]
  apply ContMDiff.prodMk_space
  · apply contMDiff_pi_space.mpr; intro row
    apply contMDiff_pi_space.mpr; intro column
    exact (regularFrameMetricMatrix period hPeriod metric row column).contMDiff_toFun
  apply ContMDiff.prodMk_space
  · exact nativeInverseCoefficients_contMDiff period hPeriod metric
  apply ContMDiff.prodMk_space
  · apply contMDiff_pi_space.mpr; intro direction
    apply contMDiff_pi_space.mpr; intro row
    apply contMDiff_pi_space.mpr; intro column
    exact (frameDerivativeComponentField period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (regularFrameMetricMatrix period hPeriod metric row column) direction).contMDiff_toFun
  · apply contMDiff_pi_space.mpr; intro outer
    apply contMDiff_pi_space.mpr; intro inner
    apply contMDiff_pi_space.mpr; intro row
    apply contMDiff_pi_space.mpr; intro column
    exact (frameDerivativeComponentField period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameMetricMatrix period hPeriod metric row column) inner) outer).contMDiff_toFun

theorem smoothMetricVariationJet_contMDiff (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ContMDiff coverModelWithCorners 𝓘(Real, MetricVariationJet) ∞
      (smoothMetricVariationJet period hPeriod metric tensor) := by
  apply ContMDiff.prodMk_space
  · apply contMDiff_pi_space.mpr; intro row
    apply contMDiff_pi_space.mpr; intro column
    have h : ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (fun point => regularFrameSmoothCovariantVariationCoefficient period hPeriod metric tensor row column point) :=
      (regularFrameSmoothCovariantVariationCoefficient period hPeriod metric tensor row column).contMDiff_toFun
    simpa only [regularFrameSmoothCovariantVariationCoefficient_apply, regularFrameCovariantVariationMatrixAt] using h
  apply ContMDiff.prodMk_space
  · apply contMDiff_pi_space.mpr; intro direction
    apply contMDiff_pi_space.mpr; intro row
    apply contMDiff_pi_space.mpr; intro column
    exact (regularFrameSmoothCovariantVariationFirstDerivative period hPeriod metric tensor direction row column).contMDiff_toFun
  · apply contMDiff_pi_space.mpr; intro outer
    apply contMDiff_pi_space.mpr; intro inner
    apply contMDiff_pi_space.mpr; intro row
    apply contMDiff_pi_space.mpr; intro column
    exact (regularFrameSmoothCovariantVariationSecondDerivative period hPeriod metric tensor outer inner row column).contMDiff_toFun

def nativeEinsteinSymbolInput (point : EffectiveQuotient period hPeriod) : EinsteinSymbolInput :=
  ((metric.volume point, nativeFrameBracket period hPeriod metric point,
    nativeFrameBracketDerivative period hPeriod metric point), nativeCurvatureJet period hPeriod metric 0 point)

theorem nativeEinsteinSymbolInput_contMDiff :
    ContMDiff coverModelWithCorners 𝓘(Real, EinsteinSymbolInput) ∞
      (nativeEinsteinSymbolInput period hPeriod metric) := by
  exact (metric.volume.contMDiff_toFun.prodMk_space
    ((nativeFrameBracket_contMDiff period hPeriod metric).prodMk_space
      (nativeFrameBracketDerivative_contMDiff period hPeriod metric))).prodMk_space
    (nativeCurvatureJet_zero_contMDiff period hPeriod metric)

end
end P0EFTJanusProgramPT12NativeJetSpatialSmooth4D
end JanusFormal
