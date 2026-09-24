import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeCurvatureJetHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeEinsteinHilbertHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeCurvatureJetBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NonlinearHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CurvatureJetSymbol4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AffineHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMetricInvariantEinsteinVolumeCorrection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedEinsteinHilbertL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAllActionDerivatives4D

/-! The actual fixed-volume Einstein--Hilbert Hessian is the integral of its finite-jet chain rule. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12EinsteinJetHessianIntegral4D

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
open P0EFTJanusProgramPT12NativeEinsteinHilbertHessian4D

private theorem linearPostHessian {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F] (linear : F →L[Real] Real)
    (field : E → F) (point first second : E) (hField : ContDiffAt Real 2 field point) :
    fderiv Real (fderiv Real (linear ∘ field)) point first second =
      linear (fderiv Real (fderiv Real field) point first second) := by
  have hConstant : fderiv Real (linear : F → Real) = fun _ => linear :=
    funext fun _ => linear.fderiv
  simpa only [hConstant, fderiv_const_apply, zero_apply, zero_add] using
    nonlinearHessian linear field point first second linear.contDiff.contDiffAt hField

variable (metric : RegularGeneralLorentzMetric period hPeriod) (couplings : EinsteinHilbertCouplings)

def jetEinsteinDensity (point : EffectiveQuotient period hPeriod) (jet : CurvatureJet) : Real :=
  metric.volume point * ((1 / (2 * couplings.gravitationalCoupling)) *
    (jetScalarCurvature (nativeFrameBracket period hPeriod metric point)
      (nativeFrameBracketDerivative period hPeriod metric point) jet - 2 * couplings.cosmologicalConstant))

theorem jetEinsteinDensity_contDiff (point : EffectiveQuotient period hPeriod) :
    ContDiff Real ∞ (jetEinsteinDensity period hPeriod metric couplings point) := by
  exact contDiff_const.mul (contDiff_const.mul ((jetScalarCurvature_contDiff _ _).sub contDiff_const))

theorem nativeEinsteinDensity_eq_jet
    (variation : RegularGeneralMetricC2Core period hPeriod metric) (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity period hPeriod metric couplings variation point =
      jetEinsteinDensity period hPeriod metric couplings point
        (nativeCurvatureJet period hPeriod metric variation point) := by
  change metric.volume point * ((1 / (2 * couplings.gravitationalCoupling)) *
    (regularGeneralMetricC0ScalarCurvature period hPeriod metric variation point - 2 * couplings.cosmologicalConstant)) = _
  rw [nativeScalarCurvature_eq_jet]
  rfl

/-- Includes the second parameter derivative of the actual inverse-metric slot. -/
def nativeEinsteinJetHessianDensity
    (first second : RegularGeneralMetricC2Core period hPeriod metric) (point : EffectiveQuotient period hPeriod) : Real :=
  fderiv Real (fderiv Real (jetEinsteinDensity period hPeriod metric couplings point))
    (nativeCurvatureJet period hPeriod metric 0 point)
    (fderiv Real (fun variation => nativeCurvatureJet period hPeriod metric variation point) 0 first)
    (fderiv Real (fun variation => nativeCurvatureJet period hPeriod metric variation point) 0 second) +
  fderiv Real (jetEinsteinDensity period hPeriod metric couplings point)
    (nativeCurvatureJet period hPeriod metric 0 point)
    (fderiv Real (fderiv Real (fun variation => nativeCurvatureJet period hPeriod metric variation point)) 0 first second)

theorem nativeEinsteinDensity_hessian_eq_jet
    (first second : RegularGeneralMetricC2Core period hPeriod metric) (point : EffectiveQuotient period hPeriod) :
    fderiv Real (fderiv Real (fun variation =>
      regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity period hPeriod metric couplings variation point))
      0 first second = nativeEinsteinJetHessianDensity period hPeriod metric couplings first second point := by
  have hEq : (fun variation =>
      regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity period hPeriod metric couplings variation point) =
      (jetEinsteinDensity period hPeriod metric couplings point) ∘
        (fun variation => nativeCurvatureJet period hPeriod metric variation point) := by
    funext variation
    exact nativeEinsteinDensity_eq_jet period hPeriod metric couplings variation point
  refine (congrArg (fun action : RegularGeneralMetricC2Core period hPeriod metric → Real =>
    fderiv Real (fderiv Real action) 0 first second) hEq).trans ?_
  exact nonlinearHessian _ _ 0 first second
    ((jetEinsteinDensity_contDiff period hPeriod metric couplings point).contDiffAt.of_le (by decide))
    ((nativeCurvatureJet_contDiffAt_zero period hPeriod metric point).of_le (by decide))

/-- Integration commutes with the second derivative via the existing continuous integral map. -/
theorem nativeEinsteinHilbertHessian_eq_jetIntegral
    (first second : RegularGeneralMetricC2Core period hPeriod metric) :
    nativeEinsteinHilbertHessian period hPeriod metric couplings first second =
    ∫ point, nativeEinsteinJetHessianDensity period hPeriod metric couplings first second point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  let density := regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity period hPeriod metric couplings
  have hDensity : ContDiffAt Real 2 density 0 :=
    (regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity_contDiffOn_two period hPeriod metric couplings).contDiffAt
      ((regularGeneralMetricC2Domain_isOpen period hPeriod metric).mem_nhds
        (zero_mem_regularGeneralMetricC2Domain period hPeriod metric))
  have hIntegral := linearPostHessian
    (regularGeneralMetricC0IntegralCLM period hPeriod (intrinsicCanonicalLorentzVolumeMeasure period hPeriod))
    density 0 first second hDensity
  change nativeEinsteinHilbertHessian period hPeriod metric couplings first second = _ at hIntegral
  rw [hIntegral, regularGeneralMetricC0IntegralCLM_apply]
  apply integral_congr_ae
  filter_upwards [] with point
  let evaluation : C(EffectiveQuotient period hPeriod, Real) →L[Real] Real := ContinuousMap.evalCLM Real point
  exact (linearPostHessian evaluation density 0 first second hDensity).symm.trans
    (nativeEinsteinDensity_hessian_eq_jet period hPeriod metric couplings first second point)

end
end P0EFTJanusProgramPT12EinsteinJetHessianIntegral4D
end JanusFormal
