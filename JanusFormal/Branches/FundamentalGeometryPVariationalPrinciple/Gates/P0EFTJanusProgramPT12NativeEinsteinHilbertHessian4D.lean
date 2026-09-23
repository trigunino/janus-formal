import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AffineHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMetricInvariantEinsteinVolumeCorrection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedEinsteinHilbertL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAllActionDerivatives4D

/-! Native fixed-volume gravity Hessian and its exact paired metric pullbacks. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12NativeEinsteinHilbertHessian4D

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

theorem nativeEinsteinHilbertAction_contDiffAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) (couplings : EinsteinHilbertCouplings) :
    ContDiffAt Real 2 (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod
      metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings) 0 :=
  (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_contDiffOn_two period hPeriod metric
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings).contDiffAt
    ((regularGeneralMetricC2Domain_isOpen period hPeriod metric).mem_nhds
      (zero_mem_regularGeneralMetricC2Domain period hPeriod metric))

def nativeEinsteinHilbertHessian (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      RegularGeneralMetricC2Core period hPeriod metric →L[Real] Real :=
  fderiv Real (fderiv Real (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod
    metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings)) 0

theorem nativeEinsteinHilbertHessian_symmetric
    (metric : RegularGeneralLorentzMetric period hPeriod) (couplings : EinsteinHilbertCouplings)
    (first second : RegularGeneralMetricC2Core period hPeriod metric) :
    nativeEinsteinHilbertHessian period hPeriod metric couplings first second =
      nativeEinsteinHilbertHessian period hPeriod metric couplings second first :=
  (nativeEinsteinHilbertAction_contDiffAt_zero period hPeriod metric couplings).isSymmSndFDerivAt
    (by norm_num) first second

def pairedEinsteinPlusProjection (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase →L[Real]
      RegularGeneralMetricC2Core period hPeriod plusBase :=
  (ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.fst Real _ _)

def pairedEinsteinMinusProjection (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase →L[Real]
      RegularGeneralMetricC2Core period hPeriod minusBase :=
  (ContinuousLinearMap.snd Real _ _).comp (ContinuousLinearMap.fst Real _ _)

theorem pairedEinsteinPlusAction_eq_composition
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) (couplings : EinsteinHilbertCouplings) :
    regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction period hPeriod plusBase minusBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings =
    (fun point => regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod plusBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings
      (pairedEinsteinPlusProjection period hPeriod plusBase minusBase point)) := rfl

theorem pairedEinsteinPlusAction_contDiffAt_zero
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) (couplings : EinsteinHilbertCouplings) :
    ContDiffAt Real 2 (regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction
      period hPeriod plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings) 0 := by
  rw [pairedEinsteinPlusAction_eq_composition]
  simpa only [map_zero, Function.comp_def] using
    (nativeEinsteinHilbertAction_contDiffAt_zero period hPeriod plusBase couplings).comp
      (0 : RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase)
      (pairedEinsteinPlusProjection period hPeriod plusBase minusBase).contDiff.contDiffAt

theorem pairedEinsteinPlusHessian_eq_native
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) (couplings : EinsteinHilbertCouplings)
    (first second : RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase) :
    fderiv Real (fderiv Real (regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction
      period hPeriod plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings))
      0 first second = nativeEinsteinHilbertHessian period hPeriod plusBase couplings
        (pairedEinsteinPlusProjection period hPeriod plusBase minusBase first)
        (pairedEinsteinPlusProjection period hPeriod plusBase minusBase second) := by
  have hEq := pairedEinsteinPlusAction_eq_composition period hPeriod plusBase minusBase couplings
  refine (congrArg (fun action : RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase → Real =>
    fderiv Real (fderiv Real action) 0 first second) hEq).trans ?_
  simpa only [one_mul, zero_add, nativeEinsteinHilbertHessian] using scaledAffineHessian
    (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod plusBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings) 0
    (pairedEinsteinPlusProjection period hPeriod plusBase minusBase) 1
    (nativeEinsteinHilbertAction_contDiffAt_zero period hPeriod plusBase couplings) first second

theorem pairedEinsteinMinusAction_eq_composition
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) (couplings : EinsteinHilbertCouplings) :
    regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction period hPeriod plusBase minusBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings =
    (fun point => regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod minusBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings
      (pairedEinsteinMinusProjection period hPeriod plusBase minusBase point)) := rfl

theorem pairedEinsteinMinusAction_contDiffAt_zero
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) (couplings : EinsteinHilbertCouplings) :
    ContDiffAt Real 2 (regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction
      period hPeriod plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings) 0 := by
  rw [pairedEinsteinMinusAction_eq_composition]
  simpa only [map_zero, Function.comp_def] using
    (nativeEinsteinHilbertAction_contDiffAt_zero period hPeriod minusBase couplings).comp
      (0 : RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase)
      (pairedEinsteinMinusProjection period hPeriod plusBase minusBase).contDiff.contDiffAt

theorem pairedEinsteinMinusHessian_eq_native
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) (couplings : EinsteinHilbertCouplings)
    (first second : RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase) :
    fderiv Real (fderiv Real (regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction
      period hPeriod plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings))
      0 first second = nativeEinsteinHilbertHessian period hPeriod minusBase couplings
        (pairedEinsteinMinusProjection period hPeriod plusBase minusBase first)
        (pairedEinsteinMinusProjection period hPeriod plusBase minusBase second) := by
  have hEq := pairedEinsteinMinusAction_eq_composition period hPeriod plusBase minusBase couplings
  refine (congrArg (fun action : RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase → Real =>
    fderiv Real (fderiv Real action) 0 first second) hEq).trans ?_
  simpa only [one_mul, zero_add, nativeEinsteinHilbertHessian] using scaledAffineHessian
    (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod minusBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings) 0
    (pairedEinsteinMinusProjection period hPeriod plusBase minusBase) 1
    (nativeEinsteinHilbertAction_contDiffAt_zero period hPeriod minusBase couplings) first second

end
end P0EFTJanusProgramPT12NativeEinsteinHilbertHessian4D
end JanusFormal
