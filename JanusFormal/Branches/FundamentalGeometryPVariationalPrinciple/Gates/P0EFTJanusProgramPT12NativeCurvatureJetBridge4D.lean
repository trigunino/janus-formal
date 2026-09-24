import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CurvatureJetSymbol4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AffineHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMetricInvariantEinsteinVolumeCorrection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedEinsteinHilbertL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAllActionDerivatives4D

/-! Exact pointwise factorization of the installed native curvature through its finite jet. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12NativeCurvatureJetBridge4D

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

variable (metric : RegularGeneralLorentzMetric period hPeriod)
  (variation : RegularGeneralMetricC2Core period hPeriod metric)
  (point : EffectiveQuotient period hPeriod)

def nativeCurvatureJet : CurvatureJet :=
  (fun row column => regularGeneralMetricC0MetricCoefficient period hPeriod metric variation row column point,
   fun row column => regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric variation row column point,
   fun direction row column => regularGeneralMetricC0MetricFirstDerivative period hPeriod metric variation direction row column point,
   fun outer inner row column => regularGeneralMetricC0MetricSecondDerivative period hPeriod metric variation outer inner row column point)

def nativeFrameBracket : MetricFirstJet :=
  fun first second contracted => regularFrameStructureCoefficientContinuous period hPeriod metric first second contracted point

def nativeFrameBracketDerivative : MetricSecondJet :=
  fun direction first second contracted => regularFrameStructureCoefficientDerivativeContinuous
    period hPeriod metric direction first second contracted point

theorem nativeKoszul_eq_jet (first second lower : Fin 4) :
    regularGeneralMetricC0KoszulLower period hPeriod metric variation first second lower point =
    jetKoszul (nativeFrameBracket period hPeriod metric point) (nativeCurvatureJet period hPeriod metric variation point) first second lower := by
  simp only [regularGeneralMetricC0KoszulLower, jetKoszul,
    ContinuousMap.sum_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rfl

theorem nativeInverseDerivative_eq_jet (direction upper lower : Fin 4) :
    regularGeneralMetricC0InverseMetricDerivative period hPeriod metric variation direction upper lower point =
    jetInverseDerivative (nativeCurvatureJet period hPeriod metric variation point) direction upper lower := by
  simp only [regularGeneralMetricC0InverseMetricDerivative, jetInverseDerivative,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.neg_apply]
  rfl

theorem nativeStructureDerivative_eq_jet (direction first second contracted row column : Fin 4) :
    regularFrameStructureMetricDerivativeTerm period hPeriod metric variation direction first second contracted row column point =
    jetStructureDerivative (nativeFrameBracket period hPeriod metric point) (nativeFrameBracketDerivative period hPeriod metric point) (nativeCurvatureJet period hPeriod metric variation point) direction first second contracted row column := by
  simp only [regularFrameStructureMetricDerivativeTerm, jetStructureDerivative,
    ContinuousMap.add_apply, ContinuousMap.mul_apply]
  rfl

theorem nativeKoszulDerivative_eq_jet (direction first second lower : Fin 4) :
    regularGeneralMetricC0KoszulLowerDerivative period hPeriod metric variation direction first second lower point =
    jetKoszulDerivative (nativeFrameBracket period hPeriod metric point) (nativeFrameBracketDerivative period hPeriod metric point) (nativeCurvatureJet period hPeriod metric variation point) direction first second lower := by
  simp only [regularGeneralMetricC0KoszulLowerDerivative, jetKoszulDerivative,
    ContinuousMap.sum_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul, nativeStructureDerivative_eq_jet]
  rfl

theorem nativeChristoffel_eq_jet (upper first second : Fin 4) :
    regularGeneralMetricC0Christoffel period hPeriod metric variation upper first second point =
    jetChristoffel (nativeFrameBracket period hPeriod metric point) (nativeCurvatureJet period hPeriod metric variation point) upper first second := by
  simp only [regularGeneralMetricC0Christoffel, jetChristoffel,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply, nativeKoszul_eq_jet]
  rfl

theorem nativeChristoffelDerivative_eq_jet (direction upper first second : Fin 4) :
    regularGeneralMetricC0ChristoffelDerivative period hPeriod metric variation direction upper first second point =
    jetChristoffelDerivative (nativeFrameBracket period hPeriod metric point) (nativeFrameBracketDerivative period hPeriod metric point) (nativeCurvatureJet period hPeriod metric variation point) direction upper first second := by
  simp only [regularGeneralMetricC0ChristoffelDerivative, jetChristoffelDerivative,
    ContinuousMap.sum_apply, ContinuousMap.add_apply, ContinuousMap.mul_apply, nativeInverseDerivative_eq_jet, nativeKoszul_eq_jet, nativeKoszulDerivative_eq_jet]
  rfl

theorem nativeRiemann_eq_jet (upper lower first second : Fin 4) :
    regularGeneralMetricC0Riemann period hPeriod metric variation upper lower first second point =
    jetRiemann (nativeFrameBracket period hPeriod metric point) (nativeFrameBracketDerivative period hPeriod metric point) (nativeCurvatureJet period hPeriod metric variation point) upper lower first second := by
  simp only [regularGeneralMetricC0Riemann, jetRiemann,
    ContinuousMap.sum_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.mul_apply, nativeChristoffelDerivative_eq_jet, nativeChristoffel_eq_jet]
  rfl

theorem nativeRicci_eq_jet (first second : Fin 4) :
    regularGeneralMetricC0Ricci period hPeriod metric variation first second point =
    jetRicci (nativeFrameBracket period hPeriod metric point) (nativeFrameBracketDerivative period hPeriod metric point) (nativeCurvatureJet period hPeriod metric variation point) first second := by
  simp only [regularGeneralMetricC0Ricci, jetRicci,
    ContinuousMap.sum_apply, nativeRiemann_eq_jet]

theorem nativeScalarCurvature_eq_jet :
    regularGeneralMetricC0ScalarCurvature period hPeriod metric variation  point =
    jetScalarCurvature (nativeFrameBracket period hPeriod metric point) (nativeFrameBracketDerivative period hPeriod metric point) (nativeCurvatureJet period hPeriod metric variation point)  := by
  simp only [regularGeneralMetricC0ScalarCurvature, jetScalarCurvature,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply, nativeRicci_eq_jet]
  rfl

end
end P0EFTJanusProgramPT12NativeCurvatureJetBridge4D
end JanusFormal
