import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeCurvatureJetBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NonlinearHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CurvatureJetSymbol4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AffineHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMetricInvariantEinsteinVolumeCorrection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedEinsteinHilbertL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAllActionDerivatives4D

/-! Native curvature second variation through the finite polynomial and actual metric jet. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12NativeCurvatureJetHessian4D

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

variable (metric : RegularGeneralLorentzMetric period hPeriod)
  (point : EffectiveQuotient period hPeriod)

theorem nativeCurvatureJet_contDiffAt_zero :
    ContDiffAt Real ∞ (fun variation => nativeCurvatureJet period hPeriod metric variation point) 0 := by
  have hEval (field : RegularGeneralMetricC2Core period hPeriod metric → C(EffectiveQuotient period hPeriod, Real))
      (h : ContDiffAt Real ∞ field 0) : ContDiffAt Real ∞ (fun variation => field variation point) 0 := by
    let evaluation : C(EffectiveQuotient period hPeriod, Real) →L[Real] Real := ContinuousMap.evalCLM Real point
    exact evaluation.contDiff.contDiffAt.comp 0 h
  have hValue (row column : Fin 4) := hEval _
    (regularGeneralMetricC0MetricCoefficient_contDiff period hPeriod metric row column).contDiffAt
  have hInverse (row column : Fin 4) := hEval _
    ((regularGeneralMetricC0InverseMetricCoefficient_contDiffOn period hPeriod metric row column).contDiffAt
      ((regularGeneralMetricC2Domain_isOpen period hPeriod metric).mem_nhds
        (zero_mem_regularGeneralMetricC2Domain period hPeriod metric)))
  have hFirst (direction row column : Fin 4) := hEval _
    (regularGeneralMetricC0MetricFirstDerivative_contDiff period hPeriod metric direction row column).contDiffAt
  have hSecond (outer inner row column : Fin 4) := hEval _
    (regularGeneralMetricC0MetricSecondDerivative_contDiff period hPeriod metric outer inner row column).contDiffAt
  exact (contDiffAt_pi.mpr fun row => contDiffAt_pi.mpr fun column => hValue row column).prodMk
    ((contDiffAt_pi.mpr fun row => contDiffAt_pi.mpr fun column => hInverse row column).prodMk
      ((contDiffAt_pi.mpr fun direction => contDiffAt_pi.mpr fun row => contDiffAt_pi.mpr
        fun column => hFirst direction row column).prodMk
        (contDiffAt_pi.mpr fun outer => contDiffAt_pi.mpr fun inner => contDiffAt_pi.mpr
          fun row => contDiffAt_pi.mpr fun column => hSecond outer inner row column)))

/-- Exact second variation: finite curvature Hessian plus the nonlinear jet acceleration. -/
theorem nativeScalarCurvature_hessian_eq_jet
    (first second : RegularGeneralMetricC2Core period hPeriod metric) :
    fderiv Real (fderiv Real (fun variation =>
      regularGeneralMetricC0ScalarCurvature period hPeriod metric variation point)) 0 first second =
    fderiv Real (fderiv Real (jetScalarCurvature
      (nativeFrameBracket period hPeriod metric point) (nativeFrameBracketDerivative period hPeriod metric point)))
      (nativeCurvatureJet period hPeriod metric 0 point)
      (fderiv Real (fun variation => nativeCurvatureJet period hPeriod metric variation point) 0 first)
      (fderiv Real (fun variation => nativeCurvatureJet period hPeriod metric variation point) 0 second) +
    fderiv Real (jetScalarCurvature
      (nativeFrameBracket period hPeriod metric point) (nativeFrameBracketDerivative period hPeriod metric point))
      (nativeCurvatureJet period hPeriod metric 0 point)
      (fderiv Real (fderiv Real (fun variation => nativeCurvatureJet period hPeriod metric variation point))
        0 first second) := by
  have hEq : (fun variation => regularGeneralMetricC0ScalarCurvature period hPeriod metric variation point) =
      (jetScalarCurvature (nativeFrameBracket period hPeriod metric point)
        (nativeFrameBracketDerivative period hPeriod metric point)) ∘
      (fun variation => nativeCurvatureJet period hPeriod metric variation point) := by
    funext variation
    exact nativeScalarCurvature_eq_jet period hPeriod metric variation point
  refine (congrArg (fun action : RegularGeneralMetricC2Core period hPeriod metric → Real =>
    fderiv Real (fderiv Real action) 0 first second) hEq).trans ?_
  exact nonlinearHessian _ _ 0 first second
    ((jetScalarCurvature_contDiff _ _).contDiffAt.of_le (by decide))
    ((nativeCurvatureJet_contDiffAt_zero period hPeriod metric point).of_le (by decide))

end
end P0EFTJanusProgramPT12NativeCurvatureJetHessian4D
end JanusFormal
