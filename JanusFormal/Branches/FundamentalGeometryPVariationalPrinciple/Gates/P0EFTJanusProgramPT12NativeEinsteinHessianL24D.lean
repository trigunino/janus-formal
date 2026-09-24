import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeEinsteinCoefficientFields4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12TensorSecondJetL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeJetSpatialSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MetricJetLinearizationSmooth4D
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

/-! Actual L2 representation and bound for the native Einstein Hessian. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12NativeEinsteinHessianL24D

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

open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPT12NativeJetSpatialSmooth4D
open P0EFTJanusProgramPT12MetricJetLinearizationSmooth4D

open P0EFTJanusProgramPT12NativeEinsteinCoefficientFields4D
open P0EFTJanusProgramPT12TensorSecondJetL24D
open P0EFTJanusProgramPT12RegularFrameSecondJetAdjoint4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusRegularFrameCanonicalFormalAdjoint4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open scoped BigOperators InnerProductSpace

private theorem sum_three_comm (f : Fin 4 → Fin 4 → Fin 4 → Real) :
    (∑ row, ∑ column, ∑ direction, f direction row column) =
      ∑ direction, ∑ row, ∑ column, f direction row column := by
  calc
    _ = ∑ row, ∑ direction, ∑ column, f direction row column := by
      apply Finset.sum_congr rfl
      intro row _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem sum_four_comm (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Real) :
    (∑ row, ∑ column, ∑ outer, ∑ inner, f outer inner row column) =
      ∑ outer, ∑ inner, ∑ row, ∑ column, f outer inner row column := by
  rw [sum_three_comm (fun outer row column => ∑ inner, f outer inner row column)]
  apply Finset.sum_congr rfl
  intro outer _
  exact sum_three_comm (f outer)

private theorem sum_jet_density (value : Fin 4 → Fin 4 → Real)
    (first : Fin 4 → Fin 4 → Fin 4 → Real) (second : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Real) :
    (∑ row, ∑ column, (value row column + (∑ direction, first direction row column) +
      ∑ outer, ∑ inner, second outer inner row column)) =
      (∑ row, ∑ column, value row column) + (∑ direction, ∑ row, ∑ column, first direction row column) +
      ∑ outer, ∑ inner, ∑ row, ∑ column, second outer inner row column := by
  simpa only [Finset.sum_add_distrib] using
    congrArg₂ (fun a b : Real => (∑ row, ∑ column, value row column) + a + b)
      (sum_three_comm first) (sum_four_comm second)

variable (metric : RegularGeneralLorentzMetric period hPeriod) (couplings : EinsteinHilbertCouplings)

private theorem variationCoefficient_eq_frame (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4) :
    regularFrameSmoothCovariantVariationCoefficient period hPeriod metric tensor row column =
      generalMetricFrameCoefficient period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) tensor row column := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [regularFrameSmoothCovariantVariationCoefficient_apply]
  rfl

private def hessianDensityField (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothScalarField period hPeriod :=
  ∑ row : Fin 4, ∑ column : Fin 4, regularFrameSecondJetDensity period hPeriod metric
    (nativeEinsteinJetValueField period hPeriod metric couplings first row column)
    (fun direction => nativeEinsteinJetFirstField period hPeriod metric couplings first direction row column)
    (fun outer inner => nativeEinsteinJetSecondField period hPeriod metric couplings first outer inner row column)
    (generalMetricFrameCoefficient period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) second row column)

private theorem hessianDensityField_apply (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    hessianDensityField period hPeriod metric couplings first second point =
      nativeEinsteinJetCoefficientDensity period hPeriod metric couplings first second point := by
  unfold hessianDensityField
  simp_rw [← variationCoefficient_eq_frame period hPeriod metric]
  simp only [smoothScalarFieldFinsetSum_apply, regularFrameSecondJetDensity,
    smoothScalarFieldAdd_apply, smoothScalarFieldMul_apply, nativeEinsteinJetValueField_apply,
    nativeEinsteinJetFirstField_apply, nativeEinsteinJetSecondField_apply]
  let value := fun row column : Fin 4 =>
    nativeEinsteinJetValueCoefficient period hPeriod metric couplings first point row column *
      regularFrameSmoothCovariantVariationCoefficient period hPeriod metric second row column point
  let firstJet := fun direction row column : Fin 4 =>
    nativeEinsteinJetFirstCoefficient period hPeriod metric couplings first point direction row column *
      regularFrameSmoothCovariantVariationFirstDerivative period hPeriod metric second direction row column point
  let secondJet := fun outer inner row column : Fin 4 =>
    nativeEinsteinJetSecondCoefficient period hPeriod metric couplings first point outer inner row column *
      regularFrameSmoothCovariantVariationSecondDerivative period hPeriod metric second outer inner row column point
  calc
    _ = (∑ row, ∑ column, value row column) + (∑ direction, ∑ row, ∑ column, firstJet direction row column) +
        ∑ outer, ∑ inner, ∑ row, ∑ column, secondJet outer inner row column :=
      sum_jet_density value firstJet secondJet
    _ = _ := by simp only [value, firstJet, secondJet, nativeEinsteinJetCoefficientDensity,
      regularFrameSmoothCovariantVariationCoefficient_apply]

theorem nativeEinsteinHilbertHessian_eq_secondJetFunctional
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    nativeEinsteinHilbertHessian period hPeriod metric couplings
      (regularGeneralMetricC2SmoothDirection period hPeriod metric first)
      (regularGeneralMetricC2SmoothDirection period hPeriod metric second) =
      tensorSecondJetFunctional period hPeriod metric
        (nativeEinsteinJetValueField period hPeriod metric couplings first)
        (nativeEinsteinJetFirstField period hPeriod metric couplings first)
        (nativeEinsteinJetSecondField period hPeriod metric couplings first) second := by
  rw [nativeEinsteinHilbertHessian_eq_coefficientsIntegral]
  calc
    _ = canonicalSmoothScalarIntegral period hPeriod
        (hessianDensityField period hPeriod metric couplings first second) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun point =>
        (hessianDensityField_apply period hPeriod metric couplings first second point).symm
    _ = _ := by simp only [hessianDensityField, map_sum, tensorSecondJetFunctional]

def nativeEinsteinHessianL2 (first : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  tensorSecondJetL2 period hPeriod metric
    (nativeEinsteinJetValueField period hPeriod metric couplings first)
    (nativeEinsteinJetFirstField period hPeriod metric couplings first)
    (nativeEinsteinJetSecondField period hPeriod metric couplings first)

theorem nativeEinsteinHessianL2_pairing (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (nativeEinsteinHessianL2 period hPeriod metric couplings first)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod second) =
      nativeEinsteinHilbertHessian period hPeriod metric couplings
        (regularGeneralMetricC2SmoothDirection period hPeriod metric first)
        (regularGeneralMetricC2SmoothDirection period hPeriod metric second) := by
  rw [nativeEinsteinHilbertHessian_eq_secondJetFunctional]
  exact tensorSecondJetL2_pairing period hPeriod metric _ _ _ second

theorem nativeEinsteinHilbertHessian_bound (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ‖nativeEinsteinHilbertHessian period hPeriod metric couplings
      (regularGeneralMetricC2SmoothDirection period hPeriod metric first)
      (regularGeneralMetricC2SmoothDirection period hPeriod metric second)‖ ≤
      ‖nativeEinsteinHessianL2 period hPeriod metric couplings first‖ *
        ‖globalGeneralMetricTensorFrameL2LinearMap period hPeriod second‖ := by
  rw [← nativeEinsteinHessianL2_pairing]
  exact norm_inner_le_norm _ _

end
end P0EFTJanusProgramPT12NativeEinsteinHessianL24D
end JanusFormal
