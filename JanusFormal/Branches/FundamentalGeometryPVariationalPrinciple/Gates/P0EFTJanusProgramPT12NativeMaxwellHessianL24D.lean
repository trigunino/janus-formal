import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RelativeTensorFirstJetL24D
namespace JanusFormal
namespace P0EFTJanusProgramPT12NativeMaxwellHessianL24D

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
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
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

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

open P0EFTJanusProgramPT12MaxwellNativeMixedHessian4D
open P0EFTJanusProgramPT12MobileMetricChartHessian4D
open P0EFTJanusProgramPT12NonlinearHessianPullback4D
open P0EFTJanusProgramPT12VectorHessianPullback4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D

open P0EFTJanusProgramPT12MaxwellJetSymbol4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularFrameGaugeCurvatureC0FromC2Coefficients4D

open P0EFTJanusProgramPT12NativeMaxwellJetBridge4D

open P0EFTJanusProgramPT12MaxwellJetHessianIntegral4D
open P0EFTJanusProgramPT12NativeMaxwellJetDifferentials4D

open P0EFTJanusProgramPT12NativeMatrixFirstJetProduct4D
open P0EFTJanusProgramPT12NativeTransportFirstJet4D
open P0EFTJanusProgramPT12MatrixFirstJetProduct4D
open P0EFTJanusProgramPT12MaxwellTransportFirstJetSymbol4D
open P0EFTJanusProgramPT12MaxwellFirstJetCovector4D
open P0EFTJanusProgramPT12NativeMaxwellExplicitHessian4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D

open P0EFTJanusProgramPT12NativeMaxwellFirstJetCovector4D
open P0EFTJanusProgramPT12NativeJetSpatialSmooth4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D

open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D

open P0EFTJanusProgramPT12NativeMaxwellSpatialSmooth4D
open P0EFTJanusProgramPT12TensorSecondJetL24D
open P0EFTJanusProgramPT12RegularFrameSecondJetAdjoint4D
open P0EFTJanusProgramPT12RegularTensorCovectorL24D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusRegularFrameCanonicalFormalAdjoint4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open scoped BigOperators InnerProductSpace

open P0EFTJanusProgramPT12RelativeTensorFirstJetL24D

attribute [local irreducible] nativeMaxwellFirstJetCovector

def nativeMaxwellJetValueField (first : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4) : SmoothScalarField period hPeriod where
  toFun point := nativeMaxwellFirstJetCovector period hPeriod metric potential
    (regularGeneralMetricC2SmoothDirection period hPeriod metric first) point (matrixValueBasis row column)
  contMDiff_toFun := nativeMaxwellFirstJetCovector_contMDiff period hPeriod metric potential first (matrixValueBasis row column)

def nativeMaxwellJetFirstField (first : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (direction row column : Fin 4) : SmoothScalarField period hPeriod where
  toFun point := nativeMaxwellFirstJetCovector period hPeriod metric potential
    (regularGeneralMetricC2SmoothDirection period hPeriod metric first) point (matrixFirstBasis direction row column)
  contMDiff_toFun := nativeMaxwellFirstJetCovector_contMDiff period hPeriod metric potential first
    (matrixFirstBasis direction row column)

private theorem sum_three_comm (f : Fin 4 → Fin 4 → Fin 4 → Real) :
    (∑ row, ∑ column, ∑ direction, f direction row column) = ∑ direction, ∑ row, ∑ column, f direction row column := by
  calc
    _ = ∑ row, ∑ direction, ∑ column, f direction row column := by
      apply Finset.sum_congr rfl; intro row _; exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem nativeMaxwellFirstJetDensity_apply (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    relativeTensorFirstJetDensity period hPeriod metric
      (nativeMaxwellJetValueField period hPeriod metric potential first)
      (nativeMaxwellJetFirstField period hPeriod metric potential first) second point =
      nativeMaxwellFirstJetCovector period hPeriod metric potential
        (regularGeneralMetricC2SmoothDirection period hPeriod metric first) point
        (nativeMatrixFirstJet period hPeriod metric
          (regularGeneralMetricC2SmoothDirection period hPeriod metric second).1 point) := by
  rw [nativeMatrixFirstJet_relative_smooth, matrixFirstJetCovector_apply]
  simp only [relativeTensorFirstJetDensity, smoothScalarFieldFinsetSum_apply, regularFrameSecondJetDensity,
    smoothScalarFieldAdd_apply, smoothScalarFieldMul_apply]
  change (∑ row : Fin 4, ∑ column : Fin 4,
    (nativeMaxwellJetValueField period hPeriod metric potential first row column point *
      nativeRelativeMatrixField period hPeriod metric second row column point +
     (∑ direction : Fin 4, nativeMaxwellJetFirstField period hPeriod metric potential first direction row column point *
       (smoothMatrixFirstJet period hPeriod metric (nativeRelativeMatrixField period hPeriod metric second) point).2 direction row column) +
     ∑ outer : Fin 4, ∑ inner : Fin 4, (0 : Real) * _)) = _
  simp only [zero_mul, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
  rw [sum_three_comm]
  rfl

attribute [local irreducible] nativeMobileMaxwellHessian

theorem nativeMobileMaxwellHessian_eq_firstJetFunctional
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    nativeMobileMaxwellHessian period hPeriod metric potential
      (regularGeneralMetricC2SmoothDirection period hPeriod metric first, 0)
      (regularGeneralMetricC2SmoothDirection period hPeriod metric second, 0) =
      canonicalSmoothScalarIntegral period hPeriod (relativeTensorFirstJetDensity period hPeriod metric
        (nativeMaxwellJetValueField period hPeriod metric potential first)
        (nativeMaxwellJetFirstField period hPeriod metric potential first) second) := by
  rw [nativeMobileMaxwellHessian_eq_firstJetIntegral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point => (nativeMaxwellFirstJetDensity_apply period hPeriod metric potential first second point).symm

def nativeMaxwellHessianL2 (first : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  relativeTensorFirstJetL2 period hPeriod metric
    (nativeMaxwellJetValueField period hPeriod metric potential first)
    (nativeMaxwellJetFirstField period hPeriod metric potential first)

theorem nativeMaxwellHessianL2_pairing (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (nativeMaxwellHessianL2 period hPeriod metric potential first)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod second) =
      nativeMobileMaxwellHessian period hPeriod metric potential
        (regularGeneralMetricC2SmoothDirection period hPeriod metric first, 0)
        (regularGeneralMetricC2SmoothDirection period hPeriod metric second, 0) := by
  rw [nativeMobileMaxwellHessian_eq_firstJetFunctional]
  exact relativeTensorFirstJetL2_pairing period hPeriod metric _ _ second

/-- Actual L2 bound for the full metric-metric Maxwell Hessian, including root transport. -/
theorem nativeMobileMaxwellHessian_metric_bound (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ‖nativeMobileMaxwellHessian period hPeriod metric potential
      (regularGeneralMetricC2SmoothDirection period hPeriod metric first, 0)
      (regularGeneralMetricC2SmoothDirection period hPeriod metric second, 0)‖ ≤
      ‖nativeMaxwellHessianL2 period hPeriod metric potential first‖ *
        ‖globalGeneralMetricTensorFrameL2LinearMap period hPeriod second‖ := by
  rw [← nativeMaxwellHessianL2_pairing]
  exact norm_inner_le_norm _ _

end
end P0EFTJanusProgramPT12NativeMaxwellHessianL24D
end JanusFormal
