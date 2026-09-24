import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeMaxwellSpatialSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12TensorSecondJetL24D
namespace JanusFormal
namespace P0EFTJanusProgramPT12RelativeTensorFirstJetL24D

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

theorem nativeRelativeMatrixField_apply (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4) (point : EffectiveQuotient period hPeriod) :
    nativeRelativeMatrixField period hPeriod metric tensor row column point =
      ∑ middle : Fin 4, regularFrameMetricInverseMatrix period hPeriod metric row middle point *
        generalMetricFrameCoefficient period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) tensor middle column point := by
  exact congrArg (fun matrix : Matrix (Fin 4) (Fin 4) Real => matrix row column)
    (regularGeneralMetricC2RelativeMatrixAt_smooth period hPeriod metric tensor point)

private theorem sum_reverse_three (f : Fin 4 → Fin 4 → Fin 4 → Real) :
    (∑ row, ∑ column, ∑ upper, f row column upper) = ∑ upper, ∑ column, ∑ row, f row column upper := by
  calc
    _ = ∑ row, ∑ upper, ∑ column, f row column upper := by
      apply Finset.sum_congr rfl; intro row _; exact Finset.sum_comm
    _ = ∑ upper, ∑ row, ∑ column, f row column upper := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl; intro upper _; exact Finset.sum_comm

def relativeTensorCovectorL2 (coefficients : Fin 4 → Fin 4 → SmoothScalarField period hPeriod) :
    GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  regularTensorCovectorActualL2 period hPeriod metric fun row column =>
    ∑ upper : Fin 4, smoothScalarFieldMul period hPeriod (coefficients upper column)
      (regularFrameMetricInverseMatrix period hPeriod metric upper row)

theorem relativeTensorCovectorL2_pairing
    (coefficients : Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (relativeTensorCovectorL2 period hPeriod metric coefficients)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
      ∑ row : Fin 4, ∑ column : Fin 4, canonicalSmoothScalarIntegral period hPeriod
        (smoothScalarFieldMul period hPeriod (coefficients row column)
          (nativeRelativeMatrixField period hPeriod metric tensor row column)) := by
  rw [relativeTensorCovectorL2, regularTensorCovectorActualL2_pairing]
  calc
    _ = canonicalSmoothScalarIntegral period hPeriod
        (∑ row : Fin 4, ∑ column : Fin 4, smoothScalarFieldMul period hPeriod (coefficients row column)
          (nativeRelativeMatrixField period hPeriod metric tensor row column)) := by
      apply integral_congr_ae
      filter_upwards [] with point
      rw [regularFrameCovariantCoefficientTensor_pairing]
      simp only [smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply, nativeRelativeMatrixField_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [sum_reverse_three]
      apply Finset.sum_congr rfl; intro upper _
      apply Finset.sum_congr rfl; intro column _
      apply Finset.sum_congr rfl; intro row _
      exact mul_assoc _ _ _
    _ = _ := by simp only [map_sum]

variable (value : Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
  (first : Fin 4 → Fin 4 → Fin 4 → SmoothScalarField period hPeriod)

def relativeTensorFirstJetDensity (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothScalarField period hPeriod :=
  ∑ row : Fin 4, ∑ column : Fin 4, regularFrameSecondJetDensity period hPeriod metric
    (value row column) (fun direction => first direction row column) (fun _ _ => 0)
    (nativeRelativeMatrixField period hPeriod metric tensor row column)

def relativeTensorFirstJetL2 : GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  relativeTensorCovectorL2 period hPeriod metric fun row column =>
    regularFrameSecondJetAdjoint period hPeriod metric
      (value row column) (fun direction => first direction row column) (fun _ _ => 0)

theorem relativeTensorFirstJetL2_pairing (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (relativeTensorFirstJetL2 period hPeriod metric value first)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
      canonicalSmoothScalarIntegral period hPeriod (relativeTensorFirstJetDensity period hPeriod metric value first tensor) := by
  rw [relativeTensorFirstJetL2, relativeTensorCovectorL2_pairing]
  simp only [relativeTensorFirstJetDensity, map_sum, regularFrameSecondJetAdjoint_integral]

end
end P0EFTJanusProgramPT12RelativeTensorFirstJetL24D
end JanusFormal
