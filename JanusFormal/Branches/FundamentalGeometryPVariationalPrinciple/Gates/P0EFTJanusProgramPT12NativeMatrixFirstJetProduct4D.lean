import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeTransportFirstJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatrixFirstJetProduct4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12NativeMatrixFirstJetProduct4D

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

open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusRegularFrameC2LorenzFeature4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D

open P0EFTJanusProgramPT12GaugeCurvatureReadout4D
open P0EFTJanusProgramPT12MaxwellTransportFirstJetSymbol4D

open P0EFTJanusProgramPT12NativeTransportFirstJet4D
open P0EFTJanusProgramPT12MatrixFirstJetProduct4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityPointwise4D

private theorem product_value (first second : C2Scalar period hPeriod) (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (canonicalPhysicalScalarC2JetCoreProduct period hPeriod first second) point =
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod first point *
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod second point := rfl

theorem nativeMatrixFirstJet_add (first second : C2FiniteMatrix period hPeriod 4)
    (point : EffectiveQuotient period hPeriod) :
    nativeMatrixFirstJet period hPeriod metric (first + second) point =
      nativeMatrixFirstJet period hPeriod metric first point + nativeMatrixFirstJet period hPeriod metric second point := by
  apply Prod.ext
  · funext row column
    exact congrArg (fun field : C(EffectiveQuotient period hPeriod, Real) => field point)
      ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).map_add (first row column) (second row column))
  · funext direction row column
    exact congrArg (fun field : C(EffectiveQuotient period hPeriod, Real) => field point)
      (regularFrameC2FirstDerivative_add period hPeriod metric direction (first row column) (second row column))

/-- The finite Leibniz product is the first jet of the actual completed matrix product. -/
theorem nativeMatrixFirstJet_product (first second : C2FiniteMatrix period hPeriod 4)
    (point : EffectiveQuotient period hPeriod) :
    nativeMatrixFirstJet period hPeriod metric (c2FiniteMatrixProduct period hPeriod 4 first second) point =
      matrixFirstJetLeft (nativeMatrixFirstJet period hPeriod metric first point)
        (nativeMatrixFirstJet period hPeriod metric second point) := by
  apply Prod.ext
  · funext row column
    change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (c2FiniteMatrixProduct period hPeriod 4 first second row column) point =
      ∑ middle, canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (first row middle) point *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (second middle column) point
    simp only [c2FiniteMatrixProduct_apply, map_sum, ContinuousMap.sum_apply, product_value]
  · funext direction row column
    change regularFrameC2FirstDerivative period hPeriod metric direction
      (c2FiniteMatrixProduct period hPeriod 4 first second row column) point =
      (∑ middle, regularFrameC2FirstDerivative period hPeriod metric direction (first row middle) point *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (second middle column) point) +
      (∑ middle, canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (first row middle) point *
        regularFrameC2FirstDerivative period hPeriod metric direction (second middle column) point)
    simp only [c2FiniteMatrixProduct_apply, regularFrameC2FirstDerivative_sum,
      regularFrameC2FirstDerivative_product, ContinuousMap.sum_apply, ContinuousMap.add_apply,
      ContinuousMap.mul_apply, Finset.sum_add_distrib]
    exact add_comm _ _

theorem nativeMatrixFirstJet_relative_value (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) (row column : Fin 4) :
    (nativeMatrixFirstJet period hPeriod metric direction.1 point).1 row column =
      regularGeneralMetricC2RelativeMatrixAt period hPeriod metric direction point row column := rfl

end
end P0EFTJanusProgramPT12NativeMatrixFirstJetProduct4D
end JanusFormal
