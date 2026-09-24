import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeMaxwellExplicitHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeMatrixFirstJetProduct4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellFirstJetCovector4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellJetHessianIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeMaxwellJetDifferentials4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12NativeMaxwellFirstJetCovector4D

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

def nativeMaxwellFirstJetCovector (first : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) : MatrixFirstJet →L[Real] Real :=
  maxwellFirstJetCovector (metric.volume point, nativeMobileMaxwellJet period hPeriod metric potential 0 point)
    (nativeGaugeTransportParameters period hPeriod metric (maxwellSmoothGaugeC2 period hPeriod metric potential) point)
    (nativeMatrixFirstJet period hPeriod metric first.1 point)

theorem nativeMaxwellJetVelocity_eq_firstJet (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    nativeMaxwellJetVelocity period hPeriod metric potential point direction =
      maxwellFirstJetVelocity (regularFrameMetricInverseMatrixMap period hPeriod metric point)
        (nativeGaugeTransportParameters period hPeriod metric (maxwellSmoothGaugeC2 period hPeriod metric potential) point)
        (nativeMatrixFirstJet period hPeriod metric direction.1 point) := by
  apply Prod.ext
  · rfl
  · change (1 / 2 : Real) • (_ : MaxwellCurvature) = (1 / 2 : Real) • (_ : MaxwellCurvature)
    rw [gaugeCurvatureReadout_transport_eq_linear]
    rfl

theorem nativeMaxwellJetAcceleration_eq_firstJet (first second : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    nativeMaxwellJetAcceleration period hPeriod metric potential point first second =
      maxwellFirstJetAcceleration (regularFrameMetricInverseMatrixMap period hPeriod metric point)
        (nativeGaugeTransportParameters period hPeriod metric (maxwellSmoothGaugeC2 period hPeriod metric potential) point)
        (nativeMatrixFirstJet period hPeriod metric first.1 point)
        (nativeMatrixFirstJet period hPeriod metric second.1 point) := by
  apply Prod.ext
  · rfl
  · change (-(1 / 8 : Real)) • (_ : MaxwellCurvature) = (-(1 / 8 : Real)) • (_ : MaxwellCurvature)
    rw [gaugeCurvatureReadout_transport_eq_linear, nativeMatrixFirstJet_add,
      nativeMatrixFirstJet_product, nativeMatrixFirstJet_product]
    rfl

theorem nativeMaxwellExplicitHessianDensity_eq_covector
    (first second : RegularGeneralMetricC2Core period hPeriod metric) (point : EffectiveQuotient period hPeriod) :
    nativeMaxwellExplicitHessianDensity period hPeriod metric potential first second point =
      nativeMaxwellFirstJetCovector period hPeriod metric potential first point
        (nativeMatrixFirstJet period hPeriod metric second.1 point) := by
  unfold nativeMaxwellExplicitHessianDensity nativeMaxwellFirstJetCovector maxwellFirstJetCovector
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    nativeMaxwellJetVelocity_eq_firstJet, nativeMaxwellJetAcceleration_eq_firstJet]
  have hInverse : (nativeMobileMaxwellJet period hPeriod metric potential 0 point).1 =
      regularFrameMetricInverseMatrixMap period hPeriod metric point := by
    funext row column
    exact regularGeneralMetricC0InverseMetricCoefficient_zero_apply period hPeriod metric row column point
  rw [hInverse]

attribute [local irreducible] nativeMobileMaxwellHessian nativeMaxwellExplicitHessianDensity
  nativeMaxwellFirstJetCovector

theorem nativeMobileMaxwellHessian_eq_firstJetIntegral
    (first second : RegularGeneralMetricC2Core period hPeriod metric) :
    nativeMobileMaxwellHessian period hPeriod metric potential (first, 0) (second, 0) =
      ∫ point, nativeMaxwellFirstJetCovector period hPeriod metric potential first point
        (nativeMatrixFirstJet period hPeriod metric second.1 point)
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  refine (nativeMobileMaxwellHessian_eq_explicitIntegral period hPeriod metric potential first second).trans ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (nativeMaxwellExplicitHessianDensity_eq_covector period hPeriod metric potential first second)

end
end P0EFTJanusProgramPT12NativeMaxwellFirstJetCovector4D
end JanusFormal
