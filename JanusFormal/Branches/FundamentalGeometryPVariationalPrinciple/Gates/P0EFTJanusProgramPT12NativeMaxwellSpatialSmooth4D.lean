import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeMaxwellFirstJetCovector4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeJetSpatialSmooth4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12NativeMaxwellSpatialSmooth4D

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

def smoothMatrixFirstJet (fields : Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) : MatrixFirstJet :=
  (fun row column => fields row column point,
   fun direction row column => frameDerivativeComponentField period hPeriod
     (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) (fields row column) direction point)

theorem nativeMatrixFirstJet_smooth (fields : Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    nativeMatrixFirstJet period hPeriod metric
      (fun row column => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (fields row column)) point =
      smoothMatrixFirstJet period hPeriod metric fields point := by
  apply Prod.ext
  · rfl
  · funext direction row column
    change regularFrameC2FirstDerivative period hPeriod metric direction
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (fields row column)) point = _
    rw [regularFrameC2FirstDerivative_smooth]
    rfl

theorem smoothMatrixFirstJet_contMDiff (fields : Fin 4 → Fin 4 → SmoothScalarField period hPeriod) :
    ContMDiff coverModelWithCorners 𝓘(Real, MatrixFirstJet) ∞
      (smoothMatrixFirstJet period hPeriod metric fields) := by
  apply ContMDiff.prodMk_space
  · apply contMDiff_pi_space.mpr; intro row
    apply contMDiff_pi_space.mpr; intro column
    exact (fields row column).contMDiff_toFun
  · apply contMDiff_pi_space.mpr; intro direction
    apply contMDiff_pi_space.mpr; intro row
    apply contMDiff_pi_space.mpr; intro column
    exact (frameDerivativeComponentField period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) (fields row column) direction).contMDiff_toFun

def nativeRelativeMatrixField (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4) : SmoothScalarField period hPeriod :=
  smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) metric.metric tensor row column

theorem nativeMatrixFirstJet_relative_smooth (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    nativeMatrixFirstJet period hPeriod metric (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor).1 point =
      smoothMatrixFirstJet period hPeriod metric (nativeRelativeMatrixField period hPeriod metric tensor) point :=
  nativeMatrixFirstJet_smooth period hPeriod metric (nativeRelativeMatrixField period hPeriod metric tensor) point

theorem nativeGaugeTransportParameters_contMDiff :
    ContMDiff coverModelWithCorners 𝓘(Real, TransportSymbolParameters) ∞
      (nativeGaugeTransportParameters period hPeriod metric (maxwellSmoothGaugeC2 period hPeriod metric potential)) := by
  apply ContMDiff.prodMk_space
  · exact nativeFrameBracket_contMDiff period hPeriod metric
  apply ContMDiff.prodMk_space
  · apply contMDiff_pi_space.mpr; intro index
    apply contMDiff_pi_space.mpr; intro component
    exact (regularFrameGaugeCoefficient period hPeriod
      (gaugePotentialFrameCoefficients period hPeriod metric potential) (index, component)).contMDiff_toFun
  · apply contMDiff_pi_space.mpr; intro direction
    apply contMDiff_pi_space.mpr; intro index
    apply contMDiff_pi_space.mpr; intro component
    change ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞ (fun point =>
      regularFrameC2FirstDerivative period hPeriod metric direction
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (regularFrameGaugeCoefficient period hPeriod
            (gaugePotentialFrameCoefficients period hPeriod metric potential) (index, component))) point)
    simp only [regularFrameC2FirstDerivative_smooth]
    exact (frameDerivativeComponentField period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (regularFrameGaugeCoefficient period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod metric potential) (index, component)) direction).contMDiff_toFun

theorem nativeMobileMaxwellJet_zero_contMDiff :
    ContMDiff coverModelWithCorners 𝓘(Real, MaxwellJet) ∞
      (fun point => nativeMobileMaxwellJet period hPeriod metric potential 0 point) := by
  unfold nativeMobileMaxwellJet
  simp only [regularGeneralMetricC0InverseMetricCoefficient_zero_apply,
    regularGeneralMetricC2MobileGaugeCoefficientTransport_zero]
  apply ContMDiff.prodMk_space
  · exact nativeInverseCoefficients_contMDiff period hPeriod metric
  · apply contMDiff_pi_space.mpr; intro component
    apply contMDiff_pi_space.mpr; intro row
    apply contMDiff_pi_space.mpr; intro column
    change ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞ (fun point =>
      regularFrameGaugeCurvatureC0FromC2Coefficients period hPeriod metric
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
          (gaugePotentialFrameCoefficients period hPeriod metric potential)) component row column point)
    rw [regularFrameGaugeCurvatureC0FromC2Coefficients_smooth]
    exact (regularFrameGaugeCurvatureCoefficient period hPeriod metric
      (regularFrameGaugePotentialFromCoefficients period hPeriod metric
        (gaugePotentialFrameCoefficients period hPeriod metric potential)) component row column).contMDiff_toFun

attribute [local irreducible] nativeMaxwellFirstJetCovector maxwellFirstJetCovector

theorem nativeMaxwellFirstJetCovector_contMDiff (first : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (test : MatrixFirstJet) :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞ (fun point =>
      nativeMaxwellFirstJetCovector period hPeriod metric potential
        (regularGeneralMetricC2SmoothDirection period hPeriod metric first) point test) := by
  have hFirst := smoothMatrixFirstJet_contMDiff period hPeriod metric (nativeRelativeMatrixField period hPeriod metric first)
  have hInput := metric.volume.contMDiff_toFun.prodMk_space (nativeMobileMaxwellJet_zero_contMDiff period hPeriod metric potential)
  have h := (maxwellFirstJetCovector_contDiff test).comp_contMDiff
    (hInput.prodMk_space ((nativeGaugeTransportParameters_contMDiff period hPeriod metric potential).prodMk_space hFirst))
  unfold nativeMaxwellFirstJetCovector
  simp only [nativeMatrixFirstJet_relative_smooth]
  exact h

end
end P0EFTJanusProgramPT12NativeMaxwellSpatialSmooth4D
end JanusFormal
