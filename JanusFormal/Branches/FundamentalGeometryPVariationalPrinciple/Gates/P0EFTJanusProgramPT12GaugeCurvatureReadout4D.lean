import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeMaxwellJetBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameC2LorenzFeature4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeCurvatureReadout4D

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

/-- Bounded Cartan-curvature coefficient, including the nonholonomic bracket term. -/
def gaugeCurvatureCoefficientCLM (component : Fin 2) (row column : Fin 4) :
    RegularGeneralMetricC2GaugeCoefficientCore period hPeriod →L[Real]
      C(EffectiveQuotient period hPeriod, Real) :=
  (regularFrameC2FirstDerivativeCLM period hPeriod metric row).comp
      (gaugeCoefficientC2CoreComponentCLM period hPeriod column component) -
    (regularFrameC2FirstDerivativeCLM period hPeriod metric column).comp
      (gaugeCoefficientC2CoreComponentCLM period hPeriod row component) -
    ∑ upper : Fin 4,
      (ContinuousLinearMap.mul Real _
        (regularFrameStructureCoefficientContinuous period hPeriod metric row column upper)).comp
        ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
          (gaugeCoefficientC2CoreComponentCLM period hPeriod upper component))

@[simp]
theorem gaugeCurvatureCoefficientCLM_apply (component : Fin 2) (row column : Fin 4)
    (coefficients : RegularGeneralMetricC2GaugeCoefficientCore period hPeriod) :
    gaugeCurvatureCoefficientCLM period hPeriod metric component row column coefficients =
      regularFrameGaugeCurvatureC0FromC2Coefficients period hPeriod metric coefficients component row column := by
  simp only [gaugeCurvatureCoefficientCLM, sub_apply, sum_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- Finite pointwise curvature readout of the completed coefficient core. -/
def gaugeCurvatureReadout (point : EffectiveQuotient period hPeriod) :
    RegularGeneralMetricC2GaugeCoefficientCore period hPeriod →L[Real] MaxwellCurvature :=
  ContinuousLinearMap.pi fun component => ContinuousLinearMap.pi fun row =>
    ContinuousLinearMap.pi fun column =>
      (ContinuousMap.evalCLM Real point).comp
        (gaugeCurvatureCoefficientCLM period hPeriod metric component row column)

@[simp]
theorem gaugeCurvatureReadout_apply (point : EffectiveQuotient period hPeriod)
    (coefficients : RegularGeneralMetricC2GaugeCoefficientCore period hPeriod)
    (component : Fin 2) (row column : Fin 4) :
    gaugeCurvatureReadout period hPeriod metric point coefficients component row column =
      regularFrameGaugeCurvatureC0FromC2Coefficients period hPeriod metric coefficients component row column point := by
  simp only [gaugeCurvatureReadout, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    gaugeCurvatureCoefficientCLM_apply]
  rfl

theorem gaugeCurvatureReadout_smooth (point : EffectiveQuotient period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2) (row column : Fin 4) :
    gaugeCurvatureReadout period hPeriod metric point
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) component row column =
      regularFrameGaugeCurvatureCoefficient period hPeriod metric
        (regularFrameGaugePotentialFromCoefficients period hPeriod metric coefficients) component row column point := by
  rw [gaugeCurvatureReadout_apply, regularFrameGaugeCurvatureC0FromC2Coefficients_smooth]
  rfl

end
end P0EFTJanusProgramPT12GaugeCurvatureReadout4D
end JanusFormal
