import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeCurvatureReadout4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12MobileCurvatureDifferentials4D

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

open P0EFTJanusRegularFrameC2LorenzFeature4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D

open P0EFTJanusProgramPT12GaugeCurvatureReadout4D
open P0EFTJanusPairedStrongMaxwellMetricTransportDerivative4D
open P0EFTJanusProgramPT12MobileGaugeTransportHessian4D

variable (coefficients : RegularGeneralMetricC2GaugeCoefficientCore period hPeriod)
  (point : EffectiveQuotient period hPeriod)

/-- Actual curvature of the transported coefficient packet. -/
def mobileCurvature (variation : RegularGeneralMetricC2Core period hPeriod metric) : MaxwellCurvature :=
  gaugeCurvatureReadout period hPeriod metric point
    (regularGeneralMetricC2MobileGaugeCoefficientTransport period hPeriod metric variation coefficients)

theorem mobileCurvature_contDiffAt_zero :
    ContDiffAt Real 2 (mobileCurvature period hPeriod metric coefficients point) 0 := by
  have h := (mobileMetricChart_contDiffAt_zero period hPeriod metric coefficients).snd
  exact (gaugeCurvatureReadout period hPeriod metric point).contDiff.contDiffAt.comp 0 h

theorem mobileCurvature_fderiv_zero (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    fderiv Real (mobileCurvature period hPeriod metric coefficients point) 0 direction =
      (1 / 2 : Real) • gaugeCurvatureReadout period hPeriod metric point
        (gaugeCoefficientC2CoreFrameTransport period hPeriod direction.1 coefficients) := by
  have h := (gaugeCurvatureReadout period hPeriod metric point).hasFDerivAt.comp 0
    (regularGeneralMetricC2MobileGaugeCoefficientTransport_hasFDerivAt_zero period hPeriod metric coefficients)
  have hEq := congrArg (fun derivative => derivative direction) h.fderiv
  simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul,
    gaugeCoefficientC2CoreFrameTransportLeftCLM_apply] at hEq
  exact hEq

theorem mobileCurvature_hessian_zero (first second : RegularGeneralMetricC2Core period hPeriod metric) :
    let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
    fderiv Real (fderiv Real (mobileCurvature period hPeriod metric coefficients point)) 0 first second =
      (-(1 / 8 : Real)) • gaugeCurvatureReadout period hPeriod metric point
        (gaugeCoefficientC2CoreFrameTransport period hPeriod
          (product first.1 second.1 + product second.1 first.1) coefficients) := by
  let readout := gaugeCurvatureReadout period hPeriod metric point
  let transport := fun variation => regularGeneralMetricC2MobileGaugeCoefficientTransport
    period hPeriod metric variation coefficients
  have hC2 : ContDiffAt Real 2 transport 0 :=
    (mobileMetricChart_contDiffAt_zero period hPeriod metric coefficients).snd
  have h := linearPostHessian readout transport 0 first second hC2
  have hAcceleration := congrArg readout
    (mobileGaugeTransport_hessian_zero period hPeriod metric coefficients first second)
  simp only [map_smul] at hAcceleration
  exact h.trans hAcceleration

end
end P0EFTJanusProgramPT12MobileCurvatureDifferentials4D
end JanusFormal
