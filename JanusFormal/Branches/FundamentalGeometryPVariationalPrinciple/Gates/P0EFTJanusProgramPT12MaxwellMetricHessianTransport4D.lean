import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellNativeMixedHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MobileMetricChartHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NonlinearHessianPullback4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12MaxwellMetricHessianTransport4D

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

/-- The fixed-frame action before the genuine root transport. -/
def nativeFixedMaxwellAction
    (input : RegularGeneralMetricC2Core period hPeriod metric ×
      RegularGeneralMetricC2GaugeCoefficientCore period hPeriod) : Real :=
  regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction period hPeriod metric
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) input.1 input.2

theorem nativeFixedMaxwellAction_contDiffAt
    (coefficients : RegularGeneralMetricC2GaugeCoefficientCore period hPeriod) :
    ContDiffAt Real 2 (nativeFixedMaxwellAction period hPeriod metric) (0, coefficients) := by
  have hOpen : IsOpen (regularGeneralMetricC2GaugeCoefficientMaxwellDomain period hPeriod metric) :=
    (regularGeneralMetricC2Domain_isOpen period hPeriod metric).prod isOpen_univ
  exact (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction_contDiffOn_two
    period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).contDiffAt
    (hOpen.mem_nhds ⟨zero_mem_regularGeneralMetricC2Domain period hPeriod metric,
      Set.mem_univ coefficients⟩)

/-- Fixed-frame Hessian on transported velocities, plus the root acceleration term. -/
def nativeMaxwellMetricTransportHessian
    (first second : RegularGeneralMetricC2Core period hPeriod metric) : Real :=
  let coefficients := maxwellSmoothGaugeC2 period hPeriod metric potential
  let transport := fun matrix => gaugeCoefficientC2CoreFrameTransport period hPeriod matrix coefficients
  let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
  let action := nativeFixedMaxwellAction period hPeriod metric
  fderiv Real (fderiv Real action) (0, coefficients)
    (first, (1 / 2 : Real) • transport first.1)
    (second, (1 / 2 : Real) • transport second.1) +
  fderiv Real action (0, coefficients)
    (0, (-(1 / 8 : Real)) • transport (product first.1 second.1 + product second.1 first.1))

attribute [local irreducible] nativeMobileMaxwellAction nativeMobileMaxwellHessian
  nativeFixedMaxwellAction nativeMaxwellMetricTransportHessian maxwellSmoothGaugeC2 mobileMetricChart

/-- Exact metric-metric entry, with no stationarity assumption. -/
theorem nativeMobileMaxwellHessian_metric_metric_transport
    (first second : RegularGeneralMetricC2Core period hPeriod metric) :
    nativeMobileMaxwellHessian period hPeriod metric potential (first, 0) (second, 0) =
      nativeMaxwellMetricTransportHessian period hPeriod metric potential first second := by
  let coefficients := maxwellSmoothGaugeC2 period hPeriod metric potential
  let action := nativeFixedMaxwellAction period hPeriod metric
  let chart := mobileMetricChart period hPeriod metric coefficients
  let projection : RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      RegularGeneralMetricC2Core period hPeriod metric ×
        RegularGeneralMetricC2GaugeCoefficientCore period hPeriod :=
    (ContinuousLinearMap.id Real _).prod 0
  have hAffine := affineHessian (nativeMobileMaxwellAction period hPeriod metric)
    (0, coefficients) projection (nativeMobileMaxwellAction_contDiffAt period hPeriod metric coefficients)
    first second
  have hEq : (fun variation => nativeMobileMaxwellAction period hPeriod metric
      ((0, coefficients) + projection variation)) = action ∘ chart := by
    funext variation
    simp only [projection, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      zero_apply, Prod.mk_add_mk, zero_add, add_zero]
    unfold action chart nativeMobileMaxwellAction nativeFixedMaxwellAction mobileMetricChart
    rfl
  have hEqDerivative := congrArg (fun current : RegularGeneralMetricC2Core period hPeriod metric → Real =>
    fderiv Real (fderiv Real current) 0 first second) hEq
  have hPullback : nativeMobileMaxwellHessian period hPeriod metric potential (first, 0) (second, 0) =
      fderiv Real (fderiv Real (action ∘ chart)) 0 first second := by
    unfold nativeMobileMaxwellHessian
    exact hAffine.symm.trans hEqDerivative
  have hAction : ContDiffAt Real 2 action (chart 0) := by
    rw [show chart 0 = (0, coefficients) from mobileMetricChart_zero period hPeriod metric coefficients]
    exact nativeFixedMaxwellAction_contDiffAt period hPeriod metric coefficients
  have h := nonlinearHessian action chart 0 first second hAction
    (mobileMetricChart_contDiffAt_zero period hPeriod metric coefficients)
  simp only [chart, mobileMetricChart_zero, mobileMetricChart_fderiv_zero, mobileMetricChart_hessian_zero] at h
  unfold nativeMaxwellMetricTransportHessian
  exact hPullback.trans h

end
end P0EFTJanusProgramPT12MaxwellMetricHessianTransport4D
end JanusFormal
