import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2FrozenEinsteinHilbertDerivativeBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameCanonicalVolumeDerivativeAtCenter4D

/-! # Explicit center derivative of the Einstein--Hilbert volume defect -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2EinsteinHilbertVolumeDefectDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 6000

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameC2ProjectedScalarCompletion4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertFrozenVolumeDecomposition4D
open P0EFTJanusFiniteFrameCanonicalVolumeDerivativeAtCenter4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : IsFiniteMeasure
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)

private abbrev Model :=
  GeneralMetricRelativeC2Core period hPeriod frame baseMetric

private abbrev Domain :=
  generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric

/-- Curvature-minus-cosmological scalar factor in the finite EH density. -/
def finiteFrameC2EinsteinHilbertScalarFactor
    (couplings : EinsteinHilbertCouplings)
    (variation : Model period hPeriod frame baseMetric) : C0Scalar period hPeriod :=
  (1 / (2 * couplings.gravitationalCoupling)) •
    (finiteFrameProjectedScalarCurvatureC0 period hPeriod frame baseMetric variation -
      finiteFrameC0Constant period hPeriod (2 * couplings.cosmologicalConstant))

/-- Pointwise density whose integral is the mobile-volume EH defect. -/
def finiteFrameC2EinsteinHilbertVolumeDefectDensity
    (couplings : EinsteinHilbertCouplings)
    (variation : Model period hPeriod frame baseMetric) : C0Scalar period hPeriod :=
  (finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric variation -
      finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric 0) *
    finiteFrameC2EinsteinHilbertScalarFactor period hPeriod frame baseMetric couplings variation

/-- Exact center derivative: moving volume times the central EH scalar factor. -/
def finiteFrameC2EinsteinHilbertVolumeDefectDerivativeAtZero
    (couplings : EinsteinHilbertCouplings) :
    Model period hPeriod frame baseMetric →L[Real] Real :=
  (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).comp
    (((ContinuousLinearMap.mul Real (C0Scalar period hPeriod)).flip
      (finiteFrameC2EinsteinHilbertScalarFactor period hPeriod frame baseMetric couplings 0)).comp
      (finiteFrameCanonicalVolumeC0DerivativeAtZero period hPeriod frame baseMetric))

theorem finiteFrameC2EinsteinHilbertVolumeDefectAction_eq_integral
    (couplings : EinsteinHilbertCouplings)
    (variation : Model period hPeriod frame baseMetric) :
    finiteFrameC2EinsteinHilbertVolumeDefectAction period hPeriod frame baseMetric couplings
        variation =
      finiteFrameBRSTCanonicalIntegralCLM period hPeriod
        (finiteFrameC2EinsteinHilbertVolumeDefectDensity period hPeriod frame baseMetric
          couplings variation) := by
  unfold finiteFrameC2EinsteinHilbertVolumeDefectAction
    finiteFrameC2EinsteinHilbertAction finiteFrameC2FrozenVolumeEinsteinHilbertAction
  rw [← map_sub]
  apply congrArg (finiteFrameBRSTCanonicalIntegralCLM period hPeriod)
  apply ContinuousMap.ext
  intro point
  simp only [finiteFrameC2EinsteinHilbertDensity,
    finiteFrameC2FrozenVolumeEinsteinHilbertDensity,
    finiteFrameC2EinsteinHilbertVolumeDefectDensity,
    finiteFrameC2EinsteinHilbertScalarFactor, ContinuousMap.sub_apply,
    ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem finiteFrameC2EinsteinHilbertVolumeDefectAction_hasFDerivAt_zero
    (couplings : EinsteinHilbertCouplings) :
    HasFDerivAt
      (finiteFrameC2EinsteinHilbertVolumeDefectAction period hPeriod frame baseMetric couplings)
      (finiteFrameC2EinsteinHilbertVolumeDefectDerivativeAtZero period hPeriod frame baseMetric
        couplings) 0 := by
  let volume := finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric
  let scalarFactor :=
    finiteFrameC2EinsteinHilbertScalarFactor period hPeriod frame baseMetric couplings
  have hVolume := finiteFrameCanonicalVolumeC0_hasFDerivAt_zero period hPeriod frame baseMetric
  have hDomain := zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric
  have hOpen := generalMetricRelativeC2VolumeDomain_isOpen period hPeriod frame baseMetric
  have hScalarOn : ContDiffOn Real 2 scalarFactor (Domain period hPeriod frame baseMetric) :=
    ((finiteFrameProjectedScalarCurvatureC0_contDiffOn_two period hPeriod frame baseMetric).mono
      (fun _ hVariation => hVariation.1)).sub contDiffOn_const |>.const_smul _
  have hScalar : DifferentiableAt Real scalarFactor 0 :=
    (((hScalarOn 0 hDomain).contDiffAt (hOpen.mem_nhds hDomain)).differentiableAt
      (by norm_num))
  have hDifference := hVolume.sub_const (volume 0)
  have hProduct := hDifference.mul hScalar.hasFDerivAt
  have hDensity : HasFDerivAt
      (finiteFrameC2EinsteinHilbertVolumeDefectDensity period hPeriod frame baseMetric couplings)
      (((ContinuousLinearMap.mul Real (C0Scalar period hPeriod)).flip (scalarFactor 0)).comp
        (finiteFrameCanonicalVolumeC0DerivativeAtZero period hPeriod frame baseMetric)) 0 := by
    apply hProduct.congr_fderiv
    apply ContinuousLinearMap.ext
    intro direction
    simp [volume, scalarFactor]
  have hIntegral :=
    (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).hasFDerivAt.comp 0 hDensity
  apply hIntegral.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun variation => by
    simpa [Function.comp_apply] using
      finiteFrameC2EinsteinHilbertVolumeDefectAction_eq_integral period hPeriod frame baseMetric
        couplings variation

theorem finiteFrameC2EinsteinHilbertVolumeDefectEuler_zero_eq_explicit
    (couplings : EinsteinHilbertCouplings) :
    finiteFrameC2EinsteinHilbertVolumeDefectEuler period hPeriod frame baseMetric couplings 0 =
      finiteFrameC2EinsteinHilbertVolumeDefectDerivativeAtZero period hPeriod frame baseMetric
        couplings :=
  (finiteFrameC2EinsteinHilbertVolumeDefectAction_hasFDerivAt_zero period hPeriod frame baseMetric
    couplings).fderiv

theorem finiteFrameC2EinsteinHilbertVolumeDefectDerivativeAtZero_apply
    (couplings : EinsteinHilbertCouplings)
    (direction : Model period hPeriod frame baseMetric) :
    finiteFrameC2EinsteinHilbertVolumeDefectDerivativeAtZero period hPeriod frame baseMetric
        couplings direction =
      ∫ point,
        finiteFrameCanonicalVolumeC0DerivativeAtZero period hPeriod frame baseMetric direction point *
          finiteFrameC2EinsteinHilbertScalarFactor period hPeriod frame baseMetric couplings 0 point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  unfold finiteFrameC2EinsteinHilbertVolumeDefectDerivativeAtZero
  rw [ContinuousLinearMap.comp_apply, finiteFrameBRSTCanonicalIntegralCLM_apply]
  rfl

end
end P0EFTJanusFiniteFrameC2EinsteinHilbertVolumeDefectDerivative4D
end JanusFormal
