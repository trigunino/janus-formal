import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2InteractionFrozenVolumeDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D

/-! # Frozen interaction derivative across the finite-frame/regular bridge -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularC2FrozenInteractionDerivativeBridge4D

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 8000

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D
open P0EFTJanusProgramPGeneralMetricC2IntegratedVolume4D
open P0EFTJanusFiniteFramePairedRelativeC2Root4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameC2SpectralInteraction4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameC2InteractionFrozenVolumeDecomposition4D
open P0EFTJanusFiniteFrameC2SpectralPotentialDerivativeAtCenter4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusPairedInteractionRecenterValue4D
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
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
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

variable (geometry : GlobalCandidateAGeometry period hPeriod)
  (frame : SmoothD8Frame period hPeriod)
  (hRegular : ∀ point, Function.Bijective
    (intrinsicCandidateASylvesterAt period hPeriod geometry point))

private abbrev Model := PairedFiniteFrameMetricC2Core period hPeriod geometry frame

/-- Exact derivative at the center of the frozen-volume finite density. -/
def pairedFiniteFrameC2FrozenVolumeInteractionDensityDerivativeAtZero
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    Model period hPeriod geometry frame →L[Real] C0Scalar period hPeriod :=
  (-interactionScale) •
    ((ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
      (finiteFrameCanonicalVolumeC0 period hPeriod frame geometry.plusMetric 0)).comp
      ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
        (pairedFiniteFrameC2SpectralPotentialDerivativeAtZero period hPeriod geometry frame
          hRegular coefficients)))

theorem pairedFiniteFrameC2FrozenVolumeInteractionDensity_hasFDerivAt_zero
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    HasFDerivAt
      (pairedFiniteFrameC2FrozenVolumeInteractionDensity period hPeriod geometry frame hRegular
        interactionScale coefficients)
      (pairedFiniteFrameC2FrozenVolumeInteractionDensityDerivativeAtZero period hPeriod geometry
        frame hRegular interactionScale coefficients) 0 := by
  let readout := canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
  let multiply := ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
    (finiteFrameCanonicalVolumeC0 period hPeriod frame geometry.plusMetric 0)
  have hPotential := pairedFiniteFrameC2SpectralPotential_hasFDerivAt_zero
    period hPeriod geometry frame hRegular coefficients
  have hReadout := HasFDerivAt.comp
    (f := pairedFiniteFrameC2SpectralPotential period hPeriod frame geometry hRegular coefficients)
    (g := fun field => readout field) 0 readout.hasFDerivAt hPotential
  have hMultiply := HasFDerivAt.comp
    (f := fun variation => readout
      (pairedFiniteFrameC2SpectralPotential period hPeriod frame geometry hRegular coefficients
        variation))
    (g := fun field => multiply field) 0 multiply.hasFDerivAt hReadout
  apply (hMultiply.const_smul (-interactionScale)).congr_of_eventuallyEq
  filter_upwards [] with variation
  rfl

theorem pairedFiniteFrameC2FrozenVolumeInteractionDensityDerivativeAtZero_valueAt
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (direction : Model period hPeriod geometry frame)
    (point : EffectiveQuotient period hPeriod) :
    pairedFiniteFrameC2FrozenVolumeInteractionDensityDerivativeAtZero period hPeriod geometry
        frame hRegular interactionScale coefficients direction point =
      (-interactionScale) *
        finiteFrameCanonicalVolumeC0 period hPeriod frame geometry.plusMetric 0 point *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (pairedFiniteFrameC2SpectralPotentialDerivativeAtZero period hPeriod geometry frame
            hRegular coefficients direction) point := by
  simp only [pairedFiniteFrameC2FrozenVolumeInteractionDensityDerivativeAtZero,
    smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', ContinuousMap.smul_apply, ContinuousMap.mul_apply,
    smul_eq_mul]
  ring

/-- Exact derivative at the center of the integrated frozen-volume action. -/
def pairedFiniteFrameC2FrozenVolumeInteractionActionDerivativeAtZero
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    Model period hPeriod geometry frame →L[Real] Real :=
  (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).comp
    (pairedFiniteFrameC2FrozenVolumeInteractionDensityDerivativeAtZero period hPeriod geometry
      frame hRegular interactionScale coefficients)

theorem pairedFiniteFrameC2FrozenVolumeInteractionAction_hasFDerivAt_zero
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    HasFDerivAt
      (pairedFiniteFrameC2FrozenVolumeInteractionAction period hPeriod geometry frame hRegular
        interactionScale coefficients)
      (pairedFiniteFrameC2FrozenVolumeInteractionActionDerivativeAtZero period hPeriod geometry
        frame hRegular interactionScale coefficients) 0 := by
  have hDensity :=
    pairedFiniteFrameC2FrozenVolumeInteractionDensity_hasFDerivAt_zero period hPeriod geometry
      frame hRegular interactionScale coefficients
  have hIntegral := HasFDerivAt.comp
    (f := pairedFiniteFrameC2FrozenVolumeInteractionDensity period hPeriod geometry frame hRegular
      interactionScale coefficients)
    (g := fun field => finiteFrameBRSTCanonicalIntegralCLM period hPeriod field) 0
    (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).hasFDerivAt hDensity
  apply hIntegral.congr_of_eventuallyEq
  filter_upwards [] with variation
  rfl

theorem pairedFiniteFrameC2FrozenVolumeInteractionEuler_zero_eq_explicit
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    pairedFiniteFrameC2FrozenVolumeInteractionEuler period hPeriod geometry frame hRegular
        interactionScale coefficients 0 =
      pairedFiniteFrameC2FrozenVolumeInteractionActionDerivativeAtZero period hPeriod geometry
        frame hRegular interactionScale coefficients :=
  (pairedFiniteFrameC2FrozenVolumeInteractionAction_hasFDerivAt_zero period hPeriod geometry frame
    hRegular interactionScale coefficients).fderiv

theorem pairedFiniteFrameC2FrozenVolumeInteractionActionDerivativeAtZero_apply
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (direction : Model period hPeriod geometry frame) :
    pairedFiniteFrameC2FrozenVolumeInteractionActionDerivativeAtZero period hPeriod geometry frame
        hRegular interactionScale coefficients direction =
      ∫ point,
        (-interactionScale) *
          finiteFrameCanonicalVolumeC0 period hPeriod frame geometry.plusMetric 0 point *
          canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
            (pairedFiniteFrameC2SpectralPotentialDerivativeAtZero period hPeriod geometry frame
              hRegular coefficients direction) point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  unfold pairedFiniteFrameC2FrozenVolumeInteractionActionDerivativeAtZero
  rw [ContinuousLinearMap.comp_apply, finiteFrameBRSTCanonicalIntegralCLM_apply]
  apply integral_congr_ae
  filter_upwards [] with point
  exact pairedFiniteFrameC2FrozenVolumeInteractionDensityDerivativeAtZero_valueAt period hPeriod
    geometry frame hRegular interactionScale coefficients direction point

/-- In canonical-volume gauge, the frozen finite density derivative on smooth
lifts is the regular paired interaction density derivative. -/
theorem pairedFiniteFrameC2FrozenVolumeInteractionDensityDerivativeAtZero_smooth_lifts_regular
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hCanonicalVolume : plusBase.volume =
      globalSmoothMetricVolumeRatio period hPeriod plusBase.metric)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore
        period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hFiniteRegular :=
      regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
        plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    pairedFiniteFrameC2FrozenVolumeInteractionDensityDerivativeAtZero period hPeriod geometry frame
        hFiniteRegular interactionScale coefficients
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric plusVariation,
          smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric minusVariation)
        point =
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (regularGeneralMetricC2PairedInteractionC2DensityDerivative period hPeriod plusBase minusBase
          interactionScale coefficients 0 hZero
          (pairedInteractionSmoothCore period hPeriod plusBase minusBase plusVariation
            minusVariation)) point := by
  dsimp only
  rw [pairedFiniteFrameC2FrozenVolumeInteractionDensityDerivativeAtZero_valueAt,
    regularGeneralMetricC2PairedInteractionC2DensityDerivative_valueAt]
  have hFiniteVolume := congrArg
    (fun field : C0Scalar period hPeriod => field point)
    (finiteFrameCanonicalVolumeC0_zero period hPeriod frame
      (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) hChart).plusMetric)
  change finiteFrameCanonicalVolumeC0 period hPeriod frame
      (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) hChart).plusMetric 0 point =
    globalMetricVolumeRatio period hPeriod
      (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) hChart).plusMetric point at hFiniteVolume
  have hGeometryVolume :
      globalMetricVolumeRatio period hPeriod
          (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart).plusMetric point =
        globalMetricVolumeRatio period hPeriod plusBase.metric point := by
    rw [regularGeneralMetricC2LorentzChartGeometry_plusMetric]
  have hVolume := congrArg
    (fun field : SmoothScalarField period hPeriod => field point) hCanonicalVolume
  change plusBase.volume point =
    globalMetricVolumeRatio period hPeriod plusBase.metric point at hVolume
  have hSpectral :=
    pairedFiniteFrameC2SpectralPotentialDerivativeAtZero_smooth_lifts_regular_of_chart
      period hPeriod coefficients plusBase minusBase hChart frame hZero plusVariation
        minusVariation point
  rw [hFiniteVolume, hGeometryVolume, ← hVolume, hSpectral]

/-- The integrated frozen finite derivative agrees with the regular paired
action derivative on every common smooth lift in canonical-volume gauge. -/
theorem pairedFiniteFrameC2FrozenVolumeInteractionActionDerivativeAtZero_smooth_lifts_regular
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hCanonicalVolume : plusBase.volume =
      globalSmoothMetricVolumeRatio period hPeriod plusBase.metric)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore
        period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hFiniteRegular :=
      regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
        plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    pairedFiniteFrameC2FrozenVolumeInteractionActionDerivativeAtZero period hPeriod geometry frame
        hFiniteRegular interactionScale coefficients
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric plusVariation,
          smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric minusVariation) =
      regularGeneralMetricC2PairedInteractionC2ActionDerivative period hPeriod plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) interactionScale coefficients 0 hZero
        (pairedInteractionSmoothCore period hPeriod plusBase minusBase plusVariation
          minusVariation) := by
  dsimp only
  unfold pairedFiniteFrameC2FrozenVolumeInteractionActionDerivativeAtZero
    regularGeneralMetricC2PairedInteractionC2ActionDerivative
  simp only [ContinuousLinearMap.comp_apply]
  rw [finiteFrameBRSTCanonicalIntegralCLM_apply,
    canonicalPhysicalC2ScalarIntegralCLM_apply]
  apply integral_congr_ae
  filter_upwards [] with point
  exact pairedFiniteFrameC2FrozenVolumeInteractionDensityDerivativeAtZero_smooth_lifts_regular
    period hPeriod interactionScale coefficients plusBase minusBase hCanonicalVolume hChart frame
      hZero plusVariation minusVariation point

/-- The actual finite frozen Euler at the chart center is the regular action
derivative on every common smooth lift in canonical-volume gauge. -/
theorem pairedFiniteFrameC2FrozenVolumeInteractionEuler_zero_smooth_lifts_regular
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hCanonicalVolume : plusBase.volume =
      globalSmoothMetricVolumeRatio period hPeriod plusBase.metric)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore
        period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hFiniteRegular :=
      regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
        plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    pairedFiniteFrameC2FrozenVolumeInteractionEuler period hPeriod geometry frame hFiniteRegular
        interactionScale coefficients 0
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric plusVariation,
          smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric minusVariation) =
      regularGeneralMetricC2PairedInteractionC2ActionDerivative period hPeriod plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) interactionScale coefficients 0 hZero
        (pairedInteractionSmoothCore period hPeriod plusBase minusBase plusVariation
          minusVariation) := by
  dsimp only
  rw [pairedFiniteFrameC2FrozenVolumeInteractionEuler_zero_eq_explicit]
  exact
    pairedFiniteFrameC2FrozenVolumeInteractionActionDerivativeAtZero_smooth_lifts_regular
      period hPeriod interactionScale coefficients plusBase minusBase hCanonicalVolume hChart frame
        hZero plusVariation minusVariation

end
end P0EFTJanusFiniteFrameRegularC2FrozenInteractionDerivativeBridge4D
end JanusFormal
