import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2FrozenInteractionDerivativeBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2InteractionVolumeDefectDerivative4D

/-! # Mobile-volume interaction derivative across the finite-frame/regular bridge -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularC2MobileInteractionDerivativeBridge4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 8000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D
open P0EFTJanusFiniteFramePairedRelativeC2Root4D
open P0EFTJanusFiniteFrameC2SpectralInteraction4D
open P0EFTJanusFiniteFramePairedC2InteractionAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerChainRule4D
open P0EFTJanusFiniteFrameC2InteractionFrozenVolumeDecomposition4D
open P0EFTJanusFiniteFrameC2InteractionVolumeDefectDerivative4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusFiniteFrameRegularC2FrozenInteractionDerivativeBridge4D
open P0EFTJanusPairedInteractionRecenterValue4D
open P0EFTJanusReciprocalBimetricPotential

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
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- The actual mobile-volume finite Euler is the regular fixed-volume
derivative plus the exact finite volume defect on every common smooth lift. -/
theorem pairedFiniteFrameC2InteractionEuler_zero_smooth_lifts_regular_add_volumeDefect
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
    let finiteDirection :=
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric plusVariation,
        smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric minusVariation)
    pairedFiniteFrameC2InteractionEuler period hPeriod geometry frame hFiniteRegular
        interactionScale coefficients 0 finiteDirection =
      regularGeneralMetricC2PairedInteractionC2ActionDerivative period hPeriod plusBase minusBase
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) interactionScale coefficients
          0 hZero
          (pairedInteractionSmoothCore period hPeriod plusBase minusBase plusVariation
            minusVariation) +
        pairedFiniteFrameC2InteractionVolumeDefectDerivativeAtZero period hPeriod geometry frame
          hFiniteRegular interactionScale coefficients finiteDirection := by
  dsimp only
  rw [pairedFiniteFrameC2InteractionEuler_eq_frozen_add_volumeDefect period hPeriod
      (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
      frame
      (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
        plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
      interactionScale coefficients 0
      (zero_mem_pairedFiniteFrameC2InteractionDomain period hPeriod
        (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
        frame
        (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
          plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart))]
  simp only [add_apply]
  apply congrArg₂ (fun first second : Real => first + second)
  · exact pairedFiniteFrameC2FrozenVolumeInteractionEuler_zero_smooth_lifts_regular period hPeriod
      interactionScale coefficients plusBase minusBase hCanonicalVolume hChart frame hZero
        plusVariation minusVariation
  · exact congrArg
      (fun derivative : PairedFiniteFrameMetricC2Core period hPeriod
          (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart) frame →L[Real] Real =>
        derivative
          (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric plusVariation,
            smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric minusVariation))
      (pairedFiniteFrameC2InteractionVolumeDefectEuler_zero_eq_explicit period hPeriod
        (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
        frame
        (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
          plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
        interactionScale coefficients)

end
end P0EFTJanusFiniteFrameRegularC2MobileInteractionDerivativeBridge4D
end JanusFormal
