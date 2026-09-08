import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2ProjectedEinsteinBRSTAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2InteractionAction4D

/-! # Intrinsic center agreement of the C² interaction action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2InteractionCenterAgreement4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff MeasureTheory
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFramePairedC2InteractionAction4D
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusReciprocalBimetricPotential

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
local instance : MeasureTheory.IsFiniteMeasure
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- At the chart center, the C² interaction action is the intrinsic root potential integral. -/
theorem pairedFiniteFrameC2InteractionAction_zero_eq_intrinsic
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (basis : ∀ point : EffectiveQuotient period hPeriod,
      Module.Basis (Fin 4) Real (TangentSpace coverModelWithCorners point)) :
    pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular
        interactionScale coefficients 0 =
      ∫ point, -interactionScale * globalMetricVolumeRatio period hPeriod geometry.plusMetric point *
        matrixSpectralPotential coefficients
          (LinearMap.toMatrix (basis point) (basis point) (geometry.rootAt point).toLinearMap)
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  unfold pairedFiniteFrameC2InteractionAction
  rw [finiteFrameBRSTCanonicalIntegralCLM_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    pairedFiniteFrameC2InteractionDensity_zero_valueAt period hPeriod geometry frame hRegular
      interactionScale coefficients point (basis point)

end
end P0EFTJanusFiniteFrameC2InteractionCenterAgreement4D
end JanusFormal
