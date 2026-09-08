import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2ProjectedPhysicalAgreement4D

/-! # Intrinsic agreement of the physical C² action at its metric center -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2ProjectedPhysicalCenterAgreement4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff MeasureTheory
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
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFrameC2ProjectedEinsteinHilbertAgreement4D
open P0EFTJanusFiniteFrameC2InteractionCenterAgreement4D
open P0EFTJanusFiniteFramePairedC2ProjectedPhysicalAgreement4D
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

/-- The actual Candidate-A pair of smooth metrics. -/
def candidateAPairedMetric (geometry : GlobalCandidateAGeometry period hPeriod) :
    Sector → SmoothGeneralLorentzMetric period hPeriod
  | .plus => geometry.plusMetric
  | .minus => geometry.minusMetric

/-- At the centered metrics, every physical contribution has its intrinsic global expression. -/
theorem finiteFramePairedC2PhysicalAction_centerMetrics_smooth
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point))
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (abelian : GlobalPairedAbelianBRSTState period hPeriod)
    (diffeomorphism : GlobalDiffeomorphismNonminimalFields period hPeriod)
    (basis : ∀ point : EffectiveQuotient period hPeriod,
      Module.Basis (Fin 4) Real (TangentSpace coverModelWithCorners point)) :
    finiteFramePairedC2PhysicalAction period hPeriod geometry frame hRegular couplings interactionScale
        coefficients
        (finiteFrameSmoothPairedC2FullBRSTGaugeCore period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric geometry.plusMetric 0 0 abelian diffeomorphism) =
      (((∫ point, finiteFrameSmoothProjectedEinsteinHilbertDensity period hPeriod frame
            geometry.plusMetric couplings.plusEinstein geometry.plusMetric point
            ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
          ∫ point, finiteFrameSmoothProjectedEinsteinHilbertDensity period hPeriod frame
            geometry.plusMetric couplings.minusEinstein geometry.minusMetric point
            ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
        (globalPairedAbelianGaugeFermionBRSTAction period hPeriod
            (candidateAPairedMetric period hPeriod geometry) abelian
            (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
          globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation period hPeriod couplings
            (candidateAPairedMetric period hPeriod geometry)
            { metricPerturbation := fun sector => match sector with
                | .plus => 0
                | .minus => geometry.minusMetric.tensor - geometry.plusMetric.tensor
              nonminimal := diffeomorphism })) +
      ∫ point, -interactionScale * globalMetricVolumeRatio period hPeriod geometry.plusMetric point *
        matrixSpectralPotential coefficients
          (LinearMap.toMatrix (basis point) (basis point) (geometry.rootAt point).toLinearMap)
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  have hPlusMetric :
      (candidateAPairedMetric period hPeriod geometry .plus).tensor =
        geometry.plusMetric.tensor + 0 := by simp [candidateAPairedMetric]
  have hMinusMetric :
      (candidateAPairedMetric period hPeriod geometry .minus).tensor =
        geometry.minusMetric.tensor + 0 := by simp [candidateAPairedMetric]
  have hMinusVolume :
      smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric
          ((geometry.minusMetric.tensor - geometry.plusMetric.tensor) + 0) ∈
        generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric := by
    simpa [finiteFramePairedC2MinusCenter] using hMinusCenter
  have hPlusVolume :
      smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric 0 ∈
        generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric := by
    simpa using zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric
  rw [finiteFramePairedC2PhysicalAction_smooth_gravity_BRST period hPeriod geometry frame hRegular
    couplings interactionScale coefficients 0 0 (candidateAPairedMetric period hPeriod geometry)
    hPlusMetric hMinusMetric
    hPlusVolume hMinusVolume abelian diffeomorphism]
  rw [show
    (smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric 0,
      smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric 0) = 0 by
        simp]
  rw [pairedFiniteFrameC2InteractionAction_zero_eq_intrinsic period hPeriod geometry frame hRegular
    interactionScale coefficients basis]
  simp [candidateAPairedMetric]
  rfl

end
end P0EFTJanusFiniteFramePairedC2ProjectedPhysicalCenterAgreement4D
end JanusFormal
