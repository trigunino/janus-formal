import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2InteractionCenterAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalAction4D

/-! # Smooth gravity-BRST agreement of the recentered physical C² action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2ProjectedPhysicalAgreement4D

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
open P0EFTJanusFiniteFramePairedC2InteractionAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFrameC2ProjectedEinsteinHilbertAgreement4D
open P0EFTJanusFiniteFramePairedC2ProjectedEinsteinBRSTAgreement4D
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

/-- The recentered physical action has intrinsic projected gravity and the established smooth BRST terms. -/
theorem finiteFramePairedC2PhysicalAction_smooth_gravity_BRST
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point))
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (hPlusMetric : (metric .plus).tensor = geometry.plusMetric.tensor + plusVariation)
    (hMinusMetric : (metric .minus).tensor = geometry.minusMetric.tensor + minusVariation)
    (hPlusVolume : smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric
        plusVariation ∈ generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (hMinusVolume : smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric
        ((geometry.minusMetric.tensor - geometry.plusMetric.tensor) + minusVariation) ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (abelian : GlobalPairedAbelianBRSTState period hPeriod)
    (diffeomorphism : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    finiteFramePairedC2PhysicalAction period hPeriod geometry frame hRegular couplings interactionScale
        coefficients
        (finiteFrameSmoothPairedC2FullBRSTGaugeCore period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric geometry.plusMetric plusVariation minusVariation
          abelian diffeomorphism) =
      (((∫ point, finiteFrameSmoothProjectedEinsteinHilbertDensity period hPeriod frame
            geometry.plusMetric couplings.plusEinstein (metric .plus) point
            ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
          ∫ point, finiteFrameSmoothProjectedEinsteinHilbertDensity period hPeriod frame
            geometry.plusMetric couplings.minusEinstein (metric .minus) point
            ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
        (globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric abelian
            (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
          globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation period hPeriod couplings metric
            { metricPerturbation := fun sector => match sector with
                | .plus => plusVariation
                | .minus => (geometry.minusMetric.tensor - geometry.plusMetric.tensor) + minusVariation
              nonminimal := diffeomorphism })) +
      pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular interactionScale
        coefficients
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric plusVariation,
          smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric minusVariation) := by
  let recenteredMinus := (geometry.minusMetric.tensor - geometry.plusMetric.tensor) + minusVariation
  have hRecenter :
      finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame
        (finiteFrameSmoothPairedC2FullBRSTGaugeCore period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric geometry.plusMetric plusVariation minusVariation
          abelian diffeomorphism) =
      finiteFrameSmoothPairedC2FullBRSTGaugeCore period hPeriod frame frame frame
        geometry.plusMetric geometry.plusMetric geometry.plusMetric plusVariation recenteredMinus
        abelian diffeomorphism := by
    unfold finiteFrameSmoothPairedC2FullBRSTGaugeCore
    exact finiteFramePairedC2PhysicalRecenter_smooth period hPeriod geometry frame plusVariation
      minusVariation _
  have hMinusRecentered :
      (metric .minus).tensor = geometry.plusMetric.tensor + recenteredMinus := by
    rw [hMinusMetric]
    dsimp [recenteredMinus]
    abel
  unfold finiteFramePairedC2PhysicalAction
  rw [hRecenter]
  rw [finiteFramePairedC2EinsteinBRSTAction_smooth period hPeriod frame frame frame
    geometry.plusMetric geometry.plusMetric geometry.plusMetric couplings plusVariation recenteredMinus metric
    hPlusMetric hMinusRecentered hPlusVolume hMinusVolume abelian diffeomorphism]
  rfl

end
end P0EFTJanusFiniteFramePairedC2ProjectedPhysicalAgreement4D
end JanusFormal
