import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D

/-! # Smooth intrinsic agreement of the projected C² Einstein-Hilbert action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2ProjectedEinsteinHilbertAgreement4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameC2ProjectedScalarCompletion4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
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

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Domain" => generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric

/-- Smooth density represented by the migrated projected C² action. -/
def finiteFrameSmoothProjectedEinsteinHilbertDensity
    (couplings : EinsteinHilbertCouplings)
    (metric : SmoothGeneralLorentzMetric period hPeriod) : SmoothScalarField period hPeriod where
  toFun := fun point =>
    globalSmoothMetricVolumeRatio period hPeriod metric point *
      ((1 / (2 * couplings.gravitationalCoupling)) *
        (finiteFrameSmoothProjectedScalarCurvature period hPeriod frame baseMetric metric point -
          2 * couplings.cosmologicalConstant))
  contMDiff_toFun := (globalSmoothMetricVolumeRatio period hPeriod metric).contMDiff_toFun.mul
    (contMDiff_const.mul
      ((finiteFrameSmoothProjectedScalarCurvature period hPeriod frame baseMetric metric).contMDiff_toFun.sub
        contMDiff_const))

/-- The migrated C² density has the projected smooth density on smooth inputs. -/
theorem finiteFrameC2EinsteinHilbertDensity_smooth
    (couplings : EinsteinHilbertCouplings)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈ Domain) :
    finiteFrameC2EinsteinHilbertDensity period hPeriod frame baseMetric couplings
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameSmoothProjectedEinsteinHilbertDensity period hPeriod frame baseMetric couplings metric) := by
  unfold finiteFrameC2EinsteinHilbertDensity
  rw [finiteFrameCanonicalVolumeC0_smooth period hPeriod frame baseMetric variation metric hMetric hVariation,
    finiteFrameProjectedScalarCurvatureC0_smooth period hPeriod frame baseMetric variation metric
      hMetric hVariation.1]
  apply ContinuousMap.ext
  intro point
  rfl

/-- In every holonomic chart, the smooth migrated density uses intrinsic scalar curvature. -/
theorem finiteFrameSmoothProjectedEinsteinHilbertDensity_eq_intrinsic
    (couplings : EinsteinHilbertCouplings)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector) :
    finiteFrameSmoothProjectedEinsteinHilbertDensity period hPeriod frame baseMetric couplings metric
        (patch.coordinateMap coordinate) =
      globalSmoothMetricVolumeRatio period hPeriod metric (patch.coordinateMap coordinate) *
        ((1 / (2 * couplings.gravitationalCoupling)) *
          (localScalarCurvature period hPeriod metric patch coordinate -
            2 * couplings.cosmologicalConstant)) := by
  change _ * (_ * (finiteFrameSmoothProjectedScalarCurvature period hPeriod frame baseMetric metric
    (patch.coordinateMap coordinate) - _)) = _
  rw [finiteFrameSmoothProjectedScalarCurvature_eq_intrinsic period hPeriod frame baseMetric metric patch
    coordinate]

/-- On smooth inputs, the migrated action is the integral of its intrinsic projected density. -/
theorem finiteFrameC2EinsteinHilbertAction_smooth
    (couplings : EinsteinHilbertCouplings)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈ Domain) :
    finiteFrameC2EinsteinHilbertAction period hPeriod frame baseMetric couplings
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      ∫ point, finiteFrameSmoothProjectedEinsteinHilbertDensity period hPeriod frame baseMetric
        couplings metric point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  unfold finiteFrameC2EinsteinHilbertAction
  rw [finiteFrameC2EinsteinHilbertDensity_smooth period hPeriod frame baseMetric couplings variation metric
    hMetric hVariation, finiteFrameBRSTCanonicalIntegralCLM_apply]
  rfl

end
end P0EFTJanusFiniteFrameC2ProjectedEinsteinHilbertAgreement4D
end JanusFormal
