import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2ProjectedEinsteinHilbertAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D

/-! # Smooth agreement of the paired projected C² Einstein-Hilbert action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2ProjectedEinsteinHilbertAgreement4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
open P0EFTJanusFiniteFrameC2ProjectedEinsteinHilbertAgreement4D

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

/-- Both sectors of the paired migrated action are their intrinsic projected integrals. -/
theorem finiteFramePairedC2EinsteinHilbertAction_smooth
    (plusFrame minusFrame : SmoothD8Frame period hPeriod)
    (plusBase minusBase plusMetric minusMetric : SmoothGeneralLorentzMetric period hPeriod)
    (plusCouplings minusCouplings : EinsteinHilbertCouplings)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hPlusMetric : plusMetric.tensor = plusBase.tensor + plusVariation)
    (hMinusMetric : minusMetric.tensor = minusBase.tensor + minusVariation)
    (hPlus : smoothToGeneralMetricRelativeC2Core period hPeriod plusFrame plusBase plusVariation ∈
      generalMetricRelativeC2VolumeDomain period hPeriod plusFrame plusBase)
    (hMinus : smoothToGeneralMetricRelativeC2Core period hPeriod minusFrame minusBase minusVariation ∈
      generalMetricRelativeC2VolumeDomain period hPeriod minusFrame minusBase) :
    finiteFramePairedC2EinsteinHilbertAction period hPeriod plusFrame minusFrame plusBase minusBase
        plusCouplings minusCouplings
        (smoothToGeneralMetricRelativeC2Core period hPeriod plusFrame plusBase plusVariation,
          smoothToGeneralMetricRelativeC2Core period hPeriod minusFrame minusBase minusVariation) =
      (∫ point, finiteFrameSmoothProjectedEinsteinHilbertDensity period hPeriod plusFrame plusBase
          plusCouplings plusMetric point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
        ∫ point, finiteFrameSmoothProjectedEinsteinHilbertDensity period hPeriod minusFrame minusBase
          minusCouplings minusMetric point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  unfold finiteFramePairedC2EinsteinHilbertAction
  rw [finiteFrameC2EinsteinHilbertAction_smooth period hPeriod plusFrame plusBase plusCouplings
      plusVariation plusMetric hPlusMetric hPlus,
    finiteFrameC2EinsteinHilbertAction_smooth period hPeriod minusFrame minusBase minusCouplings
      minusVariation minusMetric hMinusMetric hMinus]

end
end P0EFTJanusFiniteFramePairedC2ProjectedEinsteinHilbertAgreement4D
end JanusFormal
