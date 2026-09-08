import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2EinsteinBRSTEulerDecomposition4D

/-! # Sector decomposition of the paired Einstein-Hilbert Euler map -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2EinsteinHilbertEulerSectors4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
open P0EFTJanusFiniteFramePairedC2EinsteinBRSTEulerDecomposition4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

variable (plusFrame minusFrame : SmoothD8Frame period hPeriod)
  (plusMetric minusMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "MetricPair" =>
  GeneralMetricRelativeC2Core period hPeriod plusFrame plusMetric ×
    GeneralMetricRelativeC2Core period hPeriod minusFrame minusMetric
local notation "Domain" => finiteFramePairedC2EinsteinHilbertDomain period hPeriod
  plusFrame minusFrame plusMetric minusMetric

/-- The paired Einstein-Hilbert Euler map is the sum of its two sector Eulers. -/
theorem finiteFramePairedC2EinsteinHilbertEuler_eq_sector_eulers
    (plusCouplings minusCouplings : EinsteinHilbertCouplings)
    (metric : MetricPair) (hMetric : metric ∈ Domain) :
    finiteFramePairedC2EinsteinHilbertEuler period hPeriod plusFrame minusFrame plusMetric
        minusMetric plusCouplings minusCouplings metric =
      (finiteFrameC2EinsteinHilbertEuler period hPeriod plusFrame plusMetric plusCouplings
        metric.1).comp (ContinuousLinearMap.fst Real _ _) +
      (finiteFrameC2EinsteinHilbertEuler period hPeriod minusFrame minusMetric minusCouplings
        metric.2).comp (ContinuousLinearMap.snd Real _ _) := by
  have hFst : HasFDerivAt (fun current : MetricPair => current.1)
      (ContinuousLinearMap.fst Real _ _) metric := by
    fun_prop
  have hSnd : HasFDerivAt (fun current : MetricPair => current.2)
      (ContinuousLinearMap.snd Real _ _) metric := by
    fun_prop
  have hPlus :=
    (finiteFrameC2EinsteinHilbertAction_hasFDerivAt period hPeriod plusFrame plusMetric
      plusCouplings metric.1 hMetric.1).comp metric hFst
  have hMinus :=
    (finiteFrameC2EinsteinHilbertAction_hasFDerivAt period hPeriod minusFrame minusMetric
      minusCouplings metric.2 hMetric.2).comp metric hSnd
  unfold finiteFramePairedC2EinsteinHilbertEuler finiteFramePairedC2EinsteinHilbertAction
  change fderiv Real
      ((fun current : MetricPair =>
        finiteFrameC2EinsteinHilbertAction period hPeriod plusFrame plusMetric plusCouplings
          current.1) +
       (fun current : MetricPair =>
        finiteFrameC2EinsteinHilbertAction period hPeriod minusFrame minusMetric minusCouplings
          current.2)) metric = _
  exact (hPlus.add hMinus).fderiv

end
end P0EFTJanusFiniteFramePairedC2EinsteinHilbertEulerSectors4D
end JanusFormal
