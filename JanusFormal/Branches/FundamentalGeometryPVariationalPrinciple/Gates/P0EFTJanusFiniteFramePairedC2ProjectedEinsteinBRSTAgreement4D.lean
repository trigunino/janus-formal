import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2ProjectedEinsteinHilbertAgreement4D

/-! # Smooth agreement of the paired projected Einstein-BRST action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2ProjectedEinsteinBRSTAgreement4D

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
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D
open P0EFTJanusFiniteFrameC2ProjectedEinsteinHilbertAgreement4D
open P0EFTJanusFiniteFramePairedC2ProjectedEinsteinHilbertAgreement4D

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

/-- The migrated Einstein-BRST action agrees with the intrinsic gravity and smooth BRST terms. -/
theorem finiteFramePairedC2EinsteinBRSTAction_smooth
    (source plusFrame minusFrame : SmoothD8Frame period hPeriod)
    (plusReference minusReference sourceReference : SmoothGeneralLorentzMetric period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (hPlusMetric : (metric .plus).tensor = plusReference.tensor + plusTensor)
    (hMinusMetric : (metric .minus).tensor = minusReference.tensor + minusTensor)
    (hPlusVolume : smoothToGeneralMetricRelativeC2Core period hPeriod plusFrame plusReference plusTensor ∈
      generalMetricRelativeC2VolumeDomain period hPeriod plusFrame plusReference)
    (hMinusVolume : smoothToGeneralMetricRelativeC2Core period hPeriod minusFrame minusReference minusTensor ∈
      generalMetricRelativeC2VolumeDomain period hPeriod minusFrame minusReference)
    (abelian : GlobalPairedAbelianBRSTState period hPeriod)
    (diffeomorphism : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    finiteFramePairedC2EinsteinBRSTAction period hPeriod source plusFrame minusFrame
        plusReference minusReference couplings
        (finiteFrameSmoothPairedC2FullBRSTGaugeCore period hPeriod source plusFrame minusFrame
          plusReference minusReference sourceReference plusTensor minusTensor abelian diffeomorphism) =
      ((∫ point, finiteFrameSmoothProjectedEinsteinHilbertDensity period hPeriod plusFrame plusReference
          couplings.plusEinstein (metric .plus) point
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
        ∫ point, finiteFrameSmoothProjectedEinsteinHilbertDensity period hPeriod minusFrame minusReference
          couplings.minusEinstein (metric .minus) point
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
      (globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric abelian
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
        globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation period hPeriod couplings metric
          { metricPerturbation := fun | .plus => plusTensor | .minus => minusTensor
            nonminimal := diffeomorphism }) := by
  unfold finiteFramePairedC2EinsteinBRSTAction
  rw [show
    (finiteFrameSmoothPairedC2FullBRSTGaugeCore period hPeriod source plusFrame minusFrame
      plusReference minusReference sourceReference plusTensor minusTensor abelian diffeomorphism).1 =
        (smoothToGeneralMetricRelativeC2Core period hPeriod plusFrame plusReference plusTensor,
          smoothToGeneralMetricRelativeC2Core period hPeriod minusFrame minusReference minusTensor) by rfl]
  rw [finiteFramePairedC2EinsteinHilbertAction_smooth period hPeriod plusFrame minusFrame
      plusReference minusReference (metric .plus) (metric .minus) couplings.plusEinstein
      couplings.minusEinstein plusTensor minusTensor hPlusMetric hMinusMetric hPlusVolume hMinusVolume,
    finiteFramePairedC2FullBRSTGaugeAction_smooth period hPeriod source plusFrame minusFrame
      plusReference minusReference sourceReference couplings plusTensor minusTensor metric hPlusMetric
      hMinusMetric hPlusVolume hMinusVolume abelian diffeomorphism]
  rfl

end
end P0EFTJanusFiniteFramePairedC2ProjectedEinsteinBRSTAgreement4D
end JanusFormal
