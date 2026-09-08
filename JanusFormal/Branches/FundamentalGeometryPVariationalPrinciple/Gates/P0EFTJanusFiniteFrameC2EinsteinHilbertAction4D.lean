import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2ScalarCurvature4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2ProjectedScalarCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2CanonicalVolume4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D

/-! # Einstein-Hilbert action on the redundant finite-frame C² metric chart -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D

set_option autoImplicit false
set_option maxHeartbeats 800000
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
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameC2ScalarCurvature4D
open P0EFTJanusFiniteFrameC2ProjectedScalarCompletion4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
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

def finiteFrameC0Constant (value : Real) : C0Scalar period hPeriod :=
  ⟨fun _ => value, continuous_const⟩

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Model" => GeneralMetricRelativeC2Core period hPeriod frame baseMetric
local notation "Domain" => generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric

def finiteFrameC2EinsteinHilbertDensity (couplings : EinsteinHilbertCouplings)
    (variation : Model) : C0Scalar period hPeriod :=
  finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric variation *
    ((1 / (2 * couplings.gravitationalCoupling)) •
      (finiteFrameProjectedScalarCurvatureC0 period hPeriod frame baseMetric variation -
        finiteFrameC0Constant period hPeriod (2 * couplings.cosmologicalConstant)))

theorem finiteFrameC2EinsteinHilbertDensity_contDiffOn_two
    (couplings : EinsteinHilbertCouplings) :
    ContDiffOn Real 2
      (finiteFrameC2EinsteinHilbertDensity period hPeriod frame baseMetric couplings) Domain :=
  (finiteFrameCanonicalVolumeC0_contDiffOn_two period hPeriod frame baseMetric).mul
    (((finiteFrameProjectedScalarCurvatureC0_contDiffOn_two period hPeriod frame baseMetric).mono
      Set.inter_subset_left).sub contDiffOn_const |>.const_smul _)

def finiteFrameC2EinsteinHilbertAction (couplings : EinsteinHilbertCouplings)
    (variation : Model) : Real :=
  finiteFrameBRSTCanonicalIntegralCLM period hPeriod
    (finiteFrameC2EinsteinHilbertDensity period hPeriod frame baseMetric couplings variation)

theorem finiteFrameC2EinsteinHilbertAction_contDiffOn_two
    (couplings : EinsteinHilbertCouplings) :
    ContDiffOn Real 2
      (finiteFrameC2EinsteinHilbertAction period hPeriod frame baseMetric couplings) Domain :=
  (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).contDiff.comp_contDiffOn
    (finiteFrameC2EinsteinHilbertDensity_contDiffOn_two period hPeriod frame baseMetric couplings)

def finiteFrameC2EinsteinHilbertEuler (couplings : EinsteinHilbertCouplings)
    (variation : Model) : Model →L[Real] Real :=
  fderiv Real (finiteFrameC2EinsteinHilbertAction period hPeriod frame baseMetric couplings) variation

theorem finiteFrameC2EinsteinHilbertAction_hasFDerivAt
    (couplings : EinsteinHilbertCouplings) (variation : Model) (hVariation : variation ∈ Domain) :
    HasFDerivAt (finiteFrameC2EinsteinHilbertAction period hPeriod frame baseMetric couplings)
      (finiteFrameC2EinsteinHilbertEuler period hPeriod frame baseMetric couplings variation) variation :=
  (((finiteFrameC2EinsteinHilbertAction_contDiffOn_two period hPeriod frame baseMetric couplings
    variation hVariation).contDiffAt
      ((generalMetricRelativeC2VolumeDomain_isOpen period hPeriod frame baseMetric).mem_nhds
        hVariation)).differentiableAt (by norm_num)).hasFDerivAt

variable (plusFrame minusFrame : SmoothD8Frame period hPeriod)
  (plusMetric minusMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "PairModel" =>
  GeneralMetricRelativeC2Core period hPeriod plusFrame plusMetric ×
    GeneralMetricRelativeC2Core period hPeriod minusFrame minusMetric

def finiteFramePairedC2EinsteinHilbertDomain : Set PairModel :=
  generalMetricRelativeC2VolumeDomain period hPeriod plusFrame plusMetric ×ˢ
    generalMetricRelativeC2VolumeDomain period hPeriod minusFrame minusMetric

theorem finiteFramePairedC2EinsteinHilbertDomain_isOpen :
    IsOpen (finiteFramePairedC2EinsteinHilbertDomain period hPeriod plusFrame minusFrame
      plusMetric minusMetric) :=
  (generalMetricRelativeC2VolumeDomain_isOpen period hPeriod plusFrame plusMetric).prod
    (generalMetricRelativeC2VolumeDomain_isOpen period hPeriod minusFrame minusMetric)

def finiteFramePairedC2EinsteinHilbertAction
    (plusCouplings minusCouplings : EinsteinHilbertCouplings) (variation : PairModel) : Real :=
  finiteFrameC2EinsteinHilbertAction period hPeriod plusFrame plusMetric plusCouplings variation.1 +
    finiteFrameC2EinsteinHilbertAction period hPeriod minusFrame minusMetric minusCouplings variation.2

theorem finiteFramePairedC2EinsteinHilbertAction_contDiffOn_two
    (plusCouplings minusCouplings : EinsteinHilbertCouplings) :
    ContDiffOn Real 2
      (finiteFramePairedC2EinsteinHilbertAction period hPeriod plusFrame minusFrame
        plusMetric minusMetric plusCouplings minusCouplings)
      (finiteFramePairedC2EinsteinHilbertDomain period hPeriod plusFrame minusFrame
        plusMetric minusMetric) := by
  have hPlus : ContDiffOn Real 2
      (fun variation : PairModel => finiteFrameC2EinsteinHilbertAction period hPeriod plusFrame
        plusMetric plusCouplings variation.1)
      (finiteFramePairedC2EinsteinHilbertDomain period hPeriod plusFrame minusFrame
        plusMetric minusMetric) :=
    (finiteFrameC2EinsteinHilbertAction_contDiffOn_two period hPeriod plusFrame
      plusMetric plusCouplings).comp contDiff_fst.contDiffOn (fun _ hVariation => hVariation.1)
  have hMinus : ContDiffOn Real 2
      (fun variation : PairModel => finiteFrameC2EinsteinHilbertAction period hPeriod minusFrame
        minusMetric minusCouplings variation.2)
      (finiteFramePairedC2EinsteinHilbertDomain period hPeriod plusFrame minusFrame
        plusMetric minusMetric) :=
    (finiteFrameC2EinsteinHilbertAction_contDiffOn_two period hPeriod minusFrame
      minusMetric minusCouplings).comp contDiff_snd.contDiffOn (fun _ hVariation => hVariation.2)
  exact hPlus.add hMinus

end
end P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
end JanusFormal
