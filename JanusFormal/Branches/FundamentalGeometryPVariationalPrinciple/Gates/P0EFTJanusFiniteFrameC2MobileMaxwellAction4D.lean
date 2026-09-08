import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2MaxwellIntrinsicBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2CanonicalVolume4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D

/-! # Mobile Maxwell action on the redundant finite C² frame -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2MobileMaxwellAction4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameC2MaxwellPairing4D
open P0EFTJanusFiniteFrameC2MaxwellIntrinsicBridge4D

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
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)

local notation "MetricCore" =>
  GeneralMetricRelativeC2Core period hPeriod frame baseMetric
local notation "GaugeCore" => FiniteFrameAbelianGaugeC2Core period hPeriod frame
local notation "Input" => MetricCore × GaugeCore

/-- The positive-volume metric domain, with unrestricted gauge coefficients. -/
def finiteFrameC2MobileMaxwellDomain : Set Input :=
  generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric ×ˢ Set.univ

theorem finiteFrameC2MobileMaxwellDomain_isOpen :
    IsOpen (finiteFrameC2MobileMaxwellDomain period hPeriod frame baseMetric) :=
  (generalMetricRelativeC2VolumeDomain_isOpen period hPeriod frame baseMetric).prod isOpen_univ

/-- Mobile volume times the intrinsic `-1/4 F²` scalar. -/
def finiteFrameC2MobileMaxwellDensity (input : Input) : C0Scalar period hPeriod :=
  finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric input.1 *
    ((-(1 / 4 : Real)) •
      finiteFrameMaxwellPairingC0 period hPeriod frame baseMetric input.1 input.2)

theorem finiteFrameC2MobileMaxwellDensity_contDiffOn_two :
    ContDiffOn Real 2
      (finiteFrameC2MobileMaxwellDensity period hPeriod frame baseMetric)
      (finiteFrameC2MobileMaxwellDomain period hPeriod frame baseMetric) := by
  have hVolume : ContDiffOn Real 2
      (fun input : Input =>
        finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric input.1)
      (finiteFrameC2MobileMaxwellDomain period hPeriod frame baseMetric) :=
    (finiteFrameCanonicalVolumeC0_contDiffOn_two period hPeriod frame baseMetric).comp
      contDiff_fst.contDiffOn (fun _ h => h.1)
  have hPairing : ContDiffOn Real 2
      (fun input : Input =>
        finiteFrameMaxwellPairingC0 period hPeriod frame baseMetric input.1 input.2)
      (finiteFrameC2MobileMaxwellDomain period hPeriod frame baseMetric) :=
    ((finiteFrameMaxwellPairingC0_contDiffOn period hPeriod frame baseMetric).of_le
      (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).mono
        (fun _ h => ⟨h.1.1, h.2⟩)
  exact hVolume.mul (hPairing.const_smul (-(1 / 4 : Real)))

/-- Canonically integrated mobile Maxwell action. -/
def finiteFrameC2MobileMaxwellAction (input : Input) : Real :=
  finiteFrameBRSTCanonicalIntegralCLM period hPeriod
    (finiteFrameC2MobileMaxwellDensity period hPeriod frame baseMetric input)

theorem finiteFrameC2MobileMaxwellAction_contDiffOn_two :
    ContDiffOn Real 2
      (finiteFrameC2MobileMaxwellAction period hPeriod frame baseMetric)
      (finiteFrameC2MobileMaxwellDomain period hPeriod frame baseMetric) :=
  (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).contDiff.comp_contDiffOn
    (finiteFrameC2MobileMaxwellDensity_contDiffOn_two period hPeriod frame baseMetric)

def finiteFrameC2MobileMaxwellEuler (input : Input) : Input →L[Real] Real :=
  fderiv Real (finiteFrameC2MobileMaxwellAction period hPeriod frame baseMetric) input

theorem finiteFrameC2MobileMaxwellAction_hasFDerivAt
    (input : Input)
    (hInput : input ∈ finiteFrameC2MobileMaxwellDomain period hPeriod frame baseMetric) :
    HasFDerivAt (finiteFrameC2MobileMaxwellAction period hPeriod frame baseMetric)
      (finiteFrameC2MobileMaxwellEuler period hPeriod frame baseMetric input) input :=
  (((finiteFrameC2MobileMaxwellAction_contDiffOn_two period hPeriod frame baseMetric
    input hInput).contDiffAt
      ((finiteFrameC2MobileMaxwellDomain_isOpen period hPeriod frame baseMetric).mem_nhds
        hInput)).differentiableAt (by norm_num)).hasFDerivAt

/-- Smooth inputs give the mobile intrinsic Maxwell density. -/
theorem finiteFrameC2MobileMaxwellDensity_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation :
      smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
        generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    finiteFrameC2MobileMaxwellDensity period hPeriod frame baseMetric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation,
          finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame potential) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (smoothScalarFieldMul period hPeriod
          (globalSmoothMetricVolumeRatio period hPeriod metric)
          (frameFreeMaxwellDensity period hPeriod metric potential)) := by
  unfold finiteFrameC2MobileMaxwellDensity
  rw [finiteFrameCanonicalVolumeC0_smooth period hPeriod frame baseMetric variation metric
      hMetric hVariation,
    finiteFrameMaxwellPairingC0_smooth_intrinsic period hPeriod frame baseMetric
      variation metric hMetric hVariation.1 potential]
  apply ContinuousMap.ext
  intro point
  rfl

/-- Smooth agreement with the intrinsic Maxwell integral using the mobile volume. -/
theorem finiteFrameC2MobileMaxwellAction_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation :
      smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
        generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    finiteFrameC2MobileMaxwellAction period hPeriod frame baseMetric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation,
          finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame potential) =
      ∫ point,
        globalSmoothMetricVolumeRatio period hPeriod metric point *
          frameFreeMaxwellDensity period hPeriod metric potential point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  unfold finiteFrameC2MobileMaxwellAction
  rw [finiteFrameC2MobileMaxwellDensity_smooth period hPeriod frame baseMetric
      variation metric hMetric hVariation potential,
    finiteFrameBRSTCanonicalIntegralCLM_apply]
  rfl

abbrev FiniteFramePairedC2MaxwellCore
    (plusFrame minusFrame : SmoothD8Frame period hPeriod)
    (plusBase minusBase : SmoothGeneralLorentzMetric period hPeriod) :=
  (GeneralMetricRelativeC2Core period hPeriod plusFrame plusBase ×
      FiniteFrameAbelianGaugeC2Core period hPeriod plusFrame) ×
    (GeneralMetricRelativeC2Core period hPeriod minusFrame minusBase ×
      FiniteFrameAbelianGaugeC2Core period hPeriod minusFrame)

variable (plusFrame minusFrame : SmoothD8Frame period hPeriod)
  (plusBase minusBase : SmoothGeneralLorentzMetric period hPeriod)

local notation "PairInput" =>
  FiniteFramePairedC2MaxwellCore period hPeriod plusFrame minusFrame plusBase minusBase

def finiteFramePairedC2MobileMaxwellDomain : Set PairInput :=
  finiteFrameC2MobileMaxwellDomain period hPeriod plusFrame plusBase ×ˢ
    finiteFrameC2MobileMaxwellDomain period hPeriod minusFrame minusBase

theorem finiteFramePairedC2MobileMaxwellDomain_isOpen :
    IsOpen (finiteFramePairedC2MobileMaxwellDomain period hPeriod plusFrame minusFrame
      plusBase minusBase) :=
  (finiteFrameC2MobileMaxwellDomain_isOpen period hPeriod plusFrame plusBase).prod
    (finiteFrameC2MobileMaxwellDomain_isOpen period hPeriod minusFrame minusBase)

/-- Independently weighted Maxwell actions in the two sectors. -/
def finiteFramePairedC2MobileMaxwellAction
    (plusScale minusScale : Real) (input : PairInput) : Real :=
  plusScale *
      finiteFrameC2MobileMaxwellAction period hPeriod plusFrame plusBase input.1 +
    minusScale *
      finiteFrameC2MobileMaxwellAction period hPeriod minusFrame minusBase input.2

theorem finiteFramePairedC2MobileMaxwellAction_contDiffOn_two
    (plusScale minusScale : Real) :
    ContDiffOn Real 2
      (finiteFramePairedC2MobileMaxwellAction period hPeriod plusFrame minusFrame
        plusBase minusBase plusScale minusScale)
      (finiteFramePairedC2MobileMaxwellDomain period hPeriod plusFrame minusFrame
        plusBase minusBase) := by
  have hPlus : ContDiffOn Real 2
      (fun input : PairInput =>
        finiteFrameC2MobileMaxwellAction period hPeriod plusFrame plusBase input.1)
      (finiteFramePairedC2MobileMaxwellDomain period hPeriod plusFrame minusFrame
        plusBase minusBase) :=
    (finiteFrameC2MobileMaxwellAction_contDiffOn_two period hPeriod plusFrame plusBase).comp
      contDiff_fst.contDiffOn (fun _ h => h.1)
  have hMinus : ContDiffOn Real 2
      (fun input : PairInput =>
        finiteFrameC2MobileMaxwellAction period hPeriod minusFrame minusBase input.2)
      (finiteFramePairedC2MobileMaxwellDomain period hPeriod plusFrame minusFrame
        plusBase minusBase) :=
    (finiteFrameC2MobileMaxwellAction_contDiffOn_two period hPeriod minusFrame minusBase).comp
      contDiff_snd.contDiffOn (fun _ h => h.2)
  exact (contDiffOn_const.mul hPlus).add (contDiffOn_const.mul hMinus)

def finiteFramePairedC2MobileMaxwellEuler
    (plusScale minusScale : Real) (input : PairInput) : PairInput →L[Real] Real :=
  fderiv Real
    (finiteFramePairedC2MobileMaxwellAction period hPeriod plusFrame minusFrame
      plusBase minusBase plusScale minusScale) input

theorem finiteFramePairedC2MobileMaxwellAction_hasFDerivAt
    (plusScale minusScale : Real) (input : PairInput)
    (hInput : input ∈ finiteFramePairedC2MobileMaxwellDomain period hPeriod plusFrame
      minusFrame plusBase minusBase) :
    HasFDerivAt
      (finiteFramePairedC2MobileMaxwellAction period hPeriod plusFrame minusFrame
        plusBase minusBase plusScale minusScale)
      (finiteFramePairedC2MobileMaxwellEuler period hPeriod plusFrame minusFrame
        plusBase minusBase plusScale minusScale input) input :=
  (((finiteFramePairedC2MobileMaxwellAction_contDiffOn_two period hPeriod plusFrame
    minusFrame plusBase minusBase plusScale minusScale input hInput).contDiffAt
      ((finiteFramePairedC2MobileMaxwellDomain_isOpen period hPeriod plusFrame minusFrame
        plusBase minusBase).mem_nhds hInput)).differentiableAt (by norm_num)).hasFDerivAt

end
end P0EFTJanusFiniteFrameC2MobileMaxwellAction4D
end JanusFormal
