import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalEulerChainRule4D

/-! # Euler decomposition of the paired Einstein-BRST action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2EinsteinBRSTEulerDecomposition4D

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
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D

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

variable (source plusFrame minusFrame : SmoothD8Frame period hPeriod)
  (plusMetric minusMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Input" => FiniteFramePairedC2FullBRSTGaugeCore period hPeriod
  source plusFrame minusFrame plusMetric minusMetric
local notation "MetricPair" =>
  GeneralMetricRelativeC2Core period hPeriod plusFrame plusMetric ×
    GeneralMetricRelativeC2Core period hPeriod minusFrame minusMetric
local notation "Domain" => finiteFramePairedC2FullBRSTGaugeDomain period hPeriod
  source plusFrame minusFrame plusMetric minusMetric

/-- Euler map of the paired C² Einstein-Hilbert block. -/
def finiteFramePairedC2EinsteinHilbertEuler
    (plusCouplings minusCouplings : EinsteinHilbertCouplings) (metric : MetricPair) :
    MetricPair →L[Real] Real :=
  fderiv Real (finiteFramePairedC2EinsteinHilbertAction period hPeriod plusFrame minusFrame
    plusMetric minusMetric plusCouplings minusCouplings) metric

private theorem einstein_fst_fderiv
    (couplings : GlobalCandidateAActionCouplings) (input : Input) (hInput : input ∈ Domain) :
    fderiv Real
        (fun current : Input =>
          finiteFramePairedC2EinsteinHilbertAction period hPeriod plusFrame minusFrame
            plusMetric minusMetric couplings.plusEinstein couplings.minusEinstein current.1) input =
      (finiteFramePairedC2EinsteinHilbertEuler period hPeriod plusFrame minusFrame plusMetric
        minusMetric couplings.plusEinstein couplings.minusEinstein input.1).comp
        (ContinuousLinearMap.fst Real MetricPair _) := by
  have hAction : DifferentiableAt Real
      (finiteFramePairedC2EinsteinHilbertAction period hPeriod plusFrame minusFrame plusMetric
        minusMetric couplings.plusEinstein couplings.minusEinstein) input.1 :=
    (((finiteFramePairedC2EinsteinHilbertAction_contDiffOn_two period hPeriod plusFrame minusFrame
      plusMetric minusMetric couplings.plusEinstein couplings.minusEinstein) input.1 hInput.1).contDiffAt
        ((finiteFramePairedC2EinsteinHilbertDomain_isOpen period hPeriod plusFrame minusFrame
          plusMetric minusMetric).mem_nhds hInput.1)).differentiableAt (by norm_num)
  have hFst : HasFDerivAt (fun current : Input => current.1)
      (ContinuousLinearMap.fst Real MetricPair _) input := by
    fun_prop
  have hChain := hAction.hasFDerivAt.comp input hFst
  unfold finiteFramePairedC2EinsteinHilbertEuler
  exact hChain.fderiv

/-- The Einstein-BRST Euler map splits into the projected Einstein-Hilbert and BRST Eulers. -/
theorem finiteFramePairedC2EinsteinBRSTEuler_eq_component_eulers
    (couplings : GlobalCandidateAActionCouplings) (input : Input) (hInput : input ∈ Domain) :
    finiteFramePairedC2EinsteinBRSTEuler period hPeriod source plusFrame minusFrame plusMetric
        minusMetric couplings input =
      (finiteFramePairedC2EinsteinHilbertEuler period hPeriod plusFrame minusFrame plusMetric
        minusMetric couplings.plusEinstein couplings.minusEinstein input.1).comp
          (ContinuousLinearMap.fst Real MetricPair _) +
        finiteFramePairedC2FullBRSTGaugeEuler period hPeriod source plusFrame minusFrame plusMetric
          minusMetric couplings input := by
  have hEinstein : DifferentiableAt Real
      (fun current : Input =>
        finiteFramePairedC2EinsteinHilbertAction period hPeriod plusFrame minusFrame plusMetric
          minusMetric couplings.plusEinstein couplings.minusEinstein current.1) input :=
    ((((finiteFramePairedC2EinsteinHilbertAction_contDiffOn_two period hPeriod plusFrame minusFrame
      plusMetric minusMetric couplings.plusEinstein couplings.minusEinstein) input.1 hInput.1).contDiffAt
        ((finiteFramePairedC2EinsteinHilbertDomain_isOpen period hPeriod plusFrame minusFrame
          plusMetric minusMetric).mem_nhds hInput.1)).differentiableAt (by norm_num)).comp input
            differentiableAt_fst
  have hBRST : DifferentiableAt Real
      (finiteFramePairedC2FullBRSTGaugeAction period hPeriod source plusFrame minusFrame plusMetric
        minusMetric couplings) input :=
    (finiteFramePairedC2FullBRSTGaugeAction_hasFDerivAt period hPeriod source plusFrame minusFrame
      plusMetric minusMetric couplings input hInput).differentiableAt
  unfold finiteFramePairedC2EinsteinBRSTEuler finiteFramePairedC2EinsteinBRSTAction
  change fderiv Real
      ((fun current : Input =>
        finiteFramePairedC2EinsteinHilbertAction period hPeriod plusFrame minusFrame plusMetric
          minusMetric couplings.plusEinstein couplings.minusEinstein current.1) +
        finiteFramePairedC2FullBRSTGaugeAction period hPeriod source plusFrame minusFrame plusMetric
          minusMetric couplings) input = _
  rw [fderiv_add hEinstein hBRST,
    einstein_fst_fderiv period hPeriod source plusFrame minusFrame plusMetric minusMetric
      couplings input hInput]
  rfl

end
end P0EFTJanusFiniteFramePairedC2EinsteinBRSTEulerDecomposition4D
end JanusFormal
