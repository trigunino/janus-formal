import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D

/-! # Paired Einstein-Hilbert plus full BRST gauge action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D

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
local notation "Domain" => finiteFramePairedC2FullBRSTGaugeDomain period hPeriod
  source plusFrame minusFrame plusMetric minusMetric

def finiteFramePairedC2EinsteinBRSTAction (couplings : GlobalCandidateAActionCouplings)
    (input : Input) : Real :=
  finiteFramePairedC2EinsteinHilbertAction period hPeriod plusFrame minusFrame plusMetric minusMetric
      couplings.plusEinstein couplings.minusEinstein input.1 +
    finiteFramePairedC2FullBRSTGaugeAction period hPeriod source plusFrame minusFrame
      plusMetric minusMetric couplings input

theorem finiteFramePairedC2EinsteinBRSTAction_contDiffOn_two
    (couplings : GlobalCandidateAActionCouplings) :
    ContDiffOn Real 2
      (finiteFramePairedC2EinsteinBRSTAction period hPeriod source plusFrame minusFrame
        plusMetric minusMetric couplings) Domain := by
  have hEinstein : ContDiffOn Real 2
      (fun input : Input => finiteFramePairedC2EinsteinHilbertAction period hPeriod
        plusFrame minusFrame plusMetric minusMetric couplings.plusEinstein couplings.minusEinstein input.1)
      Domain :=
    (finiteFramePairedC2EinsteinHilbertAction_contDiffOn_two period hPeriod plusFrame minusFrame
      plusMetric minusMetric couplings.plusEinstein couplings.minusEinstein).comp
        contDiff_fst.contDiffOn (fun _ hInput => hInput.1)
  exact hEinstein.add
    (finiteFramePairedC2FullBRSTGaugeAction_contDiffOn_two period hPeriod source plusFrame minusFrame
      plusMetric minusMetric couplings)

def finiteFramePairedC2EinsteinBRSTEuler (couplings : GlobalCandidateAActionCouplings)
    (input : Input) : Input →L[Real] Real :=
  fderiv Real (finiteFramePairedC2EinsteinBRSTAction period hPeriod source plusFrame minusFrame
    plusMetric minusMetric couplings) input

theorem finiteFramePairedC2EinsteinBRSTAction_hasFDerivAt
    (couplings : GlobalCandidateAActionCouplings) (input : Input) (hInput : input ∈ Domain) :
    HasFDerivAt
      (finiteFramePairedC2EinsteinBRSTAction period hPeriod source plusFrame minusFrame
        plusMetric minusMetric couplings)
      (finiteFramePairedC2EinsteinBRSTEuler period hPeriod source plusFrame minusFrame
        plusMetric minusMetric couplings input) input :=
  (((finiteFramePairedC2EinsteinBRSTAction_contDiffOn_two period hPeriod source plusFrame minusFrame
    plusMetric minusMetric couplings input hInput).contDiffAt
      ((finiteFramePairedC2FullBRSTGaugeDomain_isOpen period hPeriod source plusFrame minusFrame
        plusMetric minusMetric).mem_nhds hInput)).differentiableAt (by norm_num)).hasFDerivAt

end
end P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D
end JanusFormal
