import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

/-! # Paired diffeomorphism BRST action in finite generating families

Each gauge tensor is the same variable as its metric perturbation. One total
B/antighost/ghost packet is transported from a common finite family into both
sectors. The action retains the actual Einstein weights and mobile volumes.
This is a paired metric/BRST model, not a complete action datum or global atlas.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D

set_option autoImplicit false

noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D

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

/-- A bounded diagonal insertion: the tensor slot is exactly the metric variation. -/
def finiteFrameSharedMetricDiffeomorphismBRSTInput
    (source target : SmoothD8Frame period hPeriod)
    (targetReference : SmoothGeneralLorentzMetric period hPeriod) :
    (GeneralMetricRelativeC2Core period hPeriod target targetReference ×
      FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod source) →L[Real]
        FiniteFrameC2DiffeomorphismBRSTCore period hPeriod target targetReference :=
  let metric := ContinuousLinearMap.fst Real
    (GeneralMetricRelativeC2Core period hPeriod target targetReference)
    (FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod source)
  let fields := (finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod source target targetReference).comp
    (ContinuousLinearMap.snd Real
      (GeneralMetricRelativeC2Core period hPeriod target targetReference)
      (FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod source))
  metric.prod (metric.prod fields)

@[simp] theorem finiteFrameSharedMetricDiffeomorphismBRSTInput_apply
    (source target : SmoothD8Frame period hPeriod)
    (targetReference : SmoothGeneralLorentzMetric period hPeriod)
    (input : GeneralMetricRelativeC2Core period hPeriod target targetReference ×
      FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod source) :
    finiteFrameSharedMetricDiffeomorphismBRSTInput period hPeriod source target targetReference input =
      (input.1, (input.1,
        finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod source target targetReference input.2)) := rfl

theorem finiteFrameSharedMetricDiffeomorphismBRSTInput_smooth
    (source target : SmoothD8Frame period hPeriod)
    (sourceReference targetReference : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (fields : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    finiteFrameSharedMetricDiffeomorphismBRSTInput period hPeriod source target targetReference
        (smoothToGeneralMetricRelativeC2Core period hPeriod target targetReference tensor,
          finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod source sourceReference fields) =
      finiteFrameSmoothDiffeomorphismBRSTCore period hPeriod target targetReference tensor
        { metricPerturbation := tensor, nonminimal := fields } := by
  rw [finiteFrameSharedMetricDiffeomorphismBRSTInput_apply,
    finiteFrameDiffeomorphismNonminimalC2Transition_smooth]
  rfl

/-- Exactly two metric variables and one shared nonminimal source packet. -/
abbrev FiniteFramePairedDiffeomorphismBRSTCore
    (source plusFrame minusFrame : SmoothD8Frame period hPeriod)
    (plusReference minusReference : SmoothGeneralLorentzMetric period hPeriod) :=
  (GeneralMetricRelativeC2Core period hPeriod plusFrame plusReference ×
    GeneralMetricRelativeC2Core period hPeriod minusFrame minusReference) ×
      FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod source

variable (source plusFrame minusFrame : SmoothD8Frame period hPeriod)
  (plusReference minusReference : SmoothGeneralLorentzMetric period hPeriod)
local notation "Input" => FiniteFramePairedDiffeomorphismBRSTCore period hPeriod
  source plusFrame minusFrame plusReference minusReference

def finiteFramePairedDiffeomorphismBRSTDomain : Set Input :=
  Set.prod
    (Set.prod (generalMetricRelativeC2VolumeDomain period hPeriod plusFrame plusReference)
      (generalMetricRelativeC2VolumeDomain period hPeriod minusFrame minusReference)) Set.univ

theorem finiteFramePairedDiffeomorphismBRSTDomain_isOpen :
    IsOpen (finiteFramePairedDiffeomorphismBRSTDomain period hPeriod source plusFrame minusFrame
      plusReference minusReference) :=
  ((generalMetricRelativeC2VolumeDomain_isOpen period hPeriod plusFrame plusReference).prod
    (generalMetricRelativeC2VolumeDomain_isOpen period hPeriod minusFrame minusReference)).prod isOpen_univ

def finiteFramePairedDiffeomorphismBRSTPlusInput :
    Input →L[Real] FiniteFrameC2DiffeomorphismBRSTCore period hPeriod plusFrame plusReference :=
  (finiteFrameSharedMetricDiffeomorphismBRSTInput period hPeriod source plusFrame plusReference).comp
    (((ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.fst Real _ _)).prod
      (ContinuousLinearMap.snd Real _ _))

def finiteFramePairedDiffeomorphismBRSTMinusInput :
    Input →L[Real] FiniteFrameC2DiffeomorphismBRSTCore period hPeriod minusFrame minusReference :=
  (finiteFrameSharedMetricDiffeomorphismBRSTInput period hPeriod source minusFrame minusReference).comp
    (((ContinuousLinearMap.snd Real _ _).comp (ContinuousLinearMap.fst Real _ _)).prod
      (ContinuousLinearMap.snd Real _ _))

@[simp] theorem finiteFramePairedDiffeomorphismBRSTPlusInput_apply (input : Input) :
    finiteFramePairedDiffeomorphismBRSTPlusInput period hPeriod source plusFrame minusFrame
        plusReference minusReference input =
      finiteFrameSharedMetricDiffeomorphismBRSTInput period hPeriod source plusFrame plusReference
        (input.1.1, input.2) := rfl

@[simp] theorem finiteFramePairedDiffeomorphismBRSTMinusInput_apply (input : Input) :
    finiteFramePairedDiffeomorphismBRSTMinusInput period hPeriod source plusFrame minusFrame
        plusReference minusReference input =
      finiteFrameSharedMetricDiffeomorphismBRSTInput period hPeriod source minusFrame minusReference
        (input.1.2, input.2) := rfl

def finiteFramePairedDiffeomorphismBRSTAction (couplings : GlobalCandidateAActionCouplings)
    (input : Input) : Real :=
  candidateAPlusEinsteinKineticWeight couplings *
      finiteFrameC2DiffeomorphismBRSTAction period hPeriod plusFrame plusReference
        (finiteFramePairedDiffeomorphismBRSTPlusInput period hPeriod source plusFrame minusFrame
          plusReference minusReference input) +
    candidateAMinusEinsteinKineticWeight couplings *
      finiteFrameC2DiffeomorphismBRSTAction period hPeriod minusFrame minusReference
        (finiteFramePairedDiffeomorphismBRSTMinusInput period hPeriod source plusFrame minusFrame
          plusReference minusReference input)

theorem finiteFramePairedDiffeomorphismBRSTAction_contDiffOn_two
    (couplings : GlobalCandidateAActionCouplings) :
    ContDiffOn Real 2 (finiteFramePairedDiffeomorphismBRSTAction period hPeriod source plusFrame minusFrame
      plusReference minusReference couplings)
      (finiteFramePairedDiffeomorphismBRSTDomain period hPeriod source plusFrame minusFrame
        plusReference minusReference) := by
  have hPlusInput : ContDiffOn Real 2
      (finiteFramePairedDiffeomorphismBRSTPlusInput period hPeriod source plusFrame minusFrame
        plusReference minusReference)
      (finiteFramePairedDiffeomorphismBRSTDomain period hPeriod source plusFrame minusFrame
        plusReference minusReference) :=
    ((finiteFramePairedDiffeomorphismBRSTPlusInput period hPeriod source plusFrame minusFrame
      plusReference minusReference).contDiff.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hMinusInput : ContDiffOn Real 2
      (finiteFramePairedDiffeomorphismBRSTMinusInput period hPeriod source plusFrame minusFrame
        plusReference minusReference)
      (finiteFramePairedDiffeomorphismBRSTDomain period hPeriod source plusFrame minusFrame
        plusReference minusReference) :=
    ((finiteFramePairedDiffeomorphismBRSTMinusInput period hPeriod source plusFrame minusFrame
      plusReference minusReference).contDiff.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hPlus := (finiteFrameC2DiffeomorphismBRSTAction_contDiffOn_two period hPeriod plusFrame plusReference).comp
    hPlusInput (fun _ h => ⟨h.1.1, Set.mem_univ _⟩)
  have hMinus := (finiteFrameC2DiffeomorphismBRSTAction_contDiffOn_two period hPeriod minusFrame minusReference).comp
    hMinusInput (fun _ h => ⟨h.1.2, Set.mem_univ _⟩)
  have h := ((contDiffOn_const (c := candidateAPlusEinsteinKineticWeight couplings)).mul hPlus).add
    ((contDiffOn_const (c := candidateAMinusEinsteinKineticWeight couplings)).mul hMinus)
  simp only [Function.comp_def] at h
  exact h

/-- The derivative belongs to the concrete weighted action of both sectors. -/
def finiteFramePairedDiffeomorphismBRSTEuler (couplings : GlobalCandidateAActionCouplings)
    (input : Input) : Input →L[Real] Real :=
  fderiv Real (finiteFramePairedDiffeomorphismBRSTAction period hPeriod source plusFrame minusFrame
    plusReference minusReference couplings) input

theorem finiteFramePairedDiffeomorphismBRSTAction_hasFDerivAt
    (couplings : GlobalCandidateAActionCouplings) (input : Input)
    (hInput : input ∈ finiteFramePairedDiffeomorphismBRSTDomain period hPeriod source plusFrame minusFrame
      plusReference minusReference) :
    HasFDerivAt
      (finiteFramePairedDiffeomorphismBRSTAction period hPeriod source plusFrame minusFrame
        plusReference minusReference couplings)
      (finiteFramePairedDiffeomorphismBRSTEuler period hPeriod source plusFrame minusFrame
        plusReference minusReference couplings input) input :=
  (((finiteFramePairedDiffeomorphismBRSTAction_contDiffOn_two period hPeriod source plusFrame minusFrame
    plusReference minusReference couplings input hInput).contDiffAt
      ((finiteFramePairedDiffeomorphismBRSTDomain_isOpen period hPeriod source plusFrame minusFrame
        plusReference minusReference).mem_nhds hInput)).differentiableAt (by norm_num)).hasFDerivAt

def finiteFrameSmoothPairedDiffeomorphismBRSTCore
    (sourceReference : SmoothGeneralLorentzMetric period hPeriod)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (fields : GlobalDiffeomorphismNonminimalFields period hPeriod) : Input :=
  ((smoothToGeneralMetricRelativeC2Core period hPeriod plusFrame plusReference plusTensor,
    smoothToGeneralMetricRelativeC2Core period hPeriod minusFrame minusReference minusTensor),
    finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod source sourceReference fields)

theorem finiteFrameSmoothPairedDiffeomorphismBRSTCore_mem
    (sourceReference : SmoothGeneralLorentzMetric period hPeriod)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (fields : GlobalDiffeomorphismNonminimalFields period hPeriod)
    (hPlusVolume : smoothToGeneralMetricRelativeC2Core period hPeriod plusFrame plusReference plusTensor ∈
      generalMetricRelativeC2VolumeDomain period hPeriod plusFrame plusReference)
    (hMinusVolume : smoothToGeneralMetricRelativeC2Core period hPeriod minusFrame minusReference minusTensor ∈
      generalMetricRelativeC2VolumeDomain period hPeriod minusFrame minusReference) :
    finiteFrameSmoothPairedDiffeomorphismBRSTCore period hPeriod source plusFrame minusFrame
        plusReference minusReference sourceReference plusTensor minusTensor fields ∈
      finiteFramePairedDiffeomorphismBRSTDomain period hPeriod source plusFrame minusFrame
        plusReference minusReference :=
  ⟨⟨hPlusVolume, hMinusVolume⟩, Set.mem_univ _⟩

/-- The exact diagonal smooth action, with H equal to each metric variation and one shared triple. -/
theorem finiteFramePairedDiffeomorphismBRSTAction_smooth_eq_BRST
    (sourceReference : SmoothGeneralLorentzMetric period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (hPlusMetric : (metric .plus).tensor = plusReference.tensor + plusTensor)
    (hMinusMetric : (metric .minus).tensor = minusReference.tensor + minusTensor)
    (hPlusVolume : smoothToGeneralMetricRelativeC2Core period hPeriod plusFrame plusReference plusTensor ∈
      generalMetricRelativeC2VolumeDomain period hPeriod plusFrame plusReference)
    (hMinusVolume : smoothToGeneralMetricRelativeC2Core period hPeriod minusFrame minusReference minusTensor ∈
      generalMetricRelativeC2VolumeDomain period hPeriod minusFrame minusReference)
    (fields : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    finiteFramePairedDiffeomorphismBRSTAction period hPeriod source plusFrame minusFrame
        plusReference minusReference couplings
        (finiteFrameSmoothPairedDiffeomorphismBRSTCore period hPeriod source plusFrame minusFrame
          plusReference minusReference sourceReference plusTensor minusTensor fields) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation period hPeriod couplings metric
        { metricPerturbation := fun | .plus => plusTensor | .minus => minusTensor
          nonminimal := fields } := by
  simp only [finiteFramePairedDiffeomorphismBRSTAction,
    finiteFramePairedDiffeomorphismBRSTPlusInput_apply, finiteFramePairedDiffeomorphismBRSTMinusInput_apply,
    finiteFrameSmoothPairedDiffeomorphismBRSTCore, finiteFrameSharedMetricDiffeomorphismBRSTInput_smooth]
  rw [finiteFrameC2DiffeomorphismBRSTAction_smooth period hPeriod plusFrame plusReference
      plusTensor (metric .plus) hPlusMetric hPlusVolume,
    finiteFrameC2DiffeomorphismBRSTAction_smooth period hPeriod minusFrame minusReference
      minusTensor (metric .minus) hMinusMetric hMinusVolume]
  all_goals rfl

end
end P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
end JanusFormal
