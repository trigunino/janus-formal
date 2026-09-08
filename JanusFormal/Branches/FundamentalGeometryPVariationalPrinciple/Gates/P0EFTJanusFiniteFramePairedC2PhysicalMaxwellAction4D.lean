import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2MobileMaxwellAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalAction4D

/-! # Maxwell augmentation of the paired finite C² physical action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFrameC2MobileMaxwellAction4D
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
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

variable (geometry : GlobalCandidateAGeometry period hPeriod)
  (frame : SmoothD8Frame period hPeriod)
  (hRegular : ∀ point, Function.Bijective
    (intrinsicCandidateASylvesterAt period hPeriod geometry point))

local notation "Input" =>
  FiniteFramePairedC2PhysicalCore period hPeriod geometry frame
local notation "MaxwellInput" =>
  FiniteFramePairedC2MaxwellCore period hPeriod frame frame
    geometry.plusMetric geometry.plusMetric

/-- Forget all nonminimal fields while retaining both metrics and potentials. -/
def finiteFramePairedC2PhysicalMaxwellProjection : Input →L[Real] MaxwellInput :=
  let metrics := ContinuousLinearMap.fst Real
    (GeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric ×
      GeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric)
    (FiniteFramePairedC2AbelianGaugeFields period hPeriod frame frame ×
      FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame)
  let fields : Input →L[Real] FiniteFramePairedC2AbelianGaugeFields period hPeriod frame frame :=
    (ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.snd Real _ _)
  let plusMetric := (ContinuousLinearMap.fst Real _ _).comp metrics
  let minusMetric := (ContinuousLinearMap.snd Real _ _).comp metrics
  let plusFields := (ContinuousLinearMap.fst Real _ _).comp fields
  let minusFields := (ContinuousLinearMap.snd Real _ _).comp fields
  let plusPotential := (ContinuousLinearMap.fst Real _ _).comp plusFields
  let minusPotential := (ContinuousLinearMap.fst Real _ _).comp minusFields
  (plusMetric.prod plusPotential).prod (minusMetric.prod minusPotential)

@[simp] theorem finiteFramePairedC2PhysicalMaxwellProjection_apply (input : Input) :
    finiteFramePairedC2PhysicalMaxwellProjection period hPeriod geometry frame input =
      ((input.1.1, input.2.1.1.1), (input.1.2, input.2.1.2.1)) := rfl

/-- The existing physical action plus both mobile Maxwell sectors. -/
def finiteFramePairedC2PhysicalMaxwellAction
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) : Real :=
  finiteFramePairedC2PhysicalAction period hPeriod geometry frame hRegular
      couplings interactionScale coefficients input +
    finiteFramePairedC2MobileMaxwellAction period hPeriod frame frame
      geometry.plusMetric geometry.plusMetric couplings.plusMaxwellScale
      couplings.minusMaxwellScale
      (finiteFramePairedC2PhysicalMaxwellProjection period hPeriod geometry frame
        (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input))

private theorem finiteFramePairedC2PhysicalMaxwellProjection_mem
    (input : Input)
    (hInput : input ∈ finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular) :
    finiteFramePairedC2PhysicalMaxwellProjection period hPeriod geometry frame
        (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input) ∈
      finiteFramePairedC2MobileMaxwellDomain period hPeriod frame frame
        geometry.plusMetric geometry.plusMetric := by
  exact ⟨⟨hInput.1.1.1, Set.mem_univ _⟩,
    ⟨hInput.1.1.2, Set.mem_univ _⟩⟩

theorem finiteFramePairedC2PhysicalMaxwellAction_contDiffOn_two
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    ContDiffOn Real 2
      (finiteFramePairedC2PhysicalMaxwellAction period hPeriod geometry frame hRegular
        couplings interactionScale coefficients)
      (finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular) := by
  have hProjection : ContDiff Real ∞
      (fun input : Input =>
        finiteFramePairedC2PhysicalMaxwellProjection period hPeriod geometry frame
          (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input)) :=
    (finiteFramePairedC2PhysicalMaxwellProjection period hPeriod geometry frame).contDiff.comp
      (finiteFramePairedC2PhysicalRecenter_contDiff period hPeriod geometry frame)
  have hMaxwell :=
    (finiteFramePairedC2MobileMaxwellAction_contDiffOn_two period hPeriod frame frame
      geometry.plusMetric geometry.plusMetric couplings.plusMaxwellScale
      couplings.minusMaxwellScale).comp
        (hProjection.contDiffOn.of_le (show (2 : ℕ∞ω) ≤ ∞ from
          WithTop.coe_le_coe.mpr le_top))
        (fun input hInput =>
          finiteFramePairedC2PhysicalMaxwellProjection_mem period hPeriod geometry frame
            hRegular input hInput)
  exact (finiteFramePairedC2PhysicalAction_contDiffOn_two period hPeriod geometry frame
    hRegular couplings interactionScale coefficients).add hMaxwell

def finiteFramePairedC2PhysicalMaxwellEuler
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) : Input →L[Real] Real :=
  fderiv Real
    (finiteFramePairedC2PhysicalMaxwellAction period hPeriod geometry frame hRegular
      couplings interactionScale coefficients) input

theorem finiteFramePairedC2PhysicalMaxwellAction_hasFDerivAt
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input)
    (hInput : input ∈ finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular) :
    HasFDerivAt
      (finiteFramePairedC2PhysicalMaxwellAction period hPeriod geometry frame hRegular
        couplings interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellEuler period hPeriod geometry frame hRegular
        couplings interactionScale coefficients input) input :=
  (((finiteFramePairedC2PhysicalMaxwellAction_contDiffOn_two period hPeriod geometry frame
    hRegular couplings interactionScale coefficients input hInput).contDiffAt
      ((finiteFramePairedC2PhysicalDomain_isOpen period hPeriod geometry frame hRegular).mem_nhds
        hInput)).differentiableAt (by norm_num)).hasFDerivAt

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
end JanusFormal
