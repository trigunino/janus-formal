import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2InteractionAction4D

/-! # Recentered paired Einstein-BRST-interaction action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalAction4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D
open P0EFTJanusFiniteFramePairedC2InteractionAction4D
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

abbrev FiniteFramePairedC2PhysicalCore :=
  FiniteFramePairedC2FullBRSTGaugeCore period hPeriod frame frame frame
    geometry.plusMetric geometry.plusMetric

local notation "Input" => FiniteFramePairedC2PhysicalCore period hPeriod geometry frame

/-- The fixed minus metric, encoded as a variation relative to the plus metric. -/
def finiteFramePairedC2MinusCenter :
    GeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric :=
  smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric
    (geometry.minusMetric.tensor - geometry.plusMetric.tensor)

/-- Affine recentering of the second metric while preserving every gauge field. -/
def finiteFramePairedC2PhysicalRecenter (input : Input) : Input :=
  ((input.1.1, finiteFramePairedC2MinusCenter period hPeriod geometry frame + input.1.2), input.2)

theorem finiteFramePairedC2PhysicalRecenter_contDiff :
    ContDiff Real ∞ (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame) := by
  unfold finiteFramePairedC2PhysicalRecenter
  fun_prop

@[simp] theorem finiteFramePairedC2PhysicalRecenter_zero :
    finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame 0 =
      ((0, finiteFramePairedC2MinusCenter period hPeriod geometry frame), 0) := by
  simp [finiteFramePairedC2PhysicalRecenter]

theorem finiteFramePairedC2PhysicalRecenter_smooth
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (fields : (FiniteFramePairedC2AbelianGaugeFields period hPeriod frame frame ×
      FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame)) :
    finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame
        ((smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric plusVariation,
          smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric minusVariation), fields) =
      ((smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric plusVariation,
        smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric
          ((geometry.minusMetric.tensor - geometry.plusMetric.tensor) + minusVariation)), fields) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · change finiteFramePairedC2MinusCenter period hPeriod geometry frame +
          smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric minusVariation = _
      exact ((smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric).map_add
        (geometry.minusMetric.tensor - geometry.plusMetric.tensor) minusVariation).symm
  · rfl

def finiteFramePairedC2PhysicalDomain : Set Input :=
  finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame ⁻¹'
      finiteFramePairedC2FullBRSTGaugeDomain period hPeriod frame frame frame
        geometry.plusMetric geometry.plusMetric ∩
    Prod.fst ⁻¹' pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular

theorem finiteFramePairedC2PhysicalDomain_isOpen :
    IsOpen (finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular) :=
  (finiteFramePairedC2FullBRSTGaugeDomain_isOpen period hPeriod frame frame frame
      geometry.plusMetric geometry.plusMetric).preimage
      (finiteFramePairedC2PhysicalRecenter_contDiff period hPeriod geometry frame).continuous
    |>.inter ((pairedFiniteFrameC2InteractionDomain_isOpen period hPeriod geometry frame hRegular).preimage
      continuous_fst)

theorem zero_mem_finiteFramePairedC2PhysicalDomain
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric) :
    (0 : Input) ∈ finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular := by
  refine ⟨?_, zero_mem_pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular⟩
  change finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame 0 ∈
    finiteFramePairedC2FullBRSTGaugeDomain period hPeriod frame frame frame
      geometry.plusMetric geometry.plusMetric
  rw [finiteFramePairedC2PhysicalRecenter_zero]
  exact ⟨⟨zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric,
    hMinusCenter⟩, Set.mem_univ _⟩

def finiteFramePairedC2PhysicalAction (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) (input : Input) : Real :=
  finiteFramePairedC2EinsteinBRSTAction period hPeriod frame frame frame
      geometry.plusMetric geometry.plusMetric couplings
      (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input) +
    pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular
      interactionScale coefficients input.1

theorem finiteFramePairedC2PhysicalAction_contDiffOn_two
    (couplings : GlobalCandidateAActionCouplings) (interactionScale : Real)
    (coefficients : PotentialCoefficients) :
    ContDiffOn Real 2
      (finiteFramePairedC2PhysicalAction period hPeriod geometry frame hRegular
        couplings interactionScale coefficients)
      (finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular) := by
  have hRecenter : ContDiffOn Real ∞
      (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame)
      (finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular) :=
    (finiteFramePairedC2PhysicalRecenter_contDiff period hPeriod geometry frame).contDiffOn
  have hRecenterTwo : ContDiffOn Real 2
      (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame)
      (finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular) :=
    hRecenter.of_le (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
      exact WithTop.coe_le_coe.mpr le_top)
  have hGravity := (finiteFramePairedC2EinsteinBRSTAction_contDiffOn_two period hPeriod
    frame frame frame geometry.plusMetric geometry.plusMetric couplings).comp
      hRecenterTwo (fun _ hInput => hInput.1)
  have hMetrics : ContDiffOn Real 2 (fun input : Input => input.1)
      (finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular) :=
    contDiff_fst.contDiffOn
  have hInteraction := (pairedFiniteFrameC2InteractionAction_contDiffOn period hPeriod geometry
    frame hRegular interactionScale coefficients).comp hMetrics (fun _ hInput => hInput.2)
  exact hGravity.add hInteraction

def finiteFramePairedC2PhysicalEuler (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) (input : Input) :
    Input →L[Real] Real :=
  fderiv Real (finiteFramePairedC2PhysicalAction period hPeriod geometry frame hRegular
    couplings interactionScale coefficients) input

theorem finiteFramePairedC2PhysicalAction_hasFDerivAt
    (couplings : GlobalCandidateAActionCouplings) (interactionScale : Real)
    (coefficients : PotentialCoefficients) (input : Input)
    (hInput : input ∈ finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular) :
    HasFDerivAt
      (finiteFramePairedC2PhysicalAction period hPeriod geometry frame hRegular
        couplings interactionScale coefficients)
      (finiteFramePairedC2PhysicalEuler period hPeriod geometry frame hRegular
        couplings interactionScale coefficients input) input :=
  (((finiteFramePairedC2PhysicalAction_contDiffOn_two period hPeriod geometry frame hRegular
    couplings interactionScale coefficients input hInput).contDiffAt
      ((finiteFramePairedC2PhysicalDomain_isOpen period hPeriod geometry frame hRegular).mem_nhds
        hInput)).differentiableAt (by norm_num)).hasFDerivAt

end
end P0EFTJanusFiniteFramePairedC2PhysicalAction4D
end JanusFormal
