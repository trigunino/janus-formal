import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalEulerDecomposition4D

/-! # Chain rule for the paired physical C² Euler map -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalEulerChainRule4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
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
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusFiniteFramePairedRelativeC2Root4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D
open P0EFTJanusFiniteFramePairedC2InteractionAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerDecomposition4D
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
local notation "Input" => FiniteFramePairedC2PhysicalCore period hPeriod geometry frame
local notation "MetricPair" => PairedFiniteFrameMetricC2Core period hPeriod geometry frame
local notation "Domain" => finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular

/-- Euler map of the C² interaction block. -/
def pairedFiniteFrameC2InteractionEuler
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metric : MetricPair) : MetricPair →L[Real] Real :=
  fderiv Real (pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular
    interactionScale coefficients) metric

/-- Recentring is an affine translation and therefore has identity derivative. -/
theorem finiteFramePairedC2PhysicalRecenter_hasFDerivAt (input : Input) :
    HasFDerivAt (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame)
      (ContinuousLinearMap.id Real Input) input := by
  let offset : Input := ((0, finiteFramePairedC2MinusCenter period hPeriod geometry frame), 0)
  have hAffine : finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame =
      fun current : Input => offset + current := by
    funext current
    apply Prod.ext
    · apply Prod.ext <;> simp [finiteFramePairedC2PhysicalRecenter, offset]
    · simp [finiteFramePairedC2PhysicalRecenter, offset]
  rw [hAffine]
  exact (hasFDerivAt_const_add_iff offset).2 (ContinuousLinearMap.id Real Input).hasFDerivAt

private theorem gravity_recenter_fderiv
    (couplings : GlobalCandidateAActionCouplings) (input : Input) (hInput : input ∈ Domain) :
    fderiv Real
        (fun current : Input =>
          finiteFramePairedC2EinsteinBRSTAction period hPeriod frame frame frame
            geometry.plusMetric geometry.plusMetric couplings
            (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame current)) input =
      finiteFramePairedC2EinsteinBRSTEuler period hPeriod frame frame frame
        geometry.plusMetric geometry.plusMetric couplings
        (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input) := by
  have hAction : DifferentiableAt Real
      (finiteFramePairedC2EinsteinBRSTAction period hPeriod frame frame frame
        geometry.plusMetric geometry.plusMetric couplings)
      (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input) :=
    (((finiteFramePairedC2EinsteinBRSTAction_contDiffOn_two period hPeriod frame frame frame
      geometry.plusMetric geometry.plusMetric couplings) _ hInput.1).contDiffAt
        ((finiteFramePairedC2FullBRSTGaugeDomain_isOpen period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric).mem_nhds hInput.1)).differentiableAt (by norm_num)
  have hChain := hAction.hasFDerivAt.comp input
    (finiteFramePairedC2PhysicalRecenter_hasFDerivAt period hPeriod geometry frame input)
  unfold finiteFramePairedC2EinsteinBRSTEuler
  simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using hChain.fderiv

private theorem interaction_fst_fderiv
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) (hInput : input ∈ Domain) :
    fderiv Real
        (fun current : Input =>
          pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular interactionScale
            coefficients current.1) input =
      (pairedFiniteFrameC2InteractionEuler period hPeriod geometry frame hRegular interactionScale
        coefficients input.1).comp (ContinuousLinearMap.fst Real MetricPair _) := by
  have hAction : DifferentiableAt Real
      (pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular interactionScale
        coefficients) input.1 :=
    (((pairedFiniteFrameC2InteractionAction_contDiffOn period hPeriod geometry frame hRegular
      interactionScale coefficients) input.1 hInput.2).contDiffAt
        ((pairedFiniteFrameC2InteractionDomain_isOpen period hPeriod geometry frame hRegular).mem_nhds
          hInput.2)).differentiableAt (by norm_num)
  have hFst : HasFDerivAt (fun current : Input => current.1)
      (ContinuousLinearMap.fst Real MetricPair _) input := by
    fun_prop
  have hChain := hAction.hasFDerivAt.comp input hFst
  unfold pairedFiniteFrameC2InteractionEuler
  exact hChain.fderiv

/-- The physical Euler map is the recentered Einstein-BRST Euler plus the projected interaction Euler. -/
theorem finiteFramePairedC2PhysicalEuler_eq_component_eulers
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) (hInput : input ∈ Domain) :
    finiteFramePairedC2PhysicalEuler period hPeriod geometry frame hRegular couplings interactionScale
        coefficients input =
      finiteFramePairedC2EinsteinBRSTEuler period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric couplings
          (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input) +
        (pairedFiniteFrameC2InteractionEuler period hPeriod geometry frame hRegular interactionScale
          coefficients input.1).comp (ContinuousLinearMap.fst Real MetricPair _) := by
  rw [finiteFramePairedC2PhysicalEuler_eq_component_fderivs period hPeriod geometry frame hRegular
    couplings interactionScale coefficients input hInput,
    gravity_recenter_fderiv period hPeriod geometry frame hRegular couplings input hInput,
    interaction_fst_fderiv period hPeriod geometry frame hRegular interactionScale coefficients input hInput]

end
end P0EFTJanusFiniteFramePairedC2PhysicalEulerChainRule4D
end JanusFormal
