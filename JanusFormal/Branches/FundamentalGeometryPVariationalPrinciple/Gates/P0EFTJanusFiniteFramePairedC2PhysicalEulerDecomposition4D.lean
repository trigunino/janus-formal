import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2ProjectedPhysicalCenterAgreement4D

/-! # Actual Euler decomposition of the paired physical C² action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalEulerDecomposition4D

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
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D
open P0EFTJanusFiniteFramePairedC2InteractionAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
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
local notation "Domain" => finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular

/-- The actual physical Euler map is the sum of the gravity-BRST and interaction derivatives. -/
theorem finiteFramePairedC2PhysicalEuler_eq_component_fderivs
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) (hInput : input ∈ Domain) :
    finiteFramePairedC2PhysicalEuler period hPeriod geometry frame hRegular couplings interactionScale
        coefficients input =
      fderiv Real
          (fun current : Input =>
            finiteFramePairedC2EinsteinBRSTAction period hPeriod frame frame frame
              geometry.plusMetric geometry.plusMetric couplings
              (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame current)) input +
        fderiv Real
          (fun current : Input =>
            pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular interactionScale
              coefficients current.1) input := by
  have hRecenter : ContDiffOn Real 2
      (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame) Domain :=
    (finiteFramePairedC2PhysicalRecenter_contDiff period hPeriod geometry frame).of_le
      (WithTop.coe_le_coe.mpr le_top) |>.contDiffOn
  have hGravityOn : ContDiffOn Real 2
      (fun current : Input =>
        finiteFramePairedC2EinsteinBRSTAction period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric couplings
          (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame current)) Domain :=
    (finiteFramePairedC2EinsteinBRSTAction_contDiffOn_two period hPeriod frame frame frame
      geometry.plusMetric geometry.plusMetric couplings).comp hRecenter (fun _ h => h.1)
  have hInteractionOn : ContDiffOn Real 2
      (fun current : Input =>
        pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular interactionScale
          coefficients current.1) Domain :=
    (pairedFiniteFrameC2InteractionAction_contDiffOn period hPeriod geometry frame hRegular
      interactionScale coefficients).comp contDiff_fst.contDiffOn (fun _ h => h.2)
  have hNeighborhood :=
    (finiteFramePairedC2PhysicalDomain_isOpen period hPeriod geometry frame hRegular).mem_nhds hInput
  have hGravity : DifferentiableAt Real
      (fun current : Input =>
        finiteFramePairedC2EinsteinBRSTAction period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric couplings
          (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame current)) input :=
    ((hGravityOn input hInput).contDiffAt hNeighborhood).differentiableAt (by norm_num)
  have hInteraction : DifferentiableAt Real
      (fun current : Input =>
        pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular interactionScale
          coefficients current.1) input :=
    ((hInteractionOn input hInput).contDiffAt hNeighborhood).differentiableAt (by norm_num)
  unfold finiteFramePairedC2PhysicalEuler finiteFramePairedC2PhysicalAction
  exact fderiv_add hGravity hInteraction

end
end P0EFTJanusFiniteFramePairedC2PhysicalEulerDecomposition4D
end JanusFormal
