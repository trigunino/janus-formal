import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalEulerSlotRestrictions4D

/-! # Abelian and diffeomorphism gauge slots of the paired physical Euler map -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalEulerGaugeSlots4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
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
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFramePairedRelativeC2Root4D
open P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTEulerDecomposition4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerSlotRestrictions4D
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
local notation "AbelianFields" => FiniteFramePairedC2AbelianGaugeFields period hPeriod frame frame
local notation "DiffeomorphismFields" =>
  FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame
local notation "Domain" => finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular

/-- Pure Abelian-field variations see exactly the Abelian BRST Euler map. -/
theorem finiteFramePairedC2PhysicalEuler_abelian_fields_apply
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) (hInput : input ∈ Domain) (variation : AbelianFields) :
    finiteFramePairedC2PhysicalEuler period hPeriod geometry frame hRegular couplings interactionScale
        coefficients input (0, (variation, 0)) =
      finiteFramePairedC2AbelianBRSTEuler period hPeriod frame frame geometry.plusMetric
        geometry.plusMetric
        (finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric
          (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input))
        (finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric ((0 : MetricPair), (variation, 0))) := by
  rw [finiteFramePairedC2PhysicalEuler_fields_apply period hPeriod geometry frame hRegular couplings
    interactionScale coefficients input hInput (variation, 0),
    finiteFramePairedC2FullBRSTGaugeEuler_eq_component_eulers period hPeriod frame frame frame
      geometry.plusMetric geometry.plusMetric couplings
      (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input) hInput.1]
  simp
  exact map_zero _

/-- Pure diffeomorphism-field variations see exactly the diagonal diffeomorphism BRST Euler map. -/
theorem finiteFramePairedC2PhysicalEuler_diffeomorphism_fields_apply
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) (hInput : input ∈ Domain) (variation : DiffeomorphismFields) :
    finiteFramePairedC2PhysicalEuler period hPeriod geometry frame hRegular couplings interactionScale
        coefficients input (0, (0, variation)) =
      finiteFramePairedDiffeomorphismBRSTEuler period hPeriod frame frame frame
        geometry.plusMetric geometry.plusMetric couplings
        (finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric
          (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input))
        (finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric ((0 : MetricPair), (0, variation))) := by
  rw [finiteFramePairedC2PhysicalEuler_fields_apply period hPeriod geometry frame hRegular couplings
    interactionScale coefficients input hInput (0, variation),
    finiteFramePairedC2FullBRSTGaugeEuler_eq_component_eulers period hPeriod frame frame frame
      geometry.plusMetric geometry.plusMetric couplings
      (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input) hInput.1]
  simp
  exact map_zero _

end
end P0EFTJanusFiniteFramePairedC2PhysicalEulerGaugeSlots4D
end JanusFormal
