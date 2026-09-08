import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2EinsteinHilbertEulerSectors4D

/-! # Expanded Euler map of the paired physical C² action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalEulerExpanded4D

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
open P0EFTJanusFiniteFramePairedRelativeC2Root4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerChainRule4D
open P0EFTJanusFiniteFramePairedC2EinsteinBRSTEulerDecomposition4D
open P0EFTJanusFiniteFramePairedC2EinsteinHilbertEulerSectors4D
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

/-- Full component expansion of the actual physical Euler map. -/
theorem finiteFramePairedC2PhysicalEuler_eq_expanded_components
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) (hInput : input ∈ Domain) :
    finiteFramePairedC2PhysicalEuler period hPeriod geometry frame hRegular couplings interactionScale
        coefficients input =
      ((finiteFrameC2EinsteinHilbertEuler period hPeriod frame geometry.plusMetric
          couplings.plusEinstein
          (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input).1.1).comp
            (ContinuousLinearMap.fst Real _ _) +
        (finiteFrameC2EinsteinHilbertEuler period hPeriod frame geometry.plusMetric
          couplings.minusEinstein
          (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input).1.2).comp
            (ContinuousLinearMap.snd Real _ _)).comp
          (ContinuousLinearMap.fst Real MetricPair _) +
        finiteFramePairedC2FullBRSTGaugeEuler period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric couplings
          (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input) +
      (pairedFiniteFrameC2InteractionEuler period hPeriod geometry frame hRegular interactionScale
        coefficients input.1).comp (ContinuousLinearMap.fst Real MetricPair _) := by
  rw [finiteFramePairedC2PhysicalEuler_eq_component_eulers period hPeriod geometry frame hRegular
    couplings interactionScale coefficients input hInput,
    finiteFramePairedC2EinsteinBRSTEuler_eq_component_eulers period hPeriod frame frame frame
      geometry.plusMetric geometry.plusMetric couplings
      (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input) hInput.1,
    finiteFramePairedC2EinsteinHilbertEuler_eq_sector_eulers period hPeriod frame frame
      geometry.plusMetric geometry.plusMetric couplings.plusEinstein couplings.minusEinstein
      (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input).1 hInput.1.1]

end
end P0EFTJanusFiniteFramePairedC2PhysicalEulerExpanded4D
end JanusFormal
