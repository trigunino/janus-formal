import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalEulerStationaritySplit4D

/-! # Component equations of the paired physical C² Euler map -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalEulerEquations4D

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
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerChainRule4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerStationaritySplit4D
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
local notation "Fields" =>
  FiniteFramePairedC2AbelianGaugeFields period hPeriod frame frame ×
    FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame
local notation "Domain" => finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular

/-- Vanishing of the actual Euler map is exactly the metric and gauge weak system. -/
theorem finiteFramePairedC2PhysicalEuler_eq_zero_iff_component_equations
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) (hInput : input ∈ Domain) :
    finiteFramePairedC2PhysicalEuler period hPeriod geometry frame hRegular couplings interactionScale
        coefficients input = 0 ↔
      (∀ variation : MetricPair,
        (finiteFrameC2EinsteinHilbertEuler period hPeriod frame geometry.plusMetric
            couplings.plusEinstein
            (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input).1.1 variation.1 +
          finiteFrameC2EinsteinHilbertEuler period hPeriod frame geometry.plusMetric
            couplings.minusEinstein
            (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input).1.2 variation.2) +
        finiteFramePairedC2FullBRSTGaugeEuler period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric couplings
          (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input) (variation, 0) +
        pairedFiniteFrameC2InteractionEuler period hPeriod geometry frame hRegular interactionScale
          coefficients input.1 variation = 0) ∧
      (∀ variation : Fields,
        finiteFramePairedC2FullBRSTGaugeEuler period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric couplings
          (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input)
          (0, variation) = 0) := by
  rw [finiteFramePairedC2PhysicalEuler_eq_zero_iff_restrictions period hPeriod geometry frame
    hRegular couplings interactionScale coefficients input]
  constructor
  · rintro ⟨hMetric, hFields⟩
    constructor
    · intro variation
      have h := DFunLike.congr_fun hMetric variation
      rw [finiteFramePairedC2PhysicalMetricEuler_apply period hPeriod geometry frame hRegular
        couplings interactionScale coefficients input hInput variation] at h
      exact h
    · intro variation
      have h := DFunLike.congr_fun hFields variation
      rw [finiteFramePairedC2PhysicalFieldsEuler_apply period hPeriod geometry frame hRegular
        couplings interactionScale coefficients input hInput variation] at h
      exact h
  · rintro ⟨hMetric, hFields⟩
    constructor
    · apply ContinuousLinearMap.ext
      intro variation
      rw [finiteFramePairedC2PhysicalMetricEuler_apply period hPeriod geometry frame hRegular
        couplings interactionScale coefficients input hInput variation]
      exact hMetric variation
    · apply ContinuousLinearMap.ext
      intro variation
      rw [finiteFramePairedC2PhysicalFieldsEuler_apply period hPeriod geometry frame hRegular
        couplings interactionScale coefficients input hInput variation]
      exact hFields variation

end
end P0EFTJanusFiniteFramePairedC2PhysicalEulerEquations4D
end JanusFormal
