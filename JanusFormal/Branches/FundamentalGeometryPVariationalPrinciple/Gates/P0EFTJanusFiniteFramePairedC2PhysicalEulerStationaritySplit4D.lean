import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedDiffeomorphismBRSTEulerSectors4D

/-! # Stationarity split of the paired physical C² Euler map -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalEulerStationaritySplit4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
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
local notation "Fields" =>
  FiniteFramePairedC2AbelianGaugeFields period hPeriod frame frame ×
    FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame
local notation "Domain" => finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular

/-- Metric restriction of the actual physical Euler map. -/
def finiteFramePairedC2PhysicalMetricEuler
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) (input : Input) :
    MetricPair →L[Real] Real :=
  (finiteFramePairedC2PhysicalEuler period hPeriod geometry frame hRegular couplings interactionScale
    coefficients input).comp (ContinuousLinearMap.inl Real MetricPair Fields)

/-- Gauge-field restriction of the actual physical Euler map. -/
def finiteFramePairedC2PhysicalFieldsEuler
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) (input : Input) :
    Fields →L[Real] Real :=
  (finiteFramePairedC2PhysicalEuler period hPeriod geometry frame hRegular couplings interactionScale
    coefficients input).comp (ContinuousLinearMap.inr Real MetricPair Fields)

/-- Stationarity on the product is equivalent to stationarity on its metric and field factors. -/
theorem finiteFramePairedC2PhysicalEuler_eq_zero_iff_restrictions
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) (input : Input) :
    finiteFramePairedC2PhysicalEuler period hPeriod geometry frame hRegular couplings interactionScale
        coefficients input = 0 ↔
      finiteFramePairedC2PhysicalMetricEuler period hPeriod geometry frame hRegular couplings
          interactionScale coefficients input = 0 ∧
        finiteFramePairedC2PhysicalFieldsEuler period hPeriod geometry frame hRegular couplings
          interactionScale coefficients input = 0 := by
  constructor
  · intro hEuler
    constructor
    · apply ContinuousLinearMap.ext
      intro variation
      simp [finiteFramePairedC2PhysicalMetricEuler, hEuler]
    · apply ContinuousLinearMap.ext
      intro variation
      simp [finiteFramePairedC2PhysicalFieldsEuler, hEuler]
  · rintro ⟨hMetric, hFields⟩
    apply ContinuousLinearMap.ext
    intro variation
    have hSplit : variation = (variation.1, 0) + (0, variation.2) := by
      apply Prod.ext <;> simp
    rw [hSplit, map_add]
    have hMetricZero := DFunLike.congr_fun hMetric variation.1
    have hFieldsZero := DFunLike.congr_fun hFields variation.2
    simpa [finiteFramePairedC2PhysicalMetricEuler,
      finiteFramePairedC2PhysicalFieldsEuler] using congrArg₂ (· + ·) hMetricZero hFieldsZero

/-- Concrete value of the metric restriction. -/
theorem finiteFramePairedC2PhysicalMetricEuler_apply
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) (hInput : input ∈ Domain) (variation : MetricPair) :
    finiteFramePairedC2PhysicalMetricEuler period hPeriod geometry frame hRegular couplings
        interactionScale coefficients input variation =
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
        coefficients input.1 variation := by
  exact finiteFramePairedC2PhysicalEuler_metric_apply period hPeriod geometry frame hRegular couplings
    interactionScale coefficients input hInput variation

/-- Concrete value of the gauge-field restriction. -/
theorem finiteFramePairedC2PhysicalFieldsEuler_apply
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) (hInput : input ∈ Domain) (variation : Fields) :
    finiteFramePairedC2PhysicalFieldsEuler period hPeriod geometry frame hRegular couplings
        interactionScale coefficients input variation =
      finiteFramePairedC2FullBRSTGaugeEuler period hPeriod frame frame frame
        geometry.plusMetric geometry.plusMetric couplings
        (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input) (0, variation) := by
  exact finiteFramePairedC2PhysicalEuler_fields_apply period hPeriod geometry frame hRegular couplings
    interactionScale coefficients input hInput variation

end
end P0EFTJanusFiniteFramePairedC2PhysicalEulerStationaritySplit4D
end JanusFormal
