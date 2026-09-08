import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalEulerEquations4D

/-! # Three-block stationarity split of the paired physical C² Euler map -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalEulerThreeBlockSplit4D

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
open P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTEulerDecomposition4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerGaugeSlots4D
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
local notation "AbelianFields" => FiniteFramePairedC2AbelianGaugeFields period hPeriod frame frame
local notation "DiffeomorphismFields" =>
  FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame
local notation "Fields" => AbelianFields × DiffeomorphismFields
local notation "Domain" => finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular

/-- Abelian-field restriction of the physical Euler map. -/
def finiteFramePairedC2PhysicalAbelianFieldsEuler
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) (input : Input) :
    AbelianFields →L[Real] Real :=
  (finiteFramePairedC2PhysicalFieldsEuler period hPeriod geometry frame hRegular couplings
    interactionScale coefficients input).comp
      (ContinuousLinearMap.inl Real AbelianFields DiffeomorphismFields)

/-- Diffeomorphism-field restriction of the physical Euler map. -/
def finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) (input : Input) :
    DiffeomorphismFields →L[Real] Real :=
  (finiteFramePairedC2PhysicalFieldsEuler period hPeriod geometry frame hRegular couplings
    interactionScale coefficients input).comp
      (ContinuousLinearMap.inr Real AbelianFields DiffeomorphismFields)

/-- The field restriction vanishes exactly when both gauge-field restrictions vanish. -/
theorem finiteFramePairedC2PhysicalFieldsEuler_eq_zero_iff_gauge_restrictions
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) (input : Input) :
    finiteFramePairedC2PhysicalFieldsEuler period hPeriod geometry frame hRegular couplings
        interactionScale coefficients input = 0 ↔
      finiteFramePairedC2PhysicalAbelianFieldsEuler period hPeriod geometry frame hRegular couplings
          interactionScale coefficients input = 0 ∧
        finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler period hPeriod geometry frame hRegular
          couplings interactionScale coefficients input = 0 := by
  constructor
  · intro hEuler
    constructor
    · apply ContinuousLinearMap.ext
      intro variation
      simp [finiteFramePairedC2PhysicalAbelianFieldsEuler, hEuler]
    · apply ContinuousLinearMap.ext
      intro variation
      simp [finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler, hEuler]
  · rintro ⟨hAbelian, hDiffeomorphism⟩
    apply ContinuousLinearMap.ext
    intro variation
    have hSplit : variation = (variation.1, 0) + (0, variation.2) := by
      apply Prod.ext <;> simp
    rw [hSplit, map_add]
    have hAbelianZero := DFunLike.congr_fun hAbelian variation.1
    have hDiffeomorphismZero := DFunLike.congr_fun hDiffeomorphism variation.2
    simpa [finiteFramePairedC2PhysicalAbelianFieldsEuler,
      finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler] using
        congrArg₂ (· + ·) hAbelianZero hDiffeomorphismZero

/-- Concrete Abelian-field restriction. -/
theorem finiteFramePairedC2PhysicalAbelianFieldsEuler_apply
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) (hInput : input ∈ Domain) (variation : AbelianFields) :
    finiteFramePairedC2PhysicalAbelianFieldsEuler period hPeriod geometry frame hRegular couplings
        interactionScale coefficients input variation =
      finiteFramePairedC2AbelianBRSTEuler period hPeriod frame frame geometry.plusMetric
        geometry.plusMetric
        (finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric
          (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input))
        (finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric ((0 : MetricPair), (variation, 0))) := by
  exact finiteFramePairedC2PhysicalEuler_abelian_fields_apply period hPeriod geometry frame hRegular
    couplings interactionScale coefficients input hInput variation

/-- Concrete diffeomorphism-field restriction. -/
theorem finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler_apply
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) (hInput : input ∈ Domain) (variation : DiffeomorphismFields) :
    finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler period hPeriod geometry frame hRegular
        couplings interactionScale coefficients input variation =
      finiteFramePairedDiffeomorphismBRSTEuler period hPeriod frame frame frame
        geometry.plusMetric geometry.plusMetric couplings
        (finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric
          (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input))
        (finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric ((0 : MetricPair), (0, variation))) := by
  exact finiteFramePairedC2PhysicalEuler_diffeomorphism_fields_apply period hPeriod geometry frame
    hRegular couplings interactionScale coefficients input hInput variation

/-- Full stationarity is equivalent to the metric, Abelian, and diffeomorphism blocks. -/
theorem finiteFramePairedC2PhysicalEuler_eq_zero_iff_three_blocks
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) (input : Input) :
    finiteFramePairedC2PhysicalEuler period hPeriod geometry frame hRegular couplings interactionScale
        coefficients input = 0 ↔
      finiteFramePairedC2PhysicalMetricEuler period hPeriod geometry frame hRegular couplings
          interactionScale coefficients input = 0 ∧
        finiteFramePairedC2PhysicalAbelianFieldsEuler period hPeriod geometry frame hRegular couplings
          interactionScale coefficients input = 0 ∧
        finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler period hPeriod geometry frame hRegular
          couplings interactionScale coefficients input = 0 := by
  rw [finiteFramePairedC2PhysicalEuler_eq_zero_iff_restrictions period hPeriod geometry frame hRegular
    couplings interactionScale coefficients input,
    finiteFramePairedC2PhysicalFieldsEuler_eq_zero_iff_gauge_restrictions period hPeriod geometry frame
      hRegular couplings interactionScale coefficients input]

end
end P0EFTJanusFiniteFramePairedC2PhysicalEulerThreeBlockSplit4D
end JanusFormal
