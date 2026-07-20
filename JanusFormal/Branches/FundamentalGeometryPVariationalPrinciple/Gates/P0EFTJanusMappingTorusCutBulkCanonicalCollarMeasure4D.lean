import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkScalarCurrentCanonicalStokes4D

/-!
# Canonical collar measure on the global cut bulk

The canonical base/normal product measure is pushed through the actual cut-bulk
collar map.  Its integral is exactly the iterated canonical collar integral.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open scoped Interval
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentCollarCoordinateBridge4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Canonical fundamental-domain collar map into the actual global cut bulk. -/
def canonicalLatitudeCutBulkCollarMap
    (parameter : CanonicalLatitudeCollarParameter) :
    PositiveHemisphereCutBulk period hPeriod :=
  canonicalLatitudeCutBulkCollarPath period hPeriod parameter.1 parameter.2

theorem continuous_canonicalLatitudeCutBulkCollarMap :
    Continuous (canonicalLatitudeCutBulkCollarMap period hPeriod) := by
  have hBoundaryCover : Continuous
      (fun base : CanonicalLatitudeBase ↦
        (⟨equatorialTwoSphereHomeomorph.symm base.1, base.2⟩ :
          MappingTorusCover (orientationDoubleData period hPeriod))) := by
    have hProduct := equatorialTwoSphereHomeomorph.symm.continuous.prodMap
      (continuous_id : Continuous (id : Real → Real))
    exact ((coverHomeomorphProd (orientationDoubleData period hPeriod)).symm
      |>.continuous.comp hProduct).congr fun _ ↦ rfl
  have hBoundary : Continuous
      (canonicalLatitudeCutBoundaryFirstLift period hPeriod) :=
    continuous_quotient_mk'.comp hBoundaryCover
  have hNormal : Continuous
      (fun parameter : CanonicalLatitudeCollarParameter ↦
        Set.projIcc 0 1 zero_le_one parameter.2) :=
    continuous_projIcc.comp continuous_snd
  have hParameter : Continuous
      (fun parameter : CanonicalLatitudeCollarParameter ↦
        (canonicalLatitudeCutBoundaryFirstLift period hPeriod parameter.1,
          Set.projIcc 0 1 zero_le_one parameter.2)) :=
    (hBoundary.comp continuous_fst).prodMk hNormal
  exact (continuous_cutCollarAttachment period hPeriod).comp hParameter

local instance bulkMeasurableSpace :
    MeasurableSpace (PositiveHemisphereCutBulk period hPeriod) := borel _

local instance bulkBorelSpace :
    BorelSpace (PositiveHemisphereCutBulk period hPeriod) where
  measurable_eq := rfl

/-- Pushforward of the canonical base times positive-unit-normal measure. -/
def cutBulkCanonicalCollarMeasure :
    Measure (PositiveHemisphereCutBulk period hPeriod) :=
  Measure.map (canonicalLatitudeCutBulkCollarMap period hPeriod)
    (canonicalLatitudeCollarMeasure period)

theorem integral_cutBulkCanonicalCollarMeasure
    (function : PositiveHemisphereCutBulk period hPeriod → Real)
    (hFunction : Continuous function)
    (hIntegrable : Integrable function
      (cutBulkCanonicalCollarMeasure period hPeriod)) :
    ∫ bulk, function bulk ∂cutBulkCanonicalCollarMeasure period hPeriod =
      ∫ base, (∫ normal in (0 : Real)..1,
        function (canonicalLatitudeCutBulkCollarMap period hPeriod
          (base, normal))) ∂canonicalLatitudeBaseMeasure period := by
  letI : IsFiniteMeasure (canonicalLatitudeBaseMeasure period) :=
    canonicalLatitudeBaseMeasure_isFinite period
  have hPullbackIntegrable : Integrable
      (function ∘ canonicalLatitudeCutBulkCollarMap period hPeriod)
      (canonicalLatitudeCollarMeasure period) := by
    exact hIntegrable.comp_measurable
      (continuous_canonicalLatitudeCutBulkCollarMap period hPeriod).measurable
  have hPullbackIntegrable' := hPullbackIntegrable
  change Integrable
      (Function.uncurry (fun base : CanonicalLatitudeBase ↦ fun normal : Real ↦
        function (canonicalLatitudeCutBulkCollarMap period hPeriod
          (base, normal))))
      ((canonicalLatitudeBaseMeasure period).prod
        canonicalLatitudeUnitNormalMeasure) at hPullbackIntegrable'
  rw [cutBulkCanonicalCollarMeasure]
  rw [integral_map
    (continuous_canonicalLatitudeCutBulkCollarMap period hPeriod).measurable.aemeasurable
    hFunction.aestronglyMeasurable]
  rw [canonicalLatitudeCollarMeasure]
  calc
    (∫ parameter : CanonicalLatitudeCollarParameter,
        function (canonicalLatitudeCutBulkCollarMap period hPeriod parameter)
        ∂(canonicalLatitudeBaseMeasure period).prod
          canonicalLatitudeUnitNormalMeasure) =
      ∫ base, (∫ normal,
        function (canonicalLatitudeCutBulkCollarMap period hPeriod
          (base, normal)) ∂canonicalLatitudeUnitNormalMeasure)
        ∂canonicalLatitudeBaseMeasure period :=
      by
        simpa [Function.uncurry] using
          (integral_integral hPullbackIntegrable').symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun base ↦ by
        change (∫ normal,
            function (canonicalLatitudeCutBulkCollarMap period hPeriod
              (base, normal)) ∂canonicalLatitudeUnitNormalMeasure) =
          ∫ normal in (0 : Real)..1,
            function (canonicalLatitudeCutBulkCollarMap period hPeriod
              (base, normal))
        rw [intervalIntegral.integral_of_le zero_le_one]
        rfl

end
end P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
end JanusFormal
