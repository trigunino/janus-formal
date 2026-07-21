import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalLatitudeScalarCurrentJointDivergenceSmooth4D

/-!
# Canonical divergence measure on the global cut bulk

The signed collar divergence density is pushed to the actual cut bulk.  This
does not require choosing inverse collar coordinates or proving injectivity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped Interval
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentCanonicalStokes4D
open P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
open P0EFTJanusCanonicalLatitudeScalarCurrentJointDivergenceSmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Signed divergence density on the canonical source collar. -/
def canonicalCutBulkDivergenceDensity
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeCollarParameter) : Real :=
  cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
    field test parameter.1 parameter.2

theorem canonicalCutBulkDivergenceDensity_integrable
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    Integrable
      (canonicalCutBulkDivergenceDensity period hPeriod massSquared field test)
      (canonicalLatitudeCollarMeasure period) := by
  let jointDensity : CanonicalLatitudeCollarParameter → Real :=
    jointCutoffCollarScalarCurrentDivergence period hPeriod field test
  have hContinuous : Continuous jointDensity :=
    (jointCutoffCollarScalarCurrentDivergence_contMDiff period hPeriod field test).continuous
  have hFiber (base : CanonicalLatitudeBase) : Integrable
      (fun normal ↦ jointDensity (base, normal))
      canonicalLatitudeUnitNormalMeasure := by
    have hFiberContinuous : Continuous (fun normal ↦ jointDensity (base, normal)) :=
      hContinuous.comp (continuous_const.prodMk continuous_id)
    unfold canonicalLatitudeUnitNormalMeasure
    have hIcc : Integrable (fun normal ↦ jointDensity (base, normal))
        (volume.restrict (Set.Icc (0 : Real) 1)) :=
      hFiberContinuous.continuousOn.integrableOn_Icc
    exact hIcc.mono_measure
      (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
  have hInnerInterval : Continuous (fun base : CanonicalLatitudeBase ↦
      ∫ normal in (0 : Real)..1, ‖jointDensity (base, normal)‖) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hContinuous.norm
  have hInner : Continuous (fun base : CanonicalLatitudeBase ↦
      ∫ normal, ‖jointDensity (base, normal)‖
        ∂canonicalLatitudeUnitNormalMeasure) := by
    apply hInnerInterval.congr
    intro base
    rw [intervalIntegral.integral_of_le zero_le_one]
    rfl
  have hJointIntegrable : Integrable jointDensity
      ((canonicalLatitudeBaseMeasure period).prod
        canonicalLatitudeUnitNormalMeasure) := by
    refine (integrable_prod_iff hContinuous.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall hFiber
    · exact continuous_integrable_canonicalLatitudeBaseMeasure period _ hInner
  rw [canonicalLatitudeCollarMeasure]
  exact hJointIntegrable.congr (Filter.Eventually.of_forall fun parameter ↦ by
    simpa [jointDensity, canonicalCutBulkDivergenceDensity] using
      jointCutoffCollarScalarCurrentDivergence_eq period hPeriod massSquared
        field test parameter)

local instance bulkMeasurableSpace :
    MeasurableSpace (PositiveHemisphereCutBulk period hPeriod) := borel _

local instance bulkBorelSpace :
    BorelSpace (PositiveHemisphereCutBulk period hPeriod) where
  measurable_eq := rfl

/-- Pushforward to the actual cut bulk of the signed canonical divergence
density. -/
def cutBulkCanonicalDivergenceMeasure
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    VectorMeasure (PositiveHemisphereCutBulk period hPeriod) Real :=
  ((canonicalLatitudeCollarMeasure period).withDensityᵥ
      (canonicalCutBulkDivergenceDensity period hPeriod massSquared field test)).map
    (canonicalLatitudeCutBulkCollarMap period hPeriod)

/-- The total pushed divergence is exactly the canonical iterated bulk
integral. -/
private theorem cutBulkCanonicalDivergenceMeasure_univ_of_integrable
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hIntegrable : Integrable
      (canonicalCutBulkDivergenceDensity period hPeriod massSquared field test)
      (canonicalLatitudeCollarMeasure period)) :
    cutBulkCanonicalDivergenceMeasure period hPeriod massSquared field test Set.univ =
      ∫ base, (∫ normal in (0 : Real)..1,
        cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
          field test base normal) ∂canonicalLatitudeBaseMeasure period := by
  letI : IsFiniteMeasure (canonicalLatitudeBaseMeasure period) :=
    canonicalLatitudeBaseMeasure_isFinite period
  rw [cutBulkCanonicalDivergenceMeasure, VectorMeasure.map_apply _
    (continuous_canonicalLatitudeCutBulkCollarMap period hPeriod).measurable
    MeasurableSet.univ]
  rw [Set.preimage_univ, withDensityᵥ_apply hIntegrable MeasurableSet.univ,
    setIntegral_univ,
    canonicalLatitudeCollarMeasure]
  have hIntegrable' := hIntegrable
  change Integrable
      (Function.uncurry (fun base : CanonicalLatitudeBase ↦ fun normal : Real ↦
        cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
          field test base normal))
      ((canonicalLatitudeBaseMeasure period).prod
        canonicalLatitudeUnitNormalMeasure) at hIntegrable'
  calc
    (∫ parameter : CanonicalLatitudeCollarParameter,
        canonicalCutBulkDivergenceDensity period hPeriod massSquared field test parameter
        ∂(canonicalLatitudeBaseMeasure period).prod
          canonicalLatitudeUnitNormalMeasure) =
      ∫ base, (∫ normal,
        cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
          field test base normal ∂canonicalLatitudeUnitNormalMeasure)
        ∂canonicalLatitudeBaseMeasure period := by
          simpa [canonicalCutBulkDivergenceDensity, Function.uncurry] using
            (integral_integral hIntegrable').symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun base ↦ by
        change (∫ normal,
            cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
              field test base normal ∂canonicalLatitudeUnitNormalMeasure) =
          ∫ normal in (0 : Real)..1,
            cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
              field test base normal
        rw [intervalIntegral.integral_of_le zero_le_one]
        rfl

theorem cutBulkCanonicalDivergenceMeasure_univ
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkCanonicalDivergenceMeasure period hPeriod massSquared field test Set.univ =
      ∫ base, (∫ normal in (0 : Real)..1,
        cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
          field test base normal) ∂canonicalLatitudeBaseMeasure period :=
  cutBulkCanonicalDivergenceMeasure_univ_of_integrable period hPeriod massSquared
    field test (canonicalCutBulkDivergenceDensity_integrable period hPeriod
      massSquared field test)

/-- Intrinsic bulk-measure form of canonical two-sheet Stokes. -/
theorem two_mul_cutBulkCanonicalDivergenceMeasure_univ_eq_neg_boundary
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    2 * cutBulkCanonicalDivergenceMeasure period hPeriod massSquared field test Set.univ =
      -twoSheetOrientedScalarCurrentIntegral period hPeriod field test := by
  rw [cutBulkCanonicalDivergenceMeasure_univ period hPeriod massSquared field test,
    two_mul_productHalfCollarIntegral_eq_neg_twoSheetOrientedCurrent]

end
end P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
end JanusFormal
