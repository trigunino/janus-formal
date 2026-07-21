import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarGreenConservation4D

/-!
# Full-Euler bridge for the centered cutoff divergence
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceFullEulerBridge4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalPositiveLatitudeWeightedScalarIPP4D
open P0EFTJanusMappingTorusCanonicalLatitudeNormalTangentialAdaptedHolonomicChart4D
open P0EFTJanusMappingTorusCanonicalLatitudeHolonomicGlobalCutoffPullback4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffScalarGreenDivergence4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D
open P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D
open P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarGreenConservation4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := Fin 4 → Real

/-- Full equal-mass Euler equations on the canonical total atlas discharge the
free-current hypothesis in every centered adapted chart. -/
theorem adaptedLocalActualScalarGreenCoordinateDivergence_eq_zero_of_fullEuler
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : HolonomicAtlasLocalScalarEulerEquations period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) field
      (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared 0)
    (hTest : HolonomicAtlasLocalScalarEulerEquations period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) test
      (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared 0)
    (base : CanonicalLatitudeBase) (normal : Real)
    (chart : NormalTangentialAdaptedHolonomicChart period hPeriod base normal) :
    localActualScalarGreenCoordinateDivergence period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test 0 = 0 :=
  localActualScalarGreenCoordinateDivergence_eq_zero_of_equalMassEuler
    period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test
      massSquared 0
      (hField _ (canonicalTotalHolonomicAtlasCover_patch_mem period hPeriod _) 0)
      (hTest _ (canonicalTotalHolonomicAtlasCover_patch_mem period hPeriod _) 0)

/-- With the genuine 4D Euler equations, the exact metric density is represented
in every centered adapted chart without an extra `hFree` assumption. -/
theorem canonicalLatitudeCenteredMetricCutoffDivergenceDensity_eq_local_of_fullEuler
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hFieldLatitude : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared field)
    (hTestLatitude : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared test)
    (hFieldFull : HolonomicAtlasLocalScalarEulerEquations period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) field
      (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared 0)
    (hTestFull : HolonomicAtlasLocalScalarEulerEquations period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) test
      (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared 0)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Ioo (0 : Real) 1)
    (chart : NormalTangentialAdaptedHolonomicChart period hPeriod base normal)
    (baseMap : Vector4 → CanonicalLatitudeBase) :
    canonicalLatitudeCenteredMetricCutoffDivergenceDensity period hPeriod
        massSquared field test (base, normal) =
      canonicalPositiveLatitudeWeight normal *
        localActualCutoffScalarGreenCoordinateDivergence period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test
          (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
            period hPeriod normal baseMap) 0 :=
  canonicalLatitudeCenteredMetricCutoffDivergenceDensity_eq_local
    period hPeriod massSquared field test hFieldLatitude hTestLatitude base normal
      hNormal chart baseMap
      (adaptedLocalActualScalarGreenCoordinateDivergence_eq_zero_of_fullEuler
        period hPeriod massSquared field test hFieldFull hTestFull base normal chart)

end
end P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceFullEulerBridge4D
end JanusFormal
