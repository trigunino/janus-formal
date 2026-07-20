import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCanonicalCutoffGlobalSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrentCanonicalNormalFlux4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCutoffGreenCurrentNormalFluxBridge4D

/-!
# Smooth cutoff scalar Green current on the cut bulk
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkSmoothCutoffScalarGreenCurrent4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D
open P0EFTJanusMappingTorusCutBulkAmbientSmoothGeneralLorentzMetric4D
open P0EFTJanusMappingTorusCutBulkSmoothInverseMusical4D
open P0EFTJanusMappingTorusCutBulkIntrinsicMetricVolumeDensity4D
open P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrent4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D
open P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
open P0EFTJanusMappingTorusCutBulkCanonicalCutoffGlobalSmooth4D
open P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrentCanonicalNormalFlux4D
open P0EFTJanusMappingTorusCutBulkCutoffGreenCurrentNormalFluxBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

local instance cutBulkIsManifold :
    IsManifold cutCollarModelWithCorners ∞
      (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobal_isManifold period hPeriod

/-- Genuine global vector field `χ • (φ grad ψ - ψ grad φ)`. -/
def intrinsicCutBulkSmoothCutoffScalarGreenCurrent
    (field test : SmoothQuotientField period hPeriod Real) :
    CutBulkSmoothVectorField period hPeriod where
  toFun := fun point => cutBulkCanonicalCutoff period hPeriod point •
    intrinsicCutBulkSmoothScalarGreenCurrent period hPeriod field test point
  contMDiff_toFun :=
    (cutBulkCanonicalCutoff_contMDiff period hPeriod).smul_section
      (intrinsicCutBulkSmoothScalarGreenCurrent period hPeriod field test).contMDiff

@[simp]
theorem intrinsicCutBulkSmoothCutoffScalarGreenCurrent_apply
    (field test : SmoothQuotientField period hPeriod Real)
    (point : PositiveHemisphereCutBulk period hPeriod) :
    intrinsicCutBulkSmoothCutoffScalarGreenCurrent period hPeriod field test point =
      cutBulkCanonicalCutoff period hPeriod point •
        intrinsicCutBulkSmoothScalarGreenCurrent period hPeriod field test point :=
  rfl

/-- On the canonical collar, the normal flux of the genuine cutoff vector
current is exactly the previously descended global scalar current. -/
theorem intrinsicCutBulkSmoothCutoffScalarGreenCurrent_canonicalNormalFlux
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Icc (0 : Real) 1) :
    let point := canonicalLatitudeCutBulkCollarMap period hPeriod (base, normal)
    (intrinsicCutBulkSmoothGeneralLorentzMetric period hPeriod).musical point
        (intrinsicCutBulkSmoothCutoffScalarGreenCurrent period hPeriod field test point)
        ((cutBulkToAmbientDerivativeEquiv period hPeriod point).symm
          (canonicalLatitudeNormalVector period hPeriod base normal)) =
      cutBulkScalarCurrent period hPeriod field test point := by
  dsimp only
  rw [intrinsicCutBulkSmoothCutoffScalarGreenCurrent_apply, map_smul,
    smul_apply, smul_eq_mul,
    cutBulkCanonicalCutoff_canonicalLatitudeCutBulkCollarMap
      period hPeriod base normal hNormal]
  change canonicalLatitudeCollarCutoff normal *
      canonicalCutBulkIntrinsicGreenNormalFlux period hPeriod field test base normal =
    cutBulkScalarCurrent period hPeriod field test
      (canonicalLatitudeCutBulkCollarPath period hPeriod base normal)
  exact (cutBulkScalarCurrent_canonicalCollarPath_eq_cutoff_mul_intrinsicFlux
    period hPeriod field test base normal hNormal).symm

end
end P0EFTJanusMappingTorusCutBulkSmoothCutoffScalarGreenCurrent4D
end JanusFormal
