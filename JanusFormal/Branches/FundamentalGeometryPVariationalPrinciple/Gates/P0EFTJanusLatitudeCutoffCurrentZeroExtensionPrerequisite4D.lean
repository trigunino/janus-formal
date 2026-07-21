import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialTubularOpenEmbedding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D

namespace JanusFormal
namespace P0EFTJanusLatitudeCutoffCurrentZeroExtensionPrerequisite4D
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarIPP4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D

variable (period : Real) (hPeriod : period ≠ 0)

theorem cutoffCollarScalarCurrentDensity_contDiff
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    ContDiff Real ∞
      (cutoffCollarScalarCurrentDensity period hPeriod field test base) := by
  have hValue (f : SmoothQuotientField period hPeriod Real) :
      ContDiff Real ∞ (canonicalLatitudeValue period hPeriod f base) :=
    canonicalNormalSlice_contDiff period hPeriod f
      (canonicalLatitudeAnchor period hPeriod base)
  have hDerivative (f : SmoothQuotientField period hPeriod Real) :
      ContDiff Real ∞ (canonicalLatitudeDerivative period hPeriod f base) :=
    canonicalLatitudeDerivative_contDiff period hPeriod f base
  unfold cutoffCollarScalarCurrentDensity canonicalLatitudeScalarGreenCurrent
  exact canonicalLatitudeCollarCutoff_contDiff.mul
    (((hValue field).mul (hDerivative test)).sub
      ((hDerivative field).mul (hValue test)))

theorem cutoffCollarScalarCurrentDensity_eq_zero_of_one_le_abs
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : 1 ≤ |normal|) :
    cutoffCollarScalarCurrentDensity period hPeriod field test base normal = 0 := by
  rw [cutoffCollarScalarCurrentDensity,
    canonicalLatitudeCollarCutoff_eq_zero_of_one_le_abs normal hNormal, zero_mul]

theorem support_cutoffCollarScalarCurrentDensity_subset :
    ∀ (field test : SmoothQuotientField period hPeriod Real)
      (base : CanonicalLatitudeBase),
    Function.support
      (cutoffCollarScalarCurrentDensity period hPeriod field test base) ⊆
      Metric.ball (0 : Real) 1 := by
  intro field test base normal hNormal
  change dist normal 0 < 1
  rw [Real.dist_eq]
  by_contra hOutside
  apply hNormal
  exact cutoffCollarScalarCurrentDensity_eq_zero_of_one_le_abs period hPeriod
    field test base normal (by simpa using le_of_not_gt hOutside)

theorem tsupport_cutoffCollarScalarCurrentDensity_subset :
    ∀ (field test : SmoothQuotientField period hPeriod Real)
      (base : CanonicalLatitudeBase),
    tsupport (cutoffCollarScalarCurrentDensity period hPeriod field test base) ⊆
      Metric.closedBall (0 : Real) 1 := by
  intro field test base
  exact closure_minimal
    ((support_cutoffCollarScalarCurrentDensity_subset period hPeriod field test base).trans
      Metric.ball_subset_closedBall)
    Metric.isClosed_closedBall

end
end P0EFTJanusLatitudeCutoffCurrentZeroExtensionPrerequisite4D
end JanusFormal
