import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalScalarH1Injective4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SmoothMatrixL24D

/-! Smooth directional derivatives act boundedly from canonical ten-flow H¹ to L². -/
namespace JanusFormal.P0EFTJanusProgramPT12CanonicalDirectionalH1L24D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal BigOperators
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusMappingTorusCanonicalTenFlowSmoothDual4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
open P0EFTJanusProgramPT12CanonicalScalarH1Injective4D
open P0EFTJanusProgramPT12SmoothMatrixL24D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

abbrev CanonicalTenFlowScalarH1 :=
  H1GraphSpace period hPeriod Real (canonicalTenFlowFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

variable (metric : RegularGeneralLorentzMetric period hPeriod)
variable (vector : SmoothTangentField period hPeriod)

/-- The intrinsic directional derivative represented by its ten smooth coefficients. -/
def canonicalDirectionalDerivativeSmooth :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      SmoothQuotientField period hPeriod Real :=
  ∑ index : Fin 10,
    (canonicalScalarMul period hPeriod
      (canonicalTenFlowDualCoefficient period hPeriod metric vector index)).comp
        (canonicalFrameDerivativeSmooth period hPeriod
          (canonicalTenFlowFrame period hPeriod) index)

theorem canonicalDirectionalDerivativeSmooth_apply
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    canonicalDirectionalDerivativeSmooth period hPeriod metric vector field point =
      mvfderiv coverModelWithCorners field.toFun point (vector point) := by
  simp only [canonicalDirectionalDerivativeSmooth, LinearMap.sum_apply,
    LinearMap.comp_apply]
  rw [canonicalScalar_sum_apply]
  exact (canonicalTenFlowDirectionalDerivative_reconstructs
    period hPeriod metric vector field point).symm

/-- A bounded operator assembled from completed H¹ derivatives and smooth multipliers. -/
def canonicalDirectionalH1ToL2 :
    CanonicalTenFlowScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalBulkL2 period hPeriod :=
  ∑ index : Fin 10,
    (canonicalSmoothMultiplier period hPeriod
      (canonicalTenFlowDualCoefficient period hPeriod metric vector index)).comp
        (canonicalH1DerivativeToL2 period hPeriod
          (canonicalTenFlowFrame period hPeriod) index)

theorem canonicalDirectionalH1ToL2_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalDirectionalH1ToL2 period hPeriod metric vector
        (smoothToH1GraphLinearMap period hPeriod Real
          (canonicalTenFlowFrame period hPeriod)
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field) =
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (canonicalDirectionalDerivativeSmooth period hPeriod metric vector field) := by
  simp only [canonicalDirectionalH1ToL2, sum_apply,
    ContinuousLinearMap.comp_apply, canonicalH1DerivativeToL2_smooth,
    canonicalFrameDerivativeL2, canonicalDirectionalDerivativeSmooth,
    LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact canonicalSmoothMultiplier_smooth period hPeriod
    (canonicalTenFlowDualCoefficient period hPeriod metric vector index)
    (canonicalFrameDerivativeSmooth period hPeriod
      (canonicalTenFlowFrame period hPeriod) index field)

theorem canonicalDirectionalH1ToL2_norm_le
    (field : CanonicalTenFlowScalarH1 period hPeriod) :
    ‖canonicalDirectionalH1ToL2 period hPeriod metric vector field‖ ≤
      ‖canonicalDirectionalH1ToL2 period hPeriod metric vector‖ * ‖field‖ :=
  (canonicalDirectionalH1ToL2 period hPeriod metric vector).le_opNorm field

end
end JanusFormal.P0EFTJanusProgramPT12CanonicalDirectionalH1L24D
