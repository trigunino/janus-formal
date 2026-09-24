import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalDirectionalH1L24D

/-! Directional H¹-to-L² differentiation using ten redundant generators,
with only a smooth nondegenerate Lorentz metric and no global tangent basis. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDirectionalH1L24D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal BigOperators
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
open P0EFTJanusProgramPT12CanonicalScalarH1Injective4D
open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPT12CanonicalDirectionalH1L24D

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

variable (metric : SmoothGeneralLorentzMetric period hPeriod)
variable (vector : SmoothTangentField period hPeriod)

def frameFreeTenFlowDualCoefficient (index : Fin 10) :
    SmoothQuotientField period hPeriod Real :=
  generalMetricFiniteFrameCoefficient period hPeriod
    (canonicalTenFlowFrame period hPeriod) metric vector index

theorem frameFreeTenFlowDual_reconstructs (point : EffectiveQuotient period hPeriod) :
    vector point = ∑ index : Fin 10,
      frameFreeTenFlowDualCoefficient period hPeriod metric vector index point •
        canonicalTenFlowGeneratorAt period hPeriod point
          (canonicalFlowIndexEquivFinTen.symm index) := by
  exact generalMetricFiniteFrame_reconstructs period hPeriod
    (canonicalTenFlowFrame period hPeriod) metric vector point

theorem frameFreeTenFlowDirectionalDerivative_reconstructs
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    mvfderiv coverModelWithCorners field.toFun point (vector point) =
      ∑ index : Fin 10,
        frameFreeTenFlowDualCoefficient period hPeriod metric vector index point *
          frameDerivative period hPeriod Real
            (canonicalTenFlowFrame period hPeriod) field point index := by
  rw [frameFreeTenFlowDual_reconstructs period hPeriod metric vector point]
  simp only [map_sum, map_smul, smul_eq_mul, frameDerivative_eq_mfderiv]
  apply Finset.sum_congr rfl
  intro index _
  rfl

/-- The smooth intrinsic directional derivative in redundant coordinates. -/
def frameFreeDirectionalDerivativeSmooth :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      SmoothQuotientField period hPeriod Real :=
  ∑ index : Fin 10,
    (canonicalScalarMul period hPeriod
      (frameFreeTenFlowDualCoefficient period hPeriod metric vector index)).comp
        (canonicalFrameDerivativeSmooth period hPeriod
          (canonicalTenFlowFrame period hPeriod) index)

theorem frameFreeDirectionalDerivativeSmooth_apply
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    frameFreeDirectionalDerivativeSmooth period hPeriod metric vector field point =
      mvfderiv coverModelWithCorners field.toFun point (vector point) := by
  simp only [frameFreeDirectionalDerivativeSmooth, LinearMap.sum_apply,
    LinearMap.comp_apply]
  rw [canonicalScalar_sum_apply]
  exact (frameFreeTenFlowDirectionalDerivative_reconstructs
    period hPeriod metric vector field point).symm

/-- Bounded extension to canonical ten-flow H¹. -/
def frameFreeDirectionalH1ToL2 :
    CanonicalTenFlowScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalBulkL2 period hPeriod :=
  ∑ index : Fin 10,
    (canonicalSmoothMultiplier period hPeriod
      (frameFreeTenFlowDualCoefficient period hPeriod metric vector index)).comp
        (canonicalH1DerivativeToL2 period hPeriod
          (canonicalTenFlowFrame period hPeriod) index)

theorem frameFreeDirectionalH1ToL2_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    frameFreeDirectionalH1ToL2 period hPeriod metric vector
        (smoothToH1GraphLinearMap period hPeriod Real
          (canonicalTenFlowFrame period hPeriod)
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field) =
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (frameFreeDirectionalDerivativeSmooth period hPeriod metric vector field) := by
  simp only [frameFreeDirectionalH1ToL2, sum_apply,
    ContinuousLinearMap.comp_apply, canonicalH1DerivativeToL2_smooth,
    canonicalFrameDerivativeL2, frameFreeDirectionalDerivativeSmooth,
    LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact canonicalSmoothMultiplier_smooth period hPeriod
    (frameFreeTenFlowDualCoefficient period hPeriod metric vector index)
    (canonicalFrameDerivativeSmooth period hPeriod
      (canonicalTenFlowFrame period hPeriod) index field)

theorem frameFreeDirectionalH1ToL2_norm_le
    (field : CanonicalTenFlowScalarH1 period hPeriod) :
    ‖frameFreeDirectionalH1ToL2 period hPeriod metric vector field‖ ≤
      ‖frameFreeDirectionalH1ToL2 period hPeriod metric vector‖ * ‖field‖ :=
  (frameFreeDirectionalH1ToL2 period hPeriod metric vector).le_opNorm field

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDirectionalH1L24D
