import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDivergenceStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D

/-! Metric-volume divergence and weak Stokes without a global tangent basis. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeMetricDivergenceStokes4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusProgramPT12FrameFreeDivergenceStokes4D

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

variable (metric : SmoothGeneralLorentzMetric period hPeriod)
variable (vector : SmoothTangentField period hPeriod)

/-- Densitize the current by the positive intrinsic volume ratio. -/
def frameFreeMetricVolumeCurrent : SmoothTangentField period hPeriod :=
  smoothScalarSMulTangentField period hPeriod
    (globalSmoothMetricVolumeRatio period hPeriod metric) vector

@[simp] theorem frameFreeMetricVolumeCurrent_apply
    (point : EffectiveQuotient period hPeriod) :
    frameFreeMetricVolumeCurrent period hPeriod metric vector point =
      globalMetricVolumeRatio period hPeriod metric point • vector point := rfl

def frameFreeMetricVolumeDivergence : SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    frameFreeTenFlowDivergence period hPeriod metric
        (frameFreeMetricVolumeCurrent period hPeriod metric vector) point /
      globalMetricVolumeRatio period hPeriod metric point
  contMDiff_toFun :=
    (frameFreeTenFlowDivergence period hPeriod metric
      (frameFreeMetricVolumeCurrent period hPeriod metric vector)).contMDiff_toFun.div₀
      (globalSmoothMetricVolumeRatio period hPeriod metric).contMDiff_toFun
      (fun point => ne_of_gt (globalMetricVolumeRatio_pos period hPeriod metric point))

@[simp] theorem frameFreeMetricVolumeDivergence_apply
    (point : EffectiveQuotient period hPeriod) :
    frameFreeMetricVolumeDivergence period hPeriod metric vector point =
      frameFreeTenFlowDivergence period hPeriod metric
          (frameFreeMetricVolumeCurrent period hPeriod metric vector) point /
        globalMetricVolumeRatio period hPeriod metric point := rfl

theorem globalMetricVolumeRatio_mul_frameFreeMetricVolumeDivergence
    (point : EffectiveQuotient period hPeriod) :
    globalMetricVolumeRatio period hPeriod metric point *
        frameFreeMetricVolumeDivergence period hPeriod metric vector point =
      frameFreeTenFlowDivergence period hPeriod metric
        (frameFreeMetricVolumeCurrent period hPeriod metric vector) point := by
  rw [frameFreeMetricVolumeDivergence_apply]
  field_simp [ne_of_gt (globalMetricVolumeRatio_pos period hPeriod metric point)]

theorem frameFreeMetricVolumeDivergence_integrable :
    Integrable (frameFreeMetricVolumeDivergence period hPeriod metric vector)
      (generalLorentzVolumeMeasure period hPeriod metric) := by
  letI : IsFiniteMeasure (generalLorentzVolumeMeasure period hPeriod metric) :=
    generalLorentzVolumeMeasure_isFinite period hPeriod metric
  exact (frameFreeMetricVolumeDivergence period hPeriod metric vector
    ).contMDiff_toFun.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Weak Stokes for the intrinsic metric-volume measure. -/
theorem frameFreeMetricVolumeDivergence_weak_stokes
    (test : SmoothQuotientField period hPeriod Real) :
    (∫ point,
        test point * frameFreeMetricVolumeDivergence period hPeriod metric vector point
      ∂generalLorentzVolumeMeasure period hPeriod metric) =
      -∫ point, mvfderiv coverModelWithCorners test.toFun point (vector point)
        ∂generalLorentzVolumeMeasure period hPeriod metric := by
  rw [integral_generalLorentzVolumeMeasure_eq_reference,
    integral_generalLorentzVolumeMeasure_eq_reference]
  calc
    (∫ point,
        globalMetricVolumeRatio period hPeriod metric point *
          (test point * frameFreeMetricVolumeDivergence period hPeriod metric vector point)
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
        ∫ point, test point *
          frameFreeTenFlowDivergence period hPeriod metric
            (frameFreeMetricVolumeCurrent period hPeriod metric vector) point
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
      apply integral_congr_ae
      filter_upwards [] with point
      rw [← globalMetricVolumeRatio_mul_frameFreeMetricVolumeDivergence
        period hPeriod metric vector point]
      ring
    _ = -∫ point, mvfderiv coverModelWithCorners test.toFun point
        (frameFreeMetricVolumeCurrent period hPeriod metric vector point)
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod :=
      frameFreeTenFlowDivergence_weak_stokes period hPeriod metric
        (frameFreeMetricVolumeCurrent period hPeriod metric vector) test
    _ = -∫ point, globalMetricVolumeRatio period hPeriod metric point *
        mvfderiv coverModelWithCorners test.toFun point (vector point)
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with point
      change mvfderiv coverModelWithCorners test.toFun point
        (globalMetricVolumeRatio period hPeriod metric point • vector point) = _
      rw [map_smul]
      rfl

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeMetricDivergenceStokes4D
