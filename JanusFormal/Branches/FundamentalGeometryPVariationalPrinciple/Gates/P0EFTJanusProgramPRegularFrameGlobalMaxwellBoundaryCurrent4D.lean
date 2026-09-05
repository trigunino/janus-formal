import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameWeightedGlobalMaxwellResidualTestSeparation4D

/-! # Global densitized Maxwell boundary current -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameGlobalMaxwellBoundaryCurrent4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D
open P0EFTJanusProgramPRegularFrameWeightedGlobalMaxwellResidualTestSeparation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance intrinsicCanonicalLorentzVolumeMeasureIsFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Smooth metric-raised vector associated with one element of the regular
coframe. -/
def regularFrameSmoothDualVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : Fin 4) : SmoothTangentField period hPeriod where
  toFun := fun point =>
    ∑ column : Fin 4,
      regularFrameMetricInverseMatrix period hPeriod metric index column point •
        metric.frame column point
  contMDiff_toFun := by
    apply ContMDiff.sum_section
    intro column _
    exact
      (regularFrameMetricInverseMatrix period hPeriod metric index column
        ).contMDiff_toFun.smul_section
          (metric.frame column).contMDiff_toFun

theorem regularFrameSmoothDualVector_metric_pairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : Fin 4) (point : EffectiveQuotient period hPeriod)
    (vector : TangentSpace coverModelWithCorners point) :
    metric.metric.tensor.tensor point
        (regularFrameSmoothDualVector period hPeriod metric index point) vector =
      regularFrameDualCovector period hPeriod metric index point vector := by
  rw [regularFrameDualCovector_apply]
  change metric.metric.tensor.tensor point
      (∑ column : Fin 4,
        regularFrameMetricInverseMatrix period hPeriod metric index column point •
          metric.frame column point) vector = _
  rw [map_sum]
  simp only [sum_apply, map_smul, smul_apply, smul_eq_mul]

@[simp]
theorem regularFrameSmoothDualVector_frame
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index frameIndex : Fin 4) (point : EffectiveQuotient period hPeriod) :
    metric.metric.tensor.tensor point
        (regularFrameSmoothDualVector period hPeriod metric index point)
        (metric.frame frameIndex point) =
      if index = frameIndex then 1 else 0 := by
  rw [regularFrameSmoothDualVector_metric_pairing,
    regularFrameDualCovector_frame]

/-- Raised weighted curvature coefficient in the regular coframe. -/
def regularFrameWeightedGlobalGaugeCurvatureRaisedCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    regularFrameWeightedGlobalGaugeCurvatureTensor period hPeriod metric
      potential component point
        (regularFrameSmoothDualVector period hPeriod metric first point)
        (regularFrameSmoothDualVector period hPeriod metric second point)
  contMDiff_toFun := by
    have hApplied :=
      (regularFrameWeightedGlobalGaugeCurvatureTensor period hPeriod metric
        potential component).contMDiff.clm_bundle_apply₂
          (regularFrameSmoothDualVector period hPeriod metric first).contMDiff
          (regularFrameSmoothDualVector period hPeriod metric second).contMDiff
    intro point
    have hAppliedAt := hApplied point
    rw [Bundle.contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt

/-- One smooth regular-frame coefficient of the gauge variation. -/
def regularFrameGaugeVariationCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (index : Fin 4) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    variation.toFun component point (metric.frame index point)
  contMDiff_toFun :=
    (variation.contMDiff_eval component).comp (metric.frame index).contMDiff

/-- Contravariant Maxwell excitation contracted with the gauge variation and
densitized relative to the canonical quotient volume. -/
def regularFrameCanonicalMaxwellBoundaryCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (first : Fin 4) : SmoothQuotientField period hPeriod Real :=
  smoothScalarFieldMul period hPeriod
    (globalSmoothMetricVolumeRatio period hPeriod metric.metric)
    (∑ component : Fin 2, ∑ second : Fin 4,
      smoothScalarFieldMul period hPeriod
        (regularFrameWeightedGlobalGaugeCurvatureRaisedCoefficient period
          hPeriod metric potential component first second)
        (regularFrameGaugeVariationCoefficient period hPeriod metric variation
          component second))

@[simp]
theorem regularFrameCanonicalMaxwellBoundaryCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (first : Fin 4) (point : EffectiveQuotient period hPeriod) :
    regularFrameCanonicalMaxwellBoundaryCoefficient period hPeriod metric
        potential variation first point =
      globalMetricVolumeRatio period hPeriod metric.metric point *
        ∑ component : Fin 2, ∑ second : Fin 4,
          regularFrameWeightedGlobalGaugeCurvatureTensor period hPeriod metric
              potential component point
              (regularFrameSmoothDualVector period hPeriod metric first point)
              (regularFrameSmoothDualVector period hPeriod metric second point) *
            variation.toFun component point (metric.frame second point) := by
  change globalMetricVolumeRatio period hPeriod metric.metric point *
      (∑ component : Fin 2, ∑ second : Fin 4,
        regularFrameWeightedGlobalGaugeCurvatureTensor period hPeriod metric
            potential component point
            (regularFrameSmoothDualVector period hPeriod metric first point)
            (regularFrameSmoothDualVector period hPeriod metric second point) *
          variation.toFun component point (metric.frame second point)) = _
  rfl

/-- The complete Maxwell integration-by-parts current as a genuine smooth
tangent field. -/
def regularFrameCanonicalMaxwellBoundaryCurrent
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    SmoothTangentField period hPeriod where
  toFun := fun point =>
    ∑ first : Fin 4,
      regularFrameCanonicalMaxwellBoundaryCoefficient period hPeriod metric
          potential variation first point • metric.frame first point
  contMDiff_toFun := by
    apply ContMDiff.sum_section
    intro first _
    exact
      (regularFrameCanonicalMaxwellBoundaryCoefficient period hPeriod metric
        potential variation first).contMDiff_toFun.smul_section
          (metric.frame first).contMDiff_toFun

@[simp]
theorem regularFrameCanonicalMaxwellBoundaryCurrent_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric potential
        variation point =
      ∑ first : Fin 4,
        (globalMetricVolumeRatio period hPeriod metric.metric point *
          ∑ component : Fin 2, ∑ second : Fin 4,
            regularFrameWeightedGlobalGaugeCurvatureTensor period hPeriod metric
                potential component point
                (regularFrameSmoothDualVector period hPeriod metric first point)
                (regularFrameSmoothDualVector period hPeriod metric second point) *
              variation.toFun component point (metric.frame second point)) •
          metric.frame first point := by
  change (∑ first : Fin 4,
      regularFrameCanonicalMaxwellBoundaryCoefficient period hPeriod metric
          potential variation first point • metric.frame first point) = _
  apply Finset.sum_congr rfl
  intro first _
  rw [regularFrameCanonicalMaxwellBoundaryCoefficient_apply]

/-- Boundaryless canonical Stokes and its weak form for the actual densitized
Maxwell current. -/
theorem regularFrameCanonicalMaxwellBoundaryCurrent_stokes
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    Integrable
        (canonicalTenFlowDivergence period hPeriod metric
          (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric
            potential variation))
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) ∧
      (∫ point,
          canonicalTenFlowDivergence period hPeriod metric
            (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric
              potential variation) point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) = 0 ∧
      ∀ test : SmoothQuotientField period hPeriod Real,
        (∫ point,
            test point *
              canonicalTenFlowDivergence period hPeriod metric
                (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod
                  metric potential variation) point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
          -∫ point,
            mvfderiv coverModelWithCorners test.toFun point
              (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric
                potential variation point)
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  exact ⟨canonicalTenFlowDivergence_integrable period hPeriod metric _,
    canonicalTenFlowDivergence_integral_eq_zero period hPeriod metric _,
    canonicalTenFlowDivergence_weak_stokes period hPeriod metric _⟩

/-- Gate marker: the weighted Maxwell excitation and arbitrary smooth gauge
variation now determine a concrete global current covered by intrinsic Stokes. -/
theorem regular_frame_global_maxwell_boundary_current_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    Integrable
        (canonicalTenFlowDivergence period hPeriod metric
          (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric
            potential variation))
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) ∧
      (∫ point,
          canonicalTenFlowDivergence period hPeriod metric
            (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric
              potential variation) point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) = 0 := by
  exact ⟨(regularFrameCanonicalMaxwellBoundaryCurrent_stokes period hPeriod
      metric potential variation).1,
    (regularFrameCanonicalMaxwellBoundaryCurrent_stokes period hPeriod metric
      potential variation).2.1⟩

end
end P0EFTJanusProgramPRegularFrameGlobalMaxwellBoundaryCurrent4D
end JanusFormal
