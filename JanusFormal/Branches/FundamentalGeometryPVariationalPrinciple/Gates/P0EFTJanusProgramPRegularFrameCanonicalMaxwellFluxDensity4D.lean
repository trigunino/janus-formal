import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalMaxwellElementaryDivergence4D

/-! # Metric-density and skewness of the canonical Maxwell flux -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalMaxwellFluxDensity4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D
open P0EFTJanusProgramPRegularFrameMaxwellFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularFrameGlobalMaxwellBoundaryCurrent4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellElementaryFlux4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Unweighted curvature with both regular-frame coindices raised. -/
def regularFrameGlobalGaugeCurvatureRaisedCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    regularGlobalGaugeCurvatureTensor period hPeriod metric potential component
      point
        (regularFrameSmoothDualVector period hPeriod metric first point)
        (regularFrameSmoothDualVector period hPeriod metric second point)
  contMDiff_toFun := by
    have hApplied :=
      (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
        component).contMDiff.clm_bundle_apply₂
          (regularFrameSmoothDualVector period hPeriod metric first).contMDiff
          (regularFrameSmoothDualVector period hPeriod metric second).contMDiff
    intro point
    have hAppliedAt := hApplied point
    rw [Bundle.contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt

/-- The reconstructed global curvature tensor is alternating. -/
theorem regularGlobalGaugeCurvatureTensor_swap
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (point : EffectiveQuotient period hPeriod)
    (left right : TangentSpace coverModelWithCorners point) :
    regularGlobalGaugeCurvatureTensor period hPeriod metric potential component
        point left right =
      -regularGlobalGaugeCurvatureTensor period hPeriod metric potential
        component point right left := by
  rw [regularGlobalGaugeCurvatureTensor_apply,
    regularGlobalGaugeCurvatureTensor_apply]
  rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro second _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro first _
  have hSwap := congrArg
    (fun field : SmoothQuotientField period hPeriod Real => field point)
    (regularFrameGaugeCurvatureCoefficient_swap period hPeriod metric potential
      component first second)
  change
    regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
        component first second point =
      -regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
        component second first point at hSwap
  have hSwapPoint :
      regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
          component first second point =
        -regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
          component second first point := by
    exact hSwap
  rw [hSwapPoint]
  ring

theorem regularFrameGlobalGaugeCurvatureRaisedCoefficient_swap
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4) :
    regularFrameGlobalGaugeCurvatureRaisedCoefficient period hPeriod metric
        potential component second first =
      -regularFrameGlobalGaugeCurvatureRaisedCoefficient period hPeriod metric
        potential component first second := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact regularGlobalGaugeCurvatureTensor_swap period hPeriod metric potential
    component point
      (regularFrameSmoothDualVector period hPeriod metric second point)
      (regularFrameSmoothDualVector period hPeriod metric first point)

/-- Canonical densitization cancels the frame-action weight exactly. -/
theorem regularFrameCanonicalMaxwellFluxCoefficient_eq_volume_mul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric potential
        component first second point =
      metric.volume point *
        regularFrameGlobalGaugeCurvatureRaisedCoefficient period hPeriod metric
          potential component first second point := by
  change
    globalMetricVolumeRatio period hPeriod metric.metric point *
        (regularFrameMaxwellActionWeight period hPeriod metric point *
          regularGlobalGaugeCurvatureTensor period hPeriod metric potential
            component point
              (regularFrameSmoothDualVector period hPeriod metric first point)
              (regularFrameSmoothDualVector period hPeriod metric second point)) =
      metric.volume point *
        regularGlobalGaugeCurvatureTensor period hPeriod metric potential
          component point
            (regularFrameSmoothDualVector period hPeriod metric first point)
            (regularFrameSmoothDualVector period hPeriod metric second point)
  rw [← mul_assoc,
    regularFrameMaxwellActionWeight_mul_volumeRatio period hPeriod metric point]

theorem regularFrameCanonicalMaxwellFluxCoefficient_swap
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4) :
    regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric potential
        component second first =
      -regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
        potential component first second := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change
    regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric potential
        component second first point =
      -regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
        potential component first second point
  rw [regularFrameCanonicalMaxwellFluxCoefficient_eq_volume_mul,
    regularFrameCanonicalMaxwellFluxCoefficient_eq_volume_mul]
  have hSwap := congrArg
    (fun field : SmoothQuotientField period hPeriod Real => field point)
    (regularFrameGlobalGaugeCurvatureRaisedCoefficient_swap period hPeriod
      metric potential component first second)
  change
    regularFrameGlobalGaugeCurvatureRaisedCoefficient period hPeriod metric
        potential component second first point =
      -regularFrameGlobalGaugeCurvatureRaisedCoefficient period hPeriod metric
        potential component first second point at hSwap
  have hSwapPoint :
      regularFrameGlobalGaugeCurvatureRaisedCoefficient period hPeriod metric
          potential component second first point =
        -regularFrameGlobalGaugeCurvatureRaisedCoefficient period hPeriod metric
          potential component first second point := by
    exact hSwap
  rw [hSwapPoint]
  ring

/-- Gate marker: every elementary canonical flux is the authentic metric
volume density times an alternating raised Maxwell curvature coefficient. -/
theorem regular_frame_canonical_maxwell_flux_density_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric potential
        component first second point =
      metric.volume point *
        regularFrameGlobalGaugeCurvatureRaisedCoefficient period hPeriod metric
          potential component first second point ∧
    regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric potential
        component second first point =
      -regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
        potential component first second point :=
  ⟨regularFrameCanonicalMaxwellFluxCoefficient_eq_volume_mul period hPeriod
      metric potential component first second point,
    by
      have hSwap := congrArg
        (fun field : SmoothQuotientField period hPeriod Real => field point)
        (regularFrameCanonicalMaxwellFluxCoefficient_swap period hPeriod metric
          potential component first second)
      change
        regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
            potential component second first point =
          -regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
            potential component first second point at hSwap
      exact hSwap⟩

end
end P0EFTJanusProgramPRegularFrameCanonicalMaxwellFluxDensity4D
end JanusFormal
