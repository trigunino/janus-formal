import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMatterActionMassSignObstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D

/-! # Integrated mass-sign obstruction between the two matter actions -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusMatterActionMassSignIntegratedObstruction4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D
open P0EFTJanusMappingTorusMatterActionMassSignObstruction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Exact pointwise defect left by the opposite massive-term conventions. -/
def matterActionMassSignDefect
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real) (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  metricVolumeDensity period hPeriod metric point (frame point) *
    (massSquared * field point ^ 2)

/-- Under the explicit geometric bridge, the difference of the two global
actions is exactly the integral of the mass-sign defect. -/
theorem globalHolonomicScalarAction_sub_measuredGeneralLorentzAction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (massSquared : Real) (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (hVolume : ∀ point,
      diagonalMetricVolumeDensity period hPeriod magnitude point =
        metricVolumeDensity period hPeriod metric point (frame point))
    (hKinetic : ∀ point,
      diagonalHolonomicKineticDensity period hPeriod magnitude field point =
        1 / 2 * inverseMetricContraction period hPeriod metric point
          (scalarDifferential period hPeriod field point)
          (scalarDifferential period hPeriod field point))
    (hGlobal : Integrable
      (globalHolonomicScalarDensity period hPeriod massSquared magnitude field)
      measure)
    (hCovariant : Integrable
      (generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
        field frame) measure) :
    globalHolonomicScalarAction period hPeriod massSquared magnitude field
          measure -
        measuredGeneralLorentzHolonomicScalarAction period hPeriod metric
          massSquared field frame measure =
      ∫ point, matterActionMassSignDefect period hPeriod metric massSquared
        field frame point ∂measure := by
  unfold globalHolonomicScalarAction measuredGeneralLorentzHolonomicScalarAction
  rw [← integral_sub hGlobal hCovariant]
  apply integral_congr_ae
  filter_upwards with point
  exact globalHolonomicScalarDensity_sub_holonomicScalarDensity period hPeriod
    metric magnitude massSquared field point (frame point) (hVolume point)
      (hKinetic point)

/-- Consequently, equality of the two actions is equivalent to vanishing of
the integrated defect. -/
theorem globalHolonomicScalarAction_eq_measuredGeneralLorentzAction_iff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (massSquared : Real) (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (hVolume : ∀ point,
      diagonalMetricVolumeDensity period hPeriod magnitude point =
        metricVolumeDensity period hPeriod metric point (frame point))
    (hKinetic : ∀ point,
      diagonalHolonomicKineticDensity period hPeriod magnitude field point =
        1 / 2 * inverseMetricContraction period hPeriod metric point
          (scalarDifferential period hPeriod field point)
          (scalarDifferential period hPeriod field point))
    (hGlobal : Integrable
      (globalHolonomicScalarDensity period hPeriod massSquared magnitude field)
      measure)
    (hCovariant : Integrable
      (generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
        field frame) measure) :
    globalHolonomicScalarAction period hPeriod massSquared magnitude field
          measure =
        measuredGeneralLorentzHolonomicScalarAction period hPeriod metric
          massSquared field frame measure ↔
      (∫ point, matterActionMassSignDefect period hPeriod metric massSquared
        field frame point ∂measure) = 0 := by
  have hDifference :=
    globalHolonomicScalarAction_sub_measuredGeneralLorentzAction period hPeriod
      metric magnitude massSquared field frame measure hVolume hKinetic hGlobal
      hCovariant
  constructor <;> intro h <;> linarith

/-- A nonzero integrated defect excludes the desired action identification. -/
theorem globalHolonomicScalarAction_ne_measuredGeneralLorentzAction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (massSquared : Real) (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (hVolume : ∀ point,
      diagonalMetricVolumeDensity period hPeriod magnitude point =
        metricVolumeDensity period hPeriod metric point (frame point))
    (hKinetic : ∀ point,
      diagonalHolonomicKineticDensity period hPeriod magnitude field point =
        1 / 2 * inverseMetricContraction period hPeriod metric point
          (scalarDifferential period hPeriod field point)
          (scalarDifferential period hPeriod field point))
    (hGlobal : Integrable
      (globalHolonomicScalarDensity period hPeriod massSquared magnitude field)
      measure)
    (hCovariant : Integrable
      (generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
        field frame) measure)
    (hDefect : (∫ point, matterActionMassSignDefect period hPeriod metric
      massSquared field frame point ∂measure) ≠ 0) :
    globalHolonomicScalarAction period hPeriod massSquared magnitude field
          measure ≠
      measuredGeneralLorentzHolonomicScalarAction period hPeriod metric
        massSquared field frame measure := by
  intro hEqual
  exact hDefect
    ((globalHolonomicScalarAction_eq_measuredGeneralLorentzAction_iff period
      hPeriod metric magnitude massSquared field frame measure hVolume hKinetic
      hGlobal hCovariant).mp hEqual)

end
end P0EFTJanusMappingTorusMatterActionMassSignIntegratedObstruction4D
end JanusFormal
