import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D

/-! # Mass-sign obstruction between the two matter density conventions -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusMatterActionMassSignObstruction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Once volume and kinetic terms are identified, the two existing scalar
density conventions differ exactly by the full massive term. -/
theorem globalHolonomicScalarDensity_sub_holonomicScalarDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentSpace coverModelWithCorners point)
    (hVolume : diagonalMetricVolumeDensity period hPeriod magnitude point =
      metricVolumeDensity period hPeriod metric point frame)
    (hKinetic : diagonalHolonomicKineticDensity period hPeriod magnitude field
        point =
      1 / 2 * inverseMetricContraction period hPeriod metric point
        (scalarDifferential period hPeriod field point)
        (scalarDifferential period hPeriod field point)) :
    globalHolonomicScalarDensity period hPeriod massSquared magnitude field
          point -
        holonomicScalarDensity period hPeriod metric massSquared field point
          frame =
      metricVolumeDensity period hPeriod metric point frame *
        (massSquared * field point ^ 2) := by
  rw [globalHolonomicScalarDensity, holonomicScalarDensity, hVolume, hKinetic]
  ring

/-- With nonzero metric volume, equality of the two densities is equivalent
to vanishing of the massive field contribution. -/
theorem globalHolonomicScalarDensity_eq_holonomicScalarDensity_iff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentSpace coverModelWithCorners point)
    (hVolume : diagonalMetricVolumeDensity period hPeriod magnitude point =
      metricVolumeDensity period hPeriod metric point frame)
    (hKinetic : diagonalHolonomicKineticDensity period hPeriod magnitude field
        point =
      1 / 2 * inverseMetricContraction period hPeriod metric point
        (scalarDifferential period hPeriod field point)
        (scalarDifferential period hPeriod field point))
    (hVolumeNe : metricVolumeDensity period hPeriod metric point frame ≠ 0) :
    globalHolonomicScalarDensity period hPeriod massSquared magnitude field
          point =
        holonomicScalarDensity period hPeriod metric massSquared field point
          frame ↔
      massSquared * field point ^ 2 = 0 := by
  have hDifference :=
    globalHolonomicScalarDensity_sub_holonomicScalarDensity period hPeriod
      metric magnitude massSquared field point frame hVolume hKinetic
  constructor
  · intro hEqual
    have hZero : metricVolumeDensity period hPeriod metric point frame *
        (massSquared * field point ^ 2) = 0 := by
      rw [← hDifference, hEqual, sub_self]
    exact (mul_eq_zero.mp hZero).resolve_left hVolumeNe
  · intro hMass
    rw [hMass, mul_zero] at hDifference
    linarith

/-- Hence a nonzero mass and nonzero field value formally obstruct the
proposed same-parameter density identification. -/
theorem globalHolonomicScalarDensity_ne_holonomicScalarDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentSpace coverModelWithCorners point)
    (hVolume : diagonalMetricVolumeDensity period hPeriod magnitude point =
      metricVolumeDensity period hPeriod metric point frame)
    (hKinetic : diagonalHolonomicKineticDensity period hPeriod magnitude field
        point =
      1 / 2 * inverseMetricContraction period hPeriod metric point
        (scalarDifferential period hPeriod field point)
        (scalarDifferential period hPeriod field point))
    (hVolumeNe : metricVolumeDensity period hPeriod metric point frame ≠ 0)
    (hMass : massSquared ≠ 0) (hField : field point ≠ 0) :
    globalHolonomicScalarDensity period hPeriod massSquared magnitude field
          point ≠
      holonomicScalarDensity period hPeriod metric massSquared field point
        frame := by
  intro hEqual
  have hZero :=
    (globalHolonomicScalarDensity_eq_holonomicScalarDensity_iff period hPeriod
      metric magnitude massSquared field point frame hVolume hKinetic
      hVolumeNe).mp hEqual
  exact (mul_ne_zero hMass (pow_ne_zero 2 hField)) hZero

end
end P0EFTJanusMappingTorusMatterActionMassSignObstruction4D
end JanusFormal
