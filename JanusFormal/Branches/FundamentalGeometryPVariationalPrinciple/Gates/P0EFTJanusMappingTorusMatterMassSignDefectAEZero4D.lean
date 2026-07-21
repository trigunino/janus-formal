import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMatterMultipletMassSignNoCancellation4D

/-! # Almost-everywhere zero criterion for the matter mass-sign defect -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusMatterMassSignDefectAEZero4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusMatterActionMassSignIntegratedObstruction4D
open P0EFTJanusMappingTorusMatterMultipletMassSignNoCancellation4D

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

theorem matterActionMassSignDefect_integral_eq_zero_iff_ae
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real) (hMass : 0 ≤ massSquared)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (hIntegrable : Integrable
      (matterActionMassSignDefect period hPeriod metric massSquared field frame)
      measure) :
    (∫ point, matterActionMassSignDefect period hPeriod metric massSquared field
        frame point ∂measure) = 0 ↔
      matterActionMassSignDefect period hPeriod metric massSquared field frame
        =ᵐ[measure] 0 :=
  integral_eq_zero_iff_of_nonneg
    (fun point => matterActionMassSignDefect_nonneg period hPeriod metric
      massSquared hMass field frame point) hIntegrable

theorem matterActionMassSignDefect_ae_zero_iff_field_ae_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real) (hMass : 0 < massSquared)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (hVolume : ∀ᵐ point ∂measure,
      0 < metricVolumeDensity period hPeriod metric point (frame point)) :
    matterActionMassSignDefect period hPeriod metric massSquared field frame
        =ᵐ[measure] 0 ↔
      field =ᵐ[measure] 0 := by
  constructor
  · intro hDefect
    filter_upwards [hDefect, hVolume] with point hPoint hVolumePoint
    change metricVolumeDensity period hPeriod metric point (frame point) *
        (massSquared * field point ^ 2) = 0 at hPoint
    have hMassTerm : massSquared * field point ^ 2 = 0 :=
      (mul_eq_zero.mp hPoint).resolve_left (ne_of_gt hVolumePoint)
    have hSquare : field point ^ 2 = 0 :=
      (mul_eq_zero.mp hMassTerm).resolve_left (ne_of_gt hMass)
    change field point = 0
    exact (pow_eq_zero_iff (by norm_num : (2 : Nat) ≠ 0)).mp hSquare
  · intro hField
    filter_upwards [hField] with point hPoint
    simp [matterActionMassSignDefect, hPoint]

/-- With positive mass and positive volume almost everywhere, a nonzero field
class forces a strictly positive integrated defect. -/
theorem matterActionMassSignDefect_integral_pos
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real) (hMass : 0 < massSquared)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (hVolume : ∀ᵐ point ∂measure,
      0 < metricVolumeDensity period hPeriod metric point (frame point))
    (hIntegrable : Integrable
      (matterActionMassSignDefect period hPeriod metric massSquared field frame)
      measure)
    (hField : ¬ field =ᵐ[measure] 0) :
    0 < ∫ point, matterActionMassSignDefect period hPeriod metric massSquared
      field frame point ∂measure := by
  have hNonneg := matterActionMassSignDefect_integral_nonneg period hPeriod
    metric massSquared (le_of_lt hMass) field frame measure
  have hNe : (∫ point, matterActionMassSignDefect period hPeriod metric
      massSquared field frame point ∂measure) ≠ 0 := by
    intro hZero
    apply hField
    exact (matterActionMassSignDefect_ae_zero_iff_field_ae_zero period hPeriod
      metric massSquared hMass field frame measure hVolume).mp
        ((matterActionMassSignDefect_integral_eq_zero_iff_ae period hPeriod
          metric massSquared (le_of_lt hMass) field frame measure
          hIntegrable).mp hZero)
  exact lt_of_le_of_ne hNonneg (Ne.symm hNe)

end
end P0EFTJanusMappingTorusMatterMassSignDefectAEZero4D
end JanusFormal
