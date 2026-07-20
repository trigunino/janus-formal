import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMatterMultipletMassSignIntegratedObstruction4D

/-! # No cancellation between nonnegative matter mass-sign defects -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusMatterMultipletMassSignNoCancellation4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusGlobalMatterMultipletDiagonalDiffeomorphismNoether4D
open P0EFTJanusMappingTorusMatterActionMassSignIntegratedObstruction4D
open P0EFTJanusMappingTorusMatterMultipletMassSignIntegratedObstruction4D

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

theorem matterActionMassSignDefect_nonneg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real) (hMass : 0 ≤ massSquared)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    0 ≤ matterActionMassSignDefect period hPeriod metric massSquared field frame
      point := by
  unfold matterActionMassSignDefect metricVolumeDensity
  exact mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg hMass (sq_nonneg _))

theorem matterActionMassSignDefect_integral_nonneg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real) (hMass : 0 ≤ massSquared)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    0 ≤ ∫ point, matterActionMassSignDefect period hPeriod metric massSquared
      field frame point ∂measure :=
  integral_nonneg fun point =>
    matterActionMassSignDefect_nonneg period hPeriod metric massSquared hMass
      field frame point

theorem matterMultipletMassSignDefectIntegral_nonneg
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod)
    (hMass : ∀ index, 0 ≤ configuration.massSquared index) :
    0 ≤ matterMultipletMassSignDefectIntegral period hPeriod configuration := by
  unfold matterMultipletMassSignDefectIntegral
  exact Finset.sum_nonneg fun index _ =>
    matterActionMassSignDefect_integral_nonneg period hPeriod
      configuration.metric (configuration.massSquared index) (hMass index)
      (configuration.fields index) configuration.frame configuration.measure

/-- For physical nonnegative mass-squared parameters, the total defect
vanishes exactly when every component defect integral vanishes. -/
theorem matterMultipletMassSignDefectIntegral_eq_zero_iff
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod)
    (hMass : ∀ index, 0 ≤ configuration.massSquared index) :
    matterMultipletMassSignDefectIntegral period hPeriod configuration = 0 ↔
      ∀ index : MatterComponentIndex,
        (∫ point, matterActionMassSignDefect period hPeriod configuration.metric
          (configuration.massSquared index) (configuration.fields index)
          configuration.frame point ∂configuration.measure) = 0 := by
  unfold matterMultipletMassSignDefectIntegral
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · simp
  · intro index _
    exact matterActionMassSignDefect_integral_nonneg period hPeriod
      configuration.metric (configuration.massSquared index) (hMass index)
      (configuration.fields index) configuration.frame configuration.measure

theorem matterMultipletMassSignDefectIntegral_ne_zero_of_exists
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod)
    (hMass : ∀ index, 0 ≤ configuration.massSquared index)
    (hExists : ∃ index : MatterComponentIndex,
      (∫ point, matterActionMassSignDefect period hPeriod configuration.metric
        (configuration.massSquared index) (configuration.fields index)
        configuration.frame point ∂configuration.measure) ≠ 0) :
    matterMultipletMassSignDefectIntegral period hPeriod configuration ≠ 0 := by
  intro hZero
  obtain ⟨index, hIndex⟩ := hExists
  exact hIndex
    ((matterMultipletMassSignDefectIntegral_eq_zero_iff period hPeriod
      configuration hMass).mp hZero index)

end
end P0EFTJanusMappingTorusMatterMultipletMassSignNoCancellation4D
end JanusFormal
