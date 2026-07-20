import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMatterActionMassSignIntegratedObstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalMatterMultipletDiagonalDiffeomorphismNoether4D

/-! # Integrated mass-sign obstruction for the eight-field matter multiplet -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusMatterMultipletMassSignIntegratedObstruction4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusMappingTorusGlobalMatterMultipletDiagonalDiffeomorphismNoether4D
open P0EFTJanusMappingTorusMatterActionMassSignIntegratedObstruction4D

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

/-- Sum of the eight integrated massive-sign defects on the common geometry. -/
def matterMultipletMassSignDefectIntegral
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod) :
    Real :=
  ∑ index : MatterComponentIndex,
    ∫ point, matterActionMassSignDefect period hPeriod configuration.metric
      (configuration.massSquared index) (configuration.fields index)
      configuration.frame point ∂configuration.measure

/-- Under componentwise metric bridges, the difference between the actual
eight-field Euler action and the covariant Noether action is exactly the sum
of the integrated mass-sign defects. -/
theorem globalMatterMultipletAction_sub_sameConfigurationAction
    (data : MatterMultipletActionData period hPeriod)
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod)
    (hMass : ∀ index, (data index).massSquared =
      configuration.massSquared index)
    (hMeasure : ∀ index, (data index).measure = configuration.measure)
    (hVolume : ∀ index point,
      diagonalMetricVolumeDensity period hPeriod (data index).magnitude point =
        metricVolumeDensity period hPeriod configuration.metric point
          (configuration.frame point))
    (hKinetic : ∀ index point,
      diagonalHolonomicKineticDensity period hPeriod (data index).magnitude
          (configuration.fields index) point =
        1 / 2 * inverseMetricContraction period hPeriod configuration.metric
          point
          (scalarDifferential period hPeriod (configuration.fields index) point)
          (scalarDifferential period hPeriod (configuration.fields index) point))
    (hGlobal : ∀ index, Integrable
      (globalHolonomicScalarDensity period hPeriod
        (configuration.massSquared index) (data index).magnitude
        (configuration.fields index)) configuration.measure)
    (hCovariant : ∀ index, Integrable
      (generalLorentzHolonomicScalarDensity period hPeriod configuration.metric
        (configuration.massSquared index) (configuration.fields index)
        configuration.frame) configuration.measure) :
    globalMatterMultipletAction period hPeriod data configuration.fields -
        sameConfigurationGeneralLorentzMatterAction period hPeriod
          configuration =
      matterMultipletMassSignDefectIntegral period hPeriod configuration := by
  unfold globalMatterMultipletAction
    sameConfigurationGeneralLorentzMatterAction
    matterMultipletMassSignDefectIntegral
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index _
  change
    globalHolonomicScalarAction period hPeriod (data index).massSquared
          (data index).magnitude (configuration.fields index)
          (data index).measure -
        measuredGeneralLorentzHolonomicScalarAction period hPeriod
          configuration.metric (configuration.massSquared index)
          (configuration.fields index) configuration.frame
          configuration.measure = _
  rw [hMass index, hMeasure index]
  exact globalHolonomicScalarAction_sub_measuredGeneralLorentzAction period
    hPeriod configuration.metric (data index).magnitude
      (configuration.massSquared index) (configuration.fields index)
      configuration.frame configuration.measure (hVolume index)
      (hKinetic index) (hGlobal index) (hCovariant index)

theorem globalMatterMultipletAction_eq_sameConfigurationAction_iff
    (data : MatterMultipletActionData period hPeriod)
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod)
    (hMass : ∀ index, (data index).massSquared =
      configuration.massSquared index)
    (hMeasure : ∀ index, (data index).measure = configuration.measure)
    (hVolume : ∀ index point,
      diagonalMetricVolumeDensity period hPeriod (data index).magnitude point =
        metricVolumeDensity period hPeriod configuration.metric point
          (configuration.frame point))
    (hKinetic : ∀ index point,
      diagonalHolonomicKineticDensity period hPeriod (data index).magnitude
          (configuration.fields index) point =
        1 / 2 * inverseMetricContraction period hPeriod configuration.metric
          point
          (scalarDifferential period hPeriod (configuration.fields index) point)
          (scalarDifferential period hPeriod (configuration.fields index) point))
    (hGlobal : ∀ index, Integrable
      (globalHolonomicScalarDensity period hPeriod
        (configuration.massSquared index) (data index).magnitude
        (configuration.fields index)) configuration.measure)
    (hCovariant : ∀ index, Integrable
      (generalLorentzHolonomicScalarDensity period hPeriod configuration.metric
        (configuration.massSquared index) (configuration.fields index)
        configuration.frame) configuration.measure) :
    globalMatterMultipletAction period hPeriod data configuration.fields =
        sameConfigurationGeneralLorentzMatterAction period hPeriod
          configuration ↔
      matterMultipletMassSignDefectIntegral period hPeriod configuration = 0 := by
  have hDifference :=
    globalMatterMultipletAction_sub_sameConfigurationAction period hPeriod data
      configuration hMass hMeasure hVolume hKinetic hGlobal hCovariant
  constructor <;> intro h <;> linarith

theorem globalMatterMultipletAction_ne_sameConfigurationAction
    (data : MatterMultipletActionData period hPeriod)
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod)
    (hMass : ∀ index, (data index).massSquared =
      configuration.massSquared index)
    (hMeasure : ∀ index, (data index).measure = configuration.measure)
    (hVolume : ∀ index point,
      diagonalMetricVolumeDensity period hPeriod (data index).magnitude point =
        metricVolumeDensity period hPeriod configuration.metric point
          (configuration.frame point))
    (hKinetic : ∀ index point,
      diagonalHolonomicKineticDensity period hPeriod (data index).magnitude
          (configuration.fields index) point =
        1 / 2 * inverseMetricContraction period hPeriod configuration.metric
          point
          (scalarDifferential period hPeriod (configuration.fields index) point)
          (scalarDifferential period hPeriod (configuration.fields index) point))
    (hGlobal : ∀ index, Integrable
      (globalHolonomicScalarDensity period hPeriod
        (configuration.massSquared index) (data index).magnitude
        (configuration.fields index)) configuration.measure)
    (hCovariant : ∀ index, Integrable
      (generalLorentzHolonomicScalarDensity period hPeriod configuration.metric
        (configuration.massSquared index) (configuration.fields index)
        configuration.frame) configuration.measure)
    (hDefect : matterMultipletMassSignDefectIntegral period hPeriod
      configuration ≠ 0) :
    globalMatterMultipletAction period hPeriod data configuration.fields ≠
      sameConfigurationGeneralLorentzMatterAction period hPeriod
        configuration := by
  intro hEqual
  exact hDefect
    ((globalMatterMultipletAction_eq_sameConfigurationAction_iff period hPeriod
      data configuration hMass hMeasure hVolume hKinetic hGlobal hCovariant).mp
        hEqual)

end
end P0EFTJanusMappingTorusMatterMultipletMassSignIntegratedObstruction4D
end JanusFormal
