import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMatterMassSignDefectAEZero4D

/-! # Massive nonzero-field no-go for the two eight-field matter actions -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusMatterMultipletMassiveFieldNoGo4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusMappingTorusGlobalMatterMultipletDiagonalDiffeomorphismNoether4D
open P0EFTJanusMappingTorusMatterActionMassSignIntegratedObstruction4D
open P0EFTJanusMappingTorusMatterMultipletMassSignIntegratedObstruction4D
open P0EFTJanusMappingTorusMatterMultipletMassSignNoCancellation4D
open P0EFTJanusMappingTorusMatterMassSignDefectAEZero4D

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

/-- If one positive-mass component is nonzero almost everywhere as a measure
class, then the Euler action and the covariant Noether action cannot coincide
under the proposed same-parameter geometric bridge. -/
theorem globalMatterMultipletAction_ne_sameConfigurationAction_of_massive_field
    (data : MatterMultipletActionData period hPeriod)
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod)
    (hMass : ∀ index, (data index).massSquared =
      configuration.massSquared index)
    (hMeasure : ∀ index, (data index).measure = configuration.measure)
    (hVolumeBridge : ∀ index point,
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
    (hMassNonneg : ∀ index, 0 ≤ configuration.massSquared index)
    (witness : MatterComponentIndex)
    (hWitnessMass : 0 < configuration.massSquared witness)
    (hVolumePositive : ∀ᵐ point ∂configuration.measure,
      0 < metricVolumeDensity period hPeriod configuration.metric point
        (configuration.frame point))
    (hDefectIntegrable : Integrable
      (matterActionMassSignDefect period hPeriod configuration.metric
        (configuration.massSquared witness) (configuration.fields witness)
        configuration.frame) configuration.measure)
    (hField : ¬ configuration.fields witness =ᵐ[configuration.measure] 0) :
    globalMatterMultipletAction period hPeriod data configuration.fields ≠
      sameConfigurationGeneralLorentzMatterAction period hPeriod
        configuration := by
  have hWitnessPositive :
      0 < ∫ point, matterActionMassSignDefect period hPeriod
        configuration.metric (configuration.massSquared witness)
        (configuration.fields witness) configuration.frame point
        ∂configuration.measure :=
    matterActionMassSignDefect_integral_pos period hPeriod configuration.metric
      (configuration.massSquared witness) hWitnessMass
      (configuration.fields witness) configuration.frame configuration.measure
      hVolumePositive hDefectIntegrable hField
  have hTotalDefect :
      matterMultipletMassSignDefectIntegral period hPeriod configuration ≠ 0 :=
    matterMultipletMassSignDefectIntegral_ne_zero_of_exists period hPeriod
      configuration hMassNonneg ⟨witness, ne_of_gt hWitnessPositive⟩
  exact globalMatterMultipletAction_ne_sameConfigurationAction period hPeriod
    data configuration hMass hMeasure hVolumeBridge hKinetic hGlobal hCovariant
    hTotalDefect

end
end P0EFTJanusMappingTorusMatterMultipletMassiveFieldNoGo4D
end JanusFormal
