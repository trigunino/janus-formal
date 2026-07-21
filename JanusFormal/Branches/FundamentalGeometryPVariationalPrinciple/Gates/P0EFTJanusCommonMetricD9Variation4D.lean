import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonGaugeD9Variation4D

namespace JanusFormal
namespace P0EFTJanusCommonMetricD9Variation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGlobalDiagonalLorentzRoot4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Faithful metric-only direction in the common Program-P variation space. -/
def metricOnlyIndependentVariation
    (direction : SmoothDiagonalMetricVariation period hPeriod) :
    IndependentFieldVariation period hPeriod where
  metrics := direction
  matter := 0
  gauge := 0
  ghosts := 0
  auxiliaries := 0
  llAuxMetric := 0
  llMeasure := 0
  llField := 0

theorem metricOnlyIndependentVariation_injective :
    Function.Injective (metricOnlyIndependentVariation period hPeriod) := by
  intro first second hEqual
  exact congrArg IndependentFieldVariation.metrics hEqual

/-- D9 sees exactly the three spatial diagonal velocities of the selected
metric sector. -/
theorem d9MetricPerturbation_metricOnlyIndependentVariation
    (fields : IndependentFields period hPeriod)
    (direction : SmoothDiagonalMetricVariation period hPeriod)
    (sector : Sector)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MetricPerturbation period hPeriod fields
        (metricOnlyIndependentVariation period hPeriod direction) sector point =
      { xx := (selectSector sector
            (metricMagnitudeVelocityAt period hPeriod fields
              (metricOnlyIndependentVariation period hPeriod direction) 0
              (fixedThroatQuotientInclusion period hPeriod point))) 1
        yy := (selectSector sector
            (metricMagnitudeVelocityAt period hPeriod fields
              (metricOnlyIndependentVariation period hPeriod direction) 0
              (fixedThroatQuotientInclusion period hPeriod point))) 2
        zz := (selectSector sector
            (metricMagnitudeVelocityAt period hPeriod fields
              (metricOnlyIndependentVariation period hPeriod direction) 0
              (fixedThroatQuotientInclusion period hPeriod point))) 3
        xy := 0
        xz := 0
        yz := 0 } := by
  cases sector <;> ext <;>
    simp [d9MetricPerturbation, selectedMetricVelocity, lorentzMetric,
      selectSector, signature]

theorem d9GaugeOneForm_metricOnlyIndependentVariation
    (direction : SmoothDiagonalMetricVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9GaugeOneForm period hPeriod
        (metricOnlyIndependentVariation period hPeriod direction)
        sector column point = zeroTangent := by
  cases sector <;> ext <;> rfl

theorem d9U1Ghost_metricOnlyIndependentVariation
    (direction : SmoothDiagonalMetricVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9U1Ghost period hPeriod
        (metricOnlyIndependentVariation period hPeriod direction)
        sector column point = 0 := by
  cases sector <;> rfl

theorem d9MatterCoefficient_metricOnlyIndependentVariation
    (direction : SmoothDiagonalMetricVariation period hPeriod)
    (sector : Sector)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MatterCoefficient period hPeriod
        (metricOnlyIndependentVariation period hPeriod direction) sector point = 0 := by
  cases sector <;> rfl

end

end P0EFTJanusCommonMetricD9Variation4D
end JanusFormal
