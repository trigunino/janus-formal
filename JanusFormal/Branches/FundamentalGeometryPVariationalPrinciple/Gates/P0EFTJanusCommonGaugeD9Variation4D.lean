import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonLLActionVariation4D

namespace JanusFormal
namespace P0EFTJanusCommonGaugeD9Variation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
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

/-- Faithful gauge-only direction in the common Program-P variation space. -/
def gaugeOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    IndependentFieldVariation period hPeriod where
  metrics := zeroSmoothDiagonalMetricVariation period hPeriod
  matter := 0
  gauge := direction
  ghosts := 0
  auxiliaries := 0
  llAuxMetric := 0
  llMeasure := 0
  llField := 0

theorem gaugeOnlyIndependentVariation_injective :
    Function.Injective (gaugeOnlyIndependentVariation period hPeriod) := by
  intro first second hEqual
  exact congrArg IndependentFieldVariation.gauge hEqual

/-- D9 receives exactly the three spatial rows of the selected gauge column
restricted to the throat. -/
theorem d9GaugeOneForm_gaugeOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9GaugeOneForm period hPeriod
        (gaugeOnlyIndependentVariation period hPeriod direction)
        sector column point =
      { x := (match sector with | .plus => direction.1 | .minus => direction.2)
          (fixedThroatQuotientInclusion period hPeriod point) (1, column)
        y := (match sector with | .plus => direction.1 | .minus => direction.2)
          (fixedThroatQuotientInclusion period hPeriod point) (2, column)
        z := (match sector with | .plus => direction.1 | .minus => direction.2)
          (fixedThroatQuotientInclusion period hPeriod point) (3, column) } := by
  cases sector <;> rfl

theorem d9MatterCoefficient_gaugeOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber)
    (sector : Sector)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MatterCoefficient period hPeriod
        (gaugeOnlyIndependentVariation period hPeriod direction) sector point = 0 := by
  cases sector <;> rfl

theorem d9U1Ghost_gaugeOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9U1Ghost period hPeriod
        (gaugeOnlyIndependentVariation period hPeriod direction)
        sector column point = 0 := by
  cases sector <;> rfl

theorem d9MetricPerturbation_gaugeOnlyIndependentVariation
    (fields : IndependentFields period hPeriod)
    (direction : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber)
    (sector : Sector)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MetricPerturbation period hPeriod fields
        (gaugeOnlyIndependentVariation period hPeriod direction)
        sector point = zeroSymmetric := by
  have hZero : ∀ index : Fin 4,
      (0 : SmoothQuotientField period hPeriod (Fin 4 → Real))
          (fixedThroatQuotientInclusion period hPeriod point) index = 0 :=
    fun _ => rfl
  cases sector <;> ext <;>
    simp [d9MetricPerturbation, selectedMetricVelocity,
      metricMagnitudeVelocityAt, gaugeOnlyIndependentVariation,
      zeroSmoothDiagonalMetricVariation, lorentzMetric, zeroSymmetric,
      selectSector, hZero]

end

end P0EFTJanusCommonGaugeD9Variation4D
end JanusFormal
