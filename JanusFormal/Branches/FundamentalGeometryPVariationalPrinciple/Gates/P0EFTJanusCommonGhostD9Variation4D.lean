import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonGaugeD9Variation4D

namespace JanusFormal
namespace P0EFTJanusCommonGhostD9Variation4D

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

/-- Faithful ghost-only direction in the common Program-P variation space. -/
def ghostOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod GhostFiber ×
      SmoothQuotientField period hPeriod GhostFiber) :
    IndependentFieldVariation period hPeriod where
  metrics := zeroSmoothDiagonalMetricVariation period hPeriod
  matter := 0
  gauge := 0
  ghosts := direction
  auxiliaries := 0
  llAuxMetric := 0
  llMeasure := 0
  llField := 0

theorem ghostOnlyIndependentVariation_injective :
    Function.Injective (ghostOnlyIndependentVariation period hPeriod) := by
  intro first second hEqual
  exact congrArg IndependentFieldVariation.ghosts hEqual

/-- D9 receives exactly the selected scalar component of the throat ghost. -/
theorem d9U1Ghost_ghostOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod GhostFiber ×
      SmoothQuotientField period hPeriod GhostFiber)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9U1Ghost period hPeriod
        (ghostOnlyIndependentVariation period hPeriod direction)
        sector column point =
      throatTrace period hPeriod GhostFiber
        (match sector with | .plus => direction.1 | .minus => direction.2) point column := by
  cases sector <;> rfl

theorem d9GaugeOneForm_ghostOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod GhostFiber ×
      SmoothQuotientField period hPeriod GhostFiber)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9GaugeOneForm period hPeriod
        (ghostOnlyIndependentVariation period hPeriod direction)
        sector column point = zeroTangent := by
  cases sector <;> ext <;> rfl

theorem d9MatterCoefficient_ghostOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod GhostFiber ×
      SmoothQuotientField period hPeriod GhostFiber)
    (sector : Sector)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MatterCoefficient period hPeriod
        (ghostOnlyIndependentVariation period hPeriod direction) sector point = 0 := by
  cases sector <;> rfl

theorem d9MetricPerturbation_ghostOnlyIndependentVariation
    (fields : IndependentFields period hPeriod)
    (direction : SmoothQuotientField period hPeriod GhostFiber ×
      SmoothQuotientField period hPeriod GhostFiber)
    (sector : Sector)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MetricPerturbation period hPeriod fields
        (ghostOnlyIndependentVariation period hPeriod direction)
        sector point = zeroSymmetric := by
  have hZero : ∀ index : Fin 4,
      (0 : SmoothQuotientField period hPeriod (Fin 4 → Real))
          (fixedThroatQuotientInclusion period hPeriod point) index = 0 :=
    fun _ => rfl
  cases sector <;> ext <;>
    simp [d9MetricPerturbation, selectedMetricVelocity,
      metricMagnitudeVelocityAt, ghostOnlyIndependentVariation,
      zeroSmoothDiagonalMetricVariation, lorentzMetric, zeroSymmetric,
      selectSector, hZero]

end

end P0EFTJanusCommonGhostD9Variation4D
end JanusFormal
