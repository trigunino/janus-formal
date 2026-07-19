import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonGaugeD9Variation4D

namespace JanusFormal
namespace P0EFTJanusCommonGaugeD9TemporalKernel4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCommonGaugeD9Variation4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra

variable (period : Real) (hPeriod : period ≠ 0)

/-- A gauge direction whose restriction to the throat has only temporal
components.  D9 samples rows `1`, `2`, and `3`, so it cannot see it. -/
def TemporalGaugeDirection
    (direction : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) : Prop :=
  ∀ (sector : Sector) (column : Fin 2)
      (point : MappingTorus (fixedEquatorData period hPeriod)) (row : Fin 3),
    (match sector with | .plus => direction.1 | .minus => direction.2)
      (fixedThroatQuotientInclusion period hPeriod point) (row.succ, column) = 0

theorem d9GaugeOneForm_temporalGaugeDirection
    (direction : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber)
    (hTemporal : TemporalGaugeDirection period hPeriod direction)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9GaugeOneForm period hPeriod
        (gaugeOnlyIndependentVariation period hPeriod direction)
        sector column point = zeroTangent := by
  rw [d9GaugeOneForm_gaugeOnlyIndependentVariation]
  apply TangentVector3.ext
  · exact hTemporal sector column point 0
  · exact hTemporal sector column point 1
  · exact hTemporal sector column point 2

theorem gaugeOnlyIndependentVariation_temporal_ne_zero
    (direction : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber)
    (hDirection : direction ≠ 0) :
    gaugeOnlyIndependentVariation period hPeriod direction ≠
      gaugeOnlyIndependentVariation period hPeriod 0 := by
  intro hZero
  apply hDirection
  exact congrArg IndependentFieldVariation.gauge hZero

/-- A nonzero temporal gauge direction and the zero direction are distinct in
the common variation space but have identical D9 gauge one-form projections. -/
theorem temporalGaugeDirection_information_lost_by_d9
    (direction : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber)
    (hTemporal : TemporalGaugeDirection period hPeriod direction)
    (hDirection : direction ≠ 0) :
    gaugeOnlyIndependentVariation period hPeriod direction ≠
        gaugeOnlyIndependentVariation period hPeriod 0 ∧
      ∀ (sector : Sector) (column : Fin 2)
          (point : MappingTorus (fixedEquatorData period hPeriod)),
        d9GaugeOneForm period hPeriod
            (gaugeOnlyIndependentVariation period hPeriod direction)
            sector column point =
          d9GaugeOneForm period hPeriod
            (gaugeOnlyIndependentVariation period hPeriod 0)
            sector column point := by
  constructor
  · intro hEqual
    apply hDirection
    exact congrArg IndependentFieldVariation.gauge hEqual
  · intro sector column point
    rw [d9GaugeOneForm_temporalGaugeDirection period hPeriod direction hTemporal]
    rw [d9GaugeOneForm_gaugeOnlyIndependentVariation]
    cases sector <;> rfl

end

end P0EFTJanusCommonGaugeD9TemporalKernel4D
end JanusFormal
