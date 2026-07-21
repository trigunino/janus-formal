import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMetricD9Variation4D

namespace JanusFormal
namespace P0EFTJanusCommonMetricD9TemporalKernel4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCommonMetricD9Variation4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGlobalDiagonalLorentzRoot4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- A diagonal metric direction whose throat restriction has only a temporal
component. D9 samples only diagonal indices `1`, `2`, and `3`. -/
def TemporalMetricDirection
    (direction : SmoothDiagonalMetricVariation period hPeriod) : Prop :=
  ∀ (sector : Sector)
      (point : MappingTorus (fixedEquatorData period hPeriod)) (row : Fin 3),
    (selectSector sector
      (direction.plusLogDirection, direction.minusLogDirection))
      (fixedThroatQuotientInclusion period hPeriod point) row.succ = 0

theorem d9MetricPerturbation_temporalMetricDirection
    (fields : IndependentFields period hPeriod)
    (direction : SmoothDiagonalMetricVariation period hPeriod)
    (hTemporal : TemporalMetricDirection period hPeriod direction)
    (sector : Sector)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MetricPerturbation period hPeriod fields
        (metricOnlyIndependentVariation period hPeriod direction) sector point =
      zeroSymmetric := by
  cases sector
  · have h1 : direction.plusLogDirection
        (fixedThroatQuotientInclusion period hPeriod point) 1 = 0 := by
      simpa [selectSector] using hTemporal .plus point 0
    have h2 : direction.plusLogDirection
        (fixedThroatQuotientInclusion period hPeriod point) 2 = 0 := by
      simpa [selectSector] using hTemporal .plus point 1
    have h3 : direction.plusLogDirection
        (fixedThroatQuotientInclusion period hPeriod point) 3 = 0 := by
      simpa [selectSector] using hTemporal .plus point 2
    ext <;>
      simp [d9MetricPerturbation, selectedMetricVelocity,
        metricMagnitudeVelocityAt, metricOnlyIndependentVariation,
        lorentzMetric, zeroSymmetric, selectSector, signature, h1, h2, h3]
  · have h1 : direction.minusLogDirection
        (fixedThroatQuotientInclusion period hPeriod point) 1 = 0 := by
      simpa [selectSector] using hTemporal .minus point 0
    have h2 : direction.minusLogDirection
        (fixedThroatQuotientInclusion period hPeriod point) 2 = 0 := by
      simpa [selectSector] using hTemporal .minus point 1
    have h3 : direction.minusLogDirection
        (fixedThroatQuotientInclusion period hPeriod point) 3 = 0 := by
      simpa [selectSector] using hTemporal .minus point 2
    ext <;>
      simp [d9MetricPerturbation, selectedMetricVelocity,
        metricMagnitudeVelocityAt, metricOnlyIndependentVariation,
        lorentzMetric, zeroSymmetric, selectSector, signature, h1, h2, h3]

theorem metricOnlyIndependentVariation_temporal_ne_zero
    (direction : SmoothDiagonalMetricVariation period hPeriod)
    (hDirection : direction ≠
      { plusLogDirection := 0, minusLogDirection := 0 }) :
    metricOnlyIndependentVariation period hPeriod direction ≠
      metricOnlyIndependentVariation period hPeriod
        { plusLogDirection := 0, minusLogDirection := 0 } := by
  intro hZero
  apply hDirection
  exact congrArg IndependentFieldVariation.metrics hZero

/-- A nonzero temporal metric direction and zero remain distinct in the common
variation space but have identical D9 metric projections. -/
theorem temporalMetricDirection_information_lost_by_d9
    (fields : IndependentFields period hPeriod)
    (direction : SmoothDiagonalMetricVariation period hPeriod)
    (hTemporal : TemporalMetricDirection period hPeriod direction)
    (hDirection : direction ≠
      { plusLogDirection := 0, minusLogDirection := 0 }) :
    metricOnlyIndependentVariation period hPeriod direction ≠
        metricOnlyIndependentVariation period hPeriod
          { plusLogDirection := 0, minusLogDirection := 0 } ∧
      ∀ (sector : Sector)
          (point : MappingTorus (fixedEquatorData period hPeriod)),
        d9MetricPerturbation period hPeriod fields
            (metricOnlyIndependentVariation period hPeriod direction)
            sector point =
          d9MetricPerturbation period hPeriod fields
            (metricOnlyIndependentVariation period hPeriod
              { plusLogDirection := 0, minusLogDirection := 0 })
            sector point := by
  constructor
  · exact metricOnlyIndependentVariation_temporal_ne_zero period hPeriod
      direction hDirection
  · intro sector point
    rw [d9MetricPerturbation_temporalMetricDirection period hPeriod fields
      direction hTemporal]
    have hZero : TemporalMetricDirection period hPeriod
        { plusLogDirection := 0, minusLogDirection := 0 } := by
      intro selected point row
      cases selected <;> rfl
    rw [d9MetricPerturbation_temporalMetricDirection period hPeriod fields
      { plusLogDirection := 0, minusLogDirection := 0 } hZero]

end

end P0EFTJanusCommonMetricD9TemporalKernel4D
end JanusFormal
