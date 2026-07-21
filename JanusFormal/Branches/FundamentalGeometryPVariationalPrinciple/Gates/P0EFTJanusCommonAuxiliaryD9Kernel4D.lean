import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonGaugeD9Variation4D

namespace JanusFormal
namespace P0EFTJanusCommonAuxiliaryD9Kernel4D

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

/-- Faithful auxiliary-only direction in the common Program-P variation space. -/
def auxiliaryOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) :
    IndependentFieldVariation period hPeriod where
  metrics := zeroSmoothDiagonalMetricVariation period hPeriod
  matter := 0
  gauge := 0
  ghosts := 0
  auxiliaries := direction
  llAuxMetric := 0
  llMeasure := 0
  llField := 0

theorem auxiliaryOnlyIndependentVariation_injective :
    Function.Injective (auxiliaryOnlyIndependentVariation period hPeriod) := by
  intro first second hEqual
  exact congrArg IndependentFieldVariation.auxiliaries hEqual

theorem d9GaugeOneForm_auxiliaryOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9GaugeOneForm period hPeriod
        (auxiliaryOnlyIndependentVariation period hPeriod direction)
        sector column point = zeroTangent := by
  cases sector <;> ext <;> rfl

theorem d9MatterCoefficient_auxiliaryOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber)
    (sector : Sector)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MatterCoefficient period hPeriod
        (auxiliaryOnlyIndependentVariation period hPeriod direction) sector point = 0 := by
  cases sector <;> rfl

theorem d9U1Ghost_auxiliaryOnlyIndependentVariation
    (direction : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9U1Ghost period hPeriod
        (auxiliaryOnlyIndependentVariation period hPeriod direction)
        sector column point = 0 := by
  cases sector <;> rfl

theorem d9MetricPerturbation_auxiliaryOnlyIndependentVariation
    (fields : IndependentFields period hPeriod)
    (direction : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber)
    (sector : Sector)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MetricPerturbation period hPeriod fields
        (auxiliaryOnlyIndependentVariation period hPeriod direction)
        sector point = zeroSymmetric := by
  have hZero : ∀ index : Fin 4,
      (0 : SmoothQuotientField period hPeriod (Fin 4 → Real))
          (fixedThroatQuotientInclusion period hPeriod point) index = 0 :=
    fun _ => rfl
  cases sector <;> ext <;>
    simp [d9MetricPerturbation, selectedMetricVelocity,
      metricMagnitudeVelocityAt, auxiliaryOnlyIndependentVariation,
      zeroSmoothDiagonalMetricVariation, lorentzMetric, zeroSymmetric,
      selectSector, hZero]

end

end P0EFTJanusCommonAuxiliaryD9Kernel4D
end JanusFormal
