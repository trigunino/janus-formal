import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonGhostD9Variation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonAuxiliaryD9Kernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterActionVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMetricD9TemporalKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonGaugeD9TemporalKernel4D

namespace JanusFormal
namespace P0EFTJanusCommonCompleteSectorD9Variation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusCommonGaugeD9Variation4D
open P0EFTJanusCommonGhostD9Variation4D
open P0EFTJanusCommonAuxiliaryD9Kernel4D
open P0EFTJanusCommonMetricD9Variation4D
open P0EFTJanusCommonMetricD9TemporalKernel4D
open P0EFTJanusCommonGaugeD9TemporalKernel4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra

variable (period : Real) (hPeriod : period ≠ 0)

/-- The six already constructed physical directions, before their faithful
inclusion in the common `IndependentFieldVariation`. -/
structure CommonSectorDirections where
  metric : SmoothDiagonalMetricVariation period hPeriod
  matter : SmoothQuotientField period hPeriod MatterFiber ×
    SmoothQuotientField period hPeriod MatterFiber
  gauge : SmoothQuotientField period hPeriod GaugeFiber ×
    SmoothQuotientField period hPeriod GaugeFiber
  ghost : SmoothQuotientField period hPeriod GhostFiber ×
    SmoothQuotientField period hPeriod GhostFiber
  auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
    SmoothQuotientField period hPeriod AuxiliaryFiber
  ll : SmoothThroatField period hPeriod LLFieldFiber

/-- Simultaneous inclusion of all six existing sector directions. -/
def combinedIndependentVariation
    (direction : CommonSectorDirections period hPeriod) :
    IndependentFieldVariation period hPeriod where
  metrics := direction.metric
  matter := direction.matter
  gauge := direction.gauge
  ghosts := direction.ghost
  auxiliaries := direction.auxiliary
  llAuxMetric := 0
  llMeasure := 0
  llField := direction.ll

theorem combinedIndependentVariation_injective :
    Function.Injective (combinedIndependentVariation period hPeriod) := by
  rintro ⟨metric, matter, gauge, ghost, auxiliary, ll⟩
    ⟨metric', matter', gauge', ghost', auxiliary', ll'⟩ hEqual
  have hMetric := congrArg IndependentFieldVariation.metrics hEqual
  have hMatter := congrArg IndependentFieldVariation.matter hEqual
  have hGauge := congrArg IndependentFieldVariation.gauge hEqual
  have hGhost := congrArg IndependentFieldVariation.ghosts hEqual
  have hAuxiliary := congrArg IndependentFieldVariation.auxiliaries hEqual
  have hLL := congrArg IndependentFieldVariation.llField hEqual
  change metric = metric' at hMetric
  change matter = matter' at hMatter
  change gauge = gauge' at hGauge
  change ghost = ghost' at hGhost
  change auxiliary = auxiliary' at hAuxiliary
  change ll = ll' at hLL
  subst metric'
  subst matter'
  subst gauge'
  subst ghost'
  subst auxiliary'
  subst ll'
  rfl

/-- D9's metric block depends exactly on the common metric direction. -/
theorem d9MetricPerturbation_combined
    (fields : IndependentFields period hPeriod)
    (direction : CommonSectorDirections period hPeriod)
    (sector : Sector)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MetricPerturbation period hPeriod fields
        (combinedIndependentVariation period hPeriod direction) sector point =
      d9MetricPerturbation period hPeriod fields
        (metricOnlyIndependentVariation period hPeriod direction.metric)
        sector point := by
  rfl

/-- D9's matter block depends exactly on the common matter direction. -/
theorem d9MatterCoefficient_combined
    (direction : CommonSectorDirections period hPeriod)
    (sector : Sector)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MatterCoefficient period hPeriod
        (combinedIndependentVariation period hPeriod direction) sector point =
      d9MatterCoefficient period hPeriod
        (matterOnlyIndependentVariation period hPeriod direction.matter)
        sector point := by
  rfl

/-- D9's gauge block depends exactly on the common gauge direction. -/
theorem d9GaugeOneForm_combined
    (direction : CommonSectorDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9GaugeOneForm period hPeriod
        (combinedIndependentVariation period hPeriod direction)
        sector column point =
      d9GaugeOneForm period hPeriod
        (gaugeOnlyIndependentVariation period hPeriod direction.gauge)
        sector column point := by
  rfl

/-- D9's U(1)-ghost block depends exactly on the common ghost direction. -/
theorem d9U1Ghost_combined
    (direction : CommonSectorDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9U1Ghost period hPeriod
        (combinedIndependentVariation period hPeriod direction)
        sector column point =
      d9U1Ghost period hPeriod
        (ghostOnlyIndependentVariation period hPeriod direction.ghost)
        sector column point := by
  rfl

/-- Auxiliary and LL directions are faithfully retained by the combined
variation but absent from every D9 block currently supplied. -/
theorem d9_auxiliary_ll_invisible
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber)
    (ll : SmoothThroatField period hPeriod LLFieldFiber)
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    let direction : CommonSectorDirections period hPeriod :=
      { metric := { plusLogDirection := 0, minusLogDirection := 0 }
        matter := 0
        gauge := 0
        ghost := 0
        auxiliary := auxiliary
        ll := ll }
    d9MetricPerturbation period hPeriod fields
          (combinedIndependentVariation period hPeriod direction) sector point =
        zeroSymmetric ∧
      d9MatterCoefficient period hPeriod
          (combinedIndependentVariation period hPeriod direction) sector point = 0 ∧
      d9GaugeOneForm period hPeriod
          (combinedIndependentVariation period hPeriod direction)
          sector column point = zeroTangent ∧
      d9U1Ghost period hPeriod
          (combinedIndependentVariation period hPeriod direction)
          sector column point = 0 := by
  dsimp
  constructor
  · rw [d9MetricPerturbation_combined]
    exact d9MetricPerturbation_auxiliaryOnlyIndependentVariation period hPeriod
      fields auxiliary sector point
  constructor
  · rw [d9MatterCoefficient_combined]
    cases sector <;> rfl
  constructor
  · rw [d9GaugeOneForm_combined]
    cases sector <;> ext <;> rfl
  · rw [d9U1Ghost_combined]
    cases sector <;> rfl

/-- Even in the simultaneous packet, temporal metric and gauge directions are
invisible to their spatial D9 blocks. Auxiliary and LL data may be arbitrary. -/
theorem d9_combined_temporal_blocks_invisible
    (direction : CommonSectorDirections period hPeriod)
    (fields : IndependentFields period hPeriod)
    (hMetric : TemporalMetricDirection period hPeriod direction.metric)
    (hGauge : TemporalGaugeDirection period hPeriod direction.gauge)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MetricPerturbation period hPeriod fields
          (combinedIndependentVariation period hPeriod direction) sector point =
        zeroSymmetric ∧
      d9GaugeOneForm period hPeriod
          (combinedIndependentVariation period hPeriod direction)
          sector column point = zeroTangent := by
  constructor
  · rw [d9MetricPerturbation_combined]
    exact d9MetricPerturbation_temporalMetricDirection period hPeriod fields
      direction.metric hMetric sector point
  · rw [d9GaugeOneForm_combined]
    exact d9GaugeOneForm_temporalGaugeDirection period hPeriod direction.gauge
      hGauge sector column point

end

end P0EFTJanusCommonCompleteSectorD9Variation4D
end JanusFormal
