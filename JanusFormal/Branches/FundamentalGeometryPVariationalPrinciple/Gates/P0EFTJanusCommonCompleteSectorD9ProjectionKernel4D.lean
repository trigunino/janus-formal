import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonCompleteSectorD9Variation4D

namespace JanusFormal
namespace P0EFTJanusCommonCompleteSectorD9ProjectionKernel4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusCommonGaugeD9Variation4D
open P0EFTJanusCommonGhostD9Variation4D
open P0EFTJanusCommonMetricD9Variation4D
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra

variable (period : Real) (hPeriod : period ≠ 0)

/-- The four blocks currently exported by D9 at fixed sector, column and
throat point. -/
@[ext]
structure VisibleD9Projection where
  metric : SymmetricTensor3
  matter : MatterFiber
  gauge : TangentVector3
  ghost : Real

/-- The actual four-block D9 projection of the simultaneous common direction. -/
def combinedVisibleD9Projection
    (fields : IndependentFields period hPeriod)
    (direction : CommonSectorDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    VisibleD9Projection where
  metric := d9MetricPerturbation period hPeriod fields
    (combinedIndependentVariation period hPeriod direction) sector point
  matter := d9MatterCoefficient period hPeriod
    (combinedIndependentVariation period hPeriod direction) sector point
  gauge := d9GaugeOneForm period hPeriod
    (combinedIndependentVariation period hPeriod direction) sector column point
  ghost := d9U1Ghost period hPeriod
    (combinedIndependentVariation period hPeriod direction) sector column point

/-- Equality of simultaneous D9 projections is exactly equality of the four
visible sector blocks. Auxiliary and LL directions do not occur. -/
theorem combinedVisibleD9Projection_eq_iff_visible_blocks
    (fields : IndependentFields period hPeriod)
    (first second : CommonSectorDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    combinedVisibleD9Projection period hPeriod fields first sector column point =
        combinedVisibleD9Projection period hPeriod fields second sector column point ↔
      d9MetricPerturbation period hPeriod fields
          (metricOnlyIndependentVariation period hPeriod first.metric) sector point =
        d9MetricPerturbation period hPeriod fields
          (metricOnlyIndependentVariation period hPeriod second.metric) sector point ∧
      d9MatterCoefficient period hPeriod
          (matterOnlyIndependentVariation period hPeriod first.matter) sector point =
        d9MatterCoefficient period hPeriod
          (matterOnlyIndependentVariation period hPeriod second.matter) sector point ∧
      d9GaugeOneForm period hPeriod
          (gaugeOnlyIndependentVariation period hPeriod first.gauge)
          sector column point =
        d9GaugeOneForm period hPeriod
          (gaugeOnlyIndependentVariation period hPeriod second.gauge)
          sector column point ∧
      d9U1Ghost period hPeriod
          (ghostOnlyIndependentVariation period hPeriod first.ghost)
          sector column point =
        d9U1Ghost period hPeriod
          (ghostOnlyIndependentVariation period hPeriod second.ghost)
          sector column point := by
  constructor
  · intro hEqual
    have hMetric := congrArg VisibleD9Projection.metric hEqual
    have hMatter := congrArg VisibleD9Projection.matter hEqual
    have hGauge := congrArg VisibleD9Projection.gauge hEqual
    have hGhost := congrArg VisibleD9Projection.ghost hEqual
    dsimp [combinedVisibleD9Projection] at hMetric hMatter hGauge hGhost
    rw [d9MetricPerturbation_combined, d9MetricPerturbation_combined] at hMetric
    rw [d9MatterCoefficient_combined, d9MatterCoefficient_combined] at hMatter
    rw [d9GaugeOneForm_combined, d9GaugeOneForm_combined] at hGauge
    rw [d9U1Ghost_combined, d9U1Ghost_combined] at hGhost
    exact ⟨hMetric, hMatter, hGauge, hGhost⟩
  · rintro ⟨hMetric, hMatter, hGauge, hGhost⟩
    apply VisibleD9Projection.ext
    · dsimp [combinedVisibleD9Projection]
      rw [d9MetricPerturbation_combined, d9MetricPerturbation_combined]
      exact hMetric
    · dsimp [combinedVisibleD9Projection]
      rw [d9MatterCoefficient_combined, d9MatterCoefficient_combined]
      exact hMatter
    · dsimp [combinedVisibleD9Projection]
      rw [d9GaugeOneForm_combined, d9GaugeOneForm_combined]
      exact hGauge
    · dsimp [combinedVisibleD9Projection]
      rw [d9U1Ghost_combined, d9U1Ghost_combined]
      exact hGhost

/-- Changing only auxiliary and LL directions lies exactly in the kernel of
the supplied combined D9 projection. -/
theorem combinedVisibleD9Projection_auxiliary_ll_kernel
    (fields : IndependentFields period hPeriod)
    (visible : CommonSectorDirections period hPeriod)
    (firstAux secondAux :
      SmoothQuotientField period hPeriod AuxiliaryFiber ×
        SmoothQuotientField period hPeriod AuxiliaryFiber)
    (firstLL secondLL :
      P0EFTJanusMappingTorusSmoothThroatTrace4D.SmoothThroatField
        period hPeriod LLFieldFiber)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    combinedVisibleD9Projection period hPeriod fields
        { visible with auxiliary := firstAux, ll := firstLL }
        sector column point =
      combinedVisibleD9Projection period hPeriod fields
        { visible with auxiliary := secondAux, ll := secondLL }
        sector column point := by
  rw [combinedVisibleD9Projection_eq_iff_visible_blocks]
  exact ⟨rfl, rfl, rfl, rfl⟩

end

end P0EFTJanusCommonCompleteSectorD9ProjectionKernel4D
end JanusFormal
