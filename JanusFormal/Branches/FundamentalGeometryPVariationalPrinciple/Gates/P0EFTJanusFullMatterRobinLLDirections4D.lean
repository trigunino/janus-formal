import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLActionVariation4D

/-!
# Full common + Robin directions with all three LL slots

The common packet already contains the LL field direction.  This gate adds
the actual LL auxiliary-metric and measure directions and realizes all three
existing LL slots simultaneously in `IndependentFieldVariation`.
-/

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinLLDirections4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusCommonCompleteSectorD9Variation4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Common metric/matter/gauge/ghost/auxiliary/LL-field packet, Robin
direction, and the two remaining real LL directions.  Thus all three LL slots
`field`, `auxMetric`, and `measure` occur exactly once. -/
structure FullMatterRobinLLDirections where
  common : CommonSectorDirections period hPeriod
  robin : SmoothThroatField period hPeriod Real
  llAuxMetric : SmoothThroatField period hPeriod LLMetricFiber
  llMeasure : SmoothThroatField period hPeriod Real

/-- Faithful realization in the actual independent variation paired with the
Robin slot absent from `IndependentFieldVariation`. -/
def fullMatterRobinLLVariation
    (direction : FullMatterRobinLLDirections period hPeriod) :
    IndependentFieldVariation period hPeriod ×
      SmoothThroatField period hPeriod Real :=
  ( { metrics := direction.common.metric
      matter := direction.common.matter
      gauge := direction.common.gauge
      ghosts := direction.common.ghost
      auxiliaries := direction.common.auxiliary
      llAuxMetric := direction.llAuxMetric
      llMeasure := direction.llMeasure
      llField := direction.common.ll },
    direction.robin )

theorem fullMatterRobinLLVariation_injective :
    Function.Injective (fullMatterRobinLLVariation period hPeriod) := by
  rintro ⟨⟨metric, matter, gauge, ghost, auxiliary, ll⟩,
      robin, llAuxMetric, llMeasure⟩
    ⟨⟨metric', matter', gauge', ghost', auxiliary', ll'⟩,
      robin', llAuxMetric', llMeasure'⟩ hEqual
  have hMetric := congrArg (fun value => value.1.metrics) hEqual
  have hMatter := congrArg (fun value => value.1.matter) hEqual
  have hGauge := congrArg (fun value => value.1.gauge) hEqual
  have hGhost := congrArg (fun value => value.1.ghosts) hEqual
  have hAuxiliary := congrArg (fun value => value.1.auxiliaries) hEqual
  have hLL := congrArg (fun value => value.1.llField) hEqual
  have hRobin := congrArg Prod.snd hEqual
  have hLLAuxMetric := congrArg (fun value => value.1.llAuxMetric) hEqual
  have hLLMeasure := congrArg (fun value => value.1.llMeasure) hEqual
  change metric = metric' at hMetric
  change matter = matter' at hMatter
  change gauge = gauge' at hGauge
  change ghost = ghost' at hGhost
  change auxiliary = auxiliary' at hAuxiliary
  change ll = ll' at hLL
  change robin = robin' at hRobin
  change llAuxMetric = llAuxMetric' at hLLAuxMetric
  change llMeasure = llMeasure' at hLLMeasure
  subst metric'
  subst matter'
  subst gauge'
  subst ghost'
  subst auxiliary'
  subst ll'
  subst robin'
  subst llAuxMetric'
  subst llMeasure'
  rfl

@[simp]
theorem fullMatterRobinLLVariation_metrics
    (direction : FullMatterRobinLLDirections period hPeriod) :
    (fullMatterRobinLLVariation period hPeriod direction).1.metrics =
      direction.common.metric := rfl

@[simp]
theorem fullMatterRobinLLVariation_matter
    (direction : FullMatterRobinLLDirections period hPeriod) :
    (fullMatterRobinLLVariation period hPeriod direction).1.matter =
      direction.common.matter := rfl

@[simp]
theorem fullMatterRobinLLVariation_gauge
    (direction : FullMatterRobinLLDirections period hPeriod) :
    (fullMatterRobinLLVariation period hPeriod direction).1.gauge =
      direction.common.gauge := rfl

@[simp]
theorem fullMatterRobinLLVariation_ghosts
    (direction : FullMatterRobinLLDirections period hPeriod) :
    (fullMatterRobinLLVariation period hPeriod direction).1.ghosts =
      direction.common.ghost := rfl

@[simp]
theorem fullMatterRobinLLVariation_auxiliaries
    (direction : FullMatterRobinLLDirections period hPeriod) :
    (fullMatterRobinLLVariation period hPeriod direction).1.auxiliaries =
      direction.common.auxiliary := rfl

@[simp]
theorem fullMatterRobinLLVariation_llField
    (direction : FullMatterRobinLLDirections period hPeriod) :
    (fullMatterRobinLLVariation period hPeriod direction).1.llField =
      direction.common.ll := rfl

@[simp]
theorem fullMatterRobinLLVariation_llAuxMetric
    (direction : FullMatterRobinLLDirections period hPeriod) :
    (fullMatterRobinLLVariation period hPeriod direction).1.llAuxMetric =
      direction.llAuxMetric := rfl

@[simp]
theorem fullMatterRobinLLVariation_llMeasure
    (direction : FullMatterRobinLLDirections period hPeriod) :
    (fullMatterRobinLLVariation period hPeriod direction).1.llMeasure =
      direction.llMeasure := rfl

@[simp]
theorem fullMatterRobinLLVariation_robin
    (direction : FullMatterRobinLLDirections period hPeriod) :
    (fullMatterRobinLLVariation period hPeriod direction).2 = direction.robin :=
  rfl

end

end P0EFTJanusFullMatterRobinLLDirections4D
end JanusFormal
