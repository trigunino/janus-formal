import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLEnrichedD9Projection4D

/-!
# Robin and LL enriched D9 projection

The added LL slot records the three LL components of the actual common
`IndependentFieldVariation`.  For `MatterRobinLLEnrichedDirections` the field
component is arbitrary, while the auxiliary-metric and measure velocities are
honestly zero because that source type does not expose directions for them.
The independent bulk auxiliary pair remains outside this projection.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLVisibleD9Projection4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusCommonCompleteSectorD9ProjectionKernel4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D
open P0EFTJanusCommonMatterRobinLLEnrichedD9Projection4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- The three genuine LL velocity slots of the common variation type. -/
@[ext]
structure VisibleLLDirection where
  field : SmoothThroatField period hPeriod LLFieldFiber
  auxMetric : SmoothThroatField period hPeriod LLMetricFiber
  measure : SmoothThroatField period hPeriod Real

/-- Old Robin-enriched D9 data together with the actual LL velocities. -/
@[ext]
structure RobinLLVisibleD9Projection where
  robinD9 : RobinEnrichedVisibleD9Projection period hPeriod
  ll : VisibleLLDirection period hPeriod

def robinLLVisibleD9Projection
    (fields : IndependentFields period hPeriod)
    (direction : MatterRobinLLEnrichedDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    RobinLLVisibleD9Projection period hPeriod where
  robinD9 := robinEnrichedVisibleD9Projection period hPeriod fields direction
    sector column point
  ll := {
    field := (combinedIndependentVariation period hPeriod direction.common).llField
    auxMetric :=
      (combinedIndependentVariation period hPeriod direction.common).llAuxMetric
    measure :=
      (combinedIndependentVariation period hPeriod direction.common).llMeasure }

/-- Exact recovery of all LL components present in the common variation. -/
@[simp]
theorem robinLLVisibleD9Projection_ll
    (fields : IndependentFields period hPeriod)
    (direction : MatterRobinLLEnrichedDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (robinLLVisibleD9Projection period hPeriod fields direction sector column
      point).ll =
      { field := direction.common.ll
        auxMetric := 0
        measure := 0 } :=
  rfl

/-- Equality is exactly old Robin-D9 equality plus equality of the complete
LL slot. -/
theorem robinLLVisibleD9Projection_eq_iff
    (fields : IndependentFields period hPeriod)
    (first second : MatterRobinLLEnrichedDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    robinLLVisibleD9Projection period hPeriod fields first sector column point =
        robinLLVisibleD9Projection period hPeriod fields second sector column point ↔
      robinEnrichedVisibleD9Projection period hPeriod fields first
          sector column point =
        robinEnrichedVisibleD9Projection period hPeriod fields second
          sector column point ∧
      (robinLLVisibleD9Projection period hPeriod fields first sector column
          point).ll =
        (robinLLVisibleD9Projection period hPeriod fields second sector column
          point).ll := by
  constructor
  · intro h
    exact ⟨congrArg RobinLLVisibleD9Projection.robinD9 h,
      congrArg RobinLLVisibleD9Projection.ll h⟩
  · rintro ⟨hRobin, hLL⟩
    apply RobinLLVisibleD9Projection.ext
    · exact hRobin
    · exact hLL

/-- With the old Robin-D9 data fixed, the former LL ambiguity is removed. -/
theorem robinLLVisibleD9Projection_fixed_nonLL_eq_iff
    (fields : IndependentFields period hPeriod)
    (common : CommonSectorDirections period hPeriod)
    (robin : SmoothThroatField period hPeriod Real)
    (firstLL secondLL : SmoothThroatField period hPeriod LLFieldFiber)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    robinLLVisibleD9Projection period hPeriod fields
        ⟨{ common with ll := firstLL }, robin⟩ sector column point =
      robinLLVisibleD9Projection period hPeriod fields
        ⟨{ common with ll := secondLL }, robin⟩ sector column point ↔
      firstLL = secondLL := by
  rw [robinLLVisibleD9Projection_eq_iff]
  constructor
  · intro h
    exact congrArg VisibleLLDirection.field h.2
  · intro h
    subst secondLL
    exact ⟨rfl, rfl⟩

/-- Changing only the independent bulk auxiliary pair remains invisible even
after adding the LL slot. -/
theorem robinLLVisibleD9Projection_independent_auxiliary_invisible
    (fields : IndependentFields period hPeriod)
    (common : CommonSectorDirections period hPeriod)
    (robin : SmoothThroatField period hPeriod Real)
    (firstAux secondAux : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    robinLLVisibleD9Projection period hPeriod fields
        ⟨{ common with auxiliary := firstAux }, robin⟩ sector column point =
      robinLLVisibleD9Projection period hPeriod fields
        ⟨{ common with auxiliary := secondAux }, robin⟩ sector column point := by
  apply RobinLLVisibleD9Projection.ext
  · change robinEnrichedVisibleD9Projection period hPeriod fields
        ⟨{ common with auxiliary := firstAux }, robin⟩ sector column point =
      robinEnrichedVisibleD9Projection period hPeriod fields
        ⟨{ common with auxiliary := secondAux }, robin⟩ sector column point
    rw [robinEnrichedVisibleD9Projection_eq_iff]
    exact ⟨combinedVisibleD9Projection_auxiliary_ll_kernel period hPeriod fields
      common firstAux secondAux common.ll common.ll sector column point, rfl⟩
  · rfl

end

end P0EFTJanusCommonMatterRobinLLVisibleD9Projection4D
end JanusFormal
