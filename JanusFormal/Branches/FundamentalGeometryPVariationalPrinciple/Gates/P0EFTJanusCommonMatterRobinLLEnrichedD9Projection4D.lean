import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonCompleteSectorD9ProjectionKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLD9ReconstructionObstruction4D

/-!
# Minimal Robin-enriched D9 projection

This gate adds the genuine Robin direction field to the four existing D9
blocks.  Robin is then recovered exactly and the constant-Robin ambiguity is
removed.  The construction remains pointwise in the four original D9 blocks;
auxiliary and LL directions are still invisible, and no global D9 complex is
claimed.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLEnrichedD9Projection4D

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
open P0EFTJanusCommonMatterRobinLLD9ReconstructionObstruction4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- The four actual D9 blocks plus one genuine Robin direction field. -/
@[ext]
structure RobinEnrichedVisibleD9Projection where
  visible : VisibleD9Projection
  robin : SmoothThroatField period hPeriod Real

/-- Minimal enriched projection from the same action-direction packet. -/
def robinEnrichedVisibleD9Projection
    (fields : IndependentFields period hPeriod)
    (direction : MatterRobinLLEnrichedDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    RobinEnrichedVisibleD9Projection period hPeriod where
  visible := combinedVisibleD9Projection period hPeriod fields direction.common
    sector column point
  robin := direction.robin

/-- The added slot recovers the Robin direction definitionally. -/
@[simp] theorem robinEnrichedVisibleD9Projection_robin
    (fields : IndependentFields period hPeriod)
    (direction : MatterRobinLLEnrichedDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (robinEnrichedVisibleD9Projection period hPeriod fields direction
      sector column point).robin = direction.robin := rfl

/-- Equality is exactly equality of the old visible data together with Robin;
this is the precise relative injectivity provided by the new slot. -/
theorem robinEnrichedVisibleD9Projection_eq_iff
    (fields : IndependentFields period hPeriod)
    (first second : MatterRobinLLEnrichedDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    robinEnrichedVisibleD9Projection period hPeriod fields first
        sector column point =
        robinEnrichedVisibleD9Projection period hPeriod fields second
          sector column point ↔
      combinedVisibleD9Projection period hPeriod fields first.common
          sector column point =
        combinedVisibleD9Projection period hPeriod fields second.common
          sector column point ∧ first.robin = second.robin := by
  constructor
  · intro hEqual
    exact ⟨congrArg RobinEnrichedVisibleD9Projection.visible hEqual,
      congrArg RobinEnrichedVisibleD9Projection.robin hEqual⟩
  · rintro ⟨hVisible, hRobin⟩
    apply RobinEnrichedVisibleD9Projection.ext
    · exact hVisible
    · exact hRobin

/-- With common data fixed, equality of enriched D9 projections is exactly
equality of Robin fields. -/
theorem robinEnrichedVisibleD9Projection_fixed_common_injective
    (fields : IndependentFields period hPeriod)
    (common : CommonSectorDirections period hPeriod)
    (firstRobin secondRobin : SmoothThroatField period hPeriod Real)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    robinEnrichedVisibleD9Projection period hPeriod fields
        ⟨common, firstRobin⟩ sector column point =
        robinEnrichedVisibleD9Projection period hPeriod fields
          ⟨common, secondRobin⟩ sector column point ↔
      firstRobin = secondRobin := by
  rw [robinEnrichedVisibleD9Projection_eq_iff]
  simp

/-- The explicit zero/unit Robin ambiguity of the old D9 projection disappears
after enrichment. -/
theorem zero_unit_Robin_enriched_d9_ne
    (fields : IndependentFields period hPeriod)
    (common : CommonSectorDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    robinEnrichedVisibleD9Projection period hPeriod fields
        (zeroRobinDirection period hPeriod common) sector column point ≠
      robinEnrichedVisibleD9Projection period hPeriod fields
        (unitRobinDirection period hPeriod common) sector column point := by
  intro hEqual
  have hRobin := congrArg RobinEnrichedVisibleD9Projection.robin hEqual
  have hValue := congrArg (fun field => field point) hRobin
  norm_num [zeroRobinDirection, unitRobinDirection,
    robinEnrichedVisibleD9Projection, constantSmoothThroatField] at hValue

/-- Auxiliary and LL changes remain invisible when common visible data and
Robin are fixed. -/
theorem robinEnrichedVisibleD9Projection_auxiliary_ll_invisible
    (fields : IndependentFields period hPeriod)
    (visible : CommonSectorDirections period hPeriod)
    (robin : SmoothThroatField period hPeriod Real)
    (firstAux secondAux : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber)
    (firstLL secondLL : SmoothThroatField period hPeriod LLFieldFiber)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    robinEnrichedVisibleD9Projection period hPeriod fields
        ⟨{ visible with auxiliary := firstAux, ll := firstLL }, robin⟩
        sector column point =
      robinEnrichedVisibleD9Projection period hPeriod fields
        ⟨{ visible with auxiliary := secondAux, ll := secondLL }, robin⟩
        sector column point := by
  rw [robinEnrichedVisibleD9Projection_eq_iff]
  exact ⟨combinedVisibleD9Projection_auxiliary_ll_kernel period hPeriod fields
    visible firstAux secondAux firstLL secondLL sector column point, rfl⟩

end

end P0EFTJanusCommonMatterRobinLLEnrichedD9Projection4D
end JanusFormal
