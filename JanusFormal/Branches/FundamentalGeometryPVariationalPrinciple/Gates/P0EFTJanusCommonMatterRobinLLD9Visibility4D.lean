import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLActionVariation4D

/-!
# D9 visibility of the enriched matter + Robin + LL packet

The current D9 bridge consumes the common `IndependentFieldVariation` and has
no Robin junction slot.  This gate identifies exactly that projection loss:
the common packet is recovered faithfully from the D9 input projection, while
Robin variations with fixed common data have identical current D9 inputs.  The
enriched action-direction realization itself remains faithful.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLD9Visibility4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The input visible to the current D9 bridge.  Its type has no Robin slot. -/
def d9VisibleVariation
    (direction : MatterRobinLLEnrichedDirections period hPeriod) :
    IndependentFieldVariation period hPeriod :=
  combinedIndependentVariation period hPeriod direction.common

/-- Equality of current D9 input projections is exactly equality of the common
packets; it imposes no equality on the Robin fields. -/
theorem d9VisibleVariation_eq_iff_common_eq
    (first second : MatterRobinLLEnrichedDirections period hPeriod) :
    d9VisibleVariation period hPeriod first =
        d9VisibleVariation period hPeriod second ↔
      first.common = second.common := by
  constructor
  · intro hEqual
    exact combinedIndependentVariation_injective period hPeriod hEqual
  · intro hCommon
    simp [d9VisibleVariation, hCommon]

/-- Changing only Robin leaves the current D9 input literally unchanged. -/
theorem d9VisibleVariation_robin_invisible
    (common : CommonSectorDirections period hPeriod)
    (firstRobin secondRobin : SmoothThroatField period hPeriod Real) :
    d9VisibleVariation period hPeriod ⟨common, firstRobin⟩ =
      d9VisibleVariation period hPeriod ⟨common, secondRobin⟩ := rfl

/-- Consequently every currently supplied D9 block agrees when only the Robin
direction changes. -/
theorem d9_blocks_robin_invisible
    (common : CommonSectorDirections period hPeriod)
    (firstRobin secondRobin : SmoothThroatField period hPeriod Real)
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    d9MetricPerturbation period hPeriod fields
          (d9VisibleVariation period hPeriod ⟨common, firstRobin⟩) sector point =
        d9MetricPerturbation period hPeriod fields
          (d9VisibleVariation period hPeriod ⟨common, secondRobin⟩) sector point ∧
      d9MatterCoefficient period hPeriod
          (d9VisibleVariation period hPeriod ⟨common, firstRobin⟩) sector point =
        d9MatterCoefficient period hPeriod
          (d9VisibleVariation period hPeriod ⟨common, secondRobin⟩) sector point ∧
      d9GaugeOneForm period hPeriod
          (d9VisibleVariation period hPeriod ⟨common, firstRobin⟩)
          sector column point =
        d9GaugeOneForm period hPeriod
          (d9VisibleVariation period hPeriod ⟨common, secondRobin⟩)
          sector column point ∧
      d9U1Ghost period hPeriod
          (d9VisibleVariation period hPeriod ⟨common, firstRobin⟩)
          sector column point =
        d9U1Ghost period hPeriod
          (d9VisibleVariation period hPeriod ⟨common, secondRobin⟩)
          sector column point := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Robin information is lost only by the current D9 projection: the enriched
action-direction realization still distinguishes unequal Robin fields. -/
theorem enrichedCommonVariation_ne_of_robin_ne
    (common : CommonSectorDirections period hPeriod)
    {firstRobin secondRobin : SmoothThroatField period hPeriod Real}
    (hRobin : firstRobin ≠ secondRobin) :
    enrichedCommonVariation period hPeriod ⟨common, firstRobin⟩ ≠
      enrichedCommonVariation period hPeriod ⟨common, secondRobin⟩ := by
  intro hEqual
  exact hRobin (congrArg Prod.snd hEqual)

end

end P0EFTJanusCommonMatterRobinLLD9Visibility4D
end JanusFormal
