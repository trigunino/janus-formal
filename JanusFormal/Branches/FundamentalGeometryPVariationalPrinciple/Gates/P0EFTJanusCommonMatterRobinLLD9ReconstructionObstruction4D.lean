import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLD9Visibility4D

/-!
# Observational obstruction to Robin reconstruction from current D9 data

Two explicit enriched directions differ by constant Robin fields but have the
same current D9 input.  Therefore no function from that D9 input type can be a
left inverse of the projection on every enriched direction.  This is only an
obstruction for the presently supplied D9 observation map, not a no-go theorem
for an enlarged D9 complex or for the action itself.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLD9ReconstructionObstruction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D
open P0EFTJanusCommonMatterRobinLLD9Visibility4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- Enriched direction with zero constant Robin component. -/
def zeroRobinDirection (common : CommonSectorDirections period hPeriod) :
    MatterRobinLLEnrichedDirections period hPeriod :=
  ⟨common, constantSmoothThroatField period hPeriod Real 0⟩

/-- Enriched direction with unit constant Robin component. -/
def unitRobinDirection (common : CommonSectorDirections period hPeriod) :
    MatterRobinLLEnrichedDirections period hPeriod :=
  ⟨common, constantSmoothThroatField period hPeriod Real 1⟩

/-- The two explicit enriched directions are genuinely distinct. -/
theorem zeroRobinDirection_ne_unitRobinDirection
    (point : EffectiveThroat period hPeriod)
    (common : CommonSectorDirections period hPeriod) :
    zeroRobinDirection period hPeriod common ≠
      unitRobinDirection period hPeriod common := by
  intro hEqual
  have hRobin := congrArg
    (fun direction => direction.robin point) hEqual
  norm_num [zeroRobinDirection, unitRobinDirection,
    constantSmoothThroatField] at hRobin

/-- Nevertheless the current D9 input projection cannot distinguish them. -/
theorem zero_unit_Robin_same_d9_projection
    (common : CommonSectorDirections period hPeriod) :
    d9VisibleVariation period hPeriod
        (zeroRobinDirection period hPeriod common) =
      d9VisibleVariation period hPeriod
        (unitRobinDirection period hPeriod common) := by
  exact d9VisibleVariation_robin_invisible period hPeriod common _ _

/-- No reconstruction from the current D9 input can recover every enriched
direction. -/
theorem no_global_leftInverse_from_current_d9_projection
    (point : EffectiveThroat period hPeriod) :
    ∀ reconstruct : IndependentFieldVariation period hPeriod →
        MatterRobinLLEnrichedDirections period hPeriod,
      ¬ Function.LeftInverse reconstruct (d9VisibleVariation period hPeriod) := by
  intro reconstruct hLeftInverse
  let common : CommonSectorDirections period hPeriod :=
    { metric := { plusLogDirection := 0, minusLogDirection := 0 }
      matter := 0
      gauge := 0
      ghost := 0
      auxiliary := 0
      ll := 0 }
  have hDirectionsEqual := hLeftInverse.injective
    (zero_unit_Robin_same_d9_projection period hPeriod common)
  exact zeroRobinDirection_ne_unitRobinDirection period hPeriod point common
    hDirectionsEqual

end

end P0EFTJanusCommonMatterRobinLLD9ReconstructionObstruction4D
end JanusFormal
