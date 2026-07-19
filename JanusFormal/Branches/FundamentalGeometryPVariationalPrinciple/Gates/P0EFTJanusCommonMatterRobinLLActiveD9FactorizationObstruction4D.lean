import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLD9ReconstructionObstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLActiveProjectionKernel4D

/-!
# Active-class obstruction to factorization through current D9 data

The active class of a direction for the assembled action is its concrete
matter/Robin/LL projection.  Constant zero and unit Robin directions have the
same current D9 projection but distinct active classes.  Hence the active-class
map does not factor through current D9 data, even through a noninjective
decoder.  This is restricted to the presently supplied D9 observation map.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLActiveD9FactorizationObstruction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D
open P0EFTJanusCommonMatterRobinLLD9Visibility4D
open P0EFTJanusCommonMatterRobinLLD9ReconstructionObstruction4D
open P0EFTJanusCommonMatterRobinLLActiveProjectionKernel4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- The explicit zero/unit Robin witnesses have different active classes. -/
theorem zero_unit_Robin_active_projections_ne
    (point : EffectiveThroat period hPeriod)
    (common : CommonSectorDirections period hPeriod) :
    activeMatterRobinLLProjection period hPeriod
        (zeroRobinDirection period hPeriod common) ≠
      activeMatterRobinLLProjection period hPeriod
        (unitRobinDirection period hPeriod common) := by
  intro hEqual
  have hComponents :=
    (activeMatterRobinLLProjection_eq_iff period hPeriod _ _).mp hEqual
  have hRobin := hComponents.2.1
  have hValue := congrArg (fun field => field point) hRobin
  norm_num [zeroRobinDirection, unitRobinDirection,
    activeMatterRobinLLProjection, constantSmoothThroatField] at hValue

/-- Thus equal current D9 data can represent distinct active quotient
classes. -/
theorem same_d9_projection_distinct_active_classes
    (point : EffectiveThroat period hPeriod)
    (common : CommonSectorDirections period hPeriod) :
    d9VisibleVariation period hPeriod
          (zeroRobinDirection period hPeriod common) =
        d9VisibleVariation period hPeriod
          (unitRobinDirection period hPeriod common) ∧
      activeMatterRobinLLProjection period hPeriod
          (zeroRobinDirection period hPeriod common) ≠
        activeMatterRobinLLProjection period hPeriod
          (unitRobinDirection period hPeriod common) :=
  ⟨zero_unit_Robin_same_d9_projection period hPeriod common,
    zero_unit_Robin_active_projections_ne period hPeriod point common⟩

/-- No decoder of current D9 inputs can reconstruct the active class of every
enriched direction.  This rules out any injective such factorization a
fortiori. -/
theorem no_active_projection_factorization_through_current_d9
    (point : EffectiveThroat period hPeriod) :
    ∀ recover : IndependentFieldVariation period hPeriod →
        ActiveMatterRobinLLDirection period hPeriod,
      ¬ ∀ direction : MatterRobinLLEnrichedDirections period hPeriod,
        recover (d9VisibleVariation period hPeriod direction) =
          activeMatterRobinLLProjection period hPeriod direction := by
  intro recover hRecovers
  let common : CommonSectorDirections period hPeriod :=
    { metric := { plusLogDirection := 0, minusLogDirection := 0 }
      matter := 0
      gauge := 0
      ghost := 0
      auxiliary := 0
      ll := 0 }
  have hD9 := zero_unit_Robin_same_d9_projection period hPeriod common
  have hZero := hRecovers (zeroRobinDirection period hPeriod common)
  have hUnit := hRecovers (unitRobinDirection period hPeriod common)
  have hActiveEqual :
      activeMatterRobinLLProjection period hPeriod
          (zeroRobinDirection period hPeriod common) =
        activeMatterRobinLLProjection period hPeriod
          (unitRobinDirection period hPeriod common) := by
    calc
      _ = recover (d9VisibleVariation period hPeriod
          (zeroRobinDirection period hPeriod common)) := hZero.symm
      _ = recover (d9VisibleVariation period hPeriod
          (unitRobinDirection period hPeriod common)) := congrArg recover hD9
      _ = _ := hUnit
  exact zero_unit_Robin_active_projections_ne period hPeriod point common
    hActiveEqual

end

end P0EFTJanusCommonMatterRobinLLActiveD9FactorizationObstruction4D
end JanusFormal
