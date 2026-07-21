import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLEnrichedD9Projection4D

/-!
# Minimal Robin, LL and auxiliary enrichment of current D9 data

This data package retains the four actual pointwise D9 blocks and adds the
genuine Robin, LL and auxiliary directions from the common action packet.
The added fields are recovered definitionally.  This is a data-level extension
of the current projection, not a new differential or global D9 complex.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLAuxiliaryEnrichedD9Projection4D

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

private abbrev AuxiliaryDirection :=
  SmoothQuotientField period hPeriod AuxiliaryFiber ×
    SmoothQuotientField period hPeriod AuxiliaryFiber

/-- Actual current D9 values enriched by the three missing direction data. -/
@[ext]
structure RobinLLAuxiliaryEnrichedVisibleD9Projection where
  visible : VisibleD9Projection
  robin : SmoothThroatField period hPeriod Real
  ll : SmoothThroatField period hPeriod LLFieldFiber
  auxiliary : AuxiliaryDirection period hPeriod

/-- Direct projection from the genuine enriched action-direction packet. -/
def robinLLAuxiliaryEnrichedVisibleD9Projection
    (fields : IndependentFields period hPeriod)
    (direction : MatterRobinLLEnrichedDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    RobinLLAuxiliaryEnrichedVisibleD9Projection period hPeriod where
  visible := combinedVisibleD9Projection period hPeriod fields direction.common
    sector column point
  robin := direction.robin
  ll := direction.common.ll
  auxiliary := direction.common.auxiliary

@[simp] theorem robinLLAuxiliaryEnriched_projection_robin
    (fields : IndependentFields period hPeriod)
    (direction : MatterRobinLLEnrichedDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (robinLLAuxiliaryEnrichedVisibleD9Projection period hPeriod fields direction
      sector column point).robin = direction.robin := rfl

@[simp] theorem robinLLAuxiliaryEnriched_projection_ll
    (fields : IndependentFields period hPeriod)
    (direction : MatterRobinLLEnrichedDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (robinLLAuxiliaryEnrichedVisibleD9Projection period hPeriod fields direction
      sector column point).ll = direction.common.ll := rfl

/-- The newly requested auxiliary direction is recovered exactly. -/
@[simp] theorem robinLLAuxiliaryEnriched_projection_auxiliary
    (fields : IndependentFields period hPeriod)
    (direction : MatterRobinLLEnrichedDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (robinLLAuxiliaryEnrichedVisibleD9Projection period hPeriod fields direction
      sector column point).auxiliary = direction.common.auxiliary := rfl

/-- Equality is exactly equality of the old visible values and all three added
direction slots. -/
theorem robinLLAuxiliaryEnriched_projection_eq_iff
    (fields : IndependentFields period hPeriod)
    (first second : MatterRobinLLEnrichedDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    robinLLAuxiliaryEnrichedVisibleD9Projection period hPeriod fields first
        sector column point =
        robinLLAuxiliaryEnrichedVisibleD9Projection period hPeriod fields second
          sector column point ↔
      combinedVisibleD9Projection period hPeriod fields first.common
          sector column point =
        combinedVisibleD9Projection period hPeriod fields second.common
          sector column point ∧
      first.robin = second.robin ∧ first.common.ll = second.common.ll ∧
        first.common.auxiliary = second.common.auxiliary := by
  constructor
  · intro hEqual
    exact ⟨congrArg RobinLLAuxiliaryEnrichedVisibleD9Projection.visible hEqual,
      congrArg RobinLLAuxiliaryEnrichedVisibleD9Projection.robin hEqual,
      congrArg RobinLLAuxiliaryEnrichedVisibleD9Projection.ll hEqual,
      congrArg RobinLLAuxiliaryEnrichedVisibleD9Projection.auxiliary hEqual⟩
  · rintro ⟨hVisible, hRobin, hLL, hAuxiliary⟩
    apply RobinLLAuxiliaryEnrichedVisibleD9Projection.ext
    · exact hVisible
    · exact hRobin
    · exact hLL
    · exact hAuxiliary

/-- With every other direction fixed, the enriched projection is injective in
the genuine auxiliary pair. -/
theorem robinLLAuxiliaryEnriched_projection_fixed_data_injective_auxiliary
    (fields : IndependentFields period hPeriod)
    (direction : MatterRobinLLEnrichedDirections period hPeriod)
    (firstAuxiliary secondAuxiliary : AuxiliaryDirection period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    robinLLAuxiliaryEnrichedVisibleD9Projection period hPeriod fields
        { direction with common :=
          { direction.common with auxiliary := firstAuxiliary } }
        sector column point =
      robinLLAuxiliaryEnrichedVisibleD9Projection period hPeriod fields
        { direction with common :=
          { direction.common with auxiliary := secondAuxiliary } }
        sector column point ↔
      firstAuxiliary = secondAuxiliary := by
  constructor
  · intro hEqual
    exact congrArg RobinLLAuxiliaryEnrichedVisibleD9Projection.auxiliary hEqual
  · intro hAuxiliary
    subst secondAuxiliary
    rfl

end

end P0EFTJanusCommonMatterRobinLLAuxiliaryEnrichedD9Projection4D
end JanusFormal
