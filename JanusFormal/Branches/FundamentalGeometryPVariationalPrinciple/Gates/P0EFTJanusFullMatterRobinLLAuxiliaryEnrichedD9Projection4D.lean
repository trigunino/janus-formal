import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinLLDirections4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonCompleteSectorD9ProjectionKernel4D

/-!
# D9 data enriched by Robin, complete LL and auxiliary directions

The four actual pointwise D9 blocks are augmented with genuine Robin,
LL-field, LL auxiliary-metric, LL measure and auxiliary-sector directions.
All added data are recovered definitionally.  This is still a data-level,
pointwise projection and not a global differential D9 complex.
-/

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinLLAuxiliaryEnrichedD9Projection4D

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
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev AuxiliaryDirection :=
  SmoothQuotientField period hPeriod AuxiliaryFiber ×
    SmoothQuotientField period hPeriod AuxiliaryFiber

/-- The three genuine LL directions as one concrete product. -/
abbrev CompleteLLDirection :=
  SmoothThroatField period hPeriod LLFieldFiber ×
    (SmoothThroatField period hPeriod LLMetricFiber ×
      SmoothThroatField period hPeriod Real)

/-- Actual D9 values plus Robin, all LL slots and auxiliary data. -/
@[ext]
structure FullRobinLLAuxiliaryVisibleD9Projection where
  visible : VisibleD9Projection
  robin : SmoothThroatField period hPeriod Real
  llField : SmoothThroatField period hPeriod LLFieldFiber
  llAuxMetric : SmoothThroatField period hPeriod LLMetricFiber
  llMeasure : SmoothThroatField period hPeriod Real
  auxiliary : AuxiliaryDirection period hPeriod

/-- Projection from the full genuine direction packet. -/
def fullRobinLLAuxiliaryVisibleD9Projection
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    FullRobinLLAuxiliaryVisibleD9Projection period hPeriod where
  visible := combinedVisibleD9Projection period hPeriod fields direction.common
    sector column point
  robin := direction.robin
  llField := direction.common.ll
  llAuxMetric := direction.llAuxMetric
  llMeasure := direction.llMeasure
  auxiliary := direction.common.auxiliary

@[simp] theorem fullProjection_llField
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    (fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields direction
      sector column point).llField = direction.common.ll := rfl

@[simp] theorem fullProjection_llAuxMetric
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    (fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields direction
      sector column point).llAuxMetric = direction.llAuxMetric := rfl

@[simp] theorem fullProjection_llMeasure
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    (fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields direction
      sector column point).llMeasure = direction.llMeasure := rfl

/-- Equality is exactly equality of every old and newly added datum. -/
theorem fullRobinLLAuxiliaryVisibleD9Projection_eq_iff
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields first
        sector column point =
        fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields second
          sector column point ↔
      combinedVisibleD9Projection period hPeriod fields first.common
          sector column point =
        combinedVisibleD9Projection period hPeriod fields second.common
          sector column point ∧
      first.robin = second.robin ∧ first.common.ll = second.common.ll ∧
      first.llAuxMetric = second.llAuxMetric ∧
      first.llMeasure = second.llMeasure ∧
      first.common.auxiliary = second.common.auxiliary := by
  constructor
  · intro hEqual
    exact ⟨congrArg FullRobinLLAuxiliaryVisibleD9Projection.visible hEqual,
      congrArg FullRobinLLAuxiliaryVisibleD9Projection.robin hEqual,
      congrArg FullRobinLLAuxiliaryVisibleD9Projection.llField hEqual,
      congrArg FullRobinLLAuxiliaryVisibleD9Projection.llAuxMetric hEqual,
      congrArg FullRobinLLAuxiliaryVisibleD9Projection.llMeasure hEqual,
      congrArg FullRobinLLAuxiliaryVisibleD9Projection.auxiliary hEqual⟩
  · rintro ⟨hVisible, hRobin, hField, hMetric, hMeasure, hAuxiliary⟩
    apply FullRobinLLAuxiliaryVisibleD9Projection.ext
    · exact hVisible
    · exact hRobin
    · exact hField
    · exact hMetric
    · exact hMeasure
    · exact hAuxiliary

/-- Replace exactly the three LL directions. -/
def withCompleteLLDirection
    (direction : FullMatterRobinLLDirections period hPeriod)
    (ll : CompleteLLDirection period hPeriod) :
    FullMatterRobinLLDirections period hPeriod :=
  { direction with
    common := { direction.common with ll := ll.1 }
    llAuxMetric := ll.2.1
    llMeasure := ll.2.2 }

/-- At all other data fixed, the enriched projection is injective in the
complete three-slot LL direction. -/
theorem fullProjection_fixed_data_injective_completeLL
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (firstLL secondLL : CompleteLLDirection period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields
        (withCompleteLLDirection period hPeriod direction firstLL)
        sector column point =
      fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields
        (withCompleteLLDirection period hPeriod direction secondLL)
        sector column point ↔ firstLL = secondLL := by
  constructor
  · intro hEqual
    have hField := congrArg FullRobinLLAuxiliaryVisibleD9Projection.llField hEqual
    have hMetric := congrArg FullRobinLLAuxiliaryVisibleD9Projection.llAuxMetric hEqual
    have hMeasure := congrArg FullRobinLLAuxiliaryVisibleD9Projection.llMeasure hEqual
    rcases firstLL with ⟨firstField, firstMetric, firstMeasure⟩
    rcases secondLL with ⟨secondField, secondMetric, secondMeasure⟩
    change firstField = secondField at hField
    change firstMetric = secondMetric at hMetric
    change firstMeasure = secondMeasure at hMeasure
    subst secondField
    subst secondMetric
    subst secondMeasure
    rfl
  · intro hLL
    subst secondLL
    rfl

end

end P0EFTJanusFullMatterRobinLLAuxiliaryEnrichedD9Projection4D
end JanusFormal
