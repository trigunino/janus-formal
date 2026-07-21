import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinLLAuxiliaryEnrichedD9Projection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D

/-! A pointwise D9 packet enriched by the complete global matter direction. -/

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullMatterRobinLLAuxiliaryEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

abbrev GlobalMatterDirection :=
  SmoothQuotientField period hPeriod MatterFiber ×
    SmoothQuotientField period hPeriod MatterFiber

/-- The existing enriched D9 packet together with both global matter directions. -/
@[ext]
structure GlobalMatterEnrichedD9Projection where
  pointwise : FullRobinLLAuxiliaryVisibleD9Projection period hPeriod
  globalMatter : GlobalMatterDirection period hPeriod

def globalMatterEnrichedD9Projection
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    GlobalMatterEnrichedD9Projection period hPeriod where
  pointwise := fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields
    direction sector column point
  globalMatter := direction.common.matter

/-- Read exactly the five action-visible slots from the enriched packet. -/
def toActiveDirection (packet : GlobalMatterEnrichedD9Projection period hPeriod) :
    ActiveDirection period hPeriod where
  matter := packet.globalMatter
  robin := packet.pointwise.robin
  llField := packet.pointwise.llField
  llAuxMetric := packet.pointwise.llAuxMetric
  llMeasure := packet.pointwise.llMeasure

@[simp] theorem toActiveDirection_projection
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    toActiveDirection period hPeriod
      (globalMatterEnrichedD9Projection period hPeriod fields direction sector column point) =
      activeProjection period hPeriod direction := rfl

/-- Encode an active direction, setting precisely the action-inactive sectors to zero. -/
def activeEmbedding
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (direction : ActiveDirection period hPeriod) :
    GlobalMatterEnrichedD9Projection period hPeriod :=
  globalMatterEnrichedD9Projection period hPeriod fields
    (activeRepresentative period hPeriod direction) sector column point

@[simp] theorem toActiveDirection_activeEmbedding
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (direction : ActiveDirection period hPeriod) :
    toActiveDirection period hPeriod
      (activeEmbedding period hPeriod fields sector column point direction) = direction := by
  simp [activeEmbedding]

theorem activeEmbedding_injective
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    Function.Injective (activeEmbedding period hPeriod fields sector column point) := by
  intro first second h
  have recovered := congrArg (toActiveDirection period hPeriod) h
  simpa using recovered

end
end P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
end JanusFormal
