import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D

/-!
The active quotient as the image of the global-matter-enriched D9 encoding.
This is an equivalence of data packets only, not a differential D9 complex.
-/

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLActiveQuotientD9ImageEquiv4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

/-- Precisely the enriched D9 packets obtained from active directions. -/
def ActiveD9Image
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :=
  Set.range (activeEmbedding period hPeriod fields sector column point)

/-- An active direction is equivalent to its enriched D9 image packet. -/
def activeDirectionD9ImageEquiv
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    ActiveDirection period hPeriod ≃ ActiveD9Image period hPeriod fields sector column point where
  toFun direction := ⟨activeEmbedding period hPeriod fields sector column point direction,
    ⟨direction, rfl⟩⟩
  invFun packet := toActiveDirection period hPeriod packet.1
  left_inv direction := toActiveDirection_activeEmbedding period hPeriod fields sector column point direction
  right_inv packet := by
    rcases packet.property with ⟨direction, h⟩
    apply Subtype.ext
    change activeEmbedding period hPeriod fields sector column point
      (toActiveDirection period hPeriod packet.1) = packet.1
    rw [← h]
    simp

/-- The exact active quotient is equivalent to the image of active D9 packets. -/
def activeQuotientD9ImageEquiv
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    ActiveQuotient period hPeriod ≃ ActiveD9Image period hPeriod fields sector column point :=
  (activeQuotientEquiv period hPeriod).trans
    (activeDirectionD9ImageEquiv period hPeriod fields sector column point)

@[simp] theorem activeQuotientD9ImageEquiv_mk
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (direction : P0EFTJanusFullMatterRobinLLDirections4D.FullMatterRobinLLDirections
      period hPeriod) :
    (activeQuotientD9ImageEquiv period hPeriod fields sector column point ⟦direction⟧).1 =
      activeEmbedding period hPeriod fields sector column point
        (activeProjection period hPeriod direction) := rfl

@[simp] theorem activeQuotientD9ImageEquiv_inverse
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (packet : ActiveD9Image period hPeriod fields sector column point) :
    (activeQuotientD9ImageEquiv period hPeriod fields sector column point).symm packet =
      (activeQuotientEquiv period hPeriod).symm
        (toActiveDirection period hPeriod packet.1) := rfl

end
end P0EFTJanusMatterRobinFullLLActiveQuotientD9ImageEquiv4D
end JanusFormal
