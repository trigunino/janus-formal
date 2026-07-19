import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D

/-! The active quotient is exactly the five-slot active direction space. -/

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The complete active projection descended through its exact kernel setoid. -/
def descendedActiveProjection :
    ActiveQuotient period hPeriod → ActiveDirection period hPeriod :=
  Quotient.lift (activeProjection period hPeriod) (by
    intro first second h
    exact h)

@[simp] theorem descendedActiveProjection_mk
    (direction : FullMatterRobinLLDirections period hPeriod) :
    descendedActiveProjection period hPeriod ⟦direction⟧ =
      activeProjection period hPeriod direction := by
  rfl

theorem descendedActiveProjection_injective :
    Function.Injective (descendedActiveProjection period hPeriod) := by
  intro first second h
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second =>
      apply Quotient.sound
      exact h

theorem descendedActiveProjection_surjective :
    Function.Surjective (descendedActiveProjection period hPeriod) := by
  intro active
  exact ⟨⟦activeRepresentative period hPeriod active⟧,
    activeProjection_representative period hPeriod active⟩

/-- No information is lost beyond the explicitly characterized inactive
kernel: the active quotient and active direction space are equivalent. -/
def activeQuotientEquiv :
    ActiveQuotient period hPeriod ≃ ActiveDirection period hPeriod :=
  Equiv.ofBijective (descendedActiveProjection period hPeriod)
    ⟨descendedActiveProjection_injective period hPeriod,
      descendedActiveProjection_surjective period hPeriod⟩

@[simp] theorem activeQuotientEquiv_mk
    (direction : FullMatterRobinLLDirections period hPeriod) :
    activeQuotientEquiv period hPeriod ⟦direction⟧ =
      activeProjection period hPeriod direction := by
  rfl

@[simp] theorem activeQuotientEquiv_symm_active
    (active : ActiveDirection period hPeriod) :
    (activeQuotientEquiv period hPeriod).symm active =
      ⟦activeRepresentative period hPeriod active⟧ := by
  apply (activeQuotientEquiv period hPeriod).injective
  simp only [Equiv.apply_symm_apply, activeQuotientEquiv_mk,
    activeProjection_representative]

end
end P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
end JanusFormal
