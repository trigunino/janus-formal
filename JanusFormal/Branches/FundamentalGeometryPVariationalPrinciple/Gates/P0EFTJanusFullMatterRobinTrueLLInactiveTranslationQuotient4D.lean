import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveTranslationInvariants4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveTranslationQuotient4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationAction4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Setoid of the additive inactive-translation orbits. This is only an
ensemblist quotient, not a gauge or topological quotient. -/
def inactiveTranslationSetoid : Setoid (FullMatterRobinLLDirections period hPeriod) where
  r := SameInactiveTranslationOrbit period hPeriod
  iseqv :=
    { refl := fun direction =>
        (sameInactiveTranslationOrbit_iff_activeProjection_eq period hPeriod direction direction).2 rfl
      symm := fun {first second} h =>
        (sameInactiveTranslationOrbit_iff_activeProjection_eq period hPeriod second first).2
          ((sameInactiveTranslationOrbit_iff_activeProjection_eq period hPeriod first second).1 h).symm
      trans := fun {first second third} hFirst hSecond =>
        (sameInactiveTranslationOrbit_iff_activeProjection_eq period hPeriod first third).2
          (((sameInactiveTranslationOrbit_iff_activeProjection_eq period hPeriod first second).1 hFirst).trans
            ((sameInactiveTranslationOrbit_iff_activeProjection_eq period hPeriod second third).1 hSecond)) }

abbrev InactiveTranslationQuotient :=
  Quotient (inactiveTranslationSetoid period hPeriod)

def inactiveTranslationMk (direction : FullMatterRobinLLDirections period hPeriod) :
    InactiveTranslationQuotient period hPeriod :=
  Quotient.mk (inactiveTranslationSetoid period hPeriod) direction

def inactiveTranslationQuotientToActiveDirection :
    InactiveTranslationQuotient period hPeriod → ActiveDirection period hPeriod :=
  Quotient.lift (activeProjection period hPeriod) (by
    intro first second hOrbit
    exact (sameInactiveTranslationOrbit_iff_activeProjection_eq period hPeriod first second).1 hOrbit)

@[simp] theorem inactiveTranslationQuotientToActiveDirection_mk
    (direction : FullMatterRobinLLDirections period hPeriod) :
    inactiveTranslationQuotientToActiveDirection period hPeriod
      (inactiveTranslationMk period hPeriod direction) = activeProjection period hPeriod direction := rfl

/-- Explicit set equivalence from inactive-translation classes to active
readings. -/
def inactiveTranslationQuotientEquivActiveDirection :
    InactiveTranslationQuotient period hPeriod ≃ ActiveDirection period hPeriod where
  toFun := inactiveTranslationQuotientToActiveDirection period hPeriod
  invFun active := inactiveTranslationMk period hPeriod
    (activeRepresentative period hPeriod active)
  left_inv quotient := by
    refine Quotient.inductionOn quotient ?_
    intro direction
    change inactiveTranslationMk period hPeriod
        (activeRepresentative period hPeriod (activeProjection period hPeriod direction)) =
      inactiveTranslationMk period hPeriod direction
    apply Quotient.sound
    apply (sameInactiveTranslationOrbit_iff_activeProjection_eq period hPeriod _ _).2
    simp
  right_inv active := by
    change activeProjection period hPeriod (activeRepresentative period hPeriod active) = active
    exact activeProjection_representative period hPeriod active

/-- The same set quotient is explicitly equivalent to the pre-existing active
quotient. No topology is placed on either side here. -/
def inactiveTranslationQuotientEquivActiveQuotient :
    InactiveTranslationQuotient period hPeriod ≃ ActiveQuotient period hPeriod :=
  (inactiveTranslationQuotientEquivActiveDirection period hPeriod).trans
    (activeQuotientEquiv period hPeriod).symm

/-- The canonical projection commutes with the equivalence to active
directions. -/
theorem inactiveTranslation_projection_commutes_activeDirection
    (direction : FullMatterRobinLLDirections period hPeriod) :
    inactiveTranslationQuotientEquivActiveDirection period hPeriod
        (inactiveTranslationMk period hPeriod direction) =
      activeProjection period hPeriod direction := rfl

/-- It also commutes with the canonical class in `ActiveQuotient`. -/
theorem inactiveTranslation_projection_commutes_activeQuotient
    (direction : FullMatterRobinLLDirections period hPeriod) :
    inactiveTranslationQuotientEquivActiveQuotient period hPeriod
        (inactiveTranslationMk period hPeriod direction) =
      (⟦direction⟧ : ActiveQuotient period hPeriod) := by
  apply (activeQuotientEquiv period hPeriod).injective
  simp [inactiveTranslationQuotientEquivActiveQuotient,
    inactiveTranslationQuotientEquivActiveDirection]

end
end P0EFTJanusFullMatterRobinTrueLLInactiveTranslationQuotient4D
end JanusFormal
