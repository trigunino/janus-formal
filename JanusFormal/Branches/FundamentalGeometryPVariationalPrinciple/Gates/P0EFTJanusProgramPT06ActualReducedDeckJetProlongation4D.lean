import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualOrientedGaussThroatLowOrderDeckOrbit4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D

/-!
# Actual reduced deck action on the spatial jet tower

The physical nonorientable deck involution already constructed on the actual
oriented Gauss throat acts on the reduced `(II, F)` carrier by reversing the
normal component of `II` and preserving `F`.  This gate prolongs that exact
action coefficientwise to every finite spatial Finsupp jet order, including
the `J²` and `J⁴` carriers used by T06.

The prolongation commutes definitionally with truncation and formal total
derivatives and remains involutive.  Its scope is deliberately the physical
reduced `(II, F)` carrier: the imported deck-orbit gate explicitly does not
construct a deck action on the complete fixed-frame eleven-component carrier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualReducedDeckJetProlongation4D

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusLowOrderStructuredBackground
open P0EFTJanusEuclideanStructuredJetActionGroupoidRealization
open P0EFTJanusProgramPActualOrientedGaussThroatLowOrderDeckOrbit4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D

universe u

/-- Coefficientwise prolongation of a fiber endomorphism to a finite spatial
multi-index jet. -/
def programPT06ThroatSpatialJetProlongation
    {Fiber : Type u} (action : Fiber → Fiber) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber order) :
    TruncatedThroatSpatialMultiindexJet Fiber order :=
  fun index => action (jet index)

/-- Coefficientwise prolongation commutes with every jet truncation. -/
theorem programPT06ThroatSpatialJetProlongation_commutes_truncation
    {Fiber : Type u} (action : Fiber → Fiber)
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber higher) :
    truncateThroatSpatialMultiindexJet hOrder
        (programPT06ThroatSpatialJetProlongation action higher jet) =
      programPT06ThroatSpatialJetProlongation action lower
        (truncateThroatSpatialMultiindexJet hOrder jet) := by
  rfl

/-- Coefficientwise prolongation commutes with every formal spatial total
derivative. -/
theorem programPT06ThroatSpatialJetProlongation_commutes_totalDerivative
    {Fiber : Type u} (action : Fiber → Fiber) {order : Nat}
    (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (order + 1)) :
    throatSpatialTotalDerivative direction
        (programPT06ThroatSpatialJetProlongation action (order + 1) jet) =
      programPT06ThroatSpatialJetProlongation action order
        (throatSpatialTotalDerivative direction jet) := by
  rfl

/-- The exact reduced physical carrier on which the existing nonorientable
deck action is proved. -/
abbrev ActualOrientedGaussReducedFiber :=
  LowOrderReducedData EuclideanR3 Real

/-- Fiber action induced by the already constructed physical normal-reversing
deck frame. -/
def programPT06ActualOrientedGaussReducedDeckAction
    (data : ActualOrientedGaussReducedFiber) :
    ActualOrientedGaussReducedFiber :=
  actualOrientedGaussThroatDeckSpinCFrame • data

/-- The physical reduced deck action is an involution. -/
theorem programPT06ActualOrientedGaussReducedDeckAction_involutive
    (data : ActualOrientedGaussReducedFiber) :
    programPT06ActualOrientedGaussReducedDeckAction
        (programPT06ActualOrientedGaussReducedDeckAction data) = data := by
  change actualOrientedGaussThroatDeckSpinCFrame •
      (actualOrientedGaussThroatDeckSpinCFrame • data) = data
  rw [← mul_smul, actualOrientedGaussThroatDeckSpinCFrame_mul_self, one_smul]

/-- Coefficientwise physical deck action on every finite spatial Finsupp jet
order. -/
def programPT06ActualOrientedGaussReducedJetDeckAction
    (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualOrientedGaussReducedFiber order) :
    TruncatedThroatSpatialMultiindexJet
      ActualOrientedGaussReducedFiber order :=
  programPT06ThroatSpatialJetProlongation
    programPT06ActualOrientedGaussReducedDeckAction order jet

/-- The prolonged physical deck action is involutive at every jet order. -/
theorem programPT06ActualOrientedGaussReducedJetDeckAction_involutive
    (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualOrientedGaussReducedFiber order) :
    programPT06ActualOrientedGaussReducedJetDeckAction order
        (programPT06ActualOrientedGaussReducedJetDeckAction order jet) = jet := by
  funext index
  exact programPT06ActualOrientedGaussReducedDeckAction_involutive (jet index)

/-- The prolonged physical deck action commutes with every formal total
derivative, in particular along `J⁴ → J³ → J²`. -/
theorem programPT06ActualOrientedGaussReducedJetDeckAction_commutes_totalDerivative
    {order : Nat} (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualOrientedGaussReducedFiber (order + 1)) :
    throatSpatialTotalDerivative direction
        (programPT06ActualOrientedGaussReducedJetDeckAction (order + 1) jet) =
      programPT06ActualOrientedGaussReducedJetDeckAction order
        (throatSpatialTotalDerivative direction jet) := by
  exact programPT06ThroatSpatialJetProlongation_commutes_totalDerivative
    programPT06ActualOrientedGaussReducedDeckAction direction jet

/-- The `J⁴` action restricts exactly to the `J²` action. -/
theorem programPT06ActualOrientedGaussReducedJetDeckAction_J4_to_J2
    (jet : ThroatSpatialMultiindexJet4 ActualOrientedGaussReducedFiber) :
    truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4)
        (programPT06ActualOrientedGaussReducedJetDeckAction 4 jet) =
      programPT06ActualOrientedGaussReducedJetDeckAction 2
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) := by
  exact programPT06ThroatSpatialJetProlongation_commutes_truncation
    programPT06ActualOrientedGaussReducedDeckAction (by omega) jet

end
end P0EFTJanusProgramPT06ActualReducedDeckJetProlongation4D
end JanusFormal
