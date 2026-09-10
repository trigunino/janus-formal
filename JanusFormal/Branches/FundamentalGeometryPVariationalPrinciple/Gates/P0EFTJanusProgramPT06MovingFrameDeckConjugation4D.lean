import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFixedFrameDeckData4D

/-!
# Moving-frame conjugation of the complete physical deck action

Gate896 gives the unconditional deck action on all eleven physical value
components in the canonical fixed product frame.  A moving trivialization is
represented here by a linear equivalence from its coefficient fiber to that
fixed fiber at every cover point.  Conjugating by the source and target
trivializations gives the corresponding moving-frame transport.

The construction is valid over any integer action and therefore applies to
the actual fixed-throat cover.  Identity, composition, both inverse laws, and
the conjugacy square are proved without an equivariance assumption on the
chosen trivialization.

The jet construction is deliberately the coefficientwise, spatially frozen
prolongation of that value transition.  Its compatibility square and formal
total-derivative law are proved.  Existing arbitrary-frame atlas gates have
local first- and second-order semidirect transitions, but do not yet provide
a global deck-compatible trivialization of the complete physical carrier or
an identification with the T06 multi-index tower.  Consequently this gate
does not identify its frozen prolongation with those varying-frame jets.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06MovingFrameDeckConjugation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualReducedDeckJetProlongation4D
open P0EFTJanusProgramPT06CanonicalFixedFrameDeckData4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D

universe u

/-- The actual fixed-throat cover is one instance of the base used below. -/
abbrev ProgramPT06ActualFixedThroatCover4D
    (period : Real) (hPeriod : Ne period 0) :=
  MappingTorusCover (fixedEquatorData period hPeriod)

/-- A moving coefficient frame, expressed as a map to the canonical complete
physical value fiber at every base point. -/
structure ProgramPT06MovingPhysicalTrivialization4D (Base : Type u) where
  toFixed : Base -> ActualPhysicalValueProductFiber ≃ₗ[Real]
    ActualPhysicalValueProductFiber

variable {Base : Type u} [AddAction Int Base]

/-- The target cover point of an integer deck displacement. -/
def programPT06MovingFrameDeckPoint
    (winding : Int) (point : Base) : Base :=
  VAdd.vadd winding point

@[simp] theorem programPT06MovingFrameDeckPoint_zero (point : Base) :
    programPT06MovingFrameDeckPoint 0 point = point := by
  exact zero_vadd Int point

theorem programPT06MovingFrameDeckPoint_add
    (first second : Int) (point : Base) :
    programPT06MovingFrameDeckPoint (first + second) point =
      programPT06MovingFrameDeckPoint first
        (programPT06MovingFrameDeckPoint second point) := by
  exact add_vadd first second point

/-! ## Value transport -/

/-- The canonical eleven-component action transported from the source moving
frame to the target moving frame. -/
def programPT06ActualPhysicalMovingFrameValueDeckAction
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base)
    (value : ActualPhysicalValueProductFiber) :
    ActualPhysicalValueProductFiber :=
  (trivialization.toFixed
      (programPT06MovingFrameDeckPoint winding point)).symm
    (programPT06ActualPhysicalCanonicalValueDeckAction choice winding
      (trivialization.toFixed point value))

/-- The defining transition square commutes exactly. -/
theorem programPT06ActualPhysicalMovingFrameValueDeckAction_toFixed
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base)
    (value : ActualPhysicalValueProductFiber) :
    trivialization.toFixed
        (programPT06MovingFrameDeckPoint winding point)
        (programPT06ActualPhysicalMovingFrameValueDeckAction
          trivialization choice winding point value) =
      programPT06ActualPhysicalCanonicalValueDeckAction choice winding
        (trivialization.toFixed point value) := by
  simp [programPT06ActualPhysicalMovingFrameValueDeckAction]

@[simp] theorem programPT06ActualPhysicalMovingFrameValueDeckAction_zero
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (point : Base)
    (value : ActualPhysicalValueProductFiber) :
    programPT06ActualPhysicalMovingFrameValueDeckAction
        trivialization choice 0 point value = value := by
  simp [programPT06ActualPhysicalMovingFrameValueDeckAction]

theorem programPT06ActualPhysicalMovingFrameValueDeckAction_add
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (first second : Int) (point : Base)
    (value : ActualPhysicalValueProductFiber) :
    programPT06ActualPhysicalMovingFrameValueDeckAction trivialization choice
        (first + second) point value =
      programPT06ActualPhysicalMovingFrameValueDeckAction trivialization choice
        first (programPT06MovingFrameDeckPoint second point)
        (programPT06ActualPhysicalMovingFrameValueDeckAction trivialization
          choice second point value) := by
  simp only [programPT06ActualPhysicalMovingFrameValueDeckAction,
    programPT06MovingFrameDeckPoint_add,
    programPT06ActualPhysicalCanonicalValueDeckAction_add,
    LinearEquiv.apply_symm_apply]

theorem programPT06ActualPhysicalMovingFrameValueDeckAction_inverse_left
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base)
    (value : ActualPhysicalValueProductFiber) :
    programPT06ActualPhysicalMovingFrameValueDeckAction trivialization choice
        (-winding) (programPT06MovingFrameDeckPoint winding point)
        (programPT06ActualPhysicalMovingFrameValueDeckAction trivialization
          choice winding point value) = value := by
  calc
    _ = programPT06ActualPhysicalMovingFrameValueDeckAction trivialization
        choice ((-winding) + winding) point value :=
      (programPT06ActualPhysicalMovingFrameValueDeckAction_add
        trivialization choice (-winding) winding point value).symm
    _ = value := by simp

theorem programPT06ActualPhysicalMovingFrameValueDeckAction_inverse_right
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base)
    (value : ActualPhysicalValueProductFiber) :
    programPT06ActualPhysicalMovingFrameValueDeckAction trivialization choice
        winding (programPT06MovingFrameDeckPoint (-winding) point)
        (programPT06ActualPhysicalMovingFrameValueDeckAction trivialization
          choice (-winding) point value) = value := by
  calc
    _ = programPT06ActualPhysicalMovingFrameValueDeckAction trivialization
        choice (winding + (-winding)) point value :=
      (programPT06ActualPhysicalMovingFrameValueDeckAction_add
        trivialization choice winding (-winding) point value).symm
    _ = value := by simp

/-! ## Frozen coefficientwise jet transport -/

/-- Coefficientwise transport of the moving-frame value action. -/
def programPT06ActualPhysicalMovingFrameJetDeckAction
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order :=
  programPT06ThroatSpatialJetProlongation
    (programPT06ActualPhysicalMovingFrameValueDeckAction
      trivialization choice winding point) order jet

/-- Coefficientwise application of the moving frame to a formal jet. -/
def programPT06ActualPhysicalMovingFrameJetToFixed
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (point : Base) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order :=
  programPT06ThroatSpatialJetProlongation
    (trivialization.toFixed point) order jet

/-- The coefficientwise jet transition is exactly conjugate to Gate896's
canonical jet action. -/
theorem programPT06ActualPhysicalMovingFrameJetDeckAction_toFixed
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    programPT06ActualPhysicalMovingFrameJetToFixed trivialization
        (programPT06MovingFrameDeckPoint winding point) order
        (programPT06ActualPhysicalMovingFrameJetDeckAction trivialization
          choice winding point order jet) =
      programPT06ActualPhysicalCanonicalJetDeckAction choice winding order
        (programPT06ActualPhysicalMovingFrameJetToFixed trivialization
          point order jet) := by
  funext index
  exact programPT06ActualPhysicalMovingFrameValueDeckAction_toFixed
    trivialization choice winding point (jet index)

@[simp] theorem programPT06ActualPhysicalMovingFrameJetDeckAction_zero
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (point : Base) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    programPT06ActualPhysicalMovingFrameJetDeckAction trivialization choice
        0 point order jet = jet := by
  funext index
  exact programPT06ActualPhysicalMovingFrameValueDeckAction_zero
    trivialization choice point (jet index)

theorem programPT06ActualPhysicalMovingFrameJetDeckAction_add
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (first second : Int) (point : Base)
    (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    programPT06ActualPhysicalMovingFrameJetDeckAction trivialization choice
        (first + second) point order jet =
      programPT06ActualPhysicalMovingFrameJetDeckAction trivialization choice
        first (programPT06MovingFrameDeckPoint second point) order
        (programPT06ActualPhysicalMovingFrameJetDeckAction trivialization
          choice second point order jet) := by
  funext index
  exact programPT06ActualPhysicalMovingFrameValueDeckAction_add
    trivialization choice first second point (jet index)

theorem programPT06ActualPhysicalMovingFrameJetDeckAction_inverse_left
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    programPT06ActualPhysicalMovingFrameJetDeckAction trivialization choice
        (-winding) (programPT06MovingFrameDeckPoint winding point) order
        (programPT06ActualPhysicalMovingFrameJetDeckAction trivialization
          choice winding point order jet) = jet := by
  funext index
  exact programPT06ActualPhysicalMovingFrameValueDeckAction_inverse_left
    trivialization choice winding point (jet index)

theorem programPT06ActualPhysicalMovingFrameJetDeckAction_inverse_right
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    programPT06ActualPhysicalMovingFrameJetDeckAction trivialization choice
        winding (programPT06MovingFrameDeckPoint (-winding) point) order
        (programPT06ActualPhysicalMovingFrameJetDeckAction trivialization
          choice (-winding) point order jet) = jet := by
  funext index
  exact programPT06ActualPhysicalMovingFrameValueDeckAction_inverse_right
    trivialization choice winding point (jet index)

theorem programPT06ActualPhysicalMovingFrameJetDeckAction_commutes_truncation
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base)
    {lower higher : Nat} (hOrder : lower <= higher)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber higher) :
    truncateThroatSpatialMultiindexJet hOrder
        (programPT06ActualPhysicalMovingFrameJetDeckAction trivialization
          choice winding point higher jet) =
      programPT06ActualPhysicalMovingFrameJetDeckAction trivialization choice
        winding point lower
        (truncateThroatSpatialMultiindexJet hOrder jet) := by
  exact programPT06ThroatSpatialJetProlongation_commutes_truncation
    (programPT06ActualPhysicalMovingFrameValueDeckAction
      trivialization choice winding point) hOrder jet

theorem programPT06ActualPhysicalMovingFrameJetDeckAction_commutes_totalDerivative
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base)
    {order : Nat} (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber (order + 1)) :
    throatSpatialTotalDerivative direction
        (programPT06ActualPhysicalMovingFrameJetDeckAction trivialization
          choice winding point (order + 1) jet) =
      programPT06ActualPhysicalMovingFrameJetDeckAction trivialization choice
        winding point order
        (throatSpatialTotalDerivative direction jet) := by
  exact programPT06ThroatSpatialJetProlongation_commutes_totalDerivative
    (programPT06ActualPhysicalMovingFrameValueDeckAction
      trivialization choice winding point) direction jet

omit [AddAction Int Base] in
/-- A frozen moving-frame trivialization itself commutes with the formal
spatial total derivative. -/
theorem programPT06ActualPhysicalMovingFrameJetToFixed_commutes_totalDerivative
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (point : Base) {order : Nat} (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber (order + 1)) :
    throatSpatialTotalDerivative direction
        (programPT06ActualPhysicalMovingFrameJetToFixed trivialization point
          (order + 1) jet) =
      programPT06ActualPhysicalMovingFrameJetToFixed trivialization point order
        (throatSpatialTotalDerivative direction jet) := by
  exact programPT06ThroatSpatialJetProlongation_commutes_totalDerivative
    (trivialization.toFixed point) direction jet

end
end P0EFTJanusProgramPT06MovingFrameDeckConjugation4D
end JanusFormal
