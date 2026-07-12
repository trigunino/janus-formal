import Mathlib

namespace JanusFormal
namespace P0EFTJanusDeckZ4CentralExtension

set_option autoImplicit false

/-- Deck involution phase. -/
abbrev DeckPhase := ZMod 2

/-- Order-four lift phase. -/
abbrev LiftPhase := ZMod 4

/-- Reduction of an order-four phase to its deck parity. -/
def reduceToDeck (phase : LiftPhase) : DeckPhase := phase.val

/-- Reduction respects addition. -/
theorem reduce_to_deck_additive :
    ∀ first second : LiftPhase,
      reduceToDeck (first + second) =
        reduceToDeck first + reduceToDeck second := by
  native_decide

/-- The kernel is the central sign pair `0,2`. -/
theorem reduce_to_deck_kernel_iff :
    ∀ phase : LiftPhase,
      reduceToDeck phase = 0 ↔ phase = 0 \/ phase = 2 := by
  native_decide

/-- The nontrivial deck element has exactly the two quarter lifts `1,3`. -/
theorem nontrivial_deck_lifts_iff :
    ∀ phase : LiftPhase,
      reduceToDeck phase = 1 ↔ phase = 1 \/ phase = 3 := by
  native_decide

/-- A candidate additive section of the deck reduction. -/
def IsAdditiveDeckSection (section : DeckPhase → LiftPhase) : Prop :=
  (∀ first second,
    section (first + second) = section first + section second) /\
  (∀ deck, reduceToDeck (section deck) = deck)

instance isAdditiveDeckSectionDecidable
    (section : DeckPhase → LiftPhase) :
    Decidable (IsAdditiveDeckSection section) := by
  unfold IsAdditiveDeckSection
  infer_instance

/-- The central extension `Z4 -> Z2` has no additive splitting. -/
theorem deck_z4_extension_is_nonsplit :
    Not (∃ section : DeckPhase → LiftPhase,
      IsAdditiveDeckSection section) := by
  native_decide

/-- The two lifts square to the same central sign. -/
theorem two_deck_lifts_square_to_central_sign :
    (1 : LiftPhase) + 1 = 2 /\
      (3 : LiftPhase) + 3 = 2 := by
  native_decide

/-- PT/additive inversion exchanges the two nontrivial deck lifts. -/
theorem pt_exchanges_deck_lifts :
    -(1 : LiftPhase) = 3 /\
      -(3 : LiftPhase) = 1 := by
  native_decide

/--
The order-four lift is therefore not a direct product `Z2 x Z2`: it is the
nontrivial central extension in which the lifted deck generator squares to the
central sign.  This is the precise algebraic origin available for the central
Pin/fermionic `Z4`; it does not yet provide an independent bosonic internal
`Z4` or a field multiplicity.
-/
structure DeckZ4ExtensionPhysicalStatus where
  orientationDeckInvolutionConstructed : Prop
  centralSignIdentified : Prop
  nontrivialExtensionClassDerived : Prop
  nonsplittingProvedGeometrically : Prop
  liftImplementedOnPinorBundle : Prop
  ptExchangeOfLiftsDerived : Prop
  independentInternalSymmetryDistinguished : Prop


def deckZ4ExtensionPhysicalClosed
    (s : DeckZ4ExtensionPhysicalStatus) : Prop :=
  s.orientationDeckInvolutionConstructed /\
  s.centralSignIdentified /\
  s.nontrivialExtensionClassDerived /\
  s.nonsplittingProvedGeometrically /\
  s.liftImplementedOnPinorBundle /\
  s.ptExchangeOfLiftsDerived /\
  s.independentInternalSymmetryDistinguished

end P0EFTJanusDeckZ4CentralExtension
end JanusFormal
