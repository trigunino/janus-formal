import Mathlib

namespace JanusFormal
namespace P0EFTJanusPinObstructionAudit

set_option autoImplicit false

/-- Mod-two obstruction values. -/
abbrev SWClass := ZMod 2

/-- Pin obstruction data for a nonorientable four-manifold. -/
structure PinObstructionData where
  w1Squared : SWClass
  w2 : SWClass

/-- `Pin+` obstruction. -/
def pinPlusObstruction (s : PinObstructionData) : SWClass :=
  s.w2

/-- `Pin-` obstruction. -/
def pinMinusObstruction (s : PinObstructionData) : SWClass :=
  s.w2 + s.w1Squared

/-- Vanishing `w2` and `w1^2` permits both Pin signs. -/
theorem both_pin_signs_when_both_classes_vanish
    (s : PinObstructionData)
    (hW2 : s.w2 = 0)
    (hW1Square : s.w1Squared = 0) :
    pinPlusObstruction s = 0 /\ pinMinusObstruction s = 0 := by
  constructor
  · simpa [pinPlusObstruction] using hW2
  · simp [pinMinusObstruction, hW2, hW1Square]

/-- The `RP4` pattern `w2=0`, `w1^2=1` permits `Pin+` but obstructs `Pin-`. -/
theorem rp4_pattern_is_pin_plus_only
    (s : PinObstructionData)
    (hW2 : s.w2 = 0)
    (hW1Square : s.w1Squared = 1) :
    pinPlusObstruction s = 0 /\ pinMinusObstruction s ≠ 0 := by
  constructor
  · simpa [pinPlusObstruction] using hW2
  · simp [pinMinusObstruction, hW2, hW1Square]

/--
For the twisted `S3` mapping-torus candidate, the stable tangent construction
suggests `w2=0`, while its minimal mod-two CW model has no degree-two class and
therefore suggests `w1^2=0`.  These geometric statements remain explicit proof
obligations rather than being hidden in the algebra above.
-/
structure TwistedHopfPinGeometryStatus where
  stableTangentSphereBundleModelDerived : Prop
  w2VanishesFromBaseCircleBundle : Prop
  modTwoDegreeTwoCohomologyVanishes : Prop
  w1SquareVanishes : Prop
  pinPlusStructureConstructed : Prop
  pinMinusStructureConstructed : Prop
  physicallySelectedPinSignDerived : Prop


def twistedHopfPinGeometryClosed
    (s : TwistedHopfPinGeometryStatus) : Prop :=
  s.stableTangentSphereBundleModelDerived /\
  s.w2VanishesFromBaseCircleBundle /\
  s.modTwoDegreeTwoCohomologyVanishes /\
  s.w1SquareVanishes /\
  s.pinPlusStructureConstructed /\
  s.pinMinusStructureConstructed /\
  s.physicallySelectedPinSignDerived

/-- Topology may permit both signs even though the fermionic theory selects one. -/
theorem topology_does_not_select_pin_sign_by_itself
    (s : TwistedHopfPinGeometryStatus)
    (hPlus : s.pinPlusStructureConstructed)
    (hMinus : s.pinMinusStructureConstructed)
    (hMissing : Not s.physicallySelectedPinSignDerived) :
    Not (twistedHopfPinGeometryClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2

end P0EFTJanusPinObstructionAudit
end JanusFormal
