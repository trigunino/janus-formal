import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusTwistedHopfCellularModel

namespace JanusFormal
namespace P0EFTJanusGenericPinObstruction

set_option autoImplicit false

/-- Pin obstruction classes valued in the actual degree-two coefficient group. -/
structure PinClasses (H2 : Type*) [AddCommGroup H2] where
  w1Squared : H2
  w2 : H2

/-- `Pin+` obstruction class. -/
def pinPlusObstruction
    {H2 : Type*} [AddCommGroup H2]
    (s : PinClasses H2) : H2 :=
  s.w2

/-- `Pin-` obstruction class. -/
def pinMinusObstruction
    {H2 : Type*} [AddCommGroup H2]
    (s : PinClasses H2) : H2 :=
  s.w2 + s.w1Squared

/-- If degree-two cohomology is trivial, both Pin obstruction classes vanish. -/
theorem both_pin_obstructions_vanish_of_subsingleton
    {H2 : Type*}
    [AddCommGroup H2]
    [Subsingleton H2]
    (s : PinClasses H2) :
    pinPlusObstruction s = 0 /\
      pinMinusObstruction s = 0 := by
  constructor <;> apply Subsingleton.elim

/-- Stable-tangent transport of the second Stiefel--Whitney class. -/
structure StableTangentW2Data
    (BaseH2 TotalH2 : Type*)
    [AddCommGroup BaseH2]
    [AddCommGroup TotalH2] where
  baseW2 : BaseH2
  totalW2 : TotalH2
  pullback : BaseH2 →+ TotalH2
  stableTangentLaw : totalW2 = pullback baseW2

/-- If the base has no degree-two class, stable-tangent transport forces total `w2=0`. -/
theorem stable_tangent_forces_w2_zero
    {BaseH2 TotalH2 : Type*}
    [AddCommGroup BaseH2]
    [AddCommGroup TotalH2]
    [Subsingleton BaseH2]
    (s : StableTangentW2Data BaseH2 TotalH2) :
    s.totalW2 = 0 := by
  have hBase : s.baseW2 = 0 := Subsingleton.elim _ _
  rw [s.stableTangentLaw, hBase]
  exact s.pullback.map_zero

/-- The candidate cellular degree-two group is literally a singleton. -/
theorem cellular_degree_two_group_is_subsingleton :
    Subsingleton
      P0EFTJanusTwistedHopfCellularModel.DegreeTwoModTwoCochain := by
  infer_instance

/-- In the candidate cellular model, both Pin obstruction classes vanish. -/
theorem cellular_model_has_zero_pin_obstructions
    (s : PinClasses
      P0EFTJanusTwistedHopfCellularModel.DegreeTwoModTwoCochain) :
    pinPlusObstruction s = 0 /\
      pinMinusObstruction s = 0 := by
  exact both_pin_obstructions_vanish_of_subsingleton s

/--
This closes the algebraic implication `H^2=0 -> both obstruction classes vanish`.
The remaining geometric work is to identify the cellular degree-two group with
singular cohomology of the actual mapping torus and construct the corresponding
Pin principal bundles.
-/
structure GeometricPinRealizationStatus where
  actualMappingTorusConstructed : Prop
  cellularToSingularH2ComparisonProved : Prop
  degreeTwoCohomologyVanishes : Prop
  tangentW1SquareIdentified : Prop
  tangentW2Identified : Prop
  pinPlusBundleConstructed : Prop
  pinMinusBundleConstructed : Prop
  physicalPinLiftSelected : Prop


def geometricPinRealizationClosed
    (s : GeometricPinRealizationStatus) : Prop :=
  s.actualMappingTorusConstructed /\
  s.cellularToSingularH2ComparisonProved /\
  s.degreeTwoCohomologyVanishes /\
  s.tangentW1SquareIdentified /\
  s.tangentW2Identified /\
  s.pinPlusBundleConstructed /\
  s.pinMinusBundleConstructed /\
  s.physicalPinLiftSelected

end P0EFTJanusGenericPinObstruction
end JanusFormal
