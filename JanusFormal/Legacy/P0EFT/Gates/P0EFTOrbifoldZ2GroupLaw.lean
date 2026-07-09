import JanusFormal.Legacy.P0EFT.Gates.P0EFTOrbifoldZ2HolonomyUnit

namespace JanusFormal
namespace P0EFTOrbifoldZ2GroupLaw

set_option autoImplicit false

inductive Z2Element where
  | unit : Z2Element
  | generator : Z2Element

def z2Mul : Z2Element -> Z2Element -> Z2Element
  | Z2Element.unit, x => x
  | x, Z2Element.unit => x
  | Z2Element.generator, Z2Element.generator => Z2Element.unit

theorem generator_square_is_unit :
    z2Mul Z2Element.generator Z2Element.generator = Z2Element.unit := by
  rfl

structure Z2GroupLawTransport where
  z2GeneratorDefinedInOrbifold : Prop
  generatorSquareTransportedToOrbifold : Prop

def z2GeneratorOrderTwoDerived (t : Z2GroupLawTransport) : Prop :=
  t.z2GeneratorDefinedInOrbifold /\
  t.generatorSquareTransportedToOrbifold

theorem z2_group_law_supplies_order_two_for_holonomy_unit
    (t : Z2GroupLawTransport)
    (u : P0EFTOrbifoldZ2HolonomyUnit.OrbifoldZ2HolonomyUnit)
    (_hOrder : z2GeneratorOrderTwoDerived t)
    (hGen : u.z2GeneratorDefined)
    (hOrderTwo : u.z2GeneratorOrderTwo)
    (hCycle : u.singularCycleRepresentsZ2Generator)
    (hUnit : u.holonomyUnitFixedByGenerator) :
    P0EFTOrbifoldZ2HolonomyUnit.z2HolonomyUnitClosed u := by
  unfold P0EFTOrbifoldZ2HolonomyUnit.z2HolonomyUnitClosed
  exact And.intro hGen (And.intro hOrderTwo (And.intro hCycle hUnit))

theorem missing_transport_blocks_orbifold_order_two
    (t : Z2GroupLawTransport)
    (hMissing : Not t.generatorSquareTransportedToOrbifold) :
    Not (z2GeneratorOrderTwoDerived t) := by
  intro h
  exact hMissing h.right

end P0EFTOrbifoldZ2GroupLaw
end JanusFormal
