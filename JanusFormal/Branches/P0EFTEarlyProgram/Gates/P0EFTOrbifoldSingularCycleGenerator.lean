import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldZ2HolonomyUnit
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldZ2GroupLaw

namespace JanusFormal
namespace P0EFTOrbifoldSingularCycleGenerator

set_option autoImplicit false

inductive SingularCycle where
  | aroundSigma : SingularCycle

def cycleToZ2Element :
    SingularCycle -> P0EFTOrbifoldZ2GroupLaw.Z2Element
  | SingularCycle.aroundSigma => P0EFTOrbifoldZ2GroupLaw.Z2Element.generator

theorem around_sigma_maps_to_z2_generator :
    cycleToZ2Element SingularCycle.aroundSigma =
      P0EFTOrbifoldZ2GroupLaw.Z2Element.generator := by
  rfl

structure SingularCycleGeneratorTransport where
  singularCycleAroundSigmaDefined : Prop
  quotientProjectionToZ2Defined : Prop
  aroundSigmaMapsToGenerator : Prop

def singularCycleRepresentsGeneratorDerived
    (t : SingularCycleGeneratorTransport) : Prop :=
  t.singularCycleAroundSigmaDefined /\
  t.quotientProjectionToZ2Defined /\
  t.aroundSigmaMapsToGenerator

theorem singular_cycle_generator_transport_supplies_holonomy_cycle
    (t : SingularCycleGeneratorTransport)
    (u : P0EFTOrbifoldZ2HolonomyUnit.OrbifoldZ2HolonomyUnit)
    (_hCycle : singularCycleRepresentsGeneratorDerived t)
    (hGen : u.z2GeneratorDefined)
    (hOrder : u.z2GeneratorOrderTwo)
    (hCycleRep : u.singularCycleRepresentsZ2Generator)
    (hUnit : u.holonomyUnitFixedByGenerator) :
    P0EFTOrbifoldZ2HolonomyUnit.z2HolonomyUnitClosed u := by
  unfold P0EFTOrbifoldZ2HolonomyUnit.z2HolonomyUnitClosed
  exact And.intro hGen (And.intro hOrder (And.intro hCycleRep hUnit))

theorem missing_quotient_projection_blocks_cycle_generator
    (t : SingularCycleGeneratorTransport)
    (hMissing : Not t.quotientProjectionToZ2Defined) :
    Not (singularCycleRepresentsGeneratorDerived t) := by
  intro h
  exact hMissing h.right.left

end P0EFTOrbifoldSingularCycleGenerator
end JanusFormal
