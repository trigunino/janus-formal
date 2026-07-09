import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldZ2HolonomyUnit
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldZ2GroupLaw
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldSingularCycleGenerator

namespace JanusFormal
namespace P0EFTOrbifoldGeneratorHolonomyUnit

set_option autoImplicit false

inductive HolonomyUnit where
  | z2GeneratorUnit : HolonomyUnit

def generatorHolonomyUnit :
    P0EFTOrbifoldZ2GroupLaw.Z2Element -> HolonomyUnit
  | P0EFTOrbifoldZ2GroupLaw.Z2Element.generator => HolonomyUnit.z2GeneratorUnit
  | P0EFTOrbifoldZ2GroupLaw.Z2Element.unit => HolonomyUnit.z2GeneratorUnit

theorem z2_generator_chooses_holonomy_unit :
    generatorHolonomyUnit P0EFTOrbifoldZ2GroupLaw.Z2Element.generator =
      HolonomyUnit.z2GeneratorUnit := by
  rfl

structure GeneratorHolonomyUnitTransport where
  z2GeneratorLoaded : Prop
  singularCycleMappedToGenerator : Prop
  generatorFixesHolonomyUnit : Prop

def holonomyUnitChosenByGeneratorDerived
    (t : GeneratorHolonomyUnitTransport) : Prop :=
  t.z2GeneratorLoaded /\
  t.singularCycleMappedToGenerator /\
  t.generatorFixesHolonomyUnit

theorem generator_holonomy_unit_transport_closes_z2_unit
    (t : GeneratorHolonomyUnitTransport)
    (u : P0EFTOrbifoldZ2HolonomyUnit.OrbifoldZ2HolonomyUnit)
    (_hUnit : holonomyUnitChosenByGeneratorDerived t)
    (hGen : u.z2GeneratorDefined)
    (hOrder : u.z2GeneratorOrderTwo)
    (hCycle : u.singularCycleRepresentsZ2Generator)
    (hChosen : u.holonomyUnitFixedByGenerator) :
    P0EFTOrbifoldZ2HolonomyUnit.z2HolonomyUnitClosed u := by
  unfold P0EFTOrbifoldZ2HolonomyUnit.z2HolonomyUnitClosed
  exact And.intro hGen (And.intro hOrder (And.intro hCycle hChosen))

theorem missing_generator_fix_blocks_holonomy_unit_choice
    (t : GeneratorHolonomyUnitTransport)
    (hMissing : Not t.generatorFixesHolonomyUnit) :
    Not (holonomyUnitChosenByGeneratorDerived t) := by
  intro h
  exact hMissing h.right.right

end P0EFTOrbifoldGeneratorHolonomyUnit
end JanusFormal
