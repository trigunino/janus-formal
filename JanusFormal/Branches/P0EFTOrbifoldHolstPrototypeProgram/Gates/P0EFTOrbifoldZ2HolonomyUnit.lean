import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTOrbifoldHolonomyQuantumNormalization

namespace JanusFormal
namespace P0EFTOrbifoldZ2HolonomyUnit

set_option autoImplicit false

structure OrbifoldZ2HolonomyUnit where
  z2GeneratorDefined : Prop
  z2GeneratorOrderTwo : Prop
  singularCycleRepresentsZ2Generator : Prop
  holonomyUnitFixedByGenerator : Prop

def z2HolonomyUnitClosed (u : OrbifoldZ2HolonomyUnit) : Prop :=
  u.z2GeneratorDefined /\
  u.z2GeneratorOrderTwo /\
  u.singularCycleRepresentsZ2Generator /\
  u.holonomyUnitFixedByGenerator

theorem z2_generator_supplies_holonomy_unit
    (u : OrbifoldZ2HolonomyUnit)
    (n : P0EFTOrbifoldHolonomyQuantumNormalization.OrbifoldHolonomyQuantumNormalization)
    (_hUnit : z2HolonomyUnitClosed u)
    (hCycle : n.compactSingularCycleLoaded)
    (hGauge : n.spinConnectionGaugeFixedOnCycle)
    (hUnitChosen : n.holonomyUnitChosenByOrbifoldGenerator)
    (hWellDefined : n.fluxDividedByHolonomyUnitWellDefined) :
    P0EFTOrbifoldHolonomyQuantumNormalization.holonomyQuantumNormalizationClosed n := by
  unfold P0EFTOrbifoldHolonomyQuantumNormalization.holonomyQuantumNormalizationClosed
  exact And.intro hCycle
    (And.intro hGauge (And.intro hUnitChosen hWellDefined))

theorem missing_z2_order_two_blocks_holonomy_unit
    (u : OrbifoldZ2HolonomyUnit)
    (hMissing : Not u.z2GeneratorOrderTwo) :
    Not (z2HolonomyUnitClosed u) := by
  intro h
  exact hMissing h.right.left

theorem missing_generator_cycle_blocks_holonomy_unit
    (u : OrbifoldZ2HolonomyUnit)
    (hMissing : Not u.singularCycleRepresentsZ2Generator) :
    Not (z2HolonomyUnitClosed u) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTOrbifoldZ2HolonomyUnit
end JanusFormal
