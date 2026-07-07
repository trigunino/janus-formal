namespace JanusFormal
namespace P0EFTJanusZ2GlobalAlphaConditionMatrixGate

set_option autoImplicit false

structure GlobalAlphaConditionMatrixGate where
  projectiveZ2CycleDerived : Prop
  ptTransportDerived : Prop
  holonomyPhaseDerived : Prop
  actionPeriodIAlphaDerived : Prop
  chargeLatticeUnitDerived : Prop
  vacuumFunctionalVAlphaDerived : Prop
  vacuumMinimumUnique : Prop

def discreteAlphaRouteReady (g : GlobalAlphaConditionMatrixGate) : Prop :=
  g.projectiveZ2CycleDerived /\
  g.ptTransportDerived /\
  g.holonomyPhaseDerived /\
  g.actionPeriodIAlphaDerived /\
  g.chargeLatticeUnitDerived

def continuousAlphaSelectorReady (g : GlobalAlphaConditionMatrixGate) : Prop :=
  g.vacuumFunctionalVAlphaDerived /\
  g.vacuumMinimumUnique

def alphaGeneratedByGlobalCondition (g : GlobalAlphaConditionMatrixGate) : Prop :=
  discreteAlphaRouteReady g \/ continuousAlphaSelectorReady g

theorem z2_cycle_without_phase_does_not_generate_alpha
    (g : GlobalAlphaConditionMatrixGate)
    (hMissing : Not g.holonomyPhaseDerived)
    (hNoVacuum : Not (continuousAlphaSelectorReady g)) :
    Not (alphaGeneratedByGlobalCondition g) := by
  intro h
  rcases h with hDisc | hCont
  · exact hMissing hDisc.right.right.left
  · exact hNoVacuum hCont

theorem vacuum_functional_without_unique_minimum_not_selector
    (g : GlobalAlphaConditionMatrixGate)
    (hMissing : Not g.vacuumMinimumUnique) :
    Not (continuousAlphaSelectorReady g) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ2GlobalAlphaConditionMatrixGate
end JanusFormal
