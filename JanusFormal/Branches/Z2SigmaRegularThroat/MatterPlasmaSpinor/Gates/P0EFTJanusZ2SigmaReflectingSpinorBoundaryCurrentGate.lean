import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaSpinorBoundaryProjectionMapGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaReflectingSpinorBoundaryCurrentGate

set_option autoImplicit false

structure ReflectingSpinorBoundaryCurrentGate where
  mitBagBoundaryCurrentBibliographyChecked : Prop
  localReflectingBoundaryConditionDeclared : Prop
  sigmaBoundaryVariationImported : Prop
  spinorBoundaryProjectionMapGateImported : Prop
  normalCliffordActionRequired : Prop
  noFreeBoundaryPhase : Prop
  observationalFitForbidden : Prop
  spinorBoundaryProjectionMapReady : Prop
  z2NormalOrientationReady : Prop
  projectionIdempotentReady : Prop
  projectionSelfAdjointReady : Prop
  localReflectingBoundaryConditionDerived : Prop
  localBoundaryLeakageZeroDerived : Prop
  reflectingBoundaryConditionDerived : Prop
  boundaryLeakageZeroDerived : Prop
  normalDiracCurrentZeroDerived : Prop

def reflectingSpinorBoundaryCurrentLedgerDeclared
    (g : ReflectingSpinorBoundaryCurrentGate) : Prop :=
  g.mitBagBoundaryCurrentBibliographyChecked /\
  g.localReflectingBoundaryConditionDeclared /\
  g.sigmaBoundaryVariationImported /\
  g.spinorBoundaryProjectionMapGateImported /\
  g.normalCliffordActionRequired /\
  g.noFreeBoundaryPhase /\
  g.observationalFitForbidden

def localNormalDiracCurrentZeroReady
    (g : ReflectingSpinorBoundaryCurrentGate) : Prop :=
  reflectingSpinorBoundaryCurrentLedgerDeclared g /\
  g.z2NormalOrientationReady /\
  g.projectionIdempotentReady /\
  g.projectionSelfAdjointReady /\
  g.localReflectingBoundaryConditionDerived /\
  g.localBoundaryLeakageZeroDerived

def normalDiracCurrentZeroReady
    (g : ReflectingSpinorBoundaryCurrentGate) : Prop :=
  reflectingSpinorBoundaryCurrentLedgerDeclared g /\
  g.spinorBoundaryProjectionMapReady /\
  g.z2NormalOrientationReady /\
  g.projectionIdempotentReady /\
  g.projectionSelfAdjointReady /\
  g.reflectingBoundaryConditionDerived /\
  g.boundaryLeakageZeroDerived /\
  g.normalDiracCurrentZeroDerived

theorem normal_current_zero_requires_projection_map
    (g : ReflectingSpinorBoundaryCurrentGate)
    (hReady : normalDiracCurrentZeroReady g) :
    g.spinorBoundaryProjectionMapReady := by
  exact hReady.2.1

theorem normal_current_zero_requires_no_free_phase
    (g : ReflectingSpinorBoundaryCurrentGate)
    (hReady : normalDiracCurrentZeroReady g) :
    g.noFreeBoundaryPhase := by
  exact hReady.1.2.2.2.2.2.1

theorem local_zero_does_not_claim_global_projection
    (g : ReflectingSpinorBoundaryCurrentGate)
    (_hLocal : localNormalDiracCurrentZeroReady g)
    (hProjection : g.spinorBoundaryProjectionMapReady) :
    g.spinorBoundaryProjectionMapReady := by
  exact hProjection

end P0EFTJanusZ2SigmaReflectingSpinorBoundaryCurrentGate
end JanusFormal
