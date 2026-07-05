namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracNormalCurrentZ2CancellationGate

set_option autoImplicit false

structure DiracNormalCurrentZ2CancellationGate where
  z2SheetExchangeDeclared : Prop
  normalReversalImported : Prop
  diracCurrentTransportDeclared : Prop
  projectedNormalCurrentFormulaDeclared : Prop
  noMITBoundaryAssumptionRequiredForThisRoute : Prop
  observationalFitForbidden : Prop
  z2NormalReversalReady : Prop
  spinorProjectionMapReady : Prop
  diracCurrentZ2ParityDerived : Prop
  projectedCurrentOrientationSignFixed : Prop
  z2ProjectedNormalCurrentZeroDerived : Prop

def diracNormalCurrentZ2CancellationReady
    (g : DiracNormalCurrentZ2CancellationGate) : Prop :=
  g.z2SheetExchangeDeclared /\
  g.normalReversalImported /\
  g.diracCurrentTransportDeclared /\
  g.projectedNormalCurrentFormulaDeclared /\
  g.noMITBoundaryAssumptionRequiredForThisRoute /\
  g.observationalFitForbidden /\
  g.z2NormalReversalReady /\
  g.spinorProjectionMapReady /\
  g.diracCurrentZ2ParityDerived /\
  g.projectedCurrentOrientationSignFixed /\
  g.z2ProjectedNormalCurrentZeroDerived

theorem z2_cancellation_requires_current_parity
    (g : DiracNormalCurrentZ2CancellationGate)
    (h : diracNormalCurrentZ2CancellationReady g) :
    g.diracCurrentZ2ParityDerived := by
  exact h.2.2.2.2.2.2.2.2.1

theorem z2_cancellation_is_not_mit_boundary_assumption
    (g : DiracNormalCurrentZ2CancellationGate)
    (h : diracNormalCurrentZ2CancellationReady g) :
    g.noMITBoundaryAssumptionRequiredForThisRoute := by
  exact h.2.2.2.2.1

end P0EFTJanusZ2SigmaDiracNormalCurrentZ2CancellationGate
end JanusFormal
