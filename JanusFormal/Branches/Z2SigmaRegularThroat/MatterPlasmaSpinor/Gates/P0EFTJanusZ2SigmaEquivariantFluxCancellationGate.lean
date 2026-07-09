namespace JanusFormal
namespace P0EFTJanusZ2SigmaEquivariantFluxCancellationGate

set_option autoImplicit false

structure EquivariantFluxCancellationGate where
  bibliographyChecked : Prop
  z2EquivariantEmbeddingDerived : Prop
  coorientationReady : Prop
  sigmaTangentsReady : Prop
  sigmaNormalsReady : Prop
  bulkStressPlusReady : Prop
  bulkStressMinusReady : Prop
  z2StressEquivarianceDerived : Prop
  normalReversalUnderZ2Derived : Prop
  tangentTransportUnderZ2Derived : Prop
  algebraicCancellationTheoremDeclared : Prop
  z2FluxCancellationDerived : Prop

def prerequisitesReady (g : EquivariantFluxCancellationGate) : Prop :=
  g.bibliographyChecked /\
  g.z2EquivariantEmbeddingDerived /\
  g.coorientationReady /\
  g.sigmaTangentsReady /\
  g.sigmaNormalsReady /\
  g.bulkStressPlusReady /\
  g.bulkStressMinusReady /\
  g.z2StressEquivarianceDerived /\
  g.normalReversalUnderZ2Derived /\
  g.tangentTransportUnderZ2Derived /\
  g.algebraicCancellationTheoremDeclared

def equivariantFluxCancellationReady (g : EquivariantFluxCancellationGate) : Prop :=
  prerequisitesReady g /\ g.z2FluxCancellationDerived

theorem flux_cancellation_requires_stress_equivariance
    (g : EquivariantFluxCancellationGate)
    (h : equivariantFluxCancellationReady g) :
    g.z2StressEquivarianceDerived := by
  exact h.1.2.2.2.2.2.2.2.1

theorem flux_cancellation_requires_normal_reversal
    (g : EquivariantFluxCancellationGate)
    (h : equivariantFluxCancellationReady g) :
    g.normalReversalUnderZ2Derived := by
  exact h.1.2.2.2.2.2.2.2.2.1

theorem flux_cancellation_requires_tangent_transport
    (g : EquivariantFluxCancellationGate)
    (h : equivariantFluxCancellationReady g) :
    g.tangentTransportUnderZ2Derived := by
  exact h.1.2.2.2.2.2.2.2.2.2.1

end P0EFTJanusZ2SigmaEquivariantFluxCancellationGate
end JanusFormal
