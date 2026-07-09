namespace JanusFormal
namespace P0EFTJanusZ2SigmaHolstTorsionFluxZeroOrEquivarianceGate

set_option autoImplicit false

structure HolstTorsionFluxZeroOrEquivarianceGate where
  holstNiehYanBoundaryFluxSlotDeclared : Prop
  torsionlessNiehYanZeroIdentityRouteDeclared : Prop
  z2EquivariantHolstStressRouteDeclared : Prop
  bulkHolstStressNotClaimedFromBoundaryIdentity : Prop
  observationalFitForbidden : Prop
  torsionlessBoundaryFluxReady : Prop
  z2EquivariantHolstStressReady : Prop

def holstTorsionFluxZeroOrEquivarianceReady
    (g : HolstTorsionFluxZeroOrEquivarianceGate) : Prop :=
  g.holstNiehYanBoundaryFluxSlotDeclared /\
  g.torsionlessNiehYanZeroIdentityRouteDeclared /\
  g.z2EquivariantHolstStressRouteDeclared /\
  g.bulkHolstStressNotClaimedFromBoundaryIdentity /\
  g.observationalFitForbidden /\
  (g.torsionlessBoundaryFluxReady \/ g.z2EquivariantHolstStressReady)

theorem torsionless_boundary_flux_route_suffices_for_local_sigma_slot
    (g : HolstTorsionFluxZeroOrEquivarianceGate)
    (hDeclared :
      g.holstNiehYanBoundaryFluxSlotDeclared /\
      g.torsionlessNiehYanZeroIdentityRouteDeclared /\
      g.z2EquivariantHolstStressRouteDeclared /\
      g.bulkHolstStressNotClaimedFromBoundaryIdentity /\
      g.observationalFitForbidden)
    (hZero : g.torsionlessBoundaryFluxReady) :
    holstTorsionFluxZeroOrEquivarianceReady g := by
  rcases hDeclared with ⟨hSlot, hTorsionless, hEquiv, hScope, hNoFit⟩
  exact ⟨hSlot, hTorsionless, hEquiv, hScope, hNoFit, Or.inl hZero⟩

theorem boundary_identity_does_not_claim_bulk_stress
    (g : HolstTorsionFluxZeroOrEquivarianceGate)
    (_h : holstTorsionFluxZeroOrEquivarianceReady g) :
    g.bulkHolstStressNotClaimedFromBoundaryIdentity := by
  exact _h.2.2.2.1

end P0EFTJanusZ2SigmaHolstTorsionFluxZeroOrEquivarianceGate
end JanusFormal
