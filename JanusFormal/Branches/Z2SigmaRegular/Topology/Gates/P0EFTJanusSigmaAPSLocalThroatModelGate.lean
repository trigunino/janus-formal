namespace JanusFormal
namespace P0EFTJanusSigmaAPSLocalThroatModelGate

set_option autoImplicit false

structure SigmaAPSLocalThroatModelGate where
  sigmaCompactBoundaryDeclared : Prop
  sigmaOrientedLocalModelDeclared : Prop
  sigmaSpinLocalModelDeclared : Prop
  inducedPinStructureAvailableLocally : Prop
  apsBoundaryProjectorAvailableLocally : Prop
  fredholmDomainAvailableLocally : Prop
  etaZeroModeCancellationDeferredToEtaGate : Prop
  parityAnomalyCancellationGlobalClosed : Prop
  sigmaApsLocalThroatModelClosed : Prop
  sigmaApsBoundaryPinLiftClosed : Prop

def sigmaApsLocalPackageClosed
    (g : SigmaAPSLocalThroatModelGate) : Prop :=
  g.sigmaCompactBoundaryDeclared /\
  g.sigmaOrientedLocalModelDeclared /\
  g.sigmaSpinLocalModelDeclared /\
  g.inducedPinStructureAvailableLocally /\
  g.apsBoundaryProjectorAvailableLocally /\
  g.fredholmDomainAvailableLocally /\
  g.sigmaApsLocalThroatModelClosed

def sigmaApsLocalClosedGlobalOpen
    (g : SigmaAPSLocalThroatModelGate) : Prop :=
  sigmaApsLocalPackageClosed g /\
  g.etaZeroModeCancellationDeferredToEtaGate /\
  Not g.parityAnomalyCancellationGlobalClosed /\
  Not g.sigmaApsBoundaryPinLiftClosed

theorem local_throat_model_does_not_close_global_aps_pin_lift
    (g : SigmaAPSLocalThroatModelGate)
    (h : sigmaApsLocalClosedGlobalOpen g) :
    Not g.sigmaApsBoundaryPinLiftClosed := by
  exact h.2.2.2

theorem local_throat_model_supplies_projector_and_fredholm_domain
    (g : SigmaAPSLocalThroatModelGate)
    (h : sigmaApsLocalPackageClosed g) :
    g.apsBoundaryProjectorAvailableLocally /\ g.fredholmDomainAvailableLocally := by
  rcases h with ⟨_, _, _, _, hProjector, hFredholm, _⟩
  exact And.intro hProjector hFredholm

end P0EFTJanusSigmaAPSLocalThroatModelGate
end JanusFormal
