namespace JanusFormal
namespace P0EFTJanusZ2SigmaAbstractTensorTransportBianchiGate

set_option autoImplicit false

structure AbstractTensorTransportBianchiGate where
  mixedTransportMapsDeclared : Prop
  transportMinusToPlusDeclared : Prop
  transportPlusToMinusDeclared : Prop
  determinantFactorsDeclared : Prop
  coupledRhsPlusDeclared : Prop
  coupledRhsMinusDeclared : Prop
  noQCrossDeterminantShortcut : Prop
  noNaiveTensorCopyShortcut : Prop
  plusTransportCompatibility : Prop
  minusTransportCompatibility : Prop
  sameBridgeForStressAndOpticsDeclared : Prop
  plusBianchiResidualVanishes : Prop
  minusBianchiResidualVanishes : Prop
  formalBianchiImplicationReady : Prop

def tensorTransportLedgerDeclared
    (g : AbstractTensorTransportBianchiGate) : Prop :=
  g.mixedTransportMapsDeclared /\
  g.transportMinusToPlusDeclared /\
  g.transportPlusToMinusDeclared /\
  g.determinantFactorsDeclared /\
  g.coupledRhsPlusDeclared /\
  g.coupledRhsMinusDeclared /\
  g.noQCrossDeterminantShortcut /\
  g.noNaiveTensorCopyShortcut

def transportCompatibilityReady
    (g : AbstractTensorTransportBianchiGate) : Prop :=
  g.plusTransportCompatibility /\
  g.minusTransportCompatibility /\
  g.sameBridgeForStressAndOpticsDeclared

def abstractTensorBianchiReady
    (g : AbstractTensorTransportBianchiGate) : Prop :=
  tensorTransportLedgerDeclared g /\
  transportCompatibilityReady g /\
  g.plusBianchiResidualVanishes /\
  g.minusBianchiResidualVanishes /\
  g.formalBianchiImplicationReady

theorem abstract_transport_bianchi_gives_plus_residual_zero
    (g : AbstractTensorTransportBianchiGate)
    (hReady : abstractTensorBianchiReady g) :
    g.plusBianchiResidualVanishes := by
  exact hReady.right.right.left

theorem abstract_transport_bianchi_gives_minus_residual_zero
    (g : AbstractTensorTransportBianchiGate)
    (hReady : abstractTensorBianchiReady g) :
    g.minusBianchiResidualVanishes := by
  exact hReady.right.right.right.left

theorem abstract_transport_bianchi_requires_both_transport_maps
    (g : AbstractTensorTransportBianchiGate)
    (hReady : abstractTensorBianchiReady g) :
    g.transportMinusToPlusDeclared /\ g.transportPlusToMinusDeclared := by
  exact ⟨hReady.left.right.left, hReady.left.right.right.left⟩

theorem missing_plus_transport_compatibility_blocks_bianchi
    (g : AbstractTensorTransportBianchiGate)
    (hMissing : Not g.plusTransportCompatibility) :
    Not (abstractTensorBianchiReady g) := by
  intro hReady
  exact hMissing hReady.right.left.left

theorem missing_minus_transport_compatibility_blocks_bianchi
    (g : AbstractTensorTransportBianchiGate)
    (hMissing : Not g.minusTransportCompatibility) :
    Not (abstractTensorBianchiReady g) := by
  intro hReady
  exact hMissing hReady.right.left.right.left

end P0EFTJanusZ2SigmaAbstractTensorTransportBianchiGate
end JanusFormal
