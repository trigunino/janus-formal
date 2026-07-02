import JanusFormal.P0EFTJanusZ4FullActionWardClosure

namespace JanusFormal
namespace P0EFTJanusZ4WardAtomicClosureGate

set_option autoImplicit false

structure WardAtomicClosureGate where
  currentPlusDeclared : Prop
  currentMinusDeclared : Prop
  determinantWeightedCurrentDeclared : Prop
  currentPlusCancelsWeightedMinus : Prop
  currentDivergenceVanishesGlobally : Prop
  anomalyVanishesGlobally : Prop
  wardObstructionVanishes : Prop
  wardClosureReady : Prop

def wardCurrentScaffoldReady (g : WardAtomicClosureGate) : Prop :=
  g.currentPlusDeclared /\
  g.currentMinusDeclared /\
  g.determinantWeightedCurrentDeclared /\
  g.currentPlusCancelsWeightedMinus

def wardAtomicObligationsClosed (g : WardAtomicClosureGate) : Prop :=
  wardCurrentScaffoldReady g /\
  g.currentDivergenceVanishesGlobally /\
  g.anomalyVanishesGlobally /\
  g.wardObstructionVanishes

theorem missing_global_current_divergence_blocks_ward_closure
    (g : WardAtomicClosureGate)
    (hMissing : Not g.currentDivergenceVanishesGlobally) :
    Not (wardAtomicObligationsClosed g) := by
  intro h
  exact hMissing h.right.left

theorem ward_atomic_obligations_transport_to_ready
    (g : WardAtomicClosureGate)
    (h : wardAtomicObligationsClosed g)
    (hTransport : wardAtomicObligationsClosed g -> g.wardClosureReady) :
    g.wardClosureReady := by
  exact hTransport h

end P0EFTJanusZ4WardAtomicClosureGate
end JanusFormal
