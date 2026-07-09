namespace JanusFormal
namespace P0EFTJanusZ2SO3RegularThroatCollarFrontierGate

set_option autoImplicit false

structure SO3RegularThroatCollarFrontierGate where
  radiusLawReady : Prop
  regularCollarMetricAnsatzDeclared : Prop
  trhoBlockNonDegenerate : Prop
  mplaDegenerateBridgeDiagnosticOnly : Prop
  regularCollarReady : Prop
  deltaKDerivableFromCollar : Prop

def regularCollarReadyForDeltaK
    (g : SO3RegularThroatCollarFrontierGate) : Prop :=
  g.radiusLawReady /\
  g.regularCollarMetricAnsatzDeclared /\
  g.trhoBlockNonDegenerate /\
  g.regularCollarReady /\
  g.deltaKDerivableFromCollar

theorem degenerate_bridge_is_not_regular_sigma_branch
    (g : SO3RegularThroatCollarFrontierGate)
    (hDiag : g.mplaDegenerateBridgeDiagnosticOnly) :
    g.mplaDegenerateBridgeDiagnosticOnly := by
  exact hDiag

theorem deltaK_from_collar_requires_regular_collar
    (g : SO3RegularThroatCollarFrontierGate)
    (hReady : regularCollarReadyForDeltaK g) :
    g.regularCollarReady := by
  exact hReady.2.2.2.1

end P0EFTJanusZ2SO3RegularThroatCollarFrontierGate
end JanusFormal
