namespace JanusFormal
namespace P0EFTJanusUnimodularFourFormSectorGate

set_option autoImplicit false

structure UnimodularFourFormSectorGate where
  actionCandidateDeclared : Prop
  fourFormEquationGivesConstant : Prop
  alphaMapDeclared : Prop
  fluxQuantizationDeclared : Prop
  janusChargeUnitDerived : Prop
  janusBoundaryConditionSelectsFlux : Prop
  noFitAlphaGenerated : Prop

def deepAuditCompleteButConditional (g : UnimodularFourFormSectorGate) : Prop :=
  g.actionCandidateDeclared /\
  g.fourFormEquationGivesConstant /\
  g.alphaMapDeclared /\
  g.fluxQuantizationDeclared /\
  Not g.janusChargeUnitDerived /\
  Not g.janusBoundaryConditionSelectsFlux /\
  Not g.noFitAlphaGenerated

theorem four_form_route_needs_charge_unit_and_boundary_law
    (g : UnimodularFourFormSectorGate)
    (h : deepAuditCompleteButConditional g) :
    Not g.noFitAlphaGenerated := by
  exact h.right.right.right.right.right.right

end P0EFTJanusUnimodularFourFormSectorGate
end JanusFormal
