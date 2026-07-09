namespace JanusFormal
namespace P0EFTJanusZ4ObservableOscilloscope

set_option autoImplicit false

structure ObservableOscilloscope where
  swDiagnosticDeclared : Prop
  eiswDiagnosticDeclared : Prop
  lensingDiagnosticDeclared : Prop
  muSigmaDiagnosticDeclared : Prop
  finiteDiagnostics : Prop
  planckValidationClaimed : Prop

def oscilloscopeReady (o : ObservableOscilloscope) : Prop :=
  o.swDiagnosticDeclared /\
  o.eiswDiagnosticDeclared /\
  o.lensingDiagnosticDeclared /\
  o.muSigmaDiagnosticDeclared /\
  o.finiteDiagnostics

theorem ready_does_not_claim_planck_validation
    (o : ObservableOscilloscope)
    (_h : oscilloscopeReady o)
    (hNoClaim : Not o.planckValidationClaimed) :
    Not o.planckValidationClaimed := by
  exact hNoClaim

theorem ready_contains_all_cmb_failure_channels
    (o : ObservableOscilloscope)
    (h : oscilloscopeReady o) :
    o.swDiagnosticDeclared /\
    o.eiswDiagnosticDeclared /\
    o.lensingDiagnosticDeclared /\
    o.muSigmaDiagnosticDeclared := by
  exact And.intro h.left (And.intro h.right.left (And.intro h.right.right.left h.right.right.right.left))

end P0EFTJanusZ4ObservableOscilloscope
end JanusFormal
