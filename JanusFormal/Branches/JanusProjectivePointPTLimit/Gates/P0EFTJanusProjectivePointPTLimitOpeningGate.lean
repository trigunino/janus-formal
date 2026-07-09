namespace JanusFormal
namespace P0EFTJanusProjectivePointPTLimitOpeningGate

set_option autoImplicit false

structure ProjectivePointPTLimitOpeningGate where
  GlobalCoverS4ToRP4Declared : Prop
  AntipodalPTPointIdentificationDeclared : Prop
  FiniteThroatSigmaRemoved : Prop
  RSigmaSelectionRemoved : Prop
  SingularProjectiveInitialConditionRequired : Prop
  EarlyRulerDerived : Prop

def ProjectivePointPTLimitClosed
    (g : ProjectivePointPTLimitOpeningGate) : Prop :=
  g.GlobalCoverS4ToRP4Declared /\
  g.AntipodalPTPointIdentificationDeclared /\
  g.FiniteThroatSigmaRemoved /\
  g.SingularProjectiveInitialConditionRequired /\
  g.EarlyRulerDerived

def ProjectivePointPTLimitFrontier
    (g : ProjectivePointPTLimitOpeningGate) : Prop :=
  g.GlobalCoverS4ToRP4Declared /\
  g.AntipodalPTPointIdentificationDeclared /\
  g.FiniteThroatSigmaRemoved /\
  g.RSigmaSelectionRemoved /\
  g.SingularProjectiveInitialConditionRequired /\
  Not g.EarlyRulerDerived

theorem point_limit_removes_sigma_but_not_early_ruler
    (g : ProjectivePointPTLimitOpeningGate)
    (hFrontier : ProjectivePointPTLimitFrontier g) :
    Not (ProjectivePointPTLimitClosed g) := by
  intro h
  exact hFrontier.2.2.2.2.2 h.2.2.2.2

end P0EFTJanusProjectivePointPTLimitOpeningGate
end JanusFormal
