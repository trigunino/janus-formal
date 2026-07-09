namespace JanusFormal
namespace P0EFTJanusNativeDragEpochEquationContractGate

set_option autoImplicit false

structure NativeDragEpochEquationContractGate where
  gammaPowerWithoutXeDeclared : Prop
  sahaVisibilityProxyDeclared : Prop
  thermalFrameDeclared : Prop
  dragCrossingEquationDeclared : Prop
  cIonInputRequired : Prop
  baryonNormalizationRequired : Prop
  dragNormalizationRequired : Prop
  fullHJRequired : Prop
  structuralPredictionReady : Prop
  numericPredictionReady : Prop

def nativeDragEquationContractReady
    (g : NativeDragEpochEquationContractGate) : Prop :=
  g.gammaPowerWithoutXeDeclared /\
  g.sahaVisibilityProxyDeclared /\
  g.thermalFrameDeclared /\
  g.dragCrossingEquationDeclared /\
  g.cIonInputRequired /\
  g.baryonNormalizationRequired /\
  g.dragNormalizationRequired /\
  g.fullHJRequired /\
  g.structuralPredictionReady /\
  Not g.numericPredictionReady

theorem structural_not_numeric_until_anchors_supplied
    (g : NativeDragEpochEquationContractGate)
    (hReady : nativeDragEquationContractReady g) :
    g.structuralPredictionReady /\ Not g.numericPredictionReady := by
  exact And.intro hReady.2.2.2.2.2.2.2.2.1 hReady.2.2.2.2.2.2.2.2.2

end P0EFTJanusNativeDragEpochEquationContractGate
end JanusFormal
