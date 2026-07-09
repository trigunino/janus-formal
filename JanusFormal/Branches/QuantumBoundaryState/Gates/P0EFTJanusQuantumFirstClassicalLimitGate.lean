import JanusFormal.Branches.QuantumBoundaryState.Gates.P0EFTJanusQuantumFirstAlphaSpectrumGate

namespace JanusFormal
namespace P0EFTJanusQuantumFirstClassicalLimitGate

set_option autoImplicit false

structure QuantumFirstClassicalLimitGate where
  conditionalAlphaSpectrumReady : Prop
  janusScaleFactorMapDeclared : Prop
  q0MapDeclared : Prop
  largeQuantumNumberLimitDeclared : Prop
  paperNativeClassicalLimitRecovered : Prop
  noFitNumericalAlphaRecovered : Prop

def conditionalClassicalLimitReady (g : QuantumFirstClassicalLimitGate) : Prop :=
  g.conditionalAlphaSpectrumReady /\
  g.janusScaleFactorMapDeclared /\
  g.q0MapDeclared /\
  g.largeQuantumNumberLimitDeclared /\
  g.paperNativeClassicalLimitRecovered

def noFitClassicalJanusReady (g : QuantumFirstClassicalLimitGate) : Prop :=
  conditionalClassicalLimitReady g /\ g.noFitNumericalAlphaRecovered

end P0EFTJanusQuantumFirstClassicalLimitGate
end JanusFormal
