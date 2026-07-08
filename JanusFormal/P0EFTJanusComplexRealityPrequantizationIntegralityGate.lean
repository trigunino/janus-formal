import JanusFormal.P0EFTJanusComplexRealityCombinedKKSPeriodGate
import JanusFormal.P0EFTJanusComplexRealityActiveEmbeddingOrCompactPhaseGate

namespace JanusFormal
namespace P0EFTJanusComplexRealityPrequantizationIntegralityGate

set_option autoImplicit false

structure PrequantizationIntegralityGate where
  combinedKKSSourceReady : Prop
  boundaryCycleDeclared : Prop
  compactPhaseDirectionExists : Prop
  kksDensityNonzeroOnCycle : Prop
  prequantizationPeriodComputed : Prop
  integralOverTwoPiHbarInteger : Prop
  massOrChargeLatticeDerived : Prop
  alphaMapToBoundaryChargeDerived : Prop
  jQuantizationDerived : Prop
  alphaGeneratedNow : Prop

def prequantizationIntegralityReady (g : PrequantizationIntegralityGate) : Prop :=
  g.combinedKKSSourceReady /\
  g.boundaryCycleDeclared /\
  g.compactPhaseDirectionExists /\
  g.kksDensityNonzeroOnCycle /\
  g.prequantizationPeriodComputed /\
  g.integralOverTwoPiHbarInteger /\
  g.massOrChargeLatticeDerived /\
  g.alphaMapToBoundaryChargeDerived /\
  g.jQuantizationDerived

def prequantizationAlphaDerived (g : PrequantizationIntegralityGate) : Prop :=
  prequantizationIntegralityReady g /\ g.alphaGeneratedNow

theorem integrality_missing_blocks_alpha
    (g : PrequantizationIntegralityGate)
    (hNo : Not (prequantizationIntegralityReady g)) :
    Not (prequantizationAlphaDerived g) := by
  intro h
  exact hNo h.left

end P0EFTJanusComplexRealityPrequantizationIntegralityGate
end JanusFormal
