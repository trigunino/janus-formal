import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusEntropyToRulerResolutionMapGate
import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusNativeSoundHorizonIntegralContractGate

namespace JanusFormal
namespace P0EFTJanusEntropyCutoffToNativeSoundHorizonBridgeGate

set_option autoImplicit false

structure EntropyCutoffToNativeSoundHorizonBridgeGate where
  EntropyAminSupplied : Prop
  ZeroLowerLimitDivergenceAvoided : Prop
  PredragReachAvailable : Prop
  DragEpochDerived : Prop
  NativeHJDerived : Prop
  BaryonPhotonNormalizationDerived : Prop

def EntropyCutoffSoundHorizonClosed
    (g : EntropyCutoffToNativeSoundHorizonBridgeGate) : Prop :=
  g.EntropyAminSupplied /\
  g.ZeroLowerLimitDivergenceAvoided /\
  g.PredragReachAvailable /\
  g.DragEpochDerived /\
  g.NativeHJDerived /\
  g.BaryonPhotonNormalizationDerived

def EntropyCutoffSoundHorizonFrontier
    (g : EntropyCutoffToNativeSoundHorizonBridgeGate) : Prop :=
  g.EntropyAminSupplied /\
  g.ZeroLowerLimitDivergenceAvoided /\
  g.PredragReachAvailable /\
  Not g.DragEpochDerived /\
  Not g.NativeHJDerived /\
  Not g.BaryonPhotonNormalizationDerived

theorem entropy_cutoff_does_not_alone_make_bao_executable
    (g : EntropyCutoffToNativeSoundHorizonBridgeGate)
    (hFrontier : EntropyCutoffSoundHorizonFrontier g) :
    Not (EntropyCutoffSoundHorizonClosed g) := by
  intro h
  exact hFrontier.2.2.2.1 h.2.2.2.1

end P0EFTJanusEntropyCutoffToNativeSoundHorizonBridgeGate
end JanusFormal
