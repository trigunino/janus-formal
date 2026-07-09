import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusNormalConnectionToSym4AnormalBridgeGate

namespace JanusFormal
namespace P0EFTJanusAnormalSym4SpectralConditionGate

set_option autoImplicit false

structure ANormalSym4SpectralConditionGate where
  ANormalOnC11Available : Prop
  Sym4LiftEigenvaluesAreDegree4WeightSums : Prop
  C11WeightsAreFourDissociated : Prop
  FourDissociatedWeightsJanusDerived : Prop
  M31BlockWeightsTooDegenerate : Prop
  BaseFiveWeightsWouldWorkButUnanchored : Prop
  Sym4SpectrumOrders1001States : Prop

def ANormalSpectralConditionClosed
    (g : ANormalSym4SpectralConditionGate) : Prop :=
  g.ANormalOnC11Available /\
  g.Sym4LiftEigenvaluesAreDegree4WeightSums /\
  g.C11WeightsAreFourDissociated /\
  g.FourDissociatedWeightsJanusDerived /\
  g.Sym4SpectrumOrders1001States

def ANormalSpectralConditionFrontier
    (g : ANormalSym4SpectralConditionGate) : Prop :=
  g.Sym4LiftEigenvaluesAreDegree4WeightSums /\
  Not g.C11WeightsAreFourDissociated /\
  Not g.FourDissociatedWeightsJanusDerived /\
  g.M31BlockWeightsTooDegenerate /\
  g.BaseFiveWeightsWouldWorkButUnanchored /\
  Not g.Sym4SpectrumOrders1001States

theorem no_four_dissociated_janus_weights_blocks_spectrum
    (g : ANormalSym4SpectralConditionGate)
    (hFrontier : ANormalSpectralConditionFrontier g) :
    Not (ANormalSpectralConditionClosed g) := by
  intro h
  exact hFrontier.2.2.1 h.2.2.2.1

end P0EFTJanusAnormalSym4SpectralConditionGate
end JanusFormal
