import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTOrbifoldSingularCycleGenerator
import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTOrbifoldHolonomyFluxQuantization

namespace JanusFormal
namespace P0EFTJanusProjectiveTunnelInterface

set_option autoImplicit false

structure JanusProjectiveTunnelTopology where
  sphereCoverS4Defined : Prop
  projectiveQuotientP4Defined : Prop
  antipodalDeckTransformationDefined : Prop
  twoFoldProjectiveCover : Prop
  bigBangPoleDefined : Prop
  bigCrunchPoleDefined : Prop
  polesAntipodal : Prop
  poleNeighborhoodsRemoved : Prop
  tubularThroatInserted : Prop
  deckTransformationExtendsOverThroat : Prop
  tunnelThroatSigmaDefined : Prop
  tunnelCoverManifoldDefined : Prop
  tunnelQuotientDefined : Prop
  tunnelTwoFoldCover : Prop
  twoFoldsConnectedByThroat : Prop
  singularitiesResolvedByTunnel : Prop
  torusDoubleCoverShadowDefined : Prop
  kleinBottleQuotientShadowDefined : Prop
  torusToKleinTwoFoldCover : Prop
  resolvedTunnelShadowNotBoySurface : Prop

structure ProjectiveTunnelInterface where
  projectiveCoverDefined : Prop
  antipodalQuotientDefined : Prop
  twoFoldCoverDerived : Prop
  polarNeighborhoodChosen : Prop
  tubularReplacementDefined : Prop
  tunnelThroatSigmaDefined : Prop
  aroundSigmaCycleDefined : Prop
  quotientProjectionToZ2Defined : Prop
  aroundSigmaMapsToGenerator : Prop
  tunnelPreservesTwoFoldCover : Prop

def projectiveTunnelClosed (i : ProjectiveTunnelInterface) : Prop :=
  i.projectiveCoverDefined /\
  i.antipodalQuotientDefined /\
  i.twoFoldCoverDerived /\
  i.polarNeighborhoodChosen /\
  i.tubularReplacementDefined /\
  i.tunnelThroatSigmaDefined /\
  i.aroundSigmaCycleDefined /\
  i.quotientProjectionToZ2Defined /\
  i.aroundSigmaMapsToGenerator /\
  i.tunnelPreservesTwoFoldCover

def resolvedTunnelShadowAvailable (t : JanusProjectiveTunnelTopology) : Prop :=
  t.torusDoubleCoverShadowDefined /\
  t.kleinBottleQuotientShadowDefined /\
  t.torusToKleinTwoFoldCover /\
  t.resolvedTunnelShadowNotBoySurface

theorem resolved_torus_klein_shadow_is_tunnel_not_boy
    (t : JanusProjectiveTunnelTopology)
    (h : resolvedTunnelShadowAvailable t) :
    t.resolvedTunnelShadowNotBoySurface := by
  exact h.2.2.2

theorem projective_tunnel_supplies_singular_cycle_transport
    (i : ProjectiveTunnelInterface)
    (h : projectiveTunnelClosed i) :
    P0EFTOrbifoldSingularCycleGenerator.singularCycleRepresentsGeneratorDerived
      { singularCycleAroundSigmaDefined := i.aroundSigmaCycleDefined
        quotientProjectionToZ2Defined := i.quotientProjectionToZ2Defined
        aroundSigmaMapsToGenerator := i.aroundSigmaMapsToGenerator } := by
  unfold projectiveTunnelClosed at h
  unfold P0EFTOrbifoldSingularCycleGenerator.singularCycleRepresentsGeneratorDerived
  exact And.intro h.2.2.2.2.2.2.1 (And.intro h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1)

theorem projective_tunnel_supplies_holonomy_cycle_input
    (i : ProjectiveTunnelInterface)
    (q : P0EFTOrbifoldHolonomyFluxQuantization.OrbifoldHolonomyFluxQuantization)
    (_h : projectiveTunnelClosed i)
    (hCycle : q.singularCycleAroundSigmaDefined)
    (hFlux : q.spinConnectionFluxIntegralDefined)
    (hQuant : q.fluxQuantizationConditionLoaded) :
    P0EFTOrbifoldHolonomyFluxQuantization.holonomyFluxQuantized q := by
  unfold P0EFTOrbifoldHolonomyFluxQuantization.holonomyFluxQuantized
  exact And.intro hCycle (And.intro hFlux hQuant)

structure JanusLiftedZ4Monodromy where
  tunnelLoopDefined : Prop
  sectorBundleDefined : Prop
  monodromyDefined : Prop
  monodromyFourthPowerIdentity : Prop
  monodromySquareNontrivial : Prop
  monodromySquareCoversSheetFlip : Prop
  monodromyCompatibleWithZ2Cover : Prop
  cyclicZ4Derived : Prop

def trueZ4MonodromyClosed (m : JanusLiftedZ4Monodromy) : Prop :=
  m.tunnelLoopDefined /\
  m.sectorBundleDefined /\
  m.monodromyDefined /\
  m.monodromyFourthPowerIdentity /\
  m.monodromySquareNontrivial /\
  m.monodromySquareCoversSheetFlip /\
  m.monodromyCompatibleWithZ2Cover

theorem true_z4_requires_order_four_monodromy
    (m : JanusLiftedZ4Monodromy)
    (h : trueZ4MonodromyClosed m)
    (hTransport : trueZ4MonodromyClosed m -> m.cyclicZ4Derived) :
    m.cyclicZ4Derived := by
  exact hTransport h

theorem missing_order_four_blocks_cyclic_z4_lift
    (m : JanusLiftedZ4Monodromy)
    (hMissing : Not m.monodromyFourthPowerIdentity) :
    Not (trueZ4MonodromyClosed m) := by
  intro h
  exact hMissing h.2.2.2.1

end P0EFTJanusProjectiveTunnelInterface
end JanusFormal
