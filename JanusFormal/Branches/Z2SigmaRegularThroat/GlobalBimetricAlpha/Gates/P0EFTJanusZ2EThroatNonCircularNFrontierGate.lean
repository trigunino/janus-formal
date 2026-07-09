namespace JanusFormal
namespace P0EFTJanusZ2EThroatNonCircularNFrontierGate

set_option autoImplicit false

structure NonCircularNFrontier where
  horizonEntropyGivesTarget : Prop
  horizonEntropyUsesTargetScale : Prop
  topologyOnlyNonCircular : Prop
  topologyOnlyGivesTarget : Prop
  boundaryHilbertSpaceDerived : Prop
  boundaryStateLawSelectsTarget : Prop
  tqftDerivedFromJanus : Prop
  tqftLevelSelectsTarget : Prop

def nonCircularNSelected (g : NonCircularNFrontier) : Prop :=
  (g.topologyOnlyNonCircular /\ g.topologyOnlyGivesTarget) \/
  (g.boundaryHilbertSpaceDerived /\ g.boundaryStateLawSelectsTarget) \/
  (g.tqftDerivedFromJanus /\ g.tqftLevelSelectsTarget)

theorem horizon_entropy_target_is_circular_when_it_uses_target_scale
    (g : NonCircularNFrontier)
    (_hTarget : g.horizonEntropyGivesTarget)
    (_hCircular : g.horizonEntropyUsesTargetScale)
    (hNoTopologyTarget : Not g.topologyOnlyGivesTarget)
    (hNoHilbert : Not g.boundaryHilbertSpaceDerived)
    (hNoTQFT : Not g.tqftDerivedFromJanus) :
    Not (nonCircularNSelected g) := by
  intro h
  cases h with
  | inl hTop => exact hNoTopologyTarget hTop.2
  | inr rest =>
      cases rest with
      | inl hHilbert => exact hNoHilbert hHilbert.1
      | inr hTqft => exact hNoTQFT hTqft.1

end P0EFTJanusZ2EThroatNonCircularNFrontierGate
end JanusFormal
