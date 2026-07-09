namespace JanusFormal
namespace P0EFTJanusZ2EThroatHolographicNSelectorCandidate

set_option autoImplicit false

structure HolographicNSelectorCandidate where
  horizonEntropyGivesMacroscopicN : Prop
  horizonEntropyUsesH0orL : Prop
  condensateOccupationGivesMacroscopicN : Prop
  condensateOccupationUsesL : Prop
  primitiveTopologySelectsN : Prop
  primitiveTopologyGivesMacroscopicN : Prop
  independentJanusStateLawSelectsN : Prop

def nonCircularMacroscopicNSelector (g : HolographicNSelectorCandidate) : Prop :=
  g.independentJanusStateLawSelectsN \/
  (g.primitiveTopologySelectsN /\ g.primitiveTopologyGivesMacroscopicN)

theorem horizon_entropy_is_not_prediction_if_it_uses_H0
    (g : HolographicNSelectorCandidate)
    (_hMacro : g.horizonEntropyGivesMacroscopicN)
    (_hUses : g.horizonEntropyUsesH0orL)
    (hNoLaw : Not g.independentJanusStateLawSelectsN)
    (hPrimitiveWrong : Not g.primitiveTopologyGivesMacroscopicN) :
    Not (nonCircularMacroscopicNSelector g) := by
  intro h
  cases h with
  | inl hLaw => exact hNoLaw hLaw
  | inr hPrim => exact hPrimitiveWrong hPrim.2

theorem primitive_topology_without_macroscopic_N_is_wrong_scale
    (g : HolographicNSelectorCandidate)
    (_hPrimitive : g.primitiveTopologySelectsN)
    (hNotMacro : Not g.primitiveTopologyGivesMacroscopicN) :
    Not (g.primitiveTopologySelectsN /\ g.primitiveTopologyGivesMacroscopicN) := by
  intro h
  exact hNotMacro h.2

end P0EFTJanusZ2EThroatHolographicNSelectorCandidate
end JanusFormal
