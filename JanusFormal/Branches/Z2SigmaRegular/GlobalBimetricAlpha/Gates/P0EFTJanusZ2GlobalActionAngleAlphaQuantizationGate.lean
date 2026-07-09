namespace JanusFormal
namespace P0EFTJanusZ2GlobalActionAngleAlphaQuantizationGate

set_option autoImplicit false

structure GlobalActionAngleAlphaQuantizationGate where
  exactOrbitShapeAvailable : Prop
  globalPTCycleIdentified : Prop
  cycleCompactClosed : Prop
  canonicalPairDerived : Prop
  symplecticOneFormDerived : Prop
  actionIntegralIAlphaDerived : Prop
  actionPrefactorAvailable : Prop
  alphaPowerAvailable : Prop
  bohrSommerfeldLawAccepted : Prop
  primitiveIntegerAvailable : Prop
  primitiveSectorSelected : Prop

def actionAngleAlphaQuantized
    (g : GlobalActionAngleAlphaQuantizationGate) : Prop :=
  g.exactOrbitShapeAvailable /\
  g.globalPTCycleIdentified /\
  g.cycleCompactClosed /\
  g.canonicalPairDerived /\
  g.symplecticOneFormDerived /\
  g.actionIntegralIAlphaDerived /\
  g.actionPrefactorAvailable /\
  g.alphaPowerAvailable /\
  g.bohrSommerfeldLawAccepted /\
  g.primitiveIntegerAvailable /\
  g.primitiveSectorSelected

theorem missing_canonical_pair_blocks_action_angle_quantization
    (g : GlobalActionAngleAlphaQuantizationGate)
    (hMissing : Not g.canonicalPairDerived) :
    Not (actionAngleAlphaQuantized g) := by
  intro h
  exact hMissing h.right.right.right.left

theorem missing_action_integral_blocks_action_angle_quantization
    (g : GlobalActionAngleAlphaQuantizationGate)
    (hMissing : Not g.actionIntegralIAlphaDerived) :
    Not (actionAngleAlphaQuantized g) := by
  intro h
  exact hMissing h.right.right.right.right.right.left

theorem exact_orbit_shape_alone_does_not_quantize_alpha
    (g : GlobalActionAngleAlphaQuantizationGate)
    (hMissing : Not g.symplecticOneFormDerived) :
    Not (actionAngleAlphaQuantized g) := by
  intro h
  exact hMissing h.right.right.right.right.left

end P0EFTJanusZ2GlobalActionAngleAlphaQuantizationGate
end JanusFormal
