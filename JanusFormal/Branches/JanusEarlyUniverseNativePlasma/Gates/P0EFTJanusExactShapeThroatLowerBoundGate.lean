namespace JanusFormal
namespace P0EFTJanusExactShapeThroatLowerBoundGate

set_option autoImplicit false

structure ExactShapeThroatLowerBoundGate where
  exactShapeDeclared : Prop
  presentNormalizationDeclared : Prop
  nonzeroAminDerived : Prop
  soundHorizonLowerBoundRegularized : Prop
  q0PublishedBranchDeclared : Prop
  zMaxFiniteAndLow : Prop
  standardDragRedshiftNotReached : Prop
  earlyTimeBranchRequired : Prop
  noAlphaFitRepair : Prop

def exactShapeThroatReady (g : ExactShapeThroatLowerBoundGate) : Prop :=
  g.exactShapeDeclared /\
  g.presentNormalizationDeclared /\
  g.nonzeroAminDerived /\
  g.soundHorizonLowerBoundRegularized /\
  g.q0PublishedBranchDeclared /\
  g.zMaxFiniteAndLow /\
  g.standardDragRedshiftNotReached /\
  g.earlyTimeBranchRequired /\
  g.noAlphaFitRepair

theorem exact_shape_regularizes_but_requires_early_branch
    (g : ExactShapeThroatLowerBoundGate)
    (hReady : exactShapeThroatReady g) :
    g.soundHorizonLowerBoundRegularized /\ g.earlyTimeBranchRequired := by
  exact And.intro hReady.2.2.2.1 hReady.2.2.2.2.2.2.2.1

end P0EFTJanusExactShapeThroatLowerBoundGate
end JanusFormal
