namespace JanusFormal
namespace P0EFTJanusZ2PublishedBimetricFLRWSectorSourceReductionGate

set_option autoImplicit false

structure PublishedBimetricFLRWSectorSourceReductionGate where
  dustScalarTransportClosed : Prop
  determinantFormulaClosed : Prop
  perfectFluidTransportConditional : Prop
  equationOfStateSelectedFromAction : Prop
  plusNormalizationDerived : Prop
  minusNormalizationDerived : Prop
  rhoPShapeReady : Prop
  rhoPNormalizedReady : Prop
  fittedDensityUsed : Prop

def normalizedSectorSourceReady
    (g : PublishedBimetricFLRWSectorSourceReductionGate) : Prop :=
  g.rhoPShapeReady /\
  g.equationOfStateSelectedFromAction /\
  g.plusNormalizationDerived /\
  g.minusNormalizationDerived /\
  Not g.fittedDensityUsed

theorem shape_without_normalization_is_not_source_ready
    (g : PublishedBimetricFLRWSectorSourceReductionGate)
    (hNoPlus : Not g.plusNormalizationDerived) :
    Not (normalizedSectorSourceReady g) := by
  intro h
  exact hNoPlus h.right.right.left

theorem normalized_source_has_no_fit
    (g : PublishedBimetricFLRWSectorSourceReductionGate)
    (h : normalizedSectorSourceReady g) :
    Not g.fittedDensityUsed := by
  exact h.right.right.right.right

end P0EFTJanusZ2PublishedBimetricFLRWSectorSourceReductionGate
end JanusFormal
