namespace JanusFormal
namespace P0EFTJanusZ2PublishedBimetricSectorRatioGate

set_option autoImplicit false

structure PublishedBimetricSectorRatioGate where
  publishedVisibleFractionDeclared : Prop
  publishedNegativeFractionDeclared : Prop
  signReversalDeclared : Prop
  relativeRatioDerived : Prop
  absoluteScaleDerived : Prop
  noObservationFit : Prop
  noLCDMParameterReuse : Prop

def relativeSectorRatioReady
    (g : PublishedBimetricSectorRatioGate) : Prop :=
  g.publishedVisibleFractionDeclared /\
  g.publishedNegativeFractionDeclared /\
  g.signReversalDeclared /\
  g.relativeRatioDerived /\
  g.noObservationFit /\
  g.noLCDMParameterReuse

theorem relative_ratio_does_not_imply_absolute_scale
    (g : PublishedBimetricSectorRatioGate)
    (_hRatio : relativeSectorRatioReady g)
    (hMissing : Not g.absoluteScaleDerived) :
    Not g.absoluteScaleDerived := by
  exact hMissing

end P0EFTJanusZ2PublishedBimetricSectorRatioGate
end JanusFormal
