namespace JanusFormal
namespace P0EFTJanusZ2SigmaDimensionfulScaleSeparationObligationGate

set_option autoImplicit false

structure DimensionfulScaleSeparationObligationGate where
  activeCoreZ2TunnelSigma : Prop
  dimensionlessScaleExists : Prop
  h0NormalizationExists : Prop
  curvatureRadiusExists : Prop
  canComputeScaleFreeOmegaKFromProduct : Prop
  canInvertProductToH0OrRCurv : Prop
  dimensionlessProductInsufficientForPhysicalVolume : Prop
  dimensionlessProductInsufficientForGammaDragOverH0 : Prop
  compressedPlanckLCDMBackgroundUsed : Prop
  archivedZ4BackgroundUsed : Prop
  observationalH0FitUsed : Prop
  observationalCurvatureFitUsed : Prop
  gatePassed : Prop

def dimensionfulScaleReady
    (g : DimensionfulScaleSeparationObligationGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.h0NormalizationExists /\
  g.curvatureRadiusExists /\
  Not g.canInvertProductToH0OrRCurv /\
  Not g.compressedPlanckLCDMBackgroundUsed /\
  Not g.archivedZ4BackgroundUsed /\
  Not g.observationalH0FitUsed /\
  Not g.observationalCurvatureFitUsed

theorem product_alone_does_not_supply_dimensionful_scales
    (g : DimensionfulScaleSeparationObligationGate)
    (hInsufficientVolume : g.dimensionlessProductInsufficientForPhysicalVolume)
    (hInsufficientDrag : g.dimensionlessProductInsufficientForGammaDragOverH0)
    (hNoInvert : Not g.canInvertProductToH0OrRCurv) :
    g.dimensionlessProductInsufficientForPhysicalVolume /\
    g.dimensionlessProductInsufficientForGammaDragOverH0 /\
    Not g.canInvertProductToH0OrRCurv := by
  exact ⟨hInsufficientVolume, hInsufficientDrag, hNoInvert⟩

theorem ready_requires_separate_h0_and_radius
    (g : DimensionfulScaleSeparationObligationGate)
    (hReady : dimensionfulScaleReady g) :
    g.h0NormalizationExists /\ g.curvatureRadiusExists := by
  exact ⟨hReady.2.1, hReady.2.2.1⟩

end P0EFTJanusZ2SigmaDimensionfulScaleSeparationObligationGate
end JanusFormal
