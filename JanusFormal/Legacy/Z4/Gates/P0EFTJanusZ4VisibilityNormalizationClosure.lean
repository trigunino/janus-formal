import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4RecombinationVisibilityTarget

namespace JanusFormal
namespace P0EFTJanusZ4VisibilityNormalizationClosure

set_option autoImplicit false

structure VisibilityNormalizationClosure where
  opticalDepthMonotone : Prop
  visibilityNonnegative : Prop
  visibilityIntegralNormalized : Prop
  z4BackgroundRateInserted : Prop
  thomsonUnitsConsistent : Prop
  ionizationHistorySolved : Prop

def visibilityNormalizationReady (v : VisibilityNormalizationClosure) : Prop :=
  v.opticalDepthMonotone /\
  v.visibilityNonnegative /\
  v.visibilityIntegralNormalized /\
  v.z4BackgroundRateInserted /\
  v.thomsonUnitsConsistent

def visibilityNonProxyReady (v : VisibilityNormalizationClosure) : Prop :=
  visibilityNormalizationReady v /\
  v.ionizationHistorySolved

theorem visibility_normalization_requires_unit_integral
    (v : VisibilityNormalizationClosure)
    (h : visibilityNormalizationReady v) :
    v.visibilityIntegralNormalized := by
  exact h.right.right.left

theorem visibility_normalization_does_not_solve_ionization
    (v : VisibilityNormalizationClosure)
    (_h : visibilityNormalizationReady v)
    (hMissing : Not v.ionizationHistorySolved) :
    Not (visibilityNonProxyReady v) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4VisibilityNormalizationClosure
end JanusFormal
