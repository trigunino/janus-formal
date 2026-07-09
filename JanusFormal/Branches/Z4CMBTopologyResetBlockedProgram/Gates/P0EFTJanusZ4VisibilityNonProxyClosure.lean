import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4VisibilityNormalizationClosure
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4RecombinationCoefficientClosure

namespace JanusFormal
namespace P0EFTJanusZ4VisibilityNonProxyClosure

set_option autoImplicit false

structure VisibilityNonProxyClosure where
  ionizationHistoryBounded : Prop
  recombinationCoefficientsPositive : Prop
  opticalDepthMonotone : Prop
  visibilityNonnegative : Prop
  visibilityIntegralNormalized : Prop
  z4ExpansionRateInserted : Prop
  thomsonNormalizationPhysical : Prop

def visibilityNonProxyClosureReady (v : VisibilityNonProxyClosure) : Prop :=
  v.ionizationHistoryBounded /\
  v.recombinationCoefficientsPositive /\
  v.opticalDepthMonotone /\
  v.visibilityNonnegative /\
  v.visibilityIntegralNormalized /\
  v.z4ExpansionRateInserted /\
  v.thomsonNormalizationPhysical

theorem visibility_nonproxy_gives_unit_integral
    (v : VisibilityNonProxyClosure)
    (h : visibilityNonProxyClosureReady v) :
    v.visibilityIntegralNormalized := by
  exact h.right.right.right.right.left

theorem visibility_nonproxy_uses_z4_expansion
    (v : VisibilityNonProxyClosure)
    (h : visibilityNonProxyClosureReady v) :
    v.z4ExpansionRateInserted := by
  exact h.right.right.right.right.right.left

end P0EFTJanusZ4VisibilityNonProxyClosure
end JanusFormal
