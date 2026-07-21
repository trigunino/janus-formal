import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalDerivativeIsomorphism4D

/-!
# Global Lorentz algebra of the cut-bulk ambient tensor pullback
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackGlobalLorentz4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullback4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackLorentz4D
open P0EFTJanusMappingTorusCutBulkGlobalDerivativeIsomorphism4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

theorem cutBulkAmbientTensorPullback_nondegenerate_global
    (tensor : CovariantTwoTensorField period hPeriod)
    (hTensor : ∀ point, FiberIsNondegenerate period hPeriod (tensor point))
    (point : PositiveHemisphereCutBulk period hPeriod) :
    CutBulkFiberIsNondegenerate period hPeriod
      (cutBulkAmbientTensorPullback period hPeriod tensor point) :=
  cutBulkAmbientTensorPullback_nondegenerate period hPeriod tensor point
    (cutBulkToAmbient_derivative_isomorphism period hPeriod point)
    (hTensor _)

theorem cutBulkAmbientTensorPullback_lorentzian_global
    (tensor : CovariantTwoTensorField period hPeriod)
    (hTensor : ∀ point, FiberIsLorentzian period hPeriod (tensor point))
    (point : PositiveHemisphereCutBulk period hPeriod) :
    CutBulkFiberIsLorentzian period hPeriod
      (cutBulkAmbientTensorPullback period hPeriod tensor point) :=
  cutBulkAmbientTensorPullback_lorentzian period hPeriod tensor point
    (cutBulkToAmbient_derivative_isomorphism period hPeriod point)
    (hTensor _)

end
end P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackGlobalLorentz4D
end JanusFormal
