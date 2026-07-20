import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalCapDerivativeIsomorphism4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalCollarDerivativeIsomorphism4D

/-!
# Global derivative isomorphism of the cut-bulk ambient map
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkGlobalDerivativeIsomorphism4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackLorentz4D
open P0EFTJanusMappingTorusCutBulkGlobalCapDerivativeIsomorphism4D
open P0EFTJanusMappingTorusCutBulkGlobalCollarDerivativeIsomorphism4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

/-- The natural map from the cut bulk to the ambient mapping torus has
invertible manifold derivative at every point. -/
theorem cutBulkToAmbient_derivative_isomorphism
    (bulk : PositiveHemisphereCutBulk period hPeriod) :
    CutBulkDerivativeIsomorphismAt period hPeriod bulk := by
  have hCover :
      bulk ∈ Set.range (cutOpenCollarAttachment period hPeriod) ∪
        cutBulkOpenCap period hPeriod := by
    rw [openCollar_union_openCap period hPeriod]
    exact Set.mem_univ bulk
  rcases hCover with hCollar | hCap
  · exact cutBulkToAmbient_derivative_isomorphism_on_openCollar
      period hPeriod bulk hCollar
  · exact cutBulkToAmbient_derivative_isomorphism_on_openCap
      period hPeriod ⟨bulk, hCap⟩

end
end P0EFTJanusMappingTorusCutBulkGlobalDerivativeIsomorphism4D
end JanusFormal
