import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusCompactQuotient
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D

/-!
# Closed embedding of the cut boundary

The orientation-double throat is compact and its continuous injective
inclusion into the Hausdorff positive-hemisphere cut bulk is therefore a
closed embedding.  This supplies the topological attachment condition needed
for a future smooth collar gluing; it does not perform that gluing.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBoundaryClosedEmbedding4D

set_option autoImplicit false
noncomputable section

open Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D

variable (period : Real) (hPeriod : period ≠ 0)

private theorem isClosed_closedPositiveHemisphere :
    IsClosed {point : UnitThreeSphere | 0 ≤ point.1 0} :=
  isClosed_le continuous_const
    ((continuous_apply 0).comp continuous_subtype_val)

local instance closedPositiveHemisphereT2Space :
    T2Space ClosedPositiveHemisphere :=
  inferInstanceAs (T2Space {point : UnitThreeSphere // 0 ≤ point.1 0})

local instance closedPositiveHemisphereLocallyCompactSpace :
    LocallyCompactSpace ClosedPositiveHemisphere :=
  isClosed_closedPositiveHemisphere.locallyCompactSpace

local instance cutBulkT2Space :
    T2Space (PositiveHemisphereCutBulk period hPeriod) :=
  mappingTorus_t2Space (cutBulkData period hPeriod)

local instance cutBoundaryCompactSpace :
    CompactSpace (CutThroatBoundary period hPeriod) :=
  fixedThroatQuotientCompactSpace
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

/-- The genuine doubled cut boundary is a closed embedded subspace of the
positive-hemisphere cut bulk. -/
theorem cutBoundaryInclusion_isClosedEmbedding :
    IsClosedEmbedding (cutBoundaryInclusion period hPeriod) :=
  (continuous_cutBoundaryInclusion period hPeriod).isClosedEmbedding
    (cutBoundaryInclusion_injective period hPeriod)

theorem isClosed_range_cutBoundaryInclusion :
    IsClosed (Set.range (cutBoundaryInclusion period hPeriod)) :=
  (cutBoundaryInclusion_isClosedEmbedding period hPeriod).isClosed_range

end
end P0EFTJanusMappingTorusCutBoundaryClosedEmbedding4D
end JanusFormal
