import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonCompatibility4D

/-! # Boundarylessness of the intrinsic cap in the common model -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonBoundaryless4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonCompatibility4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The identity is a smooth diffeomorphism from the standard cap atlas to
the common half-space-model atlas. -/
def intrinsicCapStandardCommonDiffeomorph :
    letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    CutBulkOpenCap period hPeriod ≃ₘ^∞⟮
      coverModelWithCorners, cutCollarModelWithCorners⟯
      CutBulkOpenCap period hPeriod := by
  letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
  letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  exact
    { toEquiv := Equiv.refl _
      contMDiff_toFun := intrinsicCapStandardToCommon_contMDiff period hPeriod
      contMDiff_invFun := intrinsicCapCommonToStandard_contMDiff period hPeriod }

theorem intrinsicCutBulkOpenCapCommon_boundaryless :
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    BoundarylessManifold cutCollarModelWithCorners
      (CutBulkOpenCap period hPeriod) := by
  letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ∞
      (CutBulkOpenCap period hPeriod) :=
    (intrinsicCutBulkOpenCap_isManifold period hPeriod).of_le le_top
  letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommon_isManifold period hPeriod
  exact (intrinsicCapStandardCommonDiffeomorph period hPeriod)
    |>.boundarylessManifold (by simp)

theorem intrinsicCutBulkOpenCapCommon_boundary_eq_empty :
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    cutCollarModelWithCorners.boundary (CutBulkOpenCap period hPeriod) = ∅ := by
  letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  letI : BoundarylessManifold cutCollarModelWithCorners
      (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommon_boundaryless period hPeriod
  exact ModelWithCorners.Boundaryless.boundary_eq_empty

end
end P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonBoundaryless4D
end JanusFormal
