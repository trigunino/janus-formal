import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D

/-! # Exact manifold boundary of the open cut-throat collar -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutThroatOpenCollarBoundary4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Removing the outer face leaves exactly the genuine throat face as the
manifold boundary of the open collar. -/
theorem cutThroatOpenCollar_boundary :
    letI := cutThroatBoundaryChartedSpace period hPeriod
    letI := cutThroatFiniteCollarChartedSpace period hPeriod
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    cutCollarModelWithCorners.boundary
        (CutThroatOpenCollar period hPeriod) =
      {point | point.1.2 = ⊥} := by
  letI := cutThroatBoundaryChartedSpace period hPeriod
  letI : IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
    cutThroatBoundary_isManifold period hPeriod
  letI := cutThroatFiniteCollarChartedSpace period hPeriod
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  change cutCollarModelWithCorners.boundary
      (cutThroatOpenCollarOpen period hPeriod) =
    {point : cutThroatOpenCollarOpen period hPeriod | point.1.2 = ⊥}
  rw [ModelWithCorners.boundary_open,
    cutThroatFiniteCollar_boundary period hPeriod]
  ext point
  simp only [mem_preimage, mem_prod, mem_univ, true_and, mem_insert_iff,
    mem_singleton_iff, mem_setOf_eq]
  constructor
  · intro hFace
    exact hFace.resolve_right (by
      intro hTop
      have hLess := point.2
      change point.1.2.1 < 1 at hLess
      rw [hTop] at hLess
      exact (lt_irrefl (1 : Real)) hLess)
  · exact Or.inl

end
end P0EFTJanusMappingTorusCutThroatOpenCollarBoundary4D
end JanusFormal
