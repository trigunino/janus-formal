import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothQuotientManifold
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D

/-!
# Smooth finite collar of the cut-throat boundary

The orientation-double boundary is an analytic three-manifold.  Its product
with `[0,1]` is therefore an actual analytic four-manifold with boundary.  The
two boundary faces are explicit; the zero face is the cut-throat boundary and
the unit face is the artificial interface to the remaining bulk.  This is the
local collar needed for a future global gluing, not that gluing itself.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev CutCollarInterval := Set.Icc (0 : Real) 1

abbrev CutCollarCoordinates :=
  ThroatCoverCoordinates × EuclideanSpace Real (Fin 1)

abbrev CutCollarModel :=
  ModelProd ThroatCoverModel (EuclideanHalfSpace 1)

abbrev cutCollarModelWithCorners :
    ModelWithCorners Real CutCollarCoordinates CutCollarModel :=
  throatCoverModelWithCorners.prod (modelWithCornersEuclideanHalfSpace 1)

abbrev CutThroatFiniteCollar :=
  CutThroatBoundary period hPeriod × CutCollarInterval

/-- Analytic atlas on the orientation-double throat. -/
@[implicit_reducible] def cutThroatBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  fixedThroatQuotientChartedSpace
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

theorem cutThroatBoundary_isManifold :
    @IsManifold Real _ ThroatCoverCoordinates _ _ ThroatCoverModel _
      throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) _
      (cutThroatBoundaryChartedSpace period hPeriod) :=
  fixedThroatQuotient_isManifold
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

/-- Product atlas on the finite cut collar. -/
@[implicit_reducible] def cutThroatFiniteCollarChartedSpace :
    ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) := by
  letI : ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
    cutThroatBoundaryChartedSpace period hPeriod
  infer_instance

theorem cutThroatFiniteCollar_isManifold :
    @IsManifold Real _ CutCollarCoordinates _ _ CutCollarModel _
      cutCollarModelWithCorners ω
      (CutThroatFiniteCollar period hPeriod) _
      (cutThroatFiniteCollarChartedSpace period hPeriod) := by
  letI : ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
    cutThroatBoundaryChartedSpace period hPeriod
  letI : IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
    cutThroatBoundary_isManifold period hPeriod
  letI : ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
    cutThroatFiniteCollarChartedSpace period hPeriod
  infer_instance

/-- The exact manifold boundary consists of the throat face and the outer
gluing face. -/
theorem cutThroatFiniteCollar_boundary :
    letI : ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
      cutThroatBoundaryChartedSpace period hPeriod
    letI : IsManifold throatCoverModelWithCorners ω
        (CutThroatBoundary period hPeriod) :=
      cutThroatBoundary_isManifold period hPeriod
    letI : ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
      cutThroatFiniteCollarChartedSpace period hPeriod
    (cutCollarModelWithCorners).boundary
        (CutThroatFiniteCollar period hPeriod) =
      Set.univ ×ˢ ({⊥, ⊤} : Set CutCollarInterval) := by
  letI : ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
    cutThroatBoundaryChartedSpace period hPeriod
  letI : IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
    cutThroatBoundary_isManifold period hPeriod
  letI : ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
    cutThroatFiniteCollarChartedSpace period hPeriod
  exact boundary_product throatCoverModelWithCorners

def cutThroatFace
    (boundary : CutThroatBoundary period hPeriod) :
    CutThroatFiniteCollar period hPeriod :=
  (boundary, ⊥)

def cutOuterFace
    (boundary : CutThroatBoundary period hPeriod) :
    CutThroatFiniteCollar period hPeriod :=
  (boundary, ⊤)

theorem cutThroatFace_injective :
    Function.Injective (cutThroatFace period hPeriod) := by
  intro first second hEqual
  exact congrArg Prod.fst hEqual

theorem cutOuterFace_injective :
    Function.Injective (cutOuterFace period hPeriod) := by
  intro first second hEqual
  exact congrArg Prod.fst hEqual

theorem range_cutThroatFace :
    Set.range (cutThroatFace period hPeriod) =
      Set.univ ×ˢ ({⊥} : Set CutCollarInterval) := by
  ext point
  constructor
  · rintro ⟨boundary, rfl⟩
    simp [cutThroatFace]
  · rintro ⟨-, hInterval⟩
    simp only [mem_singleton_iff] at hInterval
    exact ⟨point.1, Prod.ext rfl hInterval.symm⟩

theorem range_cutOuterFace :
    Set.range (cutOuterFace period hPeriod) =
      Set.univ ×ˢ ({⊤} : Set CutCollarInterval) := by
  ext point
  constructor
  · rintro ⟨boundary, rfl⟩
    simp [cutOuterFace]
  · rintro ⟨-, hInterval⟩
    simp only [mem_singleton_iff] at hInterval
    exact ⟨point.1, Prod.ext rfl hInterval.symm⟩

theorem contMDiff_cutThroatFace :
    letI : ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
      cutThroatBoundaryChartedSpace period hPeriod
    letI : ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
      cutThroatFiniteCollarChartedSpace period hPeriod
    ContMDiff throatCoverModelWithCorners cutCollarModelWithCorners ω
      (cutThroatFace period hPeriod) := by
  letI : ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
    cutThroatBoundaryChartedSpace period hPeriod
  letI : ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
    cutThroatFiniteCollarChartedSpace period hPeriod
  exact contMDiff_id.prodMk contMDiff_const

theorem contMDiff_cutOuterFace :
    letI : ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
      cutThroatBoundaryChartedSpace period hPeriod
    letI : ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
      cutThroatFiniteCollarChartedSpace period hPeriod
    ContMDiff throatCoverModelWithCorners cutCollarModelWithCorners ω
      (cutOuterFace period hPeriod) := by
  letI : ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
    cutThroatBoundaryChartedSpace period hPeriod
  letI : ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
    cutThroatFiniteCollarChartedSpace period hPeriod
  exact contMDiff_id.prodMk contMDiff_const

theorem cutThroatFiniteCollar_boundary_eq_face_ranges :
    letI : ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
      cutThroatBoundaryChartedSpace period hPeriod
    letI : IsManifold throatCoverModelWithCorners ω
        (CutThroatBoundary period hPeriod) :=
      cutThroatBoundary_isManifold period hPeriod
    letI : ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
      cutThroatFiniteCollarChartedSpace period hPeriod
    (cutCollarModelWithCorners).boundary
        (CutThroatFiniteCollar period hPeriod) =
      Set.range (cutThroatFace period hPeriod) ∪
        Set.range (cutOuterFace period hPeriod) := by
  rw [cutThroatFiniteCollar_boundary, range_cutThroatFace,
    range_cutOuterFace]
  ext point
  simp only [mem_prod, mem_univ, true_and, mem_insert_iff,
    mem_singleton_iff, mem_union]

theorem cutThroatFace_mem_boundary
    (boundary : CutThroatBoundary period hPeriod) :
    letI : ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
      cutThroatBoundaryChartedSpace period hPeriod
    letI : IsManifold throatCoverModelWithCorners ω
        (CutThroatBoundary period hPeriod) :=
      cutThroatBoundary_isManifold period hPeriod
    letI : ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
      cutThroatFiniteCollarChartedSpace period hPeriod
    cutThroatFace period hPeriod boundary ∈
      (cutCollarModelWithCorners).boundary
        (CutThroatFiniteCollar period hPeriod) := by
  rw [cutThroatFiniteCollar_boundary]
  simp [cutThroatFace]

end
end P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
end JanusFormal
