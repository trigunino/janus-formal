import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullScreenMeasureIntegratedStokes4D

/-!
# Closed warped-null half-collar

This gate restricts the global linear collar to `0 ≤ r ≤ 1`.  The resulting
product is an actual analytic manifold with corners whose boundary is exactly
the null face at `r = 0` and the artificial outer face at `r = 1`.  Its ambient
image is the slab cut out by `0 ≤ z-u ≤ 1`.

The affine current of Gate 1042 restricts to this half-collar, has prescribed
lower flux, and vanishes on the outer face.  No extension through `r = 0`,
compact-support construction, or mapping-torus incidence is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff
open Topology
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06WarpedNullCollarOrientation4D
open P0EFTJanusProgramPT06WarpedNullAffineFluxFiberStokes4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D

/-- Gate 1034's source collar, now used by the explicit warped-null chart. -/
abbrev ProgramPT06WarpedNullClosedHalfCollar :=
  ProgramPT06NullFaceFiniteCollar

/-- Product atlas on the closed half-collar. -/
@[implicit_reducible] def programPT06WarpedNullClosedHalfCollarChartedSpace :
    ChartedSpace ProgramPT06NullFaceCollarModel
      ProgramPT06WarpedNullClosedHalfCollar := by
  infer_instance

theorem programPT06WarpedNullClosedHalfCollar_isManifold :
    @IsManifold Real _ ProgramPT06NullFaceCollarCoordinates _ _
      ProgramPT06NullFaceCollarModel _
      programPT06NullFaceCollarModelWithCorners ω
      ProgramPT06WarpedNullClosedHalfCollar _
      programPT06WarpedNullClosedHalfCollarChartedSpace := by
  letI : ChartedSpace ProgramPT06NullFaceCollarModel
      ProgramPT06WarpedNullClosedHalfCollar :=
    programPT06WarpedNullClosedHalfCollarChartedSpace
  infer_instance

/-- The manifold boundary consists of the two endpoint faces. -/
theorem programPT06WarpedNullClosedHalfCollar_boundary :
    letI : ChartedSpace ProgramPT06NullFaceCollarModel
        ProgramPT06WarpedNullClosedHalfCollar :=
      programPT06WarpedNullClosedHalfCollarChartedSpace
    programPT06NullFaceCollarModelWithCorners.boundary
        ProgramPT06WarpedNullClosedHalfCollar =
      Set.univ ×ˢ
        ({⊥, ⊤} : Set CutCollarInterval) := by
  letI : ChartedSpace ProgramPT06NullFaceCollarModel
      ProgramPT06WarpedNullClosedHalfCollar :=
    programPT06WarpedNullClosedHalfCollarChartedSpace
  exact boundary_product
    (modelWithCornersSelf Real ProgramPT06NullFaceSource3)

def programPT06WarpedNullZeroFace
    (source : ProgramPT06NullFaceSource3) :
    ProgramPT06WarpedNullClosedHalfCollar :=
  (source, ⊥)

def programPT06WarpedNullOuterFace
    (source : ProgramPT06NullFaceSource3) :
    ProgramPT06WarpedNullClosedHalfCollar :=
  (source, ⊤)

theorem programPT06WarpedNullZeroFace_injective :
    Function.Injective programPT06WarpedNullZeroFace := by
  intro first second hEqual
  exact congrArg Prod.fst hEqual

theorem programPT06WarpedNullOuterFace_injective :
    Function.Injective programPT06WarpedNullOuterFace := by
  intro first second hEqual
  exact congrArg Prod.fst hEqual

theorem contMDiff_programPT06WarpedNullZeroFace :
    letI : ChartedSpace ProgramPT06NullFaceCollarModel
        ProgramPT06WarpedNullClosedHalfCollar :=
      programPT06WarpedNullClosedHalfCollarChartedSpace
    ContMDiff (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
      programPT06NullFaceCollarModelWithCorners ω
      programPT06WarpedNullZeroFace := by
  letI : ChartedSpace ProgramPT06NullFaceCollarModel
      ProgramPT06WarpedNullClosedHalfCollar :=
    programPT06WarpedNullClosedHalfCollarChartedSpace
  exact contMDiff_id.prodMk contMDiff_const

theorem contMDiff_programPT06WarpedNullOuterFace :
    letI : ChartedSpace ProgramPT06NullFaceCollarModel
        ProgramPT06WarpedNullClosedHalfCollar :=
      programPT06WarpedNullClosedHalfCollarChartedSpace
    ContMDiff (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
      programPT06NullFaceCollarModelWithCorners ω
      programPT06WarpedNullOuterFace := by
  letI : ChartedSpace ProgramPT06NullFaceCollarModel
      ProgramPT06WarpedNullClosedHalfCollar :=
    programPT06WarpedNullClosedHalfCollarChartedSpace
  exact contMDiff_id.prodMk contMDiff_const

theorem range_programPT06WarpedNullZeroFace :
    Set.range programPT06WarpedNullZeroFace =
      Set.univ ×ˢ
        ({⊥} : Set CutCollarInterval) := by
  ext point
  constructor
  · rintro ⟨source, rfl⟩
    simp [programPT06WarpedNullZeroFace]
  · rintro ⟨-, hInterval⟩
    simp only [mem_singleton_iff] at hInterval
    exact ⟨point.1, Prod.ext rfl hInterval.symm⟩

theorem range_programPT06WarpedNullOuterFace :
    Set.range programPT06WarpedNullOuterFace =
      Set.univ ×ˢ
        ({⊤} : Set CutCollarInterval) := by
  ext point
  constructor
  · rintro ⟨source, rfl⟩
    simp [programPT06WarpedNullOuterFace]
  · rintro ⟨-, hInterval⟩
    simp only [mem_singleton_iff] at hInterval
    exact ⟨point.1, Prod.ext rfl hInterval.symm⟩

theorem programPT06WarpedNullClosedHalfCollar_boundary_eq_face_ranges :
    letI : ChartedSpace ProgramPT06NullFaceCollarModel
        ProgramPT06WarpedNullClosedHalfCollar :=
      programPT06WarpedNullClosedHalfCollarChartedSpace
    programPT06NullFaceCollarModelWithCorners.boundary
        ProgramPT06WarpedNullClosedHalfCollar =
      Set.range programPT06WarpedNullZeroFace ∪
        Set.range programPT06WarpedNullOuterFace := by
  rw [programPT06WarpedNullClosedHalfCollar_boundary,
    range_programPT06WarpedNullZeroFace,
    range_programPT06WarpedNullOuterFace]
  ext point
  simp only [mem_prod, mem_univ, true_and, mem_insert_iff,
    mem_singleton_iff, mem_union]

/-- Forget the interval proof and retain the global collar coordinate. -/
def programPT06WarpedNullClosedHalfCollarCoordinate
    (point : ProgramPT06WarpedNullClosedHalfCollar) :
    ProgramPT06WarpedNullCollarCoordinate4 :=
  (point.1, point.2.1)

theorem programPT06WarpedNullClosedHalfCollarCoordinate_injective :
    Function.Injective programPT06WarpedNullClosedHalfCollarCoordinate := by
  rintro ⟨firstSource, firstRadius⟩ ⟨secondSource, secondRadius⟩ hEqual
  change (firstSource, (firstRadius : Real)) =
    (secondSource, (secondRadius : Real)) at hEqual
  apply Prod.ext
  · exact congrArg
      (fun pair : ProgramPT06NullFaceSource3 × Real => pair.1) hEqual
  · apply Subtype.ext
    exact congrArg
      (fun pair : ProgramPT06NullFaceSource3 × Real => pair.2) hEqual

theorem programPT06WarpedNullClosedHalfCollarCoordinate_isEmbedding :
    IsEmbedding programPT06WarpedNullClosedHalfCollarCoordinate := by
  change IsEmbedding
    (Prod.map id (Subtype.val : CutCollarInterval → Real))
  exact Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal

/-- Embedding of the closed half-collar into ambient coordinates. -/
def programPT06WarpedNullClosedHalfCollarEmbedding
    (point : ProgramPT06WarpedNullClosedHalfCollar) :
    ProgramPT06AmbientCoordinate4 :=
  programPT06WarpedNullCollarEquiv
    (programPT06WarpedNullClosedHalfCollarCoordinate point)

theorem programPT06WarpedNullClosedHalfCollarEmbedding_injective :
    Function.Injective programPT06WarpedNullClosedHalfCollarEmbedding :=
  programPT06WarpedNullCollarEquiv.injective.comp
    programPT06WarpedNullClosedHalfCollarCoordinate_injective

theorem programPT06WarpedNullClosedHalfCollarEmbedding_isEmbedding :
    IsEmbedding programPT06WarpedNullClosedHalfCollarEmbedding := by
  exact programPT06WarpedNullCollarEquiv.toHomeomorph.isEmbedding.comp
    programPT06WarpedNullClosedHalfCollarCoordinate_isEmbedding

/-- Its ambient image is exactly the slab `0 ≤ z-u ≤ 1`. -/
theorem range_programPT06WarpedNullClosedHalfCollarEmbedding :
    Set.range programPT06WarpedNullClosedHalfCollarEmbedding =
      programPT06WarpedNullHyperplaneDefiningDifferential ⁻¹'
        Set.Icc (0 : Real) 1 := by
  ext point
  constructor
  · rintro ⟨halfCollarPoint, rfl⟩
    change programPT06WarpedNullHyperplaneDefiningDifferential
        (programPT06WarpedNullCollarEquiv
          (programPT06WarpedNullClosedHalfCollarCoordinate
            halfCollarPoint)) ∈ Set.Icc (0 : Real) 1
    rw [programPT06WarpedNullHyperplaneDefiningDifferential_collar]
    exact halfCollarPoint.2.property
  · intro hPoint
    let coordinate := programPT06WarpedNullCollarEquiv.symm point
    have hRadius : coordinate.2 ∈ Set.Icc (0 : Real) 1 := by
      have hCoordinate : programPT06WarpedNullHyperplaneDefiningDifferential
          (programPT06WarpedNullCollarEquiv coordinate) ∈
            Set.Icc (0 : Real) 1 := by
        rw [programPT06WarpedNullCollarEquiv.apply_symm_apply]
        exact hPoint
      simpa using hCoordinate
    refine ⟨(coordinate.1, ⟨coordinate.2, hRadius⟩), ?_⟩
    change programPT06WarpedNullCollarEquiv coordinate = point
    exact programPT06WarpedNullCollarEquiv.apply_symm_apply point

@[simp] theorem programPT06WarpedNullClosedHalfCollarEmbedding_zeroFace
    (source : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullClosedHalfCollarEmbedding
        (programPT06WarpedNullZeroFace source) =
      programPT06WarpedNullHyperplaneEmbedding source := by
  simp [programPT06WarpedNullClosedHalfCollarEmbedding,
    programPT06WarpedNullClosedHalfCollarCoordinate,
    programPT06WarpedNullZeroFace]

@[simp] theorem programPT06WarpedNullClosedHalfCollarEmbedding_outerFace
    (source : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullClosedHalfCollarEmbedding
        (programPT06WarpedNullOuterFace source) =
      programPT06WarpedNullCollarEquiv (source, 1) := by
  rfl

/-- Gate 1042's affine current restricted to the genuine half-collar. -/
def programPT06WarpedNullClosedHalfCollarAffineCurrent
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (point : ProgramPT06WarpedNullClosedHalfCollar) :
    ProgramPT06AmbientCoordinate4 :=
  programPT06WarpedNullCollarAffineFluxExtension density
    (programPT06WarpedNullClosedHalfCollarEmbedding point)

theorem programPT06WarpedNullClosedHalfCollarAffineCurrent_zeroFace
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (source : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullClosedHalfCollarAffineCurrent density
        (programPT06WarpedNullZeroFace source) =
      density source • programPT06WarpedNullCollarZeroBoundaryOutward := by
  rw [programPT06WarpedNullClosedHalfCollarAffineCurrent,
    programPT06WarpedNullClosedHalfCollarEmbedding_zeroFace,
    programPT06WarpedNullCollarAffineFluxExtension_zeroSlice]

@[simp] theorem programPT06WarpedNullClosedHalfCollarAffineCurrent_outerFace
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (source : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullClosedHalfCollarAffineCurrent density
        (programPT06WarpedNullOuterFace source) = 0 := by
  rw [programPT06WarpedNullClosedHalfCollarAffineCurrent,
    programPT06WarpedNullClosedHalfCollarEmbedding_outerFace,
    programPT06WarpedNullCollarAffineFluxExtension_outer_zero]

/-- The lower face has the prescribed coordinate flux with Gate 1041's fixed
outward convention. -/
theorem programPT06WarpedNullClosedHalfCollarAffineCurrent_zeroFace_flux
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (source : ProgramPT06NullFaceSource3) :
    programPT06AmbientSignedVolume.curryLeft
        (programPT06WarpedNullClosedHalfCollarAffineCurrent density
          (programPT06WarpedNullZeroFace source))
        (programPT06FiniteNullFaceGeometricTangentFrame
          (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
          0 () source) = density source := by
  rw [programPT06WarpedNullClosedHalfCollarAffineCurrent_zeroFace]
  simp only [map_smul, ContinuousAlternatingMap.smul_apply]
  rw [programPT06WarpedNullCollarZeroBoundaryOutward_flux_eq_one]
  simp

/-- Gate bundle: the manifold boundary, ambient embedding and slab, prescribed
coordinate lower flux, and zero outer current. -/
theorem programPT06WarpedNullClosedHalfCollar_current_bundle
    (density : ProgramPT06WarpedNullHyperplaneDensity) :
    letI : ChartedSpace ProgramPT06NullFaceCollarModel
        ProgramPT06WarpedNullClosedHalfCollar :=
      programPT06WarpedNullClosedHalfCollarChartedSpace
    programPT06NullFaceCollarModelWithCorners.boundary
        ProgramPT06WarpedNullClosedHalfCollar =
          Set.range programPT06WarpedNullZeroFace ∪
            Set.range programPT06WarpedNullOuterFace ∧
      IsEmbedding programPT06WarpedNullClosedHalfCollarEmbedding ∧
      Set.range programPT06WarpedNullClosedHalfCollarEmbedding =
          programPT06WarpedNullHyperplaneDefiningDifferential ⁻¹'
            Set.Icc (0 : Real) 1 ∧
        (∀ source, programPT06AmbientSignedVolume.curryLeft
          (programPT06WarpedNullClosedHalfCollarAffineCurrent density
            (programPT06WarpedNullZeroFace source))
          (programPT06FiniteNullFaceGeometricTangentFrame
            (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
            0 () source) = density source) ∧
        (∀ source, programPT06WarpedNullClosedHalfCollarAffineCurrent density
            (programPT06WarpedNullOuterFace source) = 0) :=
  ⟨programPT06WarpedNullClosedHalfCollar_boundary_eq_face_ranges,
    programPT06WarpedNullClosedHalfCollarEmbedding_isEmbedding,
    range_programPT06WarpedNullClosedHalfCollarEmbedding,
    programPT06WarpedNullClosedHalfCollarAffineCurrent_zeroFace_flux density,
    programPT06WarpedNullClosedHalfCollarAffineCurrent_outerFace density⟩

end
end P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D
end JanusFormal
