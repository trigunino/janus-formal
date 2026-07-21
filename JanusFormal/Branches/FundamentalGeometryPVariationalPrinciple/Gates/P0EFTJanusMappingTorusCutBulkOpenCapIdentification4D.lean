import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkOpenCapSmoothMappingTorus4D

/-!
# Identification of the smooth cap model with the intrinsic cut-bulk cap

The analytic mapping torus of the strict positive hemisphere embeds openly in
the positive-hemisphere cut bulk.  Its range is exactly the intrinsic cap
`latitude > 0`, hence it is homeomorphic to that cap.  Smooth transport across
this homeomorphism is left to the next atlas-gluing step.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkOpenCapIdentification4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkLatitudeBand4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkOpenCapSmoothMappingTorus4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance positiveHemisphereInteriorOpenLocallyCompactSpace :
    LocallyCompactSpace positiveHemisphereInteriorOpen :=
  positiveHemisphereInteriorOpen.2.locallyCompactSpace

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

/-- Inclusion of the strict positive sphere open into the closed positive
hemisphere. -/
def positiveHemisphereInteriorToClosed
    (point : positiveHemisphereInteriorOpen) : ClosedPositiveHemisphere :=
  ⟨point.1, point.2.le⟩

theorem continuous_positiveHemisphereInteriorToClosed :
    Continuous positiveHemisphereInteriorToClosed :=
  continuous_subtype_val.subtype_mk _

theorem positiveHemisphereInteriorToClosed_injective :
    Function.Injective positiveHemisphereInteriorToClosed := by
  intro first second hEqual
  apply Subtype.ext
  exact congrArg (fun point : ClosedPositiveHemisphere => point.1) hEqual

theorem range_positiveHemisphereInteriorToClosed :
    Set.range positiveHemisphereInteriorToClosed =
      {point : ClosedPositiveHemisphere | 0 < point.1.1 0} := by
  ext point
  constructor
  · rintro ⟨source, rfl⟩
    exact source.2
  · intro hPoint
    exact ⟨⟨point.1, hPoint⟩, rfl⟩

theorem positiveHemisphereInteriorToClosed_isOpenEmbedding :
    IsOpenEmbedding positiveHemisphereInteriorToClosed := by
  constructor
  · have hComposite : IsEmbedding
        ((Subtype.val : ClosedPositiveHemisphere → UnitThreeSphere) ∘
          positiveHemisphereInteriorToClosed) := by
      change IsEmbedding
        (fun point : positiveHemisphereInteriorOpen => point.1)
      exact IsEmbedding.subtypeVal
    exact (IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).mp hComposite
  · rw [range_positiveHemisphereInteriorToClosed]
    exact isOpen_lt continuous_const
      ((continuous_apply 0).comp
        (continuous_subtype_val.comp continuous_subtype_val))

/-- Cover-level inclusion of the analytic cap model into the cut cover. -/
def cutBulkOpenCapCoverInclusion
    (point : MappingTorusCover (cutBulkOpenCapData period hPeriod)) :
    MappingTorusCover (cutBulkData period hPeriod) :=
  ⟨positiveHemisphereInteriorToClosed point.fiber, point.time⟩

theorem cutBulkOpenCapCoverInclusion_equivariant
    (winding : Int)
    (point : MappingTorusCover (cutBulkOpenCapData period hPeriod)) :
    cutBulkOpenCapCoverInclusion period hPeriod (winding +ᵥ point) =
      winding +ᵥ cutBulkOpenCapCoverInclusion period hPeriod point := by
  apply MappingTorusCover.ext
  · change positiveHemisphereInteriorToClosed
        (((Homeomorph.refl positiveHemisphereInteriorOpen) ^ winding)
          point.fiber) =
      ((Homeomorph.refl ClosedPositiveHemisphere) ^ winding)
        (positiveHemisphereInteriorToClosed point.fiber)
    rw [show ((Homeomorph.refl positiveHemisphereInteriorOpen) ^ winding)
        point.fiber = point.fiber by
      rw [show ((Homeomorph.refl positiveHemisphereInteriorOpen) ^ winding)
          point.fiber =
        ((Homeomorph.refl positiveHemisphereInteriorOpen) ^ winding).toEquiv
          point.fiber from rfl,
        homeomorph_toEquiv_zpow]
      rw [show (Homeomorph.refl positiveHemisphereInteriorOpen).toEquiv = 1
          from rfl, one_zpow]
      rfl,
      show ((Homeomorph.refl ClosedPositiveHemisphere) ^ winding)
          (positiveHemisphereInteriorToClosed point.fiber) =
        positiveHemisphereInteriorToClosed point.fiber by
      rw [show ((Homeomorph.refl ClosedPositiveHemisphere) ^ winding)
          (positiveHemisphereInteriorToClosed point.fiber) =
        ((Homeomorph.refl ClosedPositiveHemisphere) ^ winding).toEquiv
          (positiveHemisphereInteriorToClosed point.fiber) from rfl,
        homeomorph_toEquiv_zpow]
      rw [show (Homeomorph.refl ClosedPositiveHemisphere).toEquiv = 1 from rfl,
        one_zpow]
      rfl]
  · rfl

theorem cutBulkOpenCapCoverInclusion_isOpenEmbedding :
    IsOpenEmbedding (cutBulkOpenCapCoverInclusion period hPeriod) := by
  have hProduct : IsOpenEmbedding
      (Prod.map positiveHemisphereInteriorToClosed (id : Real → Real)) :=
    positiveHemisphereInteriorToClosed_isOpenEmbedding.prodMap
      IsOpenEmbedding.id
  have hComposite :=
    (coverHomeomorphProd (cutBulkData period hPeriod)).symm.isOpenEmbedding.comp
      (hProduct.comp
        (coverHomeomorphProd
          (cutBulkOpenCapData period hPeriod)).isOpenEmbedding)
  convert hComposite using 1
  all_goals
    funext point
    rfl

/-- Induced inclusion of the smooth cap quotient into the cut bulk. -/
def smoothCutBulkOpenCapToCutBulk :
    SmoothCutBulkOpenCap period hPeriod →
      PositiveHemisphereCutBulk period hPeriod :=
  Quotient.map (cutBulkOpenCapCoverInclusion period hPeriod)
    (fun first second hOrbit => by
      change AddAction.orbitRel Int
        (MappingTorusCover (cutBulkOpenCapData period hPeriod))
        first second at hOrbit
      change AddAction.orbitRel Int
        (MappingTorusCover (cutBulkData period hPeriod))
        (cutBulkOpenCapCoverInclusion period hPeriod first)
        (cutBulkOpenCapCoverInclusion period hPeriod second)
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
      rcases hOrbit with ⟨winding, hWinding⟩
      refine ⟨winding, ?_⟩
      rw [← cutBulkOpenCapCoverInclusion_equivariant]
      exact congrArg (cutBulkOpenCapCoverInclusion period hPeriod) hWinding)

theorem continuous_smoothCutBulkOpenCapToCutBulk :
    Continuous (smoothCutBulkOpenCapToCutBulk period hPeriod) := by
  apply (continuous_quotient_mk'.comp ?_).quotient_lift
  exact (cutBulkOpenCapCoverInclusion_isOpenEmbedding period hPeriod).continuous

theorem smoothCutBulkOpenCapToCutBulk_injective :
    Function.Injective (smoothCutBulkOpenCapToCutBulk period hPeriod) := by
  intro first second
  refine Quotient.inductionOn first ?_
  intro firstRepresentative
  refine Quotient.inductionOn second ?_
  intro secondRepresentative hEqual
  change mappingTorusMk (cutBulkData period hPeriod)
      (cutBulkOpenCapCoverInclusion period hPeriod firstRepresentative) =
    mappingTorusMk (cutBulkData period hPeriod)
      (cutBulkOpenCapCoverInclusion period hPeriod secondRepresentative)
      at hEqual
  rw [mappingTorusMk_eq_iff_exists_vadd] at hEqual ⊢
  rcases hEqual with ⟨winding, hWinding⟩
  refine ⟨winding, ?_⟩
  apply (cutBulkOpenCapCoverInclusion_isOpenEmbedding period hPeriod).injective
  rw [cutBulkOpenCapCoverInclusion_equivariant]
  exact hWinding

theorem range_smoothCutBulkOpenCapToCutBulk :
    Set.range (smoothCutBulkOpenCapToCutBulk period hPeriod) =
      cutBulkOpenCap period hPeriod := by
  ext bulk
  constructor
  · rintro ⟨cap, rfl⟩
    refine Quotient.inductionOn cap ?_
    intro representative
    exact representative.fiber.2
  · intro hBulk
    refine Quotient.inductionOn bulk ?_ hBulk
    intro representative hPositive
    change 0 < representative.fiber.1.1 0 at hPositive
    let capRepresentative :
        MappingTorusCover (cutBulkOpenCapData period hPeriod) :=
      ⟨⟨representative.fiber.1, hPositive⟩, representative.time⟩
    refine ⟨mappingTorusMk (cutBulkOpenCapData period hPeriod)
      capRepresentative, ?_⟩
    apply congrArg (mappingTorusMk (cutBulkData period hPeriod))
    rfl

theorem smoothCutBulkOpenCapToCutBulk_isOpenMap :
    IsOpenMap (smoothCutBulkOpenCapToCutBulk period hPeriod) := by
  intro source hSource
  let sourceProjection :=
    mappingTorusMk (cutBulkOpenCapData period hPeriod)
  let targetProjection := mappingTorusMk (cutBulkData period hPeriod)
  have hSourcePreimage : IsOpen (sourceProjection ⁻¹' source) :=
    hSource.preimage continuous_quotient_mk'
  have hCoverImage : IsOpen
      (cutBulkOpenCapCoverInclusion period hPeriod ''
        (sourceProjection ⁻¹' source)) :=
    (cutBulkOpenCapCoverInclusion_isOpenEmbedding period hPeriod).isOpenMap
      _ hSourcePreimage
  have hTargetImage : IsOpen
      (targetProjection ''
        (cutBulkOpenCapCoverInclusion period hPeriod ''
          (sourceProjection ⁻¹' source))) :=
    (mappingTorusMk_isCoveringMap
      (cutBulkData period hPeriod)).isLocalHomeomorph.isOpenMap _ hCoverImage
  have hImage : smoothCutBulkOpenCapToCutBulk period hPeriod '' source =
      targetProjection ''
        (cutBulkOpenCapCoverInclusion period hPeriod ''
          (sourceProjection ⁻¹' source)) := by
    ext target
    constructor
    · rintro ⟨cap, hCap, rfl⟩
      obtain ⟨representative, rfl⟩ :=
        mappingTorusMk_surjective (cutBulkOpenCapData period hPeriod) cap
      exact ⟨cutBulkOpenCapCoverInclusion period hPeriod representative,
        ⟨representative, hCap, rfl⟩, rfl⟩
    · rintro ⟨-, ⟨representative, hRepresentative, rfl⟩, rfl⟩
      exact ⟨sourceProjection representative, hRepresentative, rfl⟩
  rw [hImage]
  exact hTargetImage

theorem smoothCutBulkOpenCapToCutBulk_isOpenEmbedding :
    IsOpenEmbedding (smoothCutBulkOpenCapToCutBulk period hPeriod) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_smoothCutBulkOpenCapToCutBulk period hPeriod)
    (smoothCutBulkOpenCapToCutBulk_injective period hPeriod)
    (smoothCutBulkOpenCapToCutBulk_isOpenMap period hPeriod)

/-- Canonical homeomorphism from the analytic cap model to the intrinsic cap. -/
def smoothCutBulkOpenCapHomeomorph :
    SmoothCutBulkOpenCap period hPeriod ≃ₜ CutBulkOpenCap period hPeriod :=
  (smoothCutBulkOpenCapToCutBulk_isOpenEmbedding period hPeriod).isEmbedding
    |>.toHomeomorph |>.trans
      (Homeomorph.setCongr (range_smoothCutBulkOpenCapToCutBulk period hPeriod))

end
end P0EFTJanusMappingTorusCutBulkOpenCapIdentification4D
end JanusFormal
