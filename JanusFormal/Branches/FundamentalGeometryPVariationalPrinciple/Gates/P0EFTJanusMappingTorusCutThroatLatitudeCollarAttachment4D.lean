import Mathlib.Topology.CompactOpen
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialTubularOpenEmbedding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryClosedEmbedding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D

/-!
# Latitude attachment of the finite cut collar

The existing equatorial tubular coordinates restrict to positive latitudes
`[0,1]`.  After doubling the period, their deck action is untwisted, so this
finite collar descends to the positive-hemisphere cut bulk.  The map is
continuous and injective, agrees with the cut-boundary inclusion at latitude
zero, and has an explicit outer gluing face.  No global smooth gluing or
Stokes theorem is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Set Topology
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Positive unit latitudes lie in the already-proved tubular coordinate
domain. -/
def unitCollarTubularParameter
    (parameter : EquatorialTwoSphere × CutCollarInterval) :
    EquatorialTubularParameter :=
  (parameter.1, ⟨parameter.2.1, by
    constructor <;> linarith [parameter.2.2.1, parameter.2.2.2,
      Real.pi_gt_three]⟩)

/-- Fiber map from the equator times `[0,1]` into the closed positive
hemisphere. -/
def positiveLatitudeFiber
    (parameter : EquatorialTwoSphere × CutCollarInterval) :
    ClosedPositiveHemisphere :=
  ⟨equatorialLatitude parameter.1 parameter.2.1,
    Real.sin_nonneg_of_nonneg_of_le_pi parameter.2.2.1
      (by linarith [parameter.2.2.2, Real.pi_gt_three])⟩

theorem positiveLatitudeFiber_injective :
    Function.Injective positiveLatitudeFiber := by
  intro first second hEqual
  have hParameter : unitCollarTubularParameter first =
      unitCollarTubularParameter second :=
    equatorialTubularMap_injective (congrArg Subtype.val hEqual)
  apply Prod.ext
  · exact congrArg (fun point : EquatorialTubularParameter => point.1)
      hParameter
  · apply Subtype.ext
    exact congrArg (fun point : EquatorialTubularParameter => point.2.1)
      hParameter

private theorem refl_zpow_apply {X : Type} [TopologicalSpace X]
    (winding : Int) (point : X) :
    ((Homeomorph.refl X) ^ winding) point = point := by
  rw [show ((Homeomorph.refl X) ^ winding) point =
      ((Homeomorph.refl X) ^ winding).toEquiv point from rfl,
    homeomorph_toEquiv_zpow]
  rw [show (Homeomorph.refl X).toEquiv = 1 from rfl, one_zpow]
  rfl

/-- Cover-level latitude attachment, preserving the doubled time coordinate. -/
def cutCollarCoverAttachment
    (parameter : MappingTorusCover (orientationDoubleData period hPeriod) ×
      CutCollarInterval) :
    MappingTorusCover (cutBulkData period hPeriod) :=
  ⟨positiveLatitudeFiber (parameter.1.fiber, parameter.2), parameter.1.time⟩

theorem cutCollarCoverAttachment_equivariant
    (winding : Int)
    (anchor : MappingTorusCover (orientationDoubleData period hPeriod))
    (normal : CutCollarInterval) :
    cutCollarCoverAttachment period hPeriod (winding +ᵥ anchor, normal) =
      winding +ᵥ cutCollarCoverAttachment period hPeriod (anchor, normal) := by
  apply MappingTorusCover.ext
  · change positiveLatitudeFiber
        (((Homeomorph.refl EquatorialTwoSphere) ^ winding) anchor.fiber, normal) =
      ((Homeomorph.refl ClosedPositiveHemisphere) ^ winding)
        (positiveLatitudeFiber (anchor.fiber, normal))
    rw [refl_zpow_apply, refl_zpow_apply]
  · rfl

/-- The finite analytic collar attached topologically to the cut bulk. -/
def cutCollarAttachment :
    CutThroatFiniteCollar period hPeriod →
      PositiveHemisphereCutBulk period hPeriod :=
  fun parameter =>
    Quotient.map
      (fun anchor => cutCollarCoverAttachment period hPeriod
        (anchor, parameter.2))
      (fun first second hOrbit => by
        change AddAction.orbitRel Int
          (MappingTorusCover (orientationDoubleData period hPeriod))
          first second at hOrbit
        change AddAction.orbitRel Int
          (MappingTorusCover (cutBulkData period hPeriod))
          (cutCollarCoverAttachment period hPeriod (first, parameter.2))
          (cutCollarCoverAttachment period hPeriod (second, parameter.2))
        rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
        rcases hOrbit with ⟨winding, hWinding⟩
        refine ⟨winding, ?_⟩
        rw [← cutCollarCoverAttachment_equivariant]
        exact congrArg
          (fun anchor => cutCollarCoverAttachment period hPeriod
            (anchor, parameter.2)) hWinding)
      parameter.1

theorem continuous_cutCollarCoverAttachmentQuotient :
    Continuous (fun parameter :
      MappingTorusCover (orientationDoubleData period hPeriod) ×
        CutCollarInterval =>
      mappingTorusMk (cutBulkData period hPeriod)
        (cutCollarCoverAttachment period hPeriod parameter)) := by
  have hBase : Continuous (fun parameter :
      MappingTorusCover (orientationDoubleData period hPeriod) ×
        CutCollarInterval => parameter.1.fiber) :=
    (continuous_fiber (orientationDoubleData period hPeriod)).comp
      continuous_fst
  have hNormal : Continuous (fun parameter :
      MappingTorusCover (orientationDoubleData period hPeriod) ×
        CutCollarInterval => parameter.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hLatitude : Continuous (fun parameter :
      MappingTorusCover (orientationDoubleData period hPeriod) ×
        CutCollarInterval =>
      equatorialLatitude parameter.1.fiber parameter.2.1) :=
    by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro index
      refine Fin.cases ?_ (fun tail => ?_) index
      · exact Real.continuous_sin.comp hNormal
      · exact (Real.continuous_cos.comp hNormal).mul
          ((continuous_apply tail.succ).comp
            (continuous_subtype_val.comp hBase))
  have hFiber : Continuous (fun parameter :
      MappingTorusCover (orientationDoubleData period hPeriod) ×
        CutCollarInterval =>
      positiveLatitudeFiber (parameter.1.fiber, parameter.2)) :=
    hLatitude.subtype_mk _
  have hTime : Continuous (fun parameter :
      MappingTorusCover (orientationDoubleData period hPeriod) ×
        CutCollarInterval => parameter.1.time) :=
    (continuous_time _).comp continuous_fst
  have hCover := (coverHomeomorphProd (cutBulkData period hPeriod)).symm.continuous.comp
    (hFiber.prodMk hTime)
  exact continuous_quotient_mk'.comp (hCover.congr fun _ => rfl)

theorem continuous_cutCollarAttachment :
    Continuous (cutCollarAttachment period hPeriod) := by
  apply isQuotientMap_quotient_mk'.continuous_lift_prod_left
  convert continuous_cutCollarCoverAttachmentQuotient period hPeriod using 1
  funext parameter
  rfl

theorem cutCollarAttachment_injective :
    Function.Injective (cutCollarAttachment period hPeriod) := by
  rintro ⟨firstBoundary, firstNormal⟩ ⟨secondBoundary, secondNormal⟩ hEqual
  refine Quotient.inductionOn firstBoundary ?_ hEqual
  intro first
  refine Quotient.inductionOn secondBoundary ?_
  intro second hEqual
  change mappingTorusMk (cutBulkData period hPeriod)
      (cutCollarCoverAttachment period hPeriod (first, firstNormal)) =
    mappingTorusMk (cutBulkData period hPeriod)
      (cutCollarCoverAttachment period hPeriod (second, secondNormal)) at hEqual
  rw [mappingTorusMk_eq_iff_exists_vadd] at hEqual
  rcases hEqual with ⟨winding, hWinding⟩
  rw [← cutCollarCoverAttachment_equivariant] at hWinding
  have hPair : ((winding +ᵥ second).fiber, secondNormal) =
      (first.fiber, firstNormal) :=
    positiveLatitudeFiber_injective
      (congrArg (fun point : MappingTorusCover (cutBulkData period hPeriod) =>
        point.fiber) hWinding)
  have hBoundary : mappingTorusMk (orientationDoubleData period hPeriod) first =
      mappingTorusMk (orientationDoubleData period hPeriod) second := by
    rw [mappingTorusMk_eq_iff_exists_vadd]
    refine ⟨winding, ?_⟩
    apply MappingTorusCover.ext
    · exact congrArg Prod.fst hPair
    · exact congrArg (fun point : MappingTorusCover (cutBulkData period hPeriod) =>
        point.time) hWinding
  exact Prod.ext hBoundary (congrArg Prod.snd hPair).symm

theorem cutCollarAttachment_cutThroatFace
    (boundary : CutThroatBoundary period hPeriod) :
    cutCollarAttachment period hPeriod
        (cutThroatFace period hPeriod boundary) =
      cutBoundaryInclusion period hPeriod boundary := by
  refine Quotient.inductionOn boundary ?_
  intro representative
  change mappingTorusMk (cutBulkData period hPeriod)
      (cutCollarCoverAttachment period hPeriod (representative, ⊥)) =
    mappingTorusMk (cutBulkData period hPeriod)
      (cutBoundaryCoverToCutBulk period hPeriod representative)
  apply congrArg (mappingTorusMk (cutBulkData period hPeriod))
  apply MappingTorusCover.ext
  · simp [cutCollarCoverAttachment, positiveLatitudeFiber,
      cutBoundaryCoverToCutBulk]
  · simp [cutCollarCoverAttachment, cutBoundaryCoverToCutBulk]

/-- Explicit artificial interface supplied by latitude one. -/
def cutOuterLatitudeInclusion
    (boundary : CutThroatBoundary period hPeriod) :
    PositiveHemisphereCutBulk period hPeriod :=
  cutCollarAttachment period hPeriod (cutOuterFace period hPeriod boundary)

theorem cutCollarAttachment_cutOuterFace
    (boundary : CutThroatBoundary period hPeriod) :
    cutCollarAttachment period hPeriod
        (cutOuterFace period hPeriod boundary) =
      cutOuterLatitudeInclusion period hPeriod boundary := rfl

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

local instance cutCollarCompactSpace :
    CompactSpace (CutThroatFiniteCollar period hPeriod) := inferInstance

theorem cutCollarAttachment_isClosedEmbedding :
    IsClosedEmbedding (cutCollarAttachment period hPeriod) :=
  (continuous_cutCollarAttachment period hPeriod).isClosedEmbedding
    (cutCollarAttachment_injective period hPeriod)

theorem continuous_cutOuterLatitudeInclusion :
    Continuous (cutOuterLatitudeInclusion period hPeriod) :=
  (continuous_cutCollarAttachment period hPeriod).comp
    (continuous_id.prodMk continuous_const)

theorem cutOuterLatitudeInclusion_injective :
    Function.Injective (cutOuterLatitudeInclusion period hPeriod) :=
  (cutCollarAttachment_injective period hPeriod).comp
    (cutOuterFace_injective period hPeriod)

theorem cutOuterLatitudeInclusion_isClosedEmbedding :
    IsClosedEmbedding (cutOuterLatitudeInclusion period hPeriod) :=
  (continuous_cutOuterLatitudeInclusion period hPeriod).isClosedEmbedding
    (cutOuterLatitudeInclusion_injective period hPeriod)

end
end P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
end JanusFormal
