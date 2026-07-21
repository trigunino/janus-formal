import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialBandScalarCurrentDeckTwist4D

/-!
# Smooth scalar-current descent to the cut boundary

The latitude Green current is sign-twisted on the original quotient.  On the
orientation-double boundary only even windings are identified, so the sign
character is trivial and the current descends to a genuine smooth scalar.
The residual deck involution still negates that scalar and exchanges the two
lifts over each throat point.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusEquatorialBandScalarCurrentZeroExtension4D
open P0EFTJanusEquatorialBandScalarCurrentDeckTwist4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryCover :=
  MappingTorusCover (orientationDoubleData period hPeriod)

local instance boundaryCoverChartedSpace :
    ChartedSpace ThroatCoverModel (BoundaryCover period hPeriod) :=
  fixedThroatCoverChartedSpace
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance boundaryCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω (BoundaryCover period hPeriod) :=
  fixedThroatCover_isManifold
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance boundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance boundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  cutThroatBoundary_isManifold period hPeriod

private theorem refl_zpow_apply {X : Type} [TopologicalSpace X]
    (winding : Int) (point : X) :
    ((Homeomorph.refl X) ^ winding) point = point := by
  rw [show ((Homeomorph.refl X) ^ winding) point =
      ((Homeomorph.refl X) ^ winding).toEquiv point from rfl,
    homeomorph_toEquiv_zpow]
  rw [show (Homeomorph.refl X).toEquiv = 1 from rfl, one_zpow]
  rfl

/-- Upstairs current restricted to the doubled equatorial cover. -/
def cutBoundaryScalarCurrentCover
    (field test : SmoothQuotientField period hPeriod Real)
    (point : BoundaryCover period hPeriod) : Real :=
  equatorialBandScalarCurrentZeroExtension period hPeriod field test
    (equatorialSphereInclusion point.fiber, point.time)

theorem cutBoundaryScalarCurrentCover_contMDiff
    (field test : SmoothQuotientField period hPeriod Real) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (cutBoundaryScalarCurrentCover period hPeriod field test) := by
  have hTo := chartedSpacePullback_toFun_contMDiff
    throatCoverModelWithCorners ω
    (coverHomeomorphProd (orientationDoubleData period hPeriod))
  have hToSmooth :
      ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ∞
        (coverHomeomorphProd (orientationDoubleData period hPeriod)) :=
    hTo.of_le (by simp)
  have hSphere :
      ContMDiff
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2)))
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))) ∞
        equatorialSphereInclusion :=
    equatorialSphereInclusion_contMDiff.of_le (by simp)
  have hInclusion :
      ContMDiff throatCoverModelWithCorners coverModelWithCorners ∞
        (Prod.map equatorialSphereInclusion (id : Real → Real)) :=
    hSphere.prodMap
      (contMDiff_id : ContMDiff (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real) ∞ (id : Real → Real))
  exact (equatorialBandScalarCurrentZeroExtension_contMDiff
      period hPeriod field test).comp (hInclusion.comp hToSmooth)

private theorem cutBoundaryInput_even_vadd
    (winding : Int) (point : BoundaryCover period hPeriod) :
    (equatorialSphereInclusion (winding +ᵥ point).fiber,
        (winding +ᵥ point).time) =
      reflectedSphereProductDeck period (2 * winding)
        (equatorialSphereInclusion point.fiber, point.time) := by
  apply Prod.ext
  · change equatorialSphereInclusion
        (((Homeomorph.refl EquatorialTwoSphere) ^ winding) point.fiber) =
      (sphereReflection ^ (2 * winding))
        (equatorialSphereInclusion point.fiber)
    rw [refl_zpow_apply, sphereReflection_zpow_fixes_equator]
  · change point.time + (winding : Real) * (2 * period) =
      point.time + ((2 * winding : Int) : Real) * period
    push_cast
    ring

theorem cutBoundaryScalarCurrentCover_invariant
    (field test : SmoothQuotientField period hPeriod Real)
    (winding : Int) (point : BoundaryCover period hPeriod) :
    cutBoundaryScalarCurrentCover period hPeriod field test (winding +ᵥ point) =
      cutBoundaryScalarCurrentCover period hPeriod field test point := by
  simp only [cutBoundaryScalarCurrentCover]
  rw [cutBoundaryInput_even_vadd]
  have hEquivariant :=
    SmoothAmbientNormalSignLift.deck_sign (period := period)
      (equatorialBandScalarCurrentNormalSignLift period hPeriod field test)
      (2 * winding) (equatorialSphereInclusion point.fiber, point.time)
  rw [pulledBack_normal_sign_trivial, Units.val_one, one_mul] at hEquivariant
  exact hEquivariant

/-- Genuine scalar current on the connected cut-boundary double cover. -/
def cutBoundaryScalarCurrent
    (field test : SmoothQuotientField period hPeriod Real) :
    CutThroatBoundary period hPeriod → Real :=
  Quotient.lift (cutBoundaryScalarCurrentCover period hPeriod field test)
    (fun first second hOrbit ↦ by
      change AddAction.orbitRel Int (BoundaryCover period hPeriod)
        first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      rw [← hWinding]
      exact cutBoundaryScalarCurrentCover_invariant
        period hPeriod field test winding second)

@[simp] theorem cutBoundaryScalarCurrent_mk
    (field test : SmoothQuotientField period hPeriod Real)
    (point : BoundaryCover period hPeriod) :
    cutBoundaryScalarCurrent period hPeriod field test
        (mappingTorusMk (orientationDoubleData period hPeriod) point) =
      cutBoundaryScalarCurrentCover period hPeriod field test point :=
  rfl

theorem cutBoundaryScalarCurrent_contMDiff
    (field test : SmoothQuotientField period hPeriod Real) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (cutBoundaryScalarCurrent period hPeriod field test) := by
  intro boundary
  obtain ⟨coverPoint, rfl⟩ :=
    mappingTorusMk_surjective (orientationDoubleData period hPeriod) boundary
  have hProjection :
      IsLocalDiffeomorph throatCoverModelWithCorners throatCoverModelWithCorners ω
        (mappingTorusMk (orientationDoubleData period hPeriod)) :=
    fixedThroat_projection_isLocalDiffeomorph
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  have hAt := hProjection coverPoint
  have hLocal :
      ContMDiffAt throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
        (cutBoundaryScalarCurrentCover period hPeriod field test ∘ hAt.localInverse)
        (mappingTorusMk (orientationDoubleData period hPeriod) coverPoint) :=
    (cutBoundaryScalarCurrentCover_contMDiff period hPeriod field test).contMDiffAt.comp _
      (hAt.localInverse_contMDiffAt.of_le (by simp))
  apply hLocal.congr_of_eventuallyEq
  filter_upwards [hAt.localInverse_eventuallyEq_right] with point hPoint
  have hPoint' :
      mappingTorusMk (orientationDoubleData period hPeriod) (hAt.localInverse point) =
        point := by
    simpa [Function.comp_def] using hPoint
  calc
    cutBoundaryScalarCurrent period hPeriod field test point =
        cutBoundaryScalarCurrent period hPeriod field test
          (mappingTorusMk (orientationDoubleData period hPeriod)
            (hAt.localInverse point)) := congrArg _ hPoint'.symm
    _ = cutBoundaryScalarCurrentCover period hPeriod field test
        (hAt.localInverse point) := rfl

private theorem cutBoundaryInput_deck
    (point : BoundaryCover period hPeriod) :
    (equatorialSphereInclusion
        (orientationDeckCover period hPeriod point).fiber,
      (orientationDeckCover period hPeriod point).time) =
      reflectedSphereProductDeck period 1
        (equatorialSphereInclusion point.fiber, point.time) := by
  apply Prod.ext
  · change equatorialSphereInclusion point.fiber =
      sphereReflection (equatorialSphereInclusion point.fiber)
    exact (sphereReflection_fixes_equator point.fiber).symm
  · simp [reflectedSphereProductDeck]

/-- The residual deck involution exchanges the two lifts and negates their
scalar current values. -/
theorem cutBoundaryScalarCurrent_deck
    (field test : SmoothQuotientField period hPeriod Real)
    (boundary : CutThroatBoundary period hPeriod) :
    cutBoundaryScalarCurrent period hPeriod field test
        (orientationDeck period hPeriod boundary) =
      -cutBoundaryScalarCurrent period hPeriod field test boundary := by
  refine Quotient.inductionOn boundary ?_
  intro point
  change cutBoundaryScalarCurrentCover period hPeriod field test
      (orientationDeckCover period hPeriod point) =
    -cutBoundaryScalarCurrentCover period hPeriod field test point
  rw [cutBoundaryScalarCurrentCover, cutBoundaryScalarCurrentCover,
    cutBoundaryInput_deck]
  exact equatorialBandScalarCurrentZeroExtension_deck_generator
    period hPeriod field test _

end
end P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D
end JanusFormal
