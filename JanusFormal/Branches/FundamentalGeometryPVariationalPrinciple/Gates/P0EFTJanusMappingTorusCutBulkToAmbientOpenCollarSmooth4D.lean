import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquivariantSmoothDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkScalarCurrentOpenCollarSmooth4D

/-!
# Smoothness of the cut-bulk map on the open collar

The natural map from the cut bulk to the original mapping torus is smooth on
the finite collar, hence on its intrinsic open subcollar.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkToAmbientOpenCollarSmooth4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusMappingTorusEquivariantSmoothDescent4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev BoundaryCover :=
  MappingTorusCover (orientationDoubleData period hPeriod)

private abbrev AmbientCover :=
  MappingTorusCover (reflectedSphereData period hPeriod)

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

local instance finiteCollarChartedSpace :
    ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
  cutThroatFiniteCollarChartedSpace period hPeriod

local instance openCollarChartedSpace :
    ChartedSpace CutCollarModel (CutThroatOpenCollar period hPeriod) :=
  cutThroatOpenCollarChartedSpace period hPeriod

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance ambientCoverChartedSpace :
    ChartedSpace CoverModel (AmbientCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance ambientCoverIsManifold :
    IsManifold coverModelWithCorners ω (AmbientCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

/-- Cover formula for the cut-bulk map pulled back to collar parameters. -/
def cutBulkToAmbientCollarCover
    (parameter : BoundaryCover period hPeriod × CutCollarInterval) :
    EffectiveQuotient period hPeriod :=
  mappingTorusMk (reflectedSphereData period hPeriod)
    (cutBulkCoverToAmbient period hPeriod
      (cutCollarCoverAttachment period hPeriod parameter))

theorem cutBulkToAmbientCollarCover_contMDiff :
    ContMDiff cutCollarModelWithCorners coverModelWithCorners ∞
      (cutBulkToAmbientCollarCover period hPeriod) := by
  have hTo : ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ∞
      (coverHomeomorphProd (orientationDoubleData period hPeriod)) :=
    (chartedSpacePullback_toFun_contMDiff throatCoverModelWithCorners ω
      (coverHomeomorphProd (orientationDoubleData period hPeriod))).of_le (by simp)
  have hAnchor : ContMDiff cutCollarModelWithCorners
      throatCoverModelWithCorners ∞
      (fun parameter : BoundaryCover period hPeriod × CutCollarInterval ↦
        coverHomeomorphProd (orientationDoubleData period hPeriod) parameter.1) :=
    hTo.comp contMDiff_fst
  have hEquator := contMDiff_fst.comp hAnchor
  have hNormal : ContMDiff cutCollarModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun parameter : BoundaryCover period hPeriod × CutCollarInterval ↦
        parameter.2.1) :=
    contMDiff_subtype_coe_Icc.comp contMDiff_snd
  have hLatitude := equatorialLatitude_joint_contMDiff.comp
    (hEquator.prodMk hNormal)
  have hTime := contMDiff_snd.comp hAnchor
  have hCover : ContMDiff cutCollarModelWithCorners coverModelWithCorners ∞
      (fun parameter : BoundaryCover period hPeriod × CutCollarInterval ↦
        (coverHomeomorphProd (reflectedSphereData period hPeriod)).symm
          (equatorialLatitude parameter.1.fiber parameter.2.1,
            parameter.1.time)) :=
    (chartedSpacePullback_invFun_contMDiff coverModelWithCorners ∞
      (coverHomeomorphProd (reflectedSphereData period hPeriod))).comp
        (hLatitude.prodMk hTime)
  exact (((reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
    |>.of_le (by simp)).comp hCover).congr fun _ ↦ rfl

private def partialDiffeomorphProd
    {E H M E' H' M' F G N F' G' N' : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup E'] [NormedSpace Real E'] [TopologicalSpace H']
    [TopologicalSpace M'] [ChartedSpace H' M']
    [NormedAddCommGroup F] [NormedSpace Real F] [TopologicalSpace G]
    [TopologicalSpace N] [ChartedSpace G N]
    [NormedAddCommGroup F'] [NormedSpace Real F'] [TopologicalSpace G']
    [TopologicalSpace N'] [ChartedSpace G' N']
    {I : ModelWithCorners Real E H} {I' : ModelWithCorners Real E' H'}
    {J : ModelWithCorners Real F G} {J' : ModelWithCorners Real F' G'}
    {n : ℕ∞ω}
    (Φ : PartialDiffeomorph I I' M M' n)
    (Ψ : PartialDiffeomorph J J' N N' n) :
    PartialDiffeomorph (I.prod J) (I'.prod J') (M × N) (M' × N') n where
  __ := Φ.toOpenPartialHomeomorph.prod Ψ.toOpenPartialHomeomorph
  contMDiffOn_toFun := Φ.contMDiffOn.prodMap Ψ.contMDiffOn
  contMDiffOn_invFun := Φ.symm.contMDiffOn.prodMap Ψ.symm.contMDiffOn

private theorem cutCollarProjection_isLocalDiffeomorph :
    IsLocalDiffeomorph cutCollarModelWithCorners cutCollarModelWithCorners ω
      (Prod.map (mappingTorusMk (orientationDoubleData period hPeriod))
        (id : CutCollarInterval → CutCollarInterval)) := by
  intro parameter
  obtain ⟨Φ, hΦ, hEq⟩ :=
    (fixedThroat_projection_isLocalDiffeomorph
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)) parameter.1
  obtain ⟨Ψ, hΨ, hEq'⟩ :=
    (Diffeomorph.refl (modelWithCornersEuclideanHalfSpace 1)
      CutCollarInterval ω).isLocalDiffeomorph parameter.2
  refine ⟨partialDiffeomorphProd Φ Ψ, ⟨hΦ, hΨ⟩, ?_⟩
  rintro ⟨anchor, normal⟩ ⟨hAnchor, hNormal⟩
  exact Prod.ext (hEq hAnchor) (hEq' hNormal)

theorem cutBulkToAmbient_finiteCollar_contMDiff :
    ContMDiff cutCollarModelWithCorners coverModelWithCorners ∞
      (fun parameter : CutThroatFiniteCollar period hPeriod ↦
        cutBulkToAmbient period hPeriod
          (cutCollarAttachment period hPeriod parameter)) := by
  rintro ⟨boundary, normal⟩
  obtain ⟨anchor, rfl⟩ := mappingTorusMk_surjective
    (orientationDoubleData period hPeriod) boundary
  let coverParameter : BoundaryCover period hPeriod × CutCollarInterval :=
    (anchor, normal)
  have hAt := (cutCollarProjection_isLocalDiffeomorph
    period hPeriod) coverParameter
  have hLocal : ContMDiffAt cutCollarModelWithCorners coverModelWithCorners ∞
      (cutBulkToAmbientCollarCover period hPeriod ∘ hAt.localInverse)
      (mappingTorusMk (orientationDoubleData period hPeriod) anchor, normal) :=
    (cutBulkToAmbientCollarCover_contMDiff period hPeriod).contMDiffAt.comp _
      (hAt.localInverse_contMDiffAt.of_le (by simp))
  apply hLocal.congr_of_eventuallyEq
  filter_upwards [hAt.localInverse_eventuallyEq_right] with point hPoint
  have hPoint' :
      Prod.map (mappingTorusMk (orientationDoubleData period hPeriod))
          (id : CutCollarInterval → CutCollarInterval) (hAt.localInverse point) =
        point := by
    simpa [Function.comp_def] using hPoint
  calc
    cutBulkToAmbient period hPeriod
        (cutCollarAttachment period hPeriod point) =
      cutBulkToAmbient period hPeriod
        (cutCollarAttachment period hPeriod
          (Prod.map (mappingTorusMk (orientationDoubleData period hPeriod))
            (id : CutCollarInterval → CutCollarInterval)
            (hAt.localInverse point))) :=
      congrArg (fun current ↦ cutBulkToAmbient period hPeriod
        (cutCollarAttachment period hPeriod current)) hPoint'.symm
    _ = cutBulkToAmbientCollarCover period hPeriod
        (hAt.localInverse point) := rfl

theorem cutBulkToAmbient_openCollar_contMDiff :
    ContMDiff cutCollarModelWithCorners coverModelWithCorners ∞
      (fun parameter : CutThroatOpenCollar period hPeriod ↦
        cutBulkToAmbient period hPeriod
          (cutOpenCollarAttachment period hPeriod parameter)) := by
  exact (cutBulkToAmbient_finiteCollar_contMDiff period hPeriod).comp
    ((cutThroatOpenCollar_val_contMDiff period hPeriod).of_le (by simp))

end
end P0EFTJanusMappingTorusCutBulkToAmbientOpenCollarSmooth4D
end JanusFormal
