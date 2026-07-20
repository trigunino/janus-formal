import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalLatitudeScalarCurrentJointSmooth4D

/-!
# Smooth cutoff current on the open cut-bulk collar

The bulk current pulled back through the canonical collar attachment is smooth.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkScalarCurrentOpenCollarSmooth4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusEquatorialBandScalarCurrentZeroExtension4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D

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

local instance finiteCollarChartedSpace :
    ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
  cutThroatFiniteCollarChartedSpace period hPeriod

local instance openCollarChartedSpace :
    ChartedSpace CutCollarModel (CutThroatOpenCollar period hPeriod) :=
  cutThroatOpenCollarChartedSpace period hPeriod

def cutBulkScalarCurrentCollarCover
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : BoundaryCover period hPeriod × CutCollarInterval) : Real :=
  cutBulkScalarCurrentCover period hPeriod field test
    (cutCollarCoverAttachment period hPeriod parameter)

theorem cutBulkScalarCurrentCollarCover_contMDiff
    (field test : SmoothQuotientField period hPeriod Real) :
    ContMDiff cutCollarModelWithCorners (modelWithCornersSelf Real Real) ∞
      (cutBulkScalarCurrentCollarCover period hPeriod field test) := by
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
  exact ((equatorialBandScalarCurrentZeroExtension_contMDiff
      period hPeriod field test).comp (hLatitude.prodMk hTime)).congr fun _ ↦ rfl

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

theorem cutBulkScalarCurrent_finiteCollar_contMDiff
    (field test : SmoothQuotientField period hPeriod Real) :
    ContMDiff cutCollarModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun parameter : CutThroatFiniteCollar period hPeriod ↦
        cutBulkScalarCurrent period hPeriod field test
          (cutCollarAttachment period hPeriod parameter)) := by
  rintro ⟨boundary, normal⟩
  obtain ⟨anchor, rfl⟩ := mappingTorusMk_surjective
    (orientationDoubleData period hPeriod) boundary
  let coverParameter : BoundaryCover period hPeriod × CutCollarInterval :=
    (anchor, normal)
  have hAt := (cutCollarProjection_isLocalDiffeomorph period hPeriod) coverParameter
  have hLocal : ContMDiffAt cutCollarModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (cutBulkScalarCurrentCollarCover period hPeriod field test ∘ hAt.localInverse)
      (mappingTorusMk (orientationDoubleData period hPeriod) anchor,
        normal) :=
    (cutBulkScalarCurrentCollarCover_contMDiff period hPeriod field test)
      |>.contMDiffAt.comp _ (hAt.localInverse_contMDiffAt.of_le (by simp))
  apply hLocal.congr_of_eventuallyEq
  filter_upwards [hAt.localInverse_eventuallyEq_right] with point hPoint
  have hPoint' :
      Prod.map (mappingTorusMk (orientationDoubleData period hPeriod))
          (id : CutCollarInterval → CutCollarInterval) (hAt.localInverse point) =
        point := by
    simpa [Function.comp_def] using hPoint
  calc
    cutBulkScalarCurrent period hPeriod field test
        (cutCollarAttachment period hPeriod point) =
      cutBulkScalarCurrent period hPeriod field test
        (cutCollarAttachment period hPeriod
          (Prod.map (mappingTorusMk (orientationDoubleData period hPeriod))
            (id : CutCollarInterval → CutCollarInterval)
            (hAt.localInverse point))) :=
      congrArg (fun current ↦ cutBulkScalarCurrent period hPeriod field test
        (cutCollarAttachment period hPeriod current)) hPoint'.symm
    _ = cutBulkScalarCurrentCollarCover period hPeriod field test
        (hAt.localInverse point) := rfl

/-- Smoothness on the intrinsic open collar. -/
theorem cutBulkScalarCurrent_openCollar_contMDiff
    (field test : SmoothQuotientField period hPeriod Real) :
    ContMDiff cutCollarModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun parameter : CutThroatOpenCollar period hPeriod ↦
        cutBulkScalarCurrent period hPeriod field test
          (cutOpenCollarAttachment period hPeriod parameter)) := by
  exact (cutBulkScalarCurrent_finiteCollar_contMDiff period hPeriod field test).comp
    ((cutThroatOpenCollar_val_contMDiff period hPeriod).of_le (by simp))

end
end P0EFTJanusMappingTorusCutBulkScalarCurrentOpenCollarSmooth4D
end JanusFormal
