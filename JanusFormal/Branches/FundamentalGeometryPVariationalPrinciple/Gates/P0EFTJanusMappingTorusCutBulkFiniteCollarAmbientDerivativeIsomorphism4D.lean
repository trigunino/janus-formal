import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutCollarCoverToAmbientDerivativeIsomorphism4D

/-!
# Differential certificate on the finite collar quotient
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkToAmbientOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutCollarCoverToAmbientDerivativeIsomorphism4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryCover :=
  MappingTorusCover (orientationDoubleData period hPeriod)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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
  fixedThroatQuotient_isManifold
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance finiteCollarChartedSpace :
    ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
  cutThroatFiniteCollarChartedSpace period hPeriod

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

/-- Projection from the collar cover to the finite collar quotient. -/
def cutCollarCoverProjection :
    BoundaryCover period hPeriod × CutCollarInterval →
      CutThroatFiniteCollar period hPeriod :=
  Prod.map (mappingTorusMk (orientationDoubleData period hPeriod))
    (id : CutCollarInterval → CutCollarInterval)

theorem cutCollarCoverProjection_isLocalDiffeomorph :
    IsLocalDiffeomorph cutCollarModelWithCorners cutCollarModelWithCorners ω
      (Prod.map (mappingTorusMk (orientationDoubleData period hPeriod))
        (id : CutCollarInterval → CutCollarInterval)) := by
  intro parameter
  have hFirst : IsLocalDiffeomorphAt throatCoverModelWithCorners
      throatCoverModelWithCorners ω
      (mappingTorusMk (orientationDoubleData period hPeriod)) parameter.1 := by
    exact (fixedThroat_projection_isLocalDiffeomorph
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)) parameter.1
  obtain ⟨Φ, hΦ, hEq⟩ := hFirst
  obtain ⟨Ψ, hΨ, hEq'⟩ :=
    (Diffeomorph.refl (modelWithCornersEuclideanHalfSpace 1)
      CutCollarInterval ω).isLocalDiffeomorph parameter.2
  let productMap : PartialDiffeomorph cutCollarModelWithCorners
      cutCollarModelWithCorners
      (BoundaryCover period hPeriod × CutCollarInterval)
      (CutThroatFiniteCollar period hPeriod) ω :=
    { __ := Φ.toOpenPartialHomeomorph.prod Ψ.toOpenPartialHomeomorph
      contMDiffOn_toFun := Φ.contMDiffOn.prodMap Ψ.contMDiffOn
      contMDiffOn_invFun := Φ.symm.contMDiffOn.prodMap Ψ.symm.contMDiffOn }
  refine ⟨productMap, ?_, ?_⟩
  · exact ⟨hΦ, hΨ⟩
  rintro ⟨anchor, normal⟩ ⟨hAnchor, hNormal⟩
  exact Prod.ext (hEq hAnchor) (hEq' hNormal)

/-- Natural ambient map on the finite collar quotient. -/
def cutBulkFiniteCollarToAmbient
    (parameter : CutThroatFiniteCollar period hPeriod) :
    EffectiveQuotient period hPeriod :=
  cutBulkToAmbient period hPeriod
    (cutCollarAttachment period hPeriod parameter)

theorem cutBulkFiniteCollarToAmbient_contMDiff :
    ContMDiff cutCollarModelWithCorners coverModelWithCorners ∞
      (cutBulkFiniteCollarToAmbient period hPeriod) :=
  cutBulkToAmbient_finiteCollar_contMDiff period hPeriod

set_option backward.isDefEq.respectTransparency false in
theorem cutBulkFiniteCollarToAmbient_derivative_isomorphism
    (parameter : CutThroatFiniteCollar period hPeriod) :
    ∃ derivative : TangentSpace cutCollarModelWithCorners parameter ≃L[Real]
        TangentSpace coverModelWithCorners
          (cutBulkFiniteCollarToAmbient period hPeriod parameter),
      (derivative : TangentSpace cutCollarModelWithCorners parameter →L[Real]
        TangentSpace coverModelWithCorners
          (cutBulkFiniteCollarToAmbient period hPeriod parameter)) =
        mfderiv cutCollarModelWithCorners coverModelWithCorners
          (cutBulkFiniteCollarToAmbient period hPeriod) parameter := by
  rcases parameter with ⟨boundary, normal⟩
  obtain ⟨anchor, rfl⟩ := mappingTorusMk_surjective
    (orientationDoubleData period hPeriod) boundary
  let coverPoint : BoundaryCover period hPeriod × CutCollarInterval :=
    (anchor, normal)
  let hProjection : IsLocalDiffeomorphAt cutCollarModelWithCorners
      cutCollarModelWithCorners ω (cutCollarCoverProjection period hPeriod)
      coverPoint := by
    simpa [cutCollarCoverProjection] using
      cutCollarCoverProjection_isLocalDiffeomorph period hPeriod coverPoint
  let projectionDerivative :=
    hProjection.mfderivToContinuousLinearEquiv (by simp)
  let coverDerivative :=
    (cutCollarCoverToAmbient_derivative_isomorphism period hPeriod coverPoint).choose
  have hCoverDerivative :=
    (cutCollarCoverToAmbient_derivative_isomorphism period hPeriod coverPoint).choose_spec
  let derivative := projectionDerivative.symm.trans coverDerivative
  refine ⟨derivative, ?_⟩
  have hProjectionDiff := hProjection.mdifferentiableAt (by simp)
  have hFiniteDiff := (cutBulkFiniteCollarToAmbient_contMDiff period hPeriod)
    |>.mdifferentiableAt (x := cutCollarCoverProjection period hPeriod coverPoint)
      (by simp)
  have hComp := mfderiv_comp coverPoint hFiniteDiff hProjectionDiff
  rw [show cutBulkFiniteCollarToAmbient period hPeriod ∘
      cutCollarCoverProjection period hPeriod =
      cutCollarCoverToAmbient period hPeriod by
    funext current
    exact (cutCollarCoverToAmbient_eq_existing period hPeriod current).symm] at hComp
  ext vector
  change coverDerivative (projectionDerivative.symm vector) = _
  rw [show coverDerivative (projectionDerivative.symm vector) =
      mfderiv cutCollarModelWithCorners coverModelWithCorners
        (cutCollarCoverToAmbient period hPeriod) coverPoint
        (projectionDerivative.symm vector) by
    exact DFunLike.congr_fun hCoverDerivative _]
  have hAt := DFunLike.congr_fun hComp (projectionDerivative.symm vector)
  have hProjectionApply :
      mfderiv cutCollarModelWithCorners cutCollarModelWithCorners
        (cutCollarCoverProjection period hPeriod) coverPoint
        (projectionDerivative.symm vector) = vector := by
    rw [← hProjection.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact projectionDerivative.apply_symm_apply vector
  change mfderiv cutCollarModelWithCorners coverModelWithCorners
      (cutCollarCoverToAmbient period hPeriod) coverPoint
        (projectionDerivative.symm vector) =
    mfderiv cutCollarModelWithCorners coverModelWithCorners
      (cutBulkFiniteCollarToAmbient period hPeriod)
      (cutCollarCoverProjection period hPeriod coverPoint)
      (mfderiv cutCollarModelWithCorners cutCollarModelWithCorners
        (cutCollarCoverProjection period hPeriod) coverPoint
        (projectionDerivative.symm vector)) at hAt
  rw [hProjectionApply] at hAt
  simpa [coverPoint, cutCollarCoverProjection] using hAt

end
end P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D
end JanusFormal
