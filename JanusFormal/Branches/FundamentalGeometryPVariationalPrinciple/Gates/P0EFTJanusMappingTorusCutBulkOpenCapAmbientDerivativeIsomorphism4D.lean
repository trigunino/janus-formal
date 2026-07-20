import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackLorentz4D

/-!
# Derivative isomorphism of the analytic cut-bulk cap map
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkOpenCapAmbientDerivativeIsomorphism4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCutBulkOpenCapSmoothMappingTorus4D
open P0EFTJanusMappingTorusCutBulkOpenCapIdentification4D
open P0EFTJanusMappingTorusCutBulkToAmbientOpenCapSmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev OpenCapCover :=
  MappingTorusCover (cutBulkOpenCapData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance ambientCoverChartedSpace : ChartedSpace CoverModel
    (MappingTorusCover (reflectedSphereData period hPeriod)) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance openCapCoverChartedSpace :
    ChartedSpace CoverModel (OpenCapCover period hPeriod) :=
  cutBulkOpenCapCoverChartedSpace period hPeriod

local instance smoothOpenCapChartedSpace :
    ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
  cutBulkOpenCapQuotientChartedSpace period hPeriod

private def openSubtypePartialDiffeomorph
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners Real E H) (U : TopologicalSpace.Opens M) (base : U) :
    PartialDiffeomorph I I U M ∞ := by
  letI : Nonempty U := ⟨base⟩
  exact
    { __ := U.2.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := by
        rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
        intro point hPoint
        rw [← ContMDiffWithinAt.subtypeVal_comp_iff U]
        apply contMDiffWithinAt_id.congr_of_mem _ hPoint
        intro target hTarget
        exact U.2.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_right_inv
          Subtype.val hTarget }

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
    {n : ℕ∞}
    (Φ : PartialDiffeomorph I I' M M' n)
    (Ψ : PartialDiffeomorph J J' N N' n) :
    PartialDiffeomorph (I.prod J) (I'.prod J') (M × N) (M' × N') n where
  __ := Φ.toOpenPartialHomeomorph.prod Ψ.toOpenPartialHomeomorph
  contMDiffOn_toFun := Φ.contMDiffOn.prodMap Ψ.contMDiffOn
  contMDiffOn_invFun := Φ.symm.contMDiffOn.prodMap Ψ.symm.contMDiffOn

private def openCapCoverProductDiffeomorph :
    OpenCapCover period hPeriod ≃ₘ^∞⟮coverModelWithCorners,
      coverModelWithCorners⟯ positiveHemisphereInteriorOpen × Real where
  toEquiv := (coverHomeomorphProd (cutBulkOpenCapData period hPeriod)).toEquiv
  contMDiff_toFun := chartedSpacePullback_toFun_contMDiff
    coverModelWithCorners ∞ (coverHomeomorphProd
      (cutBulkOpenCapData period hPeriod))
  contMDiff_invFun := chartedSpacePullback_invFun_contMDiff
    coverModelWithCorners ∞ (coverHomeomorphProd
      (cutBulkOpenCapData period hPeriod))

private def ambientCoverProductDiffeomorph :
    MappingTorusCover (reflectedSphereData period hPeriod) ≃ₘ^∞⟮
      coverModelWithCorners, coverModelWithCorners⟯ UnitThreeSphere × Real where
  toEquiv := (coverHomeomorphProd (reflectedSphereData period hPeriod)).toEquiv
  contMDiff_toFun := chartedSpacePullback_toFun_contMDiff
    coverModelWithCorners ∞ (coverHomeomorphProd
      (reflectedSphereData period hPeriod))
  contMDiff_invFun := chartedSpacePullback_invFun_contMDiff
    coverModelWithCorners ∞ (coverHomeomorphProd
      (reflectedSphereData period hPeriod))

private theorem productOpenCapInclusion_isLocalDiffeomorph :
    IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ∞
      (Prod.map (Subtype.val : positiveHemisphereInteriorOpen → UnitThreeSphere)
        (id : Real → Real)) := by
  intro point
  let fiberMap := openSubtypePartialDiffeomorph (𝓡 3)
    positiveHemisphereInteriorOpen point.1
  let timeMap := (Diffeomorph.refl 𝓘(Real, Real) Real ∞).toPartialDiffeomorph
  refine ⟨partialDiffeomorphProd fiberMap timeMap, ⟨Set.mem_univ _, Set.mem_univ _⟩, ?_⟩
  rintro ⟨fiber, time⟩ -
  rfl

private def openCapCoverToAmbientCover
    (point : OpenCapCover period hPeriod) :
    MappingTorusCover (reflectedSphereData period hPeriod) :=
  (ambientCoverProductDiffeomorph period hPeriod).symm
    (Prod.map (Subtype.val : positiveHemisphereInteriorOpen → UnitThreeSphere)
      (id : Real → Real) (openCapCoverProductDiffeomorph period hPeriod point))

private theorem openCapCoverToAmbientCover_isLocalDiffeomorph :
    IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ∞
      (openCapCoverToAmbientCover period hPeriod) := by
  intro point
  have hFirst := (openCapCoverProductDiffeomorph period hPeriod).isLocalDiffeomorph point
  have hSecond := productOpenCapInclusion_isLocalDiffeomorph
    (openCapCoverProductDiffeomorph period hPeriod point)
  have hThird := (ambientCoverProductDiffeomorph period hPeriod).symm.isLocalDiffeomorph
    (Prod.map (Subtype.val : positiveHemisphereInteriorOpen → UnitThreeSphere)
      (id : Real → Real) (openCapCoverProductDiffeomorph period hPeriod point))
  exact (hFirst.comp coverModelWithCorners _ hSecond).comp
    coverModelWithCorners _ hThird

private def analyticPartialDiffeomorphToSmooth
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace CoverModel M] [ChartedSpace CoverModel N]
    (Φ : PartialDiffeomorph coverModelWithCorners coverModelWithCorners M N ω) :
    PartialDiffeomorph coverModelWithCorners coverModelWithCorners M N ∞ where
  __ := Φ.toOpenPartialHomeomorph
  contMDiffOn_toFun := Φ.contMDiffOn.of_le (by simp)
  contMDiffOn_invFun := Φ.symm.contMDiffOn.of_le (by simp)

private theorem localDiffeomorphSmooth_of_analytic
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace CoverModel M] [ChartedSpace CoverModel N]
    {function : M → N}
    (hFunction : IsLocalDiffeomorph coverModelWithCorners
      coverModelWithCorners ω function) :
    IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ∞ function := by
  intro point
  rcases hFunction point with ⟨Φ, hPoint, hEq⟩
  exact ⟨analyticPartialDiffeomorphToSmooth Φ, hPoint, hEq⟩

private def localCutBulkOpenCapToAmbientCover
    (point : OpenCapCover period hPeriod) : EffectiveQuotient period hPeriod :=
  smoothCutBulkOpenCapToAmbient period hPeriod
    (mappingTorusMk (cutBulkOpenCapData period hPeriod) point)

private theorem localCutBulkOpenCapToAmbientCover_isLocalDiffeomorph :
    IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ∞
      (localCutBulkOpenCapToAmbientCover period hPeriod) := by
  intro point
  have hCover := openCapCoverToAmbientCover_isLocalDiffeomorph
    period hPeriod point
  have hProjection := localDiffeomorphSmooth_of_analytic
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
      (openCapCoverToAmbientCover period hPeriod point)
  have hComposite := hCover.comp coverModelWithCorners _ hProjection
  exact hComposite

/-- The analytic cap map has an invertible manifold derivative everywhere. -/
theorem smoothCutBulkOpenCapToAmbient_derivative_isomorphism
    (cap : SmoothCutBulkOpenCap period hPeriod) :
    ∃ derivative : TangentSpace coverModelWithCorners cap ≃L[Real]
        TangentSpace coverModelWithCorners
          (smoothCutBulkOpenCapToAmbient period hPeriod cap),
      (derivative : TangentSpace coverModelWithCorners cap →L[Real]
        TangentSpace coverModelWithCorners
          (smoothCutBulkOpenCapToAmbient period hPeriod cap)) =
        mfderiv coverModelWithCorners coverModelWithCorners
          (smoothCutBulkOpenCapToAmbient period hPeriod) cap := by
  obtain ⟨point, rfl⟩ :=
    mappingTorusMk_surjective (cutBulkOpenCapData period hPeriod) cap
  let sourceDerivative :=
    (cutBulkOpenCap_projection_isLocalDiffeomorph period hPeriod)
      |>.mfderivToContinuousLinearEquiv (by simp) point
  let coverDerivative :=
    (localCutBulkOpenCapToAmbientCover_isLocalDiffeomorph period hPeriod)
      |>.mfderivToContinuousLinearEquiv (by simp) point
  refine ⟨sourceDerivative.symm.trans coverDerivative, ?_⟩
  have hSource := (cutBulkOpenCap_projection_isLocalDiffeomorph period hPeriod)
    |>.contMDiff.mdifferentiable (by simp) point
  have hMap := (smoothCutBulkOpenCapToAmbient_contMDiff period hPeriod)
    |>.mdifferentiable (by simp)
      (mappingTorusMk (cutBulkOpenCapData period hPeriod) point)
  have hComp := mfderiv_comp point hMap hSource
  rw [show smoothCutBulkOpenCapToAmbient period hPeriod ∘
      mappingTorusMk (cutBulkOpenCapData period hPeriod) =
      localCutBulkOpenCapToAmbientCover period hPeriod by
        funext current
        rfl] at hComp
  apply ContinuousLinearMap.ext
  intro vector
  change coverDerivative (sourceDerivative.symm vector) = _
  have hApply := DFunLike.congr_fun hComp (sourceDerivative.symm vector)
  change mfderiv coverModelWithCorners coverModelWithCorners
      (localCutBulkOpenCapToAmbientCover period hPeriod) point
        (sourceDerivative.symm vector) =
    mfderiv coverModelWithCorners coverModelWithCorners
      (smoothCutBulkOpenCapToAmbient period hPeriod)
        (mappingTorusMk (cutBulkOpenCapData period hPeriod) point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (cutBulkOpenCapData period hPeriod)) point
          (sourceDerivative.symm vector)) at hApply
  rw [← DFunLike.congr_fun
      (IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
        (localCutBulkOpenCapToAmbientCover_isLocalDiffeomorph period hPeriod)
          (by simp) point) (sourceDerivative.symm vector),
    ← DFunLike.congr_fun
      (IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
        (cutBulkOpenCap_projection_isLocalDiffeomorph period hPeriod)
          (by simp) point) (sourceDerivative.symm vector)] at hApply
  change coverDerivative (sourceDerivative.symm vector) =
    mfderiv coverModelWithCorners coverModelWithCorners
      (smoothCutBulkOpenCapToAmbient period hPeriod)
        (mappingTorusMk (cutBulkOpenCapData period hPeriod) point)
        (sourceDerivative (sourceDerivative.symm vector)) at hApply
  simpa using hApply

end
end P0EFTJanusMappingTorusCutBulkOpenCapAmbientDerivativeIsomorphism4D
end JanusFormal
