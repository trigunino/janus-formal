import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D

/-!
# Differential certificate on the intrinsic open collar
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkOpenCollarAmbientDerivativeIsomorphism4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkToAmbientOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance boundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance finiteCollarChartedSpace :
    ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
  cutThroatFiniteCollarChartedSpace period hPeriod

local instance openCollarChartedSpace :
    ChartedSpace CutCollarModel
      {parameter : CutThroatFiniteCollar period hPeriod // parameter.2.1 < 1} :=
  cutThroatOpenCollarChartedSpace period hPeriod

local instance openCollarAliasChartedSpace :
    ChartedSpace CutCollarModel (CutThroatOpenCollar period hPeriod) :=
  cutThroatOpenCollarChartedSpace period hPeriod

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

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

/-- The open collar is an open submanifold of the finite collar. -/
theorem cutThroatOpenCollar_val_isLocalDiffeomorph :
    IsLocalDiffeomorph cutCollarModelWithCorners cutCollarModelWithCorners ∞
      (Subtype.val : CutThroatOpenCollar period hPeriod →
        CutThroatFiniteCollar period hPeriod) := by
  intro point
  let localMap := openSubtypePartialDiffeomorph cutCollarModelWithCorners
    (cutThroatOpenCollarOpen period hPeriod) point
  exact localMap.isLocalDiffeomorphAt _ _ _ (by
    change point ∈ Set.univ
    simp)

/-- Natural ambient map restricted to the intrinsic open collar. -/
def cutBulkOpenCollarToAmbient
    (parameter : CutThroatOpenCollar period hPeriod) :
    EffectiveQuotient period hPeriod :=
  cutBulkToAmbient period hPeriod
    (cutOpenCollarAttachment period hPeriod parameter)

theorem cutBulkOpenCollarToAmbient_contMDiff :
    ContMDiff cutCollarModelWithCorners coverModelWithCorners ∞
      (cutBulkOpenCollarToAmbient period hPeriod) :=
  cutBulkToAmbient_openCollar_contMDiff period hPeriod

set_option backward.isDefEq.respectTransparency false in
theorem cutBulkOpenCollarToAmbient_derivative_isomorphism
    (parameter : CutThroatOpenCollar period hPeriod) :
    ∃ derivative : TangentSpace cutCollarModelWithCorners parameter ≃L[Real]
        TangentSpace coverModelWithCorners
          (cutBulkOpenCollarToAmbient period hPeriod parameter),
      (derivative : TangentSpace cutCollarModelWithCorners parameter →L[Real]
        TangentSpace coverModelWithCorners
          (cutBulkOpenCollarToAmbient period hPeriod parameter)) =
        mfderiv cutCollarModelWithCorners coverModelWithCorners
          (cutBulkOpenCollarToAmbient period hPeriod) parameter := by
  let hInclusion := cutThroatOpenCollar_val_isLocalDiffeomorph
    period hPeriod parameter
  let inclusionDerivative :=
    hInclusion.mfderivToContinuousLinearEquiv (by simp)
  let finiteDerivative :=
    (cutBulkFiniteCollarToAmbient_derivative_isomorphism period hPeriod
      parameter.1).choose
  have hFiniteDerivative :=
    (cutBulkFiniteCollarToAmbient_derivative_isomorphism period hPeriod
      parameter.1).choose_spec
  let derivative := inclusionDerivative.trans finiteDerivative
  refine ⟨derivative, ?_⟩
  have hInclusionDiff := hInclusion.mdifferentiableAt (by simp)
  have hFiniteDiff := (cutBulkFiniteCollarToAmbient_contMDiff period hPeriod)
    |>.mdifferentiableAt (x := parameter.1) (by simp)
  have hComp := mfderiv_comp parameter hFiniteDiff hInclusionDiff
  rw [show cutBulkFiniteCollarToAmbient period hPeriod ∘
      (Subtype.val : CutThroatOpenCollar period hPeriod →
        CutThroatFiniteCollar period hPeriod) =
      cutBulkOpenCollarToAmbient period hPeriod by rfl] at hComp
  ext vector
  change finiteDerivative (inclusionDerivative vector) = _
  rw [show inclusionDerivative vector =
      mfderiv cutCollarModelWithCorners cutCollarModelWithCorners
        (Subtype.val : CutThroatOpenCollar period hPeriod →
          CutThroatFiniteCollar period hPeriod) parameter vector by
    exact DFunLike.congr_fun
      (hInclusion.mfderivToContinuousLinearEquiv_coe (by simp)) vector,
    show finiteDerivative
        (mfderiv cutCollarModelWithCorners cutCollarModelWithCorners
          (Subtype.val : CutThroatOpenCollar period hPeriod →
            CutThroatFiniteCollar period hPeriod) parameter vector) =
      mfderiv cutCollarModelWithCorners coverModelWithCorners
        (cutBulkFiniteCollarToAmbient period hPeriod) parameter.1
        (mfderiv cutCollarModelWithCorners cutCollarModelWithCorners
          (Subtype.val : CutThroatOpenCollar period hPeriod →
            CutThroatFiniteCollar period hPeriod) parameter vector) by
    exact DFunLike.congr_fun hFiniteDerivative _]
  exact DFunLike.congr_fun hComp.symm vector

end
end P0EFTJanusMappingTorusCutBulkOpenCollarAmbientDerivativeIsomorphism4D
end JanusFormal
