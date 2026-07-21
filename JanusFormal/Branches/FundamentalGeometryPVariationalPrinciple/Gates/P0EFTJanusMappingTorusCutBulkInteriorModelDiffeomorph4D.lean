import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarPositiveOpenDiffeomorph4D

/-!
# Euclidean model as the interior of the cut-collar model

This supplies the common model-space change needed to glue the analytic cap
charts to the manifold-with-boundary collar charts.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkInteriorModelDiffeomorph4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D

/-- An arbitrary fixed linear identification of the two four-dimensional
ambient coordinate spaces. -/
def coverToCutCollarCoordinates :
    CoverCoordinates ≃L[Real] CutCollarCoordinates :=
  ContinuousLinearEquiv.ofFinrankEq (by
    norm_num [CoverCoordinates, CutCollarCoordinates, ThroatCoverCoordinates])

/-- Strict interior of the half-space model used by the cut collar. -/
def cutCollarModelInteriorOpen : TopologicalSpace.Opens CutCollarModel :=
  ⟨{point | 0 < point.2.1 0}, by
    have hNormal : Continuous
        (fun point : CutCollarModel => point.2.1) :=
      continuous_subtype_val.comp continuous_snd
    exact isOpen_lt continuous_const
      ((PiLp.continuous_apply 2 _ 0).comp hNormal)⟩

private def positiveSingleton (value : Real) : EuclideanHalfSpace 1 :=
  ⟨WithLp.toLp 2 (fun _ => Real.exp value), (Real.exp_pos value).le⟩

private def logarithmicSingleton
    (normal : EuclideanHalfSpace 1) : EuclideanSpace Real (Fin 1) :=
  WithLp.toLp 2 (fun _ => Real.log (normal.1 0))

private def singletonLinearMap :
    Real →ₗ[Real] EuclideanSpace Real (Fin 1) where
  toFun value := WithLp.toLp 2 (fun _ => value)
  map_add' first second := by ext; simp
  map_smul' scalar value := by ext; simp

private def singletonContinuousLinearMap :
    Real →L[Real] EuclideanSpace Real (Fin 1) :=
  LinearMap.toContinuousLinearMap singletonLinearMap

private def evaluationZeroLinearMap :
    EuclideanSpace Real (Fin 1) →ₗ[Real] Real where
  toFun value := value 0
  map_add' first second := by simp
  map_smul' scalar value := by simp

private def evaluationZeroContinuousLinearMap :
    EuclideanSpace Real (Fin 1) →L[Real] Real :=
  LinearMap.toContinuousLinearMap evaluationZeroLinearMap

private def interiorizeCutCollarCoordinates
    (coordinates : CutCollarCoordinates) : CutCollarCoordinates :=
  (coordinates.1,
    singletonContinuousLinearMap (Real.exp (coordinates.2 0)))

private theorem interiorizeCutCollarCoordinates_contDiff :
    ContDiff Real ∞ interiorizeCutCollarCoordinates := by
  unfold interiorizeCutCollarCoordinates
  fun_prop

private theorem logarithmicSingleton_positiveSingleton (value : Real) :
    logarithmicSingleton (positiveSingleton value) =
      WithLp.toLp 2 (fun _ : Fin 1 => value) := by
  ext index
  fin_cases index
  simp [logarithmicSingleton, positiveSingleton]

private theorem positiveSingleton_logarithmicSingleton
    (normal : EuclideanHalfSpace 1) (hNormal : 0 < normal.1 0) :
    positiveSingleton ((logarithmicSingleton normal) 0) = normal := by
  apply EuclideanHalfSpace.ext
  ext index
  fin_cases index
  exact Real.exp_log hNormal

/-- Euclidean model mapped into the strict interior of the collar model. -/
def coverModelToCutCollarInterior (point : CoverModel) :
    cutCollarModelInteriorOpen :=
  let coordinates := coverToCutCollarCoordinates (coverModelWithCorners point)
  ⟨(coordinates.1, positiveSingleton (coordinates.2 0)),
    Real.exp_pos (coordinates.2 0)⟩

/-- Inverse logarithmic change of model. -/
def cutCollarInteriorToCoverModel (point : cutCollarModelInteriorOpen) :
    CoverModel :=
  coverModelWithCorners.symm
    (coverToCutCollarCoordinates.symm
      (point.1.1, logarithmicSingleton point.1.2))

theorem coverModelToCutCollarInterior_leftInverse :
    Function.LeftInverse cutCollarInteriorToCoverModel
      coverModelToCutCollarInterior := by
  intro point
  simp only [coverModelToCutCollarInterior, cutCollarInteriorToCoverModel]
  rw [logarithmicSingleton_positiveSingleton]
  have hCoordinates :
      ((coverToCutCollarCoordinates (coverModelWithCorners point)).1,
        WithLp.toLp 2 (fun _ : Fin 1 =>
          (coverToCutCollarCoordinates (coverModelWithCorners point)).2 0)) =
        coverToCutCollarCoordinates (coverModelWithCorners point) := by
    apply Prod.ext
    · rfl
    · ext index
      fin_cases index
      rfl
  rw [hCoordinates]
  simp

theorem coverModelToCutCollarInterior_rightInverse :
    Function.RightInverse cutCollarInteriorToCoverModel
      coverModelToCutCollarInterior := by
  intro point
  apply Subtype.ext
  simp only [coverModelToCutCollarInterior, cutCollarInteriorToCoverModel]
  rw [show (coverModelWithCorners
      (coverModelWithCorners.symm
        (coverToCutCollarCoordinates.symm
          (point.1.1, logarithmicSingleton point.1.2)))) =
      coverToCutCollarCoordinates.symm
        (point.1.1, logarithmicSingleton point.1.2) by simp]
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply ModelProd.ext
  · rfl
  · exact positiveSingleton_logarithmicSingleton point.1.2 point.2

theorem coverModelToCutCollarInterior_contMDiff :
    ContMDiff coverModelWithCorners cutCollarModelWithCorners ∞
      coverModelToCutCollarInterior := by
  rw [← ContMDiff.subtypeVal_comp_iff cutCollarModelInteriorOpen]
  have hCoordinates : ContMDiff coverModelWithCorners
      (modelWithCornersSelf Real CutCollarCoordinates) ∞
      (interiorizeCutCollarCoordinates ∘
        coverToCutCollarCoordinates ∘ coverModelWithCorners) :=
    interiorizeCutCollarCoordinates_contDiff.contMDiff.comp
      (coverToCutCollarCoordinates.contDiff.contMDiff.comp
        (contMDiff_model (I := coverModelWithCorners)))
  have hRange (point : CoverModel) :
      (interiorizeCutCollarCoordinates ∘
          coverToCutCollarCoordinates ∘ coverModelWithCorners) point ∈
        Set.range cutCollarModelWithCorners := by
    let coordinates := coverToCutCollarCoordinates (coverModelWithCorners point)
    refine ⟨(coordinates.1, positiveSingleton (coordinates.2 0)), ?_⟩
    apply Prod.ext
    · rfl
    · ext index
      fin_cases index
      rfl
  have hSmooth := (contMDiffOn_model_symm
      (I := cutCollarModelWithCorners) (n := ∞)).comp_contMDiff
        hCoordinates hRange
  exact hSmooth.congr fun point => by
    apply cutCollarModelWithCorners.injective
    change cutCollarModelWithCorners
        (coverModelToCutCollarInterior point).1 =
      cutCollarModelWithCorners
        (cutCollarModelWithCorners.symm
          ((interiorizeCutCollarCoordinates ∘
            coverToCutCollarCoordinates ∘ coverModelWithCorners) point))
    rw [cutCollarModelWithCorners.right_inv (hRange point)]
    apply Prod.ext
    · rfl
    · ext index
      fin_cases index
      simp [coverModelToCutCollarInterior, interiorizeCutCollarCoordinates,
        singletonContinuousLinearMap, singletonLinearMap,
        positiveSingleton, modelWithCornersEuclideanHalfSpace]

theorem cutCollarInteriorToCoverModel_contMDiff :
    ContMDiff cutCollarModelWithCorners coverModelWithCorners ∞
      cutCollarInteriorToCoverModel := by
  have hVal : ContMDiff cutCollarModelWithCorners cutCollarModelWithCorners ∞
      (fun point : cutCollarModelInteriorOpen => point.1) :=
    contMDiff_subtype_val
  have hAmbient : ContMDiff cutCollarModelWithCorners
      (modelWithCornersSelf Real CutCollarCoordinates) ∞
      (fun point : cutCollarModelInteriorOpen =>
        cutCollarModelWithCorners point.1) :=
    (contMDiff_model (I := cutCollarModelWithCorners)).comp hVal
  have hFirst : ContMDiff cutCollarModelWithCorners
      (modelWithCornersSelf Real ThroatCoverCoordinates) ∞
      (fun point : cutCollarModelInteriorOpen =>
        throatCoverModelWithCorners point.1.1) :=
    ((ContinuousLinearMap.fst Real ThroatCoverCoordinates
      (EuclideanSpace Real (Fin 1))).contDiff.contMDiff.comp hAmbient).congr
        fun _ => rfl
  have hNormalVector : ContMDiff cutCollarModelWithCorners
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 1))) ∞
      (fun point : cutCollarModelInteriorOpen => point.1.2.1) :=
    ((ContinuousLinearMap.snd Real ThroatCoverCoordinates
      (EuclideanSpace Real (Fin 1))).contDiff.contMDiff.comp hAmbient).congr
        fun _ => rfl
  have hNormal : ContMDiff cutCollarModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun point : cutCollarModelInteriorOpen => point.1.2.1 0) :=
    (evaluationZeroContinuousLinearMap.contDiff.contMDiff.comp
      hNormalVector).congr fun _ => rfl
  have hLog : ContMDiff cutCollarModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun point : cutCollarModelInteriorOpen =>
        Real.log (point.1.2.1 0)) := by
    intro point
    exact (Real.contDiffAt_log.2 point.2.ne').contMDiffAt.comp point
      (hNormal point)
  have hSingleton : ContMDiff cutCollarModelWithCorners
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 1))) ∞
      (fun point : cutCollarModelInteriorOpen =>
        logarithmicSingleton point.1.2) :=
    (singletonContinuousLinearMap.contDiff.contMDiff.comp hLog).congr
      fun point => by
        ext index
        fin_cases index
        rfl
  have hPair : ContMDiff cutCollarModelWithCorners
      (modelWithCornersSelf Real CutCollarCoordinates) ∞
      (fun point : cutCollarModelInteriorOpen =>
        (throatCoverModelWithCorners point.1.1,
          logarithmicSingleton point.1.2)) :=
    hFirst.prodMk_space hSingleton
  have hCoordinates : ContMDiff cutCollarModelWithCorners
      (modelWithCornersSelf Real CoverCoordinates) ∞
      (fun point : cutCollarModelInteriorOpen =>
        coverToCutCollarCoordinates.symm
          (throatCoverModelWithCorners point.1.1,
            logarithmicSingleton point.1.2)) :=
    coverToCutCollarCoordinates.symm.contDiff.contMDiff.comp hPair
  have hRange (point : cutCollarModelInteriorOpen) :
      coverToCutCollarCoordinates.symm
          (throatCoverModelWithCorners point.1.1,
            logarithmicSingleton point.1.2) ∈
        Set.range coverModelWithCorners := by
    simp [coverModelWithCorners]
  have hSmooth := (contMDiffOn_model_symm
      (I := coverModelWithCorners) (n := ∞)).comp_contMDiff
        hCoordinates hRange
  exact hSmooth.congr fun _ => rfl

/-- Analytic identification of the Euclidean cap model with the strict
interior of the cut-collar half-space model. -/
def coverModelCutCollarInteriorDiffeomorph :
    CoverModel ≃ₘ^∞⟮coverModelWithCorners, cutCollarModelWithCorners⟯
      cutCollarModelInteriorOpen where
  toFun := coverModelToCutCollarInterior
  invFun := cutCollarInteriorToCoverModel
  left_inv := coverModelToCutCollarInterior_leftInverse
  right_inv := coverModelToCutCollarInterior_rightInverse
  contMDiff_toFun := coverModelToCutCollarInterior_contMDiff
  contMDiff_invFun := cutCollarInteriorToCoverModel_contMDiff

end
end P0EFTJanusMappingTorusCutBulkInteriorModelDiffeomorph4D
end JanusFormal
