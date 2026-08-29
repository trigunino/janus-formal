import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothSymmetricTensorFunctor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D

/-!
# Finite rotation pullback of smooth throat metric tensors

The genuine spatial rotation flow on the fixed throat is packaged as a smooth
diffeomorphism.  Its covariant pullback preserves smooth symmetric throat
two-tensors.  Only the three canonical rotation axes are treated.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPThroatMetricRotationPullback4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private abbrev ThroatTangentFiber
    (point : EffectiveThroat period hPeriod) :=
  TangentSpace throatCoverModelWithCorners point

private abbrev ThroatCotangentFiber
    (point : EffectiveThroat period hPeriod) :=
  ThroatTangentFiber period hPeriod point →L[Real] Real

private abbrev ThroatCovariantTwoTensorFiber
    (point : EffectiveThroat period hPeriod) :=
  ThroatTangentFiber period hPeriod point →L[Real]
    ThroatCotangentFiber period hPeriod point

private abbrev ThroatCovariantTwoTensorModel :=
  ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates →L[Real] Real

/-- Every fixed-angle throat rotation is smooth. -/
theorem throatSpatialRotationFlow_contMDiff
    (axis : Fin 3) (angle : Real) :
    ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ∞
      (throatSpatialRotationFlow period hPeriod axis angle) := by
  exact
    ((throatJointSpatialRotationFlow_contMDiff period hPeriod axis).comp
      (contMDiff_const.prodMk contMDiff_id)).congr (fun _ => rfl)

/-- A fixed-angle rotation of the genuine throat, with opposite-angle
inverse. -/
def throatSpatialRotationDiffeomorph
    (axis : Fin 3) (angle : Real) :
    EffectiveThroat period hPeriod ≃ₘ^∞⟮
      throatCoverModelWithCorners, throatCoverModelWithCorners⟯
      EffectiveThroat period hPeriod where
  toEquiv :=
    { toFun := throatSpatialRotationFlow period hPeriod axis angle
      invFun := throatSpatialRotationFlow period hPeriod axis (-angle)
      left_inv := by
        intro point
        rw [← throatSpatialRotationFlow_add]
        simp
      right_inv := by
        intro point
        rw [← throatSpatialRotationFlow_add]
        simp }
  contMDiff_toFun :=
    throatSpatialRotationFlow_contMDiff period hPeriod axis angle
  contMDiff_invFun :=
    throatSpatialRotationFlow_contMDiff period hPeriod axis (-angle)

/-- Fiberwise covariant pullback by a genuine finite throat rotation. -/
def throatSpatialRotationTensorPullbackField
    (axis : Fin 3) (angle : Real)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    ∀ point : EffectiveThroat period hPeriod,
      ThroatCovariantTwoTensorFiber period hPeriod point :=
  fun point =>
    let derivative :=
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (throatSpatialRotationFlow period hPeriod axis angle) point
    (derivative.precomp Real).comp
      ((tensor.tensor
        (throatSpatialRotationFlow period hPeriod axis angle point)).comp
          derivative)

@[simp]
theorem throatSpatialRotationTensorPullbackField_apply
    (axis : Fin 3) (angle : Real)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    throatSpatialRotationTensorPullbackField period hPeriod axis angle tensor
        point first second =
      tensor.tensor
        (throatSpatialRotationFlow period hPeriod axis angle point)
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (throatSpatialRotationFlow period hPeriod axis angle) point first)
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (throatSpatialRotationFlow period hPeriod axis angle) point second) :=
  rfl

private def derivativeCoordinates
    (axis : Fin 3) (angle : Real)
    (point current : EffectiveThroat period hPeriod) :
    ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates :=
  inTangentCoordinates throatCoverModelWithCorners
    throatCoverModelWithCorners id
    (throatSpatialRotationFlow period hPeriod axis angle)
    (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
      (throatSpatialRotationFlow period hPeriod axis angle))
    point current

private def tensorCoordinates
    (axis : Fin 3) (angle : Real)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point current : EffectiveThroat period hPeriod) :
    ThroatCovariantTwoTensorModel :=
  ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod)
    (ThroatCoverCoordinates →L[Real] Real)
    (ThroatCotangentFiber period hPeriod)
    (throatSpatialRotationFlow period hPeriod axis angle point)
    (throatSpatialRotationFlow period hPeriod axis angle current)
    (throatSpatialRotationFlow period hPeriod axis angle point)
    (throatSpatialRotationFlow period hPeriod axis angle current)
    (tensor.tensor
      (throatSpatialRotationFlow period hPeriod axis angle current))

private def pullbackTensorCoordinates
    (axis : Fin 3) (angle : Real)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point current : EffectiveThroat period hPeriod) :
    ThroatCovariantTwoTensorModel :=
  ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod)
    (ThroatCoverCoordinates →L[Real] Real)
    (ThroatCotangentFiber period hPeriod)
    point current point current
    (throatSpatialRotationTensorPullbackField
      period hPeriod axis angle tensor current)

private def coordinatePullback
    (derivative :
      ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates)
    (tensor : ThroatCovariantTwoTensorModel) :
    ThroatCovariantTwoTensorModel :=
  (derivative.precomp Real).comp (tensor.comp derivative)

private theorem derivativeCoordinates_apply
    (axis : Fin 3) (angle : Real)
    (point current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) point).baseSet)
    (hImage : throatSpatialRotationFlow period hPeriod axis angle current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (throatSpatialRotationFlow period hPeriod axis angle point)).baseSet)
    (vector : ThroatCoverCoordinates) :
    derivativeCoordinates period hPeriod axis angle point current vector =
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (throatSpatialRotationFlow period hPeriod axis angle point)).linearMapAt Real
          (throatSpatialRotationFlow period hPeriod axis angle current)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (throatSpatialRotationFlow period hPeriod axis angle) current
            ((trivializationAt ThroatCoverCoordinates
              (ThroatTangentFiber period hPeriod) point).symm
                current vector)) := by
  rw [show derivativeCoordinates period hPeriod axis angle point current =
      ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        point current
        (throatSpatialRotationFlow period hPeriod axis angle point)
        (throatSpatialRotationFlow period hPeriod axis angle current)
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (throatSpatialRotationFlow period hPeriod axis angle) current) by
    rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hImage]
  rw [Trivialization.linearMapAt_apply, if_pos hImage]
  rfl

private theorem pullbackTensorCoordinates_eq
    (axis : Fin 3) (angle : Real)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) point).baseSet)
    (hImage : throatSpatialRotationFlow period hPeriod axis angle current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (throatSpatialRotationFlow period hPeriod axis angle point)).baseSet) :
    pullbackTensorCoordinates period hPeriod axis angle tensor point current =
      coordinatePullback
        (derivativeCoordinates period hPeriod axis angle point current)
        (tensorCoordinates period hPeriod axis angle tensor point current) := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  rw [show pullbackTensorCoordinates period hPeriod axis angle tensor
      point current first second =
      ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        point current point current
        (throatSpatialRotationTensorPullbackField
          period hPeriod axis angle tensor current)
        first second by
    rfl]
  rw [inCoordinates_apply_eq₂ hCurrent hCurrent (Set.mem_univ _)]
  simp only [throatSpatialRotationTensorPullbackField_apply,
    coordinatePullback, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  rw [show tensorCoordinates period hPeriod axis angle tensor point current
      (derivativeCoordinates period hPeriod axis angle point current first)
      (derivativeCoordinates period hPeriod axis angle point current second) =
      ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        (throatSpatialRotationFlow period hPeriod axis angle point)
        (throatSpatialRotationFlow period hPeriod axis angle current)
        (throatSpatialRotationFlow period hPeriod axis angle point)
        (throatSpatialRotationFlow period hPeriod axis angle current)
        (tensor.tensor
          (throatSpatialRotationFlow period hPeriod axis angle current))
        (derivativeCoordinates period hPeriod axis angle point current first)
        (derivativeCoordinates period hPeriod axis angle point current second) by
    rfl]
  rw [inCoordinates_apply_eq₂ hImage hImage (Set.mem_univ _)]
  rw [derivativeCoordinates_apply period hPeriod axis angle point current
      hCurrent hImage first,
    derivativeCoordinates_apply period hPeriod axis angle point current
      hCurrent hImage second]
  simp only [Trivialization.symm_linearMapAt _ hImage]
  rfl

/-- The finite rotation pullback field is a smooth throat tensor section. -/
theorem throatSpatialRotationTensorPullbackField_contMDiff
    (axis : Fin 3) (angle : Real)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        𝓘(Real, ThroatCovariantTwoTensorModel)) ∞
      (fun point => TotalSpace.mk' ThroatCovariantTwoTensorModel
        (E := ThroatCovariantTwoTensorFiber period hPeriod) point
        (throatSpatialRotationTensorPullbackField
          period hPeriod axis angle tensor point)) := by
  intro point
  have hRotation :=
    throatSpatialRotationFlow_contMDiff period hPeriod axis angle
  have hD := hRotation.contMDiffAt.mfderiv_const
    (x₀ := point) (m := ∞) (by simp)
  have hMap := hRotation.of_le (m := ∞) (by simp)
  have hTensor := tensor.tensor.contMDiff.comp hMap
  have hTensorAt := hTensor point
  rw [contMDiffAt_hom_bundle] at hTensorAt
  have hPre := hD.clm_precomp (F₃ := Real)
  have hOuter := hTensorAt.2.clm_comp hD
  have hFormula := hPre.clm_comp hOuter
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply hFormula.congr_of_eventuallyEq
  have hCurrent : ∀ᶠ current in 𝓝 point,
      current ∈
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) point).baseSet :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) point).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) point)
  have hImage : ∀ᶠ current in 𝓝 point,
      throatSpatialRotationFlow period hPeriod axis angle current ∈
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod)
          (throatSpatialRotationFlow period hPeriod axis angle point)).baseSet :=
    hRotation.continuous
      |>.continuousAt
      ((trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (throatSpatialRotationFlow period hPeriod axis angle point))
        |>.open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod)
            (throatSpatialRotationFlow period hPeriod axis angle point)))
  filter_upwards [hCurrent, hImage] with current hCurrent' hImage'
  simpa only [pullbackTensorCoordinates, coordinatePullback,
    derivativeCoordinates, tensorCoordinates, Function.comp_apply] using
      (pullbackTensorCoordinates_eq period hPeriod axis angle tensor
        point current hCurrent' hImage')

/-- Genuine pullback of a smooth symmetric throat two-tensor by one of the
three finite rotation flows. -/
def throatSpatialRotationTensorPullback
    (axis : Fin 3) (angle : Real)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    SmoothSymmetricThroatCovariantTwoTensor period hPeriod where
  tensor :=
    { toFun :=
        throatSpatialRotationTensorPullbackField
          period hPeriod axis angle tensor
      contMDiff_toFun :=
        throatSpatialRotationTensorPullbackField_contMDiff
          period hPeriod axis angle tensor }
  symmetric := by
    intro point first second
    change throatSpatialRotationTensorPullbackField
        period hPeriod axis angle tensor point first second =
      throatSpatialRotationTensorPullbackField
        period hPeriod axis angle tensor point second first
    rw [throatSpatialRotationTensorPullbackField_apply,
      throatSpatialRotationTensorPullbackField_apply]
    exact tensor.symmetric _ _ _

@[simp]
theorem throatSpatialRotationTensorPullback_apply
    (axis : Fin 3) (angle : Real)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    (throatSpatialRotationTensorPullback
      period hPeriod axis angle tensor).tensor point first second =
      tensor.tensor
        (throatSpatialRotationFlow period hPeriod axis angle point)
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (throatSpatialRotationFlow period hPeriod axis angle) point first)
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (throatSpatialRotationFlow period hPeriod axis angle) point second) :=
  rfl

/-- The zero-angle finite rotation acts identically on every smooth symmetric
throat tensor. -/
@[simp]
theorem throatSpatialRotationTensorPullback_zero
    (axis : Fin 3)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    throatSpatialRotationTensorPullback period hPeriod axis 0 tensor =
      tensor := by
  apply SmoothSymmetricThroatCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  rw [throatSpatialRotationTensorPullback_apply]
  have hFlow :
      throatSpatialRotationFlow period hPeriod axis 0 =
        id := by
    funext current
    exact throatSpatialRotationFlow_zero period hPeriod axis current
  rw [hFlow]
  simp only [id_eq, mfderiv_id]
  rfl

end

end P0EFTJanusProgramPThroatMetricRotationPullback4D
end JanusFormal
