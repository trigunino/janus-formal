import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzMetricSpatialRotationIsometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD8RotationGhostThroatRestriction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricRotationPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicMetricBVThroatIntegrated4D

/-!
# Spatial-rotation naturality of the intrinsic throat metric pairing

The cover Lorentz isometry descends through the throat projection and
inclusion.  Hence the genuine intrinsic throat metric is invariant under each
finite spatial rotation.  This gate stops before any infinitesimal
derivative/action identification.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPThroatMetricRotationPairingNaturality4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusD8NonabelianGhostTriple4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricSpatialRotationIsometry4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatIntegrated4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusProgramPD8RotationGhostThroatRestriction4D
open P0EFTJanusProgramPThroatMetricRotationPullback4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev SphereData := reflectedSphereData period hPeriod
private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev EffectiveCover :=
  MappingTorusCover (SphereData period hPeriod)
private abbrev EffectiveQuotient :=
  MappingTorus (SphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (ThroatData period hPeriod)
private abbrev EffectiveThroat :=
  MappingTorus (ThroatData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance throatTangentFiniteDimensional
    (point : EffectiveThroat period hPeriod) :
    FiniteDimensional Real
      (TangentSpace throatCoverModelWithCorners point) := by
  change FiniteDimensional Real ThroatCoverCoordinates
  infer_instance

/-- The throat projection differential intertwines cover and quotient finite
spatial rotations. -/
theorem throatProjectionDerivative_spatialRotation_natural
    (axis : Fin 3) (angle : Real)
    (point : EffectiveThroatCover period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners point) :
    mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (throatSpatialRotationFlow period hPeriod axis angle)
        (mappingTorusMk (ThroatData period hPeriod) point)
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (mappingTorusMk (ThroatData period hPeriod)) point vector) =
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (mappingTorusMk (ThroatData period hPeriod))
        (throatCoverSpatialRotationFlow period hPeriod axis (angle, point))
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (fun current =>
            throatCoverSpatialRotationFlow period hPeriod axis
              (angle, current)) point vector) := by
  have hProjection :=
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod).contMDiff
  have hCoverRotation :
      ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ∞
        (fun current : EffectiveThroatCover period hPeriod =>
          throatCoverSpatialRotationFlow period hPeriod axis
            (angle, current)) :=
    (throatCoverSpatialRotationFlow_contMDiff period hPeriod axis).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hRotation :=
    throatSpatialRotationFlow_contMDiff period hPeriod axis angle
  have hMaps :
      throatSpatialRotationFlow period hPeriod axis angle ∘
          mappingTorusMk (ThroatData period hPeriod) =
        mappingTorusMk (ThroatData period hPeriod) ∘
          (fun current : EffectiveThroatCover period hPeriod =>
            throatCoverSpatialRotationFlow period hPeriod axis
              (angle, current)) := by
    funext current
    exact throatSpatialRotationFlow_mk period hPeriod axis angle current
  have hLeft := mfderiv_comp_apply point
    (hRotation.mdifferentiable (by simp)
      (mappingTorusMk (ThroatData period hPeriod) point))
    (hProjection.mdifferentiable (by simp) point) vector
  have hRight := mfderiv_comp_apply point
    (hProjection.mdifferentiable (by simp)
      (throatCoverSpatialRotationFlow period hPeriod axis (angle, point)))
    (hCoverRotation.mdifferentiable (by simp) point) vector
  rw [hMaps] at hLeft
  exact hLeft.symm.trans hRight

/-- The differential square formed by the cover/quotient throat inclusions
commutes. -/
theorem fixedThroatProjectionDerivative_inclusion_natural
    (point : EffectiveThroatCover period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners point) :
    mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod)
        (mappingTorusMk (ThroatData period hPeriod) point)
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (mappingTorusMk (ThroatData period hPeriod)) point vector) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (SphereData period hPeriod))
        (fixedThroatCoverInclusion period hPeriod point)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatCoverInclusion period hPeriod) point vector) := by
  have hThroatProjection :=
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod).contMDiff
  have hQuotientInclusion :=
    fixedThroatQuotientInclusion_contMDiff period hPeriod
  have hCoverInclusion :=
    fixedThroatCoverInclusion_contMDiff period hPeriod
  have hBulkProjection :=
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
  have hMaps :
      fixedThroatQuotientInclusion period hPeriod ∘
          mappingTorusMk (ThroatData period hPeriod) =
        mappingTorusMk (SphereData period hPeriod) ∘
          fixedThroatCoverInclusion period hPeriod := by
    funext current
    exact fixedThroatQuotientInclusion_mk period hPeriod current
  have hLeft := mfderiv_comp_apply point
    (hQuotientInclusion.mdifferentiable (by simp)
      (mappingTorusMk (ThroatData period hPeriod) point))
    (hThroatProjection.mdifferentiable (by simp) point) vector
  have hRight := mfderiv_comp_apply point
    (hBulkProjection.mdifferentiable (by simp)
      (fixedThroatCoverInclusion period hPeriod point))
    (hCoverInclusion.mdifferentiable (by simp) point) vector
  rw [hMaps] at hLeft
  exact hLeft.symm.trans hRight

/-- The differential of the cover inclusion intertwines throat and ambient
cover rotations. -/
theorem fixedThroatCoverInclusionDerivative_spatialRotation_natural
    (axis : Fin 3) (angle : Real)
    (point : EffectiveThroatCover period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners point) :
    mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatCoverInclusion period hPeriod)
        (throatCoverSpatialRotationFlow period hPeriod axis (angle, point))
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (fun current =>
            throatCoverSpatialRotationFlow period hPeriod axis
              (angle, current)) point vector) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (fun current =>
          coverSpatialRotationFlow period hPeriod axis (angle, current))
        (fixedThroatCoverInclusion period hPeriod point)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatCoverInclusion period hPeriod) point vector) := by
  have hThroatRotation :
      ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ∞
        (fun current : EffectiveThroatCover period hPeriod =>
          throatCoverSpatialRotationFlow period hPeriod axis
            (angle, current)) :=
    (throatCoverSpatialRotationFlow_contMDiff period hPeriod axis).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hInclusion :=
    fixedThroatCoverInclusion_contMDiff period hPeriod
  have hBulkRotation :
      ContMDiff coverModelWithCorners coverModelWithCorners ∞
        (fun current : EffectiveCover period hPeriod =>
          coverSpatialRotationFlow period hPeriod axis (angle, current)) :=
    (coverSpatialRotationFlow_contMDiff period hPeriod axis).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hMaps :
      fixedThroatCoverInclusion period hPeriod ∘
          (fun current : EffectiveThroatCover period hPeriod =>
            throatCoverSpatialRotationFlow period hPeriod axis
              (angle, current)) =
        (fun current : EffectiveCover period hPeriod =>
          coverSpatialRotationFlow period hPeriod axis (angle, current)) ∘
          fixedThroatCoverInclusion period hPeriod := by
    funext current
    exact fixedThroatCoverInclusion_spatialRotationFlow
      period hPeriod axis angle current
  have hLeft := mfderiv_comp_apply point
    (hInclusion.mdifferentiable (by simp)
      (throatCoverSpatialRotationFlow period hPeriod axis (angle, point)))
    (hThroatRotation.mdifferentiable (by simp) point) vector
  have hRight := mfderiv_comp_apply point
    (hBulkRotation.mdifferentiable (by simp)
      (fixedThroatCoverInclusion period hPeriod point))
    (hInclusion.mdifferentiable (by simp) point) vector
  rw [hMaps] at hLeft
  exact hLeft.symm.trans hRight

/-- Every genuine finite throat spatial rotation is an exact isometry of the
intrinsic nondegenerate throat metric. -/
theorem intrinsicThroatMetric_spatialRotation_isometry
    (axis : Fin 3) (angle : Real)
    (point : EffectiveThroat period hPeriod)
    (first second : TangentSpace throatCoverModelWithCorners point) :
    (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
        (throatSpatialRotationFlow period hPeriod axis angle point)
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (throatSpatialRotationFlow period hPeriod axis angle)
          point first)
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (throatSpatialRotationFlow period hPeriod axis angle)
          point second) =
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
        point first second := by
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (ThroatData period hPeriod) point
  let projectionDerivative :=
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      |>.mfderivToContinuousLinearEquiv (by simp) anchor
  let firstLift := projectionDerivative.symm first
  let secondLift := projectionDerivative.symm second
  have hProjectionDerivative :
      (projectionDerivative :
        TangentSpace throatCoverModelWithCorners anchor →L[Real]
          TangentSpace throatCoverModelWithCorners
            (mappingTorusMk (ThroatData period hPeriod) anchor)) =
        mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (mappingTorusMk (ThroatData period hPeriod)) anchor := by
    exact IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
      (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      (by simp) anchor
  have hFirst :
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (mappingTorusMk (ThroatData period hPeriod)) anchor firstLift =
        first := by
    rw [← hProjectionDerivative]
    exact projectionDerivative.apply_symm_apply first
  have hSecond :
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (mappingTorusMk (ThroatData period hPeriod)) anchor secondLift =
        second := by
    rw [← hProjectionDerivative]
    exact projectionDerivative.apply_symm_apply second
  rw [← hFirst, ← hSecond,
    throatProjectionDerivative_spatialRotation_natural,
    throatProjectionDerivative_spatialRotation_natural]
  change
    (intrinsicTensorQuotientDescent period hPeriod).tensor
        (fixedThroatQuotientInclusion period hPeriod
          (mappingTorusMk (ThroatData period hPeriod)
            (throatCoverSpatialRotationFlow period hPeriod axis
              (angle, anchor))))
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (mappingTorusMk (ThroatData period hPeriod)
            (throatCoverSpatialRotationFlow period hPeriod axis
              (angle, anchor)))
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (mappingTorusMk (ThroatData period hPeriod))
            (throatCoverSpatialRotationFlow period hPeriod axis
              (angle, anchor))
            (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
              (fun current =>
                throatCoverSpatialRotationFlow period hPeriod axis
                  (angle, current)) anchor firstLift)))
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (mappingTorusMk (ThroatData period hPeriod)
            (throatCoverSpatialRotationFlow period hPeriod axis
              (angle, anchor)))
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (mappingTorusMk (ThroatData period hPeriod))
            (throatCoverSpatialRotationFlow period hPeriod axis
              (angle, anchor))
            (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
              (fun current =>
                throatCoverSpatialRotationFlow period hPeriod axis
                  (angle, current)) anchor secondLift))) =
      (intrinsicTensorQuotientDescent period hPeriod).tensor
        (fixedThroatQuotientInclusion period hPeriod
          (mappingTorusMk (ThroatData period hPeriod) anchor))
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (mappingTorusMk (ThroatData period hPeriod) anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (mappingTorusMk (ThroatData period hPeriod)) anchor firstLift))
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (mappingTorusMk (ThroatData period hPeriod) anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (mappingTorusMk (ThroatData period hPeriod)) anchor secondLift))
  rw [fixedThroatProjectionDerivative_inclusion_natural,
    fixedThroatProjectionDerivative_inclusion_natural,
    fixedThroatProjectionDerivative_inclusion_natural,
    fixedThroatProjectionDerivative_inclusion_natural,
    fixedThroatCoverInclusionDerivative_spatialRotation_natural,
    fixedThroatCoverInclusionDerivative_spatialRotation_natural,
    fixedThroatQuotientInclusion_mk,
    fixedThroatQuotientInclusion_mk,
    fixedThroatCoverInclusion_spatialRotationFlow,
    (intrinsicTensorQuotientDescent period hPeriod).pullback,
    (intrinsicTensorQuotientDescent period hPeriod).pullback]
  exact intrinsicCoverLorentzTensor_spatialRotation_isometry
    period hPeriod axis angle
      (fixedThroatCoverInclusion period hPeriod anchor)
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatCoverInclusion period hPeriod) anchor firstLift)
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatCoverInclusion period hPeriod) anchor secondLift)

/-- The derivative of a genuine finite throat rotation as a continuous
linear equivalence. -/
def throatSpatialRotationDerivativeEquiv
    (axis : Fin 3) (angle : Real)
    (point : EffectiveThroat period hPeriod) :
    TangentSpace throatCoverModelWithCorners point ≃L[Real]
      TangentSpace throatCoverModelWithCorners
        (throatSpatialRotationFlow period hPeriod axis angle point) :=
  (throatSpatialRotationDiffeomorph period hPeriod axis angle)
    |>.mfderivToContinuousLinearEquiv
      (I := throatCoverModelWithCorners)
      (J := throatCoverModelWithCorners) (by simp) point

@[simp]
theorem throatSpatialRotationDerivativeEquiv_apply
    (axis : Fin 3) (angle : Real)
    (point : EffectiveThroat period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners point) :
    throatSpatialRotationDerivativeEquiv
        period hPeriod axis angle point vector =
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (throatSpatialRotationFlow period hPeriod axis angle)
        point vector := by
  rfl

/-- Raising a rotation-pulled throat tensor is conjugation by the inverse
rotation differential. -/
theorem raisedIntrinsicThroatTensorAt_spatialRotation_pullback
    (axis : Fin 3) (angle : Real)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (raisedIntrinsicThroatTensorAt period hPeriod
        (throatSpatialRotationTensorPullback
          period hPeriod axis angle tensor) point).toLinearMap =
      (throatSpatialRotationDerivativeEquiv
          period hPeriod axis angle point).symm.toLinearEquiv.conj
        (raisedIntrinsicThroatTensorAt period hPeriod tensor
          (throatSpatialRotationFlow
            period hPeriod axis angle point)).toLinearMap := by
  let derivative :=
    throatSpatialRotationDerivativeEquiv
      period hPeriod axis angle point
  apply LinearMap.ext
  intro vector
  change intrinsicThroatInverseMusical period hPeriod point
        ((throatSpatialRotationTensorPullback
          period hPeriod axis angle tensor).tensor point vector) =
      derivative.symm
        (intrinsicThroatInverseMusical period hPeriod
          (throatSpatialRotationFlow period hPeriod axis angle point)
          (tensor.tensor
            (throatSpatialRotationFlow period hPeriod axis angle point)
            (derivative vector)))
  apply derivative.injective
  rw [derivative.apply_symm_apply]
  apply (intrinsicThroatMusical period hPeriod
    (throatSpatialRotationFlow period hPeriod axis angle point)).injective
  apply ContinuousLinearMap.ext
  intro test
  rw [intrinsicThroatMusical_apply, intrinsicThroatMusical_apply]
  change
    (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
        (throatSpatialRotationFlow period hPeriod axis angle point)
        (derivative
          (intrinsicThroatInverseMusical period hPeriod point
            ((throatSpatialRotationTensorPullback
              period hPeriod axis angle tensor).tensor point vector)))
        test =
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
        (throatSpatialRotationFlow period hPeriod axis angle point)
        (intrinsicThroatInverseMusical period hPeriod
          (throatSpatialRotationFlow period hPeriod axis angle point)
          (tensor.tensor
            (throatSpatialRotationFlow period hPeriod axis angle point)
            (derivative vector)))
        test
  rw [← derivative.apply_symm_apply test]
  simp only [derivative, throatSpatialRotationDerivativeEquiv_apply]
  rw [intrinsicThroatMetric_spatialRotation_isometry
    period hPeriod axis angle point]
  rw [← intrinsicThroatMusical_apply period hPeriod point,
    intrinsicThroatMusical_inverse_apply period hPeriod point,
    ← intrinsicThroatMusical_apply period hPeriod
      (throatSpatialRotationFlow period hPeriod axis angle point),
    intrinsicThroatMusical_inverse_apply period hPeriod
      (throatSpatialRotationFlow period hPeriod axis angle point)]
  rw [throatSpatialRotationTensorPullback_apply]

/-- The intrinsic pointwise throat pairing is natural under simultaneous
finite spatial-rotation pullback. -/
theorem intrinsicThroatTensorPairingAt_spatialRotation_pullback
    (axis : Fin 3) (angle : Real)
    (first second :
      SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairingAt period hPeriod
        (throatSpatialRotationTensorPullback
          period hPeriod axis angle first)
        (throatSpatialRotationTensorPullback
          period hPeriod axis angle second)
        point =
      intrinsicThroatTensorPairingAt period hPeriod first second
        (throatSpatialRotationFlow period hPeriod axis angle point) := by
  unfold intrinsicThroatTensorPairingAt
  rw [raisedIntrinsicThroatTensorAt_spatialRotation_pullback
      period hPeriod axis angle first point,
    raisedIntrinsicThroatTensorAt_spatialRotation_pullback
      period hPeriod axis angle second point]
  let derivative :=
    (throatSpatialRotationDerivativeEquiv
      period hPeriod axis angle point).toLinearEquiv
  change
    LinearMap.trace Real
        (TangentSpace throatCoverModelWithCorners point)
        (derivative.symm.conj
            (raisedIntrinsicThroatTensorAt period hPeriod first
              (throatSpatialRotationFlow
                period hPeriod axis angle point)).toLinearMap *
          derivative.symm.conj
            (raisedIntrinsicThroatTensorAt period hPeriod second
              (throatSpatialRotationFlow
                period hPeriod axis angle point)).toLinearMap) =
      LinearMap.trace Real
        (TangentSpace throatCoverModelWithCorners
          (throatSpatialRotationFlow period hPeriod axis angle point))
        ((raisedIntrinsicThroatTensorAt period hPeriod first
            (throatSpatialRotationFlow
              period hPeriod axis angle point)).toLinearMap *
          (raisedIntrinsicThroatTensorAt period hPeriod second
            (throatSpatialRotationFlow
              period hPeriod axis angle point)).toLinearMap)
  have hProduct :
      (derivative.symm.conj
          (raisedIntrinsicThroatTensorAt period hPeriod first
            (throatSpatialRotationFlow
              period hPeriod axis angle point)).toLinearMap) *
          (derivative.symm.conj
            (raisedIntrinsicThroatTensorAt period hPeriod second
              (throatSpatialRotationFlow
                period hPeriod axis angle point)).toLinearMap) =
        derivative.symm.conj
          ((raisedIntrinsicThroatTensorAt period hPeriod first
              (throatSpatialRotationFlow
                period hPeriod axis angle point)).toLinearMap *
            (raisedIntrinsicThroatTensorAt period hPeriod second
              (throatSpatialRotationFlow
                period hPeriod axis angle point)).toLinearMap) := by
    exact (LinearEquiv.conj_comp derivative.symm _ _).symm
  rw [hProduct]
  exact LinearMap.trace_conj' _ derivative.symm

/-- Componentwise finite spatial-rotation pullback on the two-sector throat
tensor space. -/
def throatSpatialRotationTensorPairPullback
    (axis : Fin 3) (angle : Real)
    (tensor : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    SmoothThroatGeneralMetricTensorPair period hPeriod :=
  (throatSpatialRotationTensorPullback
      period hPeriod axis angle tensor.1,
    throatSpatialRotationTensorPullback
      period hPeriod axis angle tensor.2)

/-- Componentwise pointwise naturality for the two-sector throat metric
pairing. -/
theorem intrinsicThroatTensorPairPairingAt_spatialRotation_pullback
    (axis : Fin 3) (angle : Real)
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairPairingAt period hPeriod
        (throatSpatialRotationTensorPairPullback
          period hPeriod axis angle first)
        (throatSpatialRotationTensorPairPullback
          period hPeriod axis angle second)
        point =
      intrinsicThroatTensorPairPairingAt period hPeriod first second
        (throatSpatialRotationFlow period hPeriod axis angle point) := by
  unfold intrinsicThroatTensorPairPairingAt
    throatSpatialRotationTensorPairPullback
  rw [intrinsicThroatTensorPairingAt_spatialRotation_pullback
      period hPeriod axis angle first.1 second.1 point,
    intrinsicThroatTensorPairingAt_spatialRotation_pullback
      period hPeriod axis angle first.2 second.2 point]

private theorem integral_eq_of_measurePreserving
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {rotation : α → α}
    (hPreserving : MeasurePreserving rotation μ μ)
    (hEmbedding : MeasurableEmbedding rotation)
    (density pulledDensity : α → Real)
    (hPointwise : ∀ point, pulledDensity point = density (rotation point)) :
    (∫ point, pulledDensity point ∂μ) =
      ∫ point, density point ∂μ := by
  calc
    _ = ∫ point, density (rotation point) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hPointwise
    _ = _ := hPreserving.integral_comp hEmbedding density

/-- The canonical-measure integral of the two-sector throat pairing is
invariant under simultaneous finite spatial-rotation pullback. -/
theorem intrinsicThroatTensorPairPairing_integral_spatialRotation_invariant
    (axis : Fin 3) (angle : Real)
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    (∫ point : EffectiveThroat period hPeriod,
      intrinsicThroatTensorPairPairingAt period hPeriod
        (throatSpatialRotationTensorPairPullback
          period hPeriod axis angle first)
        (throatSpatialRotationTensorPairPullback
          period hPeriod axis angle second) point
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ∫ point : EffectiveThroat period hPeriod,
        intrinsicThroatTensorPairPairingAt period hPeriod first second point
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  letI : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
  letI : BorelSpace (EffectiveThroat period hPeriod) := ⟨rfl⟩
  exact integral_eq_of_measurePreserving
    (intrinsicCanonicalThroatVolumeMeasure_spatialRotation_measurePreserving
      period hPeriod axis angle)
    (throatSpatialRotationFlow_measurableEmbedding
      period hPeriod axis angle)
    (fun point =>
      intrinsicThroatTensorPairPairingAt
        period hPeriod first second point)
    (fun point =>
      intrinsicThroatTensorPairPairingAt period hPeriod
        (throatSpatialRotationTensorPairPullback
          period hPeriod axis angle first)
        (throatSpatialRotationTensorPairPullback
          period hPeriod axis angle second) point)
    (intrinsicThroatTensorPairPairingAt_spatialRotation_pullback
      period hPeriod axis angle first second)

/-- The same finite-rotation invariance in the canonical integrated-pairing
interface. -/
theorem canonicalIntrinsicThroatTensorPairPairing_spatialRotation_invariant
    (axis : Fin 3) (angle : Real)
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    canonicalIntrinsicThroatTensorPairPairing period hPeriod
        (throatSpatialRotationTensorPairPullback
          period hPeriod axis angle first)
        (throatSpatialRotationTensorPairPullback
          period hPeriod axis angle second) =
      canonicalIntrinsicThroatTensorPairPairing
        period hPeriod first second := by
  exact intrinsicThroatTensorPairPairing_integral_spatialRotation_invariant
    period hPeriod axis angle first second

/-- The canonical integrated pairing along the genuine finite-rotation orbit
is a constant scalar curve, hence has zero derivative at angle zero.  This
does not identify any tensor-orbit derivative with a representation action. -/
theorem canonicalIntrinsicThroatTensorPairPairing_spatialRotation_hasDerivAt_zero
    (axis : Fin 3)
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    HasDerivAt
      (fun angle =>
        canonicalIntrinsicThroatTensorPairPairing period hPeriod
          (throatSpatialRotationTensorPairPullback
            period hPeriod axis angle first)
          (throatSpatialRotationTensorPairPullback
            period hPeriod axis angle second))
      0 0 := by
  have hFunction :
      (fun angle =>
        canonicalIntrinsicThroatTensorPairPairing period hPeriod
          (throatSpatialRotationTensorPairPullback
            period hPeriod axis angle first)
          (throatSpatialRotationTensorPairPullback
            period hPeriod axis angle second)) =
        fun _ : Real =>
          canonicalIntrinsicThroatTensorPairPairing
            period hPeriod first second := by
    funext angle
    exact
      canonicalIntrinsicThroatTensorPairPairing_spatialRotation_invariant
        period hPeriod axis angle first second
  rw [hFunction]
  exact hasDerivAt_const 0 _

end

end P0EFTJanusProgramPThroatMetricRotationPairingNaturality4D
end JanusFormal
