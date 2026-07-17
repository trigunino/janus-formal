import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalLorentz4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusDifferentialNormalSmoothBundleIsomorphism

/-!
# Explicit local orthogonal lift of the intrinsic D8 normal line

The unit latitude normal is pushed through the quotient projection.  At every
chosen cover lift it gives a unit, metric-orthogonal generator of the genuine
differential-normal quotient.  Thus the orthogonal lift and projection are
explicit on that normal chart and their quadratic value is exactly the square
of the scalar chart coordinate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionLocal4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Set Topology Bundle Module
open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D
open P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalLorentz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev ThroatBase := MappingTorus (throatData period hPeriod)

private local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

private local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

private local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev throatPoint
    (anchor : EffectiveThroatCover period hPeriod) :
    ThroatBase period hPeriod :=
  mappingTorusMk (throatData period hPeriod) anchor

private abbrev ThroatTangent
    (point : ThroatBase period hPeriod) :=
  TangentSpace throatCoverModelWithCorners point

private abbrev AmbientTangent
    (point : ThroatBase period hPeriod) :=
  TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod point)

private abbrev TangentialRange
    (point : ThroatBase period hPeriod) :
    Submodule Real (AmbientTangent period hPeriod point) :=
  LinearMap.range
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap

private local instance ambientTangentFiniteDimensional
    (point : ThroatBase period hPeriod) :
    FiniteDimensional Real (AmbientTangent period hPeriod point) :=
  let targetEquiv : AmbientTangent period hPeriod point ≃L[Real]
      CoverCoordinates := ContinuousLinearEquiv.refl Real CoverCoordinates
  targetEquiv.toLinearEquiv.symm.finiteDimensional

/-- The explicit cover normal pushed to the genuine quotient tangent fiber. -/
def canonicalQuotientLatitudeNormal
    (anchor : EffectiveThroatCover period hPeriod) :
    AmbientTangent period hPeriod (throatPoint period hPeriod anchor) := by
  change TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod
      (mappingTorusMk (throatData period hPeriod) anchor))
  rw [fixedThroatQuotientInclusion_mk]
  exact mfderiv coverModelWithCorners coverModelWithCorners
    (mappingTorusMk (sphereData period hPeriod))
    (fixedThroatCoverInclusion period hPeriod anchor)
    (coverLatitudeNormalVector period hPeriod anchor)

/-- The descended intrinsic metric gives the pushed latitude normal unit
spacelike square. -/
theorem canonicalQuotientLatitudeNormal_square
    (anchor : EffectiveThroatCover period hPeriod) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod
          (throatPoint period hPeriod anchor))
        (canonicalQuotientLatitudeNormal period hPeriod anchor)
        (canonicalQuotientLatitudeNormal period hPeriod anchor) = 1 := by
  rw [show fixedThroatQuotientInclusion period hPeriod
      (throatPoint period hPeriod anchor) =
      mappingTorusMk (sphereData period hPeriod)
        (fixedThroatCoverInclusion period hPeriod anchor) by
    exact fixedThroatQuotientInclusion_mk period hPeriod anchor]
  unfold canonicalQuotientLatitudeNormal
  change
    (intrinsicTensorQuotientDescent period hPeriod).tensor
        (mappingTorusMk (sphereData period hPeriod)
          (fixedThroatCoverInclusion period hPeriod anchor))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)
          (coverLatitudeNormalVector period hPeriod anchor))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)
          (coverLatitudeNormalVector period hPeriod anchor)) = 1
  rw [(intrinsicTensorQuotientDescent period hPeriod).pullback]
  exact intrinsicCoverLorentzTensor_latitudeNormal_square
    period hPeriod anchor

/-- The pushed latitude normal is orthogonal to the actual quotient-throat
differential. -/
theorem canonicalQuotientLatitudeNormal_orthogonal
    (anchor : EffectiveThroatCover period hPeriod)
    (tangent : ThroatTangent period hPeriod
      (throatPoint period hPeriod anchor)) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod
          (throatPoint period hPeriod anchor))
        (canonicalQuotientLatitudeNormal period hPeriod anchor)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (throatPoint period hPeriod anchor) tangent) = 0 := by
  let sourceDerivative :=
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      |>.mfderivToContinuousLinearEquiv (by simp) anchor
  obtain ⟨coverTangent, hCoverTangent⟩ := sourceDerivative.surjective tangent
  have hSourceAt : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners
      (mappingTorusMk (throatData period hPeriod)) anchor :=
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod).contMDiff
      |>.mdifferentiableAt (by simp)
  have hTargetAt : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners
      (mappingTorusMk (sphereData period hPeriod))
      (fixedThroatCoverInclusion period hPeriod anchor) :=
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
      |>.mdifferentiableAt (by simp)
  have hCoverAt : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners (fixedThroatCoverInclusion period hPeriod) anchor :=
    (fixedThroatCoverInclusion_contMDiff period hPeriod).mdifferentiableAt
      (by simp)
  have hQuotientAt : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners (fixedThroatQuotientInclusion period hPeriod)
      (throatPoint period hPeriod anchor) :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod).mdifferentiableAt
      (by simp)
  have hDerivative :
      (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)).comp
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatCoverInclusion period hPeriod) anchor) =
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (throatPoint period hPeriod anchor)).comp
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (mappingTorusMk (throatData period hPeriod)) anchor) := by
    rw [← mfderiv_comp anchor hTargetAt hCoverAt,
      ← mfderiv_comp anchor hQuotientAt hSourceAt]
    rfl
  have hSourceDerivative :
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (mappingTorusMk (throatData period hPeriod)) anchor coverTangent =
        tangent := by
    rw [← (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      |>.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact hCoverTangent
  have hNaturality := congrArg (fun derivative => derivative coverTangent)
    hDerivative
  have hNaturality' :
      mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatCoverInclusion period hPeriod) anchor coverTangent) =
        mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (throatPoint period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (mappingTorusMk (throatData period hPeriod)) anchor coverTangent) := by
    change
      mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatCoverInclusion period hPeriod) anchor coverTangent) =
        mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (throatPoint period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (mappingTorusMk (throatData period hPeriod)) anchor coverTangent)
      at hNaturality
    exact hNaturality
  rw [← hSourceDerivative]
  rw [← hNaturality']
  rw [show fixedThroatQuotientInclusion period hPeriod
      (throatPoint period hPeriod anchor) =
      mappingTorusMk (sphereData period hPeriod)
        (fixedThroatCoverInclusion period hPeriod anchor) by
    exact fixedThroatQuotientInclusion_mk period hPeriod anchor]
  unfold canonicalQuotientLatitudeNormal
  change
    (intrinsicTensorQuotientDescent period hPeriod).tensor
        (mappingTorusMk (sphereData period hPeriod)
          (fixedThroatCoverInclusion period hPeriod anchor))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)
          (coverLatitudeNormalVector period hPeriod anchor))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatCoverInclusion period hPeriod) anchor coverTangent)) = 0
  rw [(intrinsicTensorQuotientDescent period hPeriod).pullback]
  exact intrinsicCoverLorentzTensor_latitudeNormal_orthogonal
    period hPeriod anchor coverTangent

/-- The normal quotient class of the pushed unit latitude vector. -/
def canonicalQuotientLatitudeNormalClass
    (anchor : EffectiveThroatCover period hPeriod) :
    DifferentialNormalFiber period hPeriod
      (throatPoint period hPeriod anchor) :=
  (TangentialRange period hPeriod (throatPoint period hPeriod anchor)).mkQ
    (canonicalQuotientLatitudeNormal period hPeriod anchor)

theorem canonicalQuotientLatitudeNormalClass_ne_zero
    (anchor : EffectiveThroatCover period hPeriod) :
    canonicalQuotientLatitudeNormalClass period hPeriod anchor ≠ 0 := by
  intro hZero
  have hMem : canonicalQuotientLatitudeNormal period hPeriod anchor ∈
      TangentialRange period hPeriod (throatPoint period hPeriod anchor) := by
    exact (Submodule.Quotient.mk_eq_zero _).mp (by simpa
      [canonicalQuotientLatitudeNormalClass] using hZero)
  rcases hMem with ⟨tangent, hTangent⟩
  have hSquare := canonicalQuotientLatitudeNormal_square
    period hPeriod anchor
  have hOrthogonal := canonicalQuotientLatitudeNormal_orthogonal
    period hPeriod anchor tangent
  have hMetricZero :
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          (fixedThroatQuotientInclusion period hPeriod
            (throatPoint period hPeriod anchor))
          (canonicalQuotientLatitudeNormal period hPeriod anchor)
          (canonicalQuotientLatitudeNormal period hPeriod anchor) = 0 := by
    calc
      _ = (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          (fixedThroatQuotientInclusion period hPeriod
            (throatPoint period hPeriod anchor))
          (canonicalQuotientLatitudeNormal period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatQuotientInclusion period hPeriod)
            (throatPoint period hPeriod anchor) tangent) :=
        congrArg
          ((intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
            (fixedThroatQuotientInclusion period hPeriod
              (throatPoint period hPeriod anchor))
            (canonicalQuotientLatitudeNormal period hPeriod anchor))
          hTangent.symm
      _ = 0 := hOrthogonal
  linarith

/-- Scalar coordinates generated by the explicit unit normal class. -/
def canonicalLocalNormalClassMap
    (anchor : EffectiveThroatCover period hPeriod) :
    Real →ₗ[Real] DifferentialNormalFiber period hPeriod
      (throatPoint period hPeriod anchor) :=
  LinearMap.toSpanSingleton Real _
    (canonicalQuotientLatitudeNormalClass period hPeriod anchor)

theorem canonicalLocalNormalClassMap_bijective
    (anchor : EffectiveThroatCover period hPeriod) :
    Function.Bijective
      (canonicalLocalNormalClassMap period hPeriod anchor) := by
  have hInjective : Function.Injective
      (canonicalLocalNormalClassMap period hPeriod anchor) := by
    apply LinearMap.ker_eq_bot.mp
    exact LinearMap.ker_toSpanSingleton Real
      (canonicalQuotientLatitudeNormalClass_ne_zero period hPeriod anchor)
  have hRank : Module.finrank Real Real = Module.finrank Real
      (DifferentialNormalFiber period hPeriod
        (throatPoint period hPeriod anchor)) := by
    rw [differentialNormalFiber_finrank]
    simp
  exact ⟨hInjective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hRank).mp
      hInjective⟩

/-- Explicit scalar coordinates on the genuine differential-normal fiber. -/
def canonicalLocalNormalClassEquiv
    (anchor : EffectiveThroatCover period hPeriod) :
    Real ≃ₗ[Real] DifferentialNormalFiber period hPeriod
      (throatPoint period hPeriod anchor) :=
  LinearEquiv.ofBijective (canonicalLocalNormalClassMap period hPeriod anchor)
    (canonicalLocalNormalClassMap_bijective period hPeriod anchor)

@[simp] theorem canonicalLocalNormalClassEquiv_apply
    (anchor : EffectiveThroatCover period hPeriod) (scalar : Real) :
    canonicalLocalNormalClassEquiv period hPeriod anchor scalar =
      scalar • canonicalQuotientLatitudeNormalClass period hPeriod anchor := by
  rfl

/-- The explicit metric-orthogonal representative in one canonical normal
chart. -/
def canonicalLocalOrthogonalNormalLift
    (anchor : EffectiveThroatCover period hPeriod) :
    DifferentialNormalFiber period hPeriod
        (throatPoint period hPeriod anchor) →ₗ[Real]
      AmbientTangent period hPeriod (throatPoint period hPeriod anchor) :=
  (LinearMap.toSpanSingleton Real _
      (canonicalQuotientLatitudeNormal period hPeriod anchor)).comp
    (canonicalLocalNormalClassEquiv period hPeriod anchor).symm.toLinearMap

theorem canonicalLocalOrthogonalNormalLift_represents
    (anchor : EffectiveThroatCover period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod
      (throatPoint period hPeriod anchor)) :
    (TangentialRange period hPeriod (throatPoint period hPeriod anchor)).mkQ
        (canonicalLocalOrthogonalNormalLift period hPeriod anchor normal) =
      normal := by
  let scalar := (canonicalLocalNormalClassEquiv period hPeriod anchor).symm normal
  change scalar • canonicalQuotientLatitudeNormalClass period hPeriod anchor = normal
  exact (canonicalLocalNormalClassEquiv period hPeriod anchor).apply_symm_apply
    normal

theorem canonicalLocalOrthogonalNormalLift_orthogonal
    (anchor : EffectiveThroatCover period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod
      (throatPoint period hPeriod anchor))
    (tangent : ThroatTangent period hPeriod
      (throatPoint period hPeriod anchor)) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod
          (throatPoint period hPeriod anchor))
        (canonicalLocalOrthogonalNormalLift period hPeriod anchor normal)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (throatPoint period hPeriod anchor) tangent) = 0 := by
  simp only [canonicalLocalOrthogonalNormalLift, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply]
  rw [map_smul, smul_apply, smul_eq_mul]
  rw [canonicalQuotientLatitudeNormal_orthogonal
    period hPeriod anchor tangent]
  simp

/-- The local lift has square equal to the square of its canonical scalar
coordinate. -/
theorem canonicalLocalOrthogonalNormalLift_square
    (anchor : EffectiveThroatCover period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod
      (throatPoint period hPeriod anchor)) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod
          (throatPoint period hPeriod anchor))
        (canonicalLocalOrthogonalNormalLift period hPeriod anchor normal)
        (canonicalLocalOrthogonalNormalLift period hPeriod anchor normal) =
      ((canonicalLocalNormalClassEquiv period hPeriod anchor).symm normal) ^ 2 := by
  simp only [canonicalLocalOrthogonalNormalLift, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [canonicalQuotientLatitudeNormal_square period hPeriod anchor]
  let coefficient : Real :=
    ((canonicalLocalNormalClassEquiv period hPeriod anchor).symm :
      DifferentialNormalFiber period hPeriod
        (throatPoint period hPeriod anchor) → Real) normal
  change coefficient * (coefficient * 1) = coefficient ^ 2
  ring

/-- In the canonical chart coordinate the intrinsic normal quadratic form is
exactly `scalar²`. -/
theorem canonicalLocalOrthogonalNormalLift_square_in_coordinates
    (anchor : EffectiveThroatCover period hPeriod) (scalar : Real) :
    let normal := canonicalLocalNormalClassEquiv period hPeriod anchor scalar
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod
          (throatPoint period hPeriod anchor))
        (canonicalLocalOrthogonalNormalLift period hPeriod anchor normal)
        (canonicalLocalOrthogonalNormalLift period hPeriod anchor normal) =
      scalar ^ 2 := by
  dsimp only
  rw [canonicalLocalOrthogonalNormalLift_square]
  rw [(canonicalLocalNormalClassEquiv period hPeriod anchor).symm_apply_apply]

/-- The normalized local quadratic model on every canonical collar chart. -/
def canonicalLocalNormalMetricModel
    (parameter : EffectiveThroatCover period hPeriod × Real) : Real :=
  parameter.2 ^ 2

theorem canonicalLocalNormalMetricModel_continuous :
    Continuous (canonicalLocalNormalMetricModel period hPeriod) := by
  change Continuous
    (fun parameter : EffectiveThroatCover period hPeriod × Real =>
      parameter.2 ^ 2)
  exact continuous_snd.pow 2

end

end P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionLocal4D
end JanusFormal
