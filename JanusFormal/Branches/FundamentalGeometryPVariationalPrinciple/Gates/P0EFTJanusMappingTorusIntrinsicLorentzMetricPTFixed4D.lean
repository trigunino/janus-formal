import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D

/-!
# PT fixed point of the intrinsic D8 Lorentz metric

Time reversal is an isometry of the ambient-product pullback tensor on the
cover.  Naturality of the two projection differentials transports this fact
to the quotient descent.  Hence the genuine smooth intrinsic Lorentz metric,
including its tied musical equivalence, is fixed by analytic PT.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicLorentzMetricPTFixed4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzTensorPTAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensorPTSmoothness4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

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

private abbrev CoverTangent (point : EffectiveCover period hPeriod) :=
  TangentSpace coverModelWithCorners point

@[simp]
theorem reflectedSpherePT_mk_timeReverse
    (point : EffectiveCover period hPeriod) :
    reflectedSpherePT period hPeriod
        (mappingTorusMk (sphereData period hPeriod) point) =
      mappingTorusMk (sphereData period hPeriod)
        (timeReverseCover (sphereData period hPeriod) point) := by
  rfl

/-- Cover time reversal is an exact isometry of the intrinsic pullback
Lorentz tensor. -/
theorem intrinsicCoverLorentzTensor_timeReverse_isometry
    (point : EffectiveCover period hPeriod)
    (first second : CoverTangent period hPeriod point) :
    intrinsicCoverLorentzTensor period hPeriod
        (timeReverseCover (sphereData period hPeriod) point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (timeReverseCover (sphereData period hPeriod)) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (timeReverseCover (sphereData period hPeriod)) point second) =
      intrinsicCoverLorentzTensor period hPeriod point first second := by
  have hFirst := coverAmbientDerivative_timeReverse_components period hPeriod
    point first
  have hSecond := coverAmbientDerivative_timeReverse_components period hPeriod
    point second
  rw [intrinsicCoverLorentzTensor_apply,
    intrinsicCoverLorentzTensor_apply,
    hFirst.1, hSecond.1, hFirst.2, hSecond.2]
  ring

/-- The quotient projection derivative commutes with the derivatives of the
cover and quotient PT maps. -/
theorem quotientProjectionDerivative_timeReverse_natural
    (point : EffectiveCover period hPeriod)
    (vector : CoverTangent period hPeriod point) :
    mfderiv coverModelWithCorners coverModelWithCorners
        (reflectedSpherePT period hPeriod)
        (mappingTorusMk (sphereData period hPeriod) point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point vector) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod))
        (timeReverseCover (sphereData period hPeriod) point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (timeReverseCover (sphereData period hPeriod)) point vector) := by
  have hProjection :=
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
  have hReverse := reflectedSphereCover_timeReverse_contMDiff period hPeriod
  have hPT := reflectedSpherePT_contMDiff period hPeriod
  have hMaps :
      reflectedSpherePT period hPeriod ∘
          mappingTorusMk (sphereData period hPeriod) =
        mappingTorusMk (sphereData period hPeriod) ∘
          timeReverseCover (sphereData period hPeriod) := by
    funext current
    rfl
  have hLeft := mfderiv_comp_apply point
    (hPT.mdifferentiable (by simp)
      (mappingTorusMk (sphereData period hPeriod) point))
    (hProjection.mdifferentiable (by simp) point) vector
  have hRight := mfderiv_comp_apply point
    (hProjection.mdifferentiable (by simp)
      (timeReverseCover (sphereData period hPeriod) point))
    (hReverse.mdifferentiable (by simp) point) vector
  rw [hMaps] at hLeft
  exact hLeft.symm.trans hRight

/-- The PT-pulled quotient tensor is another descent of the same cover
tensor. -/
def intrinsicPTPulledTensorDescent :
    IntrinsicTensorQuotientDescent period hPeriod where
  tensor :=
    (smoothPTTensorPullback period hPeriod
      (analyticPTTensorPullbackLocalSmoothness period hPeriod)
      (intrinsicTensorQuotientDescent period hPeriod).toSymmetricTensor).tensor
  pullback := by
    intro point first second
    rw [P0EFTJanusMappingTorusGeneralLorentzTensorPTAction4D.smoothPTTensorPullback_apply,
      quotientProjectionDerivative_timeReverse_natural,
      quotientProjectionDerivative_timeReverse_natural,
      reflectedSpherePT_mk_timeReverse]
    change (intrinsicTensorQuotientDescent period hPeriod).tensor
        (mappingTorusMk (sphereData period hPeriod)
          (timeReverseCover (sphereData period hPeriod) point))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (timeReverseCover (sphereData period hPeriod) point)
          (mfderiv coverModelWithCorners coverModelWithCorners
            (timeReverseCover (sphereData period hPeriod)) point first))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (timeReverseCover (sphereData period hPeriod) point)
          (mfderiv coverModelWithCorners coverModelWithCorners
            (timeReverseCover (sphereData period hPeriod)) point second)) = _
    rw [(intrinsicTensorQuotientDescent period hPeriod).pullback]
    exact intrinsicCoverLorentzTensor_timeReverse_isometry period hPeriod
      point first second

/-- The smooth intrinsic quotient tensor is fixed by genuine analytic PT
pullback. -/
theorem intrinsicSmoothTensor_pt_fixed :
    smoothPTTensorPullback period hPeriod
        (analyticPTTensorPullbackLocalSmoothness period hPeriod)
        (intrinsicTensorQuotientDescent period hPeriod).toSymmetricTensor =
      (intrinsicTensorQuotientDescent period hPeriod).toSymmetricTensor := by
  apply SmoothSymmetricCovariantTwoTensor.ext
  change (intrinsicPTPulledTensorDescent period hPeriod).tensor =
    (intrinsicTensorQuotientDescent period hPeriod).tensor
  exact IntrinsicTensorQuotientDescent.tensor_unique period hPeriod
    (intrinsicPTPulledTensorDescent period hPeriod)
    (intrinsicTensorQuotientDescent period hPeriod)

/-- The complete intrinsic Lorentz metric, including its musical
equivalence, is a PT fixed point. -/
@[simp]
theorem intrinsicSmoothGeneralLorentzMetric_pt_fixed :
    smoothGeneralLorentzMetricPTPullback period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) =
      intrinsicSmoothGeneralLorentzMetric period hPeriod := by
  apply smoothGeneralLorentzMetric_ext period hPeriod
  exact intrinsicSmoothTensor_pt_fixed period hPeriod

/-- Two identical intrinsic sectors are fixed by PT together with exchange. -/
@[simp]
theorem intrinsicSmoothGeneralLorentzMetric_pair_ptExchange_fixed :
    smoothGeneralLorentzMetricPTExchange period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod,
          intrinsicSmoothGeneralLorentzMetric period hPeriod) =
      (intrinsicSmoothGeneralLorentzMetric period hPeriod,
        intrinsicSmoothGeneralLorentzMetric period hPeriod) := by
  simp [smoothGeneralLorentzMetricPTExchange]

/-- The genuine intrinsic throat trace is unchanged after ambient PT
pullback. -/
@[simp]
theorem intrinsicGeneralLorentzMetricThroatTrace_pt_fixed :
    generalLorentzMetricThroatTrace period hPeriod
        (smoothGeneralLorentzMetricPTPullback period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)) =
      generalLorentzMetricThroatTrace period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) := by
  rw [intrinsicSmoothGeneralLorentzMetric_pt_fixed]

/-- In particular, the PT-transformed intrinsic throat trace remains
nondegenerate. -/
theorem intrinsicGeneralLorentzMetricThroatTrace_pt_nondegenerate :
    ThroatTensorIsNondegenerate period hPeriod
      (generalLorentzMetricThroatTrace period hPeriod
        (smoothGeneralLorentzMetricPTPullback period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod))) := by
  rw [intrinsicSmoothGeneralLorentzMetric_pt_fixed]
  exact intrinsicGeneralLorentzMetricThroatTrace_nondegenerate
    period hPeriod

end

end P0EFTJanusMappingTorusIntrinsicLorentzMetricPTFixed4D
end JanusFormal
