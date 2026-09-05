import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalHolonomicStereographicInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D

/-! # Intrinsic Lorentz tensor in the actual stereographic coordinates

The shifted physical map lifts explicitly to the cover. Differentiating its
ambient immersion identifies the descended tensor with the round spatial
metric minus the time product, with the exact stereographic conformal factor.
-/

namespace JanusFormal
namespace P0EFTJanusCanonicalStereographicIntrinsicMetric4D

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusCanonicalLatitudeCoareaClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarStereographicVolumeComparison4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusStereographicInverseDifferential4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusCanonicalHolonomicStereographicOverlap4D
open P0EFTJanusCanonicalHolonomicStereographicInverse4D

private abbrev Space3 := EuclideanSpace Real (Fin 3)
private abbrev Coordinates := Space3 × Real
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
private abbrev Ambient := EuclideanR4 × Real

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveCover := MappingTorusCover (reflectedSphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

def shiftedStereographicCoverLift (shift : Real) (pole : StandardSphere)
    (point : Coordinates) : EffectiveCover period hPeriod :=
  (coverHomeomorphProd (reflectedSphereData period hPeriod)).symm
    (unitThreeSphereHomeomorph.symm (stereographicInverseSphere pole point.1), point.2 + shift)

theorem shiftedStereographicCoverLift_contMDiff (shift : Real) (pole : StandardSphere) :
    ContMDiff coverModelWithCorners coverModelWithCorners ∞
      (shiftedStereographicCoverLift period hPeriod shift pole) := by
  have hSphere : ContMDiff (𝓡 3) (𝓡 3) ∞ unitThreeSphereHomeomorph.symm :=
    chartedSpacePullback_invFun_contMDiff (𝓡 3) ∞ unitThreeSphereHomeomorph
  have hParameter : ContMDiff coverModelWithCorners coverModelWithCorners ∞
      (fun point : Coordinates =>
        (unitThreeSphereHomeomorph.symm (stereographicInverseSphere pole point.1),
          point.2 + shift)) :=
    (hSphere.comp (((stereographicInverseSphere_contMDiff pole).of_le (by simp)).comp
      contMDiff_fst)).prodMk (contMDiff_snd.add contMDiff_const)
  exact (chartedSpacePullback_invFun_contMDiff coverModelWithCorners ∞
    (coverHomeomorphProd (reflectedSphereData period hPeriod))).comp hParameter

theorem shiftedStereographicCoverLift_projection (shift : Real) (pole : StandardSphere) :
    mappingTorusMk (reflectedSphereData period hPeriod) ∘
        shiftedStereographicCoverLift period hPeriod shift pole =
      shiftedStereographicPhysicalMapAmbient period hPeriod shift pole := by
  funext point
  rfl

theorem shiftedStereographicCoverLift_ambient (shift : Real) (pole : StandardSphere) :
    coverAmbientMap period hPeriod ∘ shiftedStereographicCoverLift period hPeriod shift pole =
      fun point : Coordinates => (stereographicInverseVector pole point.1, point.2 + shift) := by
  funext point
  change ((unitThreeSphereHomeomorph
    (unitThreeSphereHomeomorph.symm (stereographicInverseSphere pole point.1))).1,
      point.2 + shift) = _
  rw [unitThreeSphereHomeomorph.apply_symm_apply]
  rfl

theorem shiftedStereographicCoverLift_ambient_derivative
    (shift : Real) (pole : StandardSphere) (point vector : Coordinates) :
    coverAmbientDerivative period hPeriod
        (shiftedStereographicCoverLift period hPeriod shift pole point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (shiftedStereographicCoverLift period hPeriod shift pole) point vector) =
      (fderiv Real (stereographicInverseVector pole) point.1 vector.1, vector.2) := by
  let derivative : Coordinates →L[Real] Ambient :=
    ((fderiv Real (stereographicInverseVector pole) point.1).comp
      (ContinuousLinearMap.fst Real Space3 Real)).prod (ContinuousLinearMap.snd Real Space3 Real)
  have hDerivative : HasFDerivAt
      (fun current : Coordinates => (stereographicInverseVector pole current.1, current.2 + shift))
      derivative point :=
    ((((stereographicInverseVector_contDiff pole).differentiable (by simp) point.1).hasFDerivAt.comp
      point (hasFDerivAt_fst)).prodMk ((hasFDerivAt_snd).add_const shift))
  have hModel : mfderiv coverModelWithCorners (modelWithCornersSelf Real Ambient)
      (fun current : Coordinates => (stereographicInverseVector pole current.1, current.2 + shift))
      point = derivative := by
    have hSelf : mfderiv (modelWithCornersSelf Real Coordinates) (modelWithCornersSelf Real Ambient)
        (fun current : Coordinates => (stereographicInverseVector pole current.1, current.2 + shift))
        point = derivative := by
      rw [mfderiv_eq_fderiv]
      exact hDerivative.fderiv
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hSelf
    exact hSelf
  have hChain := mfderiv_comp point
    ((coverAmbientMap_contMDiff period hPeriod).mdifferentiableAt (by simp))
    ((shiftedStereographicCoverLift_contMDiff period hPeriod shift pole).mdifferentiableAt (by simp))
  rw [shiftedStereographicCoverLift_ambient] at hChain
  have hApplied := congrArg (fun derivative => derivative vector) hChain
  change (mfderiv coverModelWithCorners (modelWithCornersSelf Real Ambient)
      (fun current : Coordinates => (stereographicInverseVector pole current.1, current.2 + shift))
      point) vector = _ at hApplied
  rw [hModel] at hApplied
  exact hApplied.symm

/-- Exact pullback of the descended canonical tensor by the actual shifted
stereographic physical map, for all tangent vectors and all coordinates. -/
theorem shiftedStereographicPhysicalMapAmbient_intrinsic_metric
    (shift : Real) (pole : StandardSphere) (point first second : Coordinates) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole) point second) =
      (4 / (‖point.1‖ ^ 2 + 4)) ^ 2 * ⟪first.1, second.1⟫ - first.2 * second.2 := by
  let lift := shiftedStereographicCoverLift period hPeriod shift pole
  let projection := mappingTorusMk (reflectedSphereData period hPeriod)
  have hChain : mfderiv coverModelWithCorners coverModelWithCorners
      (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole) point =
      (mfderiv coverModelWithCorners coverModelWithCorners projection (lift point)).comp
        (mfderiv coverModelWithCorners coverModelWithCorners lift point) := by
    rw [← shiftedStereographicCoverLift_projection]
    exact mfderiv_comp point
      ((reflectedSphere_projection_isLocalDiffeomorph period hPeriod (lift point)).mdifferentiableAt
        (by simp))
      ((shiftedStereographicCoverLift_contMDiff period hPeriod shift pole).mdifferentiableAt (by simp))
  change intrinsicQuotientTensorField period hPeriod (projection (lift point)) _ _ = _
  rw [hChain]
  change intrinsicQuotientTensorField period hPeriod (projection (lift point))
    (mfderiv coverModelWithCorners coverModelWithCorners projection (lift point)
      (mfderiv coverModelWithCorners coverModelWithCorners lift point first))
    (mfderiv coverModelWithCorners coverModelWithCorners projection (lift point)
      (mfderiv coverModelWithCorners coverModelWithCorners lift point second)) = _
  rw [intrinsicQuotientTensorField_pullback, intrinsicCoverLorentzTensor_apply]
  rw [shiftedStereographicCoverLift_ambient_derivative,
    shiftedStereographicCoverLift_ambient_derivative]
  exact congrArg (fun value => value - first.2 * second.2)
    (stereographicInverseVector_fderiv_inner pole point.1 first.1 second.1)

/-- The intrinsic tensor in a holonomic chart is the pullback of the concrete
stereographic product tensor by the inverse transition of Gate573. -/
theorem holonomic_intrinsic_metric_stereographic_pullback
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole)
    (current first second : Vector4)
    (hCurrent : current ∈ holonomicToStereographicDomain
      period hPeriod patch coordinate shift pole point hPoint) :
    let inverse := holonomicToStereographicLocalInverse
      period hPeriod patch coordinate shift pole point hPoint
    let derivative := mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      inverse current
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor (patch.coordinateMap current)
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          patch.coordinateMap current first)
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          patch.coordinateMap current second) =
      (4 / (‖(inverse current).1‖ ^ 2 + 4)) ^ 2 *
        ⟪(derivative first).1, (derivative second).1⟫ -
          (derivative first).2 * (derivative second).2 := by
  dsimp only
  have hChain := holonomicToStereographicLocalInverse_mfderiv
    period hPeriod patch coordinate shift pole point hPoint current hCurrent
  have hFirst := congrArg (fun derivative => derivative first) hChain
  have hSecond := congrArg (fun derivative => derivative second) hChain
  simp only [ContinuousLinearMap.comp_apply] at hFirst hSecond
  have hMetric := shiftedStereographicPhysicalMapAmbient_intrinsic_metric period hPeriod shift pole
    (holonomicToStereographicLocalInverse period hPeriod patch coordinate shift pole point hPoint current)
    (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      (holonomicToStereographicLocalInverse
        period hPeriod patch coordinate shift pole point hPoint) current first)
    (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      (holonomicToStereographicLocalInverse
        period hPeriod patch coordinate shift pole point hPoint) current second)
  have hPair := congrArg (fun location : EffectiveQuotient period hPeriod =>
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor location
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      patch.coordinateMap current first)
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        patch.coordinateMap current second))
    (holonomicToStereographicLocalInverse_physical_agreement
      period hPeriod patch coordinate shift pole point hPoint current hCurrent)
  have hVectors := congrArg₂ (fun (first second : CoverCoordinates) =>
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
      (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole
        (holonomicToStereographicLocalInverse
          period hPeriod patch coordinate shift pole point hPoint current)) first second)
    hFirst hSecond
  exact hPair.symm.trans (hVectors.symm.trans hMetric)

/-- Componentwise identification of the actual holonomic metric, without a
metric-agreement hypothesis or an assumed change-of-coordinates contract. -/
theorem canonical_holonomic_stereographic_intrinsic_metric_gate
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole)
    (current : Vector4)
    (hCurrent : current ∈ holonomicToStereographicDomain
      period hPeriod patch coordinate shift pole point hPoint)
    (first second : Fin 4) :
    let inverse := holonomicToStereographicLocalInverse
      period hPeriod patch coordinate shift pole point hPoint
    let derivative := mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      inverse current
    localMetricMatrix period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch current first second =
      (4 / (‖(inverse current).1‖ ^ 2 + 4)) ^ 2 *
        ⟪(derivative (Pi.single first 1)).1, (derivative (Pi.single second 1)).1⟫ -
          (derivative (Pi.single first 1)).2 * (derivative (Pi.single second 1)).2 := by
  dsimp only
  rw [localMetricMatrix, localMetricCoefficient, patch.frame_eq_coordinateDerivative,
    patch.frame_eq_coordinateDerivative]
  exact holonomic_intrinsic_metric_stereographic_pullback period hPeriod patch coordinate shift pole
    point hPoint current (Pi.single first 1) (Pi.single second 1) hCurrent

end
end P0EFTJanusCanonicalStereographicIntrinsicMetric4D
end JanusFormal
