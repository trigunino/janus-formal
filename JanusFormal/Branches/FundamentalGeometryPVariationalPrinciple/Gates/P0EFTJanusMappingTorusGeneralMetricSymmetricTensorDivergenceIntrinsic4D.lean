import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D

/-!
# Intrinsic covector represented by the local tensor divergence

The model covector `∇^μ h_{μν}` is transported through a genuine holonomic
frame.  Its proved model transition law makes the resulting intrinsic
covector independent of the selected chart.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergenceIntrinsic4D

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Vector4 :=
  P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D.Vector4

private abbrev Index4 :=
  P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D.Index4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveTangentFiniteDimensional
    (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real
      (TangentSpace coverModelWithCorners point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

local instance effectiveTangentT2
    (point : EffectiveQuotient period hPeriod) :
    T2Space (TangentSpace coverModelWithCorners point) := by
  change T2Space CoverCoordinates
  infer_instance

/-- Intrinsic covector represented by one holonomic chart. -/
def localSymmetricTensorDivergenceIntrinsicCovector
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    TangentSpace coverModelWithCorners
        (patch.coordinateMap coordinate) →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    ((localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor
      patch coordinate).toLinearMap.comp
        ((Pi.basisFun Real Index4).equiv (patch.frame coordinate)
          (Equiv.refl Index4)).symm.toLinearMap)

@[simp]
theorem localSymmetricTensorDivergenceIntrinsicCovector_frame
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate vector : Vector4) :
    localSymmetricTensorDivergenceIntrinsicCovector period hPeriod metric tensor
        patch coordinate
        (((Pi.basisFun Real Index4).equiv (patch.frame coordinate)
          (Equiv.refl Index4)) vector) =
      localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor
        patch coordinate vector := by
  unfold localSymmetricTensorDivergenceIntrinsicCovector
  change
    localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor
        patch coordinate
        (((Pi.basisFun Real Index4).equiv (patch.frame coordinate)
          (Equiv.refl Index4)).symm
            (((Pi.basisFun Real Index4).equiv (patch.frame coordinate)
              (Equiv.refl Index4)) vector)) =
      _
  rw [LinearEquiv.symm_apply_apply]

private def transportTangent
    {first second : EffectiveQuotient period hPeriod}
    (samePoint : first = second)
    (tangent : TangentSpace coverModelWithCorners first) :
    TangentSpace coverModelWithCorners second := by
  subst second
  exact tangent

private def transportCovector
    {first second : EffectiveQuotient period hPeriod}
    (samePoint : first = second)
    (covector : TangentSpace coverModelWithCorners first →L[Real] Real) :
    TangentSpace coverModelWithCorners second →L[Real] Real := by
  subst second
  exact covector

@[simp]
private theorem transportCovector_apply_transportTangent
    {first second : EffectiveQuotient period hPeriod}
    (samePoint : first = second)
    (covector : TangentSpace coverModelWithCorners first →L[Real] Real)
    (tangent : TangentSpace coverModelWithCorners first) :
    transportCovector period hPeriod samePoint covector
        (transportTangent period hPeriod samePoint tangent) =
      covector tangent := by
  subst second
  rfl

private theorem transportTangent_eq_of_heq
    {first second : EffectiveQuotient period hPeriod}
    (samePoint : first = second)
    (firstTangent : TangentSpace coverModelWithCorners first)
    (secondTangent : TangentSpace coverModelWithCorners second)
    (hTangent : HEq firstTangent secondTangent) :
    transportTangent period hPeriod samePoint firstTangent =
      secondTangent := by
  subst second
  exact eq_of_heq hTangent

@[simp]
private theorem transportTangent_symm_transportTangent
    {first second : EffectiveQuotient period hPeriod}
    (samePoint : first = second)
    (tangent : TangentSpace coverModelWithCorners second) :
    transportTangent period hPeriod samePoint
        (transportTangent period hPeriod samePoint.symm tangent) =
      tangent := by
  subst second
  rfl

private theorem transportCovector_apply
    {first second : EffectiveQuotient period hPeriod}
    (samePoint : first = second)
    (covector : TangentSpace coverModelWithCorners first →L[Real] Real)
    (tangent : TangentSpace coverModelWithCorners second) :
    transportCovector period hPeriod samePoint covector tangent =
      covector (transportTangent period hPeriod samePoint.symm tangent) := by
  subst second
  rfl

private theorem heq_of_transportCovector_eq
    {first second : EffectiveQuotient period hPeriod}
    (samePoint : first = second)
    (firstCovector : TangentSpace coverModelWithCorners first →L[Real] Real)
    (secondCovector : TangentSpace coverModelWithCorners second →L[Real] Real)
    (hCovector :
      transportCovector period hPeriod samePoint firstCovector =
        secondCovector) :
    HEq firstCovector secondCovector := by
  subst second
  exact heq_of_eq hCovector

/-- Intrinsic local representatives agree on every overlap. -/
theorem localSymmetricTensorDivergenceIntrinsicCovector_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    HEq
      (localSymmetricTensorDivergenceIntrinsicCovector period hPeriod metric
        tensor firstPatch firstCoordinate)
      (localSymmetricTensorDivergenceIntrinsicCovector period hPeriod metric
        tensor secondPatch secondCoordinate) := by
  apply heq_of_transportCovector_eq period hPeriod samePoint
  apply ContinuousLinearMap.ext
  intro secondTangent
  let firstTangent :=
    transportTangent period hPeriod samePoint.symm secondTangent
  let firstFrame :=
    (Pi.basisFun Real Index4).equiv (firstPatch.frame firstCoordinate)
      (Equiv.refl Index4)
  let secondFrame :=
    (Pi.basisFun Real Index4).equiv (secondPatch.frame secondCoordinate)
      (Equiv.refl Index4)
  let firstVector : Vector4 := firstFrame.symm firstTangent
  have hFrameHEq :=
    holonomicCoordinateMap_mfderiv_transition_heq period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate firstVector samePoint
  rw [coordinateMap_mfderiv_eq_frameEquiv period hPeriod firstPatch,
    coordinateMap_mfderiv_eq_frameEquiv period hPeriod secondPatch] at hFrameHEq
  have hFrame :
      transportTangent period hPeriod samePoint (firstFrame firstVector) =
        secondFrame
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
              firstVector) :=
    transportTangent_eq_of_heq period hPeriod samePoint _ _ hFrameHEq
  have hFirstFrame : firstFrame firstVector = firstTangent :=
    firstFrame.apply_symm_apply firstTangent
  have hTransportFirst :
      transportTangent period hPeriod samePoint firstTangent =
        secondTangent := by
    unfold firstTangent
    exact transportTangent_symm_transportTangent
      period hPeriod samePoint secondTangent
  have hSecondCoordinates :
      secondFrame.symm secondTangent =
        holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
            firstVector := by
    apply secondFrame.injective
    rw [secondFrame.apply_symm_apply]
    rw [← hFrame, hFirstFrame, hTransportFirst]
  rw [show
    transportCovector period hPeriod samePoint
        (localSymmetricTensorDivergenceIntrinsicCovector period hPeriod metric
          tensor firstPatch firstCoordinate) secondTangent =
      localSymmetricTensorDivergenceIntrinsicCovector period hPeriod metric
          tensor firstPatch firstCoordinate firstTangent by
    unfold firstTangent
    exact transportCovector_apply period hPeriod samePoint _ secondTangent]
  change
    localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor
        firstPatch firstCoordinate firstVector =
      localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor
        secondPatch secondCoordinate (secondFrame.symm secondTangent)
  have hCovector :=
    DFunLike.congr_fun
      (localSymmetricTensorDivergenceModelCovector_transition period hPeriod
        metric tensor firstPatch secondPatch firstCoordinate secondCoordinate
          samePoint)
      firstVector
  rw [ContinuousLinearMap.comp_apply] at hCovector
  rw [hSecondCoordinates]
  exact hCovector

end

end P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergenceIntrinsic4D
end JanusFormal
