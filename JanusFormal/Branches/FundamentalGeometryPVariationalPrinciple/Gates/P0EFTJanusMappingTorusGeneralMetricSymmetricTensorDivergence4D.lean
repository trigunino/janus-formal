import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralMetricSymmetricTensorCovariantDerivative4D

/-!
# Divergence of a general symmetric tensor

This gate contracts the already-globalized local Levi--Civita derivative in
its derivative and first tensor slots.  The resulting model covector is
smooth in every holonomic chart and obeys the exact covector transition law.
No rank-three bundle or additional atlas compatibility hypothesis is used.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius Topology
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorCovariantDerivative4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 :=
  P0EFTJanusMappingTorusGeneralMetricSymmetricTensorCovariantDerivative4D.Vector4
abbrev Index4 :=
  P0EFTJanusMappingTorusGeneralMetricSymmetricTensorCovariantDerivative4D.Index4
abbrev Matrix4 :=
  P0EFTJanusMappingTorusGeneralMetricSymmetricTensorCovariantDerivative4D.Matrix4

private def coordinateBasisVector (index : Index4) : Vector4 :=
  Pi.single index 1

/-- Fixing the last slot of `∇h` gives a bilinear form in the two slots that
are contracted by the inverse metric. -/
def localSymmetricTensorCovariantDerivativeSlice
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate last : Vector4) :
    LinearMap.BilinForm Real Vector4 where
  toFun derivative :=
    { toFun := fun first =>
        localSymmetricTensorCovariantDerivativeApply period hPeriod metric
          tensor patch coordinate derivative first last
      map_add' := by
        intro left right
        change
          localSymmetricTensorCovariantDerivativeTrilinearForm period hPeriod
              metric tensor patch coordinate derivative (left + right) last =
            localSymmetricTensorCovariantDerivativeTrilinearForm period hPeriod
                metric tensor patch coordinate derivative left last +
              localSymmetricTensorCovariantDerivativeTrilinearForm period
                hPeriod metric tensor patch coordinate derivative right last
        rw [map_add, LinearMap.add_apply]
      map_smul' := by
        intro scalar vector
        change
          localSymmetricTensorCovariantDerivativeTrilinearForm period hPeriod
              metric tensor patch coordinate derivative (scalar • vector)
                last =
            scalar •
              localSymmetricTensorCovariantDerivativeTrilinearForm period
                hPeriod metric tensor patch coordinate derivative vector last
        rw [map_smul, LinearMap.smul_apply]
        }
  map_add' := by
    intro left right
    apply LinearMap.ext
    intro first
    change
      localSymmetricTensorCovariantDerivativeTrilinearForm period hPeriod metric
          tensor patch coordinate (left + right) first last =
        localSymmetricTensorCovariantDerivativeTrilinearForm period hPeriod
            metric tensor patch coordinate left first last +
          localSymmetricTensorCovariantDerivativeTrilinearForm period hPeriod
            metric tensor patch coordinate right first last
    rw [map_add, LinearMap.add_apply, LinearMap.add_apply]
  map_smul' := by
    intro scalar vector
    apply LinearMap.ext
    intro first
    change
      localSymmetricTensorCovariantDerivativeTrilinearForm period hPeriod metric
          tensor patch coordinate (scalar • vector) first last =
        scalar •
          localSymmetricTensorCovariantDerivativeTrilinearForm period hPeriod
            metric tensor patch coordinate vector first last
    rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply]

/-- Matrix of the two contracted slots of `∇h`, with the last vector fixed. -/
def localSymmetricTensorCovariantDerivativeSliceMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate last : Vector4) : Matrix4 :=
  LinearMap.BilinForm.toMatrix (Pi.basisFun Real Index4)
    (localSymmetricTensorCovariantDerivativeSlice period hPeriod metric tensor
      patch coordinate last)

@[simp]
theorem localSymmetricTensorCovariantDerivativeSliceMatrix_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate last : Vector4) (derivative first : Index4) :
    localSymmetricTensorCovariantDerivativeSliceMatrix period hPeriod metric
        tensor patch coordinate last derivative first =
      localSymmetricTensorCovariantDerivativeApply period hPeriod metric tensor
        patch coordinate (coordinateBasisVector derivative)
          (coordinateBasisVector first) last := by
  simp [localSymmetricTensorCovariantDerivativeSliceMatrix,
    localSymmetricTensorCovariantDerivativeSlice, coordinateBasisVector]

/-- The sliced covariant derivative transforms by the same congruence as any
covariant two-tensor, while its fixed last vector receives the third
Jacobian factor. -/
theorem localSymmetricTensorCovariantDerivativeSliceMatrix_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (last : Vector4) :
    localSymmetricTensorCovariantDerivativeSliceMatrix period hPeriod metric
        tensor firstPatch firstCoordinate last =
      (holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint).transpose *
        localSymmetricTensorCovariantDerivativeSliceMatrix period hPeriod metric
          tensor secondPatch secondCoordinate
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint last) *
        holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint := by
  let transition :=
    (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint)
        |>.toLinearEquiv.toLinearMap
  let firstForm :=
    localSymmetricTensorCovariantDerivativeSlice period hPeriod metric tensor
      firstPatch firstCoordinate last
  let secondForm :=
    localSymmetricTensorCovariantDerivativeSlice period hPeriod metric tensor
      secondPatch secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint last)
  have hForms : firstForm = secondForm.comp transition transition := by
    apply LinearMap.ext
    intro derivative
    apply LinearMap.ext
    intro first
    have hTransition :=
      congrArg
        (fun form : Vector4 →ₗ[Real] Vector4 →ₗ[Real] Vector4 →ₗ[Real] Real =>
          form derivative first last)
        (localSymmetricTensorCovariantDerivativeTrilinearForm_transition
          period hPeriod metric tensor firstPatch secondPatch firstCoordinate
          secondCoordinate samePoint)
    change
      localSymmetricTensorCovariantDerivativeApply period hPeriod metric tensor
          firstPatch firstCoordinate derivative first last =
        localSymmetricTensorCovariantDerivativeApply period hPeriod metric
          tensor secondPatch secondCoordinate
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint derivative)
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint first)
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint last)
    exact hTransition
  have hCongruence :=
    LinearMap.BilinForm.toMatrix_comp
      (b := Pi.basisFun Real Index4)
      (c := Pi.basisFun Real Index4) secondForm transition transition
  calc
    localSymmetricTensorCovariantDerivativeSliceMatrix period hPeriod metric
        tensor firstPatch firstCoordinate last =
      LinearMap.BilinForm.toMatrix (Pi.basisFun Real Index4) firstForm := rfl
    _ =
      LinearMap.BilinForm.toMatrix (Pi.basisFun Real Index4)
        (secondForm.comp transition transition) := by rw [hForms]
    _ =
      (LinearMap.toMatrix (Pi.basisFun Real Index4)
          (Pi.basisFun Real Index4) transition).transpose *
        LinearMap.BilinForm.toMatrix (Pi.basisFun Real Index4) secondForm *
        LinearMap.toMatrix (Pi.basisFun Real Index4)
          (Pi.basisFun Real Index4) transition := hCongruence
    _ = _ := rfl

/-- Entrywise inverse-metric contraction. -/
def matrixEntryContraction (first second : Matrix4) : Real :=
  ∑ i : Index4, ∑ j : Index4, first i j * second i j

private theorem matrixEntryContraction_eq_trace
    (first second : Matrix4) :
    matrixEntryContraction first second =
      Matrix.trace (first * second.transpose) := by
  unfold matrixEntryContraction Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]

/-- Inverse-metric contraction cancels an invertible common congruence. -/
theorem matrixEntryContraction_congruence
    (transition metric covariant : Matrix4)
    (hTransition : IsUnit transition) :
    matrixEntryContraction
        (transition.transpose * metric * transition)⁻¹
        (transition.transpose * covariant * transition) =
      matrixEntryContraction metric⁻¹ covariant := by
  rw [matrixEntryContraction_eq_trace, matrixEntryContraction_eq_trace]
  have hTransposeDet : IsUnit transition.transpose.det :=
    Matrix.isUnit_det_transpose transition
      ((Matrix.isUnit_iff_isUnit_det transition).mp hTransition)
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    Matrix.trace
        ((transition.transpose * metric * transition)⁻¹ *
          (transition.transpose * (covariant.transpose * transition))) =
      Matrix.trace
        (transition⁻¹ * (metric⁻¹ * covariant.transpose) * transition) := by
        congr 1
        rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
        calc
          (transition⁻¹ * (metric⁻¹ * transition.transpose⁻¹)) *
                (transition.transpose *
                  (covariant.transpose * transition)) =
              transition⁻¹ *
                (metric⁻¹ *
                  (transition.transpose⁻¹ *
                    (transition.transpose *
                      (covariant.transpose * transition)))) := by
                        noncomm_ring
          _ =
              transition⁻¹ *
                (metric⁻¹ * (covariant.transpose * transition)) := by
            rw [Matrix.nonsing_inv_mul_cancel_left transition.transpose
              (covariant.transpose * transition) hTransposeDet]
          _ =
              transition⁻¹ * (metric⁻¹ * covariant.transpose) *
                transition := by
            noncomm_ring
    _ = Matrix.trace (metric⁻¹ * covariant.transpose) :=
      Matrix.trace_conj' hTransition (metric⁻¹ * covariant.transpose)

/-- Coordinate component `∇^μ h_{μν}`. -/
def localSymmetricTensorDivergenceCoefficient
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (last : Index4) : Real :=
  ∑ derivative : Index4, ∑ first : Index4,
    (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
        derivative first *
      localSymmetricTensorCovariantDerivative period hPeriod metric tensor patch
        coordinate derivative first last

theorem localSymmetricTensorDivergenceCoefficient_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (last : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localSymmetricTensorDivergenceCoefficient period hPeriod metric tensor
        patch coordinate last) := by
  apply ContDiff.sum
  intro derivative _
  apply ContDiff.sum
  intro first _
  exact
    (localMetricInverseEntry_contDiff period hPeriod metric patch derivative
      first).mul
      (localSymmetricTensorCovariantDerivative_contDiff period hPeriod metric
        tensor patch derivative first last)

/-- The local divergence bundled as a continuous model covector. -/
def localSymmetricTensorDivergenceModelCovector
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Vector4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun vector =>
        ∑ last : Index4,
          localSymmetricTensorDivergenceCoefficient period hPeriod metric tensor
              patch coordinate last *
            vector last
      map_add' := by
        intro left right
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro scalar vector
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro last _
        ring }

@[simp]
theorem localSymmetricTensorDivergenceModelCovector_basis
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (last : Index4) :
    localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor
        patch coordinate (coordinateBasisVector last) =
      localSymmetricTensorDivergenceCoefficient period hPeriod metric tensor
        patch coordinate last := by
  classical
  unfold localSymmetricTensorDivergenceModelCovector
  change
    (∑ current : Index4,
      localSymmetricTensorDivergenceCoefficient period hPeriod metric tensor
          patch coordinate current *
        coordinateBasisVector last current) =
      localSymmetricTensorDivergenceCoefficient period hPeriod metric tensor
        patch coordinate last
  simp [coordinateBasisVector, Pi.single_apply]

theorem localSymmetricTensorDivergenceModelCovector_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞ (fun coordinate =>
      localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor
        patch coordinate) := by
  rw [contDiff_clm_apply_iff]
  intro vector
  change ContDiff Real ∞ (fun coordinate =>
    ∑ last : Index4,
      localSymmetricTensorDivergenceCoefficient period hPeriod metric tensor
          patch coordinate last *
        vector last)
  apply ContDiff.sum
  intro last _
  exact
    (localSymmetricTensorDivergenceCoefficient_contDiff period hPeriod metric
      tensor patch last).mul contDiff_const

private def localSymmetricTensorDivergenceContractionLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Vector4 →ₗ[Real] Real :=
  ∑ derivative : Index4, ∑ first : Index4,
    (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
        derivative first •
      (localSymmetricTensorCovariantDerivativeTrilinearForm period hPeriod
        metric tensor patch coordinate (coordinateBasisVector derivative)
          (coordinateBasisVector first))

private theorem localSymmetricTensorDivergenceContractionLinearMap_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate last : Vector4) :
    localSymmetricTensorDivergenceContractionLinearMap period hPeriod metric
        tensor patch coordinate last =
      matrixEntryContraction
        (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
        (localSymmetricTensorCovariantDerivativeSliceMatrix period hPeriod
          metric tensor patch coordinate last) := by
  simp only [localSymmetricTensorDivergenceContractionLinearMap,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    localSymmetricTensorCovariantDerivativeTrilinearForm_apply]
  unfold matrixEntryContraction
  apply Finset.sum_congr rfl
  intro derivative _
  apply Finset.sum_congr rfl
  intro first _
  rw [localSymmetricTensorCovariantDerivativeSliceMatrix_apply]

private theorem localSymmetricTensorDivergenceModelCovector_eq_contraction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    (localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor
      patch coordinate).toLinearMap =
      localSymmetricTensorDivergenceContractionLinearMap period hPeriod metric
        tensor patch coordinate := by
  apply (Pi.basisFun Real Index4).ext
  intro last
  rw [Pi.basisFun_apply]
  change
    localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor
        patch coordinate (coordinateBasisVector last) =
      localSymmetricTensorDivergenceContractionLinearMap period hPeriod metric
        tensor patch coordinate (coordinateBasisVector last)
  rw [localSymmetricTensorDivergenceModelCovector_basis]
  rw [localSymmetricTensorDivergenceContractionLinearMap_apply]
  unfold matrixEntryContraction localSymmetricTensorDivergenceCoefficient
  apply Finset.sum_congr rfl
  intro derivative _
  apply Finset.sum_congr rfl
  intro first _
  rw [localSymmetricTensorCovariantDerivativeSliceMatrix_apply]
  simp only [coordinateBasisVector]
  rw [localSymmetricTensorCovariantDerivativeApply_basis]

/-- Exact covector transition law for the contracted derivative. -/
theorem localSymmetricTensorDivergenceModelCovector_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor
        firstPatch firstCoordinate =
      (localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor
        secondPatch secondCoordinate).comp
        ((holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint)
            |>.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro last
  change
    (localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor
        firstPatch firstCoordinate).toLinearMap last =
      (localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor
        secondPatch secondCoordinate).toLinearMap
        ((holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint)
            |>.toLinearEquiv.toLinearMap last)
  rw [localSymmetricTensorDivergenceModelCovector_eq_contraction,
    localSymmetricTensorDivergenceModelCovector_eq_contraction]
  rw [localSymmetricTensorDivergenceContractionLinearMap_apply,
    localSymmetricTensorDivergenceContractionLinearMap_apply]
  let transition :=
    holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch secondPatch
      firstCoordinate secondCoordinate samePoint
  have hTransition : IsUnit transition := by
    simpa only [transition] using
      holonomicCoordinateTransitionMatrixAt_isUnit period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
  have hMetric :=
    localMetricMatrix_transition_congruence period hPeriod metric firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
  have hSlice :=
    localSymmetricTensorCovariantDerivativeSliceMatrix_transition period hPeriod
      metric tensor firstPatch secondPatch firstCoordinate secondCoordinate
        samePoint last
  rw [hMetric, hSlice]
  exact matrixEntryContraction_congruence
    (transition := transition)
    (metric :=
      localMetricMatrix period hPeriod metric secondPatch secondCoordinate)
    (covariant :=
      localSymmetricTensorCovariantDerivativeSliceMatrix period hPeriod metric
        tensor secondPatch secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint last))
    hTransition

end

end P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D
end JanusFormal
